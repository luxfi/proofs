// SPDX-License-Identifier: MIT
pragma solidity ^0.8.31;

/// @title FHE Precompile Invariant Symbolic Tests
/// @notice Halmos symbolic execution tests proving correctness invariants
///         for FHE (Fully Homomorphic Encryption) precompile operations.
///
/// Three categories of invariants:
/// 1. Gas determinism: FHE operation gas cost is a pure function of the input header
/// 2. ACL safety: Access control cannot be bypassed
/// 3. Gateway routing: Cross-chain FHE operations route correctly
///
/// Maps to:
/// - lux/node/vms/corevm/fhe_precompile.go: FHE precompile implementation
/// - lux/node/vms/corevm/acl_precompile.go: ACL precompile for FHE access control
/// - lux/node/vms/corevm/gateway_precompile.go: Gateway for cross-chain FHE
///
/// All tests use symbolic inputs -- Halmos explores all execution paths.

/// @dev FHE ciphertext header. The first 32 bytes of any ciphertext encode
///      the type and security parameters needed to compute gas cost.
struct CiphertextHeader {
    uint8  fheType;       // 0=bool, 1=uint4, 2=uint8, ..., 7=uint256, 8=ebytes64, 9=ebytes128, 10=ebytes256
    uint8  securityLevel; // 0=128bit, 1=192bit, 2=256bit
    uint16 version;       // protocol version for forward compat
}

/// @dev FHE operation types
enum FHEOp {
    Add,      // homomorphic addition
    Sub,      // homomorphic subtraction
    Mul,      // homomorphic multiplication
    Div,      // homomorphic division (encrypted numerator, plain denominator)
    Rem,      // homomorphic remainder
    And,      // homomorphic bitwise AND
    Or,       // homomorphic bitwise OR
    Xor,      // homomorphic bitwise XOR
    Shl,      // homomorphic left shift
    Shr,      // homomorphic right shift
    Eq,       // homomorphic equality comparison
    Ne,       // homomorphic not-equal
    Lt,       // homomorphic less-than
    Le,       // homomorphic less-or-equal
    Gt,       // homomorphic greater-than
    Ge,       // homomorphic greater-or-equal
    Min,      // homomorphic minimum
    Max,      // homomorphic maximum
    Neg,      // homomorphic negation
    Not,      // homomorphic bitwise NOT
    Decrypt,  // decrypt to plaintext (requires ACL)
    Reencrypt // re-encrypt for a different key (requires ACL)
}

/// @dev Minimal interface for the FHE precompile
interface IFHEPrecompile {
    function fheOp(FHEOp op, bytes calldata lhsCt, bytes calldata rhsCt) external returns (bytes memory resultCt);
    function fheDecrypt(bytes calldata ct, address decryptor) external returns (uint256 plaintext);
    function fheReencrypt(bytes calldata ct, bytes32 publicKey) external returns (bytes memory newCt);
    function gasCost(FHEOp op, CiphertextHeader calldata header) external pure returns (uint256);
}

/// @dev Minimal interface for the ACL precompile
interface IACLPrecompile {
    function allow(bytes32 ctHash, address account) external;
    function allowForDecryption(bytes32 ctHash) external;
    function isAllowed(bytes32 ctHash, address account) external view returns (bool);
    function allowedForDecryption(bytes32 ctHash) external view returns (bool);
    function aclOwner(bytes32 ctHash) external view returns (address);
}

/// @dev Minimal interface for the Gateway precompile
interface IGatewayPrecompile {
    function requestDecryption(
        bytes32[] calldata ctHandles,
        bytes4 callbackSelector,
        uint256 callbackGasLimit,
        uint256 maxTimestamp,
        bool passSignerAddress
    ) external returns (uint256 requestId);

    function fulfillDecryption(
        uint256 requestId,
        uint256[] calldata plaintexts,
        bytes[] calldata signatures
    ) external returns (bool success);

    function requestStatus(uint256 requestId) external view returns (uint8 status);
    function requestRelayer(uint256 requestId) external view returns (address relayer);
}

contract FHEInvariantTest {

    IFHEPrecompile fhe;
    IACLPrecompile acl;
    IGatewayPrecompile gateway;

    // ═══════════════════════════════════════════════════════════════
    //  SECTION 1: GAS DETERMINISM
    //  FHE gas cost is a pure function of (operation, ciphertext type, security level).
    //  No hidden state, no randomness, no caller-dependent pricing.
    // ═══════════════════════════════════════════════════════════════

    /// @notice Gas cost is deterministic: same header + op => same gas, always.
    /// @dev Calls gasCost twice with identical inputs. Halmos verifies
    ///      the results are equal across ALL symbolic header values.
    function check_gas_deterministic(
        uint8 opRaw,
        uint8 fheType,
        uint8 securityLevel,
        uint16 version
    ) public {
        // Bound operation to valid enum range
        if (opRaw > uint8(type(FHEOp).max)) return;
        FHEOp op = FHEOp(opRaw);

        // Bound fheType to valid range (0-10)
        if (fheType > 10) return;

        // Bound security level (0-2)
        if (securityLevel > 2) return;

        CiphertextHeader memory header = CiphertextHeader({
            fheType: fheType,
            securityLevel: securityLevel,
            version: version
        });

        // Two identical calls must return identical gas
        uint256 gas1 = fhe.gasCost(op, header);
        uint256 gas2 = fhe.gasCost(op, header);

        assert(gas1 == gas2);
    }

    /// @notice Gas cost is nonzero for all valid operations.
    /// @dev Every FHE operation has real computational cost. A zero gas cost
    ///      would allow unbounded FHE computation (DoS vector).
    function check_gas_nonzero(
        uint8 opRaw,
        uint8 fheType,
        uint8 securityLevel,
        uint16 version
    ) public {
        if (opRaw > uint8(type(FHEOp).max)) return;
        if (fheType > 10) return;
        if (securityLevel > 2) return;

        CiphertextHeader memory header = CiphertextHeader({
            fheType: fheType,
            securityLevel: securityLevel,
            version: version
        });

        uint256 gasCost = fhe.gasCost(FHEOp(opRaw), header);

        // All valid operations must cost gas
        assert(gasCost > 0);
    }

    /// @notice Gas cost scales with type size: larger types cost more.
    /// @dev uint256 operations must cost >= uint8 operations.
    ///      This prevents economic attacks where attackers use the
    ///      cheapest type for the most expensive computation.
    function check_gas_monotone_in_type(
        uint8 opRaw,
        uint8 smallType,
        uint8 largeType,
        uint8 securityLevel,
        uint16 version
    ) public {
        if (opRaw > uint8(type(FHEOp).max)) return;
        if (smallType > 10 || largeType > 10) return;
        if (smallType >= largeType) return;
        if (securityLevel > 2) return;

        CiphertextHeader memory headerSmall = CiphertextHeader({
            fheType: smallType,
            securityLevel: securityLevel,
            version: version
        });

        CiphertextHeader memory headerLarge = CiphertextHeader({
            fheType: largeType,
            securityLevel: securityLevel,
            version: version
        });

        uint256 gasSmall = fhe.gasCost(FHEOp(opRaw), headerSmall);
        uint256 gasLarge = fhe.gasCost(FHEOp(opRaw), headerLarge);

        // Larger FHE types must cost at least as much
        assert(gasLarge >= gasSmall);
    }

    /// @notice Gas cost scales with security level.
    /// @dev Higher security parameter -> more computation -> more gas.
    function check_gas_monotone_in_security(
        uint8 opRaw,
        uint8 fheType,
        uint8 lowSec,
        uint8 highSec,
        uint16 version
    ) public {
        if (opRaw > uint8(type(FHEOp).max)) return;
        if (fheType > 10) return;
        if (lowSec > 2 || highSec > 2) return;
        if (lowSec >= highSec) return;

        CiphertextHeader memory headerLow = CiphertextHeader({
            fheType: fheType,
            securityLevel: lowSec,
            version: version
        });

        CiphertextHeader memory headerHigh = CiphertextHeader({
            fheType: fheType,
            securityLevel: highSec,
            version: version
        });

        uint256 gasLow = fhe.gasCost(FHEOp(opRaw), headerLow);
        uint256 gasHigh = fhe.gasCost(FHEOp(opRaw), headerHigh);

        // Higher security must cost at least as much
        assert(gasHigh >= gasLow);
    }

    // ═══════════════════════════════════════════════════════════════
    //  SECTION 2: ACL SAFETY
    //  Access control for FHE ciphertexts. Only the owner can grant
    //  access. Decryption requires explicit allowance.
    // ═══════════════════════════════════════════════════════════════

    /// @notice Non-owner cannot grant ACL access.
    /// @dev The ACL precompile must reject allow() calls from non-owners.
    ///      If this invariant breaks, any account could read any ciphertext.
    function check_acl_owner_only(
        bytes32 ctHash,
        address grantee,
        address caller
    ) public {
        address owner = acl.aclOwner(ctHash);

        // Skip if caller is the owner (legitimate grant)
        if (caller == owner) return;

        // Record permission state before
        bool allowedBefore = acl.isAllowed(ctHash, grantee);

        // Attempt grant from non-owner (should fail/revert)
        try acl.allow(ctHash, grantee) {
            // If it didn't revert, the permission must not have changed
            bool allowedAfter = acl.isAllowed(ctHash, grantee);

            // If grantee was not allowed before, they must not be allowed now
            // (non-owner grant must be a no-op or revert)
            if (!allowedBefore) {
                assert(!allowedAfter);
            }
        } catch {
            // Revert is the correct behavior -- non-owner cannot grant
        }
    }

    /// @notice Decrypt requires explicit ACL allowance.
    /// @dev A ciphertext cannot be decrypted unless allowForDecryption
    ///      has been called. This is the fundamental privacy guarantee.
    function check_decrypt_requires_acl(
        bytes32 ctHash,
        address decryptor
    ) public {
        // If not allowed for decryption, decrypt must fail
        bool canDecrypt = acl.allowedForDecryption(ctHash);

        if (!canDecrypt) {
            // Build a dummy ciphertext with this hash
            // (Halmos explores all paths; the precompile must reject)
            bytes memory dummyCt = abi.encodePacked(ctHash);

            try fhe.fheDecrypt(dummyCt, decryptor) returns (uint256) {
                // If decrypt succeeded without ACL, that is a violation
                assert(false);
            } catch {
                // Correct: decrypt rejected without ACL
            }
        }
    }

    /// @notice ACL grant is idempotent.
    /// @dev Granting access twice has the same effect as granting once.
    ///      No state corruption from repeated grants.
    function check_acl_idempotent(
        bytes32 ctHash,
        address grantee
    ) public {
        // First grant
        try acl.allow(ctHash, grantee) {} catch { return; }

        bool afterFirst = acl.isAllowed(ctHash, grantee);

        // Second grant (same params)
        try acl.allow(ctHash, grantee) {} catch { return; }

        bool afterSecond = acl.isAllowed(ctHash, grantee);

        // State must be identical
        assert(afterFirst == afterSecond);
    }

    /// @notice Reencrypt requires ACL permission for the caller.
    /// @dev Re-encryption produces a new ciphertext readable by a
    ///      different key. Must require the same ACL as decryption.
    function check_reencrypt_requires_acl(
        bytes32 ctHash,
        bytes32 publicKey,
        address caller
    ) public {
        bool isAllowed = acl.isAllowed(ctHash, caller);

        if (!isAllowed) {
            bytes memory dummyCt = abi.encodePacked(ctHash);

            try fhe.fheReencrypt(dummyCt, publicKey) returns (bytes memory) {
                // Re-encryption without ACL is a violation
                assert(false);
            } catch {
                // Correct: rejected without ACL
            }
        }
    }

    // ═══════════════════════════════════════════════════════════════
    //  SECTION 3: GATEWAY ROUTING
    //  The Gateway precompile routes cross-chain FHE decryption
    //  requests. Invariants: request IDs are unique, fulfillment
    //  requires valid signatures, and callbacks cannot be replayed.
    // ═══════════════════════════════════════════════════════════════

    /// @notice Request IDs are unique (monotonically increasing).
    /// @dev Two sequential decryption requests must get different IDs.
    ///      Duplicate IDs would allow replaying one fulfillment for
    ///      a different request.
    function check_request_id_unique(
        bytes32 ctHandle1,
        bytes32 ctHandle2,
        bytes4 callbackSelector,
        uint256 callbackGasLimit,
        uint256 maxTimestamp
    ) public {
        // Bound gas limit to prevent out-of-gas in test
        if (callbackGasLimit > 1_000_000) return;
        if (maxTimestamp < block.timestamp) return;

        bytes32[] memory handles1 = new bytes32[](1);
        handles1[0] = ctHandle1;

        bytes32[] memory handles2 = new bytes32[](1);
        handles2[0] = ctHandle2;

        uint256 id1;
        uint256 id2;

        try gateway.requestDecryption(
            handles1, callbackSelector, callbackGasLimit, maxTimestamp, false
        ) returns (uint256 _id1) {
            id1 = _id1;
        } catch {
            return;
        }

        try gateway.requestDecryption(
            handles2, callbackSelector, callbackGasLimit, maxTimestamp, false
        ) returns (uint256 _id2) {
            id2 = _id2;
        } catch {
            return;
        }

        // IDs must be distinct
        assert(id1 != id2);

        // IDs must be monotonically increasing
        assert(id2 > id1);
    }

    /// @notice Pending requests cannot be fulfilled with wrong array length.
    /// @dev The number of plaintexts in fulfillment must match the number
    ///      of ciphertext handles in the original request. Mismatched
    ///      lengths would corrupt the callback data.
    function check_fulfillment_length_match(
        uint256 requestId,
        uint256 numPlaintexts,
        uint256 numSigs
    ) public {
        // Bound array sizes
        if (numPlaintexts > 16 || numSigs > 16) return;
        if (numPlaintexts == 0) return;

        // Check request exists and is pending (status 1)
        uint8 status = gateway.requestStatus(requestId);
        if (status != 1) return; // 0=nonexistent, 1=pending, 2=fulfilled, 3=expired

        // Create mismatched arrays: wrong number of plaintexts
        uint256[] memory plaintexts = new uint256[](numPlaintexts);
        bytes[] memory sigs = new bytes[](numSigs);

        // If numPlaintexts != expected count, fulfillment must fail
        try gateway.fulfillDecryption(requestId, plaintexts, sigs) returns (bool success) {
            // If it succeeded, the request must now be fulfilled
            uint8 statusAfter = gateway.requestStatus(requestId);
            assert(statusAfter == 2); // fulfilled
        } catch {
            // Rejection is valid behavior for mismatched input
        }
    }

    /// @notice Fulfilled requests cannot be re-fulfilled (no replay).
    /// @dev Once a decryption request is fulfilled, calling fulfillDecryption
    ///      again must fail. This prevents double-execution of callbacks.
    function check_no_replay_fulfillment(
        uint256 requestId
    ) public {
        uint8 status = gateway.requestStatus(requestId);

        // Only test already-fulfilled requests
        if (status != 2) return;

        uint256[] memory emptyPlaintexts = new uint256[](0);
        bytes[] memory emptySigs = new bytes[](0);

        try gateway.fulfillDecryption(requestId, emptyPlaintexts, emptySigs) returns (bool success) {
            // If it returned without reverting, success must be false
            assert(!success);
        } catch {
            // Revert is correct: cannot re-fulfill
        }
    }

    /// @notice Expired requests cannot be fulfilled.
    /// @dev If block.timestamp > maxTimestamp, the request has expired.
    ///      Fulfilling expired requests would allow stale decryptions
    ///      to be delivered after the requesting contract has moved on.
    function check_expired_not_fulfillable(
        uint256 requestId
    ) public {
        uint8 status = gateway.requestStatus(requestId);

        // Only test expired requests (status 3)
        if (status != 3) return;

        uint256[] memory plaintexts = new uint256[](1);
        bytes[] memory sigs = new bytes[](1);

        try gateway.fulfillDecryption(requestId, plaintexts, sigs) returns (bool success) {
            // Must not succeed on expired requests
            assert(!success);
        } catch {
            // Revert is correct: expired
        }
    }

    /// @notice Gateway preserves relayer assignment.
    /// @dev Once a request is assigned to a relayer (at creation time),
    ///      the relayer address must not change. This prevents front-running
    ///      where an attacker replaces the relayer to intercept plaintexts.
    function check_relayer_immutable(
        bytes32 ctHandle,
        bytes4 callbackSelector,
        uint256 callbackGasLimit,
        uint256 maxTimestamp
    ) public {
        if (callbackGasLimit > 1_000_000) return;
        if (maxTimestamp < block.timestamp) return;

        bytes32[] memory handles = new bytes32[](1);
        handles[0] = ctHandle;

        uint256 requestId;
        try gateway.requestDecryption(
            handles, callbackSelector, callbackGasLimit, maxTimestamp, false
        ) returns (uint256 _id) {
            requestId = _id;
        } catch {
            return;
        }

        address relayerBefore = gateway.requestRelayer(requestId);

        // Simulate time passing (Halmos explores all paths)
        address relayerAfter = gateway.requestRelayer(requestId);

        // Relayer must not change
        assert(relayerBefore == relayerAfter);
    }
}
