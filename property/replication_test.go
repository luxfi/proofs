// Copyright (C) 2026, Lux Industries, Inc. All rights reserved.
// See the file LICENSE for licensing terms.

// Property-based tests for the explorer E2E encrypted WAL streaming backup.
//
// These tests verify fundamental invariants of the replication system:
//   - Replication round-trip: any sequence of writes can be restored to any TXID
//   - Encryption round-trip: encrypt then decrypt = identity
//   - WAL isolation: concurrent readers see consistent committed state
//   - Pagination: iterating all pages yields all records exactly once
//   - Items cap: result size never exceeds 250 regardless of user-supplied limit
package property

import (
	"bytes"
	"crypto/rand"
	"encoding/binary"
	"fmt"
	"io"
	"math/big"
	mathrand "math/rand"
	"sort"
	"testing"
)

// ---------------------------------------------------------------------------
// Domain types (minimal models of the production types)
// ---------------------------------------------------------------------------

// WALFrame models a single WAL frame: a page write within a transaction.
type WALFrame struct {
	TXID   uint64
	PageNo uint32
	Data   []byte
}

// WALLog models the append-only WAL produced by SQLite.
type WALLog struct {
	frames    []WALFrame
	committed uint64 // highest committed TXID
}

func (w *WALLog) Append(txid uint64, page uint32, data []byte) {
	w.frames = append(w.frames, WALFrame{TXID: txid, PageNo: page, Data: data})
}

func (w *WALLog) Commit(txid uint64) {
	if txid > w.committed {
		w.committed = txid
	}
}

// FramesUpTo returns all frames with TXID <= target, ordered by position.
func (w *WALLog) FramesUpTo(target uint64) []WALFrame {
	var result []WALFrame
	for _, f := range w.frames {
		if f.TXID <= target {
			result = append(result, f)
		}
	}
	return result
}

// Restore reconstructs the page state at a given TXID by replaying frames.
// Returns a map of page number -> latest data for that page.
func Restore(frames []WALFrame) map[uint32][]byte {
	pages := make(map[uint32][]byte)
	for _, f := range frames {
		pages[f.PageNo] = f.Data
	}
	return pages
}

// S3Store models an S3 bucket holding encrypted frames.
type S3Store struct {
	frames map[uint64]map[uint32][]byte // txid -> page -> encrypted data
}

func NewS3Store() *S3Store {
	return &S3Store{frames: make(map[uint64]map[uint32][]byte)}
}

func (s *S3Store) Put(txid uint64, page uint32, data []byte) {
	if s.frames[txid] == nil {
		s.frames[txid] = make(map[uint32][]byte)
	}
	s.frames[txid][page] = data
}

func (s *S3Store) FramesUpTo(target uint64) []WALFrame {
	var result []WALFrame
	for txid, pages := range s.frames {
		if txid <= target {
			for page, data := range pages {
				result = append(result, WALFrame{TXID: txid, PageNo: page, Data: data})
			}
		}
	}
	sort.Slice(result, func(i, j int) bool {
		if result[i].TXID != result[j].TXID {
			return result[i].TXID < result[j].TXID
		}
		return result[i].PageNo < result[j].PageNo
	})
	return result
}

// ---------------------------------------------------------------------------
// XOR cipher (minimal symmetric encryption model for property tests)
// ---------------------------------------------------------------------------

// xorEncrypt models a symmetric cipher: encrypt(key, plaintext) = ciphertext.
// Using XOR so that encrypt(key, encrypt(key, x)) = x (round-trip property).
func xorEncrypt(key, plaintext []byte) []byte {
	ct := make([]byte, len(plaintext))
	for i := range plaintext {
		ct[i] = plaintext[i] ^ key[i%len(key)]
	}
	return ct
}

func xorDecrypt(key, ciphertext []byte) []byte {
	return xorEncrypt(key, ciphertext) // XOR is its own inverse
}

// ---------------------------------------------------------------------------
// Test helpers
// ---------------------------------------------------------------------------

func randomBytes(t *testing.T, n int) []byte {
	t.Helper()
	b := make([]byte, n)
	if _, err := io.ReadFull(rand.Reader, b); err != nil {
		t.Fatalf("rand: %v", err)
	}
	return b
}

func randomUint64(t *testing.T) uint64 {
	t.Helper()
	b := randomBytes(t, 8)
	return binary.BigEndian.Uint64(b)
}

// generateWriteSequence creates a random sequence of WAL writes.
// Returns the WAL log and the set of committed TXIDs.
func generateWriteSequence(t *testing.T, rng *mathrand.Rand, numTxns, maxPagesPerTx int) (*WALLog, []uint64) {
	t.Helper()
	wal := &WALLog{}
	var txids []uint64

	for tx := uint64(1); tx <= uint64(numTxns); tx++ {
		numPages := 1 + rng.Intn(maxPagesPerTx)
		for p := 0; p < numPages; p++ {
			page := uint32(rng.Intn(16)) + 1 // pages 1..16
			data := make([]byte, 64)
			rng.Read(data)
			wal.Append(tx, page, data)
		}
		wal.Commit(tx)
		txids = append(txids, tx)
	}
	return wal, txids
}

// ---------------------------------------------------------------------------
// Property 1: Replication round-trip
// ---------------------------------------------------------------------------

// TestReplication_RestoreAtAnyTXID verifies that for any sequence of SQLite
// writes, replicating all frames to S3 and restoring from S3 at any committed
// TXID yields the same page state as replaying the WAL directly.
//
// Property: For all write sequences W and all committed TXIDs t in W:
//   Restore(S3.FramesUpTo(t)) = Restore(WAL.FramesUpTo(t))
func TestReplication_RestoreAtAnyTXID(t *testing.T) {
	seeds := []int64{42, 123, 7777, 999999, 1}

	for _, seed := range seeds {
		rng := mathrand.New(mathrand.NewSource(seed))
		numTxns := 3 + rng.Intn(8) // 3..10 transactions
		maxPages := 2 + rng.Intn(4) // 2..5 pages per tx

		t.Run(fmt.Sprintf("seed=%d/txns=%d/maxpages=%d", seed, numTxns, maxPages), func(t *testing.T) {
			wal, txids := generateWriteSequence(t, rng, numTxns, maxPages)

			// Replicate all frames to S3 (encrypt with random key).
			key := make([]byte, 32)
			rng.Read(key)
			s3 := NewS3Store()
			for _, f := range wal.frames {
				encrypted := xorEncrypt(key, f.Data)
				s3.Put(f.TXID, f.PageNo, encrypted)
			}

			// For each committed TXID, restore from S3 and compare.
			for _, target := range txids {
				walPages := Restore(wal.FramesUpTo(target))
				s3Frames := s3.FramesUpTo(target)

				// Decrypt S3 frames before restoring.
				for i := range s3Frames {
					s3Frames[i].Data = xorDecrypt(key, s3Frames[i].Data)
				}
				s3Pages := Restore(s3Frames)

				// Every page in the WAL state must match S3 state.
				for page, walData := range walPages {
					s3Data, ok := s3Pages[page]
					if !ok {
						t.Fatalf("txid=%d page=%d: missing from S3 restore", target, page)
					}
					if !bytes.Equal(walData, s3Data) {
						t.Fatalf("txid=%d page=%d: data mismatch", target, page)
					}
				}
				for page := range s3Pages {
					if _, ok := walPages[page]; !ok {
						t.Fatalf("txid=%d page=%d: extra page in S3 restore", target, page)
					}
				}
			}
		})
	}
}

// ---------------------------------------------------------------------------
// Property 2: Encryption round-trip
// ---------------------------------------------------------------------------

// TestEncryption_RoundTrip verifies that for any key and any plaintext,
// decrypt(key, encrypt(key, plaintext)) = plaintext.
//
// Property: For all keys K and plaintexts P: Dec(K, Enc(K, P)) = P.
func TestEncryption_RoundTrip(t *testing.T) {
	sizes := []int{0, 1, 15, 16, 17, 64, 256, 1024, 4096}

	for _, size := range sizes {
		t.Run(fmt.Sprintf("size=%d", size), func(t *testing.T) {
			for trial := 0; trial < 50; trial++ {
				key := randomBytes(t, 32)
				plaintext := randomBytes(t, size)
				ciphertext := xorEncrypt(key, plaintext)
				recovered := xorDecrypt(key, ciphertext)

				if !bytes.Equal(plaintext, recovered) {
					t.Fatalf("trial %d: round-trip failed for size %d", trial, size)
				}
			}
		})
	}
}

// TestEncryption_DifferentKeysProduceDifferentCiphertext verifies that
// encrypting the same plaintext with different keys yields different output.
//
// Property: For all P, K1 != K2 => Enc(K1, P) != Enc(K2, P) (with high probability).
func TestEncryption_DifferentKeysProduceDifferentCiphertext(t *testing.T) {
	for trial := 0; trial < 100; trial++ {
		plaintext := randomBytes(t, 64)
		key1 := randomBytes(t, 32)
		key2 := randomBytes(t, 32)

		ct1 := xorEncrypt(key1, plaintext)
		ct2 := xorEncrypt(key2, plaintext)

		if bytes.Equal(key1, key2) {
			continue // astronomically unlikely, skip
		}
		if bytes.Equal(ct1, ct2) {
			t.Fatalf("trial %d: different keys produced same ciphertext", trial)
		}
	}
}

// TestEncryption_CiphertextDiffersFromPlaintext verifies that the ciphertext
// is not equal to the plaintext (for non-zero key).
//
// Property: For all K != 0, P != 0: Enc(K, P) != P (with high probability).
func TestEncryption_CiphertextDiffersFromPlaintext(t *testing.T) {
	for trial := 0; trial < 100; trial++ {
		key := randomBytes(t, 32)
		plaintext := randomBytes(t, 64)

		ciphertext := xorEncrypt(key, plaintext)

		if bytes.Equal(plaintext, ciphertext) {
			t.Fatalf("trial %d: ciphertext equals plaintext", trial)
		}
	}
}

// ---------------------------------------------------------------------------
// Property 3: WAL isolation (concurrent readers see consistent state)
// ---------------------------------------------------------------------------

// TestWALIsolation_ConcurrentReaders verifies that two concurrent readers
// reading the WAL at the same committed TXID both see identical page state.
// This models SQLite's WAL mode snapshot isolation.
//
// Property: For any two readers R1, R2 reading at committed TXID t:
//   Restore(WAL.FramesUpTo(t)) as seen by R1 = as seen by R2.
func TestWALIsolation_ConcurrentReaders(t *testing.T) {
	seeds := []int64{42, 1337, 8675309}

	for _, seed := range seeds {
		rng := mathrand.New(mathrand.NewSource(seed))
		numTxns := 5 + rng.Intn(6)

		t.Run(fmt.Sprintf("seed=%d", seed), func(t *testing.T) {
			wal, txids := generateWriteSequence(t, rng, numTxns, 4)

			// Pick a snapshot point for readers (some committed TXID).
			snapIdx := rng.Intn(len(txids))
			snapTxid := txids[snapIdx]

			// Reader 1: reads WAL up to snapTxid.
			r1Frames := wal.FramesUpTo(snapTxid)
			r1Pages := Restore(r1Frames)

			// Simulate writer appending more frames AFTER snapshot.
			for tx := uint64(numTxns + 1); tx <= uint64(numTxns+3); tx++ {
				pages := 1 + rng.Intn(3)
				for p := 0; p < pages; p++ {
					data := make([]byte, 64)
					rng.Read(data)
					wal.Append(tx, uint32(rng.Intn(16)+1), data)
				}
				wal.Commit(tx)
			}

			// Reader 2: reads WAL up to same snapTxid.
			// Even though new frames exist, they are beyond snapTxid.
			r2Frames := wal.FramesUpTo(snapTxid)
			r2Pages := Restore(r2Frames)

			// Both readers must see identical state.
			if len(r1Pages) != len(r2Pages) {
				t.Fatalf("readers see different page counts: %d vs %d",
					len(r1Pages), len(r2Pages))
			}
			for page, r1Data := range r1Pages {
				r2Data, ok := r2Pages[page]
				if !ok {
					t.Fatalf("page %d: missing in reader 2", page)
				}
				if !bytes.Equal(r1Data, r2Data) {
					t.Fatalf("page %d: data mismatch between readers", page)
				}
			}
		})
	}
}

// TestWALIsolation_ReaderDoesNotSeeUncommitted verifies that a reader
// at TXID t does not see frames from TXID t+1 (uncommitted or later).
//
// Property: FramesUpTo(t) contains no frame with TXID > t.
func TestWALIsolation_ReaderDoesNotSeeUncommitted(t *testing.T) {
	rng := mathrand.New(mathrand.NewSource(54321))
	wal, txids := generateWriteSequence(t, rng, 10, 4)

	for _, target := range txids {
		frames := wal.FramesUpTo(target)
		for _, f := range frames {
			if f.TXID > target {
				t.Fatalf("frame with TXID %d visible at snapshot %d", f.TXID, target)
			}
		}
	}
}

// ---------------------------------------------------------------------------
// Property 4: Pagination invariant
// ---------------------------------------------------------------------------

// page models a page of query results.
type page struct {
	items  []int
	cursor int // -1 if last page
}

// paginate splits a sorted slice into pages of the given size and returns
// all pages. Models the explorer API pagination behavior.
func paginate(items []int, pageSize int) []page {
	if pageSize <= 0 {
		pageSize = 1
	}
	var pages []page
	for i := 0; i < len(items); i += pageSize {
		end := i + pageSize
		if end > len(items) {
			end = len(items)
		}
		cursor := -1
		if end < len(items) {
			cursor = end
		}
		pages = append(pages, page{items: items[i:end], cursor: cursor})
	}
	if len(pages) == 0 {
		pages = append(pages, page{items: nil, cursor: -1})
	}
	return pages
}

// TestPagination_AllRecordsExactlyOnce verifies that iterating through all
// pages yields every record exactly once, with no duplicates or gaps.
//
// Property: For any dataset D and page size S:
//   union(page_i.items for all i) = D, and all page items are disjoint.
func TestPagination_AllRecordsExactlyOnce(t *testing.T) {
	datasets := []int{0, 1, 5, 10, 25, 100, 250}
	pageSizes := []int{1, 5, 10, 25, 50, 100, 250}

	for _, n := range datasets {
		for _, ps := range pageSizes {
			t.Run(fmt.Sprintf("n=%d/pagesize=%d", n, ps), func(t *testing.T) {
				// Build dataset.
				items := make([]int, n)
				for i := range items {
					items[i] = i
				}

				pages := paginate(items, ps)

				// Collect all items across pages.
				seen := make(map[int]int) // item -> count
				totalItems := 0
				for _, p := range pages {
					for _, item := range p.items {
						seen[item]++
						totalItems++
					}
				}

				// Every item appears exactly once.
				for i := 0; i < n; i++ {
					count, ok := seen[i]
					if !ok {
						t.Fatalf("item %d missing from pagination", i)
					}
					if count != 1 {
						t.Fatalf("item %d appeared %d times", i, count)
					}
				}

				// Total count matches.
				if totalItems != n {
					t.Fatalf("total items %d != expected %d", totalItems, n)
				}

				// Verify cursor chain: last page has cursor -1, others have valid cursor.
				for i, p := range pages {
					if i < len(pages)-1 {
						if p.cursor == -1 {
							t.Fatalf("page %d: non-terminal page has cursor -1", i)
						}
					} else {
						if p.cursor != -1 {
							t.Fatalf("last page: cursor should be -1, got %d", p.cursor)
						}
					}
				}
			})
		}
	}
}

// TestPagination_PageSizesRespected verifies that each page contains at most
// pageSize items (the last page may contain fewer).
func TestPagination_PageSizesRespected(t *testing.T) {
	rng := mathrand.New(mathrand.NewSource(12345))

	for trial := 0; trial < 50; trial++ {
		n := rng.Intn(500)
		ps := 1 + rng.Intn(100)

		items := make([]int, n)
		for i := range items {
			items[i] = i
		}

		pages := paginate(items, ps)

		for i, p := range pages {
			if len(p.items) > ps {
				t.Fatalf("trial %d page %d: %d items exceeds page size %d",
					trial, i, len(p.items), ps)
			}
		}
	}
}

// ---------------------------------------------------------------------------
// Property 5: Items count cap
// ---------------------------------------------------------------------------

const maxItemsCap = 250

// capLimit enforces the server-side maximum on user-supplied limits.
// Models the explorer API's hard cap at 250 items per response.
func capLimit(userLimit int) int {
	if userLimit <= 0 {
		return maxItemsCap
	}
	if userLimit > maxItemsCap {
		return maxItemsCap
	}
	return userLimit
}

// queryWithLimit models a paginated API query that caps results at 250.
func queryWithLimit(allItems []int, offset, userLimit int) []int {
	limit := capLimit(userLimit)

	if offset >= len(allItems) {
		return nil
	}
	end := offset + limit
	if end > len(allItems) {
		end = len(allItems)
	}
	return allItems[offset:end]
}

// TestItemsCap_NeverExceeds250 verifies that for any user-supplied limit,
// the result size is at most 250 items.
//
// Property: For all user limits L and datasets D:
//   |queryWithLimit(D, offset, L)| <= 250
func TestItemsCap_NeverExceeds250(t *testing.T) {
	// Test with a dataset larger than the cap.
	allItems := make([]int, 1000)
	for i := range allItems {
		allItems[i] = i
	}

	// Generate random user-supplied limits including adversarial values.
	limits := []int{
		-1, 0, 1, 10, 50, 100, 249, 250, 251, 500, 1000,
		999999, -999999, 2147483647, // max int32
	}

	for _, limit := range limits {
		t.Run(fmt.Sprintf("limit=%d", limit), func(t *testing.T) {
			result := queryWithLimit(allItems, 0, limit)
			if len(result) > maxItemsCap {
				t.Fatalf("limit=%d: result size %d exceeds cap %d",
					limit, len(result), maxItemsCap)
			}
		})
	}
}

// TestItemsCap_RespectedAtAllOffsets verifies the cap holds for every
// possible offset into the dataset.
func TestItemsCap_RespectedAtAllOffsets(t *testing.T) {
	allItems := make([]int, 1000)
	for i := range allItems {
		allItems[i] = i
	}

	rng := mathrand.New(mathrand.NewSource(99999))

	for trial := 0; trial < 200; trial++ {
		offset := rng.Intn(1200) // some offsets beyond dataset size
		// Random limit from a wide range including negative and huge values.
		n, _ := rand.Int(rand.Reader, big.NewInt(100000))
		userLimit := int(n.Int64()) - 50000 // range [-50000, 49999]

		result := queryWithLimit(allItems, offset, userLimit)
		if len(result) > maxItemsCap {
			t.Fatalf("trial %d offset=%d limit=%d: result size %d exceeds cap %d",
				trial, offset, userLimit, len(result), maxItemsCap)
		}
	}
}

// TestItemsCap_CapLimitFunction verifies capLimit directly for boundary values.
func TestItemsCap_CapLimitFunction(t *testing.T) {
	cases := []struct {
		input int
		want  int
	}{
		{-1, 250},
		{0, 250},
		{1, 1},
		{100, 100},
		{249, 249},
		{250, 250},
		{251, 250},
		{1000, 250},
		{999999, 250},
	}

	for _, tc := range cases {
		t.Run(fmt.Sprintf("input=%d", tc.input), func(t *testing.T) {
			got := capLimit(tc.input)
			if got != tc.want {
				t.Fatalf("capLimit(%d) = %d, want %d", tc.input, got, tc.want)
			}
		})
	}
}

// ---------------------------------------------------------------------------
// Property: Checkpoint safety (integration of replication + checkpoint)
// ---------------------------------------------------------------------------

// TestCheckpoint_OnlyAfterReplication verifies the core safety invariant:
// checkpoint never advances past the replication watermark.
//
// Property: For any sequence of operations, checkpointedUpTo <= replicatedUpTo.
func TestCheckpoint_OnlyAfterReplication(t *testing.T) {
	seeds := []int64{1, 42, 777, 31337}

	for _, seed := range seeds {
		rng := mathrand.New(mathrand.NewSource(seed))

		t.Run(fmt.Sprintf("seed=%d", seed), func(t *testing.T) {
			wal, _ := generateWriteSequence(t, rng, 10, 3)
			s3 := NewS3Store()
			key := make([]byte, 32)
			rng.Read(key)

			var replicatedUpTo uint64
			var checkpointedUpTo uint64

			// Simulate interleaved replication and checkpoint attempts.
			frameIdx := 0
			for _, f := range wal.frames {
				frameIdx++

				// Replicate this frame.
				encrypted := xorEncrypt(key, f.Data)
				s3.Put(f.TXID, f.PageNo, encrypted)

				// Advance replicatedUpTo if all frames for this TXID are in S3.
				if f.TXID > replicatedUpTo {
					allPresent := true
					for _, wf := range wal.frames {
						if wf.TXID <= f.TXID && wf.TXID > replicatedUpTo {
							if _, ok := s3.frames[wf.TXID]; !ok {
								allPresent = false
								break
							}
							if _, ok := s3.frames[wf.TXID][wf.PageNo]; !ok {
								allPresent = false
								break
							}
						}
					}
					if allPresent {
						replicatedUpTo = f.TXID
					}
				}

				// Attempt checkpoint at random intervals.
				if rng.Intn(3) == 0 {
					// Checkpoint up to replicatedUpTo (safe).
					if replicatedUpTo > checkpointedUpTo {
						checkpointedUpTo = replicatedUpTo
					}
				}

				// INVARIANT: must hold after every operation.
				if checkpointedUpTo > replicatedUpTo {
					t.Fatalf("frame %d: checkpoint %d > replicated %d",
						frameIdx, checkpointedUpTo, replicatedUpTo)
				}
			}
		})
	}
}
