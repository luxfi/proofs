---------------------------- MODULE ExplorerReplication ------------------------
(*
 * TLA+ Specification of the Explorer E2E Encrypted WAL Streaming Backup
 *
 * Source:
 *   ~/work/lux/explorer/replication/
 *   ~/work/lux/explorer/backup/
 *
 * Protocol summary:
 *   The Blockscout explorer uses SQLite for indexed chain data. A sidecar
 *   (replicate) intercepts WAL frames before SQLite's auto-checkpoint can
 *   discard them, encrypts each frame with hybrid PQ encryption (ML-KEM-768
 *   + X25519 + ChaCha20-Poly1305), and streams the encrypted frames to S3.
 *
 *   Auto-checkpoint is disabled. Replicate controls when checkpoints occur:
 *   only after confirming the corresponding WAL frames are durably stored
 *   in S3. This guarantees no frame is lost.
 *
 *   Restoration: given a base snapshot and the sequence of encrypted WAL
 *   frames up to a target TXID, the database can be reconstructed to that
 *   exact state. Each frame carries a monotonic TXID and a page number.
 *
 * State model:
 *   walFrames         -- sequence of WAL frames produced by SQLite writer
 *   replicatedUpTo    -- highest TXID confirmed durable in S3
 *   checkpointedUpTo  -- highest TXID that has been checkpointed (frames discarded)
 *   s3Frames          -- set of (txid, page) pairs stored in S3
 *   writerTxid        -- current writer transaction ID
 *   snapshotTxid      -- TXID of the last base snapshot in S3
 *
 * Actions:
 *   Write(page)             -- SQLite writer appends a WAL frame
 *   CommitTx                -- Writer commits (increments TXID)
 *   Replicate(txid)         -- Replicate reads and uploads a frame to S3
 *   ConfirmDurable(txid)    -- S3 confirms frame is durable
 *   Checkpoint(txid)        -- Replicate triggers checkpoint up to txid
 *   TakeSnapshot            -- Replicate takes a base snapshot at current TXID
 *
 * Safety:
 *   NoFrameLost             -- no frame is checkpointed before replicated
 *   S3Reconstructible       -- S3 state can reconstruct DB at any TXID
 *   MonotonicTxid           -- TXIDs are strictly monotonic
 *   CheckpointOnlyReplicated -- checkpoint never advances past replication
 *
 * Liveness:
 *   AllFramesEventuallyReplicated -- every frame is eventually in S3
 *
 * Go-to-TLA+ mapping:
 *   replication.WALFrame          -> walFrames[i]
 *   replication.Replicator.pos    -> replicatedUpTo
 *   sqlite3.Checkpoint()          -> Checkpoint action
 *   s3.PutObject()                -> Replicate + ConfirmDurable
 *   backup.Snapshot               -> TakeSnapshot
 *)

EXTENDS Integers, FiniteSets, Sequences

\* --------------------------------------------------------------------------
\* CONSTANTS
\* --------------------------------------------------------------------------

CONSTANTS
    Pages,          \* Set of page numbers (e.g. {1, 2, 3})
    MaxTxid,        \* Upper bound on transaction IDs for model checking
    MaxFrames       \* Upper bound on total WAL frames for state constraint

\* --------------------------------------------------------------------------
\* ASSUMPTIONS
\* --------------------------------------------------------------------------

ASSUME Pages # {} /\ IsFiniteSet(Pages)
ASSUME MaxTxid \in Nat \ {0}
ASSUME MaxFrames \in Nat \ {0}

\* --------------------------------------------------------------------------
\* VARIABLES
\* --------------------------------------------------------------------------

VARIABLES
    walFrames,          \* Seq of <<txid, page>> -- WAL frames in order
    replicatedUpTo,     \* Nat -- highest TXID with all frames confirmed in S3
    checkpointedUpTo,   \* Nat -- highest TXID that has been checkpointed
    s3Frames,           \* Set of <<txid, page>> -- frames durably in S3
    writerTxid,         \* Nat -- current writer TXID (uncommitted)
    snapshotTxid,       \* Nat -- TXID of last base snapshot in S3
    pendingUpload       \* Set of <<txid, page>> -- frames sent to S3, not yet confirmed

vars == <<walFrames, replicatedUpTo, checkpointedUpTo, s3Frames,
          writerTxid, snapshotTxid, pendingUpload>>

\* --------------------------------------------------------------------------
\* TYPE INVARIANT
\* --------------------------------------------------------------------------

TypeOK ==
    /\ walFrames \in Seq(Nat \X Pages)
    /\ replicatedUpTo \in 0..MaxTxid
    /\ checkpointedUpTo \in 0..MaxTxid
    /\ s3Frames \subseteq (1..MaxTxid \X Pages)
    /\ writerTxid \in 0..MaxTxid
    /\ snapshotTxid \in 0..MaxTxid
    /\ pendingUpload \subseteq (1..MaxTxid \X Pages)

\* --------------------------------------------------------------------------
\* HELPERS
\* --------------------------------------------------------------------------

\* All frames in the WAL with a given TXID
FramesForTxid(txid) ==
    {walFrames[i] : i \in {j \in 1..Len(walFrames) : walFrames[j][1] = txid}}

\* All TXIDs present in the WAL
WalTxids == {walFrames[i][1] : i \in 1..Len(walFrames)}

\* All frames in the WAL up to and including a given TXID
FramesUpTo(txid) ==
    {walFrames[i] : i \in {j \in 1..Len(walFrames) : walFrames[j][1] <= txid}}

\* Whether all frames for a TXID are in S3
TxidFullyReplicated(txid) ==
    FramesForTxid(txid) \subseteq s3Frames

\* --------------------------------------------------------------------------
\* INITIAL STATE
\* --------------------------------------------------------------------------

Init ==
    /\ walFrames = <<>>
    /\ replicatedUpTo = 0
    /\ checkpointedUpTo = 0
    /\ s3Frames = {}
    /\ writerTxid = 0
    /\ snapshotTxid = 0
    /\ pendingUpload = {}

\* --------------------------------------------------------------------------
\* ACTIONS
\* --------------------------------------------------------------------------

(*
 * Write(page):
 *   SQLite writer appends a WAL frame for the current transaction.
 *   Maps to: sqlite3 pager writing a dirty page to the WAL.
 *   Precondition: writer has an active transaction (writerTxid > 0).
 *)
Write(page) ==
    /\ writerTxid > 0
    /\ Len(walFrames) < MaxFrames
    /\ walFrames' = Append(walFrames, <<writerTxid, page>>)
    /\ UNCHANGED <<replicatedUpTo, checkpointedUpTo, s3Frames,
                   writerTxid, snapshotTxid, pendingUpload>>

(*
 * CommitTx:
 *   Writer commits the current transaction. The TXID is now final.
 *   Maps to: sqlite3 WAL commit (sync WAL to disk).
 *)
CommitTx ==
    /\ writerTxid < MaxTxid
    /\ writerTxid' = writerTxid + 1
    /\ UNCHANGED <<walFrames, replicatedUpTo, checkpointedUpTo,
                   s3Frames, snapshotTxid, pendingUpload>>

(*
 * Replicate(i):
 *   Replicate sidecar reads WAL frame at index i and uploads to S3.
 *   The frame enters pendingUpload until S3 confirms durability.
 *   Maps to: replicator goroutine reading WAL and calling s3.PutObject().
 *   Precondition: frame exists and has not been checkpointed away.
 *)
Replicate(i) ==
    /\ i \in 1..Len(walFrames)
    /\ walFrames[i][1] > checkpointedUpTo   \* not yet checkpointed
    /\ walFrames[i] \notin s3Frames          \* not already confirmed
    /\ walFrames[i] \notin pendingUpload     \* not already in flight
    /\ pendingUpload' = pendingUpload \union {walFrames[i]}
    /\ UNCHANGED <<walFrames, replicatedUpTo, checkpointedUpTo,
                   s3Frames, writerTxid, snapshotTxid>>

(*
 * ConfirmDurable(frame):
 *   S3 confirms a frame is durably stored. Move from pending to confirmed.
 *   After confirmation, update replicatedUpTo if this completes a TXID.
 *   Maps to: S3 PutObject response 200 OK.
 *)
ConfirmDurable(frame) ==
    /\ frame \in pendingUpload
    /\ s3Frames' = s3Frames \union {frame}
    /\ pendingUpload' = pendingUpload \ {frame}
    /\ LET txid == frame[1]
           newS3 == s3Frames \union {frame}
           \* Check if all frames for every TXID up to some point are now in S3.
           \* replicatedUpTo advances to the highest TXID where all frames
           \* for that TXID and all lower TXIDs are fully replicated.
           candidate == {t \in WalTxids :
                            t > replicatedUpTo
                            /\ \A t2 \in WalTxids :
                                (t2 <= t /\ t2 > replicatedUpTo)
                                => FramesForTxid(t2) \subseteq newS3}
       IN replicatedUpTo' = IF candidate = {} THEN replicatedUpTo
                            ELSE LET maxT == CHOOSE t \in candidate :
                                        \A t2 \in candidate : t2 <= t
                                 IN maxT
    /\ UNCHANGED <<walFrames, checkpointedUpTo, writerTxid, snapshotTxid>>

(*
 * Checkpoint(txid):
 *   Replicate triggers SQLite checkpoint up to txid.
 *   CRITICAL: only permitted when all frames up to txid are in S3.
 *   Maps to: sqlite3.Checkpoint(SQLITE_CHECKPOINT_PASSIVE) after replication.
 *   Precondition: txid <= replicatedUpTo (the core safety constraint).
 *)
Checkpoint(txid) ==
    /\ txid > checkpointedUpTo
    /\ txid <= replicatedUpTo   \* SAFETY: only checkpoint what is replicated
    /\ checkpointedUpTo' = txid
    /\ UNCHANGED <<walFrames, replicatedUpTo, s3Frames,
                   writerTxid, snapshotTxid, pendingUpload>>

(*
 * TakeSnapshot:
 *   Replicate takes a full database snapshot and uploads to S3.
 *   The snapshot becomes the new base for point-in-time recovery.
 *   Maps to: backup.TakeSnapshot() -> s3.PutObject(snapshot).
 *   Precondition: replicatedUpTo > snapshotTxid (progress since last snapshot).
 *)
TakeSnapshot ==
    /\ replicatedUpTo > snapshotTxid
    /\ snapshotTxid' = replicatedUpTo
    /\ UNCHANGED <<walFrames, replicatedUpTo, checkpointedUpTo,
                   s3Frames, writerTxid, pendingUpload>>

\* --------------------------------------------------------------------------
\* NEXT-STATE RELATION
\* --------------------------------------------------------------------------

Next ==
    \/ \E p \in Pages : Write(p)
    \/ CommitTx
    \/ \E i \in 1..Len(walFrames) : Replicate(i)
    \/ \E frame \in pendingUpload : ConfirmDurable(frame)
    \/ \E txid \in 1..MaxTxid : Checkpoint(txid)
    \/ TakeSnapshot

\* --------------------------------------------------------------------------
\* FAIRNESS
\* --------------------------------------------------------------------------

(*
 * Weak fairness on replication: if frames are available, they are
 * eventually uploaded. Models the replicator goroutine making progress.
 *)
Fairness ==
    /\ \A i \in 1..MaxFrames :
        WF_vars(\E p \in Pages : Write(p))
    /\ WF_vars(CommitTx)
    /\ \A i \in 1..MaxFrames :
        WF_vars(Replicate(i))
    /\ \A frame \in (1..MaxTxid \X Pages) :
        WF_vars(ConfirmDurable(frame))

\* --------------------------------------------------------------------------
\* SPECIFICATION
\* --------------------------------------------------------------------------

Spec == Init /\ [][Next]_vars /\ Fairness

\* ==========================================================================
\* SAFETY PROPERTIES
\* ==========================================================================

(*
 * NoFrameLost (primary safety invariant):
 *   No WAL frame is checkpointed before it is durably stored in S3.
 *   This is the core guarantee: checkpoint cannot discard unreplicated data.
 *
 *   Proof sketch:
 *     Checkpoint(txid) requires txid <= replicatedUpTo.
 *     replicatedUpTo only advances when ConfirmDurable moves a frame
 *     from pendingUpload to s3Frames and all frames for the TXID
 *     (and all prior TXIDs) are confirmed.
 *     Therefore checkpointedUpTo <= replicatedUpTo at all times,
 *     and every frame with txid <= checkpointedUpTo is in s3Frames.
 *)
NoFrameLost ==
    checkpointedUpTo <= replicatedUpTo

(*
 * CheckpointOnlyReplicated:
 *   Stronger version of NoFrameLost: every individual frame with a TXID
 *   at or below the checkpoint mark is in S3.
 *)
CheckpointOnlyReplicated ==
    \A i \in 1..Len(walFrames) :
        walFrames[i][1] <= checkpointedUpTo
        => walFrames[i] \in s3Frames

(*
 * S3Reconstructible:
 *   For any TXID between the snapshot and replicatedUpTo, S3 contains
 *   all WAL frames needed to reconstruct the database at that TXID.
 *   Combined with the base snapshot, this enables point-in-time recovery.
 *)
S3Reconstructible ==
    \A txid \in 1..MaxTxid :
        (txid > snapshotTxid /\ txid <= replicatedUpTo)
        => FramesUpTo(txid) \subseteq s3Frames

(*
 * MonotonicTxid:
 *   TXIDs in the WAL are monotonically non-decreasing. Frames are appended
 *   in order; the TXID of frame i+1 >= TXID of frame i.
 *)
MonotonicTxid ==
    \A i \in 1..(Len(walFrames) - 1) :
        walFrames[i][1] <= walFrames[i+1][1]

(*
 * MonotonicCheckpoint:
 *   checkpointedUpTo never decreases. Enforced structurally by
 *   Checkpoint requiring txid > checkpointedUpTo.
 *)
MonotonicCheckpointAction ==
    [][checkpointedUpTo' >= checkpointedUpTo]_vars

(*
 * MonotonicReplication:
 *   replicatedUpTo never decreases. Enforced structurally by
 *   ConfirmDurable advancing it only forward.
 *)
MonotonicReplicationAction ==
    [][replicatedUpTo' >= replicatedUpTo]_vars

(*
 * SnapshotBehindReplication:
 *   The snapshot TXID never exceeds replicatedUpTo.
 *   TakeSnapshot sets snapshotTxid = replicatedUpTo.
 *)
SnapshotBehindReplication ==
    snapshotTxid <= replicatedUpTo

(*
 * S3FramesSubsetOfWAL:
 *   Every frame in S3 was originally in the WAL. No phantom frames.
 *)
S3FramesSubsetOfWAL ==
    \A frame \in s3Frames :
        \E i \in 1..Len(walFrames) : walFrames[i] = frame

(*
 * PendingSubsetOfWAL:
 *   Every pending upload was originally in the WAL.
 *)
PendingSubsetOfWAL ==
    \A frame \in pendingUpload :
        \E i \in 1..Len(walFrames) : walFrames[i] = frame

(*
 * NoDuplicateS3:
 *   S3 frames and pending uploads are disjoint. A frame cannot be
 *   both confirmed and in-flight simultaneously.
 *)
NoDuplicateS3 ==
    s3Frames \intersect pendingUpload = {}

\* ==========================================================================
\* LIVENESS PROPERTIES
\* ==========================================================================

(*
 * AllFramesEventuallyReplicated:
 *   Every WAL frame is eventually stored in S3. Under fairness,
 *   the replicator makes progress and S3 eventually confirms.
 *)
AllFramesEventuallyReplicated ==
    \A i \in 1..MaxFrames :
        (Len(walFrames) >= i)
        ~> (walFrames[i] \in s3Frames)

=============================================================================
