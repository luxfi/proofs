---------------------------- MODULE MC_ExplorerReplication --------------------
(*
 * Model Checking Wrapper for Explorer WAL Streaming Replication
 *
 * Instantiates ExplorerReplication.tla with concrete constants for
 * tractable model checking.
 *
 * Parameters:
 *   - 2 pages: {1, 2}
 *   - MaxTxid = 3 (TXIDs 0..3)
 *   - MaxFrames = 6 (at most 6 WAL frames)
 *
 * State space analysis:
 *   walFrames: sequences of <<txid, page>> up to length 6
 *   replicatedUpTo: 0..3 (4 values)
 *   checkpointedUpTo: 0..3 (4 values)
 *   s3Frames: subsets of {1..3} x {1,2} = 2^6 = 64
 *   writerTxid: 0..3 (4 values)
 *   snapshotTxid: 0..3 (4 values)
 *   pendingUpload: subsets of {1..3} x {1,2} = 2^6 = 64
 *   With state constraint: explored in seconds.
 *
 * Usage:
 *   TLC:      java -jar tla2tools.jar -config MC_ExplorerReplication.cfg MC_ExplorerReplication
 *   Apalache: apalache-mc check --config=MC_ExplorerReplication.cfg MC_ExplorerReplication.tla
 *)

EXTENDS ExplorerReplication

\* --------------------------------------------------------------------------
\* CONCRETE CONSTANT VALUES
\* --------------------------------------------------------------------------

MC_Pages     == {1, 2}
MC_MaxTxid   == 3
MC_MaxFrames == 6

\* --------------------------------------------------------------------------
\* STATE CONSTRAINT
\* --------------------------------------------------------------------------

(*
 * Bound the WAL length and writer TXID for tractable exploration.
 * The constraint does not cut reachable invariant violations because
 * all interesting behaviors (write, replicate, checkpoint) occur
 * within this bound.
 *)
StateConstraint ==
    /\ Len(walFrames) <= MC_MaxFrames
    /\ writerTxid <= MC_MaxTxid

\* --------------------------------------------------------------------------
\* INVARIANTS
\* --------------------------------------------------------------------------

MC_TypeOK                     == TypeOK
MC_NoFrameLost                == NoFrameLost
MC_CheckpointOnlyReplicated   == CheckpointOnlyReplicated
MC_S3Reconstructible          == S3Reconstructible
MC_MonotonicTxid              == MonotonicTxid
MC_SnapshotBehindReplication  == SnapshotBehindReplication
MC_S3FramesSubsetOfWAL        == S3FramesSubsetOfWAL
MC_PendingSubsetOfWAL         == PendingSubsetOfWAL
MC_NoDuplicateS3              == NoDuplicateS3

\* --------------------------------------------------------------------------
\* TEMPORAL PROPERTIES
\* --------------------------------------------------------------------------

MC_MonotonicCheckpoint    == MonotonicCheckpointAction
MC_MonotonicReplication   == MonotonicReplicationAction

\* Liveness: under fairness all frames reach S3.
\* May produce counterexample if S3 nondeterministically drops confirms.
\* MC_AllFramesReplicated == AllFramesEventuallyReplicated

=============================================================================
