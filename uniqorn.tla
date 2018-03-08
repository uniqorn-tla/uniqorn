------------------------------ MODULE uniqorn ------------------------------
(************************************************************************************)
(* a fully-fledged specification for uniqorn. A CRUD operation consists of multiple *)
(* phases. There are infinite many clients. Each client can issue any CRUD operation*)
(* to the queue by enqueuing the first phase of the operation into the queue. The   *)
(* state machine (which is modeled by this specification) will randomly pick  up    *)
(* any phase of any operation in the queue and execute this phase according to the  *)
(* uniqorn protocol described in the draft paper. When an operation finishes a given*)
(* phase, it queues the next phase.  However, it does not remove the completed phase*)
(* from the queue. As a result, the completed phase can be picked up and run again  *)
(* All of these are intentionally designed to emulate a packet-lost, duplicate,     *)
(* reorder, delayed network/distributed environment.                                *)
(*                                                                                  *)
(* create/update operations that reuse an alternate key of a garbage index record   *)
(* will not directly delete the garbage index record. Only the garbage cleanup      *)
(* can delete a garbage index record. This behavior has the same effect (since TLA  *)
(* model checking will exhaust all state paths) as each create/update mandatorily   *)
(* delete garbage index record and then insert its own index record                 *)
(*                                                                                  *)
(* data store or index store partitioning policy does not affect the protocol, so   *)
(* we do not even express them in this specification                                *)
(************************************************************************************)

(************************************************************************************)
(* an example model values                                                          *)
(* PERSIST_INDEX_RECORD, PERSIST_DATA_RECORD : model value                          *)
(* CLEANUP_VALIDATE, CLEANUP_CHANGE_LOCK, CLEANUP_DELETE_GARBAGE: model value       *)
(* AKS: 1..16                                                                       *)
(* PKS: 1..8                                                                        *)
(* VAL: 1                                                                           *)
(* AKS_PER_RECORD: 2                                                                *)
(* PLEASE ALSO SET THE FOLLOWING STATE CONSTRAINTS TO LIMIT THE STATE SPACE, e.g.   *)
(* uuid < 32                                                                        *)
(************************************************************************************)

EXTENDS TLC, Integers, Sequences, FiniteSets, Bags

\* phases for create and update, the first phase "read data record" or "init a dummy data record" is omitted
\* since it is done at the time when a create or update operation is initiated
CONSTANTS PERSIST_INDEX_RECORD, PERSIST_DATA_RECORD

\* phases for cleanup, the first phase "read index record" is omitted since it is done when a cleanup operation is initiated
CONSTANTS CLEANUP_VALIDATE, CLEANUP_CHANGE_LOCK, CLEANUP_DELETE_GARBAGE

\* a delete operation has only one phase, it can be done when the delete operation is initiated, so we omit it

\* set of integer keys for primary keys and alternate keys 
CONSTANTS PKS, AKS

\*a non-zero integer, 0 means the val is null/empty, other values means non-empty value
CONSTANTS VAL

\*the number of aks per record, a record can have 0 to AK_PER_RECORD alternate keys
CONSTANTS AKS_PER_RECORD

\* data or index records in data store partitions or index store partitions
VARIABLES persistedDataRecords, persistedIndexRecords

\* seperate queues for all create/update and clenaup operations, delete has only one phase, no need a queue for it.
\* an operation can equeue its next phase as it progresses. All create and update operations
\* share the same queue since they follow the same protocol after their  initial phases, respectively
VARIABLES inprogressCreateUpdates, inprogressCleanups

\* a monotonically increasing integer as a uuid, which will be used as epoch values.
\* For any two epoch values, their relations are only equality and inequality, no other relation exists
\* like greater than, less than, etc. That is, we don't use the monotonicity of the integers for any use
VARIABLES uuid

RECURSIVE Cat(_)
Cat(akset) ==
         IF(Cardinality(akset) = 0) THEN <<>> ELSE
              LET akchosen == (CHOOSE ak \in akset : TRUE)
              IN Append(Cat(akset \ {akchosen}), akchosen)

\*the catenation of all aks in a sequence
AkSeq == Cat(AKS)

\*randomly choose a set of aks from the provided AKs, can be empty too
ChooseAKs(akCount) ==
  LET chooseAk[i \in 0..akCount] ==
    IF i = 0 THEN {} ELSE chooseAk[i-1] \cup {AkSeq[RandomElement(1..Len(AkSeq))]}
  IN chooseAk[akCount]

(*********************data store accesses start here**************************************)
IsDummy(pk) == IF /\ pk \in DOMAIN persistedDataRecords
                  /\ persistedDataRecords[pk].aks = {}
                  /\ persistedDataRecords[pk].val = 0
               THEN TRUE
               ELSE FALSE

isLockHeld(pk, epoch, version) == IF /\ pk \in DOMAIN persistedDataRecords
                        /\ persistedDataRecords[pk].epoch = epoch
                        /\ persistedDataRecords[pk].version = version
                     THEN TRUE
                     ELSE FALSE

DataStoreDelete(pk) ==
  /\ pk \in DOMAIN persistedDataRecords
  /\ persistedDataRecords' = [key \in (DOMAIN persistedDataRecords \ {pk}) |->
                                                               persistedDataRecords[key]]
  /\ UNCHANGED <<persistedIndexRecords, inprogressCreateUpdates, inprogressCleanups>>

DataStoreInitLock(pk, aks, epoch, version) ==
   \/ /\ pk \notin DOMAIN persistedDataRecords
      /\ persistedDataRecords' = persistedDataRecords @@ (pk :> [pk|->pk, epoch|->epoch,
                                                      version|->version, aks|->{}, val|->0])
      /\ inprogressCreateUpdates' = inprogressCreateUpdates \cup {[phase |-> PERSIST_INDEX_RECORD,
            pk|->pk, newAks|->aks, prevAks|->{}, upsertAks|->{}, epoch|->epoch, version|->version]}
         \/  /\ IsDummy(pk)
             /\ persistedDataRecords' = [persistedDataRecords EXCEPT ![pk].epoch = epoch,
                                 !    [pk].version = version, ![pk].aks = {}, ![pk].val=0]
             /\ inprogressCreateUpdates' = inprogressCreateUpdates \cup {[
                     phase |-> PERSIST_INDEX_RECORD, pk |-> pk, newAks |-> aks, prevAks |-> {},
                                          upsertAks |-> {}, epoch|->epoch, version|->version]}
         \/  UNCHANGED <<persistedDataRecords, inprogressCreateUpdates>>

DataStoreUpdateOptimistically(pk, aks, epoch, version) ==
     \/ /\ isLockHeld(pk, epoch, version)
        /\ persistedDataRecords' = [persistedDataRecords EXCEPT ![pk].version = @ + 1,
                                                        ![pk].aks = aks, ![pk].val = VAL]
     \/ UNCHANGED persistedDataRecords

DataStoreValidate(pk, ak, epoch, version) ==
   IF pk \in DOMAIN persistedDataRecords  /\ (ak \in  persistedDataRecords[pk].aks) THEN
         UNCHANGED inprogressCleanups
   ELSE inprogressCleanups' = inprogressCleanups \cup {[phase |-> CLEANUP_CHANGE_LOCK, pk |-> pk,
                                                      ak |-> ak, epoch|->epoch, version|->version]}

DataStoreChangeLock(pk, ak, epoch, version) ==
   IF pk \in DOMAIN persistedDataRecords THEN
     IF ak \notin persistedDataRecords[pk].aks THEN
       /\ IF persistedDataRecords[pk].val = 0 THEN
             persistedDataRecords' = [key \in (DOMAIN persistedDataRecords \ {pk}) |->
                                                               persistedDataRecords[key]]
          ELSE
            persistedDataRecords' = [persistedDataRecords EXCEPT ![pk].version = @ + 1]
       /\ inprogressCleanups' = inprogressCleanups \cup {[phase |-> CLEANUP_CHANGE_LOCK, pk |-> pk,
                                                        ak |-> ak, epoch|->epoch, version|->version]}
     ELSE UNCHANGED <<persistedDataRecords, inprogressCleanups>>
   ELSE
     /\ inprogressCleanups' = inprogressCleanups \cup {[phase |-> CLEANUP_DELETE_GARBAGE,
                                        pk |-> pk, ak |-> ak, epoch|->epoch, version|->version]}
     /\ UNCHANGED persistedDataRecords

(*********************data store accesses end here*************************************)

(*********************index store accesses start here**********************************)
\*index store has only two accesses methods: insert and delete. Update and replace accesses can be derived from these two.
IndexStoreDirectlyInsert(pk, epoch, version, prevAks, newAks,  upsertAks) ==
   /\ upsertAks # newAks \ prevAks
   /\ LET ak == (CHOOSE anyAk \in (newAks \ prevAks): TRUE)
      IN \/ /\ ak \notin DOMAIN persistedIndexRecords
            /\ persistedIndexRecords' = persistedIndexRecords  @@ (ak :> [ak |-> ak,
                                              pk |-> pk, epoch|->epoch, version|->version])
            /\ \/ /\ (newAks \ prevAks) = (upsertAks \cup {ak})
                  /\ inprogressCreateUpdates' = inprogressCreateUpdates \cup {[
                                      phase|->PERSIST_DATA_RECORD, pk|->pk, aks|->newAks,
                                                    epoch|->epoch, version  |->version]}
               \/ /\ (newAks \ prevAks) # (upsertAks \cup {ak})
                  /\ inprogressCreateUpdates' = inprogressCreateUpdates \cup {[phase |->
                   PERSIST_INDEX_RECORD, pk |-> pk, newAks |-> newAks, prevAks |-> prevAks,
                      upsertAks |-> (upsertAks \cup {ak}), epoch|->epoch, version|->version]}
               \/ UNCHANGED <<persistedIndexRecords, inprogressCreateUpdates>>

IndexStoreDeleteOptimistically(ak, pk, epoch, version) ==
    IF /\ ak \in DOMAIN persistedIndexRecords
       /\ persistedIndexRecords[ak].pk = pk
       /\ persistedIndexRecords[ak].epoch = epoch
       /\ persistedIndexRecords[ak].version = version
    THEN
       persistedIndexRecords' = [key \in (DOMAIN persistedIndexRecords \ {ak})
                                                          |-> persistedIndexRecords[key]]
    ELSE UNCHANGED persistedIndexRecords

(*********************index store accesses end here**********************************)

(*********************various operations start here**********************************)
\*issue a create operation
Create(pk, aks) ==
    /\ inprogressCreateUpdates' = inprogressCreateUpdates \cup {[phase |-> PERSIST_INDEX_RECORD,
                pk |-> pk, prevAks |-> {}, newAks|->aks, upsertAks |-> {}, epoch|->uuid, version|->0]}
    /\ UNCHANGED <<persistedDataRecords, persistedIndexRecords, inprogressCleanups>>

\*issue an update operation
Update(pk, epoch, version, prevAks, newAks) ==
    /\ inprogressCreateUpdates' = inprogressCreateUpdates \cup {[phase |-> PERSIST_INDEX_RECORD,
                              pk  |-> pk, prevAks |-> prevAks, newAks |-> newAks, upsertAks |-> {},
                                                             eopch |-> epoch, version |-> version]}
    /\ UNCHANGED <<persistedDataRecords, persistedIndexRecords, inprogressCleanups>>

\*issue a cleanup operation
Cleanup(ak, pk, epoch, version) ==
    /\ inprogressCleanups' = inprogressCleanups \cup {[phase |-> CLEANUP_VALIDATE, ak |-> ak,
                                              pk |-> pk, epoch |-> epoch, version |-> version]}
    /\ UNCHANGED <<persistedDataRecords, persistedIndexRecords, inprogressCreateUpdates>>

\*make a create/update operation go through its phases
RunCreateUpdate(op) ==
    LET phase == op.phase
        pk == op.pk
        epoch == op.epoch
        version == op.version
    IN \/ /\ phase = PERSIST_INDEX_RECORD
          /\ LET prevAks == op.prevAks
                 newAks == op.newAks
                 upsertAks == op.upsertAks
             IN /\ IndexStoreDirectlyInsert(pk, epoch, version, prevAks, newAks, upsertAks)
                /\ UNCHANGED <<persistedDataRecords, inprogressCleanups>>
       \/ /\ phase = PERSIST_DATA_RECORD
          /\ DataStoreUpdateOptimistically(pk, op.aks, epoch, version)
          /\ UNCHANGED <<persistedIndexRecords, inprogressCleanups, inprogressCreateUpdates>>


\*make a garbage cleanup operation go through its phases
RunCleanup(cleanupOp) ==
    LET phase == cleanupOp.phase
        pk == cleanupOp.pk
        ak == cleanupOp.ak
        epoch == cleanupOp.epoch
        version == cleanupOp.version
    IN \/ /\ phase = CLEANUP_VALIDATE
          /\ DataStoreValidate(pk, ak, epoch, version)
          /\ UNCHANGED <<persistedDataRecords, persistedIndexRecords, inprogressCreateUpdates>>
       \/ /\ phase = CLEANUP_CHANGE_LOCK
          /\ DataStoreChangeLock(pk, ak, epoch, version)
          /\ UNCHANGED <<persistedIndexRecords, inprogressCreateUpdates>>
       \/ /\ phase = CLEANUP_DELETE_GARBAGE
          /\ IndexStoreDeleteOptimistically(ak, pk, epoch, version)
          /\ UNCHANGED <<persistedDataRecords, inprogressCreateUpdates, inprogressCleanups>>

(*********************various operations end here**********************************)

(*********************state machine starts here************************************)
\* all aks and pks are initialized in each partition
Init == /\ persistedDataRecords  = [pk \in {} |-> {}]
        /\ persistedIndexRecords = [ak \in {} |-> {}]
        /\ inprogressCreateUpdates = {}
        /\ inprogressCleanups = {}
        /\ uuid = 0

\*next-state actions
Next == /\ \/ \E pk \in PKS : DataStoreDelete(pk)
           \/ \E pk \in PKS: Create(pk, ChooseAKs(AKS_PER_RECORD))
           \/ \E ak \in DOMAIN persistedIndexRecords : Cleanup(ak, persistedIndexRecords[ak].pk,
                       persistedIndexRecords[ak].epoch, persistedIndexRecords[ak].version)
           \/ \E pk \in DOMAIN persistedDataRecords: Update(pk, persistedDataRecords[pk].epoch,
                          persistedDataRecords[pk].version, persistedDataRecords[pk].aks,
                                                                ChooseAKs(AKS_PER_RECORD))
           \/ \E createUpdateOp \in inprogressCreateUpdates :  RunCreateUpdate(createUpdateOp)
           \/ \E cleanupOp \in inprogressCleanups :  RunCleanup(cleanupOp)
        /\ uuid' = uuid + 1

\* specification
Spec == Init /\ [][Next]_<<persistedDataRecords, persistedIndexRecords, inprogressCleanups,
                                                           inprogressCreateUpdates, uuid>>
(*********************state machine ends here**************************************)

\* no missing index record invariant
NoMissing == \A pk \in DOMAIN persistedDataRecords :
               IF persistedDataRecords[pk].ak # 0 THEN
                   \E ak \in DOMAIN persistedIndexRecords :
                      /\ persistedIndexRecords[ak].pk = pk
                      /\ persistedDataRecords[pk].ak = ak
               ELSE TRUE

THEOREM Spec => NoMissing
=============================================================================
\* Modification History
\* Last modified Wed Mar 07 17:10:06 PST 2018 by jyi
\* Created Mon Feb 05 09:28:50 PST 2018 by jyi
