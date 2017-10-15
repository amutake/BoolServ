From Verdi     Require Import Verdi.
From VerdiRaft Require Import Raft CommonDefinitions Linearizability
                              RaftLinearizableProofs EndToEndLinearizability.
From BoolServ  Require Import BoolServ BoolServRaft.

Section BoolServRaftCorrect.
  Variable n : nat.

  Instance raft_params : RaftParams BoolServ.bool_serv_base_params :=
    raft_params n.

  Instance base_params : BaseParams :=
    bool_serv_raft_base_params n.

  Instance multi_params : MultiParams _ :=
    bool_serv_raft_multi_params n.

  Instance failure_params : FailureParams _ :=
    bool_serv_raft_failure_params n.

  Theorem bool_serv_raft_linearizable :
    forall failed net tr,
      input_correct tr ->
      step_failure_star step_failure_init (failed, net) tr ->
      exists l tr1 st,
        equivalent _ (import tr) l /\
        exported (get_input tr) (get_output tr) l tr1 /\
        step_1_star init st tr1.
   Proof using.
     exact raft_linearizable.
   Qed.
End BoolServRaftCorrect.
