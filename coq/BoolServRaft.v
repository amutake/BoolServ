Require Import VerdiRaft.Raft.
Require Import BoolServ.BoolServ.

Section BoolServRaft.
  Variable n : nat.

  Instance raft_params : RaftParams bool_serv_base_params :=
    {
      N := n;
      input_eq_dec := input_dec;
      output_eq_dec := output_dec
    }.

  Definition bool_serv_raft_base_params := base_params.
  Definition bool_serv_raft_multi_params := multi_params.
  Definition bool_serv_raft_failure_params := failure_params.
End BoolServRaft.
