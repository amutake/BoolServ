From Verdi     Require Import Verdi Log.
From Cheerios  Require Import Cheerios Tree.
From VerdiRaft Require Import Raft.
From BoolServ  Require Import BoolServ BoolServRaft BoolServRaftSerializers.

Section Logged.
  Variables n snapshot_interval : nat.

  Instance raft_params : RaftParams BoolServ.bool_serv_base_params :=
    raft_params n.

  Definition transformed_base_params : BaseParams := @log_base_params base_params.
  Definition transformed_multi_params : DiskOpMultiParams transformed_base_params := log_multi_params snapshot_interval.
  Definition transformed_failure_params : DiskOpFailureParams transformed_multi_params := log_failure_params snapshot_interval.
End Logged.
