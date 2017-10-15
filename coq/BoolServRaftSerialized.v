From Verdi     Require Import Verdi SerializedMsgParams.
From Cheerios  Require Import Cheerios.
From VerdiRaft Require Import Raft.
From BoolServ  Require Import BoolServRaft BoolServRaftSerializers.

Section Serialized.
  Variable n : nat.

  Instance raft_params : RaftParams BoolServ.bool_serv_base_params :=
    raft_params n.

  Definition orig_base_params := base_params.
  Definition orig_multi_params := multi_params.
  Definition orig_failure_params := failure_params.

  Definition transformed_base_params :=
    @serialized_base_params orig_base_params.

  Definition transformed_multi_params :=
    @serialized_multi_params orig_base_params orig_multi_params (msg_Serializer n).

  Definition transformed_failure_params :=
    @serialized_failure_params orig_base_params orig_multi_params orig_failure_params (msg_Serializer n).
End Serialized.
