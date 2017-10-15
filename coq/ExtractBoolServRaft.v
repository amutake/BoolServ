Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.
From Verdi Require Import Verdi ExtrOcamlBasicExt ExtrOcamlNatIntExt ExtrOcamlBool ExtrOcamlList ExtrOcamlFinInt.
From BoolServ Require Import BoolServRaft.

Extraction "ml/BoolServRaft.ml" seq bool_serv_raft_base_params bool_serv_raft_multi_params bool_serv_raft_failure_params.
