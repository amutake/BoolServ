Require Import Bool.
From mathcomp Require Import ssreflect.
From Verdi Require Import Verdi StateMachineHandlerMonad.

Inductive input : Set :=
| Get : input
| Put : bool -> input.

Inductive output : Set :=
| Res : bool -> output.

Theorem input_dec : forall x y : input, {x = y} + {x <> y}.
Proof.
  decide equality.
  auto using bool_dec.
Qed.

Theorem output_dec : forall x y : output, {x = y} + {x <> y}.
Proof.
  decide equality.
  auto using bool_dec.
Qed.

Definition data := bool.

(* GenHandler1 は要は state モナド。第二節の stdio のようなもの。StateMachineHandlerMonad にある。 *)

(* StateMachineHandlerMonad の get, put を再定義しているだけ。 *)
Definition get : GenHandler1 data bool := get.

Definition put (b : bool) : GenHandler1 data unit := put b.

Definition res (b : bool) : GenHandler1 data output := write_output (Res b).

Definition BoolServHandler' (inp : input) : GenHandler1 data output :=
  match inp with
  | Get => b <- get ;; res b
  | Put b => put b ;; res b
  end.

Definition runHandler
           (h : input -> GenHandler1 data output)
           (inp : input)
           (b : data) : output * data :=
  runGenHandler1 b (h inp).     (* runGenHandler1 <初期値> <GenHandler1> *)

Definition BoolServHandler := runHandler BoolServHandler'.

Definition init := false.

(* 各種型定義を与える。型クラスになっている *)
Instance bool_serv_base_params : BaseParams :=
  {
    data := data;
    input := input;
    output := output
  }.

(* シングルノードのインスタンスを作る *)
Instance bool_serv_one_node_params : OneNodeParams _ :=
  {
    init := init;
    handler := BoolServHandler
  }.

Definition trace := list (input * output).

(* 先頭が後に来た処理 *)
Fixpoint interpret (ops : list input) (ini : data) :=
  match ops with
  | [] => ini
  | Get :: ops => interpret ops ini
  | Put b :: ops => b           (* 最後に Put された値を採用 *)
  end.

Definition trace_inputs (t : trace) : list input := map fst t.

Inductive trace_correct : data -> trace -> Prop :=
| TCnil : forall b, trace_correct b []
| TCsnoc : forall ini t i b,
    trace_correct ini t ->
    interpret (i :: rev (trace_inputs t)) ini = b ->
    trace_correct ini (t ++ [(i, Res b)]).
Hint Constructors trace_correct.

Definition trace_state_correct (ini cur : data) (t : trace) :=
  interpret (rev (trace_inputs t)) ini = cur.

Lemma trace_inputs_rev :
  forall t i o, rev (trace_inputs (t ++ [(i, o)])) = i :: rev (trace_inputs t).
Proof.
  elim=> //= a l IH i o.
  move: IH -> => //=.
Qed.

Lemma step_1_star_trace_state_correct :
  forall ini cur t,
    step_1_star ini cur t ->
    trace_state_correct ini cur t.
Proof.
  move=> ini cur t star.
  find_apply_lem_hyp refl_trans_1n_n1_trace.
  elim: star=> //= x x' x'' cs cs' star IH one.
  unfold trace_state_correct in *.
  invcs one.
  move: H; case: i=> [|b]; rewrite trace_inputs_rev=> /=; by case.
Qed.

Lemma trace_state_correct_trace_correct :
  forall st st' st'' t t',
    trace_state_correct st st' t ->
    trace_correct st t ->
    step_1 st' st'' t' ->
    trace_correct st (t ++ t').
Proof.
  move=> st st' st'' t t' st_correct correct one.
  invcs correct.
  - move: st_correct; rewrite/trace_state_correct=> /= ->.
    invcs one.
    move: H; case: out=> b; case: i=> [|b'] //=; case=> <- ->; rewrite <- app_nil_l; repeat constructor.
  - unfold trace_state_correct in st_correct.
    rewrite trace_inputs_rev in st_correct.
    invcs one.
    move: H0; case: out=> b H0; repeat constructor=> //.
    rewrite trace_inputs_rev.
    move: H0; case: i=> [|b']; case: i0=> [|b'']; case=> //=.
Qed.

Theorem step_1_star_trace_correct :
  forall ini cur t,
    step_1_star ini cur t ->
    trace_correct ini t.
Proof.
  move=> ini cur trace star.
  find_apply_lem_hyp refl_trans_1n_n1_trace.
  elim: star=> [st | st st' st'' cs cs' star IH one] //=.
  find_apply_lem_hyp refl_trans_n1_1n_trace.
  apply step_1_star_trace_state_correct in star.
  apply/trace_state_correct_trace_correct=> //=.
  rewrite star.
  apply one.
Qed.
