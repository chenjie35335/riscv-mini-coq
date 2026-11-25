From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths Semantics_with_implicit_widths.
Definition concrete_ground_value (value : hvalue) : Prop :=
 exists ground bits, value = Gval ground bits.
Lemma concrete_unary_result op ground bits result :
 eval_unop op (Gval ground bits) = Some result -> concrete_ground_value result.
Proof.
 destruct op; destruct ground; cbn [eval_unop]; intro Eval;
 try discriminate Eval.
 all: repeat match type of Eval with context [if ?b then _ else _] => destruct b end.
 all: try match type of Eval with (match ?x with O => _ | S _ => _ end) = _ => destruct x end.
 all: try discriminate Eval; inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Print Assumptions concrete_unary_result.
