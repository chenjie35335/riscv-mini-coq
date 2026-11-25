Require Import ConcreteGroundOperations.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths Semantics_with_implicit_widths.
Lemma concrete_binary_basic_result op left_type left_bits right_type right_bits result :
 eval_binop_basic op (Gval left_type left_bits) (Gval right_type right_bits) = Some result ->
 concrete_ground_value result.
Proof.
 destruct left_type; destruct right_type; destruct op;
 cbn [eval_binop_basic]; intro Eval; try discriminate Eval.
 all: try match goal with x : bcmp |- _ => destruct x end.
 all: cbn in Eval; try discriminate Eval; inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma concrete_binary_result op left_type left_bits right_type right_bits result :
 eval_binop op (Gval left_type left_bits) (Gval right_type right_bits) = Some result ->
 concrete_ground_value result.
Proof.
 unfold eval_binop.
 destruct (eval_binop_basic op (Gval left_type left_bits) (Gval right_type right_bits)) as [value|] eqn:Basic.
 - destruct (concrete_binary_basic_result op left_type left_bits right_type right_bits value Basic) as [ground [bits Value]].
   subst value. unfold refine_boolean_result.
   destruct (absorbing_bit op (Gval left_type left_bits) (Gval right_type right_bits));
   intro Eval; inversion Eval; subst; do 2 eexists; reflexivity.
 - unfold refine_boolean_result.
   destruct (absorbing_bit op (Gval left_type left_bits) (Gval right_type right_bits)); discriminate.
Qed.
Print Assumptions concrete_binary_result.
