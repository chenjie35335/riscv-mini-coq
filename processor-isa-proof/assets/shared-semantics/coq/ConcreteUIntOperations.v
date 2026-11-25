From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths Semantics_with_implicit_widths.
Definition concrete_uint_value (value : hvalue) : Prop :=
 exists width bits, value = Gval (Fuint width) bits.
Lemma concrete_uint_binary_basic op wa ba wb bb result :
 eval_binop_basic op (Gval (Fuint wa) ba) (Gval (Fuint wb) bb) = Some result ->
 concrete_uint_value result.
Proof.
 destruct op; cbn [eval_binop_basic]; intro Eval.
 all: try match goal with comparison : bcmp |- _ => destruct comparison end.
 all: inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma concrete_uint_binary op wa ba wb bb result :
 eval_binop op (Gval (Fuint wa) ba) (Gval (Fuint wb) bb) = Some result ->
 concrete_uint_value result.
Proof.
 unfold eval_binop.
 destruct (eval_binop_basic op (Gval (Fuint wa) ba) (Gval (Fuint wb) bb)) as [value|] eqn:Basic.
 - destruct (concrete_uint_binary_basic op wa ba wb bb value Basic) as [width [bits Value]]. subst value.
   unfold refine_boolean_result.
   destruct (absorbing_bit op (Gval (Fuint wa) ba) (Gval (Fuint wb) bb));
   intro Eval; inversion Eval; subst; do 2 eexists; reflexivity.
 - unfold refine_boolean_result.
   destruct (absorbing_bit op (Gval (Fuint wa) ba) (Gval (Fuint wb) bb)); discriminate.
Qed.
Definition x0_uint_unary (op : eunop) : bool :=
 match op with Uextr _ _ | Uorr | Uandr => true | _ => false end.
Lemma concrete_uint_unary op width bits result :
 x0_uint_unary op ->
 eval_unop op (Gval (Fuint width) bits) = Some result ->
 concrete_uint_value result.
Proof.
 destruct op; cbn [x0_uint_unary]; intro Allowed; try discriminate Allowed;
 cbn [eval_unop]; intro Eval.
 all: repeat match type of Eval with context [if ?b then _ else _] => destruct b end.
 all: try discriminate Eval; inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Print Assumptions concrete_uint_binary.
Print Assumptions concrete_uint_unary.
