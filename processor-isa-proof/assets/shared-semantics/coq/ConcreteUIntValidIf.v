Require Import ConcreteUIntOperations ConcreteUIntScalarExpressions.
From nbits Require Import NBits.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Theorem formal_uint_validif_concrete inputs path mm old condition body width :
 uint_scalar_ready old condition ->
 uint_scalar_ready old body ->
 eval_type_of_expr body old = Some (Gtyp (Fuint width)) ->
 forall site result,
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm (Evalidif condition body) old old = Some result ->
 concrete_uint_value result.
Proof.
 intros Condition Body Typed site result Eval.
 cbn [eval_hfexpr_validif_policy] in Eval. rewrite Typed in Eval.
 destruct (eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) (rcons site 0) mm condition old old)
 as [value|] eqn:Cond; [|discriminate Eval].
 destruct (formal_uint_scalar_concrete _ mm old condition Condition _ value Cond) as [w [bits Value]]. subst value.
 cbn [validif_policy_result] in Eval. destruct (is_zero bits).
 - inversion Eval; subst result.
   unfold isolated_validif_policy, formal_invalid_policy. cbn [input_value_of_type]. do 2 eexists. reflexivity.
 - exact (formal_uint_scalar_concrete _ mm old body Body _ result Eval).
Qed.
Print Assumptions formal_uint_validif_concrete.
