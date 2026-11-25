Require Import ConcreteGroundOperations ConcreteScalarExpressions.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Lemma scalar_formal_evaluation_equal invalid mm old expression :
 scalar_expression_ready old expression ->
 forall site, eval_hfexpr_validif_policy invalid site mm expression old old = eval_hfexpr_with_memory mm expression old old.
Proof.
 intro Ready. induction Ready as [ground bits|id ground bits Lookup|op arg Ready IH|op left right Left IHLeft Right IHRight|cast arg Ready IH]; intro site.
 - reflexivity.
 - reflexivity.
 - cbn [eval_hfexpr_validif_policy eval_hfexpr_with_memory]. rewrite IH. reflexivity.
 - cbn [eval_hfexpr_validif_policy eval_hfexpr_with_memory]. rewrite IHLeft IHRight. reflexivity.
 - destruct cast; cbn [eval_hfexpr_validif_policy eval_hfexpr_with_memory]; rewrite IH; reflexivity.
Qed.
Theorem formal_concrete_scalar_expression invalid site mm old expression result :
 scalar_expression_ready old expression ->
 eval_hfexpr_validif_policy invalid site mm expression old old = Some result ->
 concrete_ground_value result.
Proof.
 intros Ready Eval.
 rewrite (scalar_formal_evaluation_equal invalid mm old expression Ready site) in Eval.
 exact (concrete_scalar_expression mm old expression Ready result Eval).
Qed.
Print Assumptions formal_concrete_scalar_expression.
