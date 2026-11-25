Require Import ConcreteGroundOperations ConcreteBinaryOperations.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Inductive scalar_expression_ready (old : VM.t hvalue) : hfexpr VarOrder.T -> Prop :=
 | scalar_ready_const ground bits : scalar_expression_ready old (@Econst VarOrder.T ground bits)
 | scalar_ready_ref id ground bits : VM.find id old = Some (Gval ground bits) -> scalar_expression_ready old (Eref (Eid id))
 | scalar_ready_unary op arg : scalar_expression_ready old arg -> scalar_expression_ready old (Eprim_unop op arg)
 | scalar_ready_binary op left right : scalar_expression_ready old left -> scalar_expression_ready old right -> scalar_expression_ready old (Eprim_binop op left right)
 | scalar_ready_cast cast arg : scalar_expression_ready old arg -> scalar_expression_ready old (Ecast cast arg).
Theorem concrete_scalar_expression mm old expression :
 scalar_expression_ready old expression ->
 forall result, eval_hfexpr_with_memory mm expression old old = Some result -> concrete_ground_value result.
Proof.
 intro Ready. induction Ready as [ground bits|id ground bits Lookup|op arg Ready IH|op left right Left IHLeft Right IHRight|cast arg Ready IH]; intros result Eval.
 - { cbn [eval_hfexpr_with_memory] in Eval. destruct ground; try discriminate Eval.
   all: repeat match type of Eval with context [if ?b then _ else _] => destruct b end.
   all: try discriminate Eval; inversion Eval; subst; do 2 eexists; reflexivity. }
 - cbn [eval_hfexpr_with_memory eval_href_with_memory] in Eval. rewrite Lookup in Eval. inversion Eval; subst. do 2 eexists; reflexivity.
 - cbn [eval_hfexpr_with_memory] in Eval.
   destruct (eval_hfexpr_with_memory mm arg old old) as [value|] eqn:Arg; [|discriminate Eval].
   destruct (IH value (Logic.eq_refl _)) as [ground [bits Value]]. subst value.
   exact (concrete_unary_result op ground bits result Eval).
 - cbn [eval_hfexpr_with_memory] in Eval.
   destruct (eval_hfexpr_with_memory mm left old old) as [a|] eqn:A; [|discriminate Eval].
   destruct (eval_hfexpr_with_memory mm right old old) as [b|] eqn:B; [|discriminate Eval].
   destruct (IHLeft a (Logic.eq_refl _)) as [ga [ba VA]].
   destruct (IHRight b (Logic.eq_refl _)) as [gb [bb VB]]. subst a b.
   exact (concrete_binary_result op ga ba gb bb result Eval).
 - destruct cast; cbn [eval_hfexpr_with_memory] in Eval;
   destruct (eval_hfexpr_with_memory mm arg old old) as [value|] eqn:Arg; try discriminate Eval;
   destruct (IH value (Logic.eq_refl _)) as [ground [bits Value]]; subst value;
   destruct ground; try discriminate Eval; inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Print Assumptions concrete_scalar_expression.
