Require Import ConcreteUIntOperations.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Inductive uint_scalar_ready (old : VM.t hvalue) : hfexpr VarOrder.T -> Prop :=
| uint_ready_const width bits : uint_scalar_ready old (@Econst VarOrder.T (Fuint width) bits)
| uint_ready_ref id width bits : VM.find id old = Some (Gval (Fuint width) bits) -> uint_scalar_ready old (Eref (Eid id))
| uint_ready_unary op e : x0_uint_unary op -> uint_scalar_ready old e -> uint_scalar_ready old (Eprim_unop op e)
| uint_ready_binary op a b : uint_scalar_ready old a -> uint_scalar_ready old b -> uint_scalar_ready old (Eprim_binop op a b).
Theorem formal_uint_scalar_concrete invalid mm old expression :
 uint_scalar_ready old expression ->
 forall site result, eval_hfexpr_validif_policy invalid site mm expression old old = Some result -> concrete_uint_value result.
Proof.
 intro Ready. induction Ready as [width bits|id width bits Lookup|op e Allowed Ready IH|op a b A IHA B IHB]; intros site result Eval.
 - cbn [eval_hfexpr_validif_policy] in Eval.
   repeat match type of Eval with context [if ?b then _ else _] => destruct b end;
   try discriminate Eval; inversion Eval; subst; do 2 eexists; reflexivity.
 - cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
   rewrite Lookup in Eval. inversion Eval; subst; do 2 eexists; reflexivity.
 - cbn [eval_hfexpr_validif_policy] in Eval.
   destruct (eval_hfexpr_validif_policy invalid _ mm e old old) as [value|] eqn:E; [|discriminate Eval].
   destruct (IH _ _ E) as [w [bits V]]. subst value.
   exact (concrete_uint_unary op w bits result Allowed Eval).
 - cbn [eval_hfexpr_validif_policy] in Eval.
   destruct (eval_hfexpr_validif_policy invalid _ mm a old old) as [va|] eqn:EA; [|discriminate Eval].
   destruct (eval_hfexpr_validif_policy invalid _ mm b old old) as [vb|] eqn:EB; [|discriminate Eval].
   destruct (IHA _ _ EA) as [wa [ba VA]].
   destruct (IHB _ _ EB) as [wb [bb VB]]. subst va vb.
   exact (concrete_uint_binary op wa ba wb bb result Eval).
Qed.
Print Assumptions formal_uint_scalar_concrete.
