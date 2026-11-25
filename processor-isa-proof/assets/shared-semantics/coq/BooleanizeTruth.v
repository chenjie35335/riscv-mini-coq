Require Import NormalizedBit.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Lemma booleanize_true_source mm env (condition : VarOrder.T) :
 eval_hfexpr_with_memory mm
 (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T condition))
 (@Econst VarOrder.T (Fuint 1) [::true]) (@Econst VarOrder.T (Fuint 1) [::false])) env env = Some (Gval (Fuint 1) [::true]) ->
 exists width bits, VM.find condition env = Some (Gval (Fuint width) bits) /\ is_zero bits = false.
Proof.
 intro Eval. cbn [eval_hfexpr_with_memory eval_href_with_memory] in Eval.
 destruct (VM.find condition env) as [value|] eqn:Lookup; [|discriminate Eval].
 destruct value as [ground bits|element values|fields|ty|ty|ty];
 try destruct ground; try destruct ty.
 all: try match goal with g : fgtyp |- _ => destruct g end.
 all: cbn in Eval; try discriminate Eval.
 destruct (is_zero bits) eqn:Zero; [discriminate Eval|].
 eexists; eexists. split; [reflexivity|exact Zero].
Qed.
Lemma booleanize_result_normalized mm env (condition : VarOrder.T) result :
 eval_hfexpr_with_memory mm
 (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T condition))
 (@Econst VarOrder.T (Fuint 1) [::true]) (@Econst VarOrder.T (Fuint 1) [::false])) env env = Some result ->
 normalized_bit result.
Proof.
 intro Eval. cbn [eval_hfexpr_with_memory eval_href_with_memory] in Eval.
 destruct (VM.find condition env) as [value|] eqn:Lookup; [|discriminate Eval].
 destruct value as [ground bits|element values|fields|ty|ty|ty];
 try destruct ground; try destruct ty.
 all: try match goal with g : fgtyp |- _ => destruct g end.
 all: cbn in Eval; try discriminate Eval.
 all: repeat match type of Eval with context [if ?b then _ else _] => destruct b end.
 all: inversion Eval; subst result; vm_compute; constructor.
Qed.
Print Assumptions booleanize_true_source.
Print Assumptions booleanize_result_normalized.
