Require Import RegisterInvariants.
From simplssrlib Require Import Var.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From firrtl Require Import HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.

Lemma staged_finish_false_equal : forall stmts invalid scope position mm old current eval,
 formal_finish_registers invalid scope position mm old false current stmts =
 finish_registers eval old false current stmts.
Proof.
 fix IH 1. intros stmts invalid scope position mm old current eval.
 destruct stmts as [|st tail]; [reflexivity|].
 destruct st as [|w t|r reg|m mem|inst target|node expr|lhs rhs|ref|cond yes no];
 cbn [formal_finish_registers finish_registers]; try apply IH.
 - destruct (VM.find r old); [|reflexivity].
   destruct (VM.find r current); [apply IH|reflexivity].
 - rewrite (IH yes invalid (scope ++ [::position;0]) 0 mm old current eval).
   destruct (finish_registers eval old false current yes) as [after_yes|]; [|reflexivity].
   rewrite (IH no invalid (scope ++ [::position;1]) 0 mm old after_yes eval).
   destruct (finish_registers eval old false after_yes no); [apply IH|reflexivity].
Qed.

Theorem staged_combinational_holds_registers invalid mm old current result stmts id :
 has_register id stmts = true ->
 formal_value_iter invalid mm old false current stmts = Some result ->
 VM.find id result = VM.find id old.
Proof.
 intros Register Step. unfold formal_value_iter in Step.
 destruct (formal_statements invalid [::] 0 mm old false current stmts)
   as [proposed|]; [|discriminate Step].
 rewrite (staged_finish_false_equal stmts invalid [::] 0 mm old proposed
   (fun e => eval_hfexpr_with_memory mm e old old)) in Step.
 eapply finish_false_holds_registers; eassumption.
Qed.
Print Assumptions staged_combinational_holds_registers.
