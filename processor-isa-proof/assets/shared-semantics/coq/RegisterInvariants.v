From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var FMaps.
From firrtl Require Import HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Module RegisterMapFacts := FMapLemmas VM.

Lemma restore_preserves_agreement (old_map current : VM.t hvalue) id name value :
 VM.find id current = VM.find id old_map ->
 VM.find name old_map = Some value ->
 VM.find id (VM.add name value current) = VM.find id old_map.
Proof.
 intros Hagree Hname.
 case E: (id == name).
 - move/eqP: E => E. subst id.
   rewrite (RegisterMapFacts.find_add_eq (eqxx name)). symmetry. exact Hname.
 - rewrite RegisterMapFacts.find_add_neq; [exact Hagree|].
   change (~ (id == name)). rewrite E. discriminate.
Qed.

Lemma finish_false_preserves_agreement : forall (stmts : HiF.hfstmt_seq)
 (eval : HiF.hfexpr -> option hvalue) old_map current result id,
 VM.find id current = VM.find id old_map ->
 finish_registers eval old_map false current stmts = Some result ->
 VM.find id result = VM.find id old_map.
Proof.
 fix IH 1.
 intros stmts eval old_map current result id Hagree Hfinish.
 destruct stmts as [|st tl].
 - cbn [finish_registers] in Hfinish. inversion Hfinish; subst. exact Hagree.
 - destruct st as [|w t|r reg|m mem|inst target|node expr|lhs rhs|ref|cond yes no];
   cbn [finish_registers] in Hfinish;
   try (eapply IH; [exact Hagree | exact Hfinish]).
   + destruct (VM.find r old_map) as [old_value|] eqn:Hlookup; [|discriminate Hfinish].
     destruct (VM.find r current) as [proposed|]; [|discriminate Hfinish].
     eapply IH; [|exact Hfinish].
     eapply restore_preserves_agreement; eassumption.
   + destruct (finish_registers eval old_map false current yes) as [after_yes|] eqn:Hyes;
       [|discriminate Hfinish].
     destruct (finish_registers eval old_map false after_yes no) as [after_no|] eqn:Hno;
       [|discriminate Hfinish].
     eapply IH; [|exact Hfinish].
     eapply IH; [|exact Hno].
     eapply IH; [exact Hagree|exact Hyes].
Qed.

Fixpoint has_register (id : VarOrder.T) (stmts : HiF.hfstmt_seq) : bool :=
 match stmts with
 | Qnil => false
 | Qcons st tl =>
   (match st with
    | Sreg name _ => id == name
    | Swhen _ yes no => has_register id yes || has_register id no
    | _ => false end) || has_register id tl
 end.

Lemma finish_false_holds_registers : forall (stmts : HiF.hfstmt_seq)
 (eval : HiF.hfexpr -> option hvalue) old_map current result id,
 has_register id stmts = true ->
 finish_registers eval old_map false current stmts = Some result ->
 VM.find id result = VM.find id old_map.
Proof.
 fix IH 1.
 intros stmts eval old_map current result id Hreg Hfinish.
 destruct stmts as [|st tl]; [discriminate Hreg|].
 destruct st as [|w t|r reg|m mem|inst target|node expr|lhs rhs|ref|cond yes no];
   cbn [finish_registers] in Hfinish;
   cbn [has_register] in Hreg;
   try (eapply IH; [exact Hreg|exact Hfinish]).
 - destruct (VM.find r old_map) as [old_value|] eqn:Hlookup; [|discriminate Hfinish].
   destruct (VM.find r current) as [proposed|]; [|discriminate Hfinish].
   move/orP: Hreg => [Heq|Htail].
   + move/eqP: Heq => Heq. subst id.
     eapply finish_false_preserves_agreement; [|exact Hfinish].
     rewrite (RegisterMapFacts.find_add_eq (eqxx r)). symmetry. exact Hlookup.
   + eapply IH; [exact Htail|exact Hfinish].
 - destruct (finish_registers eval old_map false current yes) as [after_yes|] eqn:Hyes;
     [|discriminate Hfinish].
   destruct (finish_registers eval old_map false after_yes no) as [after_no|] eqn:Hno;
     [|discriminate Hfinish].
   move/orP: Hreg => [Hbranches|Htail].
   + move/orP: Hbranches => [Hy|Hn].
     * eapply finish_false_preserves_agreement; [|exact Hfinish].
       eapply finish_false_preserves_agreement; [|exact Hno].
       eapply IH; [exact Hy|exact Hyes].
     * eapply finish_false_preserves_agreement; [|exact Hfinish].
       eapply IH; [exact Hn|exact Hno].
   + eapply IH; [exact Htail|exact Hfinish].
Qed.

Theorem policy_combinational_iteration_holds_registers : forall invalid mm old_map current result stmts id,
 has_register id stmts = true ->
 value_iter_with_memory_policy invalid mm old_map false current stmts = Some result ->
 VM.find id result = VM.find id old_map.
Proof.
 intros invalid mm old_map current result stmts id Hreg Hstep.
 unfold value_iter_with_memory_policy in Hstep.
 destruct (value_iter_statements_with_memory_policy invalid [::] 0 mm old_map false current stmts)
   as [proposed|]; [|discriminate Hstep].
 eapply finish_false_holds_registers; eassumption.
Qed.

Corollary formal_combinational_iteration_holds_registers : forall input path mm old_map current result stmts id,
 has_register id stmts = true ->
 value_iter_with_memory_policy (formal_invalid_policy input path)
   mm old_map false current stmts = Some result ->
 VM.find id result = VM.find id old_map.
Proof. intros. eapply policy_combinational_iteration_holds_registers; eassumption. Qed.

Theorem memory_combinational_iteration_holds_registers : forall mm old_map current result stmts id,
 has_register id stmts = true ->
 value_iter_with_memory mm old_map false current stmts = Some result ->
 VM.find id result = VM.find id old_map.
Proof.
 intros mm old_map current result stmts id Hreg Hstep.
 eapply policy_combinational_iteration_holds_registers; eassumption.
Qed.

Theorem plain_combinational_iteration_holds_registers : forall old_map current result stmts id,
 has_register id stmts = true ->
 value_iter old_map false current stmts = Some result ->
 VM.find id result = VM.find id old_map.
Proof.
 intros old_map current result stmts id Hreg Hstep.
 unfold value_iter in Hstep.
 destruct (value_iter_statements old_map false current stmts) as [proposed|];
   [|discriminate Hstep].
 eapply finish_false_holds_registers; eassumption.
Qed.
Print Assumptions memory_combinational_iteration_holds_registers.
Print Assumptions plain_combinational_iteration_holds_registers.
Print Assumptions formal_combinational_iteration_holds_registers.
