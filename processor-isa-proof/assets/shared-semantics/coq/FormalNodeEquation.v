Require Import RegisterInvariants ScalarNodeFrames MemoryWriteFrames FormalNodeSuffixFrames StagedRegisterHold.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Lemma formal_straight_head invalid scope position mm old set_regs current result st tail :
 (match st with Swhen _ _ _ => False | _ => True end) ->
 formal_statements invalid scope position mm old set_regs current (Qcons st tail) = Some result ->
 exists next, formal_statements invalid scope (S position)
   mm old set_regs next tail = Some result.
Proof.
 intros Straight Step.
 destruct st as [|name typ|name reg|name mem|name mi|name expr|lhs rhs|reference|cond yes no]; try contradiction;
 cbn [formal_statements] in Step;
 try (eexists; exact Step).
 all: try match type of Step with
 | context [match ?x with Some _ => _ | None => _ end] =>
   destruct x; [eexists; exact Step|discriminate Step]
 end.
 destruct rhs;
 repeat match type of Step with
 | context [match ?x with Some _ => _ | None => _ end] => destruct x
 end; try discriminate Step; eexists; exact Step.
Qed.

Theorem formal_straight_prefix : forall count stmts suffix invalid scope position mm old set_regs current result,
 straight_drop count stmts = Some suffix ->
 formal_statements invalid scope position mm old set_regs current stmts = Some result ->
 exists next, formal_statements invalid scope (position + count)
   mm old set_regs next suffix = Some result.
Proof.
 induction count as [|count IH]; intros stmts suffix invalid scope position mm old set_regs current result Drop Step.
 - inversion Drop; subst suffix. rewrite addn0. exists current. exact Step.
 - destruct stmts as [|st tail]; [discriminate Drop|].
   assert (Straight : match st with Swhen _ _ _ => False | _ => True end).
   { destruct st; try exact I; discriminate Drop. }
   assert (Rest : straight_drop count tail = Some suffix).
   { destruct st; try exact Drop; contradiction. }
   destruct (formal_straight_head invalid scope position mm old set_regs current result st tail Straight Step)
     as [next Next].
   destruct (IH tail suffix invalid scope (S position) mm old set_regs next result Rest Next)
     as [last Last].
   exists last. rewrite addnS. rewrite addSn in Last. exact Last.
Qed.

Theorem formal_combinational_node_equation count stmts tail node expression
 invalid mm old current result :
 straight_drop count stmts = Some (Qcons (Snode node expression) tail) ->
 memory_suffix_safe mm node tail -> has_register node stmts = false ->
 formal_value_iter invalid mm old false current stmts = Some result ->
 VM.find node result = eval_hfexpr_validif_policy (isolated_validif_policy invalid)
   (validif_raw_address [::] count 0 [::]) mm expression old old.
Proof.
 intros Position Safe Nonregister Step.
 unfold formal_value_iter in Step.
 destruct (formal_statements invalid [::] 0 mm old false current stmts)
   as [proposed|] eqn:Statements; [|discriminate Step].
 rewrite (staged_finish_false_equal stmts invalid [::] 0 mm old proposed
   (fun e => eval_hfexpr_with_memory mm e old old)) in Step.
 rewrite (finish_registers_preserves_nonregister stmts _ old false proposed
   result node Nonregister Step).
 destruct (formal_straight_prefix count stmts (Qcons (Snode node expression) tail)
   invalid [::] 0 mm old false current proposed Position Statements) as [at_node NodeStep].
 rewrite add0n in NodeStep.
 cbn [formal_statements] in NodeStep.
 destruct (eval_hfexpr_validif_policy (isolated_validif_policy invalid)
   (validif_raw_address [::] count 0 [::]) mm expression old old)
   as [value|] eqn:Eval; [|discriminate NodeStep].
 eapply formal_suffix_preserves_value; [exact Safe| |exact NodeStep].
 apply RegisterMapFacts.find_add_eq. exact (eqxx node).
Qed.
Print Assumptions formal_combinational_node_equation.
