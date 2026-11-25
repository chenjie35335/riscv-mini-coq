Require Import RegisterInvariants ScalarNodeFrames ScalarSuffixCertificates MemoryWriteFrames FormalTypedNodeFrames FormalNodeEquation StagedRegisterHold.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Fixpoint formal_typed_suffix_safe_b mm node stmts : bool :=
 match stmts with
 | Qnil => true
 | Qcons st tail =>
 (match st with
 | Sskip | Sinst _ _ => true
 | Swire name _ | Sreg name _ | Smem name _ | Snode name _ => node != name
 | Sfcnct lhs rhs => (node != HiF.base_ref lhs) &&
   memory_storage_disjoint mm node (HiF.base_ref lhs) && uint_source_safe_b node rhs
 | Sinvalid reference => (node != HiF.base_ref reference) && (is_memory_writer_ref mm reference == false)
 | Swhen _ _ _ => false end) && formal_typed_suffix_safe_b mm node tail
 end.
Theorem formal_typed_suffix_safe_b_sound : forall mm node stmts,
 formal_typed_suffix_safe_b mm node stmts -> formal_typed_suffix_safe mm node stmts.
Proof.
 fix IH 3. intros mm node stmts. destruct stmts as [|st tail]; [intros _; exact I|].
 cbn [formal_typed_suffix_safe_b formal_typed_suffix_safe]. move/andP => [Head Tail].
 split; [|exact (IH mm node tail Tail)].
 destruct st as [|name typ|name reg|name mem|name mi|name expr|lhs rhs|reference|cond yes no];
 try exact Head; try exact I; try discriminate Head.
 - move/andP: Head => [/andP [Different Memory] Source].
   split; [exact Different|]. split; [exact Memory|]. apply uint_source_safe_b_sound. exact Source.
 - move/andP: Head => [Different /eqP Memory]. split; assumption.
Qed.
Print Assumptions formal_typed_suffix_safe_b_sound.

Theorem formal_combinational_known_node count stmts tail node expression width value
 invalid mm old current result :
 straight_drop count stmts = Some (Qcons (Snode node expression) tail) ->
 formal_typed_suffix_safe mm node tail -> has_register node stmts = false ->
 eval_hfexpr_validif_policy (isolated_validif_policy invalid)
   (validif_raw_address [::] count 0 [::]) mm expression old old = Some value ->
 type_of_val value = Gtyp (Fuint width) ->
 formal_value_iter invalid mm old false current stmts = Some result ->
 VM.find node result = Some value.
Proof.
 intros Position Safe Nonregister Eval Typed Step.
 unfold formal_value_iter in Step.
 destruct (formal_statements invalid [::] 0 mm old false current stmts)
   as [proposed|] eqn:Statements; [|discriminate Step].
 rewrite (staged_finish_false_equal stmts invalid [::] 0 mm old proposed
   (fun e => eval_hfexpr_with_memory mm e old old)) in Step.
 rewrite (finish_registers_preserves_nonregister stmts _ old false proposed
   result node Nonregister Step).
 destruct (formal_straight_prefix count stmts (Qcons (Snode node expression) tail)
   invalid [::] 0 mm old false current proposed Position Statements) as [at_node NodeStep].
 rewrite add0n in NodeStep. cbn [formal_statements] in NodeStep. rewrite Eval in NodeStep.
 eapply formal_typed_suffix_preserves_value; [exact Safe|exact Typed| |exact NodeStep].
 apply RegisterMapFacts.find_add_eq. exact (eqxx node).
Qed.
Print Assumptions formal_combinational_known_node.
