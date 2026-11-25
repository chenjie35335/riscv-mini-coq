Require Import GroundSourceFrames FormalTypedNodeFrames.
Require Import ScalarNodeFrames RegisterInvariants MemoryWriteFrames FormalConnectionFrames.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths
 Semantics_with_implicit_widths Semantics_with_memory.
Lemma formal_selected_ground_connection invalid site mm phase node lhs rhs ground value old current result :
 type_of_val value = Gtyp ground ->
 VM.find node current = Some value -> node != HiF.base_ref lhs ->
 memory_storage_disjoint mm node (HiF.base_ref lhs) ->
 connection_preserves_uint_source node rhs ->
 (match rhs with Eref r => if is_memory_writer_ref mm lhs then
   formal_connect invalid site mm phase lhs rhs old current
   else bidirectional_connect_with_memory mm lhs r old current
 | _ => formal_connect invalid site mm phase lhs rhs old current end) = Some result ->
 VM.find node result = Some value.
Proof.
 intros Typed Current Different Storage Source Step.
 destruct rhs; try (rewrite (formal_connection_preserves_other invalid site mm phase node lhs _ old current result Different Storage Step); exact Current).
 destruct (is_memory_writer_ref mm lhs) eqn:Writer.
 - rewrite (formal_connection_preserves_other invalid site mm phase node lhs _ old current result Different Storage Step). exact Current.
 - destruct Source as [Other|Same].
   + rewrite (bidirectional_connect_with_memory_preserves_other mm node lhs _ old current result Different Other Step). exact Current.
   + subst. eapply bidirectional_connect_with_memory_preserves_typed_ground_source; eassumption.
Qed.
Lemma formal_ground_suffix_preserves_value : forall stmts mm node ground value invalid scope position
 old set_regs current result,
 formal_typed_suffix_safe mm node stmts ->
 type_of_val value = Gtyp ground ->
 VM.find node current = Some value ->
 formal_statements invalid scope position mm old set_regs current stmts = Some result ->
 VM.find node result = Some value.
Proof.
 fix IH 1. intros stmts mm node ground value invalid scope position old set_regs current result Safe Typed Current Step.
 destruct stmts as [|st tail].
 - inversion Step; subst; exact Current.
 - destruct Safe as [Head Tail].
   destruct st as [|name t|name reg|name mem|name mi|name expr|lhs rhs|reference|cond yes no];
     cbn [formal_statements] in Step.
   + eapply IH; eassumption.
   + eapply IH; [exact Tail|exact Typed| |exact Step].
     rewrite RegisterMapFacts.find_add_neq; [exact Current|exact (elimT negP Head)].
   + destruct (VM.find name old); [|discriminate Step].
     eapply IH; [exact Tail|exact Typed| |exact Step].
     rewrite RegisterMapFacts.find_add_neq; [exact Current|exact (elimT negP Head)].
   + destruct (VM.find name old); [|discriminate Step].
     eapply IH; [exact Tail|exact Typed| |exact Step].
     rewrite RegisterMapFacts.find_add_neq; [exact Current|exact (elimT negP Head)].
   + eapply IH; eassumption.
   + destruct (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address scope position 0 [::]) mm expr old old); [|discriminate Step].
     eapply IH; [exact Tail|exact Typed| |exact Step].
     rewrite RegisterMapFacts.find_add_neq; [exact Current|exact (elimT negP Head)].
   + destruct Head as [Different [Nonmemory Source]].
     set (connection := match rhs with
       | Eref r => if is_memory_writer_ref mm lhs then
           formal_connect invalid (validif_raw_address scope position 0 [::]) mm set_regs lhs rhs old current
         else bidirectional_connect_with_memory mm lhs r old current
       | _ => formal_connect invalid (validif_raw_address scope position 0 [::]) mm set_regs lhs rhs old current end).
     assert (Dispatch : match connection with
       | Some next => formal_statements invalid scope (S position)
            mm old set_regs next tail
       | None => None end = Some result).
     { unfold connection. destruct rhs; exact Step. }
     destruct connection as [next|] eqn:Connect; [|discriminate Dispatch].
     eapply IH; [exact Tail|exact Typed| |exact Dispatch].
     eapply (formal_selected_ground_connection invalid (validif_raw_address scope position 0 [::]) mm set_regs node lhs rhs ground value old current next);
       eassumption.
   + destruct Head as [Different Nonmemory].
     destruct (invalidate_ref_with_memory mm set_regs reference (invalid (rcons scope position)) old current)
       as [next|] eqn:Invalidate; [|discriminate Step].
     eapply IH; [exact Tail|exact Typed| |exact Step].
     rewrite (nonmemory_invalidation_preserves_other mm set_regs node reference
       (invalid (rcons scope position)) old current next Different _ Invalidate); [exact Current|].
     destruct reference as [id|parent field|parent index|parent expr]; try exact I.
     destruct parent as [id|base port|base index|base expr]; try exact I.
     destruct base; try exact I. exact Nonmemory.
   + contradiction.
Qed.
Print Assumptions formal_ground_suffix_preserves_value.
