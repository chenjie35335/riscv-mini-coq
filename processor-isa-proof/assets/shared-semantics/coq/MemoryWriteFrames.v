Require Import ScalarNodeFrames RegisterInvariants.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths
 Semantics_with_implicit_widths Semantics_with_memory.
Definition memory_storage_disjoint mm node mem :=
 match VM.find mem mm with Some ml => node != ml_storage_id ml | None => true end.
Lemma write_memory_preserves_other mm mem port value phase old current result node :
 memory_storage_disjoint mm node mem ->
 write_memory_data mm mem port value phase old current = Some result ->
 VM.find node result = VM.find node current.
Proof.
 unfold memory_storage_disjoint, write_memory_data.
 destruct phase; cbn; [|intro Safe; intro Step; inversion Step; reflexivity].
 destruct (VM.find mem mm) as [ml|]; [|discriminate]. move/negP => Different.
 destruct (find_mem_port port (ml_writers ml)); [|discriminate].
 destruct (VM.find (ml_storage_id ml) current) as [v|]; [|discriminate].
 destruct v; try discriminate.
 destruct (memory_write_gate old mem port m) as [gate|]; [|discriminate].
 destruct gate; try (intro Step; inversion Step; reflexivity).
 all: destruct (adapt_hvalue_as_type value f); [|discriminate].
 all: match goal with |- context [option_map _ ?x] => destruct x end; [|discriminate].
 all: intro Step; inversion Step; subst result; apply RegisterMapFacts.find_add_neq; exact Different.
Qed.
Lemma memory_connection_preserves_other mm phase node lhs rhs old current result :
 node != HiF.base_ref lhs -> memory_storage_disjoint mm node (HiF.base_ref lhs) ->
 unidirectional_connect_with_memory mm phase lhs rhs old current = Some result ->
 VM.find node result = VM.find node current.
Proof.
 intros Different Storage Step. unfold unidirectional_connect_with_memory in Step.
 destruct lhs as [id|parent field|parent index|parent expr];
 try (exact (unidirectional_connect_bundle_preserves_other mm node _ rhs old current result Different Step)).
 destruct parent as [id|base port|base index|base expr];
 try (exact (unidirectional_connect_bundle_preserves_other mm node _ rhs old current result Different Step)).
 destruct base as [mem|r id|r index|r expr]; try (exact (unidirectional_connect_bundle_preserves_other mm node _ rhs old current result Different Step)).
 destruct (is_memory_data_port true mm mem port field);
 [|exact (unidirectional_connect_bundle_preserves_other mm node _ rhs old current result Different Step)].
 destruct (unidirectional_connect_bundle mm _ rhs old current) as [middle|] eqn:Connect; [|discriminate Step].
 destruct (eval_hfexpr_with_memory mm rhs old old) as [source|]; [|discriminate Step].
 rewrite (write_memory_preserves_other mm mem port source phase old middle result node Storage Step).
 exact (unidirectional_connect_bundle_preserves_other mm node _ rhs old current middle Different Connect).
Qed.

Lemma selected_memory_connection_preserves_other mm phase node lhs rhs value old current result :
 VM.find node current = Some value -> node != HiF.base_ref lhs ->
 memory_storage_disjoint mm node (HiF.base_ref lhs) ->
 (match rhs with Eref r => node != HiF.base_ref r | _ => True end) ->
 (match rhs with Eref r => if is_memory_writer_ref mm lhs then
   unidirectional_connect_with_memory mm phase lhs rhs old current
   else bidirectional_connect_with_memory mm lhs r old current
 | _ => unidirectional_connect_with_memory mm phase lhs rhs old current end) = Some result ->
 VM.find node result = Some value.
Proof.
 intros Current Different Storage Other Step.
 destruct rhs; try (rewrite (memory_connection_preserves_other mm phase node lhs _ old current result Different Storage Step); exact Current).
 destruct (is_memory_writer_ref mm lhs).
 - rewrite (memory_connection_preserves_other mm phase node lhs _ old current result Different Storage Step). exact Current.
 - rewrite (bidirectional_connect_with_memory_preserves_other mm node lhs _ old current result Different Other Step). exact Current.
Qed.
Fixpoint memory_suffix_safe (mm : memory_map) (node : VarOrder.T)
 (stmts : HiF.hfstmt_seq) : Prop :=
 match stmts with
 | Qnil => True
 | Qcons st tail =>
   (match st with
    | Sskip | Sinst _ _ => True
    | Swire name _ | Sreg name _ | Smem name _ | Snode name _ => node != name
    | Sfcnct lhs rhs => node != HiF.base_ref lhs /\
        memory_storage_disjoint mm node (HiF.base_ref lhs) /\ (match rhs with Eref reference => node != HiF.base_ref reference | _ => True end)
    | Sinvalid reference => node != HiF.base_ref reference /\ is_memory_writer_ref mm reference = false
    | Swhen _ _ _ => False
    end) /\ memory_suffix_safe mm node tail
 end.

Lemma memory_suffix_preserves_value : forall stmts mm node value invalid scope position
 old set_regs current result,
 memory_suffix_safe mm node stmts ->
 VM.find node current = Some value ->
 value_iter_statements_with_memory_policy invalid scope position mm old set_regs current stmts = Some result ->
 VM.find node result = Some value.
Proof.
 fix IH 1. intros stmts mm node value invalid scope position old set_regs current result Safe Current Step.
 destruct stmts as [|st tail].
 - inversion Step; subst; exact Current.
 - destruct Safe as [Head Tail].
   destruct st as [|name t|name reg|name mem|name mi|name expr|lhs rhs|reference|cond yes no];
     cbn [value_iter_statements_with_memory_policy] in Step.
   + eapply IH; eassumption.
   + eapply IH; [exact Tail| |exact Step].
     rewrite RegisterMapFacts.find_add_neq; [exact Current|exact (elimT negP Head)].
   + destruct (VM.find name old); [|discriminate Step].
     eapply IH; [exact Tail| |exact Step].
     rewrite RegisterMapFacts.find_add_neq; [exact Current|exact (elimT negP Head)].
   + destruct (VM.find name old); [|discriminate Step].
     eapply IH; [exact Tail| |exact Step].
     rewrite RegisterMapFacts.find_add_neq; [exact Current|exact (elimT negP Head)].
   + eapply IH; eassumption.
   + destruct (eval_hfexpr_with_memory mm expr old old); [|discriminate Step].
     eapply IH; [exact Tail| |exact Step].
     rewrite RegisterMapFacts.find_add_neq; [exact Current|exact (elimT negP Head)].
   + destruct Head as [Different [Nonmemory Source]].
     set (connection := match rhs with
       | Eref r => if is_memory_writer_ref mm lhs then
           unidirectional_connect_with_memory mm set_regs lhs rhs old current
         else bidirectional_connect_with_memory mm lhs r old current
       | _ => unidirectional_connect_with_memory mm set_regs lhs rhs old current end).
     assert (Dispatch : match connection with
       | Some next => value_iter_statements_with_memory_policy invalid scope (S position)
            mm old set_regs next tail
       | None => None end = Some result).
     { unfold connection. destruct rhs; exact Step. }
     destruct connection as [next|] eqn:Connect; [|discriminate Dispatch].
     eapply IH; [exact Tail| |exact Dispatch].
     eapply (selected_memory_connection_preserves_other mm set_regs node lhs rhs value old current next);
       eassumption.
   + destruct Head as [Different Nonmemory].
     destruct (invalidate_ref_with_memory mm set_regs reference (invalid (rcons scope position)) old current)
       as [next|] eqn:Invalidate; [|discriminate Step].
     eapply IH; [exact Tail| |exact Step].
     rewrite (nonmemory_invalidation_preserves_other mm set_regs node reference
       (invalid (rcons scope position)) old current next Different _ Invalidate); [exact Current|].
     destruct reference as [id|parent field|parent index|parent expr]; try exact I.
     destruct parent as [id|base port|base index|base expr]; try exact I.
     destruct base; try exact I. exact Nonmemory.
   + contradiction.
Qed.
Print Assumptions memory_suffix_preserves_value.
