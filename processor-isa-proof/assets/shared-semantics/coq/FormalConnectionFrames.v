Require Import RegisterInvariants ScalarNodeFrames MemoryWriteFrames.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Lemma formal_bundle_preserves_other invalid site mm node lhs rhs old current result :
 node != HiF.base_ref lhs ->
 formal_connect_bundle invalid site mm lhs rhs old current = Some result ->
 VM.find node result = VM.find node current.
Proof.
 move/negP => Different Step. unfold formal_connect_bundle in Step.
 destruct (VM.find (HiF.base_ref lhs) current); [|discriminate Step].
 destruct (eval_type_of_ref lhs current); [|discriminate Step].
 destruct (eval_hfexpr_validif_policy (isolated_validif_policy invalid) site mm rhs old old); [|discriminate Step].
 destruct (adapt_hvalue_as_type _ _); [|discriminate Step].
 destruct (repl_val_part _ _ _ _ _); [|discriminate Step].
 inversion Step; subst result. apply RegisterMapFacts.find_add_neq. exact Different.
Qed.

Lemma formal_connection_preserves_other invalid site mm phase node lhs rhs old current result :
 node != HiF.base_ref lhs -> memory_storage_disjoint mm node (HiF.base_ref lhs) ->
 formal_connect invalid site mm phase lhs rhs old current = Some result ->
 VM.find node result = VM.find node current.
Proof.
 intros Different Storage Step. unfold formal_connect in Step.
 destruct lhs as [id|parent field|parent index|parent expr];
 try (exact (formal_bundle_preserves_other invalid site mm node _ rhs old current result Different Step)).
 destruct parent as [id|base port|base index|base expr];
 try (exact (formal_bundle_preserves_other invalid site mm node _ rhs old current result Different Step)).
 destruct base as [mem|r id|r index|r expr]; try (exact (formal_bundle_preserves_other invalid site mm node _ rhs old current result Different Step)).
 destruct (is_memory_data_port true mm mem port field);
 [|exact (formal_bundle_preserves_other invalid site mm node _ rhs old current result Different Step)].
 destruct (formal_connect_bundle invalid site mm _ rhs old current) as [middle|] eqn:Connect; [|discriminate Step].
 destruct (eval_hfexpr_validif_policy (isolated_validif_policy invalid) site mm rhs old old) as [source|]; [|discriminate Step].
 rewrite (write_memory_preserves_other mm mem port source phase old middle result node Storage Step).
 exact (formal_bundle_preserves_other invalid site mm node _ rhs old current middle Different Connect).
Qed.

Lemma formal_selected_connection_preserves_other invalid site mm phase node lhs rhs value old current result :
 VM.find node current = Some value -> node != HiF.base_ref lhs ->
 memory_storage_disjoint mm node (HiF.base_ref lhs) ->
 (match rhs with Eref r => node != HiF.base_ref r | _ => True end) ->
 (match rhs with Eref r => if is_memory_writer_ref mm lhs then
   formal_connect invalid site mm phase lhs rhs old current
   else bidirectional_connect_with_memory mm lhs r old current
 | _ => formal_connect invalid site mm phase lhs rhs old current end) = Some result ->
 VM.find node result = Some value.
Proof.
 intros Current Different Storage Other Step.
 destruct rhs; try (rewrite (formal_connection_preserves_other invalid site mm phase node lhs _ old current result Different Storage Step); exact Current).
 destruct (is_memory_writer_ref mm lhs).
 - rewrite (formal_connection_preserves_other invalid site mm phase node lhs _ old current result Different Storage Step). exact Current.
 - rewrite (bidirectional_connect_with_memory_preserves_other mm node lhs _ old current result Different Other Step). exact Current.
Qed.

Print Assumptions formal_selected_connection_preserves_other.
