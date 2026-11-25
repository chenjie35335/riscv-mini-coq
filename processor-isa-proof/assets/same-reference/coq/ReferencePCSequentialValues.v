(* Exact source copy; provenance in ../provenance.json. *)
Require Import UIntResizeRoundtrip UIntLowExtractRoundtrip.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition reference_pc_seq_extension base value :=
 exists width, (size base <= width)%nat /\ value = Gval (Fuint width) (zext_to width base).
Lemma reference_pc_seq_resize base width target :
 (size base <= width)%nat -> (size base <= target)%nat ->
 zext_to target (take target (zext_to width base)) = zext_to target base.
Proof.
 intros Width Target.
 assert (Take : take width base = base) by (apply take_oversize; exact Width).
 rewrite <- Take at 1.
 exact (resize_uint_roundtrip_widen (size base) target width base (Logic.eq_refl _) Target Width).
Qed.
Lemma reference_pc_seq_base base : reference_pc_seq_extension base (Gval (Fuint (size base)) base).
Proof.
 exists (size base). split; [exact (leqnn _)|]. unfold zext_to,zext. rewrite subnn cats0. reflexivity.
Qed.
Lemma reference_pc_seq_mux mm old (condition : VarOrder.T) yes no bit base input source :
 reference_pc_seq_extension base input ->
 VM.find condition old = Some (Gval (Fuint 1) [::bit]) ->
 eval_hfexpr_with_memory mm (if bit then yes else no) old old = Some input ->
 eval_hfexpr_with_memory mm (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T condition)) yes no) old old = Some source ->
 reference_pc_seq_extension base source.
Proof.
 intros [width [Width Input]] Condition Selected Eval. subst input.
 cbn [eval_hfexpr_with_memory eval_href_with_memory] in Eval. rewrite Condition in Eval.
 destruct bit.
 - change (is_zero [::true]) with false in Eval. cbn in Eval.
   rewrite Selected in Eval.
   destruct (eval_type_of_expr no old) as [ty|]; [|discriminate].
   unfold extend_hvalue_as_type in Eval. destruct ty as [ground|element count|fields]; try discriminate.
   destruct ground; cbn [type_of_val ftype_mux fgtyp_mux option_map adapt_hvalue_as_type] in Eval; try discriminate.
   inversion Eval; subst source. exists (maxn width n). split; [exact (leq_trans Width (leq_maxl _ _))|].
   f_equal. apply reference_pc_seq_resize; [exact Width|exact (leq_trans Width (leq_maxl _ _))].
 - change (is_zero [::false]) with true in Eval. cbn in Eval.
   rewrite Selected in Eval.
   destruct (eval_type_of_expr yes old) as [ty|]; [|discriminate].
   unfold extend_hvalue_as_type in Eval. destruct ty as [ground|element count|fields]; try discriminate.
   destruct ground; cbn [type_of_val ftype_mux fgtyp_mux option_map adapt_hvalue_as_type] in Eval; try discriminate.
   inversion Eval; subst source. exists (maxn width n). split; [exact (leq_trans Width (leq_maxl _ _))|].
   f_equal. apply reference_pc_seq_resize; [exact Width|exact (leq_trans Width (leq_maxl _ _))].
Qed.
Definition reference_pc_plus_four pc := take 32 (from_N 33 (to_N pc + 4)).
Lemma reference_pc_plus_four_size pc : size (reference_pc_plus_four pc) = 32%nat.
Proof. unfold reference_pc_plus_four. rewrite size_take size_from_N. reflexivity. Qed.
Lemma reference_pc_seq_zero width : to_N (zext_to width [::false]) = 0.
Proof. rewrite to_N_nat. unfold zext_to. rewrite to_nat_zext. reflexivity. Qed.
Lemma reference_pc_seq_low_extract base width :
 size base = 32%nat -> (size base <= width)%nat ->
 eval_unop (Uextr 31 0) (Gval (Fuint width) (zext_to width base)) = Some (Gval (Fuint 32) base).
Proof.
 intros Size Width.
 assert (Take : take width base = base) by (apply take_oversize; exact Width).
 rewrite <- Take at 1. apply uint32_low_extract_roundtrip; [exact Size|rewrite <- Size; exact Width].
Qed.
