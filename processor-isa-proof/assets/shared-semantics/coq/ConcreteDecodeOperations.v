From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Lemma refine_concrete_uint known width word :
 refine_boolean_result known (Some (Gval (Fuint width) word)) = Some (Gval (Fuint width) word).
Proof. destruct known; reflexivity. Qed.
Lemma concrete_uint_mask width1 width2 left right :
 exists word, eval_binop Band (Gval (Fuint width1) left) (Gval (Fuint width2) right) =
 Some (Gval (Fuint (maxn width1 width2)) word).
Proof.
 unfold eval_binop. cbn [eval_binop_basic]. rewrite refine_concrete_uint. eexists; reflexivity.
Qed.
Lemma concrete_uint_equal width1 width2 left right :
 exists bit, eval_binop (Bcomp Beq) (Gval (Fuint width1) left) (Gval (Fuint width2) right) =
 Some (Gval (Fuint 1) [::bit]).
Proof.
 unfold eval_binop. cbn [eval_binop_basic]. rewrite refine_concrete_uint. eexists; reflexivity.
Qed.
Lemma concrete_uint_mux_const_ref mm old (condition no : VarOrder.T) bit left_width right_width left right :
 VM.find condition old = Some (Gval (Fuint 1) [::bit]) ->
 VM.find no old = Some (Gval (Fuint right_width) right) ->
 eval_hfexpr_with_memory mm (@Econst VarOrder.T (Fuint left_width) left) old old =
 Some (Gval (Fuint left_width) (zext_to left_width left)) ->
 exists word, eval_hfexpr_with_memory mm
 (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T condition))
 (@Econst VarOrder.T (Fuint left_width) left) (@Eref VarOrder.T (@Eid VarOrder.T no))) old old =
 Some (Gval (Fuint (maxn left_width right_width)) word).
Proof.
 intros Condition Right Constant.
 cbn [eval_hfexpr_with_memory] in Constant.
 destruct (left_width < size left) eqn:Size; [discriminate Constant|].
 cbn [eval_hfexpr_with_memory eval_href_with_memory]. rewrite Condition.
 destruct bit; cbn [is_zero eval_hfexpr_with_memory eval_href_with_memory];
 unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite Size Right.
 - eexists; reflexivity.
 - rewrite maxnC. eexists; reflexivity.
Qed.
Print Assumptions concrete_uint_mux_const_ref.
Lemma concrete_mask_ref_const mm old (source : VarOrder.T) width word const_width const_word :
 VM.find source old = Some (Gval (Fuint width) word) ->
 eval_hfexpr_with_memory mm (@Econst VarOrder.T (Fuint const_width) const_word) old old =
 Some (Gval (Fuint const_width) (zext_to const_width const_word)) ->
 exists result, eval_hfexpr_with_memory mm
 (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T source))
 (@Econst VarOrder.T (Fuint const_width) const_word)) old old =
 Some (Gval (Fuint (maxn width const_width)) result).
Proof.
 intros Source Constant. cbn [eval_hfexpr_with_memory] in Constant.
 cbn [eval_hfexpr_with_memory eval_href_with_memory]. rewrite Source Constant.
 apply concrete_uint_mask.
Qed.
Lemma concrete_equal_ref_const mm old (source : VarOrder.T) width word const_width const_word :
 VM.find source old = Some (Gval (Fuint width) word) ->
 eval_hfexpr_with_memory mm (@Econst VarOrder.T (Fuint const_width) const_word) old old =
 Some (Gval (Fuint const_width) (zext_to const_width const_word)) ->
 exists bit, eval_hfexpr_with_memory mm
 (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T source))
 (@Econst VarOrder.T (Fuint const_width) const_word)) old old =
 Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Source Constant. cbn [eval_hfexpr_with_memory] in Constant.
 cbn [eval_hfexpr_with_memory eval_href_with_memory]. rewrite Source Constant.
 apply concrete_uint_equal.
Qed.
Print Assumptions concrete_equal_ref_const.
Lemma concrete_equal_const_ref mm old (source : VarOrder.T) width word const_width const_word :
 VM.find source old = Some (Gval (Fuint width) word) ->
 eval_hfexpr_with_memory mm (@Econst VarOrder.T (Fuint const_width) const_word) old old =
 Some (Gval (Fuint const_width) (zext_to const_width const_word)) ->
 exists bit, eval_hfexpr_with_memory mm
 (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint const_width) const_word)
 (@Eref VarOrder.T (@Eid VarOrder.T source))) old old =
 Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Source Constant. cbn [eval_hfexpr_with_memory] in Constant.
 cbn [eval_hfexpr_with_memory eval_href_with_memory]. rewrite Source Constant.
 apply concrete_uint_equal.
Qed.
