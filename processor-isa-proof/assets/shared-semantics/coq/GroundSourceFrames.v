Require Import ScalarNodeFrames RegisterInvariants.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Lemma adapted_ground_is_passive value ground result :
 adapt_hvalue_as_type value (Gtyp ground) = Some result -> is_passive_value result.
Proof.
 destruct value as [source bits|element array|bundle|t|t|t]; destruct ground;
 cbn [adapt_hvalue_as_type]; intro Adapt; try discriminate Adapt.
 all: try (destruct source; cbn [adapt_hvalue_as_type] in Adapt; try discriminate Adapt).
 all: repeat match type of Adapt with context [ftype_mux ?mode ?left ?right] =>
 destruct (ftype_mux mode left right) end.
 all: inversion Adapt; reflexivity.
Qed.
Theorem bidirectional_connect_with_memory_preserves_typed_ground_source mm node lhs ground value old current result :
 type_of_val value = Gtyp ground ->
 node != HiF.base_ref lhs ->
 VM.find node current = Some value ->
 bidirectional_connect_with_memory mm lhs (@Eid VarOrder.T node) old current = Some result ->
 VM.find node result = Some value.
Proof.
 intro ValueType. move/negP => Different. intros Current Step.
 unfold bidirectional_connect_with_memory in Step.
 destruct (VM.find (HiF.base_ref lhs) current); [|discriminate Step].
 destruct (eval_type_of_ref lhs current); [|discriminate Step].
 destruct (eval_href_with_memory mm (@Eid VarOrder.T node) old old); [|discriminate Step].
 destruct (adapt_hvalue_as_type _ _); [|discriminate Step].
 destruct (repl_val_part lhs _ _ _ _) as [left_value|]; [|discriminate Step].
 cbn [option_map eval_type_of_ref HiF.base_ref] in Step.
 rewrite (RegisterMapFacts.find_add_neq Different) Current in Step.
 cbn [option_map] in Step. rewrite ValueType in Step.
 destruct (eval_href_with_memory mm lhs old old) as [source_value|]; [|discriminate Step].
 destruct (adapt_hvalue_as_type source_value (Gtyp ground))
   as [adapted|] eqn:Adapt; [|discriminate Step].
 pose proof (adapted_ground_is_passive source_value ground adapted Adapt) as Passive.
 cbn [repl_val_part] in Step.
 rewrite (passive_source_unchanged value adapted Passive) in Step.
 inversion Step; subst result.
 apply RegisterMapFacts.find_add_eq. exact (eqxx node).
Qed.

Print Assumptions bidirectional_connect_with_memory_preserves_typed_ground_source.
