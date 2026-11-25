Require Import RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.

(* Passive scalar sources must survive their later use on the RHS of a
   bidirectional connect. This is needed to lift node equations to full rounds. *)
Lemma adapted_uint_is_passive value width result :
 adapt_hvalue_as_type value (Gtyp (Fuint width)) = Some result ->
 is_passive_value result.
Proof.
 destruct value as [ground bits|element array|bundle|t|t|t];
   cbn [adapt_hvalue_as_type]; intro Adapt; try discriminate Adapt.
 - destruct ground; try discriminate Adapt. inversion Adapt; reflexivity.
 - destruct (ftype_mux false t (Gtyp (Fuint width))); [|discriminate Adapt].
   inversion Adapt; reflexivity.
 - destruct (ftype_mux false t (Gtyp (Fuint width))); [|discriminate Adapt].
   inversion Adapt; reflexivity.
 - destruct (ftype_mux false t (Gtyp (Fuint width))); [|discriminate Adapt].
   inversion Adapt; reflexivity.
Qed.

Lemma passive_source_unchanged old new_value :
 is_passive_value new_value -> replace_writeable Source old new_value = Some old.
Proof.
 destruct new_value; cbn [is_passive_value replace_writeable];
   intro Passive; try reflexivity; rewrite Passive; reflexivity.
Qed.

Lemma unidirectional_connect_preserves_other node lhs rhs old current result :
 node != HiF.base_ref lhs ->
 unidirectional_connect lhs rhs old current = Some result ->
 VM.find node result = VM.find node current.
Proof.
 move/negP => Different Step. unfold unidirectional_connect in Step.
 destruct (VM.find (HiF.base_ref lhs) current); [|discriminate Step].
 destruct (eval_type_of_ref lhs current); [|discriminate Step].
 destruct (eval_hfexpr rhs old old); [|discriminate Step].
 destruct (adapt_hvalue_as_type _ _); [|discriminate Step].
 destruct (repl_val_part _ _ _ _ _); [|discriminate Step].
 inversion Step; subst result. apply RegisterMapFacts.find_add_neq. exact Different.
Qed.

Lemma bidirectional_connect_preserves_other node lhs rhs old current result :
 node != HiF.base_ref lhs -> node != HiF.base_ref rhs ->
 bidirectional_connect lhs rhs old current = Some result ->
 VM.find node result = VM.find node current.
Proof.
 move/negP => DifferentLeft. move/negP => DifferentRight Step.
 unfold bidirectional_connect in Step.
 destruct (VM.find (HiF.base_ref lhs) current); [|discriminate Step].
 destruct (eval_type_of_ref lhs current); [|discriminate Step].
 destruct (eval_href rhs old old); [|discriminate Step].
 destruct (adapt_hvalue_as_type _ _); [|discriminate Step].
 destruct (repl_val_part lhs _ _ _ _) as [left_value|]; [|discriminate Step].
 cbn [option_map] in Step.
 destruct (VM.find (HiF.base_ref rhs) (VM.add (HiF.base_ref lhs) left_value current));
   [|discriminate Step].
 destruct (eval_type_of_ref rhs (VM.add (HiF.base_ref lhs) left_value current));
   [|discriminate Step].
 destruct (eval_href lhs old old); [|discriminate Step].
 destruct (adapt_hvalue_as_type _ _); [|discriminate Step].
 destruct (repl_val_part rhs _ _ _ _); [|discriminate Step].
 inversion Step; subst result.
 rewrite (RegisterMapFacts.find_add_neq DifferentRight)
   (RegisterMapFacts.find_add_neq DifferentLeft). reflexivity.
Qed.

Theorem bidirectional_connect_preserves_uint_source node lhs width bits old current result :
 node != HiF.base_ref lhs ->
 VM.find node current = Some (Gval (Fuint width) bits) ->
 bidirectional_connect lhs (@Eid VarOrder.T node) old current = Some result ->
 VM.find node result = Some (Gval (Fuint width) bits).
Proof.
 move/negP => Different. intros Current Step.
 unfold bidirectional_connect in Step.
 destruct (VM.find (HiF.base_ref lhs) current); [|discriminate Step].
 destruct (eval_type_of_ref lhs current); [|discriminate Step].
 destruct (eval_href (@Eid VarOrder.T node) old old); [|discriminate Step].
 destruct (adapt_hvalue_as_type _ _); [|discriminate Step].
 destruct (repl_val_part lhs _ _ _ _) as [left_value|]; [|discriminate Step].
 cbn [option_map eval_type_of_ref HiF.base_ref] in Step.
 rewrite (RegisterMapFacts.find_add_neq Different) Current in Step.
 cbn [option_map type_of_val] in Step.
 destruct (eval_href lhs old old) as [source_value|]; [|discriminate Step].
 destruct (adapt_hvalue_as_type source_value (Gtyp (Fuint width)))
   as [adapted|] eqn:Adapt; [|discriminate Step].
 pose proof (adapted_uint_is_passive source_value width adapted Adapt) as Passive.
 cbn [repl_val_part] in Step.
 rewrite (passive_source_unchanged (Gval (Fuint width) bits) adapted Passive) in Step.
 inversion Step; subst result.
 apply RegisterMapFacts.find_add_eq. exact (eqxx node).
Qed.

Print Assumptions bidirectional_connect_preserves_uint_source.

Theorem bidirectional_connect_preserves_typed_uint_source node lhs width value old current result :
 type_of_val value = Gtyp (Fuint width) ->
 node != HiF.base_ref lhs ->
 VM.find node current = Some value ->
 bidirectional_connect lhs (@Eid VarOrder.T node) old current = Some result ->
 VM.find node result = Some value.
Proof.
 intro ValueType. move/negP => Different. intros Current Step.
 unfold bidirectional_connect in Step.
 destruct (VM.find (HiF.base_ref lhs) current); [|discriminate Step].
 destruct (eval_type_of_ref lhs current); [|discriminate Step].
 destruct (eval_href (@Eid VarOrder.T node) old old); [|discriminate Step].
 destruct (adapt_hvalue_as_type _ _); [|discriminate Step].
 destruct (repl_val_part lhs _ _ _ _) as [left_value|]; [|discriminate Step].
 cbn [option_map eval_type_of_ref HiF.base_ref] in Step.
 rewrite (RegisterMapFacts.find_add_neq Different) Current in Step.
 cbn [option_map] in Step. rewrite ValueType in Step.
 destruct (eval_href lhs old old) as [source_value|]; [|discriminate Step].
 destruct (adapt_hvalue_as_type source_value (Gtyp (Fuint width)))
   as [adapted|] eqn:Adapt; [|discriminate Step].
 pose proof (adapted_uint_is_passive source_value width adapted Adapt) as Passive.
 cbn [repl_val_part] in Step.
 rewrite (passive_source_unchanged value adapted Passive) in Step.
 inversion Step; subst result.
 apply RegisterMapFacts.find_add_eq. exact (eqxx node).
Qed.

Print Assumptions bidirectional_connect_preserves_typed_uint_source.

Theorem finish_registers_preserves_nonregister : forall (stmts : HiF.hfstmt_seq)
 eval old set_regs current result node,
 has_register node stmts = false ->
 finish_registers eval old set_regs current stmts = Some result ->
 VM.find node result = VM.find node current.
Proof.
 fix IH 1. intros stmts eval old set_regs current result node Absent Finish.
 destruct stmts as [|st tail].
 - cbn [finish_registers] in Finish. inversion Finish; reflexivity.
 - destruct st as [|name t|name reg|name mem|name mi|name expr|lhs rhs|ref|cond yes no];
     cbn [has_register] in Absent; cbn [finish_registers] in Finish;
     try (eapply IH; [exact Absent|exact Finish]).
   + case Same: (node == name) in Absent; [discriminate Absent|].
     destruct (VM.find name old) as [old_value|]; [|discriminate Finish].
     destruct (VM.find name current) as [proposed|]; [|discriminate Finish].
     destruct (if set_regs then register_next_value eval reg proposed else Some old_value);
       [|discriminate Finish].
     rewrite (IH tail eval old set_regs _ result node Absent Finish).
     apply RegisterMapFacts.find_add_neq.
     change (~ (node == name)). rewrite Same. discriminate.
   + case Yes: (has_register node yes) in Absent; [discriminate Absent|].
     case No: (has_register node no) in Absent; [discriminate Absent|].
     destruct (finish_registers eval old set_regs current yes) as [after_yes|] eqn:FinishYes;
       [|discriminate Finish].
     destruct (finish_registers eval old set_regs after_yes no) as [after_no|] eqn:FinishNo;
       [|discriminate Finish].
     rewrite (IH tail eval old set_regs after_no result node Absent Finish).
     rewrite (IH no eval old set_regs after_yes after_no node No FinishNo).
     exact (IH yes eval old set_regs current after_yes node Yes FinishYes).
Qed.

Print Assumptions finish_registers_preserves_nonregister.

Theorem policy_iteration_nonregister_projection invalid mm old set_regs current result stmts node :
 has_register node stmts = false ->
 value_iter_with_memory_policy invalid mm old set_regs current stmts = Some result ->
 exists proposed,
   value_iter_statements_with_memory_policy invalid [::] 0 mm old set_regs current stmts = Some proposed /\
   VM.find node result = VM.find node proposed.
Proof.
 intros Absent Step. unfold value_iter_with_memory_policy in Step.
 destruct (value_iter_statements_with_memory_policy invalid [::] 0 mm old set_regs current stmts)
   as [proposed|] eqn:Statements; [|discriminate Step].
 exists proposed. split; [reflexivity|].
 exact (finish_registers_preserves_nonregister stmts _ old set_regs proposed result node Absent Step).
Qed.

Corollary policy_iteration_preserves_computed_node invalid mm old set_regs current result stmts node value :
 has_register node stmts = false ->
 (forall proposed,
   value_iter_statements_with_memory_policy invalid [::] 0 mm old set_regs current stmts = Some proposed ->
   VM.find node proposed = Some value) ->
 value_iter_with_memory_policy invalid mm old set_regs current stmts = Some result ->
 VM.find node result = Some value.
Proof.
 intros Absent Computed Step.
 destruct (policy_iteration_nonregister_projection invalid mm old set_regs current result stmts node Absent Step)
   as [proposed [Statements Projection]].
 rewrite Projection. exact (Computed proposed Statements).
Qed.

Print Assumptions policy_iteration_nonregister_projection.

Lemma undef_ref_preserves_other node reference make_value old current result :
 node != HiF.base_ref reference ->
 undef_ref reference make_value old current = Some result ->
 VM.find node result = VM.find node current.
Proof.
 move/negP => Different Step. unfold undef_ref in Step.
 destruct (VM.find (HiF.base_ref reference) current); [|discriminate Step].
 destruct (eval_type_of_ref reference current); [|discriminate Step].
 destruct (repl_val_part _ _ _ _ _); [|discriminate Step].
 inversion Step; subst result. apply RegisterMapFacts.find_add_neq. exact Different.
Qed.

Lemma nonmemory_invalidation_preserves_other mm set_regs node reference make_value old current result :
 node != HiF.base_ref reference ->
 (match reference with
  | Esubfield (Esubfield (Eid mem) port) field =>
      is_memory_data_port true mm mem port field = false
  | _ => True end) ->
 invalidate_ref_with_memory mm set_regs reference make_value old current = Some result ->
 VM.find node result = VM.find node current.
Proof.
 intros Different Nonmemory Step. unfold invalidate_ref_with_memory in Step.
 destruct (undef_ref reference make_value old current) as [next|] eqn:Invalidate;
   [|discriminate Step].
 assert (Same : next = result).
 { destruct reference as [id|parent field|parent index|parent expr];
     try (inversion Step; reflexivity).
   destruct parent as [id|base port|base index|base expr];
     try (inversion Step; reflexivity).
   destruct base; try (inversion Step; reflexivity).
   rewrite Nonmemory in Step. inversion Step; reflexivity. }
 subst next. eapply undef_ref_preserves_other; eassumption.
Qed.

Print Assumptions nonmemory_invalidation_preserves_other.

(* An invalid statement changes only its destination when it is not a
   memory writer. The continuation keeps its actual static source position. *)
Lemma invalid_statement_node_projection invalid scope position mm old set_regs
 current result tail node reference :
 node != HiF.base_ref reference ->
 (match reference with
  | Esubfield (Esubfield (Eid mem) port) field =>
      is_memory_data_port true mm mem port field = false
  | _ => True end) ->
 (forall next,
   VM.find node next = VM.find node current ->
   value_iter_statements_with_memory_policy invalid scope (S position)
     mm old set_regs next tail = Some result ->
   VM.find node result = VM.find node next) ->
 value_iter_statements_with_memory_policy invalid scope position
   mm old set_regs current (Qcons (Sinvalid reference) tail) = Some result ->
 VM.find node result = VM.find node current.
Proof.
 intros Different Nonmemory Tail Step.
 cbn [value_iter_statements_with_memory_policy] in Step.
 destruct (invalidate_ref_with_memory mm set_regs reference
   (invalid (rcons scope position)) old current) as [next|] eqn:Invalidate;
   [|discriminate Step].
 pose proof (nonmemory_invalidation_preserves_other mm set_regs node reference
   (invalid (rcons scope position)) old current next Different Nonmemory Invalidate) as Same.
 rewrite (Tail next Same Step). exact Same.
Qed.
Print Assumptions invalid_statement_node_projection.

Lemma node_statement_evaluation_projection invalid scope position mm old set_regs
 current result tail node expression :
 (forall value,
   eval_hfexpr_with_memory mm expression old old = Some value ->
   value_iter_statements_with_memory_policy invalid scope (S position)
     mm old set_regs (VM.add node value current) tail = Some result ->
   VM.find node result = Some value) ->
 value_iter_statements_with_memory_policy invalid scope position
   mm old set_regs current (Qcons (Snode node expression) tail) = Some result ->
 VM.find node result = eval_hfexpr_with_memory mm expression old old.
Proof.
 intros Tail Step.
 cbn [value_iter_statements_with_memory_policy] in Step.
 destruct (eval_hfexpr_with_memory mm expression old old) as [value|] eqn:Eval;
   [|discriminate Step].
 apply (Tail value); [reflexivity|exact Step].
Qed.

Corollary node_statement_preserved_evaluation invalid scope position mm old set_regs
 current result tail node expression :
 (forall value,
   eval_hfexpr_with_memory mm expression old old = Some value ->
   value_iter_statements_with_memory_policy invalid scope (S position)
     mm old set_regs (VM.add node value current) tail = Some result ->
   VM.find node result = VM.find node (VM.add node value current)) ->
 value_iter_statements_with_memory_policy invalid scope position
   mm old set_regs current (Qcons (Snode node expression) tail) = Some result ->
 VM.find node result = eval_hfexpr_with_memory mm expression old old.
Proof.
 intros Tail Step.
 apply (node_statement_evaluation_projection invalid scope position mm old set_regs
   current result tail node expression); [|exact Step].
 intros value Eval Rest. rewrite (Tail value Eval Rest).
 apply RegisterMapFacts.find_add_eq. exact (eqxx node).
Qed.
Print Assumptions node_statement_preserved_evaluation.


Lemma bidirectional_connect_with_memory_preserves_other mm node lhs rhs old current result :
 node != HiF.base_ref lhs -> node != HiF.base_ref rhs ->
 bidirectional_connect_with_memory mm lhs rhs old current = Some result ->
 VM.find node result = VM.find node current.
Proof.
 move/negP => DifferentLeft. move/negP => DifferentRight Step.
 unfold bidirectional_connect_with_memory in Step.
 destruct (VM.find (HiF.base_ref lhs) current); [|discriminate Step].
 destruct (eval_type_of_ref lhs current); [|discriminate Step].
 destruct (eval_href_with_memory mm rhs old old); [|discriminate Step].
 destruct (adapt_hvalue_as_type _ _); [|discriminate Step].
 destruct (repl_val_part lhs _ _ _ _) as [left_value|]; [|discriminate Step].
 cbn [option_map] in Step.
 destruct (VM.find (HiF.base_ref rhs) (VM.add (HiF.base_ref lhs) left_value current));
   [|discriminate Step].
 destruct (eval_type_of_ref rhs (VM.add (HiF.base_ref lhs) left_value current));
   [|discriminate Step].
 destruct (eval_href_with_memory mm lhs old old); [|discriminate Step].
 destruct (adapt_hvalue_as_type _ _); [|discriminate Step].
 destruct (repl_val_part rhs _ _ _ _); [|discriminate Step].
 inversion Step; subst result.
 rewrite (RegisterMapFacts.find_add_neq DifferentRight)
   (RegisterMapFacts.find_add_neq DifferentLeft). reflexivity.
Qed.


Theorem bidirectional_connect_with_memory_preserves_typed_uint_source mm node lhs width value old current result :
 type_of_val value = Gtyp (Fuint width) ->
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
 destruct (adapt_hvalue_as_type source_value (Gtyp (Fuint width)))
   as [adapted|] eqn:Adapt; [|discriminate Step].
 pose proof (adapted_uint_is_passive source_value width adapted Adapt) as Passive.
 cbn [repl_val_part] in Step.
 rewrite (passive_source_unchanged value adapted Passive) in Step.
 inversion Step; subst result.
 apply RegisterMapFacts.find_add_eq. exact (eqxx node).
Qed.

Print Assumptions bidirectional_connect_with_memory_preserves_typed_uint_source.

Lemma unidirectional_connect_bundle_preserves_other mm node lhs rhs old current result :
 node != HiF.base_ref lhs ->
 unidirectional_connect_bundle mm lhs rhs old current = Some result ->
 VM.find node result = VM.find node current.
Proof.
 move/negP => Different Step. unfold unidirectional_connect_bundle in Step.
 destruct (VM.find (HiF.base_ref lhs) current); [|discriminate Step].
 destruct (eval_type_of_ref lhs current); [|discriminate Step].
 destruct (eval_hfexpr_with_memory mm rhs old old); [|discriminate Step].
 destruct (adapt_hvalue_as_type _ _); [|discriminate Step].
 destruct (repl_val_part _ _ _ _ _); [|discriminate Step].
 inversion Step; subst result. apply RegisterMapFacts.find_add_neq. exact Different.
Qed.

Lemma nonmemory_unidirectional_connect_is_bundle mm set_regs lhs rhs old current :
 is_memory_writer_ref mm lhs = false ->
 unidirectional_connect_with_memory mm set_regs lhs rhs old current =
 unidirectional_connect_bundle mm lhs rhs old current.
Proof.
 intro Nonmemory.
 unfold unidirectional_connect_with_memory.
 destruct lhs as [id|parent field|parent index|parent expr]; try reflexivity.
 destruct parent as [id|base port|base index|base expr]; try reflexivity.
 destruct base; try reflexivity.
 cbn [is_memory_writer_ref] in Nonmemory. rewrite Nonmemory. reflexivity.
Qed.

Corollary nonmemory_unidirectional_connect_preserves_other mm set_regs node lhs rhs old current result :
 node != HiF.base_ref lhs ->
 is_memory_writer_ref mm lhs = false ->
 unidirectional_connect_with_memory mm set_regs lhs rhs old current = Some result ->
 VM.find node result = VM.find node current.
Proof.
 intros Different Nonmemory Step.
 rewrite (nonmemory_unidirectional_connect_is_bundle mm set_regs lhs rhs old current Nonmemory) in Step.
 exact (unidirectional_connect_bundle_preserves_other mm node lhs rhs old current result Different Step).
Qed.
Print Assumptions nonmemory_unidirectional_connect_preserves_other.

Definition connection_preserves_uint_source (node : VarOrder.T) (rhs : HiF.hfexpr) : Prop :=
 match rhs with
 | Eref reference => node != HiF.base_ref reference \/ reference = Eid node
 | _ => True
 end.

Lemma selected_connection_preserves_uint mm set_regs node lhs rhs width value old current result :
 type_of_val value = Gtyp (Fuint width) ->
 VM.find node current = Some value ->
 node != HiF.base_ref lhs ->
 is_memory_writer_ref mm lhs = false ->
 connection_preserves_uint_source node rhs ->
 (match rhs with
  | Eref reference =>
      if is_memory_writer_ref mm lhs then
        unidirectional_connect_with_memory mm set_regs lhs rhs old current
      else bidirectional_connect_with_memory mm lhs reference old current
  | _ => unidirectional_connect_with_memory mm set_regs lhs rhs old current
  end) = Some result ->
 VM.find node result = Some value.
Proof.
 intros Typed Current Different Nonmemory Source Step.
 destruct rhs; try (rewrite (nonmemory_unidirectional_connect_preserves_other
   mm set_regs node lhs _ old current result Different Nonmemory Step); exact Current).
 rewrite Nonmemory in Step.
 destruct Source as [Other|Same].
 - rewrite (bidirectional_connect_with_memory_preserves_other mm node lhs _ old current result Different Other Step).
   exact Current.
 - subst. eapply bidirectional_connect_with_memory_preserves_typed_uint_source;
     eassumption.
Qed.
Print Assumptions selected_connection_preserves_uint.

Fixpoint scalar_suffix_safe (mm : memory_map) (node : VarOrder.T)
 (stmts : HiF.hfstmt_seq) : Prop :=
 match stmts with
 | Qnil => True
 | Qcons st tail =>
   (match st with
    | Sskip | Sinst _ _ => True
    | Swire name _ | Sreg name _ | Smem name _ | Snode name _ => node != name
    | Sfcnct lhs rhs => node != HiF.base_ref lhs /\
        is_memory_writer_ref mm lhs = false /\ connection_preserves_uint_source node rhs
    | Sinvalid reference => node != HiF.base_ref reference /\
        is_memory_writer_ref mm reference = false
    | Swhen _ _ _ => False
    end) /\ scalar_suffix_safe mm node tail
 end.

Lemma scalar_suffix_preserves_uint : forall stmts mm node width value invalid scope position
 old set_regs current result,
 scalar_suffix_safe mm node stmts ->
 type_of_val value = Gtyp (Fuint width) ->
 VM.find node current = Some value ->
 value_iter_statements_with_memory_policy invalid scope position mm old set_regs current stmts = Some result ->
 VM.find node result = Some value.
Proof.
 fix IH 1. intros stmts mm node width value invalid scope position old set_regs current result Safe Typed Current Step.
 destruct stmts as [|st tail].
 - inversion Step; subst; exact Current.
 - destruct Safe as [Head Tail].
   destruct st as [|name t|name reg|name mem|name mi|name expr|lhs rhs|reference|cond yes no];
     cbn [value_iter_statements_with_memory_policy] in Step.
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
   + destruct (eval_hfexpr_with_memory mm expr old old); [|discriminate Step].
     eapply IH; [exact Tail|exact Typed| |exact Step].
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
     eapply IH; [exact Tail|exact Typed| |exact Dispatch].
     eapply (selected_connection_preserves_uint mm set_regs node lhs rhs width value old current next);
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

Theorem safe_node_suffix_evaluation invalid scope position mm old set_regs
 current result tail node expression width :
 scalar_suffix_safe mm node tail ->
 (forall value, eval_hfexpr_with_memory mm expression old old = Some value ->
   type_of_val value = Gtyp (Fuint width)) ->
 value_iter_statements_with_memory_policy invalid scope position mm old set_regs
   current (Qcons (Snode node expression) tail) = Some result ->
 VM.find node result = eval_hfexpr_with_memory mm expression old old.
Proof.
 intros Safe Typed Step.
 apply (node_statement_evaluation_projection invalid scope position mm old set_regs
   current result tail node expression); [|exact Step].
 intros value Eval Rest.
 eapply (scalar_suffix_preserves_uint tail mm node width value invalid scope (S position)
   old set_regs (VM.add node value current) result).
 - exact Safe.
 - exact (Typed value Eval).
 - apply RegisterMapFacts.find_add_eq. exact (eqxx node).
 - exact Rest.
Qed.
Print Assumptions safe_node_suffix_evaluation.

(* Prefix extraction deliberately excludes branch statements. It retains the
   static position used to identify each formal invalid source. *)
Fixpoint straight_drop (count : nat) (stmts : HiF.hfstmt_seq) : option HiF.hfstmt_seq :=
 match count, stmts with
 | O, _ => Some stmts
 | S rest, Qcons (Swhen _ _ _) _ => None
 | S rest, Qcons _ tail => straight_drop rest tail
 | _, _ => None
 end.

Lemma successful_straight_head invalid scope position mm old set_regs current result st tail :
 (match st with Swhen _ _ _ => False | _ => True end) ->
 value_iter_statements_with_memory_policy invalid scope position mm old set_regs current (Qcons st tail) = Some result ->
 exists next, value_iter_statements_with_memory_policy invalid scope (S position)
   mm old set_regs next tail = Some result.
Proof.
 intros Straight Step.
 destruct st as [|name typ|name reg|name mem|name mi|name expr|lhs rhs|reference|cond yes no]; try contradiction;
 cbn [value_iter_statements_with_memory_policy] in Step;
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

Theorem successful_straight_prefix : forall count stmts suffix invalid scope position mm old set_regs current result,
 straight_drop count stmts = Some suffix ->
 value_iter_statements_with_memory_policy invalid scope position mm old set_regs current stmts = Some result ->
 exists next, value_iter_statements_with_memory_policy invalid scope (position + count)
   mm old set_regs next suffix = Some result.
Proof.
 induction count as [|count IH]; intros stmts suffix invalid scope position mm old set_regs current result Drop Step.
 - inversion Drop; subst suffix. rewrite addn0. exists current. exact Step.
 - destruct stmts as [|st tail]; [discriminate Drop|].
   assert (Straight : match st with Swhen _ _ _ => False | _ => True end).
   { destruct st; try exact I; discriminate Drop. }
   assert (Rest : straight_drop count tail = Some suffix).
   { destruct st; try exact Drop; contradiction. }
   destruct (successful_straight_head invalid scope position mm old set_regs current result st tail Straight Step)
     as [next Next].
   destruct (IH tail suffix invalid scope (S position) mm old set_regs next result Rest Next)
     as [last Last].
   exists last. rewrite addnS. rewrite addSn in Last. exact Last.
Qed.
Print Assumptions successful_straight_prefix.

Theorem full_iteration_node_equation count stmts tail node expression width
 invalid mm old set_regs current result :
 straight_drop count stmts = Some (Qcons (Snode node expression) tail) ->
 scalar_suffix_safe mm node tail ->
 has_register node stmts = false ->
 (forall value, eval_hfexpr_with_memory mm expression old old = Some value ->
   type_of_val value = Gtyp (Fuint width)) ->
 value_iter_with_memory_policy invalid mm old set_regs current stmts = Some result ->
 VM.find node result = eval_hfexpr_with_memory mm expression old old.
Proof.
 intros Position Safe Nonregister Typed Step.
 destruct (policy_iteration_nonregister_projection invalid mm old set_regs current result stmts node Nonregister Step)
   as [proposed [Statements Projection]].
 destruct (successful_straight_prefix count stmts (Qcons (Snode node expression) tail)
   invalid [::] 0 mm old set_regs current proposed Position Statements) as [at_node NodeStep].
 rewrite Projection.
 exact (safe_node_suffix_evaluation invalid [::] (0 + count) mm old set_regs
   at_node proposed tail node expression width Safe Typed NodeStep).
Qed.
Print Assumptions full_iteration_node_equation.
