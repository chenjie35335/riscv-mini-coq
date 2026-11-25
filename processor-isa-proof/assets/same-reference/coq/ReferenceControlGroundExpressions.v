(* Exact source copy; provenance in ../provenance.json. *)
Require Import ReferenceControlGroundOperations.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Inductive reference_control_ready (old : VM.t hvalue) : hfexpr VarOrder.T -> Prop :=
| rc_const ground bits : reference_control_ready old (@Econst VarOrder.T ground bits)
| rc_ref node value : VM.find node old = Some value -> reference_control_ground value -> reference_control_ready old (Eref (Eid node))
| rc_unary op e : reference_control_ready old (Eprim_unop op e)
| rc_binary op a b : reference_control_ready old (Eprim_binop op a b)
| rc_cast op e : reference_control_ready old (Ecast op e)
| rc_mux c a b : reference_control_ready old a -> reference_control_ready old b -> reference_control_ready old (Emux c a b)
| rc_validif c b : reference_control_ready old b -> reference_control_ready old (Evalidif c b).
Lemma reference_control_nonbranch_raw_type old expression typ :
 (match expression with Eref _ | Emux _ _ _ | Evalidif _ _ => False | _ => True end) ->
 type_of_expr' (fun r => eval_type_of_ref r old) expression = Some typ -> exists ground, typ = Gtyp ground.
Proof.
 intros Shape TypeEval. pose proof (most_expressions_are_Gtyp expression old) as Ground.
 destruct expression; try contradiction; cbn -[eval_type_of_expr] in Ground; unfold eval_type_of_expr in Ground;
 rewrite TypeEval in Ground; destruct typ; cbn [option_map make_ftype_explicit] in Ground;
 try contradiction; eexists; reflexivity.
Qed.
Lemma reference_control_ready_raw_type old expression :
 reference_control_ready old expression -> forall typ,
 type_of_expr' (fun r => eval_type_of_ref r old) expression = Some typ -> exists ground, typ = Gtyp ground.
Proof.
 intro Ready. induction Ready as [ground bits|node value Lookup [ground Typed]|op e|op a b|op e|c a b A IHA B IHB|c b B IHB]; intros typ TypeEval.
 - eapply reference_control_nonbranch_raw_type; [|exact TypeEval]. exact I.
 - cbn [type_of_expr' eval_type_of_ref] in TypeEval. rewrite Lookup in TypeEval. cbn [option_map] in TypeEval. rewrite Typed in TypeEval.
   inversion TypeEval; subst. exists ground. reflexivity.
 - eapply reference_control_nonbranch_raw_type; [|exact TypeEval]. exact I.
 - eapply reference_control_nonbranch_raw_type; [|exact TypeEval]. exact I.
 - eapply reference_control_nonbranch_raw_type; [|exact TypeEval]. exact I.
 - { cbn [type_of_expr'] in TypeEval.
   destruct (type_of_expr' (fun r => eval_type_of_ref r old) c) as [ct|]; [|discriminate].
   destruct ct as [cg|elt count|fields]; [|discriminate|discriminate]. destruct cg; try discriminate TypeEval.
   all: destruct (type_of_expr' (fun r => eval_type_of_ref r old) a) as [aty|] eqn:AT; [|discriminate];
        destruct (type_of_expr' (fun r => eval_type_of_ref r old) b) as [bty|] eqn:BT; [|discriminate];
        destruct (IHA _ (Logic.eq_refl _)) as [ag AE]; destruct (IHB _ (Logic.eq_refl _)) as [bg BE]; subst aty bty;
        exact (reference_control_type_mux_ground true ag bg typ TypeEval). }
 - exact (IHB typ TypeEval).
Qed.
Lemma reference_control_ready_type old expression :
 reference_control_ready old expression -> forall typ, eval_type_of_expr expression old = Some typ -> exists ground, typ = Gtyp ground.
Proof.
 intros Ready typ TypeEval. unfold eval_type_of_expr in TypeEval.
 destruct (type_of_expr' (fun r => eval_type_of_ref r old) expression) as [raw|] eqn:Raw; [|discriminate].
 destruct (reference_control_ready_raw_type old expression Ready raw Raw) as [ground Eq]. subst raw.
 destruct ground; cbn [option_map make_ftype_explicit] in TypeEval; inversion TypeEval; subst; eexists; reflexivity.
Qed.
Require Import ReferenceControlGroundValidIf.
Theorem reference_control_expression_ground inputs path mm old expression :
 reference_control_ready old expression -> forall site result,
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm expression old old = Some result ->
 reference_control_ground result.
Proof.
 intro Ready. induction Ready as [ground bits|node value Lookup Ground|op e|op a b|op e|c a b A IHA B IHB|c b B IHB]; intros site result Eval.
 - cbn [eval_hfexpr_validif_policy] in Eval. unfold reference_control_ground. reference_control_ground_cases Eval.
 - cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval. rewrite Lookup in Eval. inversion Eval; subst result. exact Ground.
 - cbn [eval_hfexpr_validif_policy] in Eval.
   destruct (eval_hfexpr_validif_policy _ _ mm e old old) as [value|]; [|discriminate].
   exact (reference_control_unary_ground op value result Eval).
 - cbn [eval_hfexpr_validif_policy] in Eval.
   destruct (eval_hfexpr_validif_policy _ _ mm a old old) as [left|]; [|discriminate].
   destruct (eval_hfexpr_validif_policy _ _ mm b old old) as [right|]; [|discriminate].
   exact (reference_control_binary_ground op left right result Eval).
 - destruct op; cbn [eval_hfexpr_validif_policy] in Eval; unfold reference_control_ground; reference_control_ground_cases Eval.
 - { cbn [eval_hfexpr_validif_policy] in Eval.
   destruct (eval_hfexpr_validif_policy _ _ mm c old old) as [condition|]; [|discriminate].
   destruct condition as [ground bits|elt arr|fields|typ|typ|typ]; try discriminate Eval.
   - destruct ground; try discriminate Eval. destruct (is_zero bits).
     + destruct (eval_hfexpr_validif_policy _ _ mm b old old) as [value|] eqn:Value; [|discriminate].
       destruct (eval_type_of_expr a old) as [other|]; [|discriminate].
       apply (reference_control_extend_ground value other result); [eapply IHB; exact Value|exact Eval].
     + destruct (eval_hfexpr_validif_policy _ _ mm a old old) as [value|] eqn:Value; [|discriminate].
       destruct (eval_type_of_expr b old) as [other|]; [|discriminate].
       apply (reference_control_extend_ground value other result); [eapply IHA; exact Value|exact Eval].
   all: destruct typ as [ground|elt count|fields]; try discriminate Eval;
        destruct ground; try discriminate Eval;
        destruct (eval_type_of_expr a old) as [aty|] eqn:AT; [|discriminate];
        destruct (eval_type_of_expr b old) as [bty|] eqn:BT; [|discriminate];
        destruct (reference_control_ready_type old a A aty AT) as [ag AE];
        destruct (reference_control_ready_type old b B bty BT) as [bg BE]; subst aty bty;
        cbn [ftype_mux option_map] in Eval;
        destruct (fgtyp_mux ag bg); inversion Eval; subst result; eexists; reflexivity. }
 - cbn [eval_hfexpr_validif_policy] in Eval.
   destruct (eval_type_of_expr b old) as [typ|] eqn:BodyType.
   + destruct (reference_control_ready_type old b B typ BodyType) as [ground Typed]. subst typ.
     eapply reference_control_validif_ground; [|exact Eval]. intros value Body. eapply IHB; exact Body.
   + discriminate Eval.
Qed.
Print Assumptions reference_control_expression_ground.
