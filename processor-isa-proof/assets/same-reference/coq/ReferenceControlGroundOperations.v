(* Exact source copy; provenance in ../provenance.json. *)
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths Semantics_with_implicit_widths.
Definition reference_control_ground value := exists ground, type_of_val value = Gtyp ground.
Ltac reference_control_ground_cases H :=
 first [solve [discriminate H]
       | solve [inversion H; subst; eexists; reflexivity]
       | match type of H with
         | context [match ?x with _ => _ end] => destruct x; cbn in H; reference_control_ground_cases H
         | context [if ?x then _ else _] => destruct x; cbn in H; reference_control_ground_cases H
         end].
Lemma reference_control_unary_ground op input result :
 eval_unop op input = Some result -> reference_control_ground result.
Proof.
 intro Eval. unfold eval_unop in Eval. unfold reference_control_ground.
 reference_control_ground_cases Eval.
Qed.
Lemma reference_control_binary_basic_ground op left right result :
 eval_binop_basic op left right = Some result -> reference_control_ground result.
Proof.
 intro Eval. unfold eval_binop_basic in Eval. unfold reference_control_ground.
 reference_control_ground_cases Eval.
Qed.
Lemma reference_control_binary_ground op left right result :
 eval_binop op left right = Some result -> reference_control_ground result.
Proof.
 unfold eval_binop.
 destruct (eval_binop_basic op left right) as [value|] eqn:Basic;
 destruct (absorbing_bit op left right) as [bit|]; unfold refine_boolean_result.
 - destruct (reference_control_binary_basic_ground op left right value Basic) as [ground Typed].
   destruct value as [g bits|elt arr|fields|typ|typ|typ]; try destruct typ; cbn in Typed; try discriminate Typed;
   try destruct f; intro Eval; unfold reference_control_ground; reference_control_ground_cases Eval.
 - intro Eval. inversion Eval; subst result. exact (reference_control_binary_basic_ground op left right value Basic).
 - discriminate.
 - discriminate.
Qed.
Lemma reference_control_adapt_ground input typ result :
 reference_control_ground input -> adapt_hvalue_as_type input typ = Some result -> reference_control_ground result.
Proof.
 intros [ground Typed] Eval. destruct input as [g bits|elt arr|fields|t|t|t]; cbn in Typed; try discriminate Typed;
 try (inversion Typed; subst t); unfold adapt_hvalue_as_type in Eval; cbn [ftype_mux] in Eval; unfold reference_control_ground;
 reference_control_ground_cases Eval.
Qed.
Lemma reference_control_extend_ground input typ result :
 reference_control_ground input -> extend_hvalue_as_type input typ = Some result -> reference_control_ground result.
Proof.
 intros Ground. unfold extend_hvalue_as_type.
 destruct (ftype_mux true (type_of_val input) typ) as [target|]; [|discriminate].
 exact (reference_control_adapt_ground input target result Ground).
Qed.
Lemma reference_control_type_mux_ground bit left right result :
 ftype_mux bit (Gtyp left) (Gtyp right) = Some result -> exists ground, result = Gtyp ground.
Proof.
 cbn [ftype_mux]. destruct (fgtyp_mux left right); intro Eval; inversion Eval; subst; eexists; reflexivity.
Qed.
