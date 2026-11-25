(* Exact source copy; provenance in ../provenance.json. *)
Require Import ReferenceControlGroundOperations.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Lemma reference_control_validif_ground inputs path site condition ground body result :
 (forall value, body = Some value -> reference_control_ground value) ->
 validif_policy_result (isolated_validif_policy (formal_invalid_policy inputs path)) site condition (Some (Gtyp ground)) body = Some result ->
 reference_control_ground result.
Proof.
 intros Body Eval.
 destruct body as [value|].
 - destruct (Body value (Logic.eq_refl _)) as [g Typed].
   destruct value as [vg bits|elt arr|fields|typ|typ|typ]; cbn in Typed; try discriminate Typed; try (inversion Typed; subst typ);
   unfold validif_policy_result, isolated_validif_policy, formal_invalid_policy in Eval;
   unfold reference_control_ground;
   reference_control_ground_cases Eval.
 - unfold validif_policy_result, isolated_validif_policy, formal_invalid_policy in Eval.
   unfold reference_control_ground. reference_control_ground_cases Eval.
Qed.
