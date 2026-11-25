Require Import ConcreteGroundOperations.
From nbits Require Import NBits.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Lemma formal_invalid_ground_concrete inputs path site ground :
 concrete_ground_value (isolated_validif_policy (formal_invalid_policy inputs path) site (Gtyp ground)).
Proof. unfold isolated_validif_policy, formal_invalid_policy. cbn [input_value_of_type]. do 2 eexists; reflexivity. Qed.
Lemma formal_validif_result_concrete inputs path site ground width bits body result :
 (forall value, body = Some value -> concrete_ground_value value) ->
 validif_policy_result (isolated_validif_policy (formal_invalid_policy inputs path)) site
 (Some (Gval (Fuint width) bits)) (Some (Gtyp ground)) body = Some result ->
 concrete_ground_value result.
Proof.
 intros Body Eval. destruct ground; cbn [validif_policy_result] in Eval.
 all: try exact (Body result Eval).
 all: destruct (is_zero bits); [inversion Eval; subst; apply formal_invalid_ground_concrete|exact (Body result Eval)].
Qed.
Theorem formal_validif_uint_false inputs path site mm old condition body width :
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) (rcons site 0) mm condition old old = Some (Gval (Fuint 1) [::false]) ->
 eval_type_of_expr body old = Some (Gtyp (Fuint width)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm (Evalidif condition body) old old =
 Some (Gval (Fuint width) (proj1_sig (formal_symbolic_inputs inputs path (validif_source_address site) [::] width))).
Proof.
 intros Condition BodyType. cbn [eval_hfexpr_validif_policy]. rewrite Condition BodyType. reflexivity.
Qed.
Print Assumptions formal_validif_result_concrete.
Print Assumptions formal_validif_uint_false.
