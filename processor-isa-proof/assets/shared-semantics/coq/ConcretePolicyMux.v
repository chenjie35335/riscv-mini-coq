Require Import ConcreteGroundOperations ConcreteGroundAdapt.
From nbits Require Import NBits.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Theorem concrete_policy_mux invalid mm old condition yes no :
 (forall site value, eval_hfexpr_validif_policy invalid site mm condition old old = Some value -> concrete_ground_value value) ->
 (forall site value, eval_hfexpr_validif_policy invalid site mm yes old old = Some value -> concrete_ground_value value) ->
 (forall site value, eval_hfexpr_validif_policy invalid site mm no old old = Some value -> concrete_ground_value value) ->
 forall site result, eval_hfexpr_validif_policy invalid site mm (Emux condition yes no) old old = Some result -> concrete_ground_value result.
Proof.
 intros C Y N site result Eval. cbn [eval_hfexpr_validif_policy] in Eval.
 destruct (eval_hfexpr_validif_policy _ _ mm condition old old) as [v|] eqn:EC; [|discriminate Eval].
 destruct (C _ _ EC) as [g [bits V]]. subst v.
 destruct g; try discriminate Eval. destruct (is_zero bits).
 - destruct (eval_hfexpr_validif_policy _ _ mm no old old) as [v|] eqn:EN; [|discriminate Eval].
   destruct (eval_type_of_expr yes old) as [typ|]; [|discriminate Eval].
   destruct (N _ _ EN) as [gn [bn VN]]. subst v.
   exact (concrete_ground_extend gn bn typ result Eval).
 - destruct (eval_hfexpr_validif_policy _ _ mm yes old old) as [v|] eqn:EY; [|discriminate Eval].
   destruct (eval_type_of_expr no old) as [typ|]; [|discriminate Eval].
   destruct (Y _ _ EY) as [gy [yesbits VY]]. subst v.
   exact (concrete_ground_extend gy yesbits typ result Eval).
Qed.
Print Assumptions concrete_policy_mux.
