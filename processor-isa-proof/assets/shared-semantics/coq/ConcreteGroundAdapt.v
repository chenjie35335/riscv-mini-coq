Require Import ConcreteGroundOperations.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths.
Lemma concrete_ground_adapt ground bits typ result :
 adapt_hvalue_as_type (Gval ground bits) typ = Some result -> concrete_ground_value result.
Proof.
 destruct typ as [target|element count|fields]; destruct ground;
 try destruct target; cbn [adapt_hvalue_as_type]; intro Eval;
 try discriminate Eval; inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma concrete_ground_extend ground bits typ result :
 extend_hvalue_as_type (Gval ground bits) typ = Some result -> concrete_ground_value result.
Proof.
 unfold extend_hvalue_as_type.
 destruct (ftype_mux true (type_of_val (Gval ground bits)) typ) as [target|]; [|discriminate].
 exact (concrete_ground_adapt ground bits target result).
Qed.
Print Assumptions concrete_ground_extend.
