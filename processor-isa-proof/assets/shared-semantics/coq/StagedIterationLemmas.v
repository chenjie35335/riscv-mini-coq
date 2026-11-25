From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From firrtl Require Import Semantics_with_implicit_widths Semantics_with_memory.
Lemma formal_iterations_fixedpoint modules top inputs states n :
 formal_circuit_value_iter (formal_invalid_policy inputs) modules top states false = Some states ->
 circuit_formal_iterations modules top inputs n states = Some states.
Proof.
 intro Fixed. induction n as [|n IH]; [reflexivity|].
 cbn [circuit_formal_iterations]. rewrite Fixed. exact IH.
Qed.
Lemma formal_iterations_append modules top inputs first rest states :
 circuit_formal_iterations modules top inputs (Nat.add first rest) states =
 match circuit_formal_iterations modules top inputs first states with
 | Some middle => circuit_formal_iterations modules top inputs rest middle
 | None => None end.
Proof.
 revert states. induction first as [|first IH]; intro states; [reflexivity|].
 cbn [Nat.add circuit_formal_iterations].
 destruct (formal_circuit_value_iter (formal_invalid_policy inputs) modules top states false);
 [apply IH|reflexivity].
Qed.
Theorem formal_iterations_settled_tail modules top inputs first rest states fixed :
 circuit_formal_iterations modules top inputs first states = Some fixed ->
 formal_circuit_value_iter (formal_invalid_policy inputs) modules top fixed false = Some fixed ->
 circuit_formal_iterations modules top inputs (Nat.add first rest) states = Some fixed.
Proof.
 intros Prefix Fixed. rewrite formal_iterations_append Prefix.
 apply formal_iterations_fixedpoint. exact Fixed.
Qed.
Print Assumptions formal_iterations_settled_tail.

Lemma staged_iterations_last modules top inputs n states result :
 circuit_formal_iterations modules top inputs (S n) states = Some result ->
 exists previous,
 circuit_formal_iterations modules top inputs n states = Some previous /\
 formal_circuit_value_iter (formal_invalid_policy inputs) modules top previous false = Some result.
Proof.
 revert states result. induction n as [|n IH]; intros states result Step.
 - cbn [circuit_formal_iterations] in Step.
   destruct (formal_circuit_value_iter _ _ _ _ _) as [next|] eqn:Next;
     [|discriminate Step]. inversion Step; subst result.
   exists states. split; [reflexivity|exact Next].
 - cbn [circuit_formal_iterations] in Step.
   destruct (formal_circuit_value_iter _ _ _ _ _) as [next|] eqn:Next;
     [|discriminate Step].
   destruct (IH next result Step) as [previous [Prior Last]].
   exists previous. split; [|exact Last].
   cbn [circuit_formal_iterations]. rewrite Next. exact Prior.
Qed.
Print Assumptions staged_iterations_last.
