(* Exact source copy; provenance in ../provenance.json. *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Inductive rf_write_effect :=
 | RFNoWrite
 | RFWrite (destination : nat) (word : bits).
Definition rf_bank := nat -> bits.
Definition rf_apply_effect (bank : rf_bank) (effect : rf_write_effect) (index : nat) : bits :=
 if index == 0 then nseq 32 false else
 match effect with
 | RFNoWrite => bank index
 | RFWrite destination word => if index == destination then word else bank index
 end.
Lemma rf_apply_effect_x0 bank effect : rf_apply_effect bank effect 0 = nseq 32 false.
Proof. reflexivity. Qed.
Lemma rf_apply_effect_equal left right effect :
 (forall index, left index = right index) ->
 forall index, rf_apply_effect left effect index = rf_apply_effect right effect index.
Proof.
 intros Equal index. unfold rf_apply_effect. rewrite Equal. reflexivity.
Qed.
Lemma rf_apply_effect_no_write bank :
 bank 0 = nseq 32 false -> forall index, rf_apply_effect bank RFNoWrite index = bank index.
Proof.
 intros Zero index. unfold rf_apply_effect.
 case E: (index == 0); [move/eqP: E => ->; symmetry;exact Zero|reflexivity].
Qed.
Print Assumptions rf_apply_effect_equal.
