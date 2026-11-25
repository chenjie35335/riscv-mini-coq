(* Exact symbolic shift declarations/proofs; isolated imports. See ../provenance.json. *)
From Coq Require Import Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From firrtl Require Import Semantics_with_implicit_widths.


Definition rf_shift_center_word arithmetic word right :=
 take 32(sext_to 33(drop(minn(to_nat(take 5 right))32)
 (word++andB [::arithmetic](drop 31(take 32 word))))).

Definition rf_shift_word direction arithmetic left right :=
 let selected:=if direction then left else rev left in
 let shifted:=rf_shift_center_word (direction && arithmetic) selected right in
 if direction then shifted else rev shifted.

Definition rf_shift_at direction arithmetic left amount :=
 let selected:=if direction then left else rev left in
 let shifted:=take 32(sext_to 33(drop(minn amount 32)(selected++andB [::direction && arithmetic](drop 31(take 32 selected))))) in
 if direction then shifted else rev shifted.

Definition rf_shift_spec direction arithmetic left amount :=
 if direction then if arithmetic then sext_to 32(drop amount left) else zext_to 32(drop amount left)
 else take 32(zeros amount++left).

Lemma rf_shift_word_at direction arithmetic left right :
 rf_shift_word direction arithmetic left right=rf_shift_at direction arithmetic left(to_nat(take 5 right)).
Proof. reflexivity. Qed.

Lemma rf_shift_at_correct direction arithmetic left amount :
 size left=32%nat ->(amount<32)%coq_nat ->
 rf_shift_at direction arithmetic left amount=rf_shift_spec direction arithmetic left amount.
Proof.
 intros Size Amount.
 do 32(destruct left as[|? left];[discriminate Size|]). destruct left;[|discriminate Size].
 do 32(destruct amount as[|amount];[destruct direction,arithmetic;
 vm_compute;repeat rewrite ?andbT ?andbF ?orbT ?orbF;reflexivity|]). lia.
Qed.

Theorem rf_shift_word_correct direction arithmetic left right :
 size left=32%nat ->size right=32%nat ->
 rf_shift_word direction arithmetic left right=rf_shift_spec direction arithmetic left(to_nat(take 5 right)).
Proof.
 intros Left Right. rewrite rf_shift_word_at. apply rf_shift_at_correct;[exact Left|].
 pose proof(to_nat_bounded(take 5 right))as Bound. rewrite size_take Right in Bound. exact(elimT ltP Bound).
Qed.
