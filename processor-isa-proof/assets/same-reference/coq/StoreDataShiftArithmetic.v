(* Exact source copy; provenance in ../provenance.json. *)
From Coq Require Import Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Lemma store_shift_slice_cancel (word:bits) offset width :
 drop offset(take(offset+width)(zeros offset++word))=take width word.
Proof.
 induction offset as[|offset IH].
 - rewrite add0n /zeros /copy cat0s drop0. reflexivity.
 - rewrite addSn /zeros /copy /=.
 change(drop offset(take(offset+width)(zeros offset++word))=take width word).
 exact IH.
Qed.
Lemma store_shift_truncate_cancel (word:bits) offset :
 (offset<=32)%nat ->
 drop offset(take 32(zeros offset++word))=take(32-offset)word.
Proof.
 intro Bound. replace 32 with (offset+(32-offset))%nat at 1 by exact(subnKC Bound).
 exact(store_shift_slice_cancel word offset (32-offset)).
Qed.
Lemma store_shift_selected_low (word:bits) offset width :
 (offset<=32)%nat ->(width<=32-offset)%nat ->
 take width(drop offset(take 32(zeros offset++word)))=take width word.
Proof.
 intros Offset Width. rewrite(store_shift_truncate_cancel word offset Offset).
 exact(take_takel word Width).
Qed.
Print Assumptions store_shift_selected_low.
Lemma store_mask_prefix (prefix suffix:bits) :
 andB (prefix++suffix)(ones(size prefix)++zeros(size suffix))=
 prefix++zeros(size suffix).
Proof.
 induction prefix as[|bit prefix IH].
 - cbn [size cat]. exact(andB0 suffix).
 - rewrite /ones /copy /= andB_cons andbT IH. reflexivity.
Qed.
Lemma store_mask_shifted_prefix (prefix suffix:bits) offset :
 drop offset(andB (zeros offset++prefix++suffix)
 (zeros offset++ones(size prefix)++zeros(size suffix)))=
 prefix++zeros(size suffix).
Proof.
 induction offset as[|offset IH].
 - rewrite /zeros /copy /= drop0. exact(store_mask_prefix prefix suffix).
 - rewrite /zeros /copy /=. exact IH.
Qed.
Print Assumptions store_mask_shifted_prefix.
