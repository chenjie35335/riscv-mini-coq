(* Exact source copy; provenance in ../provenance.json. *)
Require Import StoreDataShiftArithmetic.
From Coq Require Import Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Lemma store_mask_low (word:bits) width :
 (width<=size word)%nat ->
 andB word(ones width++zeros(size word-width))=
 take width word++zeros(size word-width).
Proof.
 revert word. induction width as[|width IH];intros word Bound.
 - rewrite subn0 /ones /copy cat0s take0 cat0s. exact(andB0 word).
 - destruct word as[|bit word];[discriminate Bound|].
   rewrite /= subSS /ones /copy /= andB_cons andbT.
   rewrite IH;[reflexivity|exact Bound].
Qed.
Lemma store_mask_shift_prefix (word:bits) offset width :
 (width<=size word)%nat ->
 drop offset(andB(zeros offset++word)
   (zeros offset++ones width++zeros(size word-width)))=
 take width word++zeros(size word-width).
Proof.
 intro Bound. induction offset as[|offset IH].
 - rewrite /zeros /copy /= drop0. apply store_mask_low. exact Bound.
 - rewrite /zeros /copy /=. exact IH.
Qed.
Lemma store_mask_shift_truncated (word:bits) offset remaining width :
 (remaining<=size word)%nat ->(width<=remaining)%nat ->
 drop offset(andB(take(offset+remaining)(zeros offset++word))
 (zeros offset++ones width++zeros(remaining-width)))=
 take width word++zeros(remaining-width).
Proof.
 intros Remaining Width. induction offset as[|offset IH].
 - rewrite add0n /zeros /copy /= drop0.
   assert(TakeSize:size(take remaining word)=remaining).
   { rewrite size_take. case: ifP=>B;[reflexivity|].
     apply/eqP. rewrite eqn_leq Remaining andbT leqNgt B. reflexivity. }
   pose proof(store_mask_low (take remaining word) width ltac:(rewrite TakeSize;exact Width)) as Mask.
   rewrite TakeSize (take_takel word Width) in Mask. exact Mask.
 - rewrite addSn /zeros /copy /=. exact IH.
Qed.
