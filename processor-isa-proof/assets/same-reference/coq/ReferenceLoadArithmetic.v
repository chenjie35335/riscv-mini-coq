(* Exact source copy; provenance in ../provenance.json. *)
From Coq Require Import Lia ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Local Open Scope N_scope.
Lemma reference_load_mask_low width word suffix :
 (width <= size word)%coq_nat ->
 take width (andB word (ones width ++ suffix)) = take width word.
Proof.
 revert word. induction width as [|width IH]; intros word Bound.
 - rewrite !take0. reflexivity.
 - destruct word as [|bit word]; [cbn [size] in Bound;lia|].
   change (take (S width) (andB (bit::word) (true::(ones width ++ suffix))) = take (S width) (bit::word)).
   rewrite andB_cons. cbn [take]. rewrite andbT. f_equal. apply IH. cbn [size] in Bound. lia.
Qed.
Lemma reference_load_mask8 : from_N 64 255 = ones 8 ++ zeros 56.
Proof. vm_compute. reflexivity. Qed.
Lemma reference_load_mask16 : from_N 64 65535 = ones 16 ++ zeros 48.
Proof. vm_compute. reflexivity. Qed.
Lemma reference_load_mask32 : from_N 64 4294967295 = ones 32 ++ zeros 32.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_load_masked_extract word : size word = 64%nat ->
 take 8 (andB word (from_N 64 255)) = take 8 word /\
 take 16 (andB word (from_N 64 65535)) = take 16 word /\
 take 32 (andB word (from_N 64 4294967295)) = take 32 word.
Proof.
 intro Size. rewrite reference_load_mask8 reference_load_mask16 reference_load_mask32.
 split; [|split]; apply reference_load_mask_low; rewrite Size; lia.
Qed.
Print Assumptions reference_load_masked_extract.
From firrtl Require Import Semantics_with_implicit_widths.
Lemma reference_load_sext_truncate word target larger :
 (size word <= target)%nat -> (target <= larger)%nat ->
 take target (sext_to larger word) = sext_to target word.
Proof.
 intros Fits Wider. unfold sext_to,sext.
 rewrite take_cat.
 assert (Small : (target < size word)%nat = false).
 { rewrite ltnNge Fits. reflexivity. }
 rewrite Small take_nseq; [reflexivity|].
 exact (leq_sub2r (size word) Wider).
Qed.
Theorem reference_load_signed32 word : (size word <= 32)%nat ->
 take 32 (sext_to 33 word) = word ++ nseq (32-size word)%nat (msb word).
Proof.
 intro Fits. rewrite (reference_load_sext_truncate word 32 33 Fits ltac:(reflexivity)).
 reflexivity.
Qed.
Print Assumptions reference_load_signed32.
Theorem reference_load_unsigned32 word : (size word < 32)%nat ->
 take 32 (sext_to 33 (zext 1 word)) = zext_to 32 word.
Proof.
 intro Fits.
 assert (FitsZ : (size (zext 1 word) <= 32)%nat).
 { rewrite size_zext addn1. exact Fits. }
 rewrite (reference_load_sext_truncate (zext 1 word) 32 33 FitsZ ltac:(reflexivity)).
 unfold sext_to,sext. rewrite (@msb_zext 1 word ltac:(reflexivity)).
 change (zext (32-size (zext 1 word)) (zext 1 word) = zext (32-size word) word).
 rewrite zext_zext size_zext subnDA subnK; [reflexivity|].
 rewrite subn_gt0. exact Fits.
Qed.
Print Assumptions reference_load_unsigned32.
Lemma reference_load_zext_truncate word target larger :
 (size word <= target)%nat -> (target <= larger)%nat ->
 take target (zext_to larger word) = zext_to target word.
Proof.
 intros Fits Wider. unfold zext_to,zext.
 rewrite take_cat.
 assert (Small : (target < size word)%nat = false).
 { rewrite ltnNge Fits. reflexivity. }
 rewrite Small take_nseq; [reflexivity|].
 exact (leq_sub2r (size word) Wider).
Qed.
Theorem reference_load_padding_extract word width :
 (size word <= 32)%nat -> (width <= 32)%nat ->
 take width (zext_to 64 word) = take width (zext_to 32 word).
Proof.
 intros Fits Width.
 rewrite -(reference_load_zext_truncate word 32 64 Fits ltac:(reflexivity)).
 rewrite take_take; [reflexivity|exact Width].
Qed.
Print Assumptions reference_load_padding_extract.
Theorem reference_load_padded_masked_extract word : (size word <= 32)%nat ->
 take 8 (andB (zext_to 64 word) (from_N 64 255)) = take 8 (zext_to 32 word) /\
 take 16 (andB (zext_to 64 word) (from_N 64 65535)) = take 16 (zext_to 32 word) /\
 take 32 (andB (zext_to 64 word) (from_N 64 4294967295)) = take 32 (zext_to 32 word).
Proof.
 intro Fits.
 assert (Wide : size (zext_to 64 word) = 64%nat).
 { unfold zext_to. rewrite size_zext addnC subnK; [reflexivity|].
   assert (Bound : (32 <= 64)%nat) by reflexivity.
   exact (leq_trans Fits Bound). }
 destruct (reference_load_masked_extract (zext_to 64 word) Wide) as [Byte [Half Word]].
 rewrite Byte Half Word.
 split; [|split]; apply reference_load_padding_extract; try exact Fits; reflexivity.
Qed.
Print Assumptions reference_load_padded_masked_extract.
