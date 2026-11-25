(* Exact source copy; provenance in ../provenance.json. *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From firrtl Require Import Semantics_with_implicit_widths.
Lemma resize_uint_roundtrip_widen input_width target_width larger bits :
 size bits = input_width -> input_width <= target_width -> input_width <= larger ->
 zext_to target_width (take target_width (zext_to larger (take larger bits))) = zext_to target_width bits.
Proof.
 intros Size Target Large.
 assert (Take : take larger bits = bits).
 { apply take_oversize. rewrite Size. exact Large. }
 rewrite Take. unfold zext_to, zext.
 rewrite take_cat Size.
 assert (Small : (target_width < input_width) = false).
 { rewrite ltnNge Target. reflexivity. }
 rewrite Small take_zeros size_cat Size size_zeros.
 rewrite -catA zeros_cats.
 f_equal. f_equal. rewrite subnDA subnKC; [reflexivity|apply geq_minl].
Qed.
Print Assumptions resize_uint_roundtrip_widen.
