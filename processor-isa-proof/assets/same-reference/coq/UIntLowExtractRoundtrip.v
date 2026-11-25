(* Exact source copy; provenance in ../provenance.json. *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths.
Lemma uint32_low_extract_roundtrip larger bits :
 size bits = 32%nat -> 32 <= larger ->
 eval_unop (Uextr 31 0) (Gval (Fuint larger) (zext_to larger (take larger bits))) =
 Some (Gval (Fuint 32) bits).
Proof.
 intros Size Bound.
 assert (Take : take larger bits = bits).
 { apply take_oversize. rewrite Size. exact Bound. }
 cbn [eval_unop].
 assert (Range : (0 <= 31 < larger)%nat = true).
 { exact Bound. }
 rewrite Range subn0 drop0 Take.
 change (Some (Gval (Fuint 32) (take 32 (zext_to larger bits))) = Some (Gval (Fuint 32) bits)).
 unfold zext_to, zext.
 rewrite take_cat Size ltnn subnn take0 cats0.
 reflexivity.
Qed.
Print Assumptions uint32_low_extract_roundtrip.
