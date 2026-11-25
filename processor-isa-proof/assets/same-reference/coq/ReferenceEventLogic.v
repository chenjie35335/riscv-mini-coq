(* Frozen-reference symbolic logic; preserved proof bodies. See ../provenance.json. *)
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.


Definition reference_event_value (guards:VarOrder.T -> bool) :=
 let v6323 := if (guards 2966) then false else true in
 let v6332 := if (guards 2357) then (v6323) else false in
 let v6354 := if (guards 2949) then (v6332) else true in
 let v6366 := if (guards 2010) then (v6354) else (v6332) in
 let v6376 := if (guards 2929) then (v6366) else true in
 let v6380 := if (guards 2912) then (v6376) else (v6366) in
 let v6390 := if (guards 2004) then (v6380) else (v6366) in
 let v6400 := if (guards 2909) then (v6390) else true in
 let v6404 := if (guards 2892) then (v6400) else (v6390) in
 let v6414 := if (guards 1998) then (v6404) else (v6390) in
 let v6424 := if (guards 2889) then (v6414) else true in
 let v6428 := if (guards 2872) then (v6424) else (v6414) in
 let v6438 := if (guards 1992) then (v6428) else (v6414) in
 let v6448 := if (guards 2867) then (v6438) else true in
 let v6452 := if (guards 2850) then (v6448) else (v6438) in
 let v6462 := if (guards 1986) then (v6452) else (v6438) in
 let v6472 := if (guards 2847) then (v6462) else true in
 let v6476 := if (guards 2830) then (v6472) else (v6462) in
 let v6486 := if (guards 1980) then (v6476) else (v6462) in
 let v6496 := if (guards 2825) then (v6486) else true in
 let v6500 := if (guards 2806) then (v6496) else (v6486) in
 let v6510 := if (guards 1974) then (v6500) else (v6486) in
 let v6523 := if (guards 2679) then (v6510) else true in
 let v6533 := if (guards 1970) then (v6523) else (v6510) in
 let v6548 := if (guards 2664) then (v6533) else true in
 let v6557 := if (guards 1966) then (v6548) else (v6533) in
 let v6573 := if (guards 2649) then (v6557) else true in
 let v6582 := if (guards 1962) then (v6573) else (v6557) in
 let v6589 := if (guards 2634) then true else (v6582) in
 let v6595 := if (guards 1958) then (v6589) else (v6582) in
 let v6614 := if (guards 2565) then (v6595) else true in
 let v6623 := if (guards 1886) then (v6614) else (v6595) in
 let v6630 := if (guards 2736) then true else (v6623) in
 let v6640 := if (guards 1951) then (v6630) else (v6623) in
 let v6663 := if (guards 2723) then (v6640) else true in
 let v6672 := if (guards 1946) then (v6663) else (v6640) in
 let v6687 := if (guards 2708) then (v6672) else true in
 let v6696 := if (guards 1941) then (v6687) else (v6672) in
 let v6701 := if (guards 1937) then true else (v6696) in
 let v6704 := if (guards 2751) then true else (v6701) in
 let v6705 := if (guards 2750) then true else (v6704) in
 let v6706 := if (guards 2748) then true else (v6705) in
 let v6709 := if (guards 1933) then (v6706) else (v6701) in
 let v6778 := if (guards 3042) then true else (v6709) in
 let v6779 := if (guards 1707) then (v6778) else false in
 let v6780 := (v6779) in
 v6780.

Definition reference_event_safe (g : VarOrder.T -> bool) : Prop :=
 g 3042 = false /\ g 1933 = false /\ g 1937 = false /\
 (g 1941 = true -> g 2708 = true) /\
 (g 1946 = true -> g 2723 = true) /\
 (g 1951 = true -> g 2736 = false) /\
 (g 1886 = true -> g 2565 = true) /\
 (g 1958 = true -> g 2634 = false) /\
 (g 1962 = true -> g 2649 = true) /\
 (g 1966 = true -> g 2664 = true) /\
 (g 1970 = true -> g 2679 = true) /\
 (g 1974 = true -> g 2806 = true -> g 2825 = true) /\
 (g 1980 = true -> g 2830 = true -> g 2847 = true) /\
 (g 1986 = true -> g 2850 = true -> g 2867 = true) /\
 (g 1992 = true -> g 2872 = true -> g 2889 = true) /\
 (g 1998 = true -> g 2892 = true -> g 2909 = true) /\
 (g 2004 = true -> g 2912 = true -> g 2929 = true) /\
 (g 2010 = true -> g 2949 = true) /\
 (g 2357 = true -> g 2966 = true).

Theorem reference_event_safe_false g :
 reference_event_safe g -> reference_event_value g = false.
Proof.
 unfold reference_event_safe. intro H.
 repeat match type of H with _ /\ _ => destruct H as [? H] end.
 set v6323 := (if (g 2966) then false else true).
 set v6332 := (if (g 2357) then (v6323) else false).
 assert (F6332 : v6332 = false).
 { unfold v6332, v6323.
 destruct (g 2357) eqn:G6332_2357, (g 2966) eqn:G6332_2966; simpl; try reflexivity; exfalso; first [congruence | match goal with H : _ -> _ |- _ => solve [pose proof (H Logic.eq_refl); congruence] | H : _ -> _ -> _ |- _ => solve [pose proof (H Logic.eq_refl Logic.eq_refl); congruence] end]. }
 set v6354 := (if (g 2949) then (v6332) else true).
 set v6366 := (if (g 2010) then (v6354) else (v6332)).
 assert (F6366 : v6366 = false).
 { unfold v6366, v6354.
 rewrite ?F6332.
 destruct (g 2010) eqn:G6366_2010, (g 2949) eqn:G6366_2949; simpl; try reflexivity; exfalso; first [congruence | match goal with H : _ -> _ |- _ => solve [pose proof (H Logic.eq_refl); congruence] | H : _ -> _ -> _ |- _ => solve [pose proof (H Logic.eq_refl Logic.eq_refl); congruence] end]. }
 set v6376 := (if (g 2929) then (v6366) else true).
 set v6380 := (if (g 2912) then (v6376) else (v6366)).
 set v6390 := (if (g 2004) then (v6380) else (v6366)).
 assert (F6390 : v6390 = false).
 { unfold v6390, v6380, v6376.
 rewrite ?F6332 ?F6366.
 destruct (g 2004) eqn:G6390_2004, (g 2912) eqn:G6390_2912, (g 2929) eqn:G6390_2929; simpl; try reflexivity; exfalso; first [congruence | match goal with H : _ -> _ |- _ => solve [pose proof (H Logic.eq_refl); congruence] | H : _ -> _ -> _ |- _ => solve [pose proof (H Logic.eq_refl Logic.eq_refl); congruence] end]. }
 set v6400 := (if (g 2909) then (v6390) else true).
 set v6404 := (if (g 2892) then (v6400) else (v6390)).
 set v6414 := (if (g 1998) then (v6404) else (v6390)).
 assert (F6414 : v6414 = false).
 { unfold v6414, v6404, v6400.
 rewrite ?F6332 ?F6366 ?F6390.
 destruct (g 1998) eqn:G6414_1998, (g 2892) eqn:G6414_2892, (g 2909) eqn:G6414_2909; simpl; try reflexivity; exfalso; first [congruence | match goal with H : _ -> _ |- _ => solve [pose proof (H Logic.eq_refl); congruence] | H : _ -> _ -> _ |- _ => solve [pose proof (H Logic.eq_refl Logic.eq_refl); congruence] end]. }
 set v6424 := (if (g 2889) then (v6414) else true).
 set v6428 := (if (g 2872) then (v6424) else (v6414)).
 set v6438 := (if (g 1992) then (v6428) else (v6414)).
 assert (F6438 : v6438 = false).
 { unfold v6438, v6428, v6424.
 rewrite ?F6332 ?F6366 ?F6390 ?F6414.
 destruct (g 1992) eqn:G6438_1992, (g 2872) eqn:G6438_2872, (g 2889) eqn:G6438_2889; simpl; try reflexivity; exfalso; first [congruence | match goal with H : _ -> _ |- _ => solve [pose proof (H Logic.eq_refl); congruence] | H : _ -> _ -> _ |- _ => solve [pose proof (H Logic.eq_refl Logic.eq_refl); congruence] end]. }
 set v6448 := (if (g 2867) then (v6438) else true).
 set v6452 := (if (g 2850) then (v6448) else (v6438)).
 set v6462 := (if (g 1986) then (v6452) else (v6438)).
 assert (F6462 : v6462 = false).
 { unfold v6462, v6452, v6448.
 rewrite ?F6332 ?F6366 ?F6390 ?F6414 ?F6438.
 destruct (g 1986) eqn:G6462_1986, (g 2850) eqn:G6462_2850, (g 2867) eqn:G6462_2867; simpl; try reflexivity; exfalso; first [congruence | match goal with H : _ -> _ |- _ => solve [pose proof (H Logic.eq_refl); congruence] | H : _ -> _ -> _ |- _ => solve [pose proof (H Logic.eq_refl Logic.eq_refl); congruence] end]. }
 set v6472 := (if (g 2847) then (v6462) else true).
 set v6476 := (if (g 2830) then (v6472) else (v6462)).
 set v6486 := (if (g 1980) then (v6476) else (v6462)).
 assert (F6486 : v6486 = false).
 { unfold v6486, v6476, v6472.
 rewrite ?F6332 ?F6366 ?F6390 ?F6414 ?F6438 ?F6462.
 destruct (g 1980) eqn:G6486_1980, (g 2830) eqn:G6486_2830, (g 2847) eqn:G6486_2847; simpl; try reflexivity; exfalso; first [congruence | match goal with H : _ -> _ |- _ => solve [pose proof (H Logic.eq_refl); congruence] | H : _ -> _ -> _ |- _ => solve [pose proof (H Logic.eq_refl Logic.eq_refl); congruence] end]. }
 set v6496 := (if (g 2825) then (v6486) else true).
 set v6500 := (if (g 2806) then (v6496) else (v6486)).
 set v6510 := (if (g 1974) then (v6500) else (v6486)).
 assert (F6510 : v6510 = false).
 { unfold v6510, v6500, v6496.
 rewrite ?F6332 ?F6366 ?F6390 ?F6414 ?F6438 ?F6462 ?F6486.
 destruct (g 1974) eqn:G6510_1974, (g 2806) eqn:G6510_2806, (g 2825) eqn:G6510_2825; simpl; try reflexivity; exfalso; first [congruence | match goal with H : _ -> _ |- _ => solve [pose proof (H Logic.eq_refl); congruence] | H : _ -> _ -> _ |- _ => solve [pose proof (H Logic.eq_refl Logic.eq_refl); congruence] end]. }
 set v6523 := (if (g 2679) then (v6510) else true).
 set v6533 := (if (g 1970) then (v6523) else (v6510)).
 assert (F6533 : v6533 = false).
 { unfold v6533, v6523.
 rewrite ?F6332 ?F6366 ?F6390 ?F6414 ?F6438 ?F6462 ?F6486 ?F6510.
 destruct (g 1970) eqn:G6533_1970, (g 2679) eqn:G6533_2679; simpl; try reflexivity; exfalso; first [congruence | match goal with H : _ -> _ |- _ => solve [pose proof (H Logic.eq_refl); congruence] | H : _ -> _ -> _ |- _ => solve [pose proof (H Logic.eq_refl Logic.eq_refl); congruence] end]. }
 set v6548 := (if (g 2664) then (v6533) else true).
 set v6557 := (if (g 1966) then (v6548) else (v6533)).
 assert (F6557 : v6557 = false).
 { unfold v6557, v6548.
 rewrite ?F6332 ?F6366 ?F6390 ?F6414 ?F6438 ?F6462 ?F6486 ?F6510 ?F6533.
 destruct (g 1966) eqn:G6557_1966, (g 2664) eqn:G6557_2664; simpl; try reflexivity; exfalso; first [congruence | match goal with H : _ -> _ |- _ => solve [pose proof (H Logic.eq_refl); congruence] | H : _ -> _ -> _ |- _ => solve [pose proof (H Logic.eq_refl Logic.eq_refl); congruence] end]. }
 set v6573 := (if (g 2649) then (v6557) else true).
 set v6582 := (if (g 1962) then (v6573) else (v6557)).
 assert (F6582 : v6582 = false).
 { unfold v6582, v6573.
 rewrite ?F6332 ?F6366 ?F6390 ?F6414 ?F6438 ?F6462 ?F6486 ?F6510 ?F6533 ?F6557.
 destruct (g 1962) eqn:G6582_1962, (g 2649) eqn:G6582_2649; simpl; try reflexivity; exfalso; first [congruence | match goal with H : _ -> _ |- _ => solve [pose proof (H Logic.eq_refl); congruence] | H : _ -> _ -> _ |- _ => solve [pose proof (H Logic.eq_refl Logic.eq_refl); congruence] end]. }
 set v6589 := (if (g 2634) then true else (v6582)).
 set v6595 := (if (g 1958) then (v6589) else (v6582)).
 assert (F6595 : v6595 = false).
 { unfold v6595, v6589.
 rewrite ?F6332 ?F6366 ?F6390 ?F6414 ?F6438 ?F6462 ?F6486 ?F6510 ?F6533 ?F6557 ?F6582.
 destruct (g 1958) eqn:G6595_1958, (g 2634) eqn:G6595_2634; simpl; try reflexivity; exfalso; first [congruence | match goal with H : _ -> _ |- _ => solve [pose proof (H Logic.eq_refl); congruence] | H : _ -> _ -> _ |- _ => solve [pose proof (H Logic.eq_refl Logic.eq_refl); congruence] end]. }
 set v6614 := (if (g 2565) then (v6595) else true).
 set v6623 := (if (g 1886) then (v6614) else (v6595)).
 assert (F6623 : v6623 = false).
 { unfold v6623, v6614.
 rewrite ?F6332 ?F6366 ?F6390 ?F6414 ?F6438 ?F6462 ?F6486 ?F6510 ?F6533 ?F6557 ?F6582 ?F6595.
 destruct (g 1886) eqn:G6623_1886, (g 2565) eqn:G6623_2565; simpl; try reflexivity; exfalso; first [congruence | match goal with H : _ -> _ |- _ => solve [pose proof (H Logic.eq_refl); congruence] | H : _ -> _ -> _ |- _ => solve [pose proof (H Logic.eq_refl Logic.eq_refl); congruence] end]. }
 set v6630 := (if (g 2736) then true else (v6623)).
 set v6640 := (if (g 1951) then (v6630) else (v6623)).
 assert (F6640 : v6640 = false).
 { unfold v6640, v6630.
 rewrite ?F6332 ?F6366 ?F6390 ?F6414 ?F6438 ?F6462 ?F6486 ?F6510 ?F6533 ?F6557 ?F6582 ?F6595 ?F6623.
 destruct (g 1951) eqn:G6640_1951, (g 2736) eqn:G6640_2736; simpl; try reflexivity; exfalso; first [congruence | match goal with H : _ -> _ |- _ => solve [pose proof (H Logic.eq_refl); congruence] | H : _ -> _ -> _ |- _ => solve [pose proof (H Logic.eq_refl Logic.eq_refl); congruence] end]. }
 set v6663 := (if (g 2723) then (v6640) else true).
 set v6672 := (if (g 1946) then (v6663) else (v6640)).
 assert (F6672 : v6672 = false).
 { unfold v6672, v6663.
 rewrite ?F6332 ?F6366 ?F6390 ?F6414 ?F6438 ?F6462 ?F6486 ?F6510 ?F6533 ?F6557 ?F6582 ?F6595 ?F6623 ?F6640.
 destruct (g 1946) eqn:G6672_1946, (g 2723) eqn:G6672_2723; simpl; try reflexivity; exfalso; first [congruence | match goal with H : _ -> _ |- _ => solve [pose proof (H Logic.eq_refl); congruence] | H : _ -> _ -> _ |- _ => solve [pose proof (H Logic.eq_refl Logic.eq_refl); congruence] end]. }
 set v6687 := (if (g 2708) then (v6672) else true).
 set v6696 := (if (g 1941) then (v6687) else (v6672)).
 assert (F6696 : v6696 = false).
 { unfold v6696, v6687.
 rewrite ?F6332 ?F6366 ?F6390 ?F6414 ?F6438 ?F6462 ?F6486 ?F6510 ?F6533 ?F6557 ?F6582 ?F6595 ?F6623 ?F6640 ?F6672.
 destruct (g 1941) eqn:G6696_1941, (g 2708) eqn:G6696_2708; simpl; try reflexivity; exfalso; first [congruence | match goal with H : _ -> _ |- _ => solve [pose proof (H Logic.eq_refl); congruence] | H : _ -> _ -> _ |- _ => solve [pose proof (H Logic.eq_refl Logic.eq_refl); congruence] end]. }
 set v6701 := (if (g 1937) then true else (v6696)).
 assert (F6701 : v6701 = false).
 { unfold v6701.
 rewrite ?F6332 ?F6366 ?F6390 ?F6414 ?F6438 ?F6462 ?F6486 ?F6510 ?F6533 ?F6557 ?F6582 ?F6595 ?F6623 ?F6640 ?F6672 ?F6696.
 destruct (g 1937) eqn:G6701_1937; simpl; try reflexivity; exfalso; first [congruence | match goal with H : _ -> _ |- _ => solve [pose proof (H Logic.eq_refl); congruence] | H : _ -> _ -> _ |- _ => solve [pose proof (H Logic.eq_refl Logic.eq_refl); congruence] end]. }
 set v6704 := (if (g 2751) then true else (v6701)).
 set v6705 := (if (g 2750) then true else (v6704)).
 set v6706 := (if (g 2748) then true else (v6705)).
 set v6709 := (if (g 1933) then (v6706) else (v6701)).
 assert (F6709 : v6709 = false).
 { unfold v6709, v6706, v6705, v6704.
 rewrite ?F6332 ?F6366 ?F6390 ?F6414 ?F6438 ?F6462 ?F6486 ?F6510 ?F6533 ?F6557 ?F6582 ?F6595 ?F6623 ?F6640 ?F6672 ?F6696 ?F6701.
 destruct (g 1933) eqn:G6709_1933, (g 2748) eqn:G6709_2748, (g 2750) eqn:G6709_2750, (g 2751) eqn:G6709_2751; simpl; try reflexivity; exfalso; first [congruence | match goal with H : _ -> _ |- _ => solve [pose proof (H Logic.eq_refl); congruence] | H : _ -> _ -> _ |- _ => solve [pose proof (H Logic.eq_refl Logic.eq_refl); congruence] end]. }
 set v6778 := (if (g 3042) then true else (v6709)).
 assert (F6778 : v6778 = false).
 { unfold v6778.
 rewrite ?F6332 ?F6366 ?F6390 ?F6414 ?F6438 ?F6462 ?F6486 ?F6510 ?F6533 ?F6557 ?F6582 ?F6595 ?F6623 ?F6640 ?F6672 ?F6696 ?F6701 ?F6709.
 destruct (g 3042) eqn:G6778_3042; simpl; try reflexivity; exfalso; first [congruence | match goal with H : _ -> _ |- _ => solve [pose proof (H Logic.eq_refl); congruence] | H : _ -> _ -> _ |- _ => solve [pose proof (H Logic.eq_refl Logic.eq_refl); congruence] end]. }
 set v6779 := (if (g 1707) then (v6778) else false).
 assert (F6779 : v6779 = false).
 { unfold v6779.
 rewrite ?F6332 ?F6366 ?F6390 ?F6414 ?F6438 ?F6462 ?F6486 ?F6510 ?F6533 ?F6557 ?F6582 ?F6595 ?F6623 ?F6640 ?F6672 ?F6696 ?F6701 ?F6709 ?F6778.
 destruct (g 1707) eqn:G6779_1707; simpl; try reflexivity; exfalso; first [congruence | match goal with H : _ -> _ |- _ => solve [pose proof (H Logic.eq_refl); congruence] | H : _ -> _ -> _ |- _ => solve [pose proof (H Logic.eq_refl Logic.eq_refl); congruence] end]. }
 set v6780 := ((v6779)).
 assert (F6780 : v6780 = false).
 { unfold v6780.
 rewrite ?F6332 ?F6366 ?F6390 ?F6414 ?F6438 ?F6462 ?F6486 ?F6510 ?F6533 ?F6557 ?F6582 ?F6595 ?F6623 ?F6640 ?F6672 ?F6696 ?F6701 ?F6709 ?F6778 ?F6779.
 reflexivity. }
 change (v6780 = false). exact F6780.
Qed.
