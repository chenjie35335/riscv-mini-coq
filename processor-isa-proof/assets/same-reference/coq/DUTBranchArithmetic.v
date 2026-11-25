(* Extracted from the existing processor proof. Source mapping: ../provenance.json.
   Proof bodies below are unchanged; imports isolate the shared reference semantics. *)
Require Import ReferenceRedirectArithmetic.
From Coq Require Import NArith ZArith List Lia btauto.Btauto.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits NBitsDef NBitsOp.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.

Lemma dut_from_Zneg_inv n z : from_Zneg n z = invB (from_Zpos n z).
Proof.
 revert z. induction n as [|n IH]; intro z; [reflexivity|].
 cbn [from_Zneg from_Zpos invB]. rewrite IH.
 rewrite <- Z.negb_odd. reflexivity.
Qed.

Lemma dut_from_Z33_value z :
 (-4294967296 < z < 4294967296)%Z ->
 to_Zpos (from_Z 33 z) = (if Z.ltb z 0 then 8589934592 + z else z)%Z.
Proof.
 intro Bounds. destruct z as [|p|p].
 - reflexivity.
 - change (to_Zpos (from_Zpos 33 (Z.pos p)) = Z.pos p).
   rewrite to_Zpos_from_Zpos_bounded; [reflexivity|lia|change (Z.pos p < 8589934592)%Z; lia].
 - change (-4294967296 < - Z.pos p < 4294967296)%Z in Bounds.
   change (to_Zpos (from_Zneg 33 (Z.pred (Z.pos p))) = (8589934592 - Z.pos p)%Z).
   rewrite dut_from_Zneg_inv to_Zpos_invB_full size_from_Zpos.
   rewrite to_Zpos_from_Zpos_bounded; change (2 ^ Z.of_nat 33)%Z with 8589934592%Z; unfold Z.one; lia.
Qed.

Definition dut_branch_difference left right :=
 take 32 (from_Z 33 (to_Zpos left - to_Zpos right)%Z).

Lemma dut_branch_difference_subB left right :
 size left = 32%nat -> size right = 32%nat ->
 dut_branch_difference left right = subB left right.
Proof.
 intros LeftSize RightSize.
 assert (SameSize : size left = size right) by lia.
 assert (Bound : (-4294967296 < to_Zpos left - to_Zpos right < 4294967296)%Z).
 { pose proof (to_Zpos_bounded left) as L. pose proof (to_Zpos_bounded right) as R.
   pose proof (@to_Zpos_ge0 left). pose proof (@to_Zpos_ge0 right).
   rewrite LeftSize in L. rewrite RightSize in R.
   change (to_Zpos left < 4294967296)%Z in L.
   change (to_Zpos right < 4294967296)%Z in R. lia. }
 apply to_Zpos_inj_ss.
 - unfold dut_branch_difference. rewrite size_take size_from_Z size_subB LeftSize RightSize. reflexivity.
 - unfold dut_branch_difference.
   replace (take 32 (from_Z 33 (to_Zpos left - to_Zpos right)%Z)) with
    (low 32 (from_Z 33 (to_Zpos left - to_Zpos right)%Z)).
   2: { unfold low. rewrite size_from_Z. change (32 - 33)%nat with 0%nat. rewrite zeros0 cats0. reflexivity. }
   rewrite <- to_Zpos_mod_pow2.
   rewrite (dut_from_Z33_value _ Bound) (to_Zpos_subB' SameSize) LeftSize.
   change ((if Z.ltb (to_Zpos left - to_Zpos right) 0 then 8589934592 + (to_Zpos left - to_Zpos right) else to_Zpos left - to_Zpos right) mod 4294967296 = (to_Zpos left - to_Zpos right) mod 4294967296)%Z.
   destruct (Z.ltb (to_Zpos left - to_Zpos right) 0); [|reflexivity].
   replace (8589934592 + (to_Zpos left - to_Zpos right))%Z with
    ((to_Zpos left - to_Zpos right) + 2 * 4294967296)%Z by ring.
   rewrite Z.mod_add; [reflexivity|discriminate].
Qed.

Lemma dut_unsigned_compare left right :
 size left = size right ->
 (if msb left == msb right then msb (subB left right) else msb right) =
 N.ltb (to_N left) (to_N right).
Proof.
 intro SameSize. rewrite <- to_N_ltB_eqn.
 rewrite (ltB_equiv_borrow_subB SameSize) (borrow_subB_eq_msbs SameSize).
 destruct (msb left), (msb right), (msb (subB left right)); reflexivity.
Qed.

Lemma dut_signed_compare left right :
 size left = size right ->
 (if msb left == msb right then msb (subB left right) else msb left) =
 Z.ltb (to_Z left) (to_Z right).
Proof.
 intro SameSize. rewrite <- (to_Z_sltB_eqn SameSize).
 destruct (msb left == msb right) eqn:Same.
 - rewrite <- (ltB_sltB_same SameSize Same), to_N_ltB_eqn.
   pose proof (dut_unsigned_compare left right SameSize) as U. rewrite Same in U. exact U.
 - unfold sltB, msb.
   destruct (splitmsb left) as [lt ls] eqn:L.
   destruct (splitmsb right) as [rt rs] eqn:R.
   unfold msb in Same. rewrite L R in Same. cbn in Same.
   destruct ls, rs; try discriminate Same; reflexivity.
Qed.

Lemma dut_sub_zero left right :
 size left = size right -> is_zero (subB left right) = (left == right).
Proof.
 intro SameSize. destruct (eqP : reflect (left = right) (left == right)) as [Equal|Different].
 - subst right. rewrite subB_same. exact (zeros_is_zero (size left)).
 - destruct (is_zero (subB left right)) eqn:Zero; [|reflexivity].
   exfalso. apply Different. apply (to_Zpos_inj_ss SameSize).
   pose proof (is_zero_to_Zpos Zero) as V.
   rewrite (to_Zpos_subB SameSize) in V.
   pose proof (to_Zpos_bounded left) as L. pose proof (to_Zpos_bounded right) as R.
   pose proof (@to_Zpos_ge0 left). pose proof (@to_Zpos_ge0 right).
   rewrite <- SameSize in R.
   destruct (borrow_subB left right); cbn [Z.b2z] in V; lia.
Qed.

Lemma dut_eq_numeric left right :
 size left = size right ->
 is_zero (subB left right) = N.eqb (to_N left) (to_N right).
Proof.
 intro SameSize. rewrite (dut_sub_zero left right SameSize).
 destruct (eqP : reflect (left = right) (left == right)) as [Equal|Different].
 - subst right. rewrite N.eqb_refl. reflexivity.
 - symmetry. apply N.eqb_neq. intro Equal. apply Different.
   apply (to_Zpos_inj_ss SameSize). rewrite !to_Zpos_N Equal. reflexivity.
Qed.

Lemma dut_reduction_or bits : foldr orb false bits = negb (is_zero bits).
Proof.
 induction bits as [|bit bits IH]; [reflexivity|].
 cbn [foldr]. rewrite is_zero_cons IH. destruct bit; reflexivity.
Qed.

Lemma dut_sign_extract bits : size bits = 32%nat ->
 drop 31 (take 32 bits) = [::msb bits].
Proof.
 intro Size. rewrite <- Size at 1. rewrite take_size.
 rewrite (drop_nth false); [|rewrite Size; reflexivity].
 change (nth false bits 31 :: drop 32 bits = [::msb bits]).
 rewrite <- Size at 1. rewrite drop_size. f_equal.
 replace 31%nat with (size bits).-1 by (rewrite Size; reflexivity).
 rewrite nth_last. unfold msb, splitmsb, split_last, lastd. destruct bits; reflexivity.
Qed.

Definition dut_branch_bit_function kind left right :=
 let unequal := foldr orb false (subB left right) in
 let same_sign := msb left == msb right in
 let signed_lt := if same_sign then msb (subB left right) else msb left in
 let unsigned_lt := if same_sign then msb (subB left right) else msb right in
 (N.eqb kind 3 && negb unequal) || (N.eqb kind 6 && unequal) ||
 (N.eqb kind 2 && signed_lt) || (N.eqb kind 5 && negb signed_lt) ||
 (N.eqb kind 1 && unsigned_lt) || (N.eqb kind 4 && negb unsigned_lt).

Definition dut_branch_function kind left right :=
 (N.eqb kind 3 && N.eqb left right) || (N.eqb kind 6 && negb (N.eqb left right)) ||
 (N.eqb kind 2 && Z.ltb (reference_redirect_signed left) (reference_redirect_signed right)) ||
 (N.eqb kind 5 && Z.leb (reference_redirect_signed right) (reference_redirect_signed left)) ||
 (N.eqb kind 1 && N.ltb left right) || (N.eqb kind 4 && N.leb right left).

Definition dut_redirect_function selector kind left right :=
 N.eqb selector 1 || dut_branch_function kind left right.

Lemma dut_branch_numeric kind left right :
 size left = 32%nat -> size right = 32%nat ->
 dut_branch_bit_function kind left right = dut_branch_function kind (to_N left) (to_N right).
Proof.
 intros LeftSize RightSize. assert (SameSize : size left = size right) by lia.
 unfold dut_branch_bit_function, dut_branch_function.
 rewrite dut_reduction_or negbK (dut_eq_numeric left right SameSize).
 rewrite (dut_signed_compare left right SameSize) (dut_unsigned_compare left right SameSize).
 rewrite (reference_redirect_signed32 left LeftSize) (reference_redirect_signed32 right RightSize).
 rewrite N.leb_antisym Z.leb_antisym. reflexivity.
Qed.

Lemma dut_boolean_binop op a b :
 eval_binop op (Gval (Fuint 1) [::a]) (Gval (Fuint 1) [::b]) =
 match op with
 | Band => Some (Gval (Fuint 1) [::a && b])
 | Bor => Some (Gval (Fuint 1) [::a || b])
 | Bcomp Beq => Some (Gval (Fuint 1) [::a == b])
 | _ => eval_binop op (Gval (Fuint 1) [::a]) (Gval (Fuint 1) [::b])
 end.
Proof. destruct op; try match goal with c : bcmp |- _ => destruct c end; destruct a,b; reflexivity. Qed.

Definition dut_operand_tests_match kind dut_left dut_right ref_left ref_right : Prop :=
 ((N.eqb kind 3 || N.eqb kind 6) = true -> N.eqb dut_left dut_right = N.eqb ref_left ref_right) /\
 ((N.eqb kind 2 || N.eqb kind 5) = true ->
  Z.ltb (reference_redirect_signed dut_left) (reference_redirect_signed dut_right) =
  Z.ltb (reference_redirect_signed ref_left) (reference_redirect_signed ref_right)) /\
 ((N.eqb kind 1 || N.eqb kind 4) = true -> N.ltb dut_left dut_right = N.ltb ref_left ref_right).

Lemma dut_operand_tests_branch kind dut_left dut_right ref_left ref_right :
 dut_operand_tests_match kind dut_left dut_right ref_left ref_right ->
 dut_branch_function kind dut_left dut_right = dut_branch_function kind ref_left ref_right.
Proof.
 unfold dut_operand_tests_match, dut_branch_function.
 intros [Eq [Signed Unsigned]]. rewrite !N.leb_antisym !Z.leb_antisym.
 destruct (N.eqb kind 3), (N.eqb kind 6), (N.eqb kind 2), (N.eqb kind 5), (N.eqb kind 1), (N.eqb kind 4);
 cbn [orb] in Eq, Signed, Unsigned;
 try specialize (Eq (Logic.eq_refl true)); try specialize (Signed (Logic.eq_refl true)); try specialize (Unsigned (Logic.eq_refl true));
 cbn [andb orb]; congruence.
Qed.

Definition dut_redirect_controls_match instruction selector kind : Prop :=
 let code := N.land instruction 28799 in
 (N.eqb kind 3 = N.eqb code 99) /\
 (N.eqb kind 6 = N.eqb code 4195) /\
 (N.eqb kind 2 = N.eqb code 16483) /\
 (N.eqb kind 5 = N.eqb code 20579) /\
 (N.eqb kind 1 = N.eqb code 24675) /\
 (N.eqb kind 4 = N.eqb code 28771) /\
 (N.eqb selector 1 = (N.eqb (N.land instruction 127) 111 || N.eqb code 103)).

Definition dut_reference_taken instruction left right :=
 let code := N.land instruction 28799 in
 (N.eqb code 99 && N.eqb left right) || (N.eqb code 4195 && negb (N.eqb left right)) ||
 (N.eqb code 16483 && Z.ltb (reference_redirect_signed left) (reference_redirect_signed right)) ||
 (N.eqb code 20579 && Z.leb (reference_redirect_signed right) (reference_redirect_signed left)) ||
 (N.eqb code 24675 && N.ltb left right) || (N.eqb code 28771 && N.leb right left) ||
 N.eqb (N.land instruction 127) 111.

Lemma dut_redirect_decode instruction selector kind left right :
 dut_redirect_controls_match instruction selector kind ->
 dut_redirect_function selector kind left right =
 (dut_reference_taken instruction left right || N.eqb (N.land instruction 28799) 103).
Proof.
 unfold dut_redirect_controls_match, dut_redirect_function, dut_branch_function, dut_reference_taken.
 intros [Eq [Ne [Lt [Ge [Ltu [Geu Jump]]]]]].
 rewrite Eq Ne Lt Ge Ltu Geu Jump. btauto.
Qed.

Lemma dut_reference_alignment instruction left right immediate pc csr :
 reference_redirect_function instruction left right immediate pc csr =
 (dut_reference_taken instruction left right && reference_redirect_aligned (N.testbit csr 2) (pc + immediate)) ||
 (N.eqb (N.land instruction 28799) 103 && reference_redirect_aligned (N.testbit csr 2) (N.clearbit (left + immediate) 0)).
Proof. unfold reference_redirect_function, dut_reference_taken. btauto. Qed.

Lemma dut_redirect_gate a b aligned_a aligned_b :
 (a = true -> aligned_a = true) -> (b = true -> aligned_b = true) ->
 (a || b) = ((a && aligned_a) || (b && aligned_b)).
Proof. destruct a,b,aligned_a,aligned_b; intros A B; try reflexivity; try (specialize (A (Logic.eq_refl true)); discriminate A); try (specialize (B (Logic.eq_refl true)); discriminate B). Qed.

Theorem dut_redirect_reference instruction selector kind dut_left dut_right ref_left ref_right immediate pc csr :
 dut_redirect_controls_match instruction selector kind ->
 dut_operand_tests_match kind dut_left dut_right ref_left ref_right ->
 (dut_reference_taken instruction ref_left ref_right = true ->
  reference_redirect_aligned (N.testbit csr 2) (pc + immediate) = true) ->
 (N.eqb (N.land instruction 28799) 103 = true ->
  reference_redirect_aligned (N.testbit csr 2) (N.clearbit (ref_left + immediate) 0) = true) ->
 dut_redirect_function selector kind dut_left dut_right =
 reference_redirect_function instruction ref_left ref_right immediate pc csr.
Proof.
 intros Controls Operands BranchAligned JalrAligned.
 unfold dut_redirect_function at 1.
 rewrite (dut_operand_tests_branch kind dut_left dut_right ref_left ref_right Operands).
 change (dut_redirect_function selector kind ref_left ref_right = reference_redirect_function instruction ref_left ref_right immediate pc csr).
 rewrite (dut_redirect_decode instruction selector kind ref_left ref_right Controls) dut_reference_alignment.
 apply dut_redirect_gate; assumption.
Qed.
