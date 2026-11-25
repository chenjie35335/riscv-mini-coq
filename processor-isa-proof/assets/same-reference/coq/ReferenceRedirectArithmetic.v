(* Extracted from the existing processor proof. Source mapping: ../provenance.json.
   Proof bodies below are unchanged; imports isolate the shared reference semantics. *)
From Coq Require Import NArith ZArith List Lia btauto.Btauto.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits NBitsDef NBitsOp.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.

Lemma redirect_to_N_cons bit rest :
 to_N (bit :: rest) = 2 * to_N rest + (if bit then 1 else 0).
Proof. unfold to_N. destruct bit; cbn [foldr N.b2n]; lia. Qed.

Lemma redirect_to_N_and_nil right : to_N (andB [::] right) = 0.
Proof.
 induction right as [|b right IH]; [reflexivity|].
 unfold andB, lift0 in *. rewrite lift_nil_cons.
 rewrite redirect_to_N_cons. change (2 * to_N (lift b0 andb [::] right) + 0 = 0). rewrite IH. reflexivity.
Qed.

Lemma redirect_to_N_and left right :
 to_N (andB left right) = N.land (to_N left) (to_N right).
Proof.
 revert right. induction left as [|a left IH]; intros [|b right].
 - reflexivity.
 - rewrite redirect_to_N_and_nil. reflexivity.
 - unfold andB, lift0. rewrite lift_cons_nil.
   rewrite redirect_to_N_cons. change (2 * to_N (andB left [::]) + (if a && false then 1 else 0) = N.land (to_N (a :: left)) 0).
   rewrite IH !N.land_0_r. destruct a; reflexivity.
 - rewrite andB_cons !redirect_to_N_cons IH.
   destruct a, b; cbn [andb]; rewrite ?N.add_0_r;
   rewrite ?N.land_even_even ?N.land_odd_even ?N.land_even_odd ?N.land_odd_odd; reflexivity.
Qed.

Lemma redirect_N_eqb x y : (x == y) = N.eqb x y.
Proof.
 destruct (eqP : reflect (x = y) (x == y)) as [H|H].
 - subst y. rewrite N.eqb_refl. reflexivity.
 - symmetry. apply N.eqb_neq. exact H.
Qed.

Lemma redirect_to_N_testbit bits index :
 N.testbit (to_N bits) (N.of_nat index) = nth false bits index.
Proof.
 revert bits. induction index as [|index IH]; intros [|b bits].
 - reflexivity.
 - rewrite redirect_to_N_cons. change (N.testbit (2 * to_N bits + N.b2n b) 0 = b). apply N.testbit_0_r.
 - rewrite N.bits_0. reflexivity.
 - rewrite redirect_to_N_cons Nat2N.inj_succ.
   change (N.testbit (2 * to_N bits + N.b2n b) (N.succ (N.of_nat index)) = nth false bits index).
   rewrite N.testbit_succ_r. apply IH.
Qed.

Lemma redirect_msb_nth bits : msb bits = nth false bits (size bits).-1.
Proof.
 rewrite nth_last. unfold msb, splitmsb, split_last, lastd.
 destruct bits; reflexivity.
Qed.

Definition reference_redirect_aligned compressed target :=
 N.eqb (N.land target (if compressed then 1 else 3)) 0.

Definition reference_redirect_signed word :=
 if N.testbit word 31 then (Z.of_N word - 4294967296)%Z else Z.of_N word.

Definition reference_redirect_function instruction rs1 rs2 immediate pc csr : bool :=
 let code := N.land instruction 28799 in
 let compressed := N.testbit csr 2 in
 let aligned := reference_redirect_aligned compressed (pc + immediate) in
 let taken :=
 (N.eqb code 28771 && N.leb rs2 rs1) ||
 (N.eqb code 20579 && Z.leb (reference_redirect_signed rs2) (reference_redirect_signed rs1)) ||
 (N.eqb code 24675 && N.ltb rs1 rs2) ||
 (N.eqb code 16483 && Z.ltb (reference_redirect_signed rs1) (reference_redirect_signed rs2)) ||
 (N.eqb code 4195 && negb (N.eqb rs1 rs2)) ||
 (N.eqb code 99 && N.eqb rs1 rs2) || N.eqb (N.land instruction 127) 111 in
 (taken && aligned) ||
 (N.eqb code 103 && reference_redirect_aligned compressed (N.clearbit (rs1 + immediate) 0)).

Definition reference_redirect_guards (b1974 : bool) (b1980 : bool) (b1986 : bool) (b1992 : bool) (b1998 : bool) (b2004 : bool) (b2010 : bool) (b2357 : bool) (b2806 : bool) (b2825 : bool) (b2830 : bool) (b2847 : bool) (b2850 : bool) (b2867 : bool) (b2872 : bool) (b2889 : bool) (b2892 : bool) (b2909 : bool) (b2912 : bool) (b2929 : bool) (b2949 : bool) (b2966 : bool) := (b1974 && b2806 && b2825) || (b1980 && b2830 && b2847) || (b1986 && b2850 && b2867) || (b1992 && b2872 && b2889) || (b1998 && b2892 && b2909) || (b2004 && b2912 && b2929) || (b2010 && b2949) || (b2357 && b2966).

Lemma reference_redirect_guards_normalize instruction rs1 rs2 immediate pc csr :
 reference_redirect_guards
  (N.eqb (N.land instruction 28799) 28771)
  (N.eqb (N.land instruction 28799) 20579)
  (N.eqb (N.land instruction 28799) 24675)
  (N.eqb (N.land instruction 28799) 16483)
  (N.eqb (N.land instruction 28799) 4195)
  (N.eqb (N.land instruction 28799) 99)
  (N.eqb (N.land instruction 28799) 103)
  (N.eqb (N.land instruction 127) 111)
  (N.leb rs2 rs1)
  (reference_redirect_aligned (N.testbit csr 2) (pc + immediate))
  (Z.leb (reference_redirect_signed rs2) (reference_redirect_signed rs1))
  (reference_redirect_aligned (N.testbit csr 2) (pc + immediate))
  (N.ltb rs1 rs2)
  (reference_redirect_aligned (N.testbit csr 2) (pc + immediate))
  (Z.ltb (reference_redirect_signed rs1) (reference_redirect_signed rs2))
  (reference_redirect_aligned (N.testbit csr 2) (pc + immediate))
  (negb (N.eqb rs1 rs2))
  (reference_redirect_aligned (N.testbit csr 2) (pc + immediate))
  (N.eqb rs1 rs2)
  (reference_redirect_aligned (N.testbit csr 2) (pc + immediate))
  (reference_redirect_aligned (N.testbit csr 2) (N.clearbit (rs1 + immediate) 0))
  (reference_redirect_aligned (N.testbit csr 2) (pc + immediate)) =
 reference_redirect_function instruction rs1 rs2 immediate pc csr.
Proof. unfold reference_redirect_guards, reference_redirect_function. btauto. Qed.

Lemma reference_redirect_signed32 bits :
 size bits = 32%nat -> to_Z bits = reference_redirect_signed (to_N bits).
Proof.
 intro Size. unfold reference_redirect_signed.
 change (to_Z bits = if N.testbit (to_N bits) (N.of_nat 31) then (Z.of_N (to_N bits) - 4294967296)%Z else Z.of_N (to_N bits)).
 rewrite redirect_to_N_testbit to_Z_to_Zpos to_Zpos_N redirect_msb_nth Size.
 change ((Z.of_N (to_N bits) - Z.b2z (nth false bits 31) * 4294967296)%Z = if nth false bits 31 then (Z.of_N (to_N bits) - 4294967296)%Z else Z.of_N (to_N bits)).
 destruct (nth false bits 31); cbn [Z.b2z]; rewrite ?Z.mul_1_l ?Z.mul_0_l ?Z.sub_0_r; reflexivity.
Qed.

Lemma reference_redirect_aligned_bits compressed target :
 reference_redirect_aligned compressed target =
 negb (N.testbit target 0) && (compressed || negb (N.testbit target 1)).
Proof.
 unfold reference_redirect_aligned.
 destruct compressed; destruct target as [|[p|p|]]; try reflexivity; destruct p; reflexivity.
Qed.

Lemma reference_redirect_alignment_select compressed bits :
 (if compressed then (to_N (take 1 bits) == 0) else (to_N (take 2 bits) == 0)) =
 reference_redirect_aligned compressed (to_N bits).
Proof.
 rewrite reference_redirect_aligned_bits
  (redirect_to_N_testbit bits 0) (redirect_to_N_testbit bits 1).
 destruct compressed; destruct bits as [|a [|b bits]]; try reflexivity;
 destruct a; try reflexivity; destruct b; cbn [take]; rewrite ?take0; vm_compute; reflexivity.
Qed.

Lemma reference_redirect_aligned_take32_from33 compressed value :
 reference_redirect_aligned compressed (to_N (take 32 (from_N 33 value))) =
 reference_redirect_aligned compressed value.
Proof.
 rewrite !reference_redirect_aligned_bits
  (redirect_to_N_testbit _ 0) (redirect_to_N_testbit _ 1).
 rewrite !nth_take //.
 rewrite -(redirect_to_N_testbit (from_N 33 value) 0)
  -(redirect_to_N_testbit (from_N 33 value) 1) to_N_from_N.
 rewrite !N.mod_pow2_bits_low; reflexivity.
Qed.

Lemma reference_redirect_aligned_jalr compressed value :
 reference_redirect_aligned compressed
  (to_N (false :: take 31 (drop 1 (take 32 (from_N 33 value))))) =
 reference_redirect_aligned compressed (N.clearbit value 0).
Proof.
 rewrite !reference_redirect_aligned_bits N.clearbit_eq
  N.clearbit_neq; [|discriminate].
 rewrite (redirect_to_N_testbit _ 0) (redirect_to_N_testbit _ 1).
 cbn [nth]. rewrite !nth_take // nth_drop.
 change ((true && (compressed || ~~ nth false (take 32 (from_N 33 value)) 1)) =
  (true && (compressed || ~~ N.testbit value 1))).
 rewrite nth_take // -(redirect_to_N_testbit (from_N 33 value) 1) to_N_from_N.
 rewrite N.mod_pow2_bits_low; reflexivity.
Qed.

Lemma reference_redirect_adapt_word bits :
 size bits = 32%nat ->
 adapt_hvalue_as_type (Gval (Fuint 32) bits) (Gtyp (Fuint 32)) = Some (Gval (Fuint 32) bits).
Proof.
 intro Size. cbn [adapt_hvalue_as_type]. rewrite <- Size, take_size.
 unfold zext_to. rewrite subnn. unfold zext. rewrite zeros0 cats0. reflexivity.
Qed.
