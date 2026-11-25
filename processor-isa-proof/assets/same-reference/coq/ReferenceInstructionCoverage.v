(* Extracted from the existing processor proof. Source mapping: ../provenance.json.
   Proof bodies below are unchanged; imports isolate the shared reference semantics. *)
From Coq Require Import NArith ZArith List Lia btauto.Btauto.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits NBitsDef NBitsOp.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.

Definition legal_instruction_classes : seq(N*N) := [::(28799,19);(28799,8211);(28799,12307);(28799,28691);(28799,24595);(28799,16403);(4261441663,4115);(4261441663,20499);(4261441663,1073762323);(127,55);(127,23);(4261441663,51);(4261441663,8243);(4261441663,12339);(4261441663,28723);(4261441663,24627);(4261441663,16435);(4261441663,4147);(4261441663,20531);(4261441663,1073741875);(4261441663,1073762355);(127,111);(28799,103);(28799,99);(28799,4195);(28799,16483);(28799,24675);(28799,20579);(28799,28771);(28799,3);(28799,4099);(28799,8195);(28799,16387);(28799,20483);(28799,35);(28799,4131);(28799,8227)].

Definition legal_instruction_classified instruction := exists mask code,List.In(mask,code)legal_instruction_classes /\N.land(to_N instruction)mask=code.

Definition reference_instruction_codes : seq (N*N) := [::(28799,19);(28799,8211);(28799,12307);(28799,28691);(28799,24595);(28799,16403);(4261441663,4115);(4261441663,20499);(4261441663,1073762323);(127,55);(127,23);(4261441663,51);(4261441663,8243);(4261441663,12339);(4261441663,28723);(4261441663,24627);(4261441663,16435);(4261441663,4147);(4261441663,20531);(4261441663,1073741875);(4261441663,1073762355);(127,111);(28799,103);(28799,99);(28799,4195);(28799,16483);(28799,24675);(28799,20579);(28799,28771);(28799,3);(28799,4099);(28799,8195);(28799,16387);(28799,20483);(28799,35);(28799,4131);(28799,8227);(4294967295,1048691);(4294967295,115);(28799,15);(4261441663,33554483);(4261441663,33558579);(4261441663,33562675);(4261441663,33566771);(4261441663,33570867);(4261441663,33574963);(4261441663,33579059);(4261441663,33583155)].

Theorem legal_reference_mask_coverage mask code :
 List.In (mask,code) legal_instruction_classes ->
 exists row, (row < 48)%coq_nat /\ seq.nth (0,0) reference_instruction_codes row = (mask,code).
Proof.
 intro Member. cbn [legal_instruction_classes List.In] in Member.
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 0%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 1%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 2%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 3%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 4%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 5%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 6%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 7%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 8%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 9%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 10%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 11%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 12%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 13%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 14%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 15%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 16%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 17%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 18%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 19%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 20%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 21%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 22%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 23%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 24%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 25%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 26%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 27%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 28%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 29%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 30%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 31%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 32%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 33%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 34%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 35%nat;split;[lia|reflexivity]|].
 destruct Member as [Equal|Member];[inversion Equal;subst;exists 36%nat;split;[lia|reflexivity]|].
 contradiction.
Qed.

Theorem classified_reference_decode instruction :
 legal_instruction_classified instruction ->
 exists row, (row < 48)%coq_nat /\
 N.eqb (snd (seq.nth (0,0) reference_instruction_codes row))
 (N.land (to_N instruction) (fst (seq.nth (0,0) reference_instruction_codes row))) = true.
Proof.
 intros [mask [code [Member Match]]].
 destruct (legal_reference_mask_coverage mask code Member) as [row [Bound Row]].
 exists row;split;[exact Bound|]. rewrite Row. cbn. rewrite Match. apply N.eqb_refl.
Qed.
