(* Extracted from the existing processor proof. Source mapping: ../provenance.json.
   Proof bodies below are unchanged; imports isolate the shared reference semantics. *)
Require Import ReferenceLoadArithmetic.
From Coq Require Import NArith ZArith List Lia btauto.Btauto.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits NBitsDef NBitsOp.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.

Definition reference_load_width lane : nat := nth 0%nat [::16%nat;8%nat;32%nat;16%nat;8%nat] lane.

Definition reference_load_mask lane := from_N 64 (nth 0 [::65535;255;4294967295;65535;255] lane).

Definition reference_load_shift raw address := zext_to 32 (drop (to_nat (zeros 3 ++ take 2 address)) raw).

Lemma reference_load_shift_size raw address : size raw = 32%nat -> size (reference_load_shift raw address) = 32%nat.
Proof.
 intro Size. unfold reference_load_shift,zext_to. rewrite size_zext addnC subnK; [reflexivity|].
 rewrite size_drop Size. apply leq_subr.
Qed.

Lemma reference_load_remove_mask lane shifted : (lane < 5)%coq_nat -> size shifted = 32%nat ->
 take (reference_load_width lane) (andB shifted (reference_load_mask lane)) = take (reference_load_width lane) shifted.
Proof.
 intros Lane Size.
 do 5 (destruct lane as [|lane];
 [cbv [reference_load_width reference_load_mask nth]; rewrite ?reference_load_mask8 ?reference_load_mask16 ?reference_load_mask32;
 apply reference_load_mask_low;rewrite Size;lia|]). lia.
Qed.

Lemma reference_load_sign_bit width word : size word = width -> (0 < width)%nat ->
 drop (width-1)%nat (take width word) = [::msb word].
Proof.
 intros Size Positive. rewrite -Size take_size.
 pose proof (high1_msb word) as H. unfold high in H.
 assert (Zero : (1-size word)%nat = 0%nat).
 { apply/eqP. rewrite subn_eq0 Size. exact Positive. }
 rewrite Zero /= in H. exact H.
Qed.

Definition reference_load_extend lane word :=
 if (lane < 2)%nat then zext_to 32 word else
 if Nat.eqb lane 2 then take 32 word else sext_to 32 word.

Definition reference_load_address rs1 immediate := take 32 (from_N 33 (to_N rs1 + to_N immediate)).
