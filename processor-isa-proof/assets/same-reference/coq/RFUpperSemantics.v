(* Import-only isolation; exact theorem bodies, see ../provenance.json. *)
Require Import ReferenceWordSemantics.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Definition rf_upper_class auipc :=if auipc then 10%nat else 9%nat.
Definition rf_upper_immediate instruction :=zeros 12 ++drop 12(take 32 instruction).
Definition cycle_upper_semantics auipc pc instruction :=if auipc then reference_load_address pc(rf_upper_immediate instruction)else rf_upper_immediate instruction.
Lemma rf_upper_class_bound auipc :(rf_upper_class auipc<37)%coq_nat.
Proof. destruct auipc;vm_compute;lia. Qed.
Lemma rf_upper_immediate_size instruction :size instruction=32%nat ->size(rf_upper_immediate instruction)=32%nat.
Proof. intro Size;unfold rf_upper_immediate;rewrite size_cat size_nseq size_drop size_take Size;reflexivity. Qed.
Lemma cycle_upper_semantics_size auipc pc instruction :size instruction=32%nat ->size(cycle_upper_semantics auipc pc instruction)=32%nat.
Proof. intro Size;destruct auipc;[unfold cycle_upper_semantics,reference_load_address;rewrite size_take size_from_N;reflexivity|exact(rf_upper_immediate_size instruction Size)]. Qed.
