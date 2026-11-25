Require Import NormalizedBit.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths Semantics_with_implicit_widths.
Definition bit_or_known value bit :=
 match eval_binop Bor value (Gval (Fuint 1) [::bit]) with
 | Some result => result | None => Needtobedefined (Gtyp (Fuint 1)) end.
Definition bit_eq_false value :=
 match eval_binop (Bcomp Beq) value (Gval (Fuint 1) [::false]) with
 | Some result => result | None => Needtobedefined (Gtyp (Fuint 1)) end.
Lemma bit_or_known_eval value bit : normalized_bit value ->
 eval_binop Bor value (Gval (Fuint 1) [::bit]) = Some (bit_or_known value bit).
Proof. intro Normal. destruct Normal as [b| | |]; try destruct b; destruct bit; reflexivity. Qed.
Lemma bit_or_known_normal value bit : normalized_bit value -> normalized_bit (bit_or_known value bit).
Proof. intro Normal. destruct Normal as [b| | |]; try destruct b; destruct bit; vm_compute; constructor. Qed.
Lemma bit_eq_false_eval value : normalized_bit value ->
 eval_binop (Bcomp Beq) value (Gval (Fuint 1) [::false]) = Some (bit_eq_false value).
Proof. intro Normal. destruct Normal as [b| | |]; try destruct b; reflexivity. Qed.
Lemma bit_eq_false_normal value : normalized_bit value -> normalized_bit (bit_eq_false value).
Proof. intro Normal. destruct Normal as [b| | |]; try destruct b; vm_compute; constructor. Qed.
Lemma normalized_bit_type value : normalized_bit value -> type_of_val value = Gtyp (Fuint 1).
Proof. intro Normal. destruct Normal; reflexivity. Qed.
Lemma normalized_bit_adapt value : normalized_bit value ->
 adapt_hvalue_as_type value (Gtyp (Fuint 1)) = Some value.
Proof. intro Normal. destruct Normal as [b| | |]; try destruct b; reflexivity. Qed.
Definition checker_valid_symbolic bubble stall reset := bit_eq_false (bit_or_known (bit_or_known bubble stall) reset).
Lemma checker_valid_symbolic_normal bubble stall reset : normalized_bit bubble ->
 normalized_bit (checker_valid_symbolic bubble stall reset).
Proof. intro Normal. apply bit_eq_false_normal, bit_or_known_normal, bit_or_known_normal. exact Normal. Qed.
Lemma checker_valid_symbolic_true bubble stall reset : normalized_bit bubble ->
 checker_valid_symbolic bubble stall reset = Gval (Fuint 1) [::true] ->
 bubble = Gval (Fuint 1) [::false] /\ stall = false /\ reset = false.
Proof. intro Normal. destruct Normal as [b| | |]; try destruct b; destruct stall,reset;
 vm_compute; intro H; try discriminate H; repeat split; reflexivity. Qed.
