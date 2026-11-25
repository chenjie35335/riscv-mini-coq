From Coq Require Import List Bool Arith Lia NArith.
From ProcessorProof Require Import CycleRefinement RegisterEffects CheckerFacts
  EvaluationFacts RankedSettling.
Import ListNotations.

(* An increment pipeline: pending is the next result; stalls retire nothing. *)
Module IncrementPipeline.
  Definition dut := (nat * nat)%type.
  Definition step (d : dut) (go : bool) (d' : dut) :=
    d' = if go then (snd d, S (snd d)) else d.
  Definition isa_step (r : nat) (_ : bool) (next : nat) := next = S r.
  Definition retired (_ : dut) (go : bool) (_ : dut) := go.
  Definition relation (d : dut) (r : nat) := fst d = r /\ snd d = S r.

  Lemma wait d go d' r : relation d r -> step d go d' ->
    retired d go d' = false -> relation d' r.
  Proof.
    intros Rel Step Idle. unfold retired in Idle. subst go.
    unfold step in Step. cbn in Step. subst d'. exact Rel.
  Qed.
  Lemma commit d go d' r : relation d r -> step d go d' ->
    retired d go d' = true -> exists r', isa_step r go r' /\ relation d' r'.
  Proof.
    intros [Current Pending] Step Active. unfold retired in Active. subst go.
    unfold step in Step. cbn in Step. subst d'. exists (S r).
    unfold isa_step, relation; cbn. repeat split; congruence.
  Qed.
  Theorem refinement d inputs final : execution step d inputs final ->
    forall r, relation d r -> exists observed rfinal,
      matched_execution step isa_step retired d r inputs observed final rfinal /\
      relation final rfinal.
  Proof. apply (@simulate_execution dut nat bool step isa_step retired relation wait commit). Qed.

  Example two_retirements_with_stall :
    execution step (0, 1) [true; false; true] (2, 3).
  Proof. repeat (econstructor; [reflexivity|]); constructor. Qed.
End IncrementPipeline.

Module Forwarding.
  Definition initial_bank (index : nat) := index * 10.
  Example write_then_read :
    apply_effect Nat.eq_dec 0 0 initial_bank (Write 5 42) 5 = 42.
  Proof. apply read_forwarded_write. discriminate. Qed.
  Example zero_is_protected :
    apply_effect Nat.eq_dec 0 0 initial_bank (Write 0 42) 0 = 0.
  Proof. apply effect_preserves_zero. reflexivity. Qed.
  Example preview_banks_agree :
    banks_agree initial_bank initial_bank ->
    banks_agree (apply_effect Nat.eq_dec 0 0 initial_bank (Write 5 42))
                (apply_effect Nat.eq_dec 0 0 initial_bank (Write 5 42)).
  Proof. apply effect_preserves_agreement. Qed.
End Forwarding.

Module Checker.
  Definition state := (bool * (nat * nat))%type.
  Definition enabled (s : state) := fst s.
  Definition lhs (s : state) := fst (snd s).
  Definition rhs (s : state) := snd (snd s).
  Definition predicate (s : state) := Nat.eqb (lhs s) (rhs s).
  Example enabled_correct s : lhs s = rhs s -> assertion_at enabled predicate s.
  Proof.
    eapply (@guarded_checker state nat enabled predicate lhs rhs
              (fun s => lhs s = rhs s)).
    - intros x Equal _. exact Equal.
    - intros x Equal. apply Nat.eqb_eq. exact Equal.
  Qed.

  Fixpoint little_endian (xs : list bool) : N :=
    match xs with
    | [] => 0%N
    | b :: rest => N.add (if b then 1%N else 0%N) (N.mul 2 (little_endian rest))
    end.
  Example unequal_widths_same_numeric_value :
    N.eqb (little_endian [true]) (little_endian [true; false]) = true.
  Proof. apply numeric_checker. reflexivity. Qed.
End Checker.

Module Settling.
  Definition saturate (n : nat) : option nat := Some (Nat.min 2 (S n)).
  Example finite_prefix : iterate saturate 2 0 = Some 2.
  Proof. reflexivity. Qed.
  Example stable_tail extra : iterate saturate (2 + extra) 0 = Some 2.
  Proof. eapply settled_after_prefix; reflexivity. Qed.
  (* A successful budget alone cannot imply a fixed point. *)
  Example budget_is_not_fixed : iterate saturate 1 0 = Some 1 /\ saturate 1 <> Some 1.
  Proof. split; [reflexivity|discriminate]. Qed.
End Settling.

Module Cone.
  Inductive node := Root | Left | Out.
  Definition nodes := [Root; Left; Out].
  Definition deps n := match n with Root => [] | Left => [Root] | Out => [Left] end.
  Definition rank n := match n with Root => 0 | Left => 1 | Out => 2 end.
  Example certificate : ranks_valid nodes deps rank = true.
  Proof. reflexivity. Qed.
  Lemma closed n source : In n nodes -> In source (deps n) -> In source nodes.
  Proof. destruct n, source; cbn; intuition congruence. Qed.
  (* Instantiate Holds with equality/groundness at iteration time in a DUT adapter. *)
  Theorem propagation (Holds : nat -> node -> Prop)
      (root_stable : forall t, Holds t Root)
      (transfer : forall t n, In n nodes ->
        (forall source, In source (deps n) -> Holds t source) -> Holds (S t) n) :
    forall t, 2 <= t -> Holds t Out.
  Proof.
    intros t Bound. eapply (@ranked_history node nodes deps rank Holds certificate closed).
    - intros time n Member Zero. destruct n; cbn in Zero; try discriminate.
      apply root_stable.
    - exact transfer.
    - cbn. auto.
    - exact Bound.
  Qed.
  Theorem bounded_propagation limit (Holds : nat -> node -> Prop)
      (root_stable : forall t, t <= limit -> Holds t Root)
      (transfer : forall t n, t < limit -> In n nodes ->
        (forall source, In source (deps n) -> Holds t source) -> Holds (S t) n) :
    forall t, t <= limit -> 2 <= t -> Holds t Out.
  Proof.
    intros t Within Bound.
    eapply (@ranked_history_bounded node nodes deps rank Holds limit certificate closed).
    - intros time n Time Member Zero. destruct n; cbn in Zero; try discriminate.
      apply root_stable. exact Time.
    - exact transfer.
    - exact Within.
    - cbn. auto.
    - exact Bound.
  Qed.
End Cone.

Module Frame.
  Definition empty (_ : nat) : option nat := None.
  Definition eval (e : nat -> option nat) := e 1.
  Lemma locality a b : agrees_on [1] a b -> eval a = eval b.
  Proof. intro Agree. apply (Agree 1). cbn. auto. Qed.
  Example other_write : eval (write Nat.eq_dec empty 2 99) = eval empty.
  Proof. eapply eval_after_unrelated_write; [exact locality|cbn; intuition congruence]. Qed.
End Frame.

(* Unbounded N values illustrate the checker pattern, not an RV64 width proof. *)
Module PreviewChecker.
Set Implicit Arguments.
Record packet := { valid : bool; killed : bool; dst : nat; result : N }.
Record preview_state := {
  dut_bank : nat -> N; ref_bank : nat -> N;
  pending : packet; checked_index : nat; checking : bool
}.
Definition pending_effect (p : packet) : @effect nat N :=
  if andb (valid p) (negb (killed p))
  then Write (dst p) (result p) else NoWrite.
Definition preview (b : nat -> N) (s : preview_state) : N :=
  @apply_effect nat N Nat.eq_dec 0 0%N b
    (pending_effect (pending s)) (checked_index s).
Definition inv (s : preview_state) := banks_agree (dut_bank s) (ref_bank s).
Definition lhs (s : preview_state) := preview (dut_bank s) s.
Definition rhs (s : preview_state) := preview (ref_bank s) s.
Definition predicate (s : preview_state) := N.eqb (lhs s) (rhs s).
Lemma preview_agreement s : inv s -> lhs s = rhs s.
Proof.
  intro Agree. unfold lhs, rhs, preview.
  apply effect_preserves_agreement. exact Agree.
Qed.
Theorem enabled_preview_checker : forall s, inv s ->
  assertion_at checking predicate s.
Proof.
  apply (@guarded_checker preview_state N checking predicate lhs rhs inv).
  - intros s Inv Enabled. apply preview_agreement. exact Inv.
  - intros s Equal. unfold predicate. apply N.eqb_eq. exact Equal.
Qed.

End PreviewChecker.
