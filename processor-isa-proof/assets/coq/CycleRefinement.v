From Coq Require Import List.
Import ListNotations.
Set Implicit Arguments.

(* Explicit hypotheses are adapter obligations, never new processor axioms. *)
Section Execution.
  Context {State Input : Type}.
  Variable step : State -> Input -> State -> Prop.
  Inductive execution (initial : State) : list Input -> State -> Prop :=
  | execution_nil : execution initial [] initial
  | execution_cons : forall i s rest final,
      step initial i s -> execution s rest final ->
      execution initial (i :: rest) final.

  Theorem invariant_execution (Inv : State -> Prop)
      (preserve : forall s i s', Inv s -> step s i s' -> Inv s') :
    forall s inputs final,
      execution s inputs final -> Inv s -> Inv final.
  Proof.
    intros s inputs final Run. induction Run; intros Initial.
    - exact Initial.
    - apply IHRun. eapply preserve; eauto.
  Qed.
End Execution.

Section CycleAdapter.
  Context {Raw View Input : Type}.
  Variables (raw_step : Raw -> Input -> Raw -> Prop)
            (view_at : Raw -> View -> Prop)
            (view_step : View -> Input -> View -> Prop).

  Theorem lift_view_invariant (Inv : View -> Prop)
      (extract_step : forall s i s' v,
        raw_step s i s' -> view_at s v ->
        exists v', view_at s' v' /\ view_step v i v')
      (preserve_view : forall v i v', Inv v -> view_step v i v' -> Inv v') :
    forall s inputs final,
      execution raw_step s inputs final ->
      (exists v, view_at s v /\ Inv v) ->
      exists v, view_at final v /\ Inv v.
  Proof.
    intros s inputs final Run Initial.
    eapply (@invariant_execution Raw Input raw_step
      (fun x => exists v, view_at x v /\ Inv v)); [|exact Run|exact Initial].
    intros x i y [v [At InvV]] Step.
    destruct (extract_step x i y v Step At) as [v' [At' Transition]].
    exists v'. split; [exact At'|eapply preserve_view; eauto].
  Qed.
End CycleAdapter.

Section StutteringSimulation.
  Context {Dut Ref Input : Type}.
  Variables (dut_step : Dut -> Input -> Dut -> Prop)
            (ref_step : Ref -> Input -> Ref -> Prop)
            (advances : Dut -> Input -> Dut -> bool)
            (Rel : Dut -> Ref -> Prop).

  (* The reference trace records architectural advances: retirements or events.
     The adapter proves which cycles advance; traps need not retire instructions. *)
  Inductive matched_execution : Dut -> Ref -> list Input -> list Input -> Dut -> Ref -> Prop :=
  | matched_nil : forall d r, matched_execution d r [] [] d r
  | matched_wait : forall d r i d' rest observed final rfinal,
      dut_step d i d' -> advances d i d' = false ->
      matched_execution d' r rest observed final rfinal ->
      matched_execution d r (i :: rest) observed final rfinal
  | matched_advance : forall d r i d' r' rest observed final rfinal,
      dut_step d i d' -> advances d i d' = true -> ref_step r i r' ->
      matched_execution d' r' rest observed final rfinal ->
      matched_execution d r (i :: rest) (i :: observed) final rfinal.

  Theorem simulate_execution
      (wait : forall d i d' r,
        Rel d r -> dut_step d i d' -> advances d i d' = false -> Rel d' r)
      (advance : forall d i d' r,
        Rel d r -> dut_step d i d' -> advances d i d' = true ->
        exists r', ref_step r i r' /\ Rel d' r') :
    forall d inputs final,
      execution dut_step d inputs final ->
      forall r, Rel d r -> exists observed rfinal,
        matched_execution d r inputs observed final rfinal /\ Rel final rfinal.
  Proof.
    intros d inputs final Run. induction Run as [d|d i d' rest final Step Run IH].
    - intros r Relation. exists [], r. split; [constructor|exact Relation].
    - intros r Relation. destruct (advances d i d') eqn:Retired.
      + destruct (advance d i d' r Relation Step Retired) as [r' [RefStep Next]].
        destruct (IH r' Next) as [observed [rfinal [Matched Final]]].
        exists (i :: observed), rfinal. split; [eapply matched_advance; eauto|exact Final].
      + destruct (IH r (wait d i d' r Relation Step Retired))
          as [observed [rfinal [Matched Final]]].
        exists observed, rfinal. split; [eapply matched_wait; eauto|exact Final].
  Qed.
End StutteringSimulation.
