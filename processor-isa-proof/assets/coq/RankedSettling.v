From Coq Require Import List Bool Arith Lia.
Import ListNotations.
Set Implicit Arguments.

Section RankedGraph.
  Context {Node : Type}.
  Variables (nodes : list Node) (deps : Node -> list Node) (rank : Node -> nat).
  Definition ranks_valid : bool :=
    forallb (fun node => forallb (fun source => Nat.ltb (rank source) (rank node))
                                (deps node)) nodes.

  Theorem ranks_valid_sound : ranks_valid = true ->
    forall node source, In node nodes -> In source (deps node) -> rank source < rank node.
  Proof.
    unfold ranks_valid. rewrite forallb_forall.
    intros Valid node source Member Edge.
    specialize (Valid node Member). rewrite forallb_forall in Valid.
    specialize (Valid source Edge). apply Nat.ltb_lt. exact Valid.
  Qed.

  Variable Holds : nat -> Node -> Prop.
  Theorem ranked_history
      (Valid : ranks_valid = true)
      (closed : forall node source, In node nodes -> In source (deps node) -> In source nodes)
      (seeds : forall time node, In node nodes -> rank node = 0 -> Holds time node)
      (transfer : forall time node, In node nodes ->
        (forall source, In source (deps node) -> Holds time source) -> Holds (S time) node) :
    forall time node, In node nodes -> rank node <= time -> Holds time node.
  Proof.
    intro time. induction time as [|time IH]; intros node Member Bound.
    - apply seeds; [exact Member|lia].
    - destruct (Nat.eq_dec (rank node) 0) as [Zero|Nonzero].
      + apply seeds; assumption.
      + apply transfer; [exact Member|]. intros source Edge.
        apply IH; [eapply closed; eauto|].
        pose proof (ranks_valid_sound Valid node source Member Edge). lia.
  Qed.

  (* Partial evaluators generally supply only a finite successful history. *)
  Theorem ranked_history_bounded (limit : nat)
      (Valid : ranks_valid = true)
      (closed : forall node source, In node nodes -> In source (deps node) -> In source nodes)
      (seeds : forall time node, time <= limit -> In node nodes -> rank node = 0 -> Holds time node)
      (transfer : forall time node, time < limit -> In node nodes ->
        (forall source, In source (deps node) -> Holds time source) -> Holds (S time) node) :
    forall time node, time <= limit -> In node nodes -> rank node <= time -> Holds time node.
  Proof.
    intro time. induction time as [|time IH]; intros node Within Member Bound.
    - apply seeds; [exact Within|exact Member|lia].
    - destruct (Nat.eq_dec (rank node) 0) as [Zero|Nonzero].
      + apply seeds; assumption.
      + apply transfer; [lia|exact Member|]. intros source Edge.
        apply IH; [lia|eapply closed; eauto|].
        pose proof (ranks_valid_sound Valid node source Member Edge). lia.
  Qed.
End RankedGraph.
