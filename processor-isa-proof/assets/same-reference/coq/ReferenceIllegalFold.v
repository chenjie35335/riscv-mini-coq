(* Exact source copy; provenance in ../provenance.json. *)
From Coq Require Import Bool.Bool Arith.PeanoNat Lia.
Fixpoint reference_illegal_fold (guards : nat -> bool) (count : nat) : bool :=
 match count with O => true | S n => if guards n then false else reference_illegal_fold guards n end.
Lemma reference_illegal_fold_match guards count row :
 row < count -> guards row = true -> reference_illegal_fold guards count = false.
Proof.
 revert row. induction count as [|count IH];intros row Bound Match;[lia|].
 cbn. destruct (guards count) eqn:Last;[reflexivity|].
 apply (IH row);[|exact Match]. assert (row <> count) by (intro Equal;subst;congruence). lia.
Qed.
Lemma reference_illegal_fold_false guards count :
 reference_illegal_fold guards count = false -> exists row, row < count /\ guards row = true.
Proof.
 induction count as [|count IH];cbn;intro Result;[discriminate|].
 destruct (guards count) eqn:Last.
 - exists count;split;[lia|exact Last].
 - destruct (IH Result) as [row [Bound Match]]. exists row;split;[lia|exact Match].
Qed.
