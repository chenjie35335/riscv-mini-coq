From Coq Require Import List Bool NArith.
Import ListNotations.
Set Implicit Arguments.

Section Checker.
  Context {State Value : Type}.
  Variables (enabled : State -> bool) (predicate : State -> bool)
            (lhs rhs : State -> Value).
  Definition assertion_at s := enabled s = true -> predicate s = true.

  Theorem guarded_checker (Inv : State -> Prop)
      (agree : forall s, Inv s -> enabled s = true -> lhs s = rhs s)
      (compare_sound : forall s, lhs s = rhs s -> predicate s = true) :
    forall s, Inv s -> assertion_at s.
  Proof. intros s H Enable. apply compare_sound. apply agree; assumption. Qed.

  (* Useful, but establishes nothing about the enabled case or its reachability. *)
  Theorem disabled_checker s : enabled s = false -> assertion_at s.
  Proof. intros Disabled Enable. congruence. Qed.
End Checker.

Section Widths.
  Context {Bit : Type}.
  Definition word (width : nat) := { xs : list Bit | length xs = width }.
  Definition same_bits {w1 w2} (x : word w1) (y : word w2) :=
    proj1_sig x = proj1_sig y.

  Theorem same_bits_width {w1 w2} (x : word w1) (y : word w2) :
    same_bits x y -> w1 = w2.
  Proof.
    destruct x as [x X], y as [y Y]. unfold same_bits; cbn.
    intro Equal. subst y. congruence.
  Qed.
End Widths.

(* Numeric comparison permits different widths and leading zero bits. The
   adapter supplies the actual generated expression's decoding convention. *)
Section NumericChecker.
  Context {Left Right : Type}.
  Variables (decode_left : Left -> N) (decode_right : Right -> N).
  Theorem numeric_checker x y :
    decode_left x = decode_right y ->
    N.eqb (decode_left x) (decode_right y) = true.
  Proof. intro Equal. apply N.eqb_eq. exact Equal. Qed.
End NumericChecker.
