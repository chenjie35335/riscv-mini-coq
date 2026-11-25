From Coq Require Import List.
Import ListNotations.
Set Implicit Arguments.

Section Frames.
  Context {Key Value : Type}.
  Definition env := Key -> option Value.
  Variable key_eq_dec : forall x y : Key, {x = y} + {x <> y}.
  Definition write (e : env) (k : Key) (v : Value) : env :=
    fun q => if key_eq_dec q k then Some v else e q.
  Definition agrees_on (reads : list Key) (a b : env) : Prop :=
    forall key, In key reads -> a key = b key.

  Theorem write_preserves_other e k q v : q <> k -> write e k v q = e q.
  Proof. intro Different. unfold write. destruct (key_eq_dec q k); congruence. Qed.

  Theorem write_preserves_reads reads e k v :
    ~ In k reads -> agrees_on reads (write e k v) e.
  Proof.
    intros Outside q Reads. apply write_preserves_other.
    intro Equal. subst q. contradiction.
  Qed.

  Theorem eval_after_unrelated_write {Result} (reads : list Key)
      (eval : env -> option Result)
      (locality : forall a b, agrees_on reads a b -> eval a = eval b) :
    forall e k v, ~ In k reads -> eval (write e k v) = eval e.
  Proof. intros. apply locality. apply write_preserves_reads. assumption. Qed.
End Frames.

Section Settling.
  Context {State : Type}.
  Variable step : State -> option State.
  Fixpoint iterate (fuel : nat) (s : State) : option State :=
    match fuel with
    | O => Some s
    | S n => match step s with Some s' => iterate n s' | None => None end
    end.

  Theorem fixed_point_iterations s :
    step s = Some s -> forall fuel, iterate fuel s = Some s.
  Proof. intros Fixed fuel. induction fuel; cbn; [reflexivity|rewrite Fixed; exact IHfuel]. Qed.

  Theorem iterate_add n m s :
    iterate (n + m) s =
    match iterate n s with Some middle => iterate m middle | None => None end.
  Proof.
    revert s. induction n; intros s; cbn; [reflexivity|].
    destruct (step s); [apply IHn|reflexivity].
  Qed.

  Theorem settled_after_prefix n s stable :
    iterate n s = Some stable -> step stable = Some stable ->
    forall extra, iterate (n + extra) s = Some stable.
  Proof. intros Prefix Fixed extra. rewrite iterate_add, Prefix. apply fixed_point_iterations. exact Fixed. Qed.
End Settling.
