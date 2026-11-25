From Coq Require Import List.
Set Implicit Arguments.

Section RegisterEffects.
  Context {Reg Value : Type}.
  Variables (reg_eq_dec : forall x y : Reg, {x = y} + {x <> y})
            (zero_reg : Reg) (zero_value : Value).
  Definition bank := Reg -> Value.
  Inductive effect := NoWrite | Write (destination : Reg) (value : Value).

  (* Instantiate only for an architecture that has a hardwired zero register.
     The bank is already architecturally valid in the NoWrite case. *)
  Definition apply_effect (b : bank) (e : effect) : bank :=
    match e with
    | NoWrite => b
    | Write destination value => fun index =>
        if reg_eq_dec index zero_reg then zero_value
        else if reg_eq_dec index destination then value else b index
    end.
  Definition banks_agree (a b : bank) := forall index, a index = b index.

  Theorem effect_preserves_agreement a b e :
    banks_agree a b -> banks_agree (apply_effect a e) (apply_effect b e).
  Proof.
    intros Agree index. destruct e; cbn; [apply Agree|].
    destruct (reg_eq_dec index zero_reg); [reflexivity|].
    destruct (reg_eq_dec index destination); [reflexivity|apply Agree].
  Qed.

  Theorem effect_preserves_zero b e :
    b zero_reg = zero_value -> apply_effect b e zero_reg = zero_value.
  Proof.
    intro Zero. destruct e; cbn; [exact Zero|].
    destruct (reg_eq_dec zero_reg zero_reg); congruence.
  Qed.

  Theorem read_forwarded_write b destination value :
    destination <> zero_reg ->
    apply_effect b (Write destination value) destination = value.
  Proof.
    intro Nonzero. cbn. destruct (reg_eq_dec destination zero_reg); [contradiction|].
    destruct (reg_eq_dec destination destination); congruence.
  Qed.

  Theorem read_unaffected b destination value index :
    index <> zero_reg -> index <> destination ->
    apply_effect b (Write destination value) index = b index.
  Proof.
    intros Nonzero Different. cbn.
    destruct (reg_eq_dec index zero_reg); [contradiction|].
    destruct (reg_eq_dec index destination); congruence.
  Qed.
End RegisterEffects.
