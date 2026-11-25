Require Import ScalarNodeFrames.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths
 Semantics_with_implicit_widths Semantics_with_memory.
Definition uint_source_safe_b node rhs :=
 match rhs with
 | Eref (Eid _) => true
 | Eref reference => node != HiF.base_ref reference
 | _ => true end.
Lemma uint_source_safe_b_sound node rhs :
 uint_source_safe_b node rhs -> connection_preserves_uint_source node rhs.
Proof.
 destruct rhs; try (intros _; exact I).
 destruct h as [id|base field|base index|base index]; cbn [uint_source_safe_b connection_preserves_uint_source HiF.base_ref];
 try (intro H; left; exact H).
 intros _. destruct (node == id) eqn:Same.
 - right. move/eqP: Same => Same. subst id. reflexivity.
 - left. reflexivity.
Qed.
Fixpoint scalar_suffix_safe_b mm node stmts : bool :=
 match stmts with
 | Qnil => true
 | Qcons st tail =>
 (match st with
 | Sskip | Sinst _ _ => true
 | Swire name _ | Sreg name _ | Smem name _ | Snode name _ => node != name
 | Sfcnct lhs rhs => (node != HiF.base_ref lhs) &&
   (is_memory_writer_ref mm lhs == false) && uint_source_safe_b node rhs
 | Sinvalid reference => (node != HiF.base_ref reference) && (is_memory_writer_ref mm reference == false)
 | Swhen _ _ _ => false end) && scalar_suffix_safe_b mm node tail
 end.
Theorem scalar_suffix_safe_b_sound : forall mm node stmts,
 scalar_suffix_safe_b mm node stmts -> scalar_suffix_safe mm node stmts.
Proof.
 fix IH 3. intros mm node stmts. destruct stmts as [|st tail]; [intros _; exact I|].
 cbn [scalar_suffix_safe_b scalar_suffix_safe]. move/andP => [Head Tail].
 split; [|exact (IH mm node tail Tail)].
 destruct st as [|name typ|name reg|name mem|name mi|name expr|lhs rhs|reference|cond yes no];
 try exact Head; try exact I; try discriminate Head.
 - move/andP: Head => [/andP [Different /eqP Memory] Source].
   split; [exact Different|]. split; [exact Memory|]. apply uint_source_safe_b_sound. exact Source.
 - move/andP: Head => [Different /eqP Memory]. split; assumption.
Qed.
Print Assumptions scalar_suffix_safe_b_sound.
