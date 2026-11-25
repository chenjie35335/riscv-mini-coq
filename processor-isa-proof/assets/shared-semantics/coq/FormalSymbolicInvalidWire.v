From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Lemma formal_invalid_uint_wire inputs path site mm old current node width :
 VM.find node current = Some (Needtobedefined (Gtyp (Fuint width))) ->
 invalidate_ref_with_memory mm false (Eid node)
 (formal_invalid_policy inputs path site) old current =
 Some (VM.add node (formal_invalid_policy inputs path site (Gtyp (Fuint width))) current).
Proof.
 intro Current. unfold invalidate_ref_with_memory, undef_ref.
 cbn [HiF.base_ref eval_type_of_ref]. rewrite Current.
 cbn [option_map type_of_val repl_val_part].
 unfold formal_invalid_policy. cbn [input_value_of_type replace_writeable].
 reflexivity.
Qed.
Lemma formal_invalid_uint_word inputs path site width :
 exists bits,
 formal_invalid_policy inputs path site (Gtyp (Fuint width)) = Gval (Fuint width) bits /\ size bits = width.
Proof.
 unfold formal_invalid_policy. cbn [input_value_of_type].
 eexists. split; [reflexivity|].
 exact (proj2_sig (formal_symbolic_inputs inputs path site nil width)).
Qed.
Print Assumptions formal_invalid_uint_wire.
Print Assumptions formal_invalid_uint_word.
