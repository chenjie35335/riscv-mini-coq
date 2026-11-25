From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Theorem symbolic_uint_concrete inputs path id width :
 exists bits, size bits = width /\
 symbolic_register_value inputs path id (Gtyp (Fuint width)) = Gval (Fuint width) bits.
Proof.
 unfold symbolic_register_value. cbn [input_value_of_type sizeof_fgtyp].
 destruct (formal_symbolic_inputs inputs path [:: 0%nat; N.to_nat id] [::] width) as [bits Width].
 exists bits. split; [exact Width|reflexivity].
Qed.
Print Assumptions symbolic_uint_concrete.
