From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths Semantics_with_implicit_widths.
Inductive normalized_bit : hvalue -> Prop :=
 | normalized_known b : normalized_bit (Gval (Fuint 1) [::b])
 | normalized_pending : normalized_bit (Needtobedefined (Gtyp (Fuint 1)))
 | normalized_uninitialized : normalized_bit (Uninitialized (Gtyp (Fuint 1)))
 | normalized_invalid : normalized_bit (Undefinedonpurpose (Gtyp (Fuint 1))).
Lemma adapted_bit_normalized input result :
 adapt_hvalue_as_type input (Gtyp (Fuint 1)) = Some result -> normalized_bit result.
Proof.
 destruct input as [ground bits|element array|bundle|t|t|t];
 cbn [adapt_hvalue_as_type]; intro Step; try discriminate Step.
 - destruct ground; try discriminate Step. inversion Step; subst result.
   destruct bits as [|b tail].
   + change (normalized_bit (Gval (Fuint 1) [::false])). exact (normalized_known false).
   + destruct tail; change (normalized_bit (Gval (Fuint 1) [::b])); exact (normalized_known b).
 - destruct (ftype_mux false t (Gtyp (Fuint 1))); inversion Step; constructor.
 - destruct (ftype_mux false t (Gtyp (Fuint 1))); inversion Step; constructor.
 - destruct (ftype_mux false t (Gtyp (Fuint 1))); inversion Step; constructor.
Qed.
