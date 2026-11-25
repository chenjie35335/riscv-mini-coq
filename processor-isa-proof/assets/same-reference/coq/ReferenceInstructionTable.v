(* Extracted from the existing processor proof. Source mapping: ../provenance.json.
   Proof bodies below are unchanged; imports isolate the shared reference semantics. *)
From Coq Require Import NArith ZArith List Lia btauto.Btauto.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits NBitsDef NBitsOp.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.

Definition reference_instruction_codes : seq N := [::19;8211;12307;28691;24595;16403;4115;20499;1073762323;55;23;51;8243;12339;28723;24627;16435;4147;20531;1073741875;1073762355;111;103;99;4195;16483;24675;20579;28771;3;4099;8195;16387;20483;35;4131;8227;1048691;115;15;33554483;33558579;33562675;33566771;33570867;33574963;33579059;33583155].

Definition reference_instruction_code_widths : seq nat := [::5%nat;14%nat;14%nat;15%nat;15%nat;15%nat;13%nat;15%nat;31%nat;6%nat;5%nat;6%nat;14%nat;14%nat;15%nat;15%nat;15%nat;13%nat;15%nat;31%nat;31%nat;7%nat;7%nat;7%nat;13%nat;15%nat;15%nat;15%nat;15%nat;2%nat;13%nat;14%nat;15%nat;15%nat;6%nat;13%nat;14%nat;21%nat;7%nat;4%nat;26%nat;26%nat;26%nat;26%nat;26%nat;26%nat;26%nat;26%nat].

Definition reference_instruction_masks : seq N := [::28799;28799;28799;28799;28799;28799;4261441663;4261441663;4261441663;127;127;4261441663;4261441663;4261441663;4261441663;4261441663;4261441663;4261441663;4261441663;4261441663;4261441663;127;28799;28799;28799;28799;28799;28799;28799;28799;28799;28799;28799;28799;28799;28799;28799;4294967295;4294967295;28799;4261441663;4261441663;4261441663;4261441663;4261441663;4261441663;4261441663;4261441663].

Definition reference_instruction_mask_widths : seq nat := [::15%nat;15%nat;15%nat;15%nat;15%nat;15%nat;32%nat;32%nat;32%nat;7%nat;7%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;7%nat;15%nat;15%nat;15%nat;15%nat;15%nat;15%nat;15%nat;15%nat;15%nat;15%nat;15%nat;15%nat;15%nat;15%nat;15%nat;32%nat;32%nat;15%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat;32%nat].

Definition reference_instruction_code row := nth 0 reference_instruction_codes row.

Definition reference_instruction_code_width row := nth 0%nat reference_instruction_code_widths row.

Definition reference_instruction_mask row := nth 0 reference_instruction_masks row.

Definition reference_instruction_mask_width row := nth 0%nat reference_instruction_mask_widths row.
