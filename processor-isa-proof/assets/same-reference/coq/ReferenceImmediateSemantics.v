(* Extracted from the existing processor proof. Source mapping: ../provenance.json.
   Proof bodies below are unchanged; imports isolate the shared reference semantics. *)
From Coq Require Import NArith ZArith List Lia btauto.Btauto.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits NBitsDef NBitsOp.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.

Definition load_imm_word_1306 (instruction:bits) := instruction.

Definition load_imm_word_1309 (instruction:bits) := (drop 20 (take 32 (load_imm_word_1306 instruction))).

Definition load_imm_word_1310 (instruction:bits) := (load_imm_word_1309 instruction).

Definition load_imm_word_1311 (instruction:bits) := (drop 25 (take 32 (load_imm_word_1306 instruction))).

Definition load_imm_word_1312 (instruction:bits) := (drop 7 (take 12 (load_imm_word_1306 instruction))).

Definition load_imm_word_1313 (instruction:bits) := ((load_imm_word_1312 instruction) ++ (load_imm_word_1311 instruction)).

Definition load_imm_word_1314 (instruction:bits) := (load_imm_word_1313 instruction).

Definition load_imm_word_1315 (instruction:bits) := (drop 31 (take 32 (load_imm_word_1306 instruction))).

Definition load_imm_word_1316 (instruction:bits) := (drop 7 (take 8 (load_imm_word_1306 instruction))).

Definition load_imm_word_1317 (instruction:bits) := (drop 25 (take 31 (load_imm_word_1306 instruction))).

Definition load_imm_word_1318 (instruction:bits) := (drop 8 (take 12 (load_imm_word_1306 instruction))).

Definition load_imm_word_1319 (instruction:bits) := ([::false] ++ (load_imm_word_1318 instruction)).

Definition load_imm_word_1320 (instruction:bits) := ((load_imm_word_1316 instruction) ++ (load_imm_word_1315 instruction)).

Definition load_imm_word_1321 (instruction:bits) := ((load_imm_word_1317 instruction) ++ (load_imm_word_1320 instruction)).

Definition load_imm_word_1322 (instruction:bits) := ((load_imm_word_1319 instruction) ++ (load_imm_word_1321 instruction)).

Definition load_imm_word_1323 (instruction:bits) := (load_imm_word_1322 instruction).

Definition load_imm_word_1324 (instruction:bits) := (drop 12 (take 32 (load_imm_word_1306 instruction))).

Definition load_imm_word_1325 (instruction:bits) := ([::false;false;false;false;false;false;false;false;false;false;false;false] ++ (load_imm_word_1324 instruction)).

Definition load_imm_word_1326 (instruction:bits) := (load_imm_word_1325 instruction).

Definition load_imm_word_1327 (instruction:bits) := (drop 31 (take 32 (load_imm_word_1306 instruction))).

Definition load_imm_word_1328 (instruction:bits) := (drop 12 (take 20 (load_imm_word_1306 instruction))).

Definition load_imm_word_1329 (instruction:bits) := (drop 20 (take 21 (load_imm_word_1306 instruction))).

Definition load_imm_word_1330 (instruction:bits) := (drop 25 (take 31 (load_imm_word_1306 instruction))).

Definition load_imm_word_1331 (instruction:bits) := (drop 21 (take 25 (load_imm_word_1306 instruction))).

Definition load_imm_word_1332 (instruction:bits) := ((load_imm_word_1331 instruction) ++ (load_imm_word_1330 instruction)).

Definition load_imm_word_1333 (instruction:bits) := ([::false] ++ (load_imm_word_1332 instruction)).

Definition load_imm_word_1334 (instruction:bits) := ((load_imm_word_1328 instruction) ++ (load_imm_word_1327 instruction)).

Definition load_imm_word_1335 (instruction:bits) := ((load_imm_word_1329 instruction) ++ (load_imm_word_1334 instruction)).

Definition load_imm_word_1336 (instruction:bits) := ((load_imm_word_1333 instruction) ++ (load_imm_word_1335 instruction)).

Definition load_i_immediate instruction := sext_to 32(drop 20(take 32 instruction)).

Lemma load_imm_resize_id word width : size word=width ->sext_to width(take width word)=word.
Proof. intros Size. rewrite -Size take_size. unfold sext_to,sext. rewrite subnn cats0. reflexivity. Qed.

Lemma load_imm_resize_size word width : (size word<=width)%nat ->size(sext_to width(take width word))=width.
Proof. intro Bound. rewrite take_oversize;[|exact Bound]. unfold sext_to. rewrite size_sext. exact(subnKC Bound). Qed.

Lemma load_i_immediate_size instruction :size instruction=32%nat ->size(load_i_immediate instruction)=32%nat.
Proof. intro Size. unfold load_i_immediate,sext_to. rewrite size_sext size_drop size_take Size. reflexivity. Qed.

Definition dut_s_immediate instruction := sext_to 32 (load_imm_word_1313 instruction).

Definition dut_b_immediate instruction := sext_to 32 (load_imm_word_1322 instruction).

Definition dut_j_immediate instruction := sext_to 32 (load_imm_word_1336 instruction).

Definition dut_imm_result mode instruction := match mode with
 | O => load_i_immediate instruction | S O => dut_s_immediate instruction
 | S (S O) => dut_b_immediate instruction | _ => dut_j_immediate instruction end.

Lemma dut_imm_s_payload_size instruction : size instruction=32%nat -> size(load_imm_word_1313 instruction)=12%nat.
Proof. intro Size;unfold load_imm_word_1313,load_imm_word_1312,load_imm_word_1311,load_imm_word_1306;rewrite size_cat !size_drop !size_take Size;reflexivity. Qed.

Lemma dut_imm_b_payload_size instruction : size instruction=32%nat -> size(load_imm_word_1322 instruction)=13%nat.
Proof. intro Size;unfold load_imm_word_1322,load_imm_word_1321,load_imm_word_1320,load_imm_word_1319,load_imm_word_1318,load_imm_word_1317,load_imm_word_1316,load_imm_word_1315,load_imm_word_1306;rewrite !size_cat !size_drop !size_take Size;reflexivity. Qed.

Lemma dut_imm_j_payload_size instruction : size instruction=32%nat -> size(load_imm_word_1336 instruction)=21%nat.
Proof. intro Size;unfold load_imm_word_1336,load_imm_word_1335,load_imm_word_1334,load_imm_word_1333,load_imm_word_1332,load_imm_word_1331,load_imm_word_1330,load_imm_word_1329,load_imm_word_1328,load_imm_word_1327,load_imm_word_1306;rewrite !size_cat !size_drop !size_take Size;reflexivity. Qed.

Lemma dut_imm_result_size mode instruction : (mode<4)%coq_nat ->size instruction=32%nat ->size(dut_imm_result mode instruction)=32%nat.
Proof.
 intros Mode Size. destruct mode as[|[|[|[|mode]]]];try lia;cbn [dut_imm_result].
 - exact(load_i_immediate_size instruction Size).
 - unfold dut_s_immediate,sext_to;rewrite size_sext (dut_imm_s_payload_size instruction Size);reflexivity.
 - unfold dut_b_immediate,sext_to;rewrite size_sext (dut_imm_b_payload_size instruction Size);reflexivity.
 - unfold dut_j_immediate,sext_to;rewrite size_sext (dut_imm_j_payload_size instruction Size);reflexivity.
Qed.

Lemma dut_imm_extend_12_13_32 word :size word=12%nat ->
 sext_to 32(take 32(sext_to 13(take 13 word)))=sext_to 32 word.
Proof.
 intro Size. assert(S13:size(sext_to 13(take 13 word))=13%nat).
 { apply load_imm_resize_size;rewrite Size;reflexivity. }
 rewrite take_oversize;[|rewrite S13;reflexivity]. unfold sext_to at 1;rewrite S13.
 rewrite take_oversize;[|rewrite Size;reflexivity]. unfold sext_to;rewrite Size sext_sext;reflexivity.
Qed.

Lemma dut_s_immediate_bits instruction : dut_s_immediate instruction =
 sext_to 32 (drop 7 (take 12 instruction) ++ drop 25 (take 32 instruction)).
Proof. reflexivity. Qed.

Lemma dut_b_immediate_bits instruction : dut_b_immediate instruction =
 sext_to 32 (([::false] ++ drop 8 (take 12 instruction)) ++
  (drop 25 (take 31 instruction) ++ (drop 7 (take 8 instruction) ++ drop 31 (take 32 instruction)))).
Proof. reflexivity. Qed.

Lemma dut_j_immediate_bits instruction : dut_j_immediate instruction =
 sext_to 32 (([::false] ++ (drop 21 (take 25 instruction) ++ drop 25 (take 31 instruction))) ++
  (drop 20 (take 21 instruction) ++ (drop 12 (take 20 instruction) ++ drop 31 (take 32 instruction)))).
Proof. reflexivity. Qed.

Lemma dut_j_immediate_canonical instruction : size instruction=32%nat ->
 dut_j_immediate instruction=sext_to 32(([::false]++drop 21(take 31 instruction))++(drop 20(take 21 instruction)++(drop 12(take 20 instruction)++drop 31(take 32 instruction)))).
Proof.
 intro Size. do 32(let b:=fresh "b" in destruct instruction as[|b instruction];[discriminate Size|];cbn[size]in Size).
 destruct instruction;[reflexivity|discriminate Size].
Qed.
