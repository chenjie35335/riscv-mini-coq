(* Frozen-reference symbolic logic; preserved proof bodies. See ../provenance.json. *)
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.


Lemma ref_pc_target_resize32 word :size word=32%nat ->zext_to 32(take 32 word)=word.
Proof. intro Size. assert(Take:take 32 word=word)by(rewrite <-Size;apply take_size).
 rewrite Take. unfold zext_to,zext. rewrite Size subnn cats0. reflexivity. Qed.

Definition reference_pc_target_value (guards:VarOrder.T->bool) pc immediate rs1 :=
 let w6309 := from_N 33(to_N pc+to_N immediate) in
 let w6310 := take 32 w6309 in
 let w6315 := if guards 2966 then w6310 else pc in
 let w6326 := if guards 2357 then w6315 else pc in
 let w6335 := rs1 in
 let w6336 := from_N 33(to_N w6335+to_N immediate) in
 let w6337 := take 32 w6336 in
 let w6338 := drop 1(take 32 w6337) in
 let w6339 := [::false]++w6338 in
 let w6347 := if guards 2949 then w6339 else w6326 in
 let w6360 := if guards 2010 then w6347 else w6326 in
 let w6369 := from_N 33(to_N pc+to_N immediate) in
 let w6370 := take 32 w6369 in
 let w6374 := if guards 2929 then w6370 else w6360 in
 let w6378 := if guards 2912 then w6374 else w6360 in
 let w6388 := if guards 2004 then w6378 else w6360 in
 let w6393 := from_N 33(to_N pc+to_N immediate) in
 let w6394 := take 32 w6393 in
 let w6398 := if guards 2909 then w6394 else w6388 in
 let w6402 := if guards 2892 then w6398 else w6388 in
 let w6412 := if guards 1998 then w6402 else w6388 in
 let w6417 := from_N 33(to_N pc+to_N immediate) in
 let w6418 := take 32 w6417 in
 let w6422 := if guards 2889 then w6418 else w6412 in
 let w6426 := if guards 2872 then w6422 else w6412 in
 let w6436 := if guards 1992 then w6426 else w6412 in
 let w6441 := from_N 33(to_N pc+to_N immediate) in
 let w6442 := take 32 w6441 in
 let w6446 := if guards 2867 then w6442 else w6436 in
 let w6450 := if guards 2850 then w6446 else w6436 in
 let w6460 := if guards 1986 then w6450 else w6436 in
 let w6465 := from_N 33(to_N pc+to_N immediate) in
 let w6466 := take 32 w6465 in
 let w6470 := if guards 2847 then w6466 else w6460 in
 let w6474 := if guards 2830 then w6470 else w6460 in
 let w6484 := if guards 1980 then w6474 else w6460 in
 let w6489 := from_N 33(to_N pc+to_N immediate) in
 let w6490 := take 32 w6489 in
 let w6494 := if guards 2825 then w6490 else w6484 in
 let w6498 := if guards 2806 then w6494 else w6484 in
 let w6508 := if guards 1974 then w6498 else w6484 in
 w6508.
