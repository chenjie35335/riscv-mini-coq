# Porting the templates

The original `assets/coq/` modules are newly factored, standard-library-only proofs of the reusable logical patterns. They are not copies of the complete riscv-mini proof and do not import its generated model. Tested with Coq 8.20.1; other Coq/Rocq versions need their own check.

For this project's fixed-reference profile, start with [same-reference reuse](same-reference-reuse.md) and the actual proof bundles under `assets/shared-semantics` and `assets/same-reference`; they depend on the shared FIRRTL/nbits/MathComp libraries. The table below describes the portable interface templates only.

## Files and target obligations

| Module | Exported tool | Obligation the target must prove |
|---|---|---|
| `CycleRefinement.v` | finite execution invariant; raw/view lifting; stuttering simulation | actual cycle relation; view extraction; invariant base/preservation; idle/retire reference matching |
| `RegisterEffects.v` | effect preserves pointwise RF agreement; zero and read-forwarding facts | actual DUT/reference writes equal the abstract effect; architecturally valid zero bank |
| `CheckerFacts.v` | guarded checker; disabled guard; numeric equality bridge | actual generated predicate implements comparison; exact enable/phase/instance interpretation |
| `EvaluationFacts.v` | unrelated-write frame; iteration composition; fixed-point tails | expression footprint/locality; actual partial step; reached state really self-loops |
| `RankedSettling.v` | boolean rank certificate soundness; bounded/unbounded dependency propagation | dependency closure and faithful graph; stable seeds; semantic one-step transfer |
| `Examples.v` | small compiled applications | examples only, no target processor claim |

Use explicit `@lemma` arguments when Coq's inferred implicits obscure adapter errors. All templates retain ordinary transparent definitions and checked proofs; none add `Axiom`, `Admitted`, functional extensionality, or proof irrelevance.

## Suggested adapter boundary

In the target proof directory, implement only the layers needed by its obligations. Names below describe obligations; they are not unproved declarations to paste:

```text
RawCycleStep         := actual observation/commit relation with successful evaluation
ViewAt               := signal bindings + concrete representations + widths
ViewStep             := extracted reset/hold/advance/flush/writeback equations
Joint                := architectural and pending-state relation
InitialJoint         : actual initialization yields ViewAt ∧ Joint
ExtractCycle         : RawCycleStep ∧ ViewAt(before) yields ViewAt(after) ∧ ViewStep
PreserveJoint        : ViewStep ∧ Joint(before) yields Joint(after)
AdvanceMatch         : Joint ∧ architectural advance yields one ISA step and next Joint
IdleMatch            : Joint ∧ no architectural advance preserves unchanged ISA state
OriginalCheckerSound : reachable Joint yields exact generated assertions
```

If preservation needs input legality, include it in `RawCycleStep`/`ViewStep` and prove real legal executions induce that relation. For history-dependent assumptions, carry the required ghost/history state. These templates are generic relations, not an implicit assumption that every hardware transition is legal.

The simulation uses the same `Input` label in a DUT cycle and its matched ISA step. Include the committed instruction, memory observations and other relevant choices in a proved label projection, or adapt the template to a separate label relation. Do not equate fetched and retired instructions across stalls/flushes. The template has zero-or-one ISA step per cycle; model multi-issue retirement as a list of ISA steps. Reset may require a separate initialization/transition case.

`advances` describes architectural state transitions, not just successful instruction retirement. Derive it from the DUT's real retirement/event logic. A synchronous trap or interrupt may require an ISA transition even with retire-valid false; classify such a cycle as an advance and prove the corresponding event reference step. If retirement plus an event needs two ISA steps under the reference semantics, extend the template. Only true stutters may use `IdleMatch`; a trap cannot be treated as a stalled cycle to avoid its proof.

For memory and CSR, extend the architectural relation and effect algebra to cover all observed state and side effects. Respect memory response latency, MMIO visibility, exceptions, reservation state and target privilege scope as applicable. Copy neither RV32 width nor +4 PC advance into an unrelated ISA.

## Run the local checks

From the folder containing this skill:

```sh
python3 processor-isa-proof/scripts/check_templates.py
```

For a selected opam switch, pass its tools explicitly:

```sh
python3 processor-isa-proof/scripts/check_templates.py \
  --coqc /path/to/switch/bin/coqc --coqchk /path/to/switch/bin/coqchk
```

The script copies `.v` files to a fresh directory under the system temporary directory, compiles with logical prefix `ProcessorProof`, checks assumptions of exported tools/examples, and runs recursive `coqchk`. It prints the build/report path. `--build-dir` accepts a new or empty directory **outside the skill**; no compiler products enter the assets. Tool output and `report.json` stay in that build directory. A failed command exits nonzero. The script requires Python standard library plus Coq tools; no riscv-mini checkout is needed.

`Examples.v` exercises a pending-result increment pipeline with stalls, forwarding/zero behavior, bounded and unbounded rank propagation, a frame instance, fixed-point tails, unequal-width numeric comparison, a killed-packet RF-preview checker and a counterexample to “successful fuel means fixed.” The preview example uses unbounded `N` values; it does not prove an RV64 width or actual DUT wiring. `CycleRefinement` does not prove eventual retirement.

To use the templates in a target, copy only needed modules to its proof source tree and compile under an appropriate logical prefix. Adapt import paths and prove the adapter obligations before claiming target results.

## Use as a Codex skill

This directory is already a complete local skill package. To install later, place the entire `processor-isa-proof/` directory under the user's configured Codex skills directory and reload/discover skills as appropriate for that environment. Then invoke `$processor-isa-proof` with the target repository and scope. This extraction does not modify the global skill installation.

When it is not installed, an agent can read `processor-isa-proof/SKILL.md` directly and follow the linked resources. The source hash manifest is for provenance only; the package and template checks are self-contained.

The recorded extraction-time check is in [template-validation.json](template-validation.json): 6 compiled modules, 35 selected theorem/example assumption reports closed under the global context, and recursive kernel checking passed under Coq 8.20.1. Source hashes bind that record to these assets. Re-run the script after adapting or changing them.
