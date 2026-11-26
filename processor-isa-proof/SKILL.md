---
name: processor-isa-proof
description: Develop Coq/Rocq processor ISA refinement proofs using a shared reference-model proof library, DUT cycle contracts, checker and evaluator lemmas, and coordinated proof agents. Use when proving another DUT against the same reference model or extracting reusable processor proofs.
---

# Processor ISA Proof

Default to the same ISA reference model used by this project. Reuse its proved semantics and execution infrastructure; concentrate new proofs on the DUT contracts, state correspondence, and checker integration. Treat structural similarity as a source of candidate DUT invariants; establish each candidate from the actual DUT semantics.

## Reuse the reference library first

Read [fixed-reference reuse](references/same-reference-reuse.md) for this project profile. Search the actual statements before creating a new lemma. Use `python3 scripts/find_lemmas.py <name-or-terms>` from the skill folder to retrieve a few statements; use `--bundle shared|reference|history` to narrow the search. Inspect the full source when a returned statement is truncated:

- [Shared evaluator proofs](assets/shared-semantics/manifest.json): 30 original modules covering typed/ground/UInt expressions, validif, symbolic choices, frames, register hold and iteration facts.
- [Reference proof bundle](assets/same-reference/provenance.json): 21 isolated modules covering decoder, immediates, load/store arithmetic, RF effect, PC, branch/redirect and event logic.
- [High-level reference catalog](references/reference-theorem-catalog.json): 130 original theorem declarations in 20 modules, including reference RF read/write and PC/memory/event histories. Preserve these proofs behind a proved reference embedding; reconnect combined-DUT observation wrappers.
- [Portable templates](assets/coq): standard-library-only logical interfaces for cycle lifting, simulation, effects, guarded assertions, frames, ranks and fixed points.

Do not redo reference ALU/immediate/decoder/memory mathematics merely because the DUT or flattened node numbers changed. Reuse unchanged functions and proof bodies. For renamed/re-embedded reference circuits, prove lookup, expression, policy and step transport once; literal ID replacement is not a proof. Reference-internal canonical IDs may remain in pure guard functions. Match theorem premises to the selected instruction domain and configuration; old 37-class coverage does not cover newly enabled CSR/exception behavior by itself.

## Choose the boundary before proving

Inspect the DUT, ISA reference, generated semantics, assumptions, and checker. Record the exact source revision, instruction/privilege scope, reset behavior, memory environment, observation phase, and retirement event. Work on the representation selected by the user (for this extraction: flattened low FIRRTL). Actively read the instantiated processor source and decoder tables to derive combinational specifications, stage contracts and candidate invariants before expanding large generated cones. Follow [source-guided lemma extraction](references/source-guided-lemmas.md) for worked ALU/branch/RF/pipeline examples and source-to-flat traceability. Prove the resulting contracts on the selected generated model; source inspection itself does not discharge them.

Separate three time scales: internal combinational iterations, hardware cycles, and architectural retirement steps. Identify where failed evaluation returns `None`, where symbolic invalid values are chosen, and where registers/memory commit. Derive successful histories from the real execution relation.

For a new target, produce a small scope/obligation map first; continue with obligations whose contracts are already clear. Read [the porting guide](references/porting-guide.md) for the adapter checklist and template commands. Do not infer supported ISA coverage from the number of assertions.

## Build the reusable proof layers

1. **Execution facts:** Import the shared frame, expression-locality, typed-node and iteration lemmas; prove only the new target certificates and missing execution facts. Keep aliasing and symbolic choices explicit. For settling or large expression cones, read [evaluation and fixed points](references/evaluation-and-fixed-points.md).
2. **Cycle contracts:** Define a view binding raw state to concrete signals and widths. Put correctness relations in a separate invariant. Prove reset, hold, advance, forwarding, flush, and commit equations once from the DUT; expose observation-to-observation contracts without raw iteration callbacks.
3. **Architectural invariant:** Relate RF, PC, pipeline phase, pending effects, and necessary memory/CSR/event state. If their preservation depends cyclically on one another, prove a joint invariant by base and cycle step. Read [DUT invariant patterns](references/dut-invariants.md).
4. **ISA alignment:** Reuse reference decoder coverage and semantic-family lemmas at their actual scope; prove target decode/operand/effect matching and any new coverage obligations; align pending writes and control flow with the reference step at the actual architectural advance. Stalls may match zero reference steps. Traps/interrupts can advance architectural state without retiring an instruction: the template's `advances` flag must include those events. It supports at most one reference step per cycle; extend it for multiple retirements/events or reset transitions.
5. **Checker bridge:** Prove generated comparison equations and enables, discharge the exact original assertion at its actual phase, and lift through the real instance map. Read [checker and validation](references/checker-and-validation.md) before claiming assertion completion.

Use the fixed-reference/shared-semantics bundles when their statements fit; use [assets/coq](assets/coq) for generic interfaces. Section hypotheses are explicit adapter obligations. Prove them for the target; do not replace them with global axioms. Numeric checker equality can use decoded values without proving structural type equality; retain width facts needed by evaluation and arithmetic.

## Keep the proof tractable

Prove only the cones needed by current obligations. Use checked dependency/rank tables and semantic propagation instead of repeatedly reducing the whole DUT. Cache a shared cycle invariant and register-effect lemmas; instantiate them across RF entries, instruction families, and checker lanes. Keep generated node IDs, iteration bounds, and decoder rows in target-specific adapters/certificates.

For multi-agent proof work, read [agent decomposition and shared lemmas](references/agent-workflow.md) and instantiate [role task prompts](assets/agent-tasks.json). Schedule independent modules using the dependency DAG and available memory; do not create cyclic imports between RF and PC. Delegate independent families only when agent delegation is authorized. Reuse prior checks only when source, artifact, compiler, and dependency identities match. Report completed modules from successful tool results, not elapsed time or process activity.

## Validate the actual claim

For new proof code, avoid admissions and unchecked proof escapes. Preserve existing libraries and user-selected trust policy; report any inherited axioms explicitly rather than silently blessing or repairing them. Audit current declarations and `Print Assumptions` for the actual aggregate: historical admission lists may be stale.

Check that the model and theorem statements still match the original generated artifacts. Compile the dependency closure and kernel-check it, with products outside the proof source directory when requested. A parallel check requires complete, hash-bound coverage, including external dependencies. Use `scripts/check_templates.py` for portable templates and `scripts/check_reference_assets.py --library-root <firrtl2coq> --tool-bin <coq-bin> --jobs 4` for source-only rebuilding of both extracted bundles. These checks validate assets, never a new target DUT.

Report: exact scope, proved endpoints, remaining adapter obligations, trust assumptions, and verification evidence. Distinguish enabled-event correctness from an implication proved by a permanently false guard. An enlarged assume domain requires new event/CSR/trap proofs. Finite trace safety does not establish eventual retirement.

## Resources

- [Extraction analysis](references/riscv-mini-analysis.md): concrete source theorems, what transfers, and what stays DUT-specific.
- [Fixed-reference reuse](references/same-reference-reuse.md): actual reusable code and reference-cone adapters.
- [Reference asset validation](references/reference-validation.json): source identities, 195 closed theorem audits and recursive kernel coverage.
- [Source-guided lemmas](references/source-guided-lemmas.md): extract local specifications and invariant candidates from processor implementations, then prove their flat-low counterparts.
- [Agent workflow](references/agent-workflow.md): functional roles, four-slot scheduling, ownership and lemma sharing.
- [Provenance](references/provenance.json): source hashes and locations for this extraction, not a certificate for the full original processor proof.
- [Porting guide](references/porting-guide.md): generic module interfaces, example use, and local validation.
- `scripts/check_templates.py`: compile all generic modules and examples, audit exported theorem assumptions, and run recursive `coqchk` in an external build directory.
