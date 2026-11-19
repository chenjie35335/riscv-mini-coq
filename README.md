# riscv-mini

The complete proof is available at [riscv-mini-proof](https://github.com/chenjie35335/riscv-mini-proof).

## FIRRTL to Coq

`firrtl2coq/` is a translator submodule from https://github.com/wky17/firrtl2coq.
The documented translator revision is `482f062d9ea4b6638c2e1bf8327632694b44db66`.

`make coq` regenerates `formal/CoreSoc.hi.fir` from the current Scala sources
and translates it into `formal/CoreSoc.v`. It uses the same
`CoreSoc(new Core(MiniConfig().core))` top level as the formal tests, including
RVFI, the reference model, checkers, and instruction/data memories. The `Tile`
top level additionally includes instruction and data caches.
Only these two source artifacts are published; temporary compilation files are
removed automatically.

The earlier generated model contained 12 modules, two memories, 45 assertions,
and one assumption, and passed compilation with Coq 8.16.0. Its source baseline
was `dac51f0b4c2d02ac0ec235ddcd10bd5738b15f6e`, with reference-model revision
`2525d297a84e68f1c956478276e16b7a77e8b789`.

The current generation workflow requires Java 17, Mill 0.10.0-M4, Coq 8.20.1,
MathComp ssreflect/algebra 1.19.0, OCaml 4.14.2, and dune 3.16 or newer.
For example, create a dedicated opam switch:

```bash
opam switch create firrtl2coq ocaml-base-compiler.4.14.2
opam repository add coq-released https://coq.inria.fr/opam/released --switch=firrtl2coq
opam install --switch=firrtl2coq coq.8.20.1 coq-mathcomp-ssreflect.1.19.0 coq-mathcomp-algebra.1.19.0 dune
opam exec --switch=firrtl2coq -- make coq
```

If the dependencies are already available, run from the repository root:

```bash
make coq
# Optional: change the Coq library build parallelism (default: 4).
make coq JOBS=8
# The script can also be invoked directly:
bash scripts/generate-coq.sh
```

The phony `coq` target invokes `scripts/generate-coq.sh` on every run. The script
initializes the translator submodule if needed, generates high FIRRTL with
resolved connections and widths, builds the translator and its Coq libraries,
and checks the generated model with `coqc` before updating `formal/`.
Generation or compilation failures leave the existing outputs unchanged.
Scala sources are preserved, and translator build caches remain in ignored
submodule directories. The default `make` / `make compile` targets generate Verilog.

Translation alone does not prove processor correctness. The translator emits
`assert` statements as lemmas containing `Admitted`, represents `assume`
statements as premises, and ignores `printf`. The complete assertion proofs
are maintained in [riscv-mini-proof](https://github.com/chenjie35335/riscv-mini-proof).

## Flattened Low FIRRTL Assertion Proofs

The proof covers **all 45 original assertions** of
`formal/flat-low/CoreSoc.lo.fir` using Coq 8.20.1. The flattened model contains
one module, no submodule instances, and the original assumption; no design
assertions were added. Translation was reproduced, and both generated
`CoreSoc.v` files passed the original hash checks. The high FIRRTL compilation
record above belongs to the earlier workflow.

The following paths describe the local proof workspace. For the complete proof
sources, see the [dedicated proof repository](https://github.com/chenjie35335/riscv-mini-proof).
The local [file inventory](formal/README.md) groups sources by function and
separates final dependencies from auxiliary and historical files. Sources and
artifacts outside the final dependency closure were archived under
`temp/formal/`, preserving their directory structure; the move and hash manifest
is `temp/formal-archive-manifest.json`.

| Area | Main files or families | Proof approach |
| --- | --- | --- |
| Original assertions | `GeneratedAssertion0.v` through `GeneratedAssertion44.v`, `AllOriginalAssertions.v` | Preserve the generated propositions, derive each from observations and legal traces, and conjoin all 45 results. |
| Cycle interface and joint invariant | `CycleView*`, `CycleJointBase/Step/Invariant`, `CycleDataReachability` | Map environments to cycle views, establish initialization and preservation, and induct over cycles. |
| Register files, x0, and writeback | `RF*`, `DUTBank*`, `ReferenceBank*`, `X0*`, `Cycle*BankAdvance` | Relate implementation and reference register files, prove writeback by instruction class, and track pending operations. |
| PC and instruction fetch | `Fetch*`, `FormalFetch*`, `CommitPC*`, `PCRelative*`, `JALR*` | Align PCs through reset, stalls, sequential execution, branches, and jumps. |
| Decode and pipeline | `CycleInstruction*`, `ReferenceControl*`, `EarlyControl*`, `Bubble*`, `Pipeline*` | Establish instruction coverage, control correspondence, and stability through normal, bubble/NOP, and stall paths. |
| Memory operations | `Data*`, `MemoryPendingInvariant`, `StorePendingInvariant`, `CycleLoad*`, `CycleStore*` | Relate ports and memory states, track delayed requests, and align addresses, data, valid signals, and widths. |
| Exceptions, CSR, and interrupts | `Exception*`, `FormalCSR*`, `InterruptZero*` | Connect exception events, PC selection, and control inputs to the joint invariant; this does not separately establish a complete CSR specification. |
| Execution semantics and certificates | `Concrete*`, `FormalDeclared*`, `*Connection*`, `*Frames`, `*DependencyRanks`, `*GraphPropagation` | Derive evaluation, connection, typing, and environment lemmas from FIRRTL statements and reuse dependency and propagation certificates. |

Most files reside in `formal/flat-low/staged-integration/`, with shared
foundations in `formal/flat-low/`. Historical hierarchical models,
`legacy-validif-baseline/`, and unused experiments are archived under
`temp/formal/` and excluded from the current build. `CoreSocModel.v` contains
the generated definitions preceding the first unproved assertion; proofs import
this prefix to avoid depending on the generated admitted statements.

The proof proceeds from FIRRTL evaluation and connection lemmas through cycle
transitions and joint register-file/PC/memory/pipeline invariants to the 45
assertions and their conjunction. The final theorem requires only the original
model's `generated_observe … = Some states` and `generated_legal_trace …`.
`Print Assumptions` reports the two existing library axioms
`HiEnv_with_implicit_widths.ftype_eqn_eq` and `ffield_eqn_eq`.

Start with [the combined theorem](formal/flat-low/staged-integration/AllOriginalAssertions.v),
then an individual `GeneratedAssertionN.v` and
[the cycle joint invariant](formal/flat-low/staged-integration/CycleJointInvariant.v).
Consult the foundation certificates when tracing individual connections.

The documented validation includes a clean source rebuild, recursive `coqchk`,
and a separate parallel kernel check covering all dependencies. Local reports:
[final verification](formal/flat-low/final-snapshot-verification.json) and
[assertion audit](formal/flat-low/original-assertion-proof-audit.json).
Local reproduction and verification instructions are in
[REPRODUCE_FLAT_LOW.txt](formal/generators/REPRODUCE_FLAT_LOW.txt) and
[VERIFY_ORIGINAL_ASSERTIONS.txt](formal/generators/VERIFY_ORIGINAL_ASSERTIONS.txt).
Proof-specific generators and audit scripts remain in `formal/generators/`;
the main high FIRRTL generation script is `scripts/generate-coq.sh`.

## MLIR to Coq State-Machine Workflow

The alternative translator described in [fir2coq.md](fir2coq.md) resides in the
local `mlir-to-coq/` directory. It uses CIRCT to parse and verify FIRRTL dialect
MLIR and generates executable Coq definitions: `Inputs`, `State`, `Outputs`,
`eval`, `outputs`, `step`, and `trace`, with
`eval : Inputs -> State -> Outputs * State`. This workflow uses `make coq-mlir`.

Dependencies are Java 17, Mill 0.10.0-M4, a C++17 compiler, CMake 3.20 or newer,
Ninja, Python 3 for tests, Coq (validated with 8.16.0), and the complete
[CIRCT SDK firtool-1.62.0](https://github.com/llvm/circt/releases/tag/firtool-1.62.0),
including headers, libraries, `firtool`, and `circt-opt`. The standalone
`firtool` executable is insufficient. `Semantics.v` requires only the Coq
standard library.

```bash
export CIRCT_ROOT=/path/to/firtool-1.62.0
make coq-mlir
# If Coq is installed in the switch above:
opam exec --switch=firrtl2coq -- make coq-mlir
```

The command generates CoreSoc FIRRTL, lowers CHIRRTL, infers widths and resets,
flattens aggregate types, inlines modules, expands conditional connections,
and exports Coq. After both the semantics and model pass `coqc`, it publishes:

| File | Purpose |
| --- | --- |
| `formal/mlir/CoreSoc.mlir` | Normalized FIRRTL dialect MLIR |
| `formal/mlir/CoreSoc.v` | CoreSoc state-machine model |
| `formal/mlir/Semantics.v` | Bit-width, signed-integer, event, and trace semantics |

Build caches reside in `out/coq-mlir/`; `JOBS=4` adjusts C++ build parallelism.
By default, `--named-nodes` emits intermediate expressions as separate
`Definition`s. Use `make coq-mlir COQ_NAMED_NODES=0` for local `let` bindings
inside `eval_with_events`. To translate an existing FIRRTL file:

```bash
bash formal/generators/generate-coq-mlir.sh /path/to/CoreSoc.fir
```

Numeric fields use `Z`, with `bv` enforcing widths on inputs, state, and results;
`signed` interprets two's complement. Each `step` represents one rising edge of
the same clock. `outputs` observes the state before that edge, and
`trace inputs initial n` returns the state after n transitions. The caller
supplies the initial state; `step` handles synchronous reset.

Supported designs use one clock, known-width UInt/SInt values, synchronous
reset, and memories with power-of-two depth up to 1024, at most one write port,
read latency zero, write latency one, and a one-bit mask. Memory cells become
individual state fields; memories without write ports retain their initial
contents. Hierarchy, aggregates, and conditional connections must be lowered
first. Asynchronous reset, derived clocks, multiple drivers, and unsupported
operations are rejected. Additional `undef_*`, `divzero_*`, and `memundef_*`
inputs represent undefined data, division-by-zero results, and disabled reads.

`assert`, `assume`, `cover`, and `printf` are preserved as observation events
with enables, predicates, message bytes, and print arguments. `assertions` and
`assumptions` expose the corresponding propositions. Traces do not automatically
filter inputs by assumptions or prove assertions. Generated code introduces no
`Axiom` or `Admitted`. Tests use Coq `vm_compute` to check concrete operations
and transitions and verify rejection of unsupported inputs; they do not prove
semantic preservation of the entire translator or processor correctness.

## Reference-Model Integration

The modified version integrates the updated reference model. Generate formal
transition systems with:

```bash
# BTOR2 format
mill chiselModule.test.testOnly formal.RISCVMiniFormalSpecBtor
# SystemVerilog format for SymbiYosys
mill chiselModule.test.testOnly formal.RISCVMiniFormalSpecSV
```

Author: Donggyu Kim (dgkim@eecs.berkeley.edu)

`riscv-mini` is a simple RISC-V 3-stage pipeline written in Chisel. It has been a crucial example in various project developments,
including [Chisel3](https://github.com/ucb-bar/chisel3.git), [FIRRTL](https://github.com/ucb-bar/firrtl.git),
[Strober](https://bar.eecs.berkeley.edu/projects/strober.html), simulation and verification methodologies.
It implements RV32I of the User-level ISA Version 2.0 and the Machine-level ISA of the Privileged Architecture Version 1.7.
Unlike other simple pipelines, it also contains simple instruction and data caches.

Note that a real-world processor is not the goal of `riscv-mini`.
It is developed as an intermediate example before diving into [rocket-chip](https://github.com/freechipsproject/rocket-chip). 

## Datapath Diagram
![pipeline](diagram.png)

## Getting Started

    $ git clone https://github.com/ucb-bar/riscv-mini.git
    $ cd riscv-mini
    $ make            # generate firrtl & verilog files in generated-src
    
The verilog output file can be used for verilator simulation or the ASIC tool flow.
    
## Running Verilator Simulation

First, generate the verilator binary:

    $ make verilator
    
This will generate `VTile` in the top-level directory.

Now, you can run verilator simulation for a given hex file as follows:

    $ ./VTile <hex file> [<vcd file> 2> <log file>]
    
`<vcd file>` and the pipe to `<log file>` are optional. The waveform is dumped to `dump.vcd` and the execution trace is printed in the screen by default.

The following command runs the whole test hex files in verilator and dumps the traces and the waveforms to the 'outputs' directory:

    $ make run-tests

## Unit and Integration Tests with `sbt`

`riscv-mini` provides synthesizable unit & integration tests.
There are six sets of unit tests(`ALUTests`, `BrCondTests`, `ImmGenTests`, `CSRTests`, `CacheTests`, `DatapathTests`),
running user-defined test vectors.
To execute them, first launch sbt with `make sbt` and run:

    > testOnly mini.[testname]
  
There are also six sets of integration tests, running the hex files from [riscv-tests](https://github.com/riscv/riscv-tests).
To execute them, also launch `sbt` and run:

    > testOnly mini.[Core|Tile][Simple|ISA|Bmark]Tests
    
`Core` only contains the datapath and the control unit, while `Tile` also contains I$ and D$. `Simple` only runs `rv32ui-p-simple`,
`ISA` runs the whole ISA tests, and `Bmark` runs five benchmarks(`median`, `multiply`, `qsort`, `towers`, `vvadd`). 
Note that all tests in a set run in parallel.

Finally, to run all the tests, just in sbt:

    > test
    
## Running Your Own Program on `riscv-mini`

At this point, you may want to implement and execute your custom application on `riscv-mini`. In this case, you need to install RISC-V tools for priv 1.7. This repo provides a script to install the correct version of tools. Run the script as follows:

    $ export RISCV=<path to riscv tools for priv 1.7>
    $ ./build-riscv-tools.sh
    
It takes a while to install the toolchain, so please be patient.

This repo also provides a template for your own program in `custom-bmark`. Add your c or assembly code and edit `Makefile`. Next, to compile you program, run `make` in `custom-bmark` to generate the binary, dump, and the hex files. Finally, run the following command in the base directory:

    $ make run-custom-bmark

## Standalone Proof Source Package

The complete proof is published at
[chenjie35335/riscv-mini-proof](https://github.com/chenjie35335/riscv-mini-proof).

The local `mini-proof/` package collects 1,183 `.v` files needed for all 45
original assertions: 1,158 model/proof sources and 25 FIRRTL, bit-vector, and
foundation library sources. Relative directories preserve Coq namespaces.
The entry point is
`mini-proof/formal/flat-low/staged-integration/AllOriginalAssertions.v`.
The package contains source files only. To validate the local package:

```bash
python3 formal/generators/verify-mini-proof.py --jobs 3
```

The verifier copies only package sources into a separate
`/tmp/riscv-mini-proof-check-*` directory, rebuilds all dependencies, checks the
combined theorem's assumptions, and runs recursive `coqchk` with VM conversion
checking enabled. Build products, logs, and `verification.json` remain in that
temporary directory; consult its report for the outcome of a particular run.

Library sources in `mini-proof/` are kept byte-for-byte identical to the original
`firrtl2coq/` libraries, including existing unproved declarations. Final theorem
dependencies are assessed with `Print Assumptions`. Experimental library
versions that proved or removed declarations are excluded from the delivery.
