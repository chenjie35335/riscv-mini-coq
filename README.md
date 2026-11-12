# riscv-mini

## FIRRTL → Coq

`firrtl2coq/` 是工具子模块，来源于 https://github.com/wky17/firrtl2coq，
固定版本为 `482f062d9ea4b6638c2e1bf8327632694b44db66`。

`formal/CoreSoc.hi.fir` 从当前 Scala 源码重新生成，使用与现有形式化测试
相同的 `CoreSoc(new Core(MiniConfig().core))` 顶层，包含 RVFI、参考模型、
检查器和指令/数据存储器。这里不是含 I$/D$ 的 `Tile` 顶层。
`formal/CoreSoc.v` 为该 FIRRTL 经工具转换得到的 Coq 表示。
此版本仅发布这两个文件，编译验证的临时文件会自动清理。

本次产物包含 12 个模块、2 个存储器、45 条断言和 1 条假设，已通过
Coq 8.16.0 编译检查。源码基线为 `dac51f0b4c2d02ac0ec235ddcd10bd5738b15f6e`，
参考模型子模块版本为 `2525d297a84e68f1c956478276e16b7a77e8b789`。

依赖：Java 17、Mill 0.10.0-M4、Coq 8.16.0、MathComp ssreflect/algebra 1.15.0、
OCaml 4.14.2、dune（至少 3.16）。例如使用独立 opam switch：

```bash
opam switch create firrtl2coq ocaml-base-compiler.4.14.2
opam repository add coq-released https://coq.inria.fr/opam/released --switch=firrtl2coq
opam install --switch=firrtl2coq coq.8.16.0 coq-mathcomp-ssreflect.1.15.0 coq-mathcomp-algebra.1.15.0 dune
opam exec --switch=firrtl2coq -- make coq
```

依赖已在当前环境中可用时，在项目根目录运行：

```bash
make coq
# 可选：指定 firrtl2coq 的 Coq 依赖库构建并行度（默认 4）
make coq JOBS=8
```

`coq` 是伪目标，每次执行都会调用 `scripts/generate-coq.sh`，从当前
Scala 源码重新生成。默认的 `make` / `make compile` 仍用于生成 Verilog。
成功后得到 `formal/CoreSoc.hi.fir` 和 `formal/CoreSoc.v`；命令失败时
不会更新这两个输出文件。

脚本初始化子模块、生成已解析连线及宽度的 high FIRRTL、构建工具和 Coq
依赖库，转换后用 `coqc` 检查，成功后更新 `formal/`。它保留原有 Scala
源码；工具的构建缓存留在子模块的忽略目录中，不纳入版本管理。

注意：转换不等于完成处理器正确性证明。工具将 `assert` 输出为带
`Admitted` 的待证明引理，将 `assume` 输出为前提，并忽略 `printf`。

## MLIR → Coq 状态机版本

根据 [`fir2coq.md`](fir2coq.md) 实现的另一个转换器位于 `mlir-to-coq/`。
它使用 CIRCT 解析、验证 FIRRTL dialect 的 MLIR，生成可执行的 Coq
状态机：`Inputs`、`State`、`Outputs`、`eval`、`outputs`、`step` 和 `trace`。
核心类型为 `eval : Inputs -> State -> Outputs * State`。
原有 `make coq` 使用 `firrtl2coq`；此版本使用 `make coq-mlir`。

依赖：Java 17、Mill 0.10.0-M4、C++17 编译器、CMake ≥ 3.20、Ninja、
Python 3（测试使用）、Coq（已验证 8.16.0），以及包含头文件、库、`firtool`
和 `circt-opt` 的 **CIRCT SDK firtool-1.62.0**。仅下载 `firtool` 可执行文件不够。
SDK 可从 [CIRCT 发布页](https://github.com/llvm/circt/releases/tag/firtool-1.62.0)
获取。`Semantics.v` 只依赖 Coq 标准库，不需要 MathComp 或 OCaml/dune。

在项目根目录运行：

```bash
export CIRCT_ROOT=/path/to/firtool-1.62.0
make coq-mlir
# 如果 Coq 安装在前述 opam switch 中：
opam exec --switch=firrtl2coq -- make coq-mlir
```

命令从当前 Scala 源码生成 `CoreSoc` FIRRTL，依次进行 CHIRRTL 降低、位宽和
复位推断、聚合类型展开、模块内联及条件连接展开，再导出 Coq。
`Semantics.v` 和生成模型均通过 `coqc` 后，才发布到独立的 `formal/mlir/`：

| 文件 | 用途 |
| --- | --- |
| `CoreSoc.mlir` | 规范化后的 FIRRTL dialect MLIR |
| `CoreSoc.v` | 当前 CoreSoc 的状态机模型 |
| `Semantics.v` | 位宽、有符号整数、事件及轨迹基础语义 |

构建缓存位于 `out/coq-mlir/`。`JOBS=4` 可调整 C++ 构建并行度。
脚本默认启用 `--named-nodes`，将中间表达式生成为独立 `Definition`，方便
检查大型电路；`make coq-mlir COQ_NAMED_NODES=0` 改为 `eval_with_events` 内的局部 `let`。
已有 `CoreSoc.fir` 时，也可以运行：

```bash
bash scripts/generate-coq-mlir.sh /path/to/CoreSoc.fir
```

单独构建转换器、运行测试或转换其他已经规范化的 MLIR 模块：

```bash
make coq-mlir-tool
make test-coq-mlir
out/coq-mlir/firrtl-to-coq input.mlir Module output.v --named-nodes
# 也可省略 --named-nodes。将 Semantics.v 放在输出旁，再编译：
cp mlir-to-coq/Semantics.v /path/to/output-directory/
cd /path/to/output-directory
coqc Semantics.v
coqc output.v
```

模型的数值字段为 `Z`，读取输入/状态及计算结果时通过 `bv` 限定位宽；
有符号运算通过 `signed` 解释补码。每次 `step` 表示同一个时钟的一个上升沿，
时钟不作为数值输入；`outputs` 观察该沿之前的当前状态，`trace inputs initial n`
返回经过 n 次状态转换后的状态。初始状态由调用者提供，同步复位由 `step` 处理。

支持单时钟、已知位宽的 UInt/SInt、同步复位，以及深度为 2 的幂且不超过
1024 的存储器（最多一个写端口、读延迟 0、写延迟 1、单比特 mask）。
存储单元展开为独立状态字段；无写端口的存储器保持其初始内容。
层次实例、聚合类型和条件连接需预先展开；异步复位、派生时钟、多驱动和
未实现的操作会报错。未定义数据、除零结果、关闭读使能时的读结果分别由
`undef_*`、`divzero_*`、`memundef_*` 额外输入表示，而非固定为零。

`assert`、`assume`、`cover`、`printf` 保留为 `events` 中的观察事件，包含
使能、谓词、消息字节和打印参数；`assertions` / `assumptions` 给出对应命题。
轨迹不会自动过滤不满足假设的输入，也不会自动证明断言；生成代码不引入
`Axiom` 或 `Admitted`。测试通过 Coq `vm_compute` 检查具体运算和状态转换，
并检查不支持的输入被拒绝；这不构成整个转换器语义保持或处理器正确性的证明。

## 修改说明
关于接入最新参考模型的修改版本
```bash
# Compile to generate transition system for formal verification
# for btor2 format
mill chiselModule.test.testOnly formal.RISCVMiniFormalSpecBtor
# for SystemVerilog format (to Symbiyosys)
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
Theres are six sets of unit tests(`ALUTests`, `BrCondTests`, `ImmGenTests`, `CSRTests`, `CacheTests`, `DatapathTests`),
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

At this point, you may want to implement and exeucte your custom application on `riscv-mini`. In this case, you need to install RISC-V tools for priv 1.7. This repo provides a script to install the correct version of tools. Run the script as follows:

    $ export RISCV=<path to riscv tools for priv 1.7>
    $ ./build-riscv-tools
    
It takes a while to install the toolchain, so please be patient.

This repo also provides a template for your own program in `custom-bmark`. Add your c or assembly code and edit `Makefile`. Next, to compile you program, run `make` in `custom-bmark` to generate the binary, dump, and the hex files. Finally, run the following command in the base directory:

    $ make run-custom-bmark
