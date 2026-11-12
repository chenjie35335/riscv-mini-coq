# firrtl2coq 修改总结

整理日期：2026-11-12。后续已补充参数化内存初值、常量位序修复和通用 invalid 来源选择语义，见第 14–16 节；第 12 节记录的是这些实现之前的问题定位。

这些修改围绕同一个问题展开：让 riscv-mini 的 CoreSoc 在 Coq 中能够正确地传递信号、执行内存访问、跨周期更新状态，并生成有实际意义的断言证明义务。此前出现的 `None`、reset 始终未知和正周期断言空真，来自不同层次的问题，需要分别处理。

## 1. 修改范围与版本基线

本文依据当前 Git 差异、实现代码和已有验证记录整理，区分两类变化：

- **版本更新**：主仓库索引记录的 firrtl2coq 子模块提交为 `482f062`；当前检出为 `58759b5`，提交说明为 `support multi-clock`。这是引入已有提交，不应把其中全部代码都算成本地新写的修改。
- **本地修改**：相对 `58759b5`，当前有 7 个文件存在未提交差异（5 个实现源文件、2 个测试或配置文件），共增加 780 行、删除 121 行。这是 Git 行数统计，包含重命名和结构调整。

| 文件 | 本地修改的主要内容 |
|---|---|
| [Semantics_with_implicit_widths.v](firrtl2coq/src/Semantics_with_implicit_widths.v) | `validif` 未知值传播、单比特布尔运算、寄存器提交与 reset 优先级、父子实例端口同步、配套类型正确性证明 |
| [Semantics_with_memory.v](firrtl2coq/src/Semantics_with_memory.v) | 内存与普通 bundle 的访问分派、端口字段和存储布局、读写及未知控制处理、`Smem` 类型分析适配，并接入寄存器和端口同步逻辑 |
| [coqgen.ml](firrtl2coq/src/ocaml/lib/coqgen.ml) | 输出内存 `storage_id`、带初始内存和 invalid 来源选择参数的运行接口、量化这些参数与任意周期数的断言模板 |
| [transhiast_without_inline.ml](firrtl2coq/src/ocaml/lib/transhiast_without_inline.ml) | 分配内存私有存储编号、传递 `storage_id`、修正 assert/assume 参数顺序、保留 `when` 分支条件 |
| [transhiast.ml](firrtl2coq/src/ocaml/lib/transhiast.ml) | 将整数常量转换为 NBits 所需的最低位在前位列表 |
| [test/dune](firrtl2coq/src/ocaml/test/dune)、[test_ocaml.ml](firrtl2coq/src/ocaml/test/test_ocaml.ml) | 加入并运行常量位序、补码和截断回归 |

实际 Dune 库使用的是 `src/ocaml/lib/` 中的文件。`src/ocaml/` 根目录也存在同名文件，版本更新中已有部分相近修改；本次把所需改动落实到了实际参与构建的 `lib/` 版本。

版本更新还带来了 `hfmem.storage_id`、复位初始状态和跨周期运行等基础设施。下面会注明哪些是在此基础上接入、修复，而非本地从零新增。

## 2. 给迭代次数的类型分析补上 Smem 支持

**原问题**：带内存的电路直接调用原来的 `circuit_iter_count`，其类型分析没有正确处理 `Smem`。即使后续存在内存求值逻辑，计算组合迭代次数这一步也可能先返回 `None`。

**修改**：在内存语义文件中增加：

- `memory_type_view`：仅在类型分析视图中，把 `Smem` 映射成具有内存端口 bundle 类型的 `Swire`，并递归处理条件分支。
- `memory_module_type_view`：对模块应用上述转换。
- `circuit_iter_count_with_memory`：在该视图上复用原有迭代次数计算。
- `circuit_value_with_memory` 改用新的计数入口。

**原因**：类型分析需要知道内存端口的结构，但不需要把真正的内存执行改成普通 wire。单独提供分析视图，可以复用既有分析逻辑，同时保留运行时的存储语义。

当前 CoreSoc 算出的结果是 `Some 1865`，表示每个电路周期使用的组合求值轮数，不是只允许运行 1865 个周期，也不是内存容量。

## 3. 修正内存端口的字段编号

**原问题**：初始化内存端口 bundle 时，曾用端口自身的 `id` 充当 `data` 字段编号。端口编号属于外层内存 bundle，数据字段编号属于端口内部，两者不是同一层级。

**修改**：增加 `memory_data_field := N.of_nat 4`，与翻译器的字段布局一致：

| 字段 | 端口内部编号 |
|---|---:|
| `addr` | 0 |
| `en` | 1 |
| `clk` | 2 |
| `mask` | 3 |
| `data` | 4 |

`memory_port_initial_value` 使用固定的数据字段编号，避免 `mem.port.data` 查不到字段或与其他字段冲突。

## 4. 避免把普通 bundle 字段误判成内存访问

**原问题**：旧代码看到形如 `Esubfield (Esubfield (Eid x) p) f` 的引用，就尝试按内存端口处理。但普通接口也会出现同样的语法形状，例如 `io.xxx.valid`。结果是普通信号被送入内存查询，找不到内存布局后返回 `None`。

**修改**：增加 `is_memory_data_port`。只有同时满足以下条件，才使用专门的内存数据读写逻辑：

1. 基对象在 `memory_map` 中确实是一块内存。
2. 端口属于相应的 reader 或 writer 列表。
3. 最内层字段是 `data`，即编号 4。

其余引用通过 `read_bundle_field` 或 `unidirectional_connect_bundle` 执行普通字段访问。`addr`、`en`、`clk`、`mask` 等控制字段也按 bundle 字段读写。

**原因**：访问类别应由内存布局确定，不能只根据引用长得像不像内存端口来判断。已经识别为真实内存访问后发生的错误仍返回 `None`，不会再退回普通字段访问而掩盖错误。

## 5. 分离内存端口与实际存储数组，修正读写行为

### 5.1 使用两份独立状态

**原问题**：内存的可见名称用于保存端口 bundle，但部分求值逻辑又把同一个名称下的值当成 `Aval` 存储数组读取，布局不一致。

**修改**：

```text
mem 标识符          → 端口 bundle
mem 的 storage_id   → 实际存储数组
```

翻译器为 `mem._memory_storage` 分配私有编号，并把它写入 `hfmem.storage_id`；代码生成器也输出这个构造参数。运行时通过 `ml_storage_id` 访问数组。

`storage_id` 字段和部分初始化支持由版本更新引入，本地修改把实际编译的翻译器、生成器及读写路径接通。普通 FIRRTL 引用仍指向可见端口，不会被改写成私有数组引用。

### 5.2 按层级读取端口控制字段

原先部分代码直接执行 `VM.find (addr mp)`，把端口内部字段编号当成模块顶层变量编号。

现在使用 `read_memory_port_field`，按 `mem → port → field` 三层读取地址、使能和掩码。

### 5.3 修正读端口和写提交

- 读端口不再依赖写掩码。读使能为 0 时返回有意无效值；使能为 1 时按地址读取存储。
- 读操作观察 `sem_old` 中的存储；写操作在 `sem_new` 的累积存储上更新，避免后一次写入直接覆盖前一次更新的整个数组。
- 组合迭代阶段只计算写端口的数据；`set_regs=true` 时才提交数组写入。
- 实际写入经过 `adapt_hvalue_as_type` 适配后的值。
- 写入保留可见端口 bundle，只更新私有数组。
- 即使写数据右侧是 `Eref`，真实 writer 的 `data` 连接也会进入写提交路径，不再被普通双向连接路径绕过。

### 5.4 保守传播未知控制

新增 `memory_gate`、`classify_memory_gate`、`memory_write_gate`、`write_memory_address` 等辅助定义。

| 情况 | 当前处理 |
|---|---|
| 明确禁用写入，或写掩码为 0 | 保留数组 |
| 写控制未知、地址已知 | 将可能受影响的单元标为未知 |
| 可能发生写入且地址未知 | 将所有可能受影响的单元保守地标为未知 |
| 读使能或地址尚未确定 | 返回带正确元素类型的未知值 |
| 必需字段缺失、类型错误、已知地址越界等 | 保留求值失败 `None` |

**原因**：不能把“可能发生写入”直接当成“没有写入”，也不能为了继续运行而把未知内存填成 0。这些修改是当前抽象求值器的读写和未知值处理修复，不代表已经完整验证所有 FIRRTL 内存延迟及读写冲突语义。

## 6. 让 validif 的未知条件继续传播，而非直接失败

**原问题**：`validif(cond, value)` 的条件在组合迭代中暂时未知时，旧求值器直接返回 `None`。这会中止整个电路求值，而实际条件可能在后续轮次才稳定。

**修改**：普通求值器和内存求值器采用相同处理：

- 条件为 `Needtobedefined` 或 `Uninitialized`：返回 `Some (Needtobedefined value_type)`。
- 条件为 `Undefinedonpurpose`：返回相应结果类型的有意无效值。
- 已知真、假条件保持原有分支行为。
- 条件求值失败、类型不支持、无法确定所需结果类型等情况仍返回 `None`。

返回值使用的是 `value` 的类型，不是条件的单比特类型。因此输出可以正确保留为 UInt、Clock 等不同类型。

**原因**：区分“本轮尚不知道结果”与“表达式不能按当前语义求值”。

## 7. 在父子实例之间同步端口，修复 reset 始终未知

**原问题**：实例接口在状态中有两份表示：父模块里的实例 bundle，以及子模块环境中的各个端口。旧代码逐模块执行语句，却没有在这两份表示之间传递信号。父模块已经驱动 reset，子模块仍可能一直保存 `Needtobedefined`。

**修改**：新增 `sync_instance_ports` 和 `sync_circuit_ports`，在每轮各模块局部求值之后同步接口。普通和内存电路求值器都调用它们。

- 普通输入方向从父实例接口传入子模块，输出方向从子模块传回父模块。
- 复用 `replace_writeable` 处理 bundle 内部的 `flip` 和数组元素方向。
- 所有源值来自同一份快照，目标更新累积到当前状态，避免兄弟实例互相覆盖。
- 顶层输入仍由外部输入提供。
- 不复制寄存器或私有内存数组。
- 缺失端口、缺失实例状态及类型不匹配仍返回 `None`。

**效果**：完整 CoreSoc 中，reset 能沿 `top → dut → dpath → checker → specCore` 传播。两周期验证中，输入 reset 从 1 变成 0，checker 的 reset 正确跟随，第一条断言的使能从 0 变成 1。

这也使依赖“checker 的使能永远未知”的旧空真证明失效。

## 8. 分开组合求值和寄存器提交，并落实 reset 优先级

**原问题**：仅在遇到 `Sreg` 声明时恢复旧值并不够，后面的连接语句仍可能覆盖寄存器。这样，一次电路周期内多轮组合迭代就可能错误地推进寄存器状态。另外，周期末的更新没有正确落实寄存器声明中的 reset 优先级。

**修改**：

- 原递归语句执行器改名为 `value_iter_statements`；内存版本相应改名。
- 外层 `value_iter` / `value_iter_with_memory` 在完整语句序列执行后调用 `finish_registers`。
- `set_regs=false`：恢复已声明寄存器的旧值，组合迭代不推进寄存器。
- `set_regs=true`：通过 `register_next_value` 确定提交值。
- reset 有效时，使用声明的复位值；reset 无效时，使用候选下一状态。
- reset 未知或有意无效时传播相应状态，不擅自当成未复位。
- reset 条件和复位表达式读取稳定的旧环境，使多个寄存器同时更新。
- 遍历嵌套 `Swhen` 中的寄存器声明。

**原因**：组合求值轮次只用于传播信号，不能等同于硬件时钟周期。寄存器应在一次周期提交时统一更新，复位应对该更新具有优先级。

现有 `circuit_reset_state`、`reset_registers` 和 `reset_zero` 属于版本更新已有的初始化机制。本地修改还修正了每个后续周期提交时的 reset 行为，两者不能混为一谈。

## 9. 对单比特布尔运算保留可确定的结果

**原问题**：原二元运算求值器过于保守，只要有未知操作数，就可能把本可确定的结果也变成未知，例如 `0 AND x`、`1 OR x`。这会进一步污染断言使能、异常信号和 assume 条件。

**修改**：

- 原实现保留为 `eval_binop_basic`。
- 新增 `exact_bit`、`absorbing_bit`、`refine_boolean_result`。
- 新的 `eval_binop` 在原结果上应用单比特吸收律：`0 AND x = 0`、`1 OR x = 1`，支持两侧操作数的对称情形。
- 只在两边都是 `UInt<1>`，且原结果已经是合法类型的未知值时细化结果。
- 保留原有已知结果和错误 `None`；没有把这条规则泛化到任意宽度、符号数或其他运算。

新增 `refine_boolean_result_type_correct`，并更新原来的表达式类型正确性证明。另有 Coq 引理对未知单比特的所有布尔具体化证明 AND/OR 处理正确。

**原因**：提高抽象求值的精度，同时保持错误检测和类型约束。

## 10. 修正断言提取，并生成任意周期的证明义务

### 10.1 修正 assert/assume 的参数顺序

解析得到的结构是 `Sassert(clock, property, enable, name)`，`Sassume` 同理。实际编译的翻译器此前把 property 和 enable 的角色取反。

修改 `collect_verification`，按正确顺序保存待证明谓词和使能表达式，避免生成错误的“使能成立则性质成立”命题。

### 10.2 保留 when 的路径条件

`collect_verification` 增加 `guards` 参数，遍历 `when` 时累积条件：

```text
then 分支的实际使能 = 外层条件 ∧ cond  ∧ 原 enable
else 分支的实际使能 = 外层条件 ∧ ¬cond ∧ 原 enable
```

**原因**：分支里的断言和假设应在该分支有效时才生效，不能丢掉控制条件后无条件提取。

### 10.3 从单周期接口扩展到任意周期数

生成器新增 `generated_run inputs k`，调用已有的 `circuit_run_from_reset`；原单周期 `generated_circuit_value` 仍保留。

原断言模板只针对一次 `generated_circuit_value` 的结果；现在改为：

```coq
forall inputs (k : nat) states,
  generated_run inputs k = Some states ->
  generated_all_assumptions states ->
  generated_assert_..._all states.
```

**原因**：将证明义务扩展到任意有限周期数，而不是只描述一次求值。

这里有三个需要准确理解的边界：

1. “任意周期”是量化 `k : nat`，没有把每周期的 1865 轮组合迭代改成无限循环。
2. `k=0` 返回构造出的复位初态；运行 `k` 步消费 `inputs 0` 到 `inputs (k-1)`。reset 脉冲由输入序列提供，`generated_run` 没有把该波形硬编码进去。
3. 现有初始化辅助函数会对 `NRst` 寄存器采用 `reset_zero` 约定；这不等同于一般硬件中所有无复位寄存器天然为 0。内存内容仍可保持未初始化。

生成器仍输出带 `Admitted` 的证明模板。生成了任意周期命题，不等于已经证明这些命题。

## 11. 已有验证及其范围

以下是已有源码、编译产物和日志记录的验证结果；本次 Markdown 整理没有重新执行全部长时间回归。

| 验证目录 | 主要覆盖内容 |
|---|---|
| [field_dispatch_tests](formal/field_dispatch_tests/README.txt) | 14 项字段分派回归，以及实际 CoreSoc 表达式访问检查 |
| [validif_tests](formal/validif_tests/README.txt) | 12 项计算回归、2 条一般传播引理，以及 CoreSoc 相关节点检查 |
| [memory_layout_tests](formal/memory_layout_tests/README.txt) | 32 项内存回归、3 项电路检查及完整周期运行记录 |
| [hierarchy_tests](formal/hierarchy_tests/README.txt) | 15 项层次连接回归，多级 reset 与断言使能传播检查 |
| [register_timing_tests](formal/register_timing_tests/README.txt) | 20 项寄存器保持、提交、复位优先级和同时更新回归 |
| [boolean_refinement_tests](formal/boolean_refinement_tests/BooleanRefinementTests.v) | 17 项布尔细化和错误路径回归 |
| [assertion_proofs_hierarchy](formal/assertion_proofs_hierarchy/README.txt) | 45 条检查器等价性、45 条初始周期基础情形、一般寄存器保持引理、布尔运算正确性及审计执行等价性等 |

语义库、Dune 工具和原始 `CoreSoc.v` 已有重新构建成功的记录。当前语义下还执行了完整六周期审计，每周期使用全部 1865 轮组合迭代及最后一次提交；具体状态检查见 [progress.json](formal/assertion_proofs_hierarchy/progress.json)。

这些结果分别属于小模型证明、给定轨迹运行检查或辅助引理，不能合并宣称为“45 条任意周期断言均已证明”。历史语义下依赖求值失败、使能未知的旧证明也不能直接沿用。

证明依赖方面：新增相关引理的假设审计仍出现原库的 `ftype_eqn_eq`、`ffield_eqn_eq`；所检查的新增引理未引入新的公理，但不能据此称整个工具库无公理。版本更新中的 `hfmem_eq_dec` 本身已有 `Admitted`，生成的 45 条断言模板也仍有 `Admitted`。

## 12. 当前仍未解决的问题，以及尚未实施的方案

当前求值器已经能够返回电路状态，但状态中的信号仍可能未知。需要区分：

```text
None                         → 求值失败
Some (Needtobedefined ...)    → 求值完成，但值尚不确定
Some (Uninitialized ...)      → 保存的是未初始化状态
```

已经定位的后续问题是：CoreSoc 的指令内存没有初始化程序，未初始化数据能够进入取指流水寄存器。在完整运行记录中：

```text
imem 未初始化
  → icache 数据未初始化
  → k=4 写入 fe_reg.inst
  → k=5 控制器译码未知，io.ctrl.st_type 和 store_width 未知
  → 未知写有效位进入寄存器
  → k=6 的 assert_3 比较“未知 == 0”
```

见 [store_width_trace.log](formal/assertion_proofs_hierarchy/store_width_trace.log) 和 [反例诊断说明](formal/assertion_proofs_hierarchy/COUNTEREXAMPLE_DIAGNOSTIC.txt)。完整运行在 `k=6` 出现“当前 assume 成立，但 assert_3 的谓词未知”；此前 `k=3`、`k=5` 的 assume 为假。

原命题目前只约束最终状态的 assume。尚未加入“所有历史周期都满足 assume”的前提，也尚未把初始内存改成可量化的 Coq 参数。此前讨论的加载具体程序、参数化初始内存、保留符号译码关系，均是后续方案，不是已经实现的修改。

候选状态的“assume 成立而 assert_3 不成立”已通过 Coq 检查，审计流程与 `generated_run` 的等价性也已有证明；候选状态的完整内核可达性认证仍缺失。因此，当前不能宣称已有完整的 Coq 反例定理，更不能宣称已完成全部 45 条任意周期证明。

## 13. 常用复查命令

在主仓库根目录查看当前修改：

```bash
git -C firrtl2coq diff --stat
git -C firrtl2coq diff
git -C firrtl2coq diff 482f062..58759b5
```

在已经配置好 Coq、MathComp、OCaml 和 Dune 的环境中，可按需运行对应回归：

```bash
bash formal/field_dispatch_tests/build.sh
bash formal/validif_tests/build.sh
bash formal/memory_layout_tests/build.sh
bash formal/hierarchy_tests/build.sh
bash formal/register_timing_tests/build.sh
bash formal/boolean_refinement_tests/build.sh
```

`make coq` 会重新生成并检查 CoreSoc 的 FIRRTL/Coq 源文件；只修改被引用的语义库时，已有 `CoreSoc.v` 通常只需重新编译。`formal/` 当前被主仓库 `.gitignore` 忽略，里面的测试和证明产物与 firrtl2coq 的 4 个源文件差异是分开保存的。

## 14. 后续实现：在复位初态中赋予内存任意值

根据最新要求，没有采用统一填零，而是把任意内存初值作为显式 Coq 参数。

- 新增 `memory_initialization`：按实例路径、内存编号和单元/叶子位置返回 `N`。
- 新增 `memory_initial_value` / `memory_initial_fields`，按照元素类型和位宽构造真实的 `Gval`、数组及 bundle。每个叶子保留参数给出的位模式，不生成未知值标记。
- `initialize_module_memories` 初始化模块内的全部内存声明，包括条件分支中的声明。
- 新增 `circuit_reset_state_with_memory_init` 和 `circuit_run_from_reset_with_memory_init`：构造初态时先填充内存，再处理寄存器复位；后续周期继承存储和写入结果。
- 生成接口改为 `generated_run memory_init inputs k`，并提供 `generated_initial_state`。45 条断言模板增加 `forall memory_init`。

任意值表示可量化的 Coq 参数，不代表随机抽样；参数尚未具体化时，译码等操作保留为需要证明分析的表达式。再次拉高普通 reset 输入不会重新选择内存内容。

已重新生成并编译 CoreSoc.v，新增 18 项 Coq 例子/引理通过，既有 67 项内存、寄存器、层次回归通过。此前未知内存模型的运行记录和证明义务与新接口不同，不能直接重用。历史 assume 前提未在本次修改，45 条一般性断言仍未证明。接口说明与复现命令见 [参数化内存初值说明](formal/memory_initialization_tests/README.md)。

## 15. 后续修复：FIRRTL 常量位序

继续证明时发现，`src/ocaml/lib/transhiast.ml` 的 `int_to_bool_list` 按最高位在前输出，但 Coq NBits 采用最低位在前。修复前 NOP 常量 19 被解释为 3355443200（0xC8000000），两位控制常量1与2也会互换。这影响整个译码过程。

现改为按位索引0到width-1生成列表，保留原有位宽截断及补码处理。`test/dune` 与 `test/test_ocaml.ml` 增加7825项数值回归；另有5条端到端Coq求值证明。CoreSoc已重新生成。详见 [常量位序回归](formal/literal_bit_order_tests/README.md)。

修复后，参数化内存下的NOP、ADDI、SW能够正确译码，前几个周期的内存断言成立。当前新障碍是共享寄存器文件初值来自DontCare：x1到x31被表示为invalid，提交时对应寄存器比较无法得到真。NOP的相关轨迹中历史assume全部成立，因此该问题也不能靠补充历史假设解决。是否参数化共享寄存器初值尚待明确，本次未改变RTL。最新证明与证据位于 [assertion_proofs_initialized](formal/assertion_proofs_initialized/README.md)。


## 16. 通用 DontCare / Sinvalid 来源参数化

本次用户要求一般性方案后，将处理放在 `Sinvalid` 的求值语义中，不再针对Datapath或某个寄存器编号替换AST。Chisel的DontCare生成FIRRTL的invalid语句；原来的Undefinedonpurpose标记不能表达一个来源经过复制后的关联性。

- `invalid_choices` 按周期、实例路径、静态语句路径、聚合叶子返回N位模式。同一周期内所有组合迭代和提交共用同一选择；不同周期允许变化。
- `value_iter_statements_with_memory_policy` 统一处理所有显式invalid来源。保留赋值覆盖、Bundle方向、动态下标和寄存器时序。未收敛、未初始化及None不会被自动填值。
- 新增 `circuit_*_with_choices` 运行入口。生成接口为 `generated_run memory_init choices inputs k`，45条模板增加全称量化choices。
- memory写端口data的invalid赋值也在提交阶段遵守enable/address/mask更新存储；此前只更新端口的问题一并修复。
- CoreSoc的模块AST、RTL、断言表达式和assume表达式没有改变。保守迭代上限仍为1865。

这是一项明确的Coq建模选择，不把Chisel的“不驱动”直接等同于固定随机常数，也不宣称覆盖所有编译器对未定义行为的实现。27项新Coq语义/端到端检查、既有85项回归通过；NOP/ADDI/SW在按周期变化的非零来源下，k=0到8的条件断言均成立。45条任意周期命题仍未证明。

实现、限制和复现命令见 [通用选择语义](formal/invalid_choice_tests/README.md)。此前的共享寄存器特例实验和blocked记录属于历史证据；本次要求已明确采用更一般的模型修正，不再等待是否仅参数化该寄存器文件的选择。


## 17. 按项目正式验证后端重做有限输入与约束语义

核对本项目的ChiselTest 0.6.0 / FIRRTL 1.6.0源码后，确认DontCare通过DefRandom被建模为有宽度的符号输入；assume在整个检查前缀逐步生效。ChiselVerify的CRV生成器与这一formal后端不是同一个组件。

新正式接口为 `generated_run memory_init inputs k`，其中 `inputs : nat -> formal_inputs` 同时提供普通端口和有限宽符号输入。`symbolic_word width`用依赖类型保证位数，保留同源共享和不同来源独立。原N值函数仅保留为适配器，入口为 `generated_run_with_choices`；适配器保持原求值的5条通用等价引理已通过Coq。

生成的45条模板现在要求 `generated_legal_trace memory_init inputs k`，检查每个已消费周期的assume，不再只检查末状态。结构初态0没有执行组合语句，故不作为采样周期。None不能作为合法轨迹；违反assume的输入可正常求值，但不满足证明前提。

上游真实转换探针、13项新输入/约束检查、5条适配器引理及2条轨迹引理已验证。CoreSoc重新生成并编译，模块AST和assert/assume表达式保持不变；变化是输入域和证明前提。45条任意周期证明仍未完成。当前工作区未保留上述测试目录，以上为历史验证记录，不能作为本次重新执行的结果。当前接口见 `firrtl2coq/src/Semantics_with_memory.v`，现有证明审计见 [证明目录](formal/assertion_proofs_formal_inputs/README.md)。

后续已将45个初态证明及局部/全局检查等价性迁移到当前接口，并证明合法逐步执行关系与原始运行及历史约束前提等价。新增任意符号输入下的寄存器保持、端口同步保持私有条目，以及固定点跳过的条件正确性引理。它们为跨周期证明提供构件，尚未证明DUT与参考模型的具体状态关系，也不计为45条任意周期断言的完成。详见 [当前接口的证明进展](formal/assertion_proofs_formal_inputs/README.md)。

复位范围需单独区分：上游formal默认要求首周期复位有效，但当前全称命题没有自动加入这一外部输入条件；现有结构化初始化规则也不等同于上游全部复位选项。已完成的DontCare/assume改动不能据此称为与完整formal后端等价。

进一步完成了实际求值器的时钟提交证明：`RegisterCommit.v` 将递归提交过程化为静态寄存器列表，并证明候选值/reset初值的选择；`CircuitCommit.v` 证明实例遍历及端口同步不会覆盖目标私有寄存器；`CoreCommit.v` 将其用于DUT寄存器数组和参考模型状态bundle；`CoreCycle.v` 将结果接到任意成功的后继周期及历史assume约束。它们沿用该周期同一份有限符号输入，没有新增随机选择、固定点或复位协议假设。这些证明建立了实际写回路径，仍需证明两侧候选状态的对应关系；45条任意周期断言仍未完成。

## 18. 保持语义的无符号比较优化与电路级寄存器不变量

继续证明时，`LUI x1,0x80000` 的求值在第5步耗时异常。定位发现 `eval_binop_basic` 中UInt的大小比较通过MathComp的 `nat_of_bin` 转成自然数；高位非零数据导致大量递归计算。现将四个关系比较分支改为直接使用 `N.ltb`/`N.leb`。

修改前的完整运算定义已保留；Coq证明了对任意运算符、任意两个hvalue，新旧整个 `eval_binop_basic` 的返回结果相同，且该等价定理没有公理依赖。没有改变输入域、断言或假设。相同LUI运行从旧版11分16秒仍未完成第5步，改善为约85.6秒完成7步检查；两版状态0…4结构一致。详见 [二进制比较](formal/binary_comparison_tests/README.md)。

另将寄存器保持证明提升到真实的整个电路遍历和层次端口同步，并由当前CoreSoc AST收集全部寄存器位置，证明它们在任意轮组合迭代中保持不变。下一步仍需证明时钟提交所计算的DUT与参考模型状态关系；这些构件不计入45条任意周期断言的完成数。

## 19. 将提交前状态连接到上一周期寄存器值

新增输入准备证明，覆盖局部声明、整个实例遍历和顶层端口更新。结构检查要求非寄存器声明不会覆盖目标寄存器编号，分别检查memory接口及私有存储编号；CoreSoc的全部59处寄存器声明均已通过检查。

同时证明了成功的正式运行始终包含实例表中的各个实例，覆盖任意内存初值、任意输入流和所有周期。因此，输入准备复制上一周期寄存器值时所需的实例存在条件，由原始运行前提直接推出，不需要用户增加假设。

`reachable_register_held_until_commit` 已将输入准备和任意多轮组合迭代串联起来，证明59处寄存器在提交前仍等于上一周期的值。`generated_run_successor_register_transition` 进一步将此关系与DUT及参考模型的实际提交过程合并，合法轨迹版本保留原始历史assume约束。这一阶段新增34条引理/定理；未修改求值器、生成模型、45条断言或其前提，未新增公理。

这一结果建立了实际跨周期寄存器流转关系，仍不是DUT与参考模型的功能等价证明。剩余工作包括两侧候选状态的对应、流水线提交时序和访存行为。最新核验记录见 [当前证明进展](formal/assertion_proofs_formal_inputs/README.md)。

## 20. x0数据路径的局部正确性

开始证明实际数据路径，首先核对x0比较所依赖的生成节点：DUT RegFile的78/79/114/178、参考RiscvTrans的5037，以及检查器的39。参考模块包含多个语句块，核对使用其完整AST，未仅检查第一个分块。

已证明DUT的x0组合计算对所有5位写地址、两种写使能和任意写入数据恒为0；任意局部状态满足对应节点方程时也得到相同结论。三轮传播引理使用上一轮读取语义，显式保留写地址稳定性、输入取值及每轮节点方程等前提。参考模型有效指令的x0输出为0；两侧值为0且比较节点一致时，检查器原始 `generated_assert_assert_8_all` 成立。

另外证明已知UInt节点作为双向连接的被动源时不被改写，用于后续将节点方程提升到完整模块迭代。这一阶段新增27条引理/定理，未改变模型和原始45条目标。局部引理的状态条件尚需从实际运行推出，因此任意周期断言完成数仍为0/45。

### DontCare 语义来源与当前核对

本次直接核对了项目对应的 [ChiselTest v0.6.0 UndefinedValuesTests](https://github.com/ucb-bar/chiseltest/blob/v0.6.0/src/test/scala/chiseltest/formal/UndefinedValuesTests.scala)：对二位 `DontCare`，分别断言它恒等于 0、1、2、3 都必须失败；关闭 undefined 建模才测试其取零。[Maltese 后端](https://github.com/ucb-bar/chiseltest/blob/v0.6.0/src/main/scala/chiseltest/formal/backends/Maltese.scala)默认启用 `InvalidToRandomPass`。这是 formal 非确定输入语义的直接依据，不能将 ChiselVerify 的 constrained-random 测试生成器与此混为一谈。

当前工作区已有下述实现，因此本次保留现有语义，并新增 `formal/DontCareSemanticsChecks.v`：证明每个符合位宽的向量都能成为符号输入、同一来源的读取对应同一个输入值、输入位宽受依赖类型约束。该文件已通过 `coqc`；存在性定理不依赖额外公理。源码审计也通过，但不表示 CoreSoc 的 45 条任意周期性质已获证明。

[Chisel 官方说明](https://www.chisel-lang.org/docs/explanations/unconnected-wires)指出 `DontCare` 生成 FIRRTL `is invalid`。[ChiselVerify 论文的 formal 流程](https://www.cs.princeton.edu/~ad4048/pdfs/verification-of-chisel-hardware-designs-with-chiselverify.pdf)包含 Invalid to Random 转换；这与 constrained-random testing 的抽样器不同。

这里将随机解释为非确定的有限位向量输入：宽度 w 的值范围为 0 到 2^w−1，不要求均匀分布。实例路径、静态 invalid 位置和聚合叶子标识来源；同周期求值和提交共享该来源，跨周期由输入序列重新指定。复制同一来源保留相等关系，不同来源允许独立取值。设计中的 assume 进一步约束整个已消费的轨迹；不把全部未知状态自动转成随机值，也不强制内存清零。

当前 `CoreSoc.v` 已使用 `formal_inputs` 和 `generated_legal_trace`。本次运行 `python3 formal/assertion_proofs_formal_inputs/check_sources.py` 通过；这只是源码及原命题一致性审计，不是45条任意周期断言的证明。
