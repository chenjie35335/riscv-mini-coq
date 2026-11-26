# 从处理器源码提取引理：先恢复局部规格，再接到展平模型

读取Chisel/Verilog、参数配置、decoder表和已有单元测试，主动发现能减少证明工作的局部等式、周期契约与不变式。不要仅在展平节点之间盲目搜索。

本项目已有与这种做法对应的证明实例：共享移位器的规格恢复、减法器实现分支比较、RF写回预览和旁路、流水级控制保持。下面记录的是本次核对源码与已有证明后的结构对应；不声称已自动从Scala生成证明，也不据此追溯每条历史引理最初如何发现。源码/hash和实际定理位置见 [对应记录](source-lemma-evidence.json)。

## 1. 从哪些源码信息入手

先确认实际elaboration配置。当前 `src/main/scala/mini/Config.scala` 的 `MiniConfig` 选择32位 `AluArea`、`BrCondArea`、`ImmGenWire`。同一个仓库同时存在Simple/Area、Wire/Mux实现；不能读了未实例化的实现就把其表达式当成当前DUT。

| 源码信息 | 首选提取内容 | 给后续证明节省的工作 |
|---|---|---|
| `RegInit`、`RegNext`、`when/elsewhen` | 每个字段的reset、保持、更新与优先级 | 避免每周期重展开寄存器写入逻辑 |
| `Mux`、`MuxCase`、`MuxLookup` | 有优先级的选择等式与选中分支条件 | 一次获得控制路径契约，供多个指令族调用 |
| RF端口、写使能、旁路与输出wire | 任意索引读写、zero可见值、preview和forwarding | 用一个bank/effect定理覆盖全部寄存器assert |
| ALU共享数据通路、位反转、借位/符号位 | 实现表达式等价于简洁数值规格 | 将几十级组合节点归约为一个数学引理 |
| slice、Cat、cast、扩展、移位 | 位宽、端序、符号、截断与立即数构造 | 直接连接共同参考的bitvector函数 |
| decoder表和控制常量 | instruction→控制族/effect的对应 | 共享family证明；区分coverage与执行正确性 |
| valid、kill、exception及级间寄存器 | 指令/PC/pending result的phase关系 | 为联合不变式选择必要字段和历史信息 |
| memory请求/响应及mask | 地址、offset、数据选择和提交阶段 | 复用共同参考load/store数学，仅证DUT接口 |

单元测试用于发现边界、操作码含义和反例，不代替全称证明。注释可以提示设计意图，真实赋值和配置决定应证明什么。

## 2. 将源码规律分成三种引理

**组合等式**：例如共享移位器等价于SLL/SRL/SRA，或分支符号位网络等价于有符号/无符号比较。优先把它提成与nodeID无关的数学引理；固定参考已有相同结论时直接调用。

**单周期契约**：例如字段在stall时保持、在允许推进时取前一级值。由实际展平节点/寄存器语义证明，然后由cycle wrapper隐藏内部求值迭代。

**可达不变式**：例如pending ALU等于对应指令的参考结果、RF与参考bank相等、PC按phase对齐。需要初始条件与保持性；源码里“设计上应该相等”只能形成候选，不能作为证明前提悄悄引入。

## 3. 现成尝试与可复用结论

### A. 位反转复用右移器 → 移位规格

`Alu.scala` 的 `AluArea` 用 `Reverse(A)` 选择输入，构造带符号位的右移，再对左移路径反转结果。`B(4,0)` 决定shamt。

由此恢复的局部规格是：SLL为低32位左移，SRL为零扩展右移，SRA为符号扩展右移；shamt取低5位。已收集的 `RFShiftArithmetic.rf_shift_at_correct` 和 `rf_shift_word_correct` 正是这类“实现函数→规格函数”的已证明引理。

源证明链还包含 `RFShiftCenter.rf_shift_center_history`、`RFShiftALUHistory`：先把展平实际节点推导为实现函数，再用数学等价改写为规格。新DUT复用这种移位结构时只需证明其控制/输入/输出对应该实现函数，不要重证位反转数学。32位条件不能直接用于64位新配置。

### B. 减法与符号位网络 → 分支比较

`BrCond.scala` 的 `BrCondArea` 先计算 `diff = rs1 - rs2`，以两操作数符号位是否相同选择diff符号位或某个操作数符号位；零检测决定EQ/NE。

现有 `DUTBranchArithmetic.dut_unsigned_compare` / `dut_signed_compare` 将这种网络连接到 `N.ltb` / `Z.ltb`；`dut_branch_difference_subB` 处理生成语义中33位运算后截断到32位的表达式；`dut_branch_numeric` 汇总各branch kind。

这里“看到同号取差值符号位”的源码规律用于选定正确的数学引理。最终仍由实际node equations证明展平网络产生该函数，继而复用共同参考的比较语义。

### C. RF源码 → bank更新、zero与preview

`RegFile.scala` 同时包含存储 `regs` 和用于checker的 `resultRegWire`：后者先取旧bank、将索引0置零，再在写使能且目的非零时覆盖写入目的。读口也显式将地址0读成零。

可提取三个不同接口：存储提交后的bank、当前组合读口、供checker使用的写后preview。已有 `RFReadPorts.rf_actual_read_port_history`、`rf_actual_forwarding_observed`、`CycleRFOriginalAssertions.cycle_rf_original_assertion_normal` 分别封装读口/旁路和preview到原assert的桥；共用 `RFWriteEffect`。

不要仅由输出强制为零就推断物理 `regs(0)=0`：这还取决于初始化定义。源码中同名“RF”信号可能代表不同阶段和不同zero处理，应在ViewAt中绑定实际被检查的对象。

### D. Datapath源码 → 控制与流水级转移

`Datapath.scala` 的 `stall` 由两路cache响应valid决定。`fe_reg` 在 `!stall` 时更新。写回级控制字段在 `reset || (!stall && expt)` 分支清除，在 `!stall && !expt` 分支更新。该清除分支并未给所有payload字段赋零，不能泛化成“异常时整级寄存器全部清零”。

已有 `CommitPCControlledPropagation.commit_pc_controlled_after_four` 将真实展平求值归约为flush/advance选择；`InstructionNormalTransfer.instruction_transfer_after_two` 封装instruction选择网络；上层周期/联合不变式调用这些契约。

`next_pc` 的 `MuxCase` 将stall放在异常和跳转之前，因此提取PC候选等式时必须保留优先级；寄存器reset又属于提交层，不能仅凭组合next_pc式推出reset时PC保持。

旁路源码只有满足 `WB_ALU`、写使能、非零源地址及目的匹配时才直接选择 `ew_reg.alu`。不能把它扩成“任何writeback类型都直接旁路ALU值”。`RFAddPendingInvariant.cycle_add_pending_forwarded` 展示了如何将实际旁路与应用pending effect后的参考bank相连。

## 4. 从源码追踪到实际证明的操作流程

1. 围绕当前assert或缺失的Joint分量阅读最小模块；记录实际配置、读写端口、控制优先级、位宽/符号、时钟相位和候选等式。
2. 查共同参考和现有数学库，优先复用规格、effect、compare、extension、shift等引理；把新工作缩小到DUT实现与这些函数的对应。
3. 通过层级名、端口、FIRRTL source info及AST结构定位展平cone。本仓库的 `CoreSoc.lo.fir` 保留 `@[src/main/scala/mini/... 行:列]` 信息，可作导航；优化、复制和别名使该映射可能多对多，注解本身不是语义等价证书。
4. 在生成Coq AST上核对真实表达式、位置、width和register/memory属性；检查后续写者及间接alias。已有 `generate-rf-shift-center.py` 等生成器采用依赖和表达式事实构造Coq证明，生成结果仍需核内检查；先核对脚本路径/输入，别在旧仓库直接运行后覆盖文件。
5. 用共享typed-node/frame/history引理证明实际节点产生实现函数；再调用源码启发的数学引理；最后包装为周期契约或Joint的base/step分量。
6. 接回原checker并记录编译、Assumptions和kernel结果。若卡在定位、类型或history窗口，把它明确列为adapter义务，不把候选写成admitted定理。

没有经过验证的Chisel→FIRRTL正确性桥时，不能仅在自写的Scala简化模型上证明，再宣称完成了原展平模型。此流程利用源码找出更好的证明分解，实际目标仍是用户指定的flat-low语义。

## 5. Agent如何参与

复杂DUT可增加 `source_analysis` 角色：只负责配置、源码切片、候选引理和对应cone/已有lemma清单；交付 [任务模板](../assets/source-lemma-task.json)。DUT contracts agent负责展平模型上的节点/周期证明；Reference agent负责寻找共同参考结论；Integration负责可达性和原assert。槽位有限时让DUT contracts角色同时做源码分析即可。

候选记录至少区分 `candidate`、`mathematical-core-proved`、`flat-local-proved`、`cycle-proved`、`integrated`；各级记录实际证据。现有数学引理闭合不代表新DUT的接线已经证明。
