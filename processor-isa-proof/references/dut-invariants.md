# DUT 结构与不变式：从相似结构提取候选，再证明契约

## 1. 将信号视图和正确性分开

可迁移的分层是：

```text
生成的原始执行关系
  → 节点/寄存器方程、可执行历史
  → ViewAt raw view + 每周期 ViewStep
  → InitInv / PreserveInv
  → 架构模拟与原始 checker
```

`ViewAt` 只说明观察状态中的哪些信号对应视图字段、值是否具体、位宽是多少。它可以绑定 DUT RF 和参考 RF，但不能在视图存在性的定义中预先要求两者相等，否则提取视图本身就暗含待证性质。

源例：`staged-integration/CycleView.v` 的 `cycle_view`、`cycle_view_at`、`cycle_transition`。其周期接口在两个 observation 之间隐藏真实 commit，保留执行成功和合法输入前提；上层无需携带9259步内部历史。

模板：`CycleRefinement.lift_view_invariant` 将已证明的 raw-to-view 转移和视图保持性组合到有限执行上。它不自动证明这两个前提。

## 2. 可识别的结构与候选证明

先阅读实际实例化的处理器源码，按 [源码引导提取引理](source-guided-lemmas.md) 记录候选、已有证明和展平cone；再使用下面的结构模式。

| DUT 结构 | 候选不变式/契约 | 必须核实的条件 |
|---|---|---|
| 寄存器输入由 enable mux 选择 | 禁用保持、启用更新 | reset/flush/stall 优先级；最终寄存器写者 |
| 各流水级重复的 valid、PC、instruction 寄存器 | 有效指令和PC按级转移；bubble不退休 | flush覆盖范围；分支恢复；背压传播 |
| RF数组与重复读mux | 任意索引下的选择关系，一次证明后实例化 | 地址具体性、边界、同步/异步读、读写冲突策略 |
| 旁路mux | 读取“应用较老 pending effect 后”的参考RF | 最新写者优先级、目的寄存器匹配、zero规则 |
| writeback选择器 | 不同执行单元结果归一成同一写回effect | 符号扩展、截断、load响应时序、link PC |
| PC多路选择与延迟redirect | 按流水线phase对齐参考PC | 寄存器延迟、bubble、重放、变长指令 |
| 重复ALU/访存decoder分支 | 按语义族共享主引理 | decoder覆盖、重叠与优先级、非法指令行为 |

相同 AST 形状不能证明语义相同。将实例差异抽成参数（节点映射、位宽、操作、优先级、读写模式），证明共同结构契约，再用经过检查的实例事实满足其前提。

## 3. 联合归纳解决 RF / PC 的逻辑互依赖

单独证明RF可能需要当前指令正确；指令对齐又需要PC；PC转移需要分支比较、JALR源值，最终依赖RF。不要把这些假设互相当成已完成定理。

定义一个足以保持的联合关系，例如：

```text
Joint(v,r) :=
  BanksAgree(v,r)
  ∧ PCPhaseAligned(v,r)
  ∧ PendingALUCorrect(v,r)
  ∧ PendingMemoryCorrect(v,r)
  ∧ RedirectAndJalrCorrect(v,r)
```

从 reset/initial 得到 Base；在同一个归纳步中按旧状态关系推出下一状态所有分量。局部组合证明可以只接受其中必要的分量；全局可达性负责同时建立它们。

源例：`CycleJointBase.cycle_joint_initial` → `CycleJointStep.cycle_joint_step` → `CycleJointInvariant.cycle_joint_observed_invariant`。`cycle_joint_step_with_quiet` 有额外无异常前提，公开 step 必须用已经证明的 `cycle_reference_no_exception_active` 关闭该前提。带历史PC假设的 `*_reachable_from_pc` 仍是条件引理。

## 4. 将 RF 更新归一成 effect

对单写端口，effect可以是 NoWrite 或 Write(dst,value)。证明：

1. 当前DUT/参考bank逐项相等；
2. 两边产生同一个effect；
3. 两边的提交/preview等于apply_effect；
4. 得到下一bank或checker输入相等。

`RegisterEffects.v` 提供逐项相等的保持、zero保护、写后读旁路和不受影响寄存器引理，不使用函数外延性公理。它显式采用硬接零寄存器架构；无zero寄存器的ISA应更换effect定义。多写端口要定义写入顺序或冲突优先级，证明effect列表的组合，不能直接复用单写模型。

源例：`RFWriteEffect.rf_apply_effect`，`MemoryPendingInvariant.cycle_reference_effect_step`，`RFAddPendingInvariant.cycle_add_pending_forwarded`。旁路应与 `apply_effect reference_bank pending` 对比；对旧参考bank直接取值会错过同周期writeback。

## 5. PC 与流水线phase

riscv-mini示例按 late bubble / early bubble / started 分情况，使 commitPC、frontPC 或 fetchPC 的变换对应参考PC。此关系是该DUT的phase关系，不是通用“DUT PC=参考PC”。其中 fetch为33位，架构PC为32位，含模2^32转换；固定+4和4字节对齐不能移植到支持压缩指令的处理器。

先证明每一级 hold/advance/flush 的真实周期契约，之后PC证明只调用契约。若重新设计为变长取指、异常入口或乱序退休，应重建phase/retirement关系；乱序设计通常需要队列/ROB对应关系，而不是沿用两级PC公式。

## 6. 将指令覆盖与语义正确性分开

`CycleInstructionCoverage.cycle_commit_instruction_coverage` 只给出合法指令落入37行decoder和9个语义族，不证明执行正确。另需每族的操作数、ALU/访存结果、RF effect和PC effect正确性，再由 `CycleISAReferenceAdvance.cycle_isa_reference_advance` 接到参考状态更新。

增加CSR/异常支持时，将必要的CSRbank、特权模式、异常cause/PC/优先级加入关系；仅放宽assume或接上线不产生这些新保持性定理。
