# 从 riscv-mini 证明中抽取的可复用方法

提取源：`~/curricular/Research/HV/code/riscv-mini-proof`。下述路径以该仓库为根；未标目录的证明模块均在 `formal/flat-low/staged-integration/`。本skill不改动源库或处理器模型。固定参考模型模式新增了51个实际证明模块：30个共享执行语义模块、21个隔离参考语义模块，共195个已证明声明；大型组合模型和DUT专有证书仍留在源仓库。

## 抽取结果分三类

| 类别 | 内容 | 如何迁移 |
|---|---|---|
| 原样/隔离后可直接使用的原证明 | 共享求值/frame/validif、固定参考decoder/立即数/PC/RF/load/store/branch/event符号证明 | 使用 `assets/shared-semantics/` 与 `assets/same-reference/`；保留原声明与证明体 |
| 通用逻辑模板 | rank传播、有限执行归纳、effect保持、guarded checker、不动点后缀 | 使用 `assets/coq/`；为无DUT依赖的已证明引理 |
| 可复用的证明组织方法 | 周期视图、RF/PC联合不变式、pending forwarding、指令族分解、原checker桥接 | 在新DUT证明adapter与保持性，不能只重命名 |
| 新DUT适配与集成 | DUT节点/表达式、结构与rank证书、预算充分性、PC phase及参考接线 | 参考内部语义与decoder保持不变时直接复用；只证明新embedding/接口和受影响前提 |

## 具体来源和抽取理由

| 源定理/定义 | 原作用 | 抽取落点 |
|---|---|---|
| `CycleView.cycle_view_at` / `cycle_transition` | 信号快照；隐藏commit的周期上下文 | view/transition接口，正确性另置 |
| `CycleJointBase.cycle_joint_initial` | 初始联合不变式 | target initialization obligation |
| `CycleJointStep.cycle_joint_step` | 一周期同时保持PC与pending/data | cycle contract与joint preservation |
| `CycleJointInvariant.cycle_joint_observed_invariant` | 对真实合法周期归纳 | `CycleRefinement.invariant_execution` / view lifting |
| `RFWriteEffect.rf_apply_effect` | writeback与zero规则 | `RegisterEffects`，显式参数化寄存器和值 |
| `RFAddPendingInvariant.cycle_add_pending_forwarded` | 使用pending effect后的参考操作数 | forwarded-bank关系，而非陈旧RF |
| `MemoryPendingInvariant.cycle_reference_effect_step` | 参考RF跨周期更新 | common-effect证明分解 |
| `RFReadPorts.rf_actual_forwarding_observed` | 隐藏读端口mux与history细节 | 观察层read contract；不复制35/36/37常数 |
| `CommitPCControlledPropagation.commit_pc_controlled_after_four` | 由真实迭代证明PC reset/hold/advance | 周期级stage contract；四步是目标相关界 |
| `CycleInstructionCoverage.cycle_commit_instruction_coverage` | 37行decoder分类覆盖 | coverage与semantics分开 |
| `CycleISAReferenceAdvance.cycle_isa_reference_advance` | pending/effect接到ISA更新 | retirement reference matching |
| `CycleRFOriginalAssertions.cycle_rf_original_assertion_normal` | preview bank接原始RFassert | checker相位桥接 |
| `FormalObservationCommit.observation_then_commit` | 真实observe接真实commit | 保留成功性和阶段顺序 |
| `FormalLocalHistory.local_iteration_history` | 从成功执行提取内部history | history有执行依据，非额外假设 |
| `FormalTypedNodeEquation.formal_combinational_known_node` | 定位+求值+类型+后缀frame得到节点值 | target node-equation adapter |
| `FormalNodeSuffixFrames.formal_suffix_preserves_value` | 后续statement不破坏目标 | `EvaluationFacts`局部性模式；memory另证 |
| `DependencyRankSoundness.dependency_ranks_valid_sound` | 检查证书推出依赖降秩 | `RankedSettling.ranks_valid_sound` |
| `CheckedDependencyHistory.checked_dependency_history` | 降秩图上的有界history传播 | `RankedSettling.ranked_history`的显式前提版本 |
| `ALUInputStability.alu_stability_from_roots` | 两时刻相等/ground的锥稳定 | 按cone与rank证明，而非全电路归约 |
| `StagedIterationLemmas.formal_iterations_settled_tail` | 已到固定点可丢弃任意后缀 | `EvaluationFacts.settled_after_prefix` |
| `formal/flat-low/ComparisonTruth.uint_equal_comparison` | UInt数值相等使真实比较为true | `CheckerFacts.numeric_checker`及真实比较adapter |
| `FormalAssertionDischarge.assertion_0_from_enabled_agreement` | 启用时old操作数相等接到result原assert | `CheckerFacts.guarded_checker`逻辑骨架 |
| `EventAssertionSemantics.event_dut_valid_false_observed` | 原no-trap域下event禁用 | 覆盖范围/非空性提示，不能当异常语义证明 |
| `AllOriginalAssertions.all_original_assertions` | 合取原45个generated谓词 | 保留真实endpoint和完整依赖审计 |

源文件SHA-256和声明位置见 [provenance.json](provenance.json)，可定位此次分析快照。位置是检索辅助；hash对应整份文件。原通用模板是重新泛化的代码；新增共享执行语义模块原样复制，参考模块保留原声明/证明体并隔离导入，分别有独立manifest。它们均不是原全量处理器证明重新检查的报告。

## 推荐的新处理器证明顺序

先确定真实assume、观察点及退休边界；优先检索固定参考和共享执行语义包，复用已有frame/节点/数值定理，仅补新的目标证书；封装少量每周期read/write/PC/flush契约；选择可保持的联合不变式；按操作族证明共同effect；将其接到原checker和架构步；最后检查完整endpoint的依赖和信任边界。

这比“每个assert都直接展开整个DUT”更容易共享工作。结构重复度高的寄存器、读端口、writeback和decoder可参数化；对逻辑互依赖的RF/PC以同一归纳收敛，而不是让独立agent分别假设对方结果。

## 需要保留的范围限定

- 此源的coverage theorem仍显式使用 `row<37`，event证明使用no-trap上下文。历史原45断言结论不能直接推广到放开CSR/异常后的新模型。
- CSR信号出现在证明中不等于证明了完整CSR状态一致性。对新域需增加CSR写读、异常入口/返回、cause与特权状态对应关系，并核对参考模型实际支持。
- 9259是求值预算；ALU相关锥128后稳定是有额外条件的局部结果，二者不等价于全状态fixed point。
- 当前源库的两个类型布尔等价引理已经以 `Qed` 证明；不能沿用历史“两处Admitted”的假设清单。这里没有重跑原处理器的全量编译/kernel check。
- 此次确实重编译和kernel-check的是通用模板与例子。它们证明通用蕴含关系；新处理器的契约前提仍需实际证明。

详细方法按需读取： [DUT不变式](dut-invariants.md)、[语义与不动点](evaluation-and-fixed-points.md)、[checker和审计](checker-and-validation.md)、[迁移操作](porting-guide.md)。

扩展内容：[固定参考模型复用](same-reference-reuse.md)、[高层参考定理目录](reference-theorem-catalog.json)、[多agent分工](agent-workflow.md)。
