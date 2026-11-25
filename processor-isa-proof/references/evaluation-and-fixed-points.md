# 求值、frame、依赖秩和不动点

## 1. 分清一次求值、组合迭代、周期提交

该源库有一次statement列表求值、同一周期内反复组合求值（`set_regs=false`）、寄存器提交（`set_regs=true`）三个操作。`generated_observe` 处于相应观察阶段，`generated_run` 跨周期递归。

`FormalLocalHistory.circuit_iteration_history` / `local_iteration_history` 从成功迭代构造实际history：起点、终点和每一步成功。使用此history证明节点延迟；不要额外假设一条与执行器无联系的history。

`FormalObservationCommit.observation_then_commit` 将真实successor运行接到观察后的commit；`generated_successful_commit` 提供成功观察witness。保留 `Some` 成功条件。`None` 不是合法状态或证明成功。

## 2. 节点方程：定位 + 表达式 + 类型 + frame

源定理 `FormalTypedNodeEquation.formal_combinational_known_node` 的关键前提为：

- statement中指定位置确实是该node及expression；
- expression在指定 old 环境和 invalid policy 下成功求值；
- 得到指定UInt宽度的值；
- 它不是寄存器节点；
- 后缀不会再次修改目标（`formal_typed_suffix_safe`）；
- 整次真实执行成功。

这样推出结果map的节点值。上层可只rewrite这个方程，无需再次展开整个DUT AST。

`FormalNodeSuffixFrames.formal_suffix_preserves_value` 的frame前提考虑memory suffix安全。简单“后面没有同名lhs”不够：connection可能影响多个位置，memory存储可能别名，条件分支可能写入目标。源布尔检查器对不支持的 `Swhen` 拒绝，不能擅自扩大其soundness域。

模板 `EvaluationFacts.eval_after_unrelated_write` 抽象了局部性：在reads集合上一致的环境具有相同求值；不属于reads的写入不影响结果。对于含memory的表达式，reads必须覆盖真实memory footprint，不能只列出语法寄存器名。

## 3. rank证书负责调度，语义引理负责含义

源链条：

```text
提取依赖锥和rank表（非可信生成）
 → dependency_ranks_valid table = true（核内检查证书）
 → dependency_ranks_valid_sound（每条依赖严格降秩）
 → checked_dependency_history（抽象Holds传播）
 → DUT具体的一步节点方程/稳定性
```

模板 `RankedSettling.ranked_history` 的前提：节点集合对依赖闭合；每条依赖严格降秩；rank0节点在所有所需时间成立；依赖在t成立可推出目标在t+1成立。结论为 rank(node)<=t 时Holds(t,node)。所有这些前提都必须在adapter证明。

模板使用函数rank和有限nodes，与源带lookup的表不同。若以外部表实现rank/deps，须检查成员、缺失项、闭合性以及数据与DUT语法的一致性。一个完全错误但无环的图也可能通过rank检查，因而rank soundness不能代替语义transfer。

源 `CheckedDependencyHistory` 还有limit边界。模板 `ranked_history` 要求所有时间的seeds和transfer；`ranked_history_bounded` 则只要求 `time<=limit` 的seeds和 `time<limit` 的transfer，结论限制在 `time<=limit`。只有有限成功历史时使用有界版本，不要将有限事实提升为无限事实。`Examples.Cone.bounded_propagation` 演示了直接实例化。

## 4. 只稳定相关锥

`ALUInputStability.alu_stability_from_roots` 证明：固定policy下每一步成功；所有root在55之后ground且两时刻相等；由严格降秩和transfer，rank为r的节点在55+r之后ground且两时刻相等。随后 `alu_inputs_stable_history` 将ALU target专门化为128后稳定，`alu_stable_value_at` 在中间稳定迭代与最终观察间运输值。

这里的55、128、nodeID和9259都是目标相关参数。方法可复用，数字不可复制。证明pairwise equality需要把Holds实例化为groundness/不同history时刻之间相等，或使用相应的rank良基归纳；单纯“值存在”不足以推出稳定。

对仅有有限迭代语义的目标，可以在实际预算范围内证明所需锥的值；不必为了checker强行证明全状态不动点。若有组合环或跨迭代不降秩的依赖，需SCC局部不动点、单调有限格收敛等额外论证，当前DAG模板不直接适用。

## 5. 真正不动点需要self-loop

模板与源 `StagedIterationLemmas` 都只证明：

```text
step stable = Some stable
  ⇒ iterate step fuel stable = Some stable

iterate step prefix initial = Some stable
∧ step stable = Some stable
  ⇒ iterate step (prefix + extra) initial = Some stable
```

其中 `step` 必须是同一确定函数：相同输入、实例路径、invalid choices、commit mode。`StagedIterationCount.flat_iteration_count_exact` 证明预算是9259，不能据此推出全状态已固定。模板 `Examples.Settling.budget_is_not_fixed` 给出成功运行1步但尚未固定的具体反例。

## 6. invalid、位宽和语义替换

源 `Semantics_with_memory.symbolic_word` 使用带长度证明的bits；`symbolic_inputs` 由instance path、syntax site、leaf和width索引。一个周期的组合求值中固定choices，跨周期可改变。用零替代任意invalid会缩小待证域；每次迭代重选invalid则改变收敛问题。

`FormalConcreteScalarExpressions.scalar_formal_evaluation_equal` 仅在 `scalar_expression_ready` 等条件下连接formal-policy求值和旧求值；`ConcreteUIntValidIf.formal_uint_validif_concrete` 同样有具体准备性/类型条件。不能不加前提地替换所有表达式语义。

数值比较相等不要求结构类型相等，但截断、拼接、符号扩展、除法和移位的语义依赖位宽。把这些类型/长度前提留在对应表达式引理里，避免为每个数值checker重复证明整棵类型树相等。
