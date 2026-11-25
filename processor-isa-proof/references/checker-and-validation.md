# Checker、覆盖范围与可复核检查

## 1. 从位串值相等接回原始assert

源 `ComparisonTruth.comparison_inputs_agree` 是：左右均成功读取UInt值，且 `to_N b1 = to_N b2`。`uint_equal_comparison` 允许不同宽度，推出真实比较表达式为 `Some (Gval (Fuint 1) [true])`。并不需要先证明 `w1=w2` 或原始bits列表相等。

模板 `CheckerFacts.guarded_checker` 将已证明的“启用时左右相等”和比较soundness接到 `enabled=true -> predicate=true`。将Value实例化为解码后的N即可使用数值相等；`numeric_checker` 提供N.eqb的桥梁。`same_bits_width` 只是另一种更强的列表相等关系的辅助事实，不是数值比较的必要步骤。

这些模板不认识某个生成器的assert语义。adapter仍需证明真实enable、比较节点、布尔truth和instance lookup的对应性。

源 `generated_hvalue_true` 对UInt1使用 `bits != [false]`；未有具体值/宽度约束时，不要自动解释成 `bits=[true]`。用确定的 `[true]` 接 `known_true_node` 是充分路径。

## 2. Old / result 和 preview / commit 是不同边界

源 `FormalAssertionDischarge.assertion_0_from_enabled_agreement` 等45个同构引理要求：

```text
真实一次迭代 old → result 成功
∧ (enable在result成立 → 两个比较输入在old中agreement)
⇒ 原generated local assertion在result成立
```

`FormalComparisonNodes.formal_comparison_0_iteration` 给出真实比较节点在result的值等于比较表达式在old的求值。不要把“在result相等”未经运输直接代入old义务。

类似地，`CycleRFOriginalAssertions.cycle_rf_original_assertion_normal` 接的是迭代9258处的写回preview，不只是snapshot中RF已经相等。先证明两边preview都是同一个pending effect应用于相等bank，再获得真实checker输入一致。reset分支用单独的 `cycle_rf_original_assertion_reset`。

## 3. 断言成立可能由enable不可达得到

`disabled_checker` 证明enable=false时蕴含式成立。这是合法逻辑，但不说明启用时数据正确，也不说明合法执行中存在启用事件。

源 `EventAssertionSemantics.event_dut_valid_false_observed` 经过 `dut_no_trap_observed_context` 关闭event-valid。在该scope中这类断言可能以禁用方式成立。若放开异常、ECALL/EBREAK或CSR，需重新证明启用事件的cause、PC、地址、CSR更新、优先级及参考步，不能把旧的禁用证据当成新的事件支持。

实际项目的覆盖表建议至少区分：

| 义务 | 范围 | 原始endpoint | discharge方式 | 还需证明 |
|---|---|---|---|---|
| RF[0..n) | 正常退休/reset | 真实generated predicates | common effect/zero规则 | 每指令族effect |
| PC | bubble/advance/redirect | 真实PCassert | phase relation | 新控制流模式 |
| memory | 合法请求/响应 | 地址、数据、mask等assert | memory契约 | 新异常/一致性域 |
| event/CSR | 明确特权/异常域 | 对应assert或独立模拟 | enabled proof或禁用 | 尚未覆盖的事件 |

从实际assume解码scope，考虑参考模型是否实现相应指令、旧/新ISA编码、计数器和memory时序。45个assert与45个指令类别无直接等价关系。

## 4. 接回完整原始声明

`AssertionInstances.assertion_0_at_top` 将local结论提升到实际top map；缺失top在源中是False，不能用空实例集合规避。`GeneratedAssertion0.generated_assert_0` 等使用真实 `generated_observe` 和 `generated_legal_trace`；`AllOriginalAssertions.all_original_assertions` 合取45个原predicates。

对生成模型拆分时，保持模型定义前缀与原文件一致，另证endpoint而不是导入原来admitted的endpoint。精确比对原声明、所有assume、语义入口和依赖闭包；“看起来一样”或重新写的弱checker不够。

即使这些原断言全成立，对完整ISA refinement的结论仍取决于checker覆盖、状态对应关系和模型可信边界。`CycleRefinement.simulate_execution` 只给有限trace、允许停顿的安全模拟；允许永久停顿时不能推出进展或活性。其 `advances` 必须包括参考模型要求推进的trap/interrupt，不能将“未退休指令”一概解释成stutter。

## 5. 信任边界和验证记录

- `Print Assumptions` 针对实际聚合endpoint，显式列出继承公理；源码扫描不能替代依赖审计。
- 通用模板中的Section变量是定理参数，必须由adapter证明；不增加全局公理。
- 当前提取快照中 `HiEnv_with_implicit_widths.ftype_eqn_eq` 和 `ffield_eqn_eq` 已是 `Qed`，Nflip分支比较字段名。历史上允许两处admission的记录不能证明当前 `.vo` 或其他分支；审计必须绑定当次源码与构建。
- 不修改库来绕过困难，不新加admit、unchecked casts、关闭guard checking等证明逃逸。既有用户允许的公理应明确报告为条件性结果。
- 编译、kernel check、原始声明一致性和assumption audit是不同证据，分别记录。

## 6. 并行与复用检查结果

先按 `coqdep` 等实际依赖安排编译；独立语义族、节点契约和checker实例可并行，聚合endpoint等待依赖。按峰值内存限制工作者，避免增加线程导致交换和整体变慢。

kernel分片要覆盖全部目标模块及外部递归依赖，并绑定源码、artifact、Coq版本和命令。单独 `-norec` 分片不代表已经递归检查了所有依赖。只复用与当前构建身份一致的成功结果；不要以进程活跃或日志最后一个“Checking”标记声明模块完成。

模板脚本运行普通递归 `coqchk`，因为模板体量小；不需要搬入原项目为巨型生成AST设计的完整并行调度系统。
