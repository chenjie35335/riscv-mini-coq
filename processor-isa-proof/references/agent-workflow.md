# 多 agent 证明分工与共享引理

## 经验依据与适用范围

本次会话可见的历史任务名包括 `bank_resume`、`bubble_nop`、`early_control_wires`、`early_control_history`、`pc_resume`、`pc_finish`，以及本次提取的 `extract_dut_patterns` / `extract_semantic_patterns`。原证明仓库 `.agents/`、`.codex/` 目录为空，没有完整的逐次派工记录。下面结合这些任务主题和现有模块依赖整理成可复用方案；它不是对每个历史 agent 实际修改范围的追溯声明。

核心经验：先并行补独立语义/局部执行契约，再围绕共享cycle invariant集成。不要让RF agent假设尚未完成的PC结论，同时让PC agent假设尚未完成的RF结论。

## 历史任务主题如何收敛到共享接口

下表是任务主题与现存模块的功能对应，供重新派工时使用；不表示已恢复每个agent的完整提交历史。

| 会话任务名 | 对应的证明工作 | 新项目中的交付边界 |
|---|---|---|
| `bank_resume` | `RFArchitecturalNormalRelation` / `RFArchitecturalObservedRelation` 等RF关系 | bank逐项相等、pending effect、reset/normal分支，供Joint使用 |
| `bubble_nop` | `RFReferenceNopHistory` / `RFReferenceNopRelation`、`CheckerValidBubbleHistory` | bubble/NOP的保持与valid契约，避免每个assert重复推导 |
| `early_control_wires` | `EarlyControlWireCongruence` / `EarlyControlWireBitNormalization` | 控制线接线、位宽和一步节点方程 |
| `early_control_history` | `EarlyControlStabilityHistory` | 由真实history及稳定root传播控制值，封装settling细节 |
| `pc_resume` / `pc_finish` | `PipelinePCRelation`、`PipelinePCFrontToCommit`、`CycleJointInvariant`等 | PC phase与跨周期保持；最终和RF等分量统一归纳 |

x0、reset、bubble/NOP等容易独立闭合的义务可先完成并共享；之后agent集中处理尚未闭合的正常执行、分支、访存和事件。不为已经证明的x0继续开重复任务，也不把“完成的assert数量”代替联合不变式中的缺失条件。

## 按证明接口分工

| 角色 | 输入 | 交付的定理/证据 | 共享边界 |
|---|---|---|---|
| Source analysis（可与DUT contracts合并） | 实际elaboration配置、处理器源码、当前缺失义务 | 局部规格/候选不变式、源码到flat cone线索、可复用lemma清单 | 依[源码提取流程](source-guided-lemmas.md)，不把候选当作已证明前提 |
| Reference | 固定参考模型、复用包、允许的ISA域 | 已有参考定理的复用入口；缺失语义与relocation清单 | 不按新DUT重新证明参考算法 |
| Semantics | shared evaluator/库、生成AST | typed node equation、frame、成功history、rank soundness | 不证明某条指令的架构正确性 |
| DUT contracts | DUT AST/RTL说明、冻结的View接口 | reset/hold/advance/flush/read/write/旁路每周期契约 | 接口不暴露整周期内部迭代history |
| RF / ALU families | 周期契约、参考effect、decoder覆盖 | Add/Sub、Compare、Bitwise、Shift、Upper、Link的pending/effect匹配 | 共享apply_effect、操作数和zero规则 |
| PC / Pipeline | 周期契约、分支操作数接口、参考PC函数 | bubble/phase、顺序/跳转/JALR/redirect关系 | 给联合step提供条件分量，不循环依赖可达性 |
| Memory | memory环境、load/store参考语义、总线契约 | 地址/对齐/宽度/符号扩展/mask/data/effect匹配 | 明确请求、响应和提交相位 |
| CSR / Events | 同一参考的CSR/trap接口、合法域 | CSR effects、cause/EPC/tval/priority、事件对应 | trap可推进架构而不退休；不沿用禁用event结论 |
| Integration / Checker | 各分量局部step、真实checker | JointBase、JointStep、Reachability、每个原assert及聚合endpoint | 父agent拥有公共接口与聚合模块 |
| Verification | 冻结的源码及依赖图 | 编译、Assumptions、kernel覆盖和hash报告 | 检查者不为通过检查而改语义/assume |

分角色不意味着同时开启全部agent。可用槽位少时按波次安排，同一agent完成一个独立包后转岗。

## 四个并发槽位的具体排程

固定参考库和共享语义已验证时，默认跳过基础重建波次。直接按当前义务分配，例如父agent做新reference transport与集成，三个子agent分别处理load mismatch、RF/ALU shift、CSR/Events；只在新契约缺失时临时切换相应角色。下面第一波主要用于首次建库或基础接口确实缺失的情况。

1. 父agent固定scope、接口、模块所有权和任务板。三个子agent分别做 Reference复用、Semantics、DUT contracts。已有并验证过的共享库直接复用；无需每次重建参考证明。
2. 基础接口就绪后，三个子agent分别做 RF/ALU、PC/Pipeline、Memory。父agent集成局部step与联合不变式，尽早检查是否缺少pending、phase或别名信息。CSR/Event域较大时，将已完成的RF或Memory agent转到该任务。
3. 原assert按共享关系分组：RF的所有索引共享一个bank定理；PC共享phase关系；load/store共享请求/响应契约；event/CSR共享事件模型。需要更多并行时才拆指令族或checker实例，避免45个assert各自展开整份DUT。
4. 有模块闭合即可按DAG编译，与其余证明工作重叠。最终对冻结的aggregate做完整检查；资源限制按内存和实际编译代价设置，而不是agent数等于compiler数。

若任务明确只修改一个低层义务，启用相关角色即可。agent并行使用遵守当前会话授权和可用槽位。

## 每项任务的最小契约

直接使用 [任务模板](../assets/agent-tasks.json) 中的角色提示，补齐：

```text
目标：一个明确的公开定理，包含成功执行/合法输入/宽度等前提。
读：固定版本的参考语义、共享引理和上游接口。
写：指定的文件；公共View/Joint/aggregate仅由约定owner修改。
依赖：哪些已完成，哪些仍是显式待证的adapter前提。
交付：声明、源文件、编译命令/结果、Print Assumptions、未闭合义务。
```

父agent可以在同一工作树按文件分配互不重叠的写入范围。需要隔离时用独立worktree；集成时保留源hash和实际检查身份。不要让多个agent同时修改共享接口或同一个生成器输出。

## 把 agent 的成果转成共享 lemma

- 两个任务都在重复展开同一表达式/寄存器更新：由Semantics或DUT contracts角色先抽公共节点/周期定理，调用者只rewrite接口。
- 多个ALU族都证明相同RF预览更新：把共同effect保持性提升到共享层，各族只证明effect选择和值。
- RF与PC互相需要：将条件分量装入同一个Joint；局部step可以使用旧Joint中需要的分量，父agent证明完整联合归纳。
- 多个参考族重复decode/immediate/extension：放入固定参考库，所有DUT adapter共同使用，不再复制到各DUT目录。
- 同一锥在多个任务重复传播：共享rank证书和语义transfer；不要把不同policy、memory alias条件或commit相位的事实误合并。

公共lemma必须公开前提及来源；合并一次后通知所有调用者。调用者证明成功不等于前提已在真实可达性中关闭。

## 状态、交接和检查频率

任务板使用 `blocked-on-contract`、`proving`、`compiled-local`、`integrated`、`kernel-checked` 等可核实状态，另列 `remaining_hypotheses`。局部有额外前提的定理记为conditional，不写“证明完成”。依赖接口未就绪时，让agent处理其他独立义务或返回缺失条件；不等待一个永远循环的假设。

状态更新以定理完成、接口变化、编译失败和资源瓶颈等事件为主。对长时间运行的检查按用户约定降低轮询频率；若用户要求每半小时查询，遵守该间隔。记录每条完成证据及失败原因，避免父agent反复读取巨大日志。

已有串行结果仅在同一源码、artifact、编译器和依赖身份下复用。检查进程正在运行不是kernel验证完成；中断的最后一个模块需要重新确认。最终由Integration/Verification统一报告，不能把各agent的独立“通过”数量简单相加。
