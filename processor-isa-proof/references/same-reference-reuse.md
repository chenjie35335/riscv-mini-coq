# 固定参考模型时的积极复用

后续项目默认继续使用同一个参考模型。先使用这里的参考证明库，不从头证明参考端。处理器变化主要产生新的 DUT 周期契约、两端输入/状态对应和原checker接线义务。XLEN/扩展配置及参考函数确实发生变化时，才针对受影响的声明更新参考证明。

## 三层代码已收集

| 层 | 本地资源 | 新DUT上的工作 |
|---|---|---|
| 共享执行语义 | `assets/shared-semantics/coq/` | 原样使用FIRRTL、UInt、validif、frame、寄存器保持和求值history引理；提供新AST位置/安全证书 |
| 固定参考的符号证明 | `assets/same-reference/coq/` | 原样使用参考bitvector函数及数值证明；证明DUT算出的操作数/effect与之对应 |
| 参考电路历史与状态更新 | [高层参考定理目录](reference-theorem-catalog.json) | 保留已有推导，将节点/执行器/阶段接入新reference embedding；不重新展开参考算法 |

第一、二层是实际 `.v` 证明代码，不只是方法总结。第三层目录记录真实定理头、源码位置与hash；其原定理有些仍依赖旧组合模型，尚未全部改造成独立参数化库，不能直接声称在新DUT编译通过。

## 现有可直接使用的参考证明族

| 模块 | 可复用内容 | 实例义务 |
|---|---|---|
| `ReferenceInstructionTable` | 固定参考的48行code/mask及位宽、索引函数 | 输入instruction对应；配置/表未改变 |
| `ReferenceInstructionCoverage` | `legal_reference_mask_coverage`、`classified_reference_decode` | `legal_instruction_classified`；本表的合法子集是原37类 |
| `ReferenceIllegalFold` | decoder匹配折叠为合法/非法布尔结果 | decoder项及guard匹配 |
| `ReferenceImmediateSemantics` | I/S/B/J立即数的原符号构造与相关size事实 | DUT提取字段对应这些构造；不能只凭函数名认定等价 |
| `RFUpperSemantics` | LUI/AUIPC构造、立即数及结果宽度 | DUT控制类、PC和instruction输入对应 |
| `ReferenceWordSemantics` | load lane宽度、mask、shift、扩展、地址函数 | lane/rs1/imm/raw响应对应 |
| `ReferenceLoadArithmetic` | mask去除、8/16/32位提取、符号/零扩展、padding截断 | 相应size和width界 |
| `RFWriteEffect` | 同一个参考RF effect及zero/逐项相等保持 | 两端应用相同的effect，写回/preview相位正确 |
| `ReferencePCSequentialValues` | 参考PC extension/resize/mux/+4/low extract | 原配置的32位PC与顺序推进语义 |
| `ReferencePCTargetValue` | JAL/JALR/branch共享参考目标值函数及resize | canonical guard map、PC、imm、rs1对应 |
| `ReferenceRedirectArithmetic` | signed/unsigned条件、对齐、重定向符号计算 | 操作数宽度、guard条件；不是重证整棵redirect mux |
| `RFShiftArithmetic` | 原SLL/SRL/SRA的移位实现→规格证明；`rf_shift_at_correct` / `rf_shift_word_correct` | left/right为32位；shamt取低5位；新DUT只证明其移位表达式/操作数对应 |
| `DUTBranchArithmetic` | 名称含DUT但实际是纯位向量恒等式：差值、signed/unsigned compare、branch numeric | 相同算术表达式和位宽即可用；不要按文件前缀丢弃 |
| `StoreDataShiftArithmetic` / `StoreMaskArithmetic` | 左移/截断/前缀mask等恒等式 | 对齐、尺寸和offset界 |
| `UIntResizeRoundtrip` / `UIntLowExtractRoundtrip` | UInt调整宽度/低位提取保持 | 具体值和位宽条件 |
| `ReferenceEventLogic` | 参考event布尔网络函数、safe条件及safe时false | `safe_false`仅为无事件分支；启用异常仍需对应证明 |
| `ReferenceControlGroundOperations/Expressions/ValidIf` | 同一参考控制表达式groundness闭包 | 表达式准备性、lookup groundness、policy条件 |

不同模块有同名常量时使用完整限定名，例如 `ReferenceInstructionTable.reference_instruction_codes` 和 `ReferenceInstructionCoverage.reference_instruction_codes` 的类型不同，不能混用。

## 快速检索已有结论

从包含skill的目录运行：

```sh
python3 processor-isa-proof/scripts/find_lemmas.py reference_load_unsigned32
python3 processor-isa-proof/scripts/find_lemmas.py rf_reference_effect_preview_history --bundle history
python3 processor-isa-proof/scripts/find_lemmas.py formal validif --bundle shared --limit 5
```

结果包含声明、来源、是否已收集源码以及是否仍需embedding。长声明有截断标记；应用前读取完整声明，不能忽略显示范围外的前提。

## 共享语义不再逐项目重建

`assets/shared-semantics/manifest.json` 包含每个定理的完整声明头和本地依赖。常用入口：

- `ConcreteGroundOperations` / `ConcreteBinaryOperations` / `ConcreteScalarExpressions`：具体值的一元/二元/表达式求值闭包。
- `ConcreteUIntOperations` / `ConcreteUIntScalarExpressions` / `ConcreteUIntValidIf`：UInt表达式、宽度及validif。
- `ConcreteFormalValidIf` / `FormalConcreteScalarExpressions`：带明确前提的formal-policy与既有求值桥接。
- `FormalSymbolicInvalidWire` / `SymbolicUInt` / `SymbolicBit` / `NormalizedBit`：命名symbolic choices与类型/位宽事实。
- `RegisterInvariants` / `StagedRegisterHold`：非提交迭代保持寄存器，避免每个cone重证。
- `ScalarNodeFrames` → `MemoryWriteFrames` → `FormalConnectionFrames` → `FormalTypedNodeFrames` / `FormalNodeSuffixFrames`：共享frame依赖层。
- `FormalNodeEquation` / `FormalTypedNodeEquation`：用新AST定位与suffix安全证书导出节点方程。
- `StagedIterationLemmas`：真实库上的迭代append、固定点及settled tail。

这些原样源码依赖同一 `firrtl2coq` 库和MathComp/nbits，不依赖 `CoreSocModel`、`ComparisonNodes` 或当前DUT。保持已有模块名可复用原来的 `Require Import`，不必每次发明新抽象名称。

## 实际组合：symbolic byte接参考unsigned load

迁移测试编译过下列组合；它直接复用两个不同共享层的结论，无需再次展开invalid policy或符号扩展算法：

```coq
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
  Semantics_with_implicit_widths Semantics_with_memory.
Require Import ReferenceLoadArithmetic FormalSymbolicInvalidWire.
Lemma reusable_unsigned_symbolic_byte inputs path site :
 exists byte,
  formal_invalid_policy inputs path site (Gtyp (Fuint 8)) = Gval (Fuint 8) byte /\
  size byte = 8%nat /\
  take 32 (sext_to 33 (zext 1 byte)) = zext_to 32 byte.
Proof.
 destruct (formal_invalid_uint_word inputs path site 8) as [byte [Value Width]].
 exists byte. split; [exact Value|]. split; [exact Width|].
 apply reference_load_unsigned32. rewrite Width. reflexivity.
Qed.
```

这证明的是任意symbolic byte的参考扩展关系；实际DUT的响应byte与该值对应、以及load结果到checker的传输仍由新DUT契约给出。

## 保留高层参考证明：按“参考内部名称”与“目标节点名称”分离

展平后nodeID改变，不代表参考逻辑需要重证。把旧参考cone的编号当作canonical内部名称；为新组合电路建立映射 `rho`。例如纯函数 `reference_event_value g` 中的数字索引读取的是canonical guard map，可令 `g n` 对应新电路节点 `rho n` 的已证明布尔值。

要迁移带真实执行history的高层定理，需要一个**已证明的**reference embedding/step adapter，至少包括：

1. canonical参考信号与目标reference节点的lookup、类型及width对应；
2. 相关节点表达式/连接/寄存器/存储的映射与实际写入安全；
3. 新电路成功一步可投影为所需参考cone的一步关系，含old/result和commit mode；
4. 相同参考输入、instance path和symbolic invalid choice的对应；若syntax位置/instance路径改变，证明policy transport，不能默认随机值自然相等；
5. 参考输入在需要的settling窗口保持；从新电路的实际history提取该窗口；
6. observation/commit阶段和memory side effects的对应。

全局迭代预算变大或变小，重新证明预算足以覆盖参考cone的所需窗口。原proof的语义主体和局部深度可以保留；不能机械沿用9259或把新预算成功当作fixedpoint。

同一namespace下参考AST和节点完全不变时，可直接导入对应原模块；若模块仍 `Require CoreSocModel`，先隔离其参考常量/位置证书，或把这些作为Section参数再复用主体。只做文本nodeID替换不是上述adapter的证明。

## 高层参考端最值得保留的证明

| 族 | 已有核心定理 | 保留的推导与新wrapper |
|---|---|---|
| RF读口 | `reference_register_read_history` / `reference_second_register_read_history` | 保留32路选择链证明；新wrapper提供bank/地址/成功history与时间窗 |
| RF写回 | `rf_reference_effect_history` / `rf_reference_effect_preview_history` | 保留36级decoder/write-mux fold；新wrapper提供各类effect数据和commit映射 |
| 按启用类写回 | `rf_reference_guarded_effect_history` / `rf_reference_guarded_bank_effect_commit` | 只需活动opcode的数据前提，优先用于受限ISA子集，避免证明不可达分支 |
| 顺序PC | `reference_pc_sequential_payload_after_nine` / `reference_pc_sequential_commit_after_nine` | 保留参考PC网络和提交；适配新observation |
| 停顿/重定向PC | `reference_pc_disabled_payload_after_five` / `reference_pc_redirect_payload_after_five` | 保留对应参考控制路径，提供真实guard和history |
| decoder | `reference_instruction_decode_history` | 保留mask/code语义和48行网络传播；提供实际输入instruction |
| load | `reference_load_function_history` | 保留地址/shift/mask/extend网络；新DUT证明访存请求/响应关系 |
| store | `reference_store_request_data_history` / `reference_store_request_alias_history` | 保留参考数据选择及alias传播；新DUT证明rs2/guard/请求相位 |
| event | `reference_event_spine_history` | 对任意稳定guard map的网络传播，本身不限于禁用event；新的启用事件需要语义对应 |
| 非法/system decode | `reference_illegal_output_history` / `reference_system_decode_history` | 保留分类；旧 `*_absent_observed` 的合法域前提需按新scope审视 |
| CSR具体性 | `misa_normal_history` | 保留参考CSR类型/具体性引理；不等于完整CSR状态refinement |

精确模块、声明和前提在 [catalog](reference-theorem-catalog.json)。`*_observed`、`*_reachable`、`*FullHistory` 通常加入旧组合模型的周期/合法域连接；检查真实声明，保留参考部分，替换集成wrapper。

## 检查与后续积累

运行新的source-only检查：

```sh
python3 processor-isa-proof/scripts/check_reference_assets.py \
  --library-root /path/to/firrtl2coq --tool-bin /path/to/coq/bin --jobs 4
```

脚本只复制`.v`到外部临时目录；用coqdep安排本地闭包并行编译，逐个审计收集的定理，再递归coqchk。不会使用源目录中可能陈旧的`.vo`，也不编译原DUT。MathComp和Coq标准库来自指定工具环境；库源码/hash与结果写入report。

第一次建立固定参考库后，后续DUT项目复用已经验证且身份匹配的库/证明构建。新增参考端结论回收到共同库；新DUT只保存其结构证书、cycle contracts及对应关系。共享库版本变化时按依赖增量重查，不以更换DUT为由重做全部参考端证明。

此次新增代码的验证记录见 [reference-validation.json](reference-validation.json)：51个收集模块、195个闭合定理审计；连同共享库共75个模块从源码构建，递归kernel覆盖通过。ALU shift增量检查复用了hash完全一致的基线产物，未重复编译已完成的库。该结果不包含尚未迁移的130个高层历史定理，也不是新DUT的验证结果。
