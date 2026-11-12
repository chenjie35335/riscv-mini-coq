# FIRRTL to Coq Exporter

## 1. 功能简介

`ExportCoq.cpp` 实现了一个 FIRRTL 到 Coq 的导出工具，将 CIRCT FIRRTL Dialect 的 MLIR 中间表示转换为 Coq 代码，用于建立硬件电路的形式化状态机模型。

导出器将硬件电路表示为：

- **Inputs**：电路输入。

- **State**：电路内部状态，包括寄存器和存储器。

- **Outputs**：电路输出。

- **step**：电路状态转移函数。

- **trace**：电路运行轨迹。

注意：本工具不直接解析 FIRRTL 文本文件，输入必须是经过验证的 CIRCT FIRRTL Dialect MLIR IR。

## 2. 输入与输出

### 2.1 输入

命令行参数：

```
firrtl-to-coq input.mlir Module output.v [--named-nodes]
```

| 参数              | 说明                               |
| --------------- | -------------------------------- |
| `input.mlir`    | 输入的 FIRRTL MLIR 文件               |
| `Module`        | 需要导出的 FIRRTL 模块名称                |
| `output.v`      | 生成的 Coq 文件路径                     |
| `--named-nodes` | 可选参数，将中间表达式生成为独立的 Coq Definition |

程序首先解析并验证 MLIR，然后查找指定名称的 `FModuleOp`，最后执行 Coq 导出。

### 2.2 输出

生成的 `.v` 文件依赖：

```
From Coq Require Import ZArith.Require Import Semantics.Open Scope Z_scope.
```

主要包含以下定义：

| Coq 定义    | 作用                 |
| --------- | ------------------ |
| `Inputs`  | 定义电路输入             |
| `State`   | 定义电路内部状态           |
| `Outputs` | 定义电路输出             |
| `eval`    | 根据当前输入和状态计算输出及下一状态 |
| `outputs` | 提取当前电路输出           |
| `step`    | 提取状态转移结果           |
| `trace`   | 描述电路的运行轨迹          |

其中，核心函数的类型为：

```
eval : Inputs -> State -> Outputs * State
```

即：

```
当前输入 + 当前状态          ↓        eval          ↓当前输出 + 下一状态
```

## 3. FIRRTL 与 Coq 数据类型转换

### 3.1 基本数据类型

导出器使用 Coq 的数学整数类型 `Z` 作为统一的数据存储类型，并通过 `bv` 包装表达式，保留 FIRRTL 信号的位宽信息。

| FIRRTL 类型 | Coq 表示              | 说明             |
| --------- | ------------------- | -------------- |
| `UInt<W>` | `Z` + `(bv W expr)` | 无符号 W 位整数      |
| `SInt<W>` | `Z` + `(bv W expr)` | 有符号 W 位整数      |
| `Clock`   | 时钟信号                | 用于寄存器和时序事件     |
| `Reset`   | 复位信号                | 支持同步复位，不支持异步复位 |

例如，FIRRTL 中：

```
UInt<8>
```

对应的 Coq 表达式：

```
(bv 8 expr)
```

对于有符号整数 `SInt<W>`，在数值运算中还会通过：

```
(signed W expr)
```

进行有符号解释。

需要注意，`Inputs`、`State` 和 `Outputs` 中的数值字段统一声明为 `Z`，实际信号位宽由表达式中的 `bv` 处理。

`bv` 和 `signed` 的具体语义由外部依赖文件 `Semantics.v` 定义。

### 3.2 运算表达式转换

| FIRRTL 操作     | Coq 表达式                 | 说明      |
| ------------- | ----------------------- | ------- |
| `constant`    | 整数常量                    | 常量转换    |
| `add`         | `+`                     | 加法      |
| `sub`         | `-`                     | 减法      |
| `mul`         | `*`                     | 乘法      |
| `div`         | `Z.quot`                | 除法      |
| `rem`         | `Z.rem`                 | 取余      |
| `and`         | `Z.land`                | 按位与     |
| `or`          | `Z.lor`                 | 按位或     |
| `xor`         | `Z.lxor`                | 按位异或    |
| `not`         | `Z.lnot`                | 按位取反    |
| `neg`         | `-`                     | 取负      |
| `eq` / `neq`  | `Z.eqb` / `negb`        | 相等比较    |
| `lt` / `leq`  | `Z.ltb` / `Z.leb`       | 小于、小于等于 |
| `gt` / `geq`  | 反向比较                    | 大于、大于等于 |
| `mux`         | `mux`                   | 多路选择    |
| `shl` / `shr` | `Z.shiftl` / `Z.shiftr` | 位移      |
| `cat`         | `Z.shiftl` + `Z.lor`    | 位拼接     |
| `bits`        | `Z.shiftr`              | 位提取     |

其他支持的操作还包括 `pad`、`cvt`、`asUInt`、`asSInt`、`head`、`tail`、`dshl`、`dshlw`、`dshr`、`orr`、`andr` 和 `multibit_mux`。

所有转换结果会根据目标 FIRRTL 类型进行位宽包装。

### 3.3 特殊值处理

对于部分不确定行为，导出器采用额外输入进行建模：

| FIRRTL 情况      | Coq 表示       | 说明           |
| -------------- | ------------ | ------------ |
| `invalidvalue` | `undef_*`    | 未定义值，作为外部输入  |
| 除数为零           | `divzero_*`  | 使用外部输入表示任意结果 |
| Memory 读使能关闭   | `memundef_*` | 使用外部输入表示读结果  |

这些变量均加入 `Inputs`，不直接将不确定行为替换为固定常量。

## 4. 硬件状态转换

### 4.1 寄存器

FIRRTL 寄存器转换为 Coq `State` 中的独立字段。

例如：

```
reg_a <= in_a + in_b
```

对应的状态转移关系：

```
reg_0 := bv 8 (in_a + in_b)
```

寄存器当前值通过：

```
(reg_0 s)
```

访问，下一状态由 `step` 计算。

支持普通寄存器和同步复位寄存器。

### 4.2 Memory

Memory 被展开为多个独立的状态变量，每个存储单元对应一个 Coq State 字段。

例如，深度为 4 的 Memory：

```
mem_0_0 : Z;mem_0_1 : Z;mem_0_2 : Z;mem_0_3 : Z
```

读取操作转换为基于地址比较的多路选择逻辑。

写入操作根据以下条件决定是否更新对应存储单元：

```
write_enable = en AND mask AND (addr == index)
```

Memory 的下一状态通过 `step` 更新。

## 5. 当前实现的支持范围

| 功能     | 支持范围                       |
| ------ | -------------------------- |
| 时钟     | 单时钟                        |
| 数据类型   | 已知位宽的 UInt、SInt            |
| 寄存器    | 普通寄存器、同步复位寄存器              |
| 算术运算   | 加、减、乘、除、取余                 |
| 逻辑运算   | AND、OR、XOR、NOT             |
| 比较运算   | EQ、NEQ、LT、LEQ、GT、GEQ       |
| 位操作    | 位提取、位拼接、移位等                |
| Memory | 单写端口，读延迟 0，写延迟 1           |
| 验证事件   | printf、assert、assume、cover |

### 主要限制

1. 不支持多个时钟。

2. 不支持异步复位。

3. 不支持未知位宽的数据类型。

4. 不支持任意派生时钟。

5. Memory 深度必须是 2 的幂，且不超过 1024。

6. Memory 只支持一个写端口，mask 位宽必须为 1。

7. 不支持未展开的多重驱动，需要提前完成相应的 FIRRTL 规范化处理。

8. 不支持未实现的 FIRRTL Operation，遇到不支持的操作会报错。

## 6. 总结

本工具通过解析 FIRRTL MLIR，将硬件电路转换为 Coq 中的状态机模型。

核心转换关系为：

```
FIRRTL MLIR    |    v分析硬件结构    |    v提取 Inputs / State / Outputs    |    v递归转换 FIRRTL 表达式    |    v生成 Coq eval 函数    |    v提取 outputs 和 step    |    v构建 trace 运行轨迹
```

最终实现：

```
eval : Inputs -> State -> Outputs * State
```

从而将硬件电路表示为可供 Coq 进一步分析和形式化验证的数学模型。

**依赖文件：** `Semantics.v`，提供位宽处理、数值语义、多路选择及运行轨迹等基础定义。
