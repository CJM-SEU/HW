# DPV Constraint Recovery 具体实现解读

相关代码：

- `src/main.cpp:1107-1173`
- `src/dce.cpp:16-168`
- `src/dce.cpp:503-588`
- `src/dce.hpp:38-61`

## 1. 核心功能

这段代码识别 formal frontend 把“执行条件/分支条件”包在 bad 属性里的情况，将该条件从 bad 表达式中剥离并提升为 BTOR2 `constraint`，让后续分析在更明确的合法输入空间中运行。[VERIFY: src/main.cpp:1107] [VERIFY: src/dce.cpp:503]

原始形式：

```text
constraints ∧ (guard ∧ residual_bad)
```

恢复后：

```text
(constraints ∧ guard) ∧ residual_bad
```

两种形式完全等价，因此该变换保持选定属性的可满足性。[VERIFY: src/dce.hpp:38]

## 2. 调用处的作用

```cpp
size_t pre_dce_recovered = 0;
std::string pre_dce_recovered_text;

if (args.constraint_recovery)
{
  pre_dce_recovered_text =
      dpv::emit_constraint_recovered_model(
          model, pre_dce_recovered, args.property);
}
```

三个参数分别是：

- `model`：尚未经过 DCE 和常量折叠的原始 BTOR2 模型。
- `pre_dce_recovered`：输出参数，记录成功提升的 guard 数量。
- `args.property`：需要处理的 bad 属性在声明顺序中的下标。

[VERIFY: src/main.cpp:1116] [VERIFY: src/dce.cpp:503]

识别必须预先在原始模型上进行，因为 DCE 或常量折叠可能破坏 frontend 生成的“左边是 guard、右边是原始性质”这一方向性结构。[VERIFY: src/main.cpp:1107]

## 3. `emit_constraint_recovered_model()` 实现步骤

### 3.1 检查 property 选择

函数首先将 `recovered` 清零，并检查属性下标是否合法：

```cpp
recovered = 0;

if (keep_bad < -1 ||
    (keep_bad >= 0 &&
     static_cast<size_t>(keep_bad) >= m.bads().size()))
  throw ...;
```

如果 `keep_bad == -1`，则要求输入模型已经只包含一个 bad，否则函数无法确定应该恢复哪个属性。[VERIFY: src/dce.cpp:507]

### 3.2 沿 bad 的右侧主干提取 guard

```cpp
std::vector<int64_t> conjuncts =
    selected_bad_conjuncts(
        m, m.bads()[selected]->args[0]);
```

[VERIFY: src/dce.cpp:516]

`selected_bad_conjuncts()` 识别两种 formal frontend 常见结构。

#### 直接 AND

```text
guard1 ∧ (guard2 ∧ residual_bad)
```

函数沿 AND 的右操作数继续遍历：

```cpp
if (literal > 0 && l->tag == BTOR2_TAG_and)
{
  result.push_back(
      normalize_bad_literal(m, l->args[0]));
  literal = l->args[1];
  continue;
}
```

最终获得：

```text
conjuncts = [guard1, guard2, residual_bad]
```

[VERIFY: src/dce.cpp:122]

函数不会递归拆开左侧 guard。即使 `guard1` 本身是大型合取，也会将其作为完整条件保留，避免误拆其内部控制或数据通路。[VERIFY: src/dce.cpp:103]

#### 否定的 OR

Formal frontend 也可能将蕴含关系写成：

```text
¬(¬guard ∨ property_ok)
```

根据德摩根律：

```text
¬(¬guard ∨ property_ok)
= guard ∧ ¬property_ok
```

对应处理代码为：

```cpp
if (literal < 0 && l->tag == BTOR2_TAG_or)
{
  result.push_back(
      normalize_bad_literal(m, -l->args[0]));
  literal = -l->args[1];
  continue;
}
```

它将左侧恢复成 `guard`，将右侧恢复成真正的违规条件 `¬property_ok`。[VERIFY: src/dce.cpp:128]

### 3.3 消除布尔包装

`normalize_bad_literal()` 清除不改变表达式含义的 frontend 展示层包装：[VERIFY: src/dce.cpp:69]

- 显式 `not`：通过切换 BTOR2 有符号 ID 的正负号归一化。
- `true ∧ x`：归一化为 `x`。
- `x ∧ true`：归一化为 `x`。

例如：

```text
true ∧ ¬(¬guard ∨ property_ok)
```

会被归一化并拆分为：

```text
guard
¬property_ok
```

提取结束后，值恒为 `true` 的合取项也会被删除。[VERIFY: src/dce.cpp:136]

### 3.4 防止错误识别普通 gated property

提取出的最后一个元素被视为原始性质：

```cpp
const int64_t residual_bad = conjuncts.back();
conjuncts.pop_back();
```

剩余元素被视为待提升的 guards。[VERIFY: src/dce.cpp:525]

以下两个表达式虽然逻辑上都是合取，但架构含义不同：

```text
case_guard ∧ large_residual_property   // 希望恢复
large_datapath_failure ∧ tiny_enable   // 不应将 large failure 提升为 constraint
```

函数分别计算 residual 和各 guard 的结构 cone 大小：

```cpp
size_t residual_cone =
    wrapper_cone_size(m, residual_bad);

size_t largest_antecedent_cone = ...;
```

如果 residual 的 cone 小到不足最大前置项的一半，则拒绝恢复：

```cpp
if (residual_cone * 2 < largest_antecedent_cone)
  return {};
```

[VERIFY: src/dce.cpp:527]

`wrapper_cone_size()` 使用栈遍历表达式依赖图，并以 `unordered_set` 去重，统计从某节点可达的结构节点数量。[VERIFY: src/dce.cpp:153]

如果 residual 本身只是布尔常量 `0/1`，函数也会拒绝恢复。[VERIFY: src/dce.cpp:533]

上述检查是用于判断“是否像 frontend wrapper”的结构启发式；一旦识别成功，后续变换本身是精确等价的。

### 3.5 重新输出 BTOR2 模型

函数遍历原模型所有节点，为输出模型重新分配连续 ID，并通过 `mapped` 保存旧 ID 到新 ID 的映射。[VERIFY: src/dce.cpp:535] [VERIFY: src/dce.cpp:544]

遇到未选中的 bad 时直接跳过：

```cpp
if (bad_index++ != selected)
  continue;
```

因此输出模型只保留当前选中的属性。[VERIFY: src/dce.cpp:557]

遇到选中的 bad 时，原 guard 被输出成 constraint：

```cpp
for (int64_t guard : conjuncts)
  os << ++counter
     << " constraint "
     << map_arg(guard)
     << " dpv_recovered_case_guard_..."
     << '\n';
```

然后只把 residual 输出成新的 bad：

```cpp
os << bad_id
   << " bad "
   << map_arg(residual_bad)
   << " ; residual selected property\n";
```

最后通过：

```cpp
recovered = conjuncts.size();
```

记录被提升的 guard 数量。[VERIFY: src/dce.cpp:560]

## 4. BTOR2 示例

假设 frontend 生成以下简化模型：

```btor
1 sort bitvec 1
2 input 1 mode
3 input 1 result_wrong
4 and 1 2 3
5 bad 4 selected_bad
```

其含义为：

```text
bad = mode ∧ result_wrong
```

只有 `mode = 1` 且 `result_wrong = 1` 时，bad 才可达。

恢复函数识别出：

```text
guard        = mode
residual_bad = result_wrong
```

然后生成逻辑上类似的模型：

```btor
1 sort bitvec 1
2 input 1 mode
3 input 1 result_wrong
4 constraint 2 dpv_recovered_case_guard_0
5 bad 3 ; residual selected property
```

变换前的求解条件为：

```text
mode ∧ result_wrong
```

变换后的求解条件为：

```text
constraint(mode) ∧ bad(result_wrong)
= mode ∧ result_wrong
```

因此两者的 SAT/UNSAT 结果相同。

## 5. 提升 guard 的实际价值

变换前：

```text
bad
└── AND
    ├── mode guard
    └── large arithmetic comparison
```

后续乘法器候选发现或等价采样看到的是一个受条件包裹的属性；随机合法输入可能大量落在 `mode=0` 区域，使真正的数据通路不活跃。

变换后：

```text
constraint: mode = 1

bad
└── large arithmetic comparison
```

合法输入生成、候选采样、乘法器发现和最终求解可以直接在 `mode=1` 的有效 case 内工作，而 bad 本身保留为原始算术违规条件。[VERIFY: src/main.cpp:1101] [VERIFY: src/main.cpp:1250] [VERIFY: src/main.cpp:1275]

## 6. `pre_dce_recovered_text` 的回退机制

预识别完成后，主流程先对选定 property 执行 DCE，然后尝试在裁剪后的模型上重新应用恢复：

```cpp
std::string text =
    emit_constraint_recovered_model(*cur, recovered);
```

[VERIFY: src/main.cpp:1146]

正常情况下使用 DCE 后生成的恢复模型，以保持较小的图结构和稳定的 solver stimulus。

如果 DCE 后识别出的 guard 数量与 DCE 前不同：

```cpp
bool used_pre_dce_fallback =
    recovered != pre_dce_recovered;
```

则说明图变换可能影响了 wrapper 结构识别，此时回退到原始图上已经生成好的 `pre_dce_recovered_text`。[VERIFY: src/main.cpp:1151]

之后程序重新解析恢复模型，并再次执行 DCE，得到最终的 `case_recovered` 活动模型。[VERIFY: src/main.cpp:1157]

该设计同时满足：

1. 在原始图上预识别，不受 DCE 或常量折叠影响。
2. 尽量在裁剪后的图上重写，以获得更小、更稳定的求解模型；识别结果不一致时使用原始图恢复结果兜底。

## 7. 总结

`emit_constraint_recovered_model()` 沿选定 bad 的右侧表达式主干识别 frontend 包装的 case guards，经过布尔归一化和结构方向检查后，将 guards 输出为 BTOR constraints、将剩余性质输出为唯一 bad；调用方同时保存 DCE 前结果作为回退，从而兼顾识别稳定性、模型规模和求解效率。[VERIFY: src/dce.cpp:503] [VERIFY: src/main.cpp:1146]
