# DPV `src/main.cpp` 实现架构梳理

源文件：`/home/jiongming/desktop/dpv/src/main.cpp`

## 1. 总体定位

参数解析与建模
    │
    ├── 独立模式：合法 stimulus (分为FreeRandom,SmtConstrained)生成 ───────────────► 输出并结束
    │
    ▼
解析原始 BTOR2 Model
    │
    ▼
选择单个 bad property
    │
    ▼
约束恢复 → 属性裁剪/DCE → 常量传播
    │
    ├──────── 启动 Early Bitwuzla ─────────┐
    │                                      │并行竞速
    ▼                                      │
Assume 可满足性检查                         │
    │                                      │
    ▼                                      │
乘法器抽象：发现 → 验证 → 重写             │
    │                                      │
    ▼                                      │
算术简化：候选发现 → 形式证明 → 重写       │
    │                                      │
    ▼                                      │
二次常量传播 + 二次 DCE                    │
    │                                      │
    └──────────────► 最终求解 ◄────────────┘
                          │
                  SAT / UNSAT / UNKNOWN
```

乘法抽象的输出成为算术简化的输入，最后的活动模型再交给最终求解器。[VERIFY: src/main.cpp:1084] [VERIFY: src/main.cpp:1275] [VERIFY: src/main.cpp:2182] [VERIFY: src/main.cpp:2612]


## 3. 主流程

### 3.1 初始化时间体系

程序解析参数、设置日志级别、安装硬超时，然后建立两套预算函数：[VERIFY: src/main.cpp:877]

- `total_remaining_s()`：整次 DPV 调用的剩余时间。[VERIFY: src/main.cpp:889]
- `front_remaining_s()`：预处理阶段的剩余时间。[VERIFY: src/main.cpp:928]
- 未显式设置预处理预算时，如果启用最终求解，预处理默认获得总超时的 60%。[VERIFY: src/main.cpp:910]
- 局部采样和证明时限可以通过 `heuristic_time_scale` 整体缩放，但不能超过共享预算。[VERIFY: src/main.cpp:897] [VERIFY: src/main.cpp:903] [VERIFY: src/main.cpp:936]

```text
整次调用硬超时
└── 共享预处理预算
    └── 单次采样 / 单候选证明 / ABC / SCA 局部时限
```

### 3.2 解析模型

`Model::parse_file()` 将输入 BTOR2 文件解析为原始 `model`。[VERIFY: src/main.cpp:954]

### 3.3 生成 stimulus相关(会直接退出)

如果是dpv::InputSource::FreeRandom
执行：
dpv::SimResult sim = dpv::simulate(model, opt);
        assignments = std::move(sim.legal_assignments);

1. dpv::simulate(model, opt) 按配置 opt 对模型 model 生成随机输入并进行仿真。
  2. 仿真时会过滤掉不满足 BTOR2 约束的输入，并记录合法输入、违规属性及统计信息。
  3. 返回的 SimResult 保存合法输入数量、拒绝次数、超时状态和 legal_assignments 等结果。
  4. std::move(sim.legal_assignments) 将合法输入集合的内部资源转移给 assignments，避免复制大量数据。
  5. 移动后 assignments 获得所有合法输入，而 sim.legal_assignments 仍有效但其内容处于未指定状态，通常不应继续使用。

如果是dpv::InputSource::SmtConstrained
执行：
dpv::SmtSampleResult sample =
            dpv::sample_constraint_legal(model, opt);
        assignments = std::move(sample.assignments);

1. dpv::sample_constraint_legal(model, opt) 使用 Bitwuzla SMT 求解器寻找满足 model 中全部约束的输入赋值。
  2. 它会根据 opt 指定的样本数量、随机种子和时间限制生成尽可能多样且互不相同的合法输入。
  3. 不参与约束计算的输入会被填入随机值，从而增加样本的多样性。
  4. 返回的 SmtSampleResult 包含输入赋值、求解次数、约束是否可满足以及是否超时等信息。
  5. std::move(sample.assignments) 将生成的输入赋值高效地转移到 assignments 中，避免复制整个二维数组。

### 3.3 生成 stimulus相关-ai

指定 `--generate-stimulus` 时，程序进入独立工具模式：

- `random` 调用 `simulate()` 收集满足 constraint 的输入帧。[VERIFY: src/main.cpp:971]
- `bitwuzla` 调用 `sample_constraint_legal()` 生成合法输入。[VERIFY: src/main.cpp:989]
- 输入帧写入 stdout 或指定文件后立即返回，不执行后续 DCE、抽象、简化或求解。[VERIFY: src/main.cpp:960] [VERIFY: src/main.cpp:1006]

### 3.3 选择属性与检查求解后端

DPV 是单属性驱动器。程序按照原始 bad 声明顺序检查 `--property`，保存 `original_bad_id`；后续即使模型重编号，输出仍使用原始 ID。[VERIFY: src/main.cpp:1051]

程序根据最终求解器、预处理证明器和 frontier 证明器判断是否需要 AIG/ABC；请求 ABC 但构建中不可用时直接报错。[VERIFY: src/main.cpp:1024] [VERIFY: src/main.cpp:1036]

### 3.4 活动模型状态机

模型变换不是原地修改，而是由 `cur` 指向当前模型：

```cpp
const dpv::Model *cur = &model;
```

每次重写都生成 BTOR2 文本、重新解析为新 `Model`，然后更新 `cur`。[VERIFY: src/main.cpp:1084] [VERIFY: src/main.cpp:1099]

```text
model               原始模型，始终保留
pruned              初始属性裁剪/DCE
case_recovered      属性内嵌 guard 恢复
folded              初始常量传播
abstracted          乘法器抽象结果
simplified          已证明的算术简化结果
post_folded         重写后二次常量传播
post_pruned         重写后二次 DCE
```

[VERIFY: src/main.cpp:1088] [VERIFY: src/main.cpp:2512] [VERIFY: src/main.cpp:2534]

当 `cur` 前进后，已经失效的大模型会被 `reset()` 释放，以降低后续 fork 求解子进程继承的地址空间。[VERIFY: src/main.cpp:1093] [VERIFY: src/main.cpp:2495]

### 3.5 约束恢复

程序先在原始图上识别选定 bad 中嵌入的 case guard，并将：

```text
constraints ∧ (guard ∧ residual_bad)
```

等价改写为：

```text
(constraints ∧ guard) ∧ residual_bad
```

[VERIFY: src/main.cpp:1107]
识别 formal frontend 把“执行条件/分支条件”包在 bad 属性里的情况，将该条件从 bad 表达式中剥离并提升为 BTOR2 constraint，让后续分析在更明确的合法输入空间约束中运
  行。
### 3.6 DCE锥取

emit_live_model(model, dropped, args.property) 以指定的 bad 属性、全部 constraints 和全部主输入作为存活根节点，其他 bad 及无关 output 不进入当前单属性问题。
  它利用 BTOR2 节点依赖 ID 小于当前节点的特性，从最大 ID 向前扫描，将存活节点的 sort 和操作数递归标记为存活。
  随后按原始顺序重新输出存活节点、分配连续的新 ID、修正参数引用，并合并位宽相同的重复 sort。
  函数将删除或合并的行数写入 dropped，并把裁剪后的单属性 BTOR2 模型文本返回给 live。

1. 根据选定 property 做 cone pruning；即使传入 `--no-dce`，其他 property 的裁剪仍强制执行。[VERIFY: src/main.cpp:1127]
2. 应用 constraint recovery，再次 DCE。[VERIFY: src/main.cpp:1146]
3. 验证活动模型恰好只剩一个 bad。[VERIFY: src/main.cpp:1175]
4. 传播属性选择产生的常量和别名，再清除不可达分支。[VERIFY: src/main.cpp:1179]

### 3.7 DCE之后，再做一次约束恢复

1. if (pre_dce_recovered) 表示只有在原始模型中预先发现了可恢复的 case guard 时，才执行约束恢复流程。
  2. 局部变量 recovered 用来记录在当前 DCE 裁剪后模型 *cur 中重新识别出的 guard 数量。
  3. emit_constraint_recovered_model(*cur, recovered) 尝试把当前 selected bad 内嵌的 guard 提升为 BTOR constraint，并生成新的 BTOR2 文本。
  4. used_pre_dce_fallback 通过比较 DCE 前后的 guard 数量，判断 DCE 是否改变了 wrapper 的可识别结构。
  5. 如果两次识别数量不同，代码就放弃当前恢复结果，改用原始模型上预先生成的 pre_dce_recovered_text。
  6. 回退时还会将 recovered 恢复为 pre_dce_recovered，保证统计信息与实际采用的模型一致。
  7. Model::parse_string(text) 将恢复后的 BTOR2 文本解析为临时模型 lifted。
  8. emit_live_model(lifted, dropped) 对该模型再次执行活性裁剪，删除约束提升后遗留的 wrapper 和不可达逻辑。
  9. 裁剪后的文本被解析为 case_recovered，并通过 cur = &*case_recovered 成为后续常量折叠、抽象和求解使用的当前模型。
  10. 最后释放已被替代的 pruned 模型，并把最新 BTOR2 文本保存到 transformed_btor2，供后续导出或继续变换。

### 3.8 常量传播

1. 这段代码在单属性裁剪和 constraint recovery 之后，对当前模型 *cur 进行常量传播。
  2. 选择单个 property 后，相关 mode 或 case guard 可能已经被约束成确定的 0 或 1。
  3. emit_constant_folded_model() 根据这些确定值计算可推导的常量，并将等价节点改写为别名。
  4. constants_folded 记录被推导为常量的节点数量，aliases_folded 记录被折叠为其他节点引用的数量。
  5. 如果两项计数都为零，说明模型没有发生变化，因此代码不会创建新的中间模型。
  6. 如果发生折叠，代码将生成的 BTOR2 文本解析成临时模型 f。
  7. 随后调用 emit_live_model() 再做一次 DCE，删除因常量条件确定而不可达的 ITE 分支及其依赖逻辑。
  8. 清理后的模型被解析并保存到 folded，同时 cur 更新为指向这个最新模型。
  9. case_recovered.reset() 和 pruned.reset() 释放已经被新模型取代的中间模型，以降低后续求解和子进程继承的内存占用。
  10. 最后保存最新的 BTOR2 文本并输出统计日志，确保不可达的乘法器等逻辑不会进入后续抽象、算术简化或最终求解阶段。

### 3.6 Early Solve 竞速

初始 fold 后，程序可以 fork 一个 Bitwuzla 子进程，让它与剩余预处理并行竞速。[VERIFY: src/main.cpp:1205] [VERIFY: src/main.cpp:1235]

- 子进程先得出结论时，主流程立即返回 SAT/UNSAT。[VERIFY: src/main.cpp:1220] [VERIFY: src/main.cpp:1273]
- 抽象或简化先成功重写模型时，程序停止仍在求解旧模型的子进程。[VERIFY: src/main.cpp:2172] [VERIFY: src/main.cpp:2372]
- 如果最终求解前模型没有变化，portfolio 可以接管已运行的子进程，避免重新求解。[VERIFY: src/main.cpp:2669]

完成属性裁剪和常量折叠后，DPV 默认 fork 一个 Bitwuzla 子进程直接求解当前模型，同时主进程继续执行乘法抽象和算术简化。由于后续正常重写都经过证明且保持属性等价，因此子
  进程对旧模型得到的 SAT/UNSAT 结论，对后续重写后的模型仍然有效。若子进程先完成，就立即采用其结论；若预处理先成功简化模型，则可停止旧模型上的子进程并求解新模型。对于没有发现任何可
  抽象或可简化结构的常见情况，这相当于执行“解析 → DCE → Bitwuzla 直接求解”，避免预处理延迟最终结论。

### 3.7 Assume 可满足性检查

`check_assume_feasible()` 检查所有 BTOR constraints 的合取。[VERIFY: src/main.cpp:1250]

- `INFEASIBLE`：合法输入区域为空，属性空成功，返回 UNSAT/20。[VERIFY: src/main.cpp:1259]
- `FEASIBLE`：继续后续流程。[VERIFY: src/main.cpp:1266]
- 超过预处理预算：不做空成功判断，继续执行。[VERIFY: src/main.cpp:1268]

### 3.8 乘法器抽象

函数：
std::vector<dpv::MulAbstraction> cands =
          dpv::find_mul_abstractions(*cur, ao, &astat);
功能：
 1. 这行代码调用 find_mul_abstractions()，在当前活动模型 *cur 中搜索可以被字级乘法替换的 RTL 优化乘法结构。
  2. *cur 是经过属性裁剪、constraint recovery 和常量折叠后的单属性模型，因此搜索范围主要集中在当前 bad 的有效逻辑锥中。
  3. 参数 ao 指定候选发现策略，包括是否启用代数识别、SCA 采样识别、采样数量、随机种子、工作线程数和时间限制。
  4. 在代数模式下，函数会寻找可由分配律证明的共享操作数乘积和，例如将 X0×B + (X1×B)<<k 识别为组合操作数与 B 的乘法。
  5. 在 SCA 模式下，函数会生成满足 constraints 的输入样本，仿真模型中的乘法节点和 RTL 输出，并依据数值关系提名潜在对应结构。
  6. 启用 steering 时，函数还会主动生成能够激活未被普通样本覆盖的乘法器或数据路径的输入，以减少候选漏检。
  7. 每个发现结果被封装为 dpv::MulAbstraction，其中记录 spec 乘法节点、RTL 输出节点、候选操作数、位宽、输出移位和候选类型等重写信息。
  8. 所有候选组成 std::vector<dpv::MulAbstraction> 并赋给 cands，但这些候选此时通常只是“值得证明”的提名，并不都能立即修改模型。
  9. 第三个参数 &astat 用于返回发现过程的统计信息，包括检查的乘法器数量、代数与位级候选数量、合法样本、steering 结果和超时状态。
  10. 这行代码的最终目的是先低成本定位可能等价于 A'×B' 的复杂 RTL 乘法逻辑，再由穷举、ArisCA 或 RevSCA 等后续步骤完成严格验证并授权抽象重写。
这段注释说明：当外层并行处理多个 property、系统资源紧张时，设置了硬超时的采样器可能在期限内连一个有效输入样本都来不及生成。没有样本会同时导致 SCA 乘法候选发现和后续等价算术对发现
  失效，因此代码会针对这种明确的“采样饥饿”情况增加预算并重试一次。重试是有界的，不会无限占用预处理时间。正常的“采样成功但没有候选”以及“constraints 本身不可满足”不会触发该重试，原结
  果保持不变。
把抽象发现阶段生成的合法输入样本转移到 abstraction_stimulus，并记录普通采样或定向 steering 是否因超时而出现资源饥饿。随后根据实际执行路径输出统计信息，区分严格代数快速匹
  配、禁用 SCA 时无候选，以及 SCA 对乘法器、常量列、退化目标和过大分组的筛选情况。最后它报告 steering 补充样本和超时状态，并汇总最终候选总数及其中代数候选、位级候选各有多少。

这一阶段把门级或 PPA 优化后的 RTL 乘法结构替换为字级 `A' * B'`。[VERIFY: src/main.cpp:1275]

1. **候选发现**：`find_mul_abstractions()` 使用代数结构识别和/或合法输入采样发现 SCA 候选；采样结果可以供后续 simplify 重用。[VERIFY: src/main.cpp:1282] [VERIFY: src/main.cpp:1304]
2. **稀有 guard 恢复**：普通采样找不到候选时，从 oracle cut-point 提取 guard 集，筛除不活跃或与乘法值不匹配的集合，再临时固定高排名 guard 重新发现候选。[VERIFY: src/main.cpp:1365] [VERIFY: src/main.cpp:1478] [VERIFY: src/main.cpp:1636]

释说明一种乘法候选发现的补救机制：门级乘法结果可能只在多层 ite(guard, product, oracle-slice) 的特定分支上可见，而普通合法输入采样很难同时满足所有 guard，导致候选发现无法把
  spec 乘法值与 RTL 输出匹配起来。为解决这个问题，程序从 oracle cut-point 中挑选宽位且自身不含字级乘法的计算分支，临时将对应 guard 固定为 assumptions，然后在这个受限模型上重新运行
  候选发现。重试模型保留原始节点 ID，因此找到的候选仍可应用于当前工作模型。候选之后仍必须通过穷举、ArisCA 或 RevSCA 的严格证明才能触发重写，所以错误提名只会浪费有限时间，不会破坏验
  证可靠性。

3. **候选证明**：代数候选可由分配律直接接受；其他候选依次经过 cone 提取、低位为零证明、全空间穷举、ArisCA 和可选 RevSCA。[VERIFY: src/main.cpp:1716] [VERIFY: src/main.cpp:1729] [VERIFY: src/main.cpp:1747] [VERIFY: src/main.cpp:1773] [VERIFY: src/main.cpp:1911] [VERIFY: src/main.cpp:2019]

释说明：如果 RTL 结构是多个共享操作数 B 的乘积移位后求和，例如 S = Σ((X_i × B) << k_i)，那么根据分配律可以将它严格合并为 A × B，其中 A = Σ(X_i << k_i)。这种代数恒等关系本身
  已经足以证明等价，因此默认无需调用 SCA 验证器，程序可以直接进行字级乘法抽象。若启用 --verify-algebraic，程序还会对提取出的乘法 cone 额外运行 ArisCA 或 RevSCA。额外验证只适用于各
  个 X_i 对应的位段互不重叠、能够干净拼成操作数 A 的情况。

4. **模型重写**：`emit_abstracted_model()` 重定向消费者、生成新 BTOR2 并更新 `cur`；严格代数模式迭代扫描直至结构固定点或达到轮数上限。[VERIFY: src/main.cpp:2095] [VERIFY: src/main.cpp:2110]

默认只有被证明的候选才能改写；`--risky-merge` 允许未证明、但也未被反驳的候选进入不可靠改写。[VERIFY: src/main.cpp:2067]

### 3.9 已证明的算术简化

这一阶段处理 add、mul、udiv 和 urem 等算术结构。[VERIFY: src/main.cpp:2182]

1. `find_equivalent_pairs()` 使用 constraint-legal stimulus 发现可能等价的浅层/深层算术对，重用抽象阶段保留的输入帧，并对采样资源饥饿进行一次有界重试。[VERIFY: src/main.cpp:2229] [VERIFY: src/main.cpp:2233] [VERIFY: src/main.cpp:2250]
2. `prove_and_simplify()` 对候选进行形式证明；通过证明的关系才用于 operator merge、frontier cut、变量移位约束或除法降级等重写。[VERIFY: src/main.cpp:2293] [VERIFY: src/main.cpp:2443]

如果生成新模型，代码更新 `cur`，并释放之前的抽象、fold、recovery 和 pruning 模型。[VERIFY: src/main.cpp:2495]

### 3.10 重写后清理与导出

算术重写可能使 selector 变为常量，也会使原门级乘法器 cone 不可达，因此程序执行：

- 二次常量传播。[VERIFY: src/main.cpp:2509]
- 二次 DCE；`--no-dce` 可以关闭这一轮。[VERIFY: src/main.cpp:2529]
- `--cut` 输出最后一次 transformation 的文本。[VERIFY: src/main.cpp:2550]
- `--emit` 输出最终求解器实际看到的单属性模型。[VERIFY: src/main.cpp:2559]
- `--emit-miter-aig` 输出二进制 AIGER miter 和输入位映射。[VERIFY: src/main.cpp:2580]

### 3.11 最终求解

最终模型由 `active = *cur` 固化。[VERIFY: src/main.cpp:2556]

`portfolio_solve_bad()` 根据配置运行 Bitwuzla、bitblast→可选 ABC→Kissat，或者让两个后端竞速。[VERIFY: src/main.cpp:2623] [VERIFY: src/main.cpp:2679]

| 结果 | 输出 | 退出码 |
|---|---|---:|
| SAT | `satisfiable`，可打印 witness | 10 |
| UNSAT | `unsatisfiable` | 20 |
| UNKNOWN | `unknown` | 0 |
| 异常 | stderr 错误 | 1 |

[VERIFY: src/main.cpp:2689] [VERIFY: src/main.cpp:2716]

关闭最终求解时，前面的抽象和简化不会被当作性质结论，程序输出 `unknown`。[VERIFY: src/main.cpp:2711]

## 4. 关键数据流

```text
原始 BTOR2 文件
      │ parse_file
      ▼
original model ───────────────────────────────┐
      │                                      │
      │ 只读保留：原始 property 编号、witness │
      ▼                                      │
cur → pruned → recovered → folded             │
                         │                    │
                         ├── Early Solver     │
                         │                    │
                         ▼                    │
                    abstracted                │
                         │                    │
                         ▼                    │
                    simplified                │
                         │                    │
                         ▼                    │
                 post_folded → post_pruned    │
                         │                    │
                         ▼                    │
                       active                 │
                         │                    │
                         ▼                    │
                    final solver              │
                         │                    │
                         └── witness 映射回原模型 ─┘
```

SAT witness 使用原始 `model` 的输入声明打印，因为可靠重写保持主输入顺序，避免内部 DCE 或重编号泄漏给用户。[VERIFY: src/main.cpp:2691]

## 5. 架构特点与边界

- `main.cpp` 是控制层，核心算法分别位于 `model`、`dce`、`abstraction`、`analysis`、`guarantee` 和 `portfolio` 等模块中。[VERIFY: src/main.cpp:49] [VERIFY: src/main.cpp:56]
- 正常流程始终只携带一个 selected bad；原始模型作为编号和 witness 映射基准保留。[VERIFY: src/main.cpp:1051] [VERIFY: src/main.cpp:1175]
- 候选发现与候选证明分离：采样负责提名，形式验证负责授权重写。[VERIFY: src/main.cpp:1306] [VERIFY: src/main.cpp:1762] [VERIFY: src/main.cpp:2240] [VERIFY: src/main.cpp:2443]
- `--risky-merge` 是可靠性边界：它允许未获证明的抽象或 merge，开启后不再具有默认流程相同的 soundness 保证。[VERIFY: src/main.cpp:366] [VERIFY: src/main.cpp:2067] [VERIFY: src/main.cpp:2380]
- 文件的主要复杂度来自 CLI 解析、流程编排、抽象候选恢复、外部证明器适配和模型生命周期管理集中于同一个入口文件。[VERIFY: src/main.cpp:414] [VERIFY: src/main.cpp:877] [VERIFY: src/main.cpp:1365] [VERIFY: src/main.cpp:1762]

## 6. 总结

`main.cpp` 通过 `cur` 指针和一组具有明确生命周期的 `optional<Model>`，把“单属性裁剪—可靠预处理重写—竞速求解—最终判定”组织成一条受统一时间预算约束的模型演化流水线。[VERIFY: src/main.cpp:1084] [VERIFY: src/main.cpp:2612]
