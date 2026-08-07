# DPV 源码高效阅读计划（重点：`src/`）

> 目标：不是逐文件“从头看到尾”，而是在 10 个阅读单元内建立可运行、可验证、可复述的 DPV 心智模型；最终能够沿一条 property 的生命周期，解释它如何被解析、裁剪、抽象、证明化简并交给求解器。
>
> 适用代码版本：当前 `/home/jiongming/desktop/dpv` 工作区。文中的 `[VERIFY: ...]` 是建议现场核对的源码锚点。

## 1. 先明确阅读终点

完成本计划后，你应当能够独立回答以下问题：

1. 一个 BTOR2 节点在 DPV 中如何表示、按什么顺序求值，负节点 ID 表示什么？[VERIFY: src/model.hpp:17] [VERIFY: src/eval.hpp:18]
2. 默认 CLI 流程为何是“约束恢复 → 单 property DCE → 常量折叠 → vacuity check → multiplier abstraction → verified simplification → final solve”？[VERIFY: src/main.cpp:1] [VERIFY: src/main.cpp:1118]
3. 为什么 sampling 只能提名候选，不能授权 rewrite；真正的 soundness gate 在哪里？[VERIFY: src/analysis.hpp:1] [VERIFY: src/main.cpp:1769]
4. algebra、SCA、exhaustive、ArisCA、RevSCA 分别解决哪一段 multiplier abstraction 问题？[VERIFY: src/abstraction.hpp:81] [VERIFY: src/main.cpp:1718]
5. `guarantee.cpp` 如何把 add/mul/div 的候选关系变成经过证明的 cut、constraint 或模型重写？[VERIFY: src/guarantee.hpp:108] [VERIFY: src/main.cpp:2183]
6. Bitwuzla 路径与 AIG+ABC+Kissat 路径如何分工，`both` 如何竞争并回收子进程？[VERIFY: src/portfolio.hpp:28] [VERIFY: src/subprocess.hpp:1]
7. SAT witness 如何从 solver model 映射回原始 BTOR2 input node id？[VERIFY: src/witness.hpp:27] [VERIFY: src/main.cpp:1225]

建议在整个阅读过程中维护一个 `notes/` 目录（你审查本计划后再创建），包含：

- `pipeline.md`：主流程和模型版本变化；
- `types.md`：核心结构体字段与所有权；
- `proof-obligations.md`：每类 rewrite 的候选条件、证明条件和产物；
- `questions.md`：暂时不能从代码回答的问题；
- `experiments.md`：命令、输入模型、输出和结论。

## 2. 总体路线

```text
CLI/main
   │
   ▼
Model ──► eval/sim ──► sample/analysis
   │                         │
   ├──► DCE/constant fold    ├──► abstraction candidate
   │                         │           │
   │                         │           ├──► exhaustive/AIG
   │                         │           ├──► ArisCA/RevSCA
   │                         │           └──► abstracted BTOR2
   │                         │
   │                         └──► equivalence candidates
   │                                     │
   │                                     ▼
   │                              guarantee proof/rewrite
   │                                     │
   ├─────────────────────────────────────┘
   ▼
Bitwuzla solve  ◄── portfolio ──► AIG/ABC/Kissat solve
   │
   ▼
verdict / witness
```

这条路线对应 `main()` 实际编排，而不是按文件名字推测。[VERIFY: src/main.cpp:877] [VERIFY: src/main.cpp:1084] [VERIFY: src/main.cpp:2614]

推荐总投入约 20～28 小时：基础链路 6～8 小时，抽象 4～6 小时，verified simplification 7～10 小时，求解/并发/回顾 3～4 小时。时间是阅读配额，不是代码复杂度结论；遇到不能复述的阶段应延长，而不是赶进度。

## 3. 阅读方法：每个单元都执行同一个闭环

每个阅读单元按以下顺序进行：

1. 先读 `.hpp`：只记录输入、输出、状态和契约。
2. 再读对应 `.cpp` 的公开 API 实现，沿调用向下展开；不要先读所有静态 helper。
3. 找 2～4 个紧贴该模块的 unit test，把测试输入手算一次。
4. 运行窄测试：`build/dpv_ut "<doctest filter>"`；不确定 filter 时先执行 `build/dpv_ut --list-test-cases`。
5. 用 `build/dpv -v ...` 跑一个 CLI 小模型，记录日志阶段与源码位置。
6. 合上代码，用 5～10 句话复述：输入是什么、做了什么、soundness 依赖什么、输出给谁。

统一完成标准：能画出数据流；能指出至少三个源码锚点；能解释一个正常路径和一个失败/UNKNOWN 路径；能找到相应测试。

## 4. 单元 0：建立地图，不进入算法细节（1 小时）

### 阅读顺序

1. `README.md` 的 default flow、exit code、quick start。
2. `doc/heuristics.md`：先只看目录和每节首尾，不追细节。
3. `doc/soundness_checking.md`：理解项目怎样看待 soundness 回归。
4. `CMakeLists.txt:119-293`：确认 `dpvcore` 模块、外部库与测试注册。[VERIFY: CMakeLists.txt:119] [VERIFY: CMakeLists.txt:127] [VERIFY: CMakeLists.txt:265]
5. `src/main.cpp:1-22`：把文件头的 pipeline 注释抄到 `pipeline.md`。[VERIFY: src/main.cpp:1]

### 产出

- 一页模块表：文件、职责、上游、下游、对应测试。
- 标出三类代码：模型语义层、证明/重写层、solver/backend 层。

### 验收问题

- 为什么不能直接从 `main.cpp` 第 1 行一路读到第 2721 行？
- 哪些模块改变 BTOR2 模型，哪些模块只分析或求解？

## 5. 单元 1：BTOR2 模型与精确语义（2～3 小时）

### 必读文件

1. `src/model.hpp` 全文，随后读 `src/model.cpp` 全文。
2. `src/eval.hpp` 全文，随后读 `src/eval.cpp` 全文。
3. `test/ut/test_eval.cpp` 全文；补读 `test/ut/test_sim.cpp:222` 的时序模型拒绝测试。[VERIFY: test/ut/test_eval.cpp:25] [VERIFY: test/ut/test_sim.cpp:222]

### 重点追踪

- `Model::parse_stream()` 如何建立按 ID 索引的节点表、inputs/bads/constraints/outputs 与 `eval_order`。[VERIFY: src/model.cpp:24]
- `width()`、`cone_of_influence()`、`logic_levels()` 分别支持后续哪些算法。[VERIFY: src/model.cpp:150] [VERIFY: src/model.cpp:175] [VERIFY: src/model.cpp:189]
- `arg_value()` 对负 ID 的解释，以及 `bvops::wrap()` 如何保持固定宽度二进制补码语义。[VERIFY: src/eval.hpp:18] [VERIFY: src/eval.hpp:32]
- `eval_node()` 对算术、比较、slice/concat/extend/ite 和除零的实际处理；逐项和测试对照。[VERIFY: test/ut/test_eval.cpp:36] [VERIFY: test/ut/test_eval.cpp:68] [VERIFY: test/ut/test_eval.cpp:162]

### 动手实验

从 `test/ut/test_eval.cpp` 选一个最小 BTOR2 字符串：画节点 DAG，写出 eval order，并手算一次所有节点值，再运行对应 test case。

### 产出与验收

- `types.md` 中画出 `Model` 所有权：parser、裸 `Btor2Line*` 视图、move-only 生命周期。
- 能解释为何节点参数只指向较小 ID，以及这如何使顺序求值成立。[VERIFY: src/model.hpp:29]
- 能解释为何缓存不能只用节点指针做跨 rewrite 身份标识。[VERIFY: src/model.hpp:39]

## 6. 单元 2：simulation、合法 stimulus 与候选关系（2～3 小时）

### 阅读顺序

1. `src/sim.hpp` → `src/sim.cpp` → `test/ut/test_sim.cpp`。
2. `src/sample.hpp` → `src/sample.cpp` → `test/ut/test_sample.cpp`。
3. `src/analysis.hpp` → `src/analysis.cpp` → `test/ut/test_mul_equiv.cpp`。
4. 最后读 `src/parallel.hpp` 与 `test/ut/test_parallel.cpp`。

### 建立三种概念边界

- random simulation：约束非法 draw 被拒绝，目标数指合法 pattern 数，且固定 seed 的结果不依赖 worker 数。[VERIFY: src/sim.hpp:1] [VERIFY: test/ut/test_sim.cpp:64] [VERIFY: test/ut/test_sim.cpp:114]
- SMT sampling：Bitwuzla 生成 constraint-legal assignment，通过 steering 与 blocking 增加多样性。[VERIFY: src/sample.hpp:1] [VERIFY: test/ut/test_sample.cpp:31]
- equivalence analysis：对指定 op 的输出列做 slice/shift 关系匹配，它只产生 candidate，不构成证明。[VERIFY: src/analysis.hpp:1] [VERIFY: src/analysis.hpp:41]

### 必做实验

```bash
build/dpv --generate-stimulus random -n 5 \
  --stimulus-out /tmp/dpv-random.witness test/it/data/constrained_sat.btor2

build/dpv --generate-stimulus bitwuzla -n 5 \
  --stimulus-out /tmp/dpv-smt.witness test/it/data/constrained_sat.btor2
```

若路径名与当前仓库 fixture 不符，先用 `rg --files test | rg 'constrained.*btor2'` 选实际文件。比较两份 witness，并在代码中定位 rejected draw、blocking clause 和 unconstrained input 补值位置。

### 产出与验收

- 表格比较 `SimOptions`、`SmtSampleOptions`、`EquivOptions`。
- 能举例说明“样本完全一致但全空间不等价”，并指出为什么后续必须建立 proof obligation。
- 能解释 steering 为何针对内部 target，而不仅是让 input tuple 彼此不同。[VERIFY: src/sample.hpp:51]

## 7. 单元 3：精确预处理与模型版本链（2 小时）

### 阅读顺序

1. `src/dce.hpp` 全文。
2. `src/dce.cpp` 按三个公开入口分块读：constraint recovery、constant folding、live-model emission。
3. `test/ut/test_dce.cpp` 全文。
4. `src/main.cpp:1084-1210`，观察 `model → pruned → case_recovered → folded` 的所有权和释放时机。[VERIFY: src/main.cpp:1084]

### 必须画出的模型演进

```text
original Model
  ├─ inspect selected bad for embedded guard
  ▼
single-property live model
  ▼
guard lifted into constraint（若匹配）
  ▼
constant folded model
  ▼
DCE after folding
```

`emit_constraint_recovered_model()` 的等价式应手工验证：旧约束与 `(guard & residual_bad)`，等价于加入 `guard` 约束后检查 `residual_bad`。[VERIFY: src/dce.hpp:41]

### 产出与验收

- 对每次 reparse 记录：节点 ID 是否稳定、property index 是否稳定、input interface 是否稳定。
- 能解释为何 guard recovery 必须检查原始图，而 DCE/constant folding 可能抹去它的方向结构。[VERIFY: src/main.cpp:1107]
- 能解释为什么选单 property 即使 `--no-dce` 也仍需要 property pruning。[VERIFY: src/main.cpp:1129]

## 8. 单元 4：先通读主控，再进入 multiplier abstraction（1.5 小时）

这次只读 `src/main.cpp` 的骨架，不钻 helper：

- `Args` 与 `parse_args()`：`src/main.cpp:335-860`；
- timeout/budget：`src/main.cpp:877-944`；
- standalone stimulus：`src/main.cpp:961-1028`；
- 模型版本链与 early solve：`src/main.cpp:1084-1250`；
- vacuity：`src/main.cpp:1252-1272`；
- abstraction：`src/main.cpp:1275-2180`；
- guarantee：`src/main.cpp:2183-2550`；
- emit/final solve/verdict：`src/main.cpp:2550-2716`。

### 产出

把 `pipeline.md` 扩充为状态机，每个阶段写：进入条件、预算来源、可能早退、是否改写 `cur`、下一阶段消费什么。

### 验收

任选一组参数，例如 `--no-abstract --solve-engine both -t 10`，不运行程序先预测哪些分支被跳过、哪些 child 会创建，再用 `-v` 日志验证。[VERIFY: src/main.cpp:1037] [VERIFY: src/main.cpp:2614]

## 9. 单元 5：multiplier abstraction（4～6 小时）

这是第一个算法专题，应拆成四轮，不要一次读完 `abstraction.cpp`。

### 第 1 轮：数据契约

读 `src/abstraction.hpp` 全文，重点画出 `MulAbstraction`：spec mul、RTL output、word-level operands、split operand parts、algebraic parts、所有 shift。[VERIFY: src/abstraction.hpp:27]

把 `AbstractionOptions` 分为：候选族开关、stimulus/steering、筛选阈值、结构 fast path、复用 stimulus。[VERIFY: src/abstraction.hpp:81]

### 第 2 轮：纯结构 algebra 路径

在 `src/abstraction.cpp` 中从 shared-operand mul-sum 的分解 helper 读到 strict fast path，再读模型重写 `emit_abstracted_model()`；与以下测试逐个对应：

- shared-operand mul-sum 检测：[VERIFY: test/ut/test_abstraction.cpp:174]
- algebraic abstraction 保值：[VERIFY: test/ut/test_abstraction.cpp:195]
- deepest/widest 优先级：[VERIFY: test/ut/test_abstraction.cpp:315]
- fixed-point rescan：[VERIFY: test/ut/test_abstraction.cpp:338]

手推等式 `Σ(X_i·B << k_i) = (Σ(X_i << k_i))·B`，并特别记录 retained bits、truncation 和 overlap 检查如何限制适用范围。[VERIFY: src/abstraction.hpp:58]

### 第 3 轮：SCA 候选发现

从 `find_mul_abstractions()` 入口反向标记：列生成、fingerprint bucket、distinct 筛选、output/operand shift 匹配、split-bit tiling、constraint-constant hole、steering。[VERIFY: src/abstraction.hpp:123]

对应测试：普通 decomposed multiplier、constant-column 筛除、constraint-constant split bits、辅助 input 只有经证明为常量才能折叠。[VERIFY: test/ut/test_abstraction.cpp:45] [VERIFY: test/ut/test_abstraction.cpp:115] [VERIFY: test/ut/test_abstraction.cpp:402] [VERIFY: test/ut/test_abstraction.cpp:429]

### 第 4 轮：proof gate 与应用

读 `src/main.cpp:1690-2168`，画候选的 verdict 状态机：

```text
candidate
  ├─ algebraic identity accepted by exact structural rule
  └─ SCA candidate
       ├─ low-bit-zero obligation
       ├─ exhaustive check（足够小）
       ├─ AIG export
       ├─ ArisCA
       ├─ optional conditional retry
       └─ optional RevSCA fallback
             │
             ├─ proved  → rewrite
             ├─ refuted → reject
             └─ unknown → reject（除非显式 risky mode）
```

验证后端接口读：`aiger.hpp/cpp` 的 cone/miter 与 exhaustive 部分、`arisca.hpp/cpp`、`revsca.hpp/cpp`、`subprocess.hpp/cpp`。对应 `test_aiger.cpp:176-266` 与 `test_arisca.cpp`。[VERIFY: test/ut/test_aiger.cpp:176] [VERIFY: test/ut/test_aiger.cpp:197] [VERIFY: test/ut/test_arisca.cpp:8]

### 单元完成标准

- 能明确区分 candidate evidence 与 proof evidence。
- 能解释 part-level、algebraic、word-level 三种候选在重写时的差异。
- 能指出 UNKNOWN、REFUTED、timeout 分别如何处理。

## 10. 单元 6：AIG 语义与直接求解路径（2～3 小时）

### 阅读顺序

1. `src/aiger.hpp`：先列出导出 API。
2. `src/aiger.cpp`：按 primitive gates → add/mul/shift/divmod → BTOR2 bitblast → miter → exhaustive 顺序读。
3. `test/ut/test_aiger.cpp`：每种语义至少手算一个 2～4 bit 例子。
4. `src/aigsolve.hpp/cpp`：AIG → optional ABC → CNF → Kissat。

### 特别检查

- udiv/urem 的除零语义必须与 `eval.cpp`、Bitwuzla 编码和测试一致。[VERIFY: test/ut/test_aiger.cpp:139] [VERIFY: test/ut/test_eval.cpp:68]
- pair miter 只 blast obligation cone，不能把无关 multiplier 带入。[VERIFY: test/ut/test_aiger.cpp:332]
- relation miter 是 guarantee 中辅助证明的共享接口。[VERIFY: test/ut/test_aiger.cpp:368]
- ABC 是优化层；直接 bitblast+Kissat 仍可用。[VERIFY: CMakeLists.txt:135]

### 产出

画出一条 `BTOR2 bad → AIG literals → optional ABC rewrite → CNF → Kissat verdict` 数据流，标注每一层的输入输出类型。

## 11. 单元 7：`guarantee.cpp` 分专题阅读（7～10 小时）

`src/guarantee.cpp` 是全项目最大实现文件，必须以 `src/guarantee.hpp` 的公开类型和 `test_guarantee.cpp` 的行为主题作为索引，禁止线性通读。

### 7A. 先建立公开契约（1 小时）

完整阅读 `src/guarantee.hpp`，将内容分成：proof engine、候选/报告、options、simplify result、oracle cut points。重点记录 `GuaranteeReport` 如何表达每次尝试，`SimplifyResult` 如何汇总 rewrite 和各种 cut。[VERIFY: src/guarantee.hpp:47] [VERIFY: src/guarantee.hpp:70] [VERIFY: src/guarantee.hpp:335]

找到 `prove_and_simplify()` 公开入口，先只看它的顶层调度和返回构造；静态 helper 按后续专题按需展开。

### 7B. 固定 shift 的浅到深 arithmetic merge（1.5 小时）

从测试驱动阅读：

- generic add pair merge：[VERIFY: test/ut/test_guarantee.cpp:28]
- bad-cone add 不依赖 terminal mul pair：[VERIFY: test/ut/test_guarantee.cpp:73]
- assume-guarantee cut 保持 UNSAT：[VERIFY: test/ut/test_guarantee.cpp:144]
- shifted cut：[VERIFY: test/ut/test_guarantee.cpp:215]
- protected target 的 fallback/skip：[VERIFY: test/ut/test_guarantee.cpp:633] [VERIFY: test/ut/test_guarantee.cpp:695]

为每个测试写四格表：candidate 来源、miter 命题、UNSAT 代表什么、模型如何变化。

### 7C. variable shift、guard 与 control frontier（2 小时）

按测试顺序读：

- variable-shift equality 只加 constraint、不直接 merge：[VERIFY: test/ut/test_guarantee.cpp:274]
- IEEE source-class guards：[VERIFY: test/ut/test_guarantee.cpp:372]
- carrier-backed cut：[VERIFY: test/ut/test_guarantee.cpp:565]
- finite control frontier：[VERIFY: test/ut/test_guarantee.cpp:751]
- control/datapath bridge：[VERIFY: test/ut/test_guarantee.cpp:892]
- sampled false equality 必须被证明阶段拒绝：[VERIFY: test/ut/test_guarantee.cpp:970]

这一专题的核心产出是“控制条件如何进入证明命题”的公式和 DAG，不追求记住所有 heuristic 阈值。

### 7D. division 与 remainder（1.5 小时）

围绕三个测试追代码：

- udiv output replacement：[VERIFY: test/ut/test_guarantee.cpp:1063]
- finite denominator lowering 同时消去 udiv/urem：[VERIFY: test/ut/test_guarantee.cpp:1119]
- high-fanout remainder predicate terminal envelope：[VERIFY: test/ut/test_guarantee.cpp:1170]

必须核对除零、有限 divisor 枚举、quotient/remainder 关系以及重写前后的 width。

### 7E. oracle chain 与 signed multiplication（2 小时）

先读 oracle census 测试，理解 cut point、stand-in 和 connected chain depth。[VERIFY: test/ut/test_guarantee.cpp:1237] [VERIFY: test/ut/test_guarantee.cpp:1266] [VERIFY: test/ut/test_guarantee.cpp:1300]

再读 signed-mul 系列测试：outer minus、two's-complement wrapper、sign/zero extension、narrow negation、低位保持 cast。[VERIFY: test/ut/test_guarantee.cpp:1330] [VERIFY: test/ut/test_guarantee.cpp:1550] [VERIFY: test/ut/test_guarantee.cpp:1626] [VERIFY: test/ut/test_guarantee.cpp:1720]

每识别一种 wrapper，画出原始表达式、规范化表达式、需要额外证明的 helper relation。

### 7F. 总入口回读（1 小时）

最后回读 `prove_and_simplify()` 全部顶层流程，再读 `src/main.cpp:2183-2550`。此时才整理候选 cost tier、proof engine 选择、预算、early solve 交互、BTOR2 emission 与统计输出。[VERIFY: src/main.cpp:2183]

### 单元完成标准

- 能从任一 `GuaranteeReport` 追到候选、proof obligation、verdict、rewrite。
- 能明确哪些变换替换节点，哪些只添加已证明 constraint。
- 能解释为什么 sample/starvation/timeout 只能降低优化机会，不能把未经证明的关系变成 sound rewrite。

## 12. 单元 8：最终求解、portfolio 与进程生命周期（2～3 小时）

### 阅读顺序

1. `src/encode.hpp/cpp`：BTOR2 → Bitwuzla term，重点是 Bool/BV1 边界、memoization、override term。[VERIFY: src/encode.hpp:13]
2. `src/solve.hpp/cpp`：`Verdict`、witness、terminator、forked deadline 路径。[VERIFY: src/solve.hpp:15]
3. `src/portfolio.hpp/cpp`：engine selection、both race、early solve adopt/poll/wait/stop。[VERIFY: src/portfolio.hpp:28] [VERIFY: src/portfolio.hpp:73]
4. `src/aigsolve.hpp/cpp`：第二求解引擎。
5. `src/subprocess.hpp/cpp`：process group、timeout kill、output capture。[VERIFY: src/subprocess.hpp:1]
6. `src/witness.hpp/cpp`：SAT model 和 BTOR2 witness 输出区别。[VERIFY: src/witness.hpp:14] [VERIFY: src/witness.hpp:27]

### 对应测试

- child topology 与 analysis jobs 无关：[VERIFY: test/ut/test_solve.cpp:23]
- in-process terminator 到 Kissat：[VERIFY: test/ut/test_solve.cpp:30]
- constrained UNSAT/SAT 与 witness 语义：[VERIFY: test/ut/test_solve.cpp:59] [VERIFY: test/ut/test_solve.cpp:81] [VERIFY: test/ut/test_solve.cpp:106]
- CLI portfolio/ABC 走集成测试 `CMakeLists.txt:365-405`。[VERIFY: CMakeLists.txt:365]

### 动手实验

对同一小模型分别运行：

```bash
build/dpv --solve-engine bitwuzla -v MODEL.btor2
build/dpv --solve-engine aig -v MODEL.btor2
build/dpv --solve-engine both -v MODEL.btor2
```

记录 winner、AIG and count、退出码、SAT model；再加极短 `-t` 观察 UNKNOWN 与 child 回收。模型从 `test/it/data` 中选择实际存在的 SAT/UNSAT fixture。

### 验收

- 画出 single engine、both、early-solve 三种进程拓扑。
- 说明何时 solver 在 DPV 进程内，何时为 deadline/race 使用 child。
- 解释为什么 parent 必须回收 loser 和外部 SCA 工具的整个 process group。

## 13. 单元 9：端到端复盘（2 小时）

选择两个最小 fixture：一个 SAT、一个 UNSAT；要求至少一个触发 rewrite。分别做以下工作：

1. 用 `build/dpv -v --emit /tmp/final.btor2 MODEL.btor2` 保存阶段日志与最终模型。
2. 在日志每行后标注负责它的 `src/main.cpp` 段和底层模块。
3. 对比原始模型与 emitted 模型：节点数、bad、constraints、关键 arithmetic node。
4. 关闭一个阶段再运行，例如 `--no-abstract` 或 `--no-guarantee`，解释差异。
5. 使用两个 final engine 复核 verdict。
6. 最后执行 `ctest --test-dir build --output-on-failure`，确保阅读实验没有污染构建。

### 最终产出

写一份不超过 3 页的“DPV 从 input 到 verdict”说明，必须包含：

- 模型版本链；
- candidate 与 proof 的边界；
- abstraction 与 simplification 的关系；
- 两条 solver 路径；
- timeout/UNKNOWN 的保守语义；
- SAT witness 的来源。

如果这三页写不清楚，就回到对应单元，而不是继续扩展第三方库。

## 14. 测试作为阅读索引

| 主题 | 首选测试 | 用法 |
|---|---|---|
| BTOR2 精确语义 | `test_eval.cpp` | 每个 operator 手算小宽度结果 |
| 随机模拟 | `test_sim.cpp` | 对照合法 pattern、determinism、timeout |
| SMT stimulus | `test_sample.cpp` | 观察 feasibility、blocking、steering |
| candidate equivalence | `test_mul_equiv.cpp` | 区分 sample relation 与证明 |
| DCE/constraint recovery | `test_dce.cpp` | 对比 rewrite 前后 BTOR2 文本 |
| multiplier abstraction | `test_abstraction.cpp` | 从 fixture 反推候选结构 |
| AIG/miter | `test_aiger.cpp` | 验证 bit-level 语义和 obligation cone |
| verified simplification | `test_guarantee.cpp` | 按主题定位超大实现文件 |
| solver/termination | `test_solve.cpp` | 验证 verdict、witness、process topology |
| CLI contract | `test/it/*.sh` + CTest | 验证真实参数组合和输出契约 |

测试被 CMake 注册为一个 unit test executable 加多项 CLI integration tests。[VERIFY: CMakeLists.txt:265] [VERIFY: CMakeLists.txt:280]

## 15. 暂缓阅读清单

以下内容在完成单元 9 前不要深挖：

- Bitwuzla、Kissat、ABC 内部算法；先把它们视为具有明确接口的 backend。
- ArisCA 的 Rust 源码和 RevSCA 逆向算法；先理解 DPV 如何构造输入、解析 verdict、处理 timeout。
- `guarantee.cpp` 中尚未被当前专题或测试触达的所有静态 helper。
- benchmark 大模型的业务语义；先在小 fixture 上建立正确心智模型。
- CLI 每个 heuristic 参数的默认值；先理解参数属于哪个阶段和它是否影响 soundness。

暂缓不是忽略：当你能从 DPV 的调用点提出明确问题时，再进入第三方代码会高效得多。

## 16. 建议的审查检查表

审查本计划时，请重点判断：

- [ ] 你的目标更偏“能修改算法”还是“能运行并定位问题”；若偏后者，可压缩单元 7。
- [ ] 是否需要把 `guarantee.cpp` 再拆成独立的两周专题。
- [ ] 是否要把第三方 Bitwuzla/Kissat/ABC 纳入第二阶段计划。
- [ ] 是否希望每个单元都产出中文笔记，还是只保留图和问题清单。
- [ ] 每周可投入时间是否足以维持“阅读—实验—复述”闭环。

## 17. 源码锚点校验记录

本计划使用的源码路径均相对仓库根目录；生成时已检查文件存在且引用行号未越界。建议源码大改或切换 commit 后，用以下方式重新抽查：

```bash
rg -o 'VERIFY: [^]]+' /home/jiongming/desktop/DPV_CODE_READING_PLAN.md \
  | sed 's/^VERIFY: //' \
  | sort -u
```

行号是导航锚点，不替代对完整函数和所有条件分支的阅读。
