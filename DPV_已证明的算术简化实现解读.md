# DPV `main.cpp` 已证明的算术简化实现解读

## 1. 对应代码区间

用户引用的“已证明的算术简化”在 `main.cpp` 中不是一行调用，而是一个完整的编排阶段：核心区间为 `src/main.cpp:2182–2507`。[VERIFY: src/main.cpp:2182]

紧随其后的 `src/main.cpp:2509–2527` 会对已证明重写产生的新常量和别名再次做常量传播，因此属于该阶段的直接收尾。[VERIFY: src/main.cpp:2509]

再往后的 `src/main.cpp:2529–2545` 进行重写后 DCE，删除因消费者改接而失去可达性的旧算术锥；它是抽象和算术简化共用的后处理。[VERIFY: src/main.cpp:2529]

所以更完整的阅读范围可以记作：

```text
主编排：main.cpp:2182–2507
后折叠：main.cpp:2509–2527
后 DCE：main.cpp:2529–2545
核心算法：guarantee.cpp:4397–11405
候选初筛：analysis.cpp:230–约 410
```

`main.cpp` 的职责是选择算术家族、准备样本与预算、配置证明器、调用核心算法并接管重写模型；真正的逐候选证明、切割和固定点调度位于 `prove_and_simplify`。[VERIFY: src/main.cpp:2443]

## 2. 这一阶段解决什么问题

该阶段寻找规格侧与实现侧之间值相同或存在可解释位移/切片关系的 `add`、`mul`、`udiv`、`urem` 结构，并在证明关系成立后用一侧结果替代另一侧冗余结果。[VERIFY: src/guarantee.hpp:385]

它与前一阶段“乘法器抽象”的区别是：抽象阶段把门级或部分积结构恢复成字级乘法，而本阶段在当前模型中证明不同算术节点或算术状态之间的等价关系并消除冗余。[VERIFY: src/main.cpp:18]

正常模式下，采样只用于提名候选和推断操作数对应关系；每个实际 cut、merge 或追加的关系约束都必须由独立证明授权。[VERIFY: src/analysis.hpp:13]

## 3. 总体执行流程

```text
当前模型 cur
   │
   ├─ 读取启用的 add / mul / div 家族
   ├─ 构造 EquivOptions
   │    ├─ 约束合法采样
   │    ├─ 复用乘法器抽象样本
   │    └─ dead-mul 定向补样
   ├─ find_equivalent_pairs
   │    └─ 生成 mul / udiv / urem 的候选对
   ├─ 若采样完全饥饿，有限重试一次
   ├─ 构造 GuaranteeOptions
   │    ├─ 算术家族与专项开关
   │    ├─ proof engine
   │    ├─ 单对与总预算
   │    └─ early-solve 协作回调
   ├─ prove_and_simplify
   │    ├─ 过滤、排序与操作数对应推断
   │    ├─ signed-mul / div / add / control-frontier 专项
   │    ├─ 浅到深逐对证明
   │    ├─ 证明成功立即重写当前模型
   │    └─ 后续候选在新模型上继续证明
   ├─ 接管 SimplifyResult::model_btor2
   ├─ 重写后常量传播
   └─ 重写后 DCE
        ▼
最终性质求解
```

整个过程是增量的：候选按逻辑层级浅到深处理，每次证明成功后立即简化模型，后续证明面对的是更小的当前模型，而不是原始复杂锥。[VERIFY: src/guarantee.cpp:6320]

## 4. 第一步：选择算术家族

阶段只在 `args.guarantee` 开启且预处理公共预算尚未耗尽时执行。[VERIFY: src/main.cpp:2183]

`add`、`mul`、`div` 三个族分别由 `args.guarantee_ops` 中的同名项控制，其中 `div` 同时代表 `udiv` 和 `urem`。[VERIFY: src/main.cpp:2185]

乘法还可以独立开启变量移位等式和有符号乘法视图；日志会区分 fixed-shift、variable-shift-equal 和 signed-view。[VERIFY: src/main.cpp:2190]

主程序明确声明统一采用 shallow-to-deep 优先策略，证明器可以是 Bitwuzla、AIG+Kissat，或二者竞速；ABC 仅是 AIG 路径上的可选优化。[VERIFY: src/main.cpp:2197]

## 5. 第二步：发现候选关系

### 5.1 构造 `EquivOptions`

主程序先通过 `equiv_options` 填入种子、并行线程、输入源和 steering 开关，再把输入源固定为 `SmtConstrained`，使所有发现样本满足当前模型 constraints。[VERIFY: src/main.cpp:2206]

全局发现集合只加入启用的 `mul`、`udiv` 和 `urem`；`add` 不在这里做全模型两两扫描，而是在核心简化器内围绕 bad 两侧做哈希分桶发现。[VERIFY: src/main.cpp:2221]

关闭变量移位等式时，`max_shift_values` 被置为 0，从候选层面停止生成 data-dependent shift 对。[VERIFY: src/main.cpp:2223]

样本数使用独立的 `guarantee_patterns`，局部采样时间由剩余预处理预算截断，并要求保留 assignments 给证明阶段继续做操作数对应推断。[VERIFY: src/main.cpp:2229]

若乘法器抽象阶段已经生成约束合法样本，主程序把它们作为 `initial_assignments` 交给候选发现，避免再次求解同一个约束区域。[VERIFY: src/main.cpp:2233]

### 5.2 `find_equivalent_pairs` 的实际工作

函数先扫描模型求值顺序，只收集操作名属于 `op_names` 的节点；目标算术节点少于两个或样本数为零时直接返回。[VERIFY: src/analysis.cpp:235]

它只计算这些目标节点的影响锥，而不是对完整模型求值，以减少每个样本的计算成本。[VERIFY: src/analysis.cpp:253]

约束采样模式下，函数优先检查并消费可复用样本；没有可用样本时才调用 `sample_constraint_legal`。[VERIFY: src/analysis.cpp:257]

如果合法样本没有真正激活某些乘法器，它会调用 `steer_at_dead_muls`，定向让其操作数变化，再重新收集全部目标值列。[VERIFY: src/analysis.cpp:288]

候选关系包括三类：固定左移相等、跨宽度切片相等，以及随样本变化的移位相等。[VERIFY: src/analysis.cpp:340]

跨宽度候选采用以下关系：

```text
lo = slice(hi, shift + width(lo) - 1, shift)
```

它允许宽规格结果的未使用高位非零，适合 C 整数提升宽度大于 RTL 信号宽度的场景。[VERIFY: src/analysis.cpp:98]

变量移位候选要求无法用单一固定移位对齐，但逐样本可以找到二的幂移位；它仍只是候选，真正用于 cut 的 shift 必须在证明阶段找到信号载体并形式验证。[VERIFY: src/analysis.cpp:381]

### 5.3 采样饥饿重试

如果候选发现超时、约束区域并非不可满足且取得的合法帧少于 2，主程序把它视为硬时限下的资源饥饿，扩大局部时间、改变种子并只重试一次。[VERIFY: src/main.cpp:2250]

这次重试仍只是 nomination retry；所有新候选仍需后续正式证明，因而重试不会降低正常模式的可靠性门槛。[VERIFY: src/main.cpp:2243]

若采样器证明 assume 区域不可满足，主程序立即把所选性质报告为 vacuously safe 并返回 UNSAT 退出码。[VERIFY: src/main.cpp:2285]

## 6. 第三步：配置正式证明与简化

主程序把候选发现保留的 assignments 移入 `GuaranteeOptions::inference_assignments`；如果发现阶段因目标算术节点不足而没有消费抽象样本，还会直接把兼容的抽象样本交给简化器。[VERIFY: src/main.cpp:2305]

`inference_sampling_starved` 会记录候选采样或 steering 是否超时，供核心算法判断是否需要采取覆盖恢复策略；它不直接授权任何改写。[VERIFY: src/main.cpp:2323]

`max_pairs` 限制最多证明多少候选对，`pair_time_limit_s` 是单对浅层 SAT screen 的预算，`total_time_limit_s` 则使用当前剩余的公共预处理预算。[VERIFY: src/main.cpp:2326]

主程序把 `mul_simplify`、`signed_mul_simplify`、`variable_shift_equal`、`step_lemmas`、`div_simplify` 和 add operator merge 分别映射到核心配置。[VERIFY: src/main.cpp:2335]

普通 add 通过 `operator_merge` 处理；含 ITE 或掩码 mux 的控制重 add 会被推迟到 `accum_frontier`，并可单独选择证明后端。[VERIFY: src/main.cpp:2344]

局部重试预算可以随 `heuristic_time_scale` 缩放，但总预处理预算不变；这改变的是调度耐心，不是证明规则。[VERIFY: src/main.cpp:2350]

`external_stop` 会轮询并行 early-solve 子进程：若性质已经被其决定，简化器像预算耗尽一样有序停止并保留已有结果。[VERIFY: src/main.cpp:2362]

`on_rewrite` 在第一次证明重写发生时停止尚未得出结果的 early-solve 子进程，避免它继续与已经取得进展的简化流水线争抢资源。[VERIFY: src/main.cpp:2368]

全局 proof engine 按命令行映射为 Bitwuzla、AIG 或 Both；Both 会为每个证明义务竞速两个 solver child，由 DPV 父进程协调。[VERIFY: src/main.cpp:2380]

## 7. 第四步：`prove_and_simplify` 内部流程

### 7.1 候选过滤、排序与样本复用

核心函数首先删除未启用算术族、两端操作不同、宽窄方向不合法以及禁用变量移位时的候选。[VERIFY: src/guarantee.cpp:4412]

候选按两端最大逻辑层级从小到大稳定排序，即更接近输入的浅层算术边界先处理；同层时优先跨宽度关系。[VERIFY: src/guarantee.cpp:4474]

函数只在原模型上采样一次，因为后续 sound cut 都保持值；有至少两个传入 assignments 时直接复用，否则重新约束采样。[VERIFY: src/guarantee.cpp:4512]

它对每个候选的四个操作数收集值列，并推断直连或 crossed 对应、固定或变量移位关系；`mul/add` 允许交换两个操作数，`udiv/urem` 不允许 crossed 对应。[VERIFY: src/guarantee.cpp:4582]

对于变量移位乘法，代码还扩大列收集范围以寻找承载归一化移位量的实际窄信号，因为仅把样本中出现的 shift 值列成有限析取并不是定理。[VERIFY: src/guarantee.cpp:4559]

### 7.2 属性两侧约束与调度

函数尝试恢复 bad 比较的规格侧和实现侧根，只保留跨越语义两侧的相关算术对；若根恢复没有命中任何候选，则 fail-open 回到原浅到深队列，因为所有改写仍有独立证明兜底。[VERIFY: src/guarantee.cpp:6133]

在显式总预算下，最后一个仍具有采样一致操作数对应的候选获得更大的自适应预算，以避免所有时间都消耗在浅层候选上。[VERIFY: src/guarantee.cpp:4603]

函数维护 `cur` 指向逐步重写后的模型，并维护原 id 到当前 id 的 `cur_id` 映射；每次重写后统一更新全部后续候选的节点编号。[VERIFY: src/guarantee.cpp:6320]

只有被替代的节点会加入 `replaced`，作为 canonical source 保留下来的节点仍可继续让其他等价表示折叠到它。[VERIFY: src/guarantee.cpp:6390]

## 8. 四类算术结构如何处理

### 8.1 `add`：控制轻直接 cut，控制重进入 frontier

普通 add 候选围绕当前 bad 的两侧根，通过 `find_fanin_candidates` 进行哈希分桶发现，避免对属性锥内所有 add 做全对全比较。[VERIFY: src/guarantee.cpp:7465]

候选被分成 control-light 和 control-heavy；前者进行直接输出 slice miter 证明，后者推迟给 control frontier。[VERIFY: src/guarantee.cpp:7502]

control-light 候选只有在 `prove_slice_unsat_forked` 返回 `HOLDS` 时才会调用 `emit_forward_cut` 或 `emit_one_cut` 改接消费者。[VERIFY: src/guarantee.cpp:7575]

每次成功 add cut 后，函数立即重建当前模型、更新候选 id，并增加 `operator_cuts`、`adds_simplified` 和 `cuts_applied`。[VERIFY: src/guarantee.cpp:7619]

control-heavy 路径在配对算术 corridor 上运行固定点，覆盖 ITE 和常见 OR-of-masked-AND mux；定向 guard 采样仅在普通合法采样没有取得直接或条件进展后启用。[VERIFY: src/guarantee.cpp:7641]

### 8.2 `mul`：证明输入对应，再判断安全 cut 方向

乘法输出相似度只是发现线索；核心函数还会在 bad 的相对语义侧搜索输入对应的乘法器，即使二者因截断或后处理导致输出样本不直接相似。[VERIFY: src/guarantee.cpp:4614]

普通 fixed-shift mul 必须证明两个输入关系，并要求两输入 shift 之和与输出 shift 一致。[VERIFY: src/guarantee.hpp:92]

有符号乘法并不是另一种 BTOR2 op，而是普通 `mul` 外围的符号扩展和二补码 plumbing；代码对两个操作数分别证明二补码辅助关系，全部成功后才允许切 observable product output。[VERIFY: src/guarantee.cpp:6403]

变量移位乘法若证明了输入或输出关系，通常把关系追加为 constraints 而不合并节点；carrier-backed 且满足额外精确性和依赖安全条件时才可能进一步 cut 宽乘法。[VERIFY: src/guarantee.hpp:189]

固定移位乘法优先删除宽规格乘法，但只有在证明窄乘积没有截断时才安全；否则通常保留宽结果，用其切片替代窄结果。[VERIFY: src/guarantee.cpp:11154]

代码还禁止替换会影响 model constraint 的目标节点，以免改写 assumptions 后扩大合法输入域。[VERIFY: src/guarantee.cpp:11203]

### 8.3 `udiv` 与 `urem`：有序操作数和输出证明

除法和余数不具交换律，因此操作数推断一旦是 crossed 就被拒绝。[VERIFY: src/guarantee.cpp:4593]

`udiv/urem` 被视作独立浅到深任务，其实现侧对端可以是 add/shift/mux 网络而不一定是另一个 division 节点；代码会在 bad 的另一侧寻找任意输出候选并直接证明输出关系。[VERIFY: src/guarantee.cpp:6588]

通过短 proof screen 的 div 候选会立即改写目标，并分别计入 `udivs_simplified`、`urems_simplified` 或 `div_envelope_cuts`。[VERIFY: src/guarantee.cpp:6766]

成功的 div/urem output cut 后会立即常量传播和 DCE，因为商/余数变化经常使一组 decoder predicates 固定，及时清理能减小后续证明锥。[VERIFY: src/guarantee.cpp:6836]

若分母虽然是宽信号但只取少量常量，代码会证明其有限取值集合，再把 udiv/urem 精确降低为移位/掩码或倒数乘法分支。[VERIFY: src/guarantee.cpp:6861]

当两个输入都已证明对齐时，部分 `urem` 和 `udiv` 输出关系可以直接由代数关系得出；其他情况仍调用显式输出 miter。[VERIFY: src/guarantee.cpp:11083]

跨宽度 `udiv` 还需处理除零语义：等宽可直接使用代数关系，跨宽则额外证明窄分母在合法输入上非零。[VERIFY: src/guarantee.cpp:11095]

## 9. “已证明”具体意味着什么

对普通候选，最终 `rep.proven` 要同时满足：两个输入关系已证明、shift 和一致、存在宽度允许的 cut 方向、目标不在 constraint cone 中，并且非乘法操作还必须有输出关系证明。[VERIFY: src/guarantee.cpp:11250]

证明成功后，`CutDir::Op2FromOp1` 用宽结果的 slice 替代窄结果；`CutDir::Op1FromOp2` 用窄结果左移后替代宽结果。[VERIFY: src/guarantee.cpp:11264]

若目标定义早于 source 且不存在依赖环，代码使用 forward cut；否则使用通用 `emit_one_cut` 重新编号并发射模型。[VERIFY: src/guarantee.cpp:11281]

成功 cut 会累计消费者重定向数、按 op 更新简化计数、解析新 BTOR2 为当前模型，并更新原始到当前的 id 映射。[VERIFY: src/guarantee.cpp:11306]

若未启用 `--risky-merge`，`UNKNOWN` 不会改写；只有 `HOLDS/UNSAT` 关系进入正常 cut。[VERIFY: src/guarantee.cpp:11254]

`--risky-merge` 是明确不可靠的例外：乘法候选未证明但没有实际反例、结构条件满足时可以假定等价；若任一输入 miter 返回 `VIOLATED/SAT`，仍绝不合并。[VERIFY: src/guarantee.cpp:11259]

## 10. 主程序如何接管结果

`prove_and_simplify` 返回 `SimplifyResult`，其中包含逐候选报告、各算术家族计数、重定向统计以及最后一次改写后的完整 BTOR2 文本。[VERIFY: src/guarantee.hpp:335]

主程序统计 `reports` 中 `proven` 的数量，并分别打印 add、mul、udiv、urem、div-envelope、普通 operator cut、control frontier cut、guarded constraint、signed mul、variable shift 和 constant divisor 等结果。[VERIFY: src/main.cpp:2444]

如果最后调度的乘法器没有证明两个输入相等，主程序明确保留该 pair，不做合并，继续把剩余原始 bad 交给最终求解器。[VERIFY: src/main.cpp:2487]

只有 `sr.model_btor2` 非空时才解析为新模型、更新 `cur`、标记 `arith_rewrite_applied`，并释放已经被它取代的早期中间模型。[VERIFY: src/main.cpp:2495]

无论是否全部候选证明成功，流程都会继续进入最终性质求解；本阶段不是必须把模型完全消完才算 sound。[VERIFY: src/main.cpp:2506]

## 11. 重写后的二次清理

已证明 cut 可能把 selector predicate 变为常量，因此主程序在最终求解前再次调用 `emit_constant_folded_model`，消除新产生的常量与别名。[VERIFY: src/main.cpp:2509]

随后若允许 DCE，程序调用 `emit_live_model` 删除不再可达的旧算术实现和重复节点，并让最终求解使用清理后的模型。[VERIFY: src/main.cpp:2529]

这两步解释了为什么某次算术 cut 的收益可能大于“少一个 operator”：它还可能连带折叠 mux 分支并使整片旧锥失活。[VERIFY: src/main.cpp:2515]

## 12. 方法论总结

### 12.1 候选发现与正确性证明分离

合法采样、值列、哈希桶和 shift 推断用于控制候选规模；它们提供必要条件但不授权改写。[VERIFY: src/analysis.hpp:13]

正式 miter 证明针对局部关系，只有反例不存在的 `UNSAT/HOLDS` 才把局部语义关系升级为 cut 或约束。[VERIFY: src/guarantee.cpp:7575]

### 12.2 浅到深、证明一个就简化一个

先消除靠近输入的浅层差异，可以让后续深层 miter 看到更相似、更小的两侧算术锥。[VERIFY: src/guarantee.cpp:4474]

这也是 `cur_id` 与逐次重建模型存在的原因：候选来自原模型，但证明和改写必须落在不断变化的当前模型上。[VERIFY: src/guarantee.cpp:6329]

### 12.3 按结构选择专用证明策略

add 分为控制轻直接输出证明与控制重 frontier；mul 重点证明操作数对应、截断精确性和有符号/变量移位辅助关系；div/rem 同时支持输出 cut 和有限分母精确 lowering。[VERIFY: src/guarantee.hpp:183]

这不是用某个单一“万能等价检查”处理所有算术，而是把每类结构中最便宜且足够强的局部义务优先暴露给求解器。[VERIFY: src/main.cpp:2208]

### 12.4 约束安全与依赖安全是重写前置条件

即使值关系已经证明，若替换目标参与 constraints 或 source 依赖 target，代码仍会拒绝相应方向的 cut，避免改变合法输入域或制造组合环。[VERIFY: src/guarantee.cpp:11240]

### 12.5 调度预算不参与语义授权

单对预算、总预算、启发式时间缩放、最终 pair 预算保留和 early-solve 停止回调只决定“先证明谁、证明多久”；它们不会让一个未证明关系自动变成可靠关系。[VERIFY: src/guarantee.hpp:140]

## 13. 一页式伪代码

```text
if guarantee disabled or preprocess budget exhausted:
    skip

families = {enabled add, mul, div}

equiv_opt = constrained_sampling_options()
equiv_opt.ops = enabled {mul, udiv, urem}
equiv_opt.initial_frames = abstraction_frames
eq = find_equivalent_pairs(cur, equiv_opt)

if eq is unmistakably sampling-starved:
    retry once with larger bounded timeout and new seed

if assume region is UNSAT:
    return property UNSAT

gopt = configure proof families, engines, budgets, callbacks
gopt.inference_frames = eq.assignments
sr = prove_and_simplify(cur, eq.pairs, gopt)

inside prove_and_simplify:
    filter unsupported pairs
    sort shallow-to-deep
    infer operand correspondence from legal frames
    recover property sides and specialist candidates
    handle signed mul
    handle div outputs and finite denominators
    handle control-light add
    run control-heavy frontier fixed point
    for each remaining arithmetic pair on current model:
        prove input relations
        prove/derive output relation if required
        check shift, width, constraint and dependency safety
        if proven:
            emit cut immediately
            parse rewritten model
            remap all remaining ids
    return last rewritten BTOR2 and statistics

if sr contains rewritten model:
    cur = parse(sr.model_btor2)

constant_fold(cur)
DCE(cur)
continue to final solve
```

## 14. 对原小节的建议改写

原句“这一阶段处理 add、mul、udiv 和 urem 等算术结构”方向正确，但信息不足；更准确的表述如下：

> 该阶段位于 `src/main.cpp:2182–2507`，先用约束合法样本为 `mul/udiv/urem` 提名固定移位、切片或变量移位候选，并在核心简化器内围绕性质两侧发现 `add` 候选；随后按浅到深顺序在逐步简化的当前模型上证明操作数或输出关系，只有通过独立形式证明且满足宽度、约束与依赖安全条件的关系才会触发 cut，证明得到但不适合合并的变量移位或 guarded 关系则作为 constraints 保留。[VERIFY: src/main.cpp:2182]

## 15. 复核清单

- 已定位主程序完整区间、后常量传播和后 DCE 区间。[VERIFY: src/main.cpp:2182]
- 已核对 `EquivOptions`、`EquivPair`、`GuaranteeOptions`、`GuaranteeReport` 和 `SimplifyResult` 的实际字段语义。[VERIFY: src/guarantee.hpp:108]
- 已核对候选发现的采样、steering、固定移位、跨宽切片与变量移位逻辑。[VERIFY: src/analysis.cpp:230]
- 已核对 add、mul、signed mul、variable-shift mul、udiv、urem 和有限分母 lowering 的真实分支。[VERIFY: src/guarantee.cpp:4397]
- 已核对正常 cut 的 proof、shift、width、constraint 和 dependency 安全门槛。[VERIFY: src/guarantee.cpp:11250]
- 文档未把 sampling match、超时 UNKNOWN 或启发式调度描述成形式证明。[VERIFY: src/analysis.hpp:13]
