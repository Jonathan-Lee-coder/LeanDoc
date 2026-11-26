# DLMST 预印本 ↔ Lean 定理对照表

**口径**：2026-11-27，91 模块 / 29295 行 / 1128 条审计（行数口径 `grep -c ""`；`wc -l` 计 29232）（`Axioms.lean`，`#print axioms` 全部只含 `propext / Classical.choice / Quot.sound`，0 `sorryAx`）。
**编号**：列出的编号按预印本；若编号有出入，以「论文内容」一列的描述为准。Lean 名可在 `Axioms.lean` 中直接 grep 复核。

**关系标记**：
- 逐字 —— 陈述与论文同义，前提也基本一致；
- 加强 —— 结论更强或前提更弱（都是可机检的真命题）；
- 放弱 —— 结论比论文弱，或多了论文没有的前提；
- 重述 —— 换了等价/接口化说法，便于递归消费；
- 条件化 —— 论文里的概率/估计/存在性陈述被写成「给定这些数据则……」的确定性形式；
- 空洞 —— 陈述为真但前提互不相容（vacuous），不构成对论文的支持；
- 未做 —— 尚未写出。

---

## §1–§2 基础

| 论文内容 | Lean 命题 | 关键前提 | 关系 |
| --- | --- | --- | --- |
| §1 记号：多重图、连通、森林、生成森林、MSF、权重和 | `MsfKernel.lean`：`WGraph`、`Conn`、`IsForest`、`IsSpanningForestOf`、`IsMSFOf`、`wsum` | — | 逐字（自定定义） |
| Fact 2.5：轻边/割性质（最轻出边可入某 MSF） | `LightSpan.lean`：`LightSpan`、`supported_of`、`exists_msf_contains` 系列 | 权重全序 | 逐字 |
| 阈值图与重标号的单调性 | `MsfKernel.lean` 阈值边集单调、权重保序重标号 | — | 加强（任意阈值） |
| 交换论证（割/环性质） | `Exchange.lean`：`conn_insert_sep` 等整条链 | — | 逐字 |
| 森林中路径唯一 | `Tree.lean`：`Path.split` 等显式边序列手术 | — | 加强（显式路径） |
| `U(F)`（不被森林支持的边） | `Exchange.lean` / `LightSpan.lean` | — | 逐字 |
| Borůvka 一轮不成环；单边轮可扩 | `Boruvka.lean`：`boruvka_forest(_in/_at)`、`boruvka_round_at` | 蓝规则（每分量一条最轻出边） | 逐字 |
| 相位减半：`c_k ≤ 2m/2^k` | `BoruvkaHalving.lean` / `InstanceCount.lean`：`compCount_halves`、`c_k` 界 | 每分量有出边（激活） | 逐字（条件化） |
| Lemma 1.2：证书式 `\|F\|+\|U(F)\|+Σ\|Eᵢ\| ≤ εm+C_ε√(mn)` | `Certificate.lean` / `CertificateBuild.lean`：`Certificate`、`linear_of_display` | 显示式 | 逐字（接口化） |

## §3.1–§3.3 工具

| 论文内容 | Lean 命题 | 关键前提 | 关系 |
| --- | --- | --- | --- |
| Lemma 3.2：批量选择的二择一（支持或投影） | `Batch.lean`：`batch_at_vertex`、`exists_cnd`、`supported_of_declared`、**`batch_supported_or_project`** | `BatchSpec` / `SpokeSpec`（其存在性由 `BatchSel.lean` 给出） | 逐字（条件化） |
| Lemma 3.3：测试/比较的正确性 | `Queries.lean`、`ScanOfSlot.lean`、`Portals.lean` | — | 重述 |
| Lemma 3.7：偏好 = 路径上的最重边 | `PrefTrail.lean`：**`prefFind_iff_trail_weight`** | — | 逐字 |
| Lemma 3.9：向量极大与 `log\|A\| ≤ 4√(2n log n)` | `VectorMaxima.lean`：`maxima_vector_determined`、`maxima_vectors_card`、`pref_vectors_le` | — | 逐字 |
| Lemma 3.10：历史条数上界 | `HistoryCount.lean`：`card_histories_le`、`log_card_histories_le` | 轮数据 | 逐字 |
| Lemma 3.10 实例局部版（`m=\|E₀\|`、`n=\|P\|`） | `InstanceHistory.lean`：`degOn`、`sum_degOn_le`、`sum_log_degOn_le`、`card_spokeOKOn_le`、`card_subsetsOn_le_choose`、`card_historiesOn_le`、`log_card_historiesOn_le`、`LegalOn`、`exists_good_scheduleOn`（非空性 `legalOn_canonical`） | `hends`（`E₀` 的端点都在 `P` 内）；`hB : B ⊆ E₀`（下游） | 逐字（把全局口径 `m,n` 换成实例口径，代价是 `hends`） |
| Lemma 3.11：调度（丢失量的和界） | `ScheduleBound.lean`：`exists_schedule_lost_le`、`exists_schedule_lost_paper`；实例形式 `InstanceCount.lean`：`lemma311_on` | — | 逐字 |
| Lemma 3.11 与实例局部 3.10 的合成（即 `EvidenceOn.hlost` 的形状） | `InstanceHistory.lean`：**`exists_schedule_lostOn_paper`**（`∃ρ, ∀H∈Hs, lostOn·log2 ≤ (2√2+4)t²√(\|E₀\|\|P\|) + 2\|E₀\|/t`） | `ht : 2 ≤ t`、`H ∈ LegalOn P E₀ e₀` | 逐字（精确平均，无概率） |
| `EvidenceOn` 的真值构造：`hc`／`agree`／`hlost` 变定理 | `DriverEvidence.lean`：`history_legalOn`、`truthCand`、**`evidenceOn_of_good_schedule`**、`agree_truthOn`、`card_U_le_number_bound_of_truth`、`exists_good_schedule` | **(a) 调用自己的 schedule 恰好是好的**、**(b) Lemma 3.7 逐边 `edge_ok`**、`hB : B ⊆ E₀`、`hP0 : 0 < P.card` | 条件化（只剩这两条前提，见 B6） |
| `DriverCall` 接口非空 | `DriverWitness.lean`：`Gpar`（两点五平行边）、`incident_all`、`preF_par_card_le`、**`callPar`**（`hsupply` 由「森林 ≤1 条 < 5 条关联边」给出）、`callPar_nonempty`、**`callPar_legalOn`**（把 `history_legalOn` 落到真实驱动） | 模型层面的可满足性；不声称算法行为 | 见证（非空洞） |
| 小实例上「好调度」自动成立 | `SmallInstance.lean`：`History.lostOn_le_card`、**`lostOn_log_le_of_bound`**、`callPar2`、`callPar2_hbig`、`callPar2_good`、**`callPar2_evidence`**、**`callPar2_card_U`** | `|E₀|·log2 ≤ (2√2+4)t²√(|E₀||P|)+2|E₀|/t`（小实例自动满足）；`edge_ok` 仍为前提 | 加强（B6 的基例：任意调度都好） |
| Lemma 3.7 的结论（`bad` 形式） | `Lemma37Bad.lean`：**`errOf_truth_iff`**、`evidenceOn_of_good_schedule_badFor`、**`card_U_le_number_bound_of_badFor`** | `∀ e ∈ E₀, ¬supported → badFor e (R.sched e)`（真值估计下 `errOf` 的第二析取消失） | 逐字（与 `errOf` 形式等价，更贴论文） |
| Lemma 3.7 逐边前提：`t=1` 自动成立 | `ProcDriver.lean`：**`History.badFor_one`**（单轮调用每个轮次对每条边都是坏轮）、**`DriverCall.badFor_of_unsupp_one`**、`evidenceOn_of_good_schedule_one`、`callPar_one_hbig`／`callPar_one_good`／**`callPar_evidence_uncond`** | **无**（定义 3.4 的尾条件在 `Fin 1` 上为空量词） | 逐字（定义性坍塌，非算法行为） |
| Lemma 3.7 逐边前提：一般 `t` 从层级链推出 | `ProcDriver.lean`：**`history_spoke_incident`**（链的 `hspoke` 由供给推出）、**`badFor_of_procChains`**、**`evidenceOn_of_procChains`**、**`card_U_le_number_bound_of_procChains`** | 每条边一条 `ProcChain`（`hproj`／`hfroz`／`hret`／`hsub`／`hmsf`／`hlift`／`hσS` 即算法的过程义务）＋好调度前提 | 合成（把 `ProcChain` 的 `errOf` 用真值估计与 `errOf_truth_iff` 化成第一百一十九批的 `hbad`；`hcons`／`hspoke` 已由接口给出） |
| 平行边见证的每条边都被支持 | `WitnessSupported.lean`：**`head_kept`**（第 0 轮扫描 = 实例按权排序全表；Kruskal 保留其首元素，进 `preF (2^2)`）、**`all_supported`**、`badFor_vacuous`、**`callPar2_unsupp_empty`**／**`callPar2_U_eq_empty`**、**`callPar2_evidence_uncond`**、`callPar2_card_U_uncond` | **无** | 加强（该见证上 `edge_ok` 空真、`U=∅`；`EvidenceOn` 无前提居留，数值界平凡） |
| Lemma 3.7 过程侧：驱动形态的层级链 | `ChainDriver.lean`：`ProcChain.unSupp_errOf_on`、**`badFor_of_procChainsOn`**（链只建在 `E₀` 上）、**`history_spoke_frozen`**（块内批次冻结 ⟹ 辐条冻结 ⟹ `hfroz` 由接口推出）、**`ProcChain.ofDriver`**、**`badFor_of_driverChains`**（逐边前提 = 算法义务 `hproj`／`hret`／`hsub`／`hmsf`／`hlift`／`hσS` + 根识别 + `hchild`） | `∀ e ∈ E₀, ¬supported → badFor`（推论）；`hcons`／`hfroz`／`hspoke` 已由驱动接口给出 |
| 层级链的形状：接口只表示无休止投影 | `ChainShape.lean`：**`ProcChain.childF_nonempty`**（无自环 ⟹ 每层孩子森林非空）、**`not_chain_of_empty_child`**／**`not_chain_of_eventually_empty`** | 论文的有限链（`lemma37_error`：`∀ j ≥ d, supp`，只对 `j < d` 要求投影步）与之不同构；链路线是充分证书（B7） |
| 过程侧的单一入口：驱动形态 ⟹ §3.5 界 | `ChainShape.lean`：**`evidenceOn_of_driverChains`**、**`card_U_le_number_bound_of_driverChains`** | `EvidenceOn` 与 `\|U\| ≤ 10t²√(\|E₀\|\|P\|)+4\|E₀\|/t`，前提 = `hBfroz` + 算法义务 `hproj`/`hret`/`hsub`/`hmsf`/`hlift`/`hσS` + 根识别 + `hchild` + 好调度 + `hB` + `0<\|P\|` + `2≤t` |
| 单层步骤接口：过程侧的最小数据 | `OneStep.lean`：**`StepData`**（一层的 slot/森林/子实例/提升路径 + `hcons`/`hproj`/`hfroz`/`hret`/`hsub`/`hmsf`/`hspoke`/`hlift`/`hσS`）、**`StepData.step_error`**／**`StepData.badFor`**（**无**孩子支持前提）、`ProcChain.stepData`、**`badFor_of_stepsOn`**、**`badFor_of_procChains_noChild`**（`hchild` 冗余）、`evidenceOn_of_steps`、**`card_U_le_number_bound_of_steps`** | `∀ e ∈ E₀, ¬supported → badFor`；§3.5 界只剩 `2≤t`、`hB`、`0<\|P\|`、好调度 |
| 投影判据：不支持 ⟹ `project` | `ProjectRule.lean`：**`not_prefFind_of_unsupp`**（辐条关联 + 门户相异 + `w(σu),w(σv) ≤ w(e)` + 不支持 ⟹ 不 `find`）、**`supported_mono`**、**`DriverCall.pref_project_of_unsupp`**、**`StepData.ofDriver`**、**`badFor_of_stepObligations`**、`evidenceOn_of_stepObligations`、**`card_U_le_number_bound_of_stepObligations`** | `hproj` 由状态推出；逐边义务只剩 `hret`/`hsub`/`hmsf`/`hlift`/`hσS` 与 `S`/`es` |
| 辐条属于批次；几何化每边义务 | `SpokeInst.lean`：**`history_spoke_mem_B`**（辐条 ∈ 本轮批次 `B b i`）、**`history_spoke_mem_of_batch`**（`B b i ⊆ S` ⟹ `hσS`）、**`badFor_of_geomObligations`**、**`evidenceOn_of_geomObligations`**、**`card_U_le_number_bound_of_geomObligations`** | `hσS` 由批次包含推出；与第 125 批合起来，逐边只剩算法数据 `hret`/`hsub`/`S`/`es`/`hmsf`/`hlift` 与几何三条 |
| 森林单调；`hret`／`hsub` 消去 | `ForestMono.lean`：**`forestUpTo_mono`**、**`history_forest_mono`**、**`history_forest_sub_F`**、**`nextForest`**、**`hret_nextForest`**、**`nextForest_sub`**、**`badFor_of_geomObligations_next`**、**`evidenceOn_of_geomObligations_next`**、**`card_U_le_number_bound_of_geomObligations_next`** | `hret`／`hsub` 取 `nextForest` 时无需假设；剩余 = `hmsf`／`hlift`（关于 `nextForest`）+ `S`/`es` + 几何三条 |
| 辐条轻量条件来自选择集 | `SpokeLe.lean`：**`history_spoke_weight_le_of_mem`**、**`badFor_of_selObligations`**、`evidenceOn_of_selObligations`、`card_U_le_number_bound_of_selObligations` | 轻量前提化为 `e ∈ selAt`（两端）；端到端封装后被判空真（第 129 批） |
| 轻辐条与子实例支持互斥（更正） | `LightVacuous.lean`：**`supported_of_light_and_child`**、**`unsupp_false_of_light_and_child`**、**`pE_gt_of_unsupp`** | 第 126／127／128 批的 `hproj` 派生封装在 `¬supported` 分支前提互斥、结论空真；非空路线 = 第 125 批 `badFor_of_stepObligations` + 第 124 批 `StepData` |
| Claim 3.12：查询数 `O(t²√(mn))` | `Sampling.lean`、`QueryCount.lean`：`sampleSets_*`、`card_U_le_number_bound_of_queries`、`card_U_le_display_form_of_queries`；`Driver.lean`：`round_budget_sum` | 逐轮查询数据 | 逐字（计数，不含概率） |

## §3.4–§3.6 轮次、估计、显示式

| 论文内容 | Lean 命题 | 关键前提 | 关系 |
| --- | --- | --- | --- |
| §3.4 轮/坏轮/历史/几何族 | `Rounds.lean`、`History.lean`、`Geometric.lean`、`GeometricHistory.lean`、`HistoryOfRounds.lean`：`geomFamily_log_ceil_le`、`sum_sqrt_card_fibre_le`、`sampleSets_geomFamily_*` | 轮数据 | 重述 |
| Claim 3.5/3.6：采样估计（显示 `herrU`）与 `γ²·40000√(mn)+16m/γ` | `EstimateBound.lean`、`InstanceCount.lean`：`estOfOn`、`geomFamilyOn`、`truth_of_historyOn`、`driverScheme_herrU`、`display_of_driver` | **`hsup`（数据假设）**、全局 `m=\|E\|`/实例 `m=\|E₀\|` 两种口径 | 条件化（概率陈述未形式化） |
| §3.5 轮次求和 / 全局分类 | `RoundScan.lean`、`ProcChain.lean`、`Assembly.lean`：`errors_levels`、`lemma12_bound`、`round_budget_sum_paper` | — | 逐字 |
| §3.6 一次调用的产出 `(F,P′,cls)` 与 `CallOut` | `CallFromRounds.lean`、`Section36.lean`、`Procedure.lean`、`DriverCall.lean`：`CallOut`、`CallOut.ofClass`/`ofForest`、`display_of_callout`、`comparisons_of_levels`、`portals_shrink`、`Step.ofCallOut`；构造侧 `RoundScan.lean`：`isForest_K`、`roundData_F`、`sum_kidE_le_batches`、`ofScan_wf` | `CallOut` 的字段（**`hUkid`：未被宣告的孩子边即不被支持**） | 重述（**与 §4 不同构，见边界 B1**） |
| §3.7 策略与层链 | `Procedure.lean`：`Strategy`、`Level.allChildren`、`Step.ofCalls`、`Level.next`、`Level.chain`、`LevelChain.chain_step`、`display_of_strategy`；`DriverSelect.lean`：`Strategy.Strict`/`Leaf`、`chain_insts_empty_of_le` | 良构策略 | 逐字 |
| 逐实例代价递推 / 条件线性 | `CostLinear.lean`、`LevelSize.lean`：`cost_linear`、`cost_linear_of_nodes`、`htd_all_roots_impossible` | 节点显示式（层边减半已删，见 B2） | 放弱（见边界 B2） |
| §3.6 层模型总工作量线性 | `LevelLinear.lean`：**`level_edges_summable`**、`level_verts_summable`、`level_work_linear`、`chain_work_linear`、**`chain_display_of_calls`**、**`chain_work_linear_of_calls`** | 逐层显示（由 `chain_display_of_calls` 化归为逐实例孩子界）；`ε ≤ 1/4`、`N ≤ 2M` | 逐字（论文的「各层规模之和」口径，不用边减半） |
| §3.6 逐调用计数 ⟹ 层链总工作量线性（层级 `t_d = γ(d+1)³`） | `LevelWork.lean`：**`chain_edges_display`**（§3.5 估计算 `10t_d²√(mn)+4m/t_d` + p.24 输入计数 ⟹ 层边总数 `10t_d²√(m_d n_d)+4m_d/t_d+(2t_d²+t_d+64t_d⁷)n_d`）、**`level_work_poly`**（增长系数 `γ²(d+1)⁶`、`γ⁷(d+1)²¹` 被 `4^{-d}` 顶点衰减吸收 ⟹ `Σ(n_d+m_d) ≤ 4N/3+(4/3)(M+R)`）、**`chain_work_linear_counts`**（策略链上对所有深度一致） | 逐调用的两个数值不等式（`hU`、`hrnd`，即 §3.1–§3.5 的解析输出）；`γ ≥ 16` | 逐字（不要求层统一 `C`，不用 `htd`，不用边减半） |
| §3.6 端到端：同一组前提同时给出显示式与总工作量线性 | `LevelWork.lean`：**`strategy_display_and_work`**（`display_of_strategy_of_nat_counts` + `chain_work_linear_of_counts_bounded`，桥接 `input_poly_of_nat`）；`CostLinear.lean`：`strict_of_shrink`、`cost_linear_of_shrink` | 逐实例（`d ≤ \|E₀\|`）`\|U\| ≤ 10t_d²√(mn)+4m/t_d` 与 `Σ\|kidE\| ≤ \|U\|+2t_d²(n−1)⁺+t_d((n−1)⁺+r_d²n)`（**自然数减法**，退化 `(∅,∅)` 实例上可满足）；`hnm`；常数条件 | 逐字（前提集最小化：无需逐实例非空、无需统一 `C`） |

## §4 收缩递归

| 论文内容 | Lean 命题 | 关键前提 | 关系 |
| --- | --- | --- | --- |
| §4 一步：孩子最优 ⟹ 拼接最优（整图形式） | `Contract.lean`：**`isMSF_union_cGraph`**、`isSpanningForest_cGraph_of_union`、`wsum_splice_le_iff` | `F ⊆ M`，孩子 MSF | 逐字 |
| §4 一步（实例形式，递归真正消费的形状） | `Contract.lean`：**`isMSFOf_union_cGraph`**、`isMSFOf_union_cGraph_child` | `F ⊆ M ⊆ E₀`，孩子 `IsMSFOf` | 逐字 |
| §4 收缩尺寸与孩子规模 | `ContractSize.lean`：`contract_step_sound_and_small''`、`four_mul_repSet_card_le`、`four_mul_child_forest_card_le`、`contract_two_levels''` | 两相位、`hcontract`（由相位自动给出，`hcontract_of_phases`） | 逐字 |
| §4 一步的记录与策略 | `ContractStrategy.lean`：`ContractOut`、`ContractStep`、`ContractWf`、`contractOutOfTower`、`contractStrategyTower` | 同上 | 重述 |
| 塔：任意深度的 MSF 可靠性 | `Tower.lean`：`tower_sound`、`tower_terminates` | **激活：每一层、每一相位、每个顶点都有出边** | **空洞**（见 B3） |
| 塔：权重望远镜 / 边数相加 | `Tower.lean`：**`tower_wsum`**、`tower_card`、`tower_wsum_lvl` | 同上 | 空洞（推理本身已机检，前提不自洽） |
| 塔：规模 `4^d·\|lvlVerts d\| ≤ \|P\|`、`4^(d+1)·\|B\| ≤ \|P\|` | `Tower.lean`：**`four_pow_mul_lvlVerts_le`**、`tower_small` | 同上 | 空洞 |
| §4 结论：MSF 且 `3\|F\| ≤ 4\|P\|`（显示式） | `ContractStrategy.lean`：`contractDisplay`、`contractStrategyTower_display`、`tower_work_log` | 激活（同上）+ 工作量前提 | 空洞（组合骨架为真） |
| 主定理打包 | `Main.lean`：`mst_main`、`mst_main_weight`、`mst_main_log`、`mst_main_root_conn` | `TowerInputs` / 无界 `hact` | **空洞**（`towerInputs_false`、`mst_main_log_hypotheses_false`、`mst_main_root_conn_hypotheses_false`） |
| §4 在**自选停止深度**（第 112 批） | `TowerDepth.lean`：**`four_pow_mul_lvlVerts_le_of_lt`**（`d ≤ D` 上的测度）、**`lvlVerts_card_le_one_of_le_pow`**（`\|P\| ≤ 4^D` ⟹ 底部塌缩，`hstop` 由测度**推出**）、**`mst_stop_depth`**（`D = log₄\|P\|+1`，MSF 且 `\|F\| ≤ \|P\|−1`）、`mst_stop_depth_three_fourths`、`mst_stop_depth_weight`、`mst_stop_depth_package` | 激活只在 `d < D`；无界 `hact` 不再出现 | 加强（把 `D` 与 `hstop` 从假设变成结论；仍假设 `D` 以下激活） |
| §4 塔**无条件正确**（第 113 批） | `TowerUncond.lean`：**`contract_step_sound_nohact`**、**`tower_sound_nohact`**、`tower_msf_at_stop_nohact(_card)`、**`lvlVerts_succ_lt`**（`≥2` 顶点层严格收缩，激活由连通性推出）、`lvlVerts_le_one_or_card_add_le`、`lvlVerts_card_le_one_at_card`、**`mst_main_connected`**（连通 ⟹ MSF 且 `\|F\| ≤ \|P\|−1`）、`mst_main_connected_three_fourths`（`3\|F\| ≤ 4\|P\|`）、`mst_main_connected_weight`、`mst_main_connected_package`、**`activated_iff_two_le_compCountOn`** | 仅 `hPE`、`0 < \|P\|`、`G[E₀]` 在 `P` 上连通；**无任何激活假设** | 加强（B3 的“正确性 + 4/3”半边现在无条件；测度 `\|P\|/4^d` 账仍属第 112 批的有界激活版） |
| **可满足的停机接口**（替代品） | `Tower.lean`：`tower_sound_bd`、`tower_msf_of_stop`、`tower_msf_of_stop_card`；`Main.lean`：**`mst_main_stop`** | 激活只在 `d < D`；`\|lvlVerts D\| ≤ 1` | 放弱（结论 `\|F\| ≤ \|P\|−1`，不再声称 `4/3`） |
| 停机接口的 `4/3`（第一百一十七批） | `StopFourThirds.lean`：**`answer_three_fourths`**、**`mst_main_stop_three_fourths`**、`stop_witness_three_fourths` | 与 `mst_main_stop` 同一组停止前提 | 逐字（`|F| ≤ |P|−1` ⟹ `3|F| ≤ 4|P|`；同一四顶点见证） |
| §3.6 显示 ↔ §4 塔（R1 组装） | `TowerLevels.lean`：`towerLevelChain`/`towerLevelChain_step`、`tower_display_rest`/`tower_display_poly`、`tower_e2e`、`tower_e2e_witness` | 显示只吃计数层链；激活只需 `d < D`（尾部空层） | 已组装（分析接口）；强显示 `ρ<1` 对链式递归被 `hshr_refuted` 否证，线性仍需分支递归（B2/B4） |
| §4 的分支递归（B2：由逐实例显示推线性代价） | `BranchRec.lean`：`kidE_le_of_display`、`kidE_display_of_counts`、`child_shrink_of_counts`、**`cost_linear_of_counts`**、`exists_displayC_phase` | 显示式在每个实例上成立（逐节点计数数据）；`T` 是计数代价 | 条件化（数据前提：逐节点 `hU` 估计、轮次、`n ≤ 2m/2^{2j}`、代价递归 `hrec`） |
| §3.4–§3.5 的概率语言（B4：期望、Markov、尾界、成功概率） | `Prob.lean`：`unifProb`/`unifExpect`、`markov`、`History.unifExpect_two_pow_lost_le`、`History.lost_tail_prob`、`sample_budget_exp`、`bad_prob_le`、`claim312_success_prob`、`claim312_exists_via_prob`；**第一百零九批**：`unifExpect_mono`、`History.genEdge_le_real`、`History.weighted_sum_le_real`、`History.unifExpect_mgf_le`、`History.chernoff_tail`、`History.unifExpect_lost_le`、`History.half_schedules_good`、`History.lost_tail_prob_paper` | 有限均匀分布；事件取 `Finset`；随机性仅用于存在性 | 已机检；算法确定性不变（B4 边界保持） |
| §3.4–§3.5 的多事件形式（B4：并集界、Bonferroni、独立性、Claim 3.12 概率版） | `ProbUnion.lean`：`unifProb_union_le`、`unifProb_biUnion_le`、**`unifProb_all_good_ge`**、**`unifProb_indep`**、`unifProb_prod_two_good`、`claim312_four_fifths`、`unifProb_agreeTuples`、`unifProb_agreeTuples_le`、`bad_prob_le_via_union`、**`bad_prob_le_union`** | 有限均匀分布；乘积空间 `×ˢ`；随机性仅用于存在性 | 已机检；与 `Sampling.bad_prob_le` 的计数链互为印证（B4 边界保持） |
| §4 输出的可满足包（MSF ∧ 权重 ∧ `\|F\| ≤ \|P\|−1` ∧ 逐层收缩 ∧ 计数工作量） | `LinearTime.lean`：**`tower_stop_display`** | 激活只在 `d < D`；`\|lvlVerts D\| ≤ 1` | 放弱（替代空洞的 `contractDisplay`：结论不再含 `4/3`，改为 `\|P\|−1`）；非空洞见证 `LinearTime.stop_display_witness`、求值 `stop_display_witness_values`（`G4`） |
| 停机接口的非空洞见证 | `StopWitness.lean`：`phaseIn_one/two`、`phaseChain_one/two`、`conn_pair_iff`、`compCount_final`、`stop_hstop`、`stop_hact`、`stop_witness_answer`、`stop_witness_value`、**`stop_witness`** | 具体 4 顶点图 `G4`（权重 1,1,2） | 见证（`mst_main_stop` 在该实例上实例化） |
| §4 与 §3.6 的接口冲突（B1 机检） | `ContractStrategy.lean`：**`CallOut.supported_of_mem_kidE`**、**`CallOut.disjoint_crossE_kidE`**、**`CallOut.not_subset_kidE_of_crossE`**、**`CallOut.not_mem_kidE_of_phase`** | `CallOut.hUkid`；`crossE_subset_unsupp`、`crossE_subset`；相位数据 `M ⊇ F`、`M ⊆ E₀` | 否定（接口不相容；§4 的孩子跨边永不能进 `CallOut`，且相位差集边确实如此） |
| §4 的「线性时间」口径与边数账 | `LinearTime.lean`：**`tower_work_le_bd`**（`3·totalWork ≤ 4\|P\| + 3d\|E₀\|`）、**`counting_log_stop`**（`(4/3)\|P\| + 3D\|E₀\|`，`D = log₄\|P\|+1`）、`mst_main_stop_log`；论文路线 **`counting_linear_of_display`**（§3.6 显示 + 相位减半 ⟹ `W m = O(m)`）；反例 **`hshr_refuted`**／**`hshr_refuted_stop`**（`G8`：8 点 17 边，`2·9 > 17`） | 计数模型（无机器/数据结构/可执行程序）；线性版的 display 与相位减半是论文 Claim 3.6／Borůvka 的数据前提 | 重述 + **否定**（边减半在该递归下不成立；第九十四批已删除全部 `hshr` 条件定理，线性改走论文的 display 路线） |

---

## 边界（对照后仍然没有的东西）

- **B1 §3.6 与 §4 不同构**：`CallOut.hUkid` 要求「未被宣告的孩子边不被支持」，而 §4 的收缩递归中跨边集 `crossE ⊆ unsupp`（`crossE_subset_unsupp`），两者不能同时满足；因此两条线在 Lean 里**各自闭合**（§3.6 的 `display_of_strategy` 吃 `CallOut`；§4 的 `ContractStrategy` 不吃），**没有**一条端到端定理把 §4 的输出喂给 §3.6 的显示层。这在论文里是「§4 调用 §3.6」的一句话，在形式化里是一个真实的接口缺陷。第一百批把该冲突本身机检：`CallOut` 的孩子边必被 `F` 支持（`CallOut.supported_of_mem_kidE`），而 §4 的跨边不被支持且与孩子边集不交（`CallOut.disjoint_crossE_kidE`、`not_subset_kidE_of_crossE`），相位差集边确实落在跨边里（`not_mem_kidE_of_phase`）——冲突非空洞。
- **B2 无成本模型**（第九十五、九十六批补充）：所有「线性/`O(·)`」都落在**计数**（比较数、查询数、边数、顶点数）上；`LinearTime.lean` 把塔的计数口径写死（`levelWork`/`totalWork`/`counting_log_stop`），`LevelLinear.lean` 补上了论文自己的总量口径（`Σ_d(|V_d|+|E_d|)` 线性，逐层显示由 `chain_display_of_calls` 化归为逐实例孩子界），`LevelWork.lean` 再把该孩子界换成论文真正的**逐调用计数**（层级 `t_d = γ(d+1)³`，`chain_edges_display`/`level_work_poly`/`chain_work_linear_counts`），但仍无「一次基本操作 = 单位时间」的代价定义与可执行实现，所以「线性时间」本身未机检。层边减半 `hshr` 不再是假设而是**被推翻**（`hshr_refuted`：`G8` 上 `2·9 > 17`），故塔的计数版最强形式是带 log 的 `counting_log_stop`；层模型的总量线性不依赖边减半，也不依赖层统一常数 `C`，只依赖 §3.6 的逐调用数值不等式。第九十七–九十九批把这组前提进一步收紧并合并：逐调用计数只需断言到深度 `|E₀|`（`forall_chain_of_le_card`），减法取自然数形式（`((n−1:ℕ):ℝ)`，退化 `(∅,∅)` 孩子上可满足），且**显示式与总工作量线性由同一组前提推出**（`strategy_display_and_work`）；`Strategy.Strict` 也由“孩子边和减半”推出（`strict_of_shrink`）。第一百零七批补上此前点名的分支递归缺口：`BranchRec.lean` 把 `LevelWork` 的**根显示式**提升为**逐实例显示式**（`kidE_display_of_counts`，常数 `displayC γ`），经 `children_shrink` 化为 `Σ|Eᵢ| ≤ m/2`，再由 `cost_linear_of_counts` 沿策略自身孩子树强归纳，得到每个实例 `T ≤ 2c|E₀|`——无 `m` 索引最坏情形、无 `hshr`、无 `hrec` 之外的运行假设。
- **B3 4/3 链空洞**：无界激活 `hact` 与测度 `4^d·|lvlVerts d| ≤ |P|` 矛盾——在 `d = log₄|P|+1` 层实例塌缩到 ≤1 个顶点，此时所有边都是自环，而 `phaseChain 0 = ∅` 下 `leaves` 不可满足（`not_activated_of_card_le_one`）。故 `mst_main` / `mst_main_log` / `mst_main_root_conn` 及策略层显示式都是**空洞真**；诚实的最强形式是 `mst_main_stop`（已由 `stop_witness` 证非空洞）。**第 112–113 批把 B3 拆成正反两面**：(一) `TowerDepth.lean` 把停止深度 `D` 写成结论的一部分——有界测度 `4^d·|lvlVerts d| ≤ |P|`（`d ≤ D`）配 `card_le_pow_log` 推出底部塌缩 `|lvlVerts D| ≤ 1`，于是 `mst_stop_depth` 在 `D = log₄|P|+1` 给出 MSF、`|F| ≤ |P|−1` 与 `3|F| ≤ 4|P|`，激活只需在 `D` 以下（`hstop` 不再是假设）；(二) 更正一点：拼接**不需要激活**——`InstanceSafety.phaseChain_safe` 已给「两相位森林含于某实例 MSF」，配 `isMSFOf_union_cGraph_child` 就有无激活的层步。`TowerUncond.lean` 据此证明 `tower_sound_nohact`（除 `hPE` 外无假设），并从层连通性推出停止深度（`lvlVerts_succ_lt`：`≥2` 顶点层的第一相位激活由 `hact_of_connOn_E₀` 从 `compCountOn ∅ = |V_d| ≥ 2` 推出），最终 `mst_main_connected` 在**连通实例**上无条件给出 MSF、`|F| ≤ |P|−1` 与 `3|F| ≤ 4|P|`。激活只在**测度**账里仍必要：`activated_iff_two_le_compCountOn` 机检「连通实例上 激活 ⇔ 分量数 ≥ 2」，所以 `tower_sound` 的双相位停机接口只在**层边界**塌缩时可满足（4 顶点路径最小；奇数星在一个层内塌缩后第二相位无出边）。
- **B4 随机化**（第一百零八–一百一十一批补充）：`Prob.lean` 现在给出有限均匀概率、期望、Markov 不等式、`E[2^{X_H}] ≤ (1+2/t)^m`、尾界 `P[X_H ≥ s] ≤ e^{2m/t}/2^s`、Claim 3.12 的 `P[Bad] ≤ |A|²(1−1/t)^k` 与成功概率 `≥ 1−e^{−2}`，并由正概率重推分离样本的存在性；第一百零九批把固定底数换成任意矩母函数族（`genEdge_le_real`／`weighted_sum_le_real`／`unifExpect_mgf_le`／`chernoff_tail`／`unifExpect_lost_le`／`half_schedules_good`／`lost_tail_prob_paper`，后者即“坏调度至多占 `1/|Hs|`”）；第一百一十–一百一十一批新增 `ProbUnion.lean`，补上论文同时避开多事件所需的并集界、Bonferroni（`unifProb_all_good_ge`）、乘积空间独立性（`unifProb_indep`），并沿“独立采样 + 对坏对取并”重推 Claim 3.12（`unifProb_agreeTuples`／`unifProb_agreeTuples_le`／`bad_prob_le_via_union`／`bad_prob_le_union`），与 `Sampling.bad_prob_le` 的计数链结论一致、路径不同。边界保持：算法本身按论文保持**确定性**（随机性只用于证明存在），仍无 randomized running time，也无测度论概率空间；Claim 3.5/3.6 的 `hsup` 仍是数据假设，Lemma 3.10（义务 4）未动。
- **B5 义务 4**（`CallOut` 构造的完整数值收尾）按约定不在范围。
- **B6 好调度与批次是「联合选择」**（第一百一十五批）：`InstanceHistory.exists_good_scheduleOn` 只证明**存在**某个好调度（对固定的 `LegalOn` 历史族，平均丢失量 `≤ (2√2+4)t²√(|E₀||P|) + 2|E₀|/t`），而驱动里的 `hsupply`（每轮每点有 `F` 外批次边）与 `DriverSelect.ofSchedule` 的供给前提都**耦合于被选中的 `slot`**，即「schedule 与 batch 一起选」这一步——论文只写一句话，仓库尚未把二者作为同一个选择的输出。因此 `evidenceOn_of_good_schedule` 的前提 (a) 是「实际选中的 `ρ` 恰好满足结论」，不是由算法选择推出。另需 `hB : ∀ i j, B i j ⊆ E₀`：`DriverCall.ofSlot` 取 `B := univ`（辐条取全局关联边），只有在 `E₀ = univ` 时满足，故实例局部计数与 `ofSlot` 之间还差「批次取本实例的边」这一条（`ofSchedule` 路线可以承接）。第一百一十六批补充：`DriverWitness.callPar` 证明 `DriverCall` 的五条决策字段（含 `hsupply`）**同时可满足**，`callPar_legalOn` 又把 `history_legalOn` 落到这个真实驱动上——B6 是「选择的正确性」而非「前提互不相容」。

## 第一百一十四批：逐调用数值界由数据推出（`PerCallCount.lean`）

`LevelWork` 把 `hU`（§3.5：`|U| ≤ 10t²√(mn)+4m/t`，`m=|E₀|`）与 `hrnd`（p.24：`Σ|kidE| ≤ |U|+2t²(n−1)+t(n−1+r²n)`，`r=8t³`）当数据前提。本批把两者变成结论：

- `KidBoundCall`：一次调用的归派数据（`inp p ⊆ U(F) ∪ ⋃roundIn ∪ ⋃blkIn`，逐轮 `≤2(n−1)`，逐块 `≤(n−1)+r²n`）；`KidBoundCall.ofForests` 可用论文分解「旧森林+新森林」「旧森林+门边」推出这两个大小（`InputCount` 的两条引理）。
- `KidBoundCall.hrnd`／`hrnd_cast`／`hrnd_level`：ℕ、ℝ、层形（`t=γ(d+1)³`）三版。
- `EvidenceOn.herrU`／`herrU_level`：§3.5 的界在同一次调用上的重述。
- `sum_kidE_driverStrategy`／`U_driverStrategy`（等式搬运，避免在不等式里重写依赖指标）、`hrnd_strategy`／`herrU_strategy`：搬到合成策略 `driverStrategy`。
- `herrU_chain`／`hrnd_chain`、`display_of_driver_derived`／`work_linear_of_driver_derived`／`driver_display_and_work_derived`：沿层链盖章，结论与 `display_of_driver`／`strategy_display_and_work` 相同但不假设两项数值界。
- 非空真与边界：`level_t_of_nat`（`γ=16` 时层 `t` 是自然数）说明逐调用层形前提可满足；链版本仍带逐调用识别 `htd`，全局版本被 `htd_all_roots_impossible` 否证。因此该批闭合的是「数据 ⟹ 逐调用数值界」这一步；程序的归派数据与查询一致性本身仍属待产出项（义务 1 的可执行定义），概率部分仍是已证的采样估计（B4），RAM 模型（B2）与义务 4 不在范围。

## 第一百一十五批：实例局部的 Lemma 3.10/3.11 与 `EvidenceOn` 的真值构造（`InstanceHistory.lean` / `DriverEvidence.lean`）

`DriverCall.EvidenceOn` 的四个字段此前全是前提。本批把其中三个变成定理，并补上此前缺的实例局部计数：

- **实例局部 Lemma 3.10**（`InstanceHistory.lean`，413 行）：`degOn G E₀ v`（`E₀` 内度数）、`sum_degOn_le`（`≤ 2|E₀|`）、`sum_log_degOn_le`（`∑ log(deg+1) ≤ 2√(2|E₀||P|)`，走 `Selection.test_budget`）、`SpokeOKOn`＋`card_spokeOKOn_le`（辐条数 `≤ ∏_{v∈P}(degOn v+1)`；`P` 外的辐条只能是 `e₀`，靠 `hends` 排除）、`card_subsetsOn_le_choose`（E₀-幂集曲棍球棒）、`card_historiesOn_le`／`log_card_historiesOn_le`（`m=|E₀|`、`n=|P|`）。配合 `History.lemma311_on` 得到 **`exists_schedule_lostOn_paper`**——正是 `EvidenceOn.hlost` 的表达式。
- **非空性**：`canonicalHistory`（常值 `e₀`、空森林）+ `legalOn_canonical`，确保 `univ.filter (LegalOn …)` 非空，故 `exists_good_scheduleOn` 不是空洞的「∃ 空集上的调度」。
- **真值证据**（`DriverEvidence.lean`，141 行）：`history_legalOn` 把驱动的 `history` 认成 `LegalOn`（辐条：`selAt_nonempty_of_adm`＋`spokeTable_mem`＋`sel_sub`；森林：`forestUpTo_sub`＋`roundData_F_sub`＋`card_le_card_sub_one_of_isForest_of_ends`）；`truthCand` 是「历史自己的偏好」这一候选；`evidenceOn_of_good_schedule` 组装出 `EvidenceOn`，其中 `hc`（`truth_of_historyOn`）、`agree`（`agree_truthOn`）、`hlost`（好调度假设）分别是定理；`card_U_le_number_bound_of_truth` 给出实例级 `|U| ≤ 10t²√(|E₀||P|) + 4|E₀|/t`。
- **剩余前提**：`evidenceOn_of_good_schedule` 只需要 (a) 调用自己的 `sched` 恰好满足平均界（B6：与 `hsupply` 耦合的联合选择未形式化）与 (b) Lemma 3.7 的逐边 `edge_ok`；另有 `hB : B ⊆ E₀`。`exists_good_schedule` 只把 (a) 降成「∃ 某个好 `ρ`」，并未消除选择问题。

## 第一百一十六批：`DriverCall` 接口的非空性见证（`DriverWitness.lean`）

第一百一十五批的 `LegalOn` 只有 `canonicalHistory` 一个住客；`DriverWitness` 给出一个同时满足 `DriverCall` 全部字段的真实调用：

- 图 `Gpar`：`V = Fin 2`、`E = Fin 5`，五条平行边 `0 → 1`（权重 0..4）；`incident_all` 机检「每条边关联每个顶点」。
- `preF_par_card_le`：`t=1` 的单槽扫描森林是两顶点上的森林，`card_le_card_sub_one_of_isForest_of_ends` 给 `≤ 1` 条。
- **`callPar`**：`P = E₀ = univ`、`Pp = ∅`、`B := univ`、`quota = 1`；`hsupply` 由「`univ ⊄ preF`（`1 < 5`）」给出 —— 每个顶点都有一条 `F` 外批次边。
- `callPar_nonempty`：`Nonempty (DriverCall Gpar univ univ 1)`；`callPar_legalOn`：`history_legalOn` 在该调用上实例化，`LegalOn univ univ 0 callPar.history`。

口径：这是**模型层面**的非空性（接口字段可同时满足、且能喂给 §3.4 的实例局部引理），不声称算法在该图上产生此调用；`edge_ok` 与「自己的 schedule 好」仍是 B6 下的两条前提。

## 第一百一十七批：停机接口的 `4/3`（`StopFourThirds.lean`）

`mst_main_stop` 只给 `|F| ≤ |P| − 1`，而 `mst_main_root_conn` 直接写 `3|F| ≤ 4|P|`；两者之间那条显然的蕴含一直没写。本批补上：

- `answer_three_fourths`：望远镜自己的答案 `answer G P E₀ D ∅` 满足 `3|F| ≤ 4|P|`（`tower_msf_of_stop_card` + `0 < |P|`，`omega`）。
- `mst_main_stop_three_fourths`：与 `mst_main_root_conn` 同形的 `∃ F, IsMSFOf G E₀ F ∧ 3|F| ≤ 4|P|`，前提与 `mst_main_stop` 完全相同。
- `stop_witness_three_fourths`：在 `StopWitness` 的四顶点见证上实例化，故 `4/3` 形式与停机形式同住客、非空洞。

无界激活版仍空洞（B3 不变）；本批只是把「§4 的 `4/3` 预算」在可满足路线上写成逐字命题。

## 第一百一十八批：小实例上「好调度」前提自动成立（`SmallInstance.lean`）

B6 的前提 (a) 在递归基上不需要平均：

- `History.lostOn_le_card`：丢失数是 `E₀` 的子集过滤，故 `≤ |E₀|`。
- `lostOn_log_le_of_bound`：若 `|E₀|·log 2 ≤ B`，则**任意** `ρ` 都有 `lostOn·log 2 ≤ B`（`mul_le_mul_of_nonneg_right` + `Real.log_nonneg`）。
- `callPar2`（`t = 2` 的见证）、`preF_par_card_le_t`（扫描森林 ≤ 1 条，任意 `t`）、`callPar2_hbig`（`5·log2 ≤ 4(2√2+4)√10+5`）、`callPar2_good`（见证自己的调度无条件好）。
- `callPar2_evidence`：`EvidenceOn`，其中 `hc`／`agree`／`hlost` 全部从数据推出；`callPar2_card_U`：同一前提下 `|U| ≤ 40√10+10`。

于是 §3.5 的整条链在一个真实驱动调用上跑通，唯一剩的前提是 Lemma 3.7 的逐边 `edge_ok`；B6 的「联合选择」只在大实例上才是真约束。

## 第一百一十九批：Lemma 3.7 的 `bad` 形式（`Lemma37Bad.lean`）

- `errOf_truth_iff`：`e ∈ E₀` 时，`errOf (estOfOn E₀ R.sched (truthCand R)) e (R.sched e) ↔ badFor e (R.sched e)`（`estOfOn_of_mem` + `truthCand` 的定义）。
- `evidenceOn_of_good_schedule_badFor`：`EvidenceOn` 的 `edge_ok` 换成 `∀ e ∈ E₀, ¬supported → badFor`。
- `card_U_le_number_bound_of_badFor`：逐调用界 `|U| ≤ 10t²√(|E₀||P|) + 4|E₀|/t` 同前提。

于是驱动侧剩余的**过程**前提只剩一句：**不支持的实例边在自己的轮次是坏轮**（Lemma 3.7 逐字），其从层链/扫描记录推出的过程侧工作仍未写。

## 第一百二十批：平行边见证的每条边都被支持（`WitnessSupported.lean`）

第一百一十九批之后，逐边前提在 `DriverWitness` 见证上被证明为空：

- `scan_zero_eq`：`scanOfSlot (t:=2) slotPar2 univ univ 0 = univ.sort (·≤·)`（`slotPar2` 恒为 0，第 0 轮过滤保留全部）。
- `sort_univ_ne_nil`（`Finset.length_sort`：排序长度 = `card = 5`）、`weight_le_of_fin_le`（`Fin` 序 `≤` 即权 `ℝ` 序）、`eq_of_conn_empty`（空集上的 `Conn` 只可能是 `refl`）。
- **`head_kept`**：排序后取首元素 `a`；`pairwise_sort` 给 `a` 比尾表每个元素都轻；`step_accept`（`¬ Conn ∅ 0 1`）把首轮累加器变成 `insert a ∅`，`K_mono` 把 `a` 送进 `K`，`preF_mono` 升到 `2^2`。故返回森林里有一条比所有边都轻的边。
- **`all_supported`**：对任何 `e`，`a ∈ F.filter (· ≤ w e)`，`Conn.step` 给出 `0→1` 连通，即 `supported`（五条边都是同一个 `0→1`）。
- 推论：`callPar2_unsupp_empty`（`unsupp = ∅`）、`callPar2_U_eq_empty`（`U = ∅`）、`badFor_vacuous`（逐边前提空真）、**`callPar2_evidence_uncond`**（`EvidenceOn` **无任何前提**的居留者）、`callPar2_card_U_uncond`。

诚实读法：该见证上数值界**没有内容**（`U` 为空，`|U| ≤ 40√10+10` 由 `0 ≤ …` 平凡成立）。这一批证成的是 `EvidenceOn` 接口（`hc`／`edge_ok`／`hlost` 同时成立）**可居留**——比接口字段可满足（批次 116）更强——而不是一般实例的 Lemma 3.7；一般实例的 `badFor` 过程侧推导仍是未写项（B6 不变）。

## 第一百二十一批：`badFor` 过程侧的 `t=1` 自证与层级链合成（`ProcDriver.lean`）

- **`History.badFor_one`**：`t=1` 时 `badProject` 的「块内更晚轮次全 `find`」与 `badFind` 的「更晚块全 `find`」都量化在空集上，故**每个**轮次对**每条**边都是坏轮；`DriverCall.badFor_of_unsupp_one` 随即给出任意图/实例的单轮调用上 Lemma 3.7 逐边前提的无条件形式（注意：这是定义性坍塌，不含算法内容）。
- **`evidenceOn_of_good_schedule_one`**：`t=1` 的 `EvidenceOn` 只剩好调度（B6）、`hB`、`0<|P|`；数值界仍要 `2 ≤ t`。
- **`history_spoke_incident`**：驱动历史的辐条必关联，由 `hsupply` 经 `historyOfTable_spoke_incident` 推出——`ProcChain.hspoke` 在驱动调用上不是假设。
- **一般 `t`**：`badFor_of_procChains`／`evidenceOn_of_procChains`／`card_U_le_number_bound_of_procChains` 由每条边一条层级链推出 `hbad` 并接上 §3.5 整条链；`hcons`＝`history_consistent`、`hspoke`＝`history_spoke_incident` 已由接口给出，剩余过程义务精确为 `hproj`／`hfroz`／`hret`／`hsub`／`hmsf`／`hlift`／`hσS`。
- 见证：`callPar_one_hbig`（`5·log2 ≤ (2√2+4)√10+10`）、`callPar_one_good`、**`callPar_evidence_uncond`**（`t=1` 见证的无前提 `EvidenceOn`；`lost = 5` 使损失界非平凡，而 `U=∅` 使最终 `|U|` 界平凡）。

## 第一百二十二批：驱动形态的层级链（`ChainDriver.lean`）

第一百二十一批的合成仍以「每条边一条 `ProcChain`」为开销，且 `hfroz` 是链的字段。本批把它压到驱动接口能直接供给的形态：

- **`ProcChain.unSupp_errOf_on`／`DriverCall.badFor_of_procChainsOn`**：链只建在 `E₀` 上（`∀ e ∈ E₀, ProcChain`），与 `hbad` 的量词一致，省掉 `E₀` 外的空链。
- **`DriverCall.history_spoke_frozen`**：块内批次冻结 `∀ b i j, B b i = B b j` 时，`spokeOf` 只依赖 `B b i`／`adm`／`quota`，故同一块各轮辐条逐点相同；于是 `ProcChain.hfroz` 由接口推出，不再是过程假设。
- **`ProcChain.ofDriver`**：把 `hcons`（`history_consistent`）、`hfroz`（上一行）、`hspoke`（`history_spoke_incident`）内联，链的其余字段即算法数据。
- **`DriverCall.badFor_of_driverChains`**：只剩 `hproj`／`hret`／`hsub`／`hmsf`／`hlift`／`hσS`、根识别 `h0e`／`h0F`／`hslot0` 与子层支持 `hchild`。

结构性发现（记账）：`DriverCall.cls` 只记录扫描轮次，不含 project/find 决策；模型里也没有「子调用返回并入森林」的状态。故 `hproj` 与 `hret` **不能**从驱动接口推出，它们是真算法义务，需要把递归与决策写进模型。

## 第一百二十三批：链接口的形状与驱动形态的整链（`ChainShape.lean`）

**新边界 B7（接口与论文证明结构不同构）**：

- **`ProcChain.childF_nonempty`**：`hloop : ∀ f, src f ≠ dst f` 下，任何层的孩子森林 `(lev (j+1)).F` 非空。证明：`hmsf` 给孩子森林「张成 `S j`」；`hσS` 把该层辐条 `σ (src (lev j).e)` 放进 `S j`；张成要求 `∅` 连通辐条两端；`conn_empty_eq` 只允许 `refl`，与无自环矛盾。
- **`not_chain_of_empty_child`／`not_chain_of_eventually_empty`**：孩子森林为空（或从某层起全空）就**没有** `ProcChain`。
- 结论：`ProcChain` 要求每一层都投影并带 MSF 调用与提升路径，故它表示**无休止自持**的链；论文的链在深度 `d` 处停下（`Rounds.lemma37_error` 的 `hfind : ∀ j ≥ d, Lev.supp` 与只对 `j < d` 的投影步）。链路线的定理仍是可靠真命题，但其前提是**充分证书**，不是论文过程的忠实刻画；忠实刻画要把逐调用递归与子调用返回写进模型（与 B1 的模型不相容问题同源）。

**新边界 B8（模型的森林是分段 Kruskal，动作规则与它无联系）**：`RoundScan.preF` 是 `preF (k+1) = K G (sc k) (preF k)`，`ofScan` 取 `Fr r = preF (r+1)`——调用森林是按调度**分段做 Kruskal**（分段而非全局排序，故可不最优，这正是 `lostOn` 的来源）；而历史动作 `pref` 由 `actOf`／`prefFind`（门户判据）另行定义，二者在模型中无联系。所以「`e` 自己那轮的动作是 `project`」（`hproj`）是**真正的算法内容**，不能从森林数据推出；第一百二十九批的互斥性（`LightVacuous.supported_of_light_and_child`）进一步说明轻辐条也替代不了它。过程侧目前的完整前提 = `hproj` + `hmsf`／`hlift`（子调用返回）+ 接口事实，`hσS`（126 批）、`hret`／`hsub`（127 批）已推出。

**整链（过程侧的单一入口）**：

- `DriverCall.evidenceOn_of_driverChains`、`DriverCall.card_U_le_number_bound_of_driverChains`：以 `hBfroz` + 算法义务 `hproj`／`hret`／`hsub`／`hmsf`／`hlift`／`hσS` + 根识别 `h0e`／`h0F`／`hslot0` + `hchild` + 好调度 + `hB` + `0<|P|`（数值界另需 `2 ≤ t`）推出 `EvidenceOn` 与 §3.5 的逐调用界。

## 第一百二十四批：单层步骤接口，`hchild` 冗余（`OneStep.lean`）

- **`StepData`**：`ProcChain` 在单层的全部数据——slot `(b, r)`、层森林 `F`、孩子森林 `F₁`、子实例 `S`、提升路径 `es`，以及 `hcons`／`hproj`／`hfroz`／`hret`／`hsub`／`hmsf`／`hspoke`／`hlift`／`hσS`。没有 `ℕ` 索引的对象，B7 的形状问题在驱动路线上消失。
- **`StepData.step_error`**：层森林不支持 `e` ⟹ `error` 在 `(b,r)`。**不需要**「孩子支持」：`lemma37_project_error` 只要 `conn`，而 `claim_3_6` 用 `hmsf`／`hspoke`／`hlift`／`hσS` 无条件给出它——论文的「若子递归支持」正是 `hlift`。
- **`StepData.badFor`**：真值估计下估计分支是 `a ≠ a`，故直接得 `H.badFor e (b, r)`。
- **`ProcChain.stepData`**：链在每层给出 `StepData`（新接口更弱）。
- **`DriverCall.badFor_of_stepsOn`**：每条实例边一层数据 ⟹ 逐边句子；**`badFor_of_procChains_noChild`**：链路线去掉第一百二十二批的 `hchild`（它在 `level_error`／`errorOr_unsupp`／`unSupp_errOf` 里都未被使用）。
- **`evidenceOn_of_steps`／`card_U_le_number_bound_of_steps`**：`EvidenceOn` 与 `|U| ≤ 10t²√(|E₀||P|)+4|E₀|/t`，前提 = 逐边 `StepData` + `2 ≤ t` + `hB` + `0<|P|` + 好调度。

## 第一百二十五批：投影判据（`ProjectRule.lean`）

- **`not_prefFind_of_unsupp`**：若 `σ (src e)`、`σ (dst e)` 都关联、门户相异、且 `w(σu), w(σv) ≤ w(e)`，则不支持 `e` 满足 `¬ prefFind`。逐款排除：前两款被关联性否掉，第三款被门户相异否掉，第四款 `Conn (F≤p(e))` 连同 `p(e) ≤ w(e)`（`pmax = max`）经 `belowLe_mono` + `Conn.mono` 推出 `supported`，矛盾。
- **`supported_mono`**：`F ⊆ F'` 时 `supported F e → supported F' e`。
- **`DriverCall.pref_project_of_unsupp`**：记录 `= actOf`（`history_consistent`）+ 本轮森林 ⊆ 调用森林（`forestUpTo_sub`）+ 上一条 ⟹ 不支持边在 `e` 自己的 slot 取 `project`。这是「`hproj` 不是自由数据」的机检版本。
- **`StepData.ofDriver`**：`hcons`、`hfroz`（块内批次冻结）、`hspoke` 自动填充。
- **`badFor_of_stepObligations`／`evidenceOn_of_stepObligations`／`card_U_le_number_bound_of_stepObligations`**：逐边义务 = 一层数据（`hproj`、`hret`、`hsub`、`S`、`es`、`hmsf`、`hlift`、`hσS`）。

## 第一百二十六批：辐条属于本轮批次，几何化每边义务（`SpokeInst.lean`）

- **`DriverCall.history_spoke_mem_B`**：`R.history.spoke b i v ∈ R.B b i`。表历史的辐条是 `spokeOf`（`spokeTable_mem` ⟹ 属 `selAt`），`BatchSpec.sel_sub` 给 `selAt ⊆ Bv`，`mem_Bv` 给 `Bv ⊆ B`。
- **`DriverCall.history_spoke_mem_of_batch`**：`R.B b i ⊆ S` ⟹ `∀ x, R.history.spoke b i x ∈ S`，即 `hσS` 由「本轮批次是子实例的边」推出（递归输入口径）。
- **`DriverCall.badFor_of_geomObligations`**：`hcons`／`hfroz`／`hspoke` 由接口、`hproj` 由投影判据（第 125 批）、`hσS` 由批次包含，逐边义务只剩 `hret`／`hsub`／`S`／`es`／`hmsf`／`hlift` 与几何三条（门户相异、两辐条不重于 `e`）及 `B b i ⊆ S`。
- **`evidenceOn_of_geomObligations`／`card_U_le_number_bound_of_geomObligations`**：`EvidenceOn` 与 `|U| ≤ 10t²√(|E₀||P|)+4|E₀|/t` 接在上述几何化义务上。

## 第一百二十七批：森林随轮次单调，时序义务消去（`ForestMono.lean`）

- **`CallOut.forestUpTo_mono`**：`roundIdx t r₁ ≤ roundIdx t r₂ ⇒ forestUpTo D r₁ ⊆ forestUpTo D r₂`（前缀并集随轮号放大）。
- **`DriverCall.history_forest_mono`**：`i ≤ j ⇒ R.history.forest b i ⊆ R.history.forest b j`（`roundIdx_le_of_le`）；**`history_forest_sub_F`**：任何前缀森林 ⊆ `R.roundData.F`（`forestUpTo_sub`）。
- **`nextForest R e`**：`e` 的轮次之后下一轮的前缀森林（`e` 在块末轮时取 `R.roundData.F`）；**`hret_nextForest`**（单调性给出 `hret`）、**`nextForest_sub`**（`hsub`）。
- **`badFor_of_geomObligations_next`／`evidenceOn_of_geomObligations_next`／`card_U_le_number_bound_of_geomObligations_next`**：`hret`／`hsub` 不再作为前提；剩 `hmsf`／`hlift`（关于 `nextForest`）、`S`／`es`、`B b i ⊆ S` 与几何三条。
- 口径：驱动模型无子调用返回状态（B1），`nextForest` 是模型内唯一可见的候选；本批消去的是时序义务，不是 MSF 正确性。

## 第一百二十八批：辐条轻量条件的选择集来源（`SpokeLe.lean`）

- **`DriverCall.history_spoke_weight_le_of_mem`**：`e ∈ selAt G (B b i) adm quota v` ⟹ `w(spoke b i v) ≤ w(e)`（`spokeOf_le` 加权序 `OrderedByWeight`）。
- **`badFor_of_selObligations`／`evidenceOn_of_selObligations`／`card_U_le_number_bound_of_selObligations`**：把「辐条不重于 `e`」换成两端的选择集成员条件。
- 口径：`selAt` 是「按另一端分组取最轻、截断 `quota` 个」的最轻集，强于论文的「批内最轻边」；`e ∈ B → 辐条 ≤ e` 需要轮内扫描次序，模型未记录，故停在成员条件。
- **注意**：本批的端到端封装随后被第一百二十九批证明为**空真**（见下）。

## 第一百二十九批：轻辐条与子实例支持互斥，更正第 126／128 批（`LightVacuous.lean`）

- **`DriverCall.supported_of_light_and_child`**：轻辐条（`e` 在两端 `selAt` 中，故 `pE ≤ w(e)`）＋子实例 MSF（`hmsf`）＋提升路径（`hlift`）⟹ `claim_3_6` 的连通在 `max{w(e), pE} = w(e)` 处，经 `nextForest_sub` 搬回调用森林 ⟹ `supported G R.roundData.F e`。
- **`unsupp_false_of_light_and_child`**：轻辐条＋子实例支持＋**不支持**三者不能同真。
- **`pE_gt_of_unsupp`**：在不支持分支里，子实例连通在 `max{w(e),pE}` 处，故只能是 `pE > w(e)`（论文的无效投影分支）。
- **更正**：第 126 批 `badFor_of_geomObligations`、第 127 批 `badFor_of_geomObligations_next`、第 128 批 `badFor_of_selObligations` 都把 `hproj` 由轻辐条推出；在不支持分支里这些前提互斥，结论**空真**，**没有消去 `hproj`**。非空路线是第 125 批的 `badFor_of_stepObligations`（`hproj` 作前提）与第 124 批的 `StepData`。论文里不支持边若子递归支持投影就会在本层被支持，故真正的不支持只出现在无效投影分支，那里 `hlift` 本身失败。

## 一句话结论

**§2/§3 的图论地基与计数骨架逐字或加强地机检通过；§3.6–§3.7 的显示层在 `CallOut` 假设下闭合，层模型「各层规模之和」的线性已机检到论文自己的逐调用计数（`LevelLinear.lean` + `LevelWork.lean`，无统一常数、无边减半、无 `htd`）；第一百一十四批进一步把该层的两项逐调用数值界（§3.5 估计、p.24 输入计数）从驱动数据推出（`PerCallCount.lean`：逐调用版非空真，链级版带 `htd` 识别）；第一百一十五批把 §3.4 的 Lemma 3.10/3.11 搬到**实例口径**（`InstanceHistory.lean`，`m=|E₀|`、`n=|P|`，合成 `exists_schedule_lostOn_paper`）并把 `EvidenceOn` 的 `hc`／`agree`／`hlost` 变成定理（`DriverEvidence.lean`），只剩「调用自己的调度是好的」（B6：与供给耦合的联合选择）与 Lemma 3.7 的逐边 `edge_ok` 两条前提（第一百一十六批又证明该接口连同 `hsupply` 在具体图上可满足，`DriverWitness.callPar`；第一百一十七批把停机接口的 `4/3` 显示补成机检命题 `StopFourThirds.mst_main_stop_three_fourths`；第一百一十八批又证明「好调度」前提在小实例上自动成立，并在 `t=2` 的真实驱动上把 §3.5 整条链跑到「只剩 `edge_ok`」；第一百一十九批再把 `edge_ok` 化成 Lemma 3.7 的 `bad` 形式 `errOf_truth_iff`／`card_U_le_number_bound_of_badFor`；第一百二十批证明平行边见证的每条边都被支持，从而 `EvidenceOn` 在该调用上**无前提居留**、`U=∅`，数值界平凡；第一百二十一批证明 `t=1` 时逐边前提按定义自明（`History.badFor_one`），并把一般 `t` 的 `hbad` 合成到每条边一条 `ProcChain`，其中 `hcons`/`hspoke` 已由驱动接口给出；第一百二十二批再把链收紧到实例边、由批次冻结推出 `hfroz`，逐边前提只剩算法义务 `hproj`/`hret`/`hsub`/`hmsf`/`hlift`/`hσS`、根识别与 `hchild`；第一百二十三批证明该链接口要求每层孩子森林非空、因而只表示无休止投影的链，与论文的有限链不同构（B7），并把整条驱动形态接成 §3.5 界的单一入口；第一百二十四批改为一层数据的 `StepData`（驱动路线不再需要链），并证明「孩子支持」前提 `hchild` 是冗余的（它已被 `hlift` 编码），过程侧只剩逐边一层的算法数据；第一百二十五批把其中唯一「由状态决定」的 `hproj` 也推出（投影判据：辐条关联 + 门户相异 + 辐条不重于边 + 不支持 ⟹ `project`）；第一百二十六批再把 `hσS` 推出（辐条取自本轮批次，批次 ⊆ 子实例即可），逐边义务只剩算法数据 `hret`/`hsub`/`S`/`es`/子实例 `hmsf`/`hlift` 与几何三条；第一百二十七批证明 `hret`／`hsub` 对前缀森林自动成立（`nextForest`，`forestUpTo_mono`），逐边义务只剩关于该具体森林的 `hmsf`／`hlift` 与 `S`／`es`；第一百二十八批把「辐条不重于 `e`」化为选择集成员（`history_spoke_weight_le_of_mem`），第一百二十九批再**更正**：轻辐条＋子实例支持＋不支持三者互斥（`supported_of_light_and_child`），故第 126–128 批把 `hproj` 由轻辐条推出的封装在 `¬supported` 分支**空真**，`hproj` 仍是算法义务前提——非空路线是第 125 批 `badFor_of_stepObligations` 与第 124 批 `StepData`）；§4 的单步收缩与交换论证逐字通过；§4 的 4/3 塔的无界激活版前提不自洽（空洞），但第 112–113 批给出两条可满足的正面定理：自选停止深度版（有界激活、`hstop` 由测度推出）与**无条件版**（以连通性取代激活，MSF + `|F| ≤ |P|−1` + `3|F| ≤ 4|P|` 全无条件）；基于测度的 `|P|/4^d` 账仍属有界激活版。** 因此可以说的仍是「可信，未确认」，不能说「论文经过形式化验证」。
