import DLMST.SpokeLe

/-!
# 第 129 批：轻辐条与子实例支持互斥（更正第 126／128 批的空真封装）

第 126 批把 `hproj` 由投影判据（第 125 批）推出，第 128 批再把「辐条不重于 `e`」化为选择集
成员条件。复查发现一个必须记账的事实，本批把它机检下来：

**若 `e` 两端的辐条都不重于 `e`（`pE ≤ w(e)`），而子实例 `S` 的 MSF `F₁` 支持 `e` 的投影
（`hlift`），那么 `e` 在本层森林里就是被支持的**（`claim_3_6` 的连通在 `max{w(e), pE} = w(e)`
处，经 `hsub` 搬回调用森林）。因此在**不支持**分支里，第一条前提必假：`pE > w(e)`。

推论（本批要记录的口径）：
* 第 126 批的 `badFor_of_geomObligations`、第 127 批的 `…_next`、第 128 批的
  `badFor_of_selObligations` 都以「轻辐条 + 子实例支持 + 不支持」为前提；这三条在同一分支里
  互不相容，故这些封装的 `badFor` 结论是**空真**的，它们没有消去 `hproj`；
* `hproj`（`e` 自己那轮的动作为 `project`）仍是**算法义务**，不能由轻辐条推出——论文的
  project 情形正是把「实际动作是 `project`」当作用户可见的轮次状态（第 124 批的 `StepData.hproj`），
  其结论 `badFor` 的「坏轮」部分也含 `hproj`。

真正非空的路线仍是第 125 批的 `badFor_of_stepObligations`（`hproj` 作前提，其余义务由接口
与几何给出）以及第 124 批的 `StepData` 单层接口。
-/

namespace DLMST

open Classical

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

namespace DriverCall

variable {P : Finset V} {E₀ : Finset E} {t : ℕ} [Nonempty E]

/-- **轻辐条 + 子实例支持 ⟹ 支持。** 辐条两端都在本轮选择集中（故 `pE ≤ w(e)`），子实例 MSF
经提升路径连上 `e` 的两端（`claim_3_6`，阈值 `max{w(e), pE} = w(e)`），再经 `hsub` 搬回调用森林。 -/
theorem supported_of_light_and_child (R : DriverCall G P E₀ t) (hw : OrderedByWeight G) {e : E}
    (hselU : e ∈ selAt G (R.B (R.sched e).1 (R.sched e).2)
      (fun f => f ∉ R.roundData.F) R.quota (G.src e))
    (hselV : e ∈ selAt G (R.B (R.sched e).1 (R.sched e).2)
      (fun f => f ∉ R.roundData.F) R.quota (G.dst e))
    (S : Finset E) (hBS : R.B (R.sched e).1 (R.sched e).2 ⊆ S)
    (hmsf : IsMSFOf G S (nextForest R e)) (es : List E)
    (hlift : LiftsLe G (R.history.spoke (R.sched e).1 (R.sched e).2) S (G.weight e)
      (portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.src e)) es
      (portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.dst e))) :
    supported G R.roundData.F e := by
  have hsp : ∀ x, incident G x (R.history.spoke (R.sched e).1 (R.sched e).2 x) :=
    R.history_spoke_incident (R.sched e).1 (R.sched e).2
  have hwu := R.history_spoke_weight_le_of_mem hw hselU
  have hwv := R.history_spoke_weight_le_of_mem hw hselV
  have hp : pE G (R.history.spoke (R.sched e).1 (R.sched e).2) e ≤ G.weight e :=
    max_le hwu hwv
  have hσS : ∀ x, R.history.spoke (R.sched e).1 (R.sched e).2 x ∈ S :=
    fun x => R.history_spoke_mem_of_batch hBS x
  have hconn := claim_3_6 hmsf hsp hlift hσS
  rw [max_eq_left hp] at hconn
  exact hconn.mono (belowLe_subset (R.nextForest_sub e) _)

/-- **不支持分支里前提互斥（第 126／127／128 批封装的空真性）**：轻辐条 + 子实例支持 + 不支持
三者不能同真。 -/
theorem unsupp_false_of_light_and_child (R : DriverCall G P E₀ t) (hw : OrderedByWeight G) {e : E}
    (hselU : e ∈ selAt G (R.B (R.sched e).1 (R.sched e).2)
      (fun f => f ∉ R.roundData.F) R.quota (G.src e))
    (hselV : e ∈ selAt G (R.B (R.sched e).1 (R.sched e).2)
      (fun f => f ∉ R.roundData.F) R.quota (G.dst e))
    (S : Finset E) (hBS : R.B (R.sched e).1 (R.sched e).2 ⊆ S)
    (hmsf : IsMSFOf G S (nextForest R e)) (es : List E)
    (hlift : LiftsLe G (R.history.spoke (R.sched e).1 (R.sched e).2) S (G.weight e)
      (portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.src e)) es
      (portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.dst e)))
    (hnot : ¬ supported G R.roundData.F e) : False :=
  hnot (R.supported_of_light_and_child hw hselU hselV S hBS hmsf es hlift)

/-- 同一条的「不支持 ⟹ `pE > w(e)`」形态：轻辐条与不支持不能同真。 -/
theorem pE_gt_of_unsupp (R : DriverCall G P E₀ t) {e : E}
    (hnot : ¬ supported G R.roundData.F e) (hsub : nextForest R e ⊆ R.roundData.F)
    (hconn : Conn G (belowLe G (nextForest R e)
      (max (G.weight e) (pE G (R.history.spoke (R.sched e).1 (R.sched e).2) e)))
      (G.src e) (G.dst e)) :
    ¬ (pE G (R.history.spoke (R.sched e).1 (R.sched e).2) e ≤ G.weight e) := by
  intro hp
  rw [max_eq_left hp] at hconn
  exact hnot (hconn.mono (belowLe_subset hsub _))

end DriverCall

end DLMST