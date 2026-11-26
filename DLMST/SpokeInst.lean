import DLMST.ProjectRule

/-!
# 第 126 批：辐条落在本轮的批次里，以及几何化的每边义务

第 125 批把 `hcons`／`hfroz`／`hspoke` 交给接口，并给出 `hproj` 的推导（投影规则）。本批再收
两件：

1. **`hσS`**：记录里的每条辐条都是 `spokeOf` 从本轮批次 `B b i` 的 `Bv` 中选出的代表，所以它
   落在 `B b i` 里；于是只要本轮批次整体落进子实例 `S`（`B b i ⊆ S`，即「本轮的批次边属于子实例」），
   `hσS`（辐条 ∈ `S`）就自动成立；
2. **几何化的每边义务**：`hproj` 不再作为前提——由入射性（接口）、沿门的两个端点互异、以及
   两根辐条不重于 `e`（这三条都是 §3.5 的几何事实，见第 125 批的投影规则）推出。

由此，`badFor`／`EvidenceOn`／§3.5 数值界 的每边义务收拢为
`hret`／`hsub`／`hmsf`／`hlift` 四条算法数据，加上 `B b i ⊆ S`（子实例包含本轮批次）与几何三条
（门互异、辐条不重）。

本文件不改动任何既有定义，只新增引理与封装。
-/

namespace DLMST

open Classical

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

namespace DriverCall

variable {P : Finset V} {E₀ : Finset E} {t : ℕ} [Nonempty E]

/-- **辐条属于本轮的批次。** 表历史的辐条就是 `spokeOf` 在本轮选择 `selAt` 上的最小值，而
`selAt ⊆ Bv ⊆ B`。 -/
theorem history_spoke_mem_B (R : DriverCall G P E₀ t) (b i : Fin t) (v : V) :
    R.history.spoke b i v ∈ R.B b i := by
  change spokeTable (G := G) R.B (fun e => e ∉ R.roundData.F) R.quota b i v ∈ R.B b i
  have hne : (selAt G (R.B b i) (fun e => e ∉ R.roundData.F) R.quota v).Nonempty :=
    selAt_nonempty_of_adm R.hquota
      (by
        obtain ⟨e, he, hout⟩ := R.hsupply b i v
        refine ⟨e, he, ?_⟩
        rw [roundData_F]
        simpa [sc] using hout)
  have hmem : spokeTable (G := G) R.B (fun e => e ∉ R.roundData.F) R.quota b i v
      ∈ selAt G (R.B b i) (fun e => e ∉ R.roundData.F) R.quota v :=
    spokeTable_mem (G := G) R.B _ R.quota b i v hne
  exact (mem_Bv.mp
    ((batchSpec_selAt G (R.B b i) (fun e => e ∉ R.roundData.F) R.quota).sel_sub v hmem)).1

/-- **`hσS` 由「批次 ⊆ 子实例」推出。** -/
theorem history_spoke_mem_of_batch (R : DriverCall G P E₀ t) {S : Finset E} {b i : Fin t}
    (hBS : R.B b i ⊆ S) (v : V) : R.history.spoke b i v ∈ S :=
  hBS (R.history_spoke_mem_B b i v)

/-- **几何化每边义务 → `badFor`。** 前提只剩：批次块冻结、`e` 的子森林
`F₁ e`（返回时序、落在本层森林内、是其子实例的 MSF、提升路径）、子实例 `S e` 包含本轮批次，
以及 `e` 沿门互异、两根辐条不重于 `e`。`hcons`／`hfroz`／`hspoke`／`hproj`／`hσS` 全部内填。 -/
theorem badFor_of_geomObligations (R : DriverCall G P E₀ t)
    (hBfroz : ∀ b i j, R.B b i = R.B b j) (F₁ : E → Finset E)
    (hne : ∀ e ∈ E₀,
      portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.src e) ≠
        portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.dst e))
    (hwu : ∀ e ∈ E₀,
      G.weight (R.history.spoke (R.sched e).1 (R.sched e).2 (G.src e)) ≤ G.weight e)
    (hwv : ∀ e ∈ E₀,
      G.weight (R.history.spoke (R.sched e).1 (R.sched e).2 (G.dst e)) ≤ G.weight e)
    (hret : ∀ e ∈ E₀, ∀ i, (((R.sched e).2).val + 1 : ℕ) ≤ i.val →
      F₁ e ⊆ R.history.forest (R.sched e).1 i)
    (hsub : ∀ e ∈ E₀, F₁ e ⊆ R.roundData.F)
    (S : E → Finset E)
    (hBS : ∀ e ∈ E₀, R.B (R.sched e).1 (R.sched e).2 ⊆ S e)
    (es : E → List E)
    (hmsf : ∀ e ∈ E₀, IsMSFOf G (S e) (F₁ e))
    (hlift : ∀ e ∈ E₀, LiftsLe G (R.history.spoke (R.sched e).1 (R.sched e).2) (S e) (G.weight e)
      (portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.src e)) (es e)
      (portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.dst e))) :
    ∀ e ∈ E₀, ¬ supported G R.roundData.F e → R.history.badFor e (R.sched e) :=
  fun e he hnot =>
    (StepData.ofDriver (F := R.roundData.F) (F₁ := F₁ e) R hBfroz
      (R.pref_project_of_unsupp (R.history_spoke_incident (R.sched e).1 (R.sched e).2)
        (hne e he) (hwu e he) (hwv e he) hnot)
      (hret e he) (hsub e he) (S e) (es e) (hmsf e he) (hlift e he)
      (fun x => R.history_spoke_mem_of_batch (hBS e he) x)).badFor hnot

/-- **`EvidenceOn` 从几何化每边义务。** -/
noncomputable def evidenceOn_of_geomObligations (R : DriverCall G P E₀ t)
    (hBfroz : ∀ b i j, R.B b i = R.B b j) (F₁ : E → Finset E)
    (hne : ∀ e ∈ E₀,
      portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.src e) ≠
        portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.dst e))
    (hwu : ∀ e ∈ E₀,
      G.weight (R.history.spoke (R.sched e).1 (R.sched e).2 (G.src e)) ≤ G.weight e)
    (hwv : ∀ e ∈ E₀,
      G.weight (R.history.spoke (R.sched e).1 (R.sched e).2 (G.dst e)) ≤ G.weight e)
    (hret : ∀ e ∈ E₀, ∀ i, (((R.sched e).2).val + 1 : ℕ) ≤ i.val →
      F₁ e ⊆ R.history.forest (R.sched e).1 i)
    (hsub : ∀ e ∈ E₀, F₁ e ⊆ R.roundData.F)
    (S : E → Finset E)
    (hBS : ∀ e ∈ E₀, R.B (R.sched e).1 (R.sched e).2 ⊆ S e)
    (es : E → List E)
    (hmsf : ∀ e ∈ E₀, IsMSFOf G (S e) (F₁ e))
    (hlift : ∀ e ∈ E₀, LiftsLe G (R.history.spoke (R.sched e).1 (R.sched e).2) (S e) (G.weight e)
      (portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.src e)) (es e)
      (portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.dst e)))
    (e₀ : E) (hB : ∀ i j, R.B i j ⊆ E₀) (hP0 : 0 < P.card)
    (hgood : ∀ H : History V E t, LegalOn (G := G) P E₀ e₀ H →
      (H.lostOn E₀ R.sched : ℝ) * Real.log 2 ≤
        (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 *
            Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) + 2 * (E₀.card : ℝ) / (t : ℝ)) :
    EvidenceOn R :=
  evidenceOn_of_good_schedule_badFor R e₀ hB hP0 hgood
    (badFor_of_geomObligations R hBfroz F₁ hne hwu hwv hret hsub S hBS es hmsf hlift)

/-- **§3.5 的数值界从几何化每边义务。** -/
theorem card_U_le_number_bound_of_geomObligations (R : DriverCall G P E₀ t)
    (hBfroz : ∀ b i j, R.B b i = R.B b j) (F₁ : E → Finset E)
    (hne : ∀ e ∈ E₀,
      portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.src e) ≠
        portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.dst e))
    (hwu : ∀ e ∈ E₀,
      G.weight (R.history.spoke (R.sched e).1 (R.sched e).2 (G.src e)) ≤ G.weight e)
    (hwv : ∀ e ∈ E₀,
      G.weight (R.history.spoke (R.sched e).1 (R.sched e).2 (G.dst e)) ≤ G.weight e)
    (hret : ∀ e ∈ E₀, ∀ i, (((R.sched e).2).val + 1 : ℕ) ≤ i.val →
      F₁ e ⊆ R.history.forest (R.sched e).1 i)
    (hsub : ∀ e ∈ E₀, F₁ e ⊆ R.roundData.F)
    (S : E → Finset E)
    (hBS : ∀ e ∈ E₀, R.B (R.sched e).1 (R.sched e).2 ⊆ S e)
    (es : E → List E)
    (hmsf : ∀ e ∈ E₀, IsMSFOf G (S e) (F₁ e))
    (hlift : ∀ e ∈ E₀, LiftsLe G (R.history.spoke (R.sched e).1 (R.sched e).2) (S e) (G.weight e)
      (portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.src e)) (es e)
      (portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.dst e)))
    (e₀ : E) (hB : ∀ i j, R.B i j ⊆ E₀) (hP0 : 0 < P.card) (ht : 2 ≤ t)
    (hgood : ∀ H : History V E t, LegalOn (G := G) P E₀ e₀ H →
      (H.lostOn E₀ R.sched : ℝ) * Real.log 2 ≤
        (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 *
            Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) + 2 * (E₀.card : ℝ) / (t : ℝ)) :
    ((R.roundData.toCall.U).card : ℝ) ≤
      10 * (t : ℝ) ^ 2 * Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) +
        4 * (E₀.card : ℝ) / (t : ℝ) :=
  card_U_le_number_bound_of_badFor R e₀ hB hP0 ht hgood
    (badFor_of_geomObligations R hBfroz F₁ hne hwu hwv hret hsub S hBS es hmsf hlift)

end DriverCall

end DLMST