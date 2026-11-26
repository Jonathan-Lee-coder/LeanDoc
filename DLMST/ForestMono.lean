import DLMST.SpokeInst

/-!
# 第 127 批：森林随轮次单调，`hret`／`hsub` 不需前提

`StepData` 里有两条并非算法内容的「时序」义务：

* `hret`：孩子森林 `F₁` 落在 **`e` 的轮次之后**每一轮的森林里；
* `hsub`：孩子森林 `F₁` ⊆ 本层调用返回的森林 `F`。

本批证明它们对**前缀森林**自动成立：

1. `forestUpTo_mono`：调用森林 `forestUpTo D (b,i)` 随轮号增大（`roundIdx_le_of_le`）；
2. `DriverCall.history_forest_mono`／`history_forest_sub_F`：记录里同一块的森林单调，
   且任何前缀森林 ⊆ `R.roundData.F`（`forestUpTo_sub`）；
3. `DriverCall.nextForest`：把「孩子森林」取为 `e` 的轮次之后**下一轮**的前缀森林（若 `e`
   在块的最后一轮则取整个调用森林），并证明它自动满足 `hret`（单调）与 `hsub`（前缀 ⊆ 全体）。

于是 `StepData` 的 `hret`／`hsub` 可以消去：只要把 `F₁` 取成 `nextForest`，这两条便无需假设。
代价是 `hmsf`／`hlift` 变成对该前缀森林的陈述——在现在的驱动模型里没有「子调用返回」状态
（B1），前缀森林是模型内唯一可见的「孩子森林」。这就是本批要记账的口径。
-/

namespace DLMST

open Classical

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

namespace CallOut

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ} {P : Finset V} {E₀ : Finset E}

/-- **调用森林随轮号单调增大**（前缀并集在两个可比的 `roundIdx` 之间放大）。 -/
theorem forestUpTo_mono (D : RoundData G P E₀ ι t) {r₁ r₂ : Fin t × Fin t}
    (h : roundIdx t r₁ ≤ roundIdx t r₂) : forestUpTo D r₁ ⊆ forestUpTo D r₂ := by
  intro e he
  simp only [forestUpTo, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  obtain ⟨p, hp, hpe⟩ := he
  exact ⟨p, lt_of_lt_of_le hp h, hpe⟩

end CallOut

namespace DriverCall

variable {P : Finset V} {E₀ : Finset E} {t : ℕ} [Nonempty E]

/-- 记录里同一块、轮号增大的森林包含关系。 -/
theorem history_forest_mono (R : DriverCall G P E₀ t) {b i j : Fin t} (hij : i ≤ j) :
    R.history.forest b i ⊆ R.history.forest b j :=
  CallOut.forestUpTo_mono R.roundData (roundIdx_le_of_le hij)

/-- 任何前缀森林都在调用森林 `R.roundData.F` 里。 -/
theorem history_forest_sub_F (R : DriverCall G P E₀ t) (b i : Fin t) :
    R.history.forest b i ⊆ R.roundData.F :=
  forestUpTo_sub R.roundData (b, i)

/-- **「下一轮的森林」**：`e` 的轮次之后若还有一轮，就取那一轮的前缀森林；否则（最后一轮）
取整个调用森林。 -/
noncomputable def nextForest (R : DriverCall G P E₀ t) (e : E) : Finset E :=
  if h : (R.sched e).2.val + 1 < t then
    R.history.forest (R.sched e).1 ⟨(R.sched e).2.val + 1, h⟩
  else R.roundData.F

/-- `nextForest` 在调用森林内（即 `hsub`）。 -/
theorem nextForest_sub (R : DriverCall G P E₀ t) (e : E) :
    nextForest R e ⊆ R.roundData.F := by
  unfold nextForest
  by_cases h : (R.sched e).2.val + 1 < t
  · rw [dite_eq_left h]
    exact R.history_forest_sub_F _ _
  · rw [dite_eq_right h]

/-- `nextForest` 落在 `e` 之后每一轮的森林里（即 `hret`）：下一轮之后单调放大。 -/
theorem hret_nextForest (R : DriverCall G P E₀ t) (e : E) :
    ∀ i, (((R.sched e).2).val + 1 : ℕ) ≤ i.val →
      nextForest R e ⊆ R.history.forest (R.sched e).1 i := by
  intro i hi
  unfold nextForest
  rw [dite_eq_left (lt_of_le_of_lt hi i.isLt)]
  exact R.history_forest_mono (Fin.le_def.mpr hi)

/-- **`hret`／`hsub` 消去后的几何化每边义务。** 孩子森林固定为 `nextForest`；前提只剩
子实例的 `hmsf`／`hlift`（现在是关于 `nextForest` 的陈述）、`S`／`es` 的选择、`B b i ⊆ S`，
以及几何三条。 -/
theorem badFor_of_geomObligations_next (R : DriverCall G P E₀ t)
    (hBfroz : ∀ b i j, R.B b i = R.B b j)
    (hne : ∀ e ∈ E₀,
      portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.src e) ≠
        portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.dst e))
    (hwu : ∀ e ∈ E₀,
      G.weight (R.history.spoke (R.sched e).1 (R.sched e).2 (G.src e)) ≤ G.weight e)
    (hwv : ∀ e ∈ E₀,
      G.weight (R.history.spoke (R.sched e).1 (R.sched e).2 (G.dst e)) ≤ G.weight e)
    (S : E → Finset E)
    (hBS : ∀ e ∈ E₀, R.B (R.sched e).1 (R.sched e).2 ⊆ S e)
    (es : E → List E)
    (hmsf : ∀ e ∈ E₀, IsMSFOf G (S e) (nextForest R e))
    (hlift : ∀ e ∈ E₀, LiftsLe G (R.history.spoke (R.sched e).1 (R.sched e).2) (S e) (G.weight e)
      (portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.src e)) (es e)
      (portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.dst e))) :
    ∀ e ∈ E₀, ¬ supported G R.roundData.F e → R.history.badFor e (R.sched e) :=
  badFor_of_geomObligations R hBfroz (nextForest R) hne hwu hwv
    (fun e _ i hi => R.hret_nextForest e i hi) (fun e _ => R.nextForest_sub e) S hBS es hmsf hlift

/-- **`EvidenceOn`，`hret`／`hsub` 已消去。** -/
noncomputable def evidenceOn_of_geomObligations_next (R : DriverCall G P E₀ t)
    (hBfroz : ∀ b i j, R.B b i = R.B b j)
    (hne : ∀ e ∈ E₀,
      portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.src e) ≠
        portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.dst e))
    (hwu : ∀ e ∈ E₀,
      G.weight (R.history.spoke (R.sched e).1 (R.sched e).2 (G.src e)) ≤ G.weight e)
    (hwv : ∀ e ∈ E₀,
      G.weight (R.history.spoke (R.sched e).1 (R.sched e).2 (G.dst e)) ≤ G.weight e)
    (S : E → Finset E)
    (hBS : ∀ e ∈ E₀, R.B (R.sched e).1 (R.sched e).2 ⊆ S e)
    (es : E → List E)
    (hmsf : ∀ e ∈ E₀, IsMSFOf G (S e) (nextForest R e))
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
    (badFor_of_geomObligations_next R hBfroz hne hwu hwv S hBS es hmsf hlift)

/-- **§3.5 数值界，`hret`／`hsub` 已消去。** -/
theorem card_U_le_number_bound_of_geomObligations_next (R : DriverCall G P E₀ t)
    (hBfroz : ∀ b i j, R.B b i = R.B b j)
    (hne : ∀ e ∈ E₀,
      portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.src e) ≠
        portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.dst e))
    (hwu : ∀ e ∈ E₀,
      G.weight (R.history.spoke (R.sched e).1 (R.sched e).2 (G.src e)) ≤ G.weight e)
    (hwv : ∀ e ∈ E₀,
      G.weight (R.history.spoke (R.sched e).1 (R.sched e).2 (G.dst e)) ≤ G.weight e)
    (S : E → Finset E)
    (hBS : ∀ e ∈ E₀, R.B (R.sched e).1 (R.sched e).2 ⊆ S e)
    (es : E → List E)
    (hmsf : ∀ e ∈ E₀, IsMSFOf G (S e) (nextForest R e))
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
    (badFor_of_geomObligations_next R hBfroz hne hwu hwv S hBS es hmsf hlift)

end DriverCall

end DLMST