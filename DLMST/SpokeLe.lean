import DLMST.ForestMono

/-!
# 第 128 批：辐条不重于 `e` 的选择集来源

投影判据（第 125 批）与几何化义务（第 126、127 批）里还剩一条几何前提：「`e` 两端的辐条
都不重于 `e`」（`hwu`／`hwv`）。本批把它落到**选择集成员条件**上：

* `history_spoke_weight_le_of_mem`：若 `e` 本身在本轮批次的选择集 `selAt` 里（在该端点处），
  则表历史在该端点的辐条不重于 `e`——辐条是 `selAt` 的最小元（`spokeOf_le` + 权序
  `OrderedByWeight`）；
* `badFor_of_selObligations` 及其 `EvidenceOn`／数值界版本：把第 127 批的前提里的 `hwu`／`hwv`
  换成「`e` ∈ `selAt`（在两端）」的成员条件。

**口径记账（选择集是截断的）**：论文里辐条是本轮批次 `B(v)` 里的最轻边，于是「`e` ∈ 本轮批次
⟹ 辐条 ≤ `e`」直接成立；本形式化里辐条是选择集 `selAt`（按「另一端」分组、每组取最轻、再取最轻
的 `quota` 个）的最小元，故需要的成员前提是 `e ∈ selAt` 而非更弱的 `e ∈ B`。这不是论文论证的
缺口——`e ∈ B` 推出辐条 ≤ `e` 需要「选择集包含 `e` 所代表的组」，而在批次按重量扫描的次序里，
`e` 在自己的轮次被扫描时正是该组的最轻代表——但该推理依赖轮内扫描次序，当前驱动模型没有记录
轮内次序，故本批只到「成员条件」为止。
-/

namespace DLMST

open Classical

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

namespace DriverCall

variable {P : Finset V} {E₀ : Finset E} {t : ℕ} [Nonempty E]

/-- **选择集成员 ⟹ 辐条不重于 `e`。** 辐条是 `selAt` 的最小元。 -/
theorem history_spoke_weight_le_of_mem (R : DriverCall G P E₀ t) (hw : OrderedByWeight G)
    {b i : Fin t} {v : V} {e : E}
    (he : e ∈ selAt G (R.B b i) (fun f => f ∉ R.roundData.F) R.quota v) :
    G.weight (R.history.spoke b i v) ≤ G.weight e := by
  change G.weight (spokeTable (G := G) R.B (fun f => f ∉ R.roundData.F) R.quota b i v) ≤
    G.weight e
  exact spokeOf_weight_le (G := G) hw ⟨e, he⟩ he

/-- **辐条不重于 `e`（两端），从选择集成员推出。** 两条成员条件分别是 `e` 在 `src e`、`dst e`
处的选择集里。 -/
theorem badFor_of_selObligations (R : DriverCall G P E₀ t) (hw : OrderedByWeight G)
    (hBfroz : ∀ b i j, R.B b i = R.B b j)
    (S : E → Finset E)
    (hBS : ∀ e ∈ E₀, R.B (R.sched e).1 (R.sched e).2 ⊆ S e)
    (es : E → List E)
    (hselU : ∀ e ∈ E₀,
      e ∈ selAt G (R.B (R.sched e).1 (R.sched e).2) (fun f => f ∉ R.roundData.F) R.quota (G.src e))
    (hselV : ∀ e ∈ E₀,
      e ∈ selAt G (R.B (R.sched e).1 (R.sched e).2) (fun f => f ∉ R.roundData.F) R.quota (G.dst e))
    (hne : ∀ e ∈ E₀,
      portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.src e) ≠
        portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.dst e))
    (hmsf : ∀ e ∈ E₀, IsMSFOf G (S e) (nextForest R e))
    (hlift : ∀ e ∈ E₀, LiftsLe G (R.history.spoke (R.sched e).1 (R.sched e).2) (S e) (G.weight e)
      (portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.src e)) (es e)
      (portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.dst e))) :
    ∀ e ∈ E₀, ¬ supported G R.roundData.F e → R.history.badFor e (R.sched e) :=
  badFor_of_geomObligations_next R hBfroz hne
    (fun e he => R.history_spoke_weight_le_of_mem hw (hselU e he))
    (fun e he => R.history_spoke_weight_le_of_mem hw (hselV e he))
    S hBS es hmsf hlift

/-- **`EvidenceOn`，辐条权重条件改为选择集成员条件。** -/
noncomputable def evidenceOn_of_selObligations (R : DriverCall G P E₀ t) (hw : OrderedByWeight G)
    (hBfroz : ∀ b i j, R.B b i = R.B b j)
    (S : E → Finset E)
    (hBS : ∀ e ∈ E₀, R.B (R.sched e).1 (R.sched e).2 ⊆ S e)
    (es : E → List E)
    (hselU : ∀ e ∈ E₀,
      e ∈ selAt G (R.B (R.sched e).1 (R.sched e).2) (fun f => f ∉ R.roundData.F) R.quota (G.src e))
    (hselV : ∀ e ∈ E₀,
      e ∈ selAt G (R.B (R.sched e).1 (R.sched e).2) (fun f => f ∉ R.roundData.F) R.quota (G.dst e))
    (hne : ∀ e ∈ E₀,
      portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.src e) ≠
        portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.dst e))
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
    (badFor_of_selObligations R hw hBfroz S hBS es hselU hselV hne hmsf hlift)

/-- **§3.5 数值界，辐条权重条件改为选择集成员条件。** -/
theorem card_U_le_number_bound_of_selObligations (R : DriverCall G P E₀ t)
    (hw : OrderedByWeight G)
    (hBfroz : ∀ b i j, R.B b i = R.B b j)
    (S : E → Finset E)
    (hBS : ∀ e ∈ E₀, R.B (R.sched e).1 (R.sched e).2 ⊆ S e)
    (es : E → List E)
    (hselU : ∀ e ∈ E₀,
      e ∈ selAt G (R.B (R.sched e).1 (R.sched e).2) (fun f => f ∉ R.roundData.F) R.quota (G.src e))
    (hselV : ∀ e ∈ E₀,
      e ∈ selAt G (R.B (R.sched e).1 (R.sched e).2) (fun f => f ∉ R.roundData.F) R.quota (G.dst e))
    (hne : ∀ e ∈ E₀,
      portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.src e) ≠
        portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.dst e))
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
    (badFor_of_selObligations R hw hBfroz S hBS es hselU hselV hne hmsf hlift)

end DriverCall

end DLMST