/-
# The §4 tower as a §3.6 level chain: the display applied to §4 data

§3.6's display analysis (`hrest_of_levels_rest`, `lemma12_bound_gen`) consumes only a **counting**
chain: a sequence of `Level`s whose vertex totals shrink by `4` and whose instances nest.  It never
looks at how the levels were produced.  This file feeds it the §4 tower.

* `towerLevel` — level `d` as the single instance `(V_d, E_d)`.
* `towerLevel_step` — nesting (`lvlE_succ_subset`, `repSet_subset`) and the `1/4` vertex shrink
  (`four_mul_lvlVerts_succ_le`), from the level activation alone.
* `towerU` — the node's retained set `U(F) = unsupp G F ∩ E₀` at `F = phaseChain G E₀ 2`.
* `tower_display_rest` — **§3.6's display at the §4 node**: given the per-level numeric counts
  (`errL`, `inL`), `|F| + |U| + Σ|kidE| ≤ ε|E₀| + C_ε·√(|E₀|·|P|)` with `C_ε = √2 +
  γ²·40000·(2 + √2·C)`.

The dictionary between the two interfaces is also recorded: §4's child edge set is the *cross*
set, contained in `U` (`towerKidE_subset_unsupp`), whereas §3.6's `CallOut` requires the opposite
(`CallOut.hUkid`, boundary B1).  That is why the display is proved here from counts rather than by
producing a `CallOut`.
-/
import DLMST.ContractStrategy
import DLMST.LinearTime

open Classical

namespace DLMST

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]

/-! ## The level chain -/

/-- The tower's level `d` as a counting level: its one instance is the level's own `(V_d, E_d)`. -/
noncomputable def towerLevel (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (d : ℕ) :
    Level V E where
  insts := {(lvlVerts G P E₀ d, lvlE G P E₀ d)}
  edisj := by
    intro a ha b hb hab
    rw [Finset.mem_singleton] at ha hb
    subst ha
    subst hb
    exact absurd rfl hab

theorem towerLevel_verts (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (d : ℕ) :
    (towerLevel G P E₀ d).verts = (lvlVerts G P E₀ d).card := by
  simp [towerLevel, Level.verts]

theorem towerLevel_edges (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (d : ℕ) :
    (towerLevel G P E₀ d).edges = (lvlE G P E₀ d).card := by
  simp [towerLevel, Level.edges]

theorem towerLevel_verts_zero (G : WGraph V E) (P : Finset V) (E₀ : Finset E) :
    (towerLevel G P E₀ 0).verts = P.card := by
  simp [towerLevel, Level.verts, lvlVerts, lvlData]

theorem towerLevel_edges_zero (G : WGraph V E) (P : Finset V) (E₀ : Finset E) :
    (towerLevel G P E₀ 0).edges = E₀.card := by
  simp [towerLevel, Level.edges, lvlE, lvlData]

/-- **One tower level is one recursion step**: the child instance `(V_{d+1}, E_{d+1})` is contained
in the parent and the vertex totals shrink by `4`.  The shrink is the level activation, via
`four_mul_lvlVerts_succ_le`. -/
theorem towerLevel_step {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) : Step (towerLevel G P E₀ d) (towerLevel G P E₀ (d + 1)) where
  sub := by
    intro b hb
    have hb' : b = (lvlVerts G P E₀ (d + 1), lvlE G P E₀ (d + 1)) := by
      simpa [towerLevel] using hb
    subst hb'
    refine ⟨(lvlVerts G P E₀ d, lvlE G P E₀ d), ?_, ?_, ?_⟩
    · simp [towerLevel]
    · rw [lvlVerts_succ G P E₀ d]
      exact repSet_subset (G := lvlGraph G P E₀ d) (P := lvlVerts G P E₀ d)
        (F := lvlForest G P E₀ d)
    · exact lvlE_succ_subset G P E₀ d
  shrink := by
    rw [towerLevel_verts, towerLevel_verts]
    exact four_mul_lvlVerts_succ_le hPE hact d

/-- **One tower level is one recursion step, with activation only at that level** — the bounded
form used by the stopping chain. -/
theorem towerLevel_step_bd {G : WGraph V E} {P : Finset V} {E₀ : Finset E} {D : ℕ}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hact : ∀ (d i : ℕ), d < D → i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (hd : d < D) : Step (towerLevel G P E₀ d) (towerLevel G P E₀ (d + 1)) where
  sub := by
    intro b hb
    have hb' : b = (lvlVerts G P E₀ (d + 1), lvlE G P E₀ (d + 1)) := by
      simpa [towerLevel] using hb
    subst hb'
    refine ⟨(lvlVerts G P E₀ d, lvlE G P E₀ d), ?_, ?_, ?_⟩
    · simp [towerLevel]
    · rw [lvlVerts_succ G P E₀ d]
      exact repSet_subset (G := lvlGraph G P E₀ d) (P := lvlVerts G P E₀ d)
        (F := lvlForest G P E₀ d)
    · exact lvlE_succ_subset G P E₀ d
  shrink := by
    rw [towerLevel_verts, towerLevel_verts]
    rw [lvlVerts_succ_chain]
    exact four_mul_repSet_card_le (G := lvlGraph G P E₀ d) (P := lvlVerts G P E₀ d) 2
      (by norm_num) (lvlE G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d))
      rfl (fun i => rfl) (lvl_hPE hPE d) (fun i hi => hact d i hd hi)

/-- The empty tail level: one empty instance.  It makes the chain constant past the stopping
depth, where activation is unavailable. -/
noncomputable def emptyLevel (V E : Type*) [DecidableEq V] [DecidableEq E] : Level V E where
  insts := {((∅ : Finset V), (∅ : Finset E))}
  edisj := by
    intro a ha b hb hab
    rw [Finset.mem_singleton] at ha hb
    subst ha
    subst hb
    exact absurd rfl hab

/-- **The tower's level chain up to stopping depth `D`**: real tower levels above `D`, the empty
level from `D` on.  Activation is needed only above `D`, exactly as in `mst_main_stop`. -/
noncomputable def towerLevelChain (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (D : ℕ) :
    ℕ → Level V E :=
  fun d => if d ≤ D then towerLevel G P E₀ d else emptyLevel V E

theorem towerLevelChain_of_le {G : WGraph V E} {P : Finset V} {E₀ : Finset E} {D d : ℕ}
    (hd : d ≤ D) : towerLevelChain G P E₀ D d = towerLevel G P E₀ d := by
  simp [towerLevelChain, hd]

theorem towerLevelChain_of_lt {G : WGraph V E} {P : Finset V} {E₀ : Finset E} {D d : ℕ}
    (hd : D < d) : towerLevelChain G P E₀ D d = emptyLevel V E := by
  simp [towerLevelChain, Nat.not_le.mpr hd]

/-- **The chain is a `Step` chain**, with activation only above the stopping depth. -/
theorem towerLevelChain_step {G : WGraph V E} {P : Finset V} {E₀ : Finset E} {D : ℕ}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hact : ∀ (d i : ℕ), d < D → i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) : Step (towerLevelChain G P E₀ D d) (towerLevelChain G P E₀ D (d + 1)) := by
  by_cases hd : d < D
  · rw [towerLevelChain_of_le (Nat.le_of_lt hd), towerLevelChain_of_le (Nat.succ_le_of_lt hd)]
    exact towerLevel_step_bd hPE hact d hd
  · by_cases hD : d = D
    · rw [hD]
      rw [towerLevelChain_of_le (Nat.le_refl D), towerLevelChain_of_lt (Nat.lt_succ_self D)]
      refine ⟨?_, ?_⟩
      · intro b hb
        have hb' : b = ((∅ : Finset V), (∅ : Finset E)) := by
          simpa [emptyLevel] using hb
        subst hb'
        exact ⟨(lvlVerts G P E₀ D, lvlE G P E₀ D), by simp [towerLevel],
          Finset.empty_subset _, Finset.empty_subset _⟩
      · simp [emptyLevel, Level.verts]
    · have hgt : D < d := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hd) (Ne.symm hD)
      rw [towerLevelChain_of_lt hgt, towerLevelChain_of_lt (Nat.lt_succ_of_lt hgt)]
      refine ⟨?_, ?_⟩
      · intro b hb
        have hb' : b = ((∅ : Finset V), (∅ : Finset E)) := by
          simpa [emptyLevel] using hb
        subst hb'
        exact ⟨((∅ : Finset V), (∅ : Finset E)), by simp [emptyLevel],
          Finset.Subset.refl _, Finset.Subset.refl _⟩
      · simp [emptyLevel, Level.verts]

/-! ## The retained set at the §4 node -/

/-- The node's retained set: the edges of `E₀` unsupported by the two-phase forest.  This is §3.6's
`U(F)`, and §4's recursion hands the child only the *cross* part of it. -/
noncomputable def towerU (G : WGraph V E) (E₀ : Finset E) : Finset E :=
  unsupp G (phaseChain G E₀ 2) ∩ E₀

/-- **The child's input is inside the retained set** — the §4 side of boundary B1: a cross edge is
not connected by the forest, hence not supported, hence `U`. -/
theorem towerKidE_subset_unsupp (G : WGraph V E) (P : Finset V) (E₀ : Finset E) :
    lvlE G P E₀ 1 ⊆ towerU G E₀ := by
  intro e he
  rw [lvlE_one] at he
  exact Finset.mem_inter.mpr
    ⟨crossE_subset_unsupp (G := G) (F := phaseChain G E₀ 2) (E₀ := E₀) he,
      crossE_subset (G := G) (F := phaseChain G E₀ 2) (E₀ := E₀) he⟩

/-- The retained set sits inside the instance. -/
theorem towerU_subset (G : WGraph V E) (E₀ : Finset E) : towerU G E₀ ⊆ E₀ :=
  Finset.inter_subset_right

/-- The forest and the retained set are disjoint (an `F` edge supports itself). -/
theorem disjoint_towerForest_towerU (G : WGraph V E) (E₀ : Finset E) :
    Disjoint (phaseChain G E₀ 2) (towerU G E₀) :=
  (disjoint_unsupp (G := G) (F := phaseChain G E₀ 2)).mono_right Finset.inter_subset_left

/-- **The node's three-bucket count identity**: `E₀` splits into the forest, the retained set, and
the discarded supported edges.  This is the §4 counterpart of `CallOut.partition_eq`; here the
retained set is not a fourth bucket but the one the recursion descends into. -/
theorem tower_partition (G : WGraph V E) (P : Finset V) (E₀ : Finset E) :
    (phaseChain G E₀ 2).card + (towerU G E₀).card +
        (E₀ \ (phaseChain G E₀ 2 ∪ towerU G E₀)).card = E₀.card := by
  have hFsub : phaseChain G E₀ 2 ⊆ E₀ := by
    rw [← lvlForest_zero G P E₀]
    exact lvlForest_subset_lvlE G P E₀ 0
  have hun : phaseChain G E₀ 2 ∪ towerU G E₀ ⊆ E₀ :=
    Finset.union_subset hFsub (towerU_subset G E₀)
  calc (phaseChain G E₀ 2).card + (towerU G E₀).card +
          (E₀ \ (phaseChain G E₀ 2 ∪ towerU G E₀)).card
      = (phaseChain G E₀ 2 ∪ towerU G E₀).card +
          (E₀ \ (phaseChain G E₀ 2 ∪ towerU G E₀)).card := by
        rw [Finset.card_union_of_disjoint (disjoint_towerForest_towerU G E₀)]
    _ = ((phaseChain G E₀ 2 ∪ towerU G E₀) ∪
          (E₀ \ (phaseChain G E₀ 2 ∪ towerU G E₀))).card :=
        (Finset.card_union_of_disjoint Finset.disjoint_sdiff).symm
    _ = E₀.card := by rw [Finset.union_sdiff_of_subset hun]

/-- The forest plus the child's input fits in the instance — the display's left-hand side is at
most `|E₀| + |U|` (the retained set is counted separately by the display). -/
theorem tower_forest_add_kid_le (G : WGraph V E) (P : Finset V) (E₀ : Finset E) :
    (phaseChain G E₀ 2).card + (lvlE G P E₀ 1).card ≤ E₀.card := by
  have hsub : phaseChain G E₀ 2 ∪ lvlE G P E₀ 1 ⊆ E₀ := by
    rw [lvlE_one]
    exact Finset.union_subset
      (by rw [← lvlForest_zero G P E₀]; exact lvlForest_subset_lvlE G P E₀ 0)
      (crossE_subset (G := G) (F := phaseChain G E₀ 2) (E₀ := E₀))
  have hdisj : Disjoint (phaseChain G E₀ 2) (crossE G (phaseChain G E₀ 2) E₀) :=
    disjoint_crossE_F (G := G) (F := phaseChain G E₀ 2) (E₀ := E₀)
  calc (phaseChain G E₀ 2).card + (lvlE G P E₀ 1).card
      = (phaseChain G E₀ 2 ∪ lvlE G P E₀ 1).card := by
        rw [lvlE_one, Finset.card_union_of_disjoint hdisj]
    _ ≤ E₀.card := Finset.card_le_card hsub

/-! ## §3.6's display at the §4 node -/

/-- **The §3.6 display with §4 data.**  With the per-level numeric counts `errL`/`inL` bounded at
`t_d = γ(d+1)³` (the paper's §3.1–§3.5 content, `C` open) and the two totals booked
(`|U| ≤ Σ errL`, `|kidE| ≤ Σ inL`), the §4 node satisfies

`|F| + |U| + |kidE| ≤ ε|E₀| + (√2 + γ²·40000·(2 + √2·C))·√(|E₀|·|P|)`.

The proof is `hrest_of_levels_rest` on the tower's own levels plus `lemma12_bound_gen`; no
`CallOut` is constructed, so boundary B1 does not block it. -/
theorem tower_display_rest {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    {D : ℕ}
    (hact : ∀ (d i : ℕ), d < D → i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    {γ ε C : ℝ} (hγ : 0 < γ) (hε : 0 < ε) (hγε : 16 ≤ ε * γ) (hC : 0 ≤ C)
    (hnm : (P.card : ℝ) ≤ 2 * (E₀.card : ℝ))
    {errL inL : ℕ → ℕ}
    (herr : ∀ d ∈ Finset.range D, (errL d : ℝ) ≤
      (γ * ((d : ℝ) + 1) ^ 3) ^ 2 *
          Real.sqrt (((lvlE G P E₀ d).card : ℝ) * ((lvlVerts G P E₀ d).card : ℝ)) +
        4 * ((lvlE G P E₀ d).card : ℝ) / (γ * ((d : ℝ) + 1) ^ 3))
    (hin : ∀ d ∈ Finset.range D, (inL d : ℝ) ≤ (errL d : ℝ) +
      C * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 * ((lvlVerts G P E₀ d).card : ℝ)))
    (hU : (towerU G E₀).card ≤ ∑ d ∈ Finset.range D, errL d)
    (hSE : (lvlE G P E₀ 1).card ≤ ∑ d ∈ Finset.range D, inL d) :
    ((phaseChain G E₀ 2).card : ℝ) + ((towerU G E₀).card : ℝ) +
        ((lvlE G P E₀ 1).card : ℝ) ≤
      ε * (E₀.card : ℝ) +
        (Real.sqrt 2 + γ ^ 2 * (40000 * (2 + Real.sqrt 2 * C))) *
          Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) := by
  have hstep : ∀ d, Step (towerLevelChain G P E₀ D d) (towerLevelChain G P E₀ D (d + 1)) :=
    fun d => towerLevelChain_step hPE hact d
  have herr' : ∀ d ∈ Finset.range D, (errL d : ℝ) ≤
      (γ * ((d : ℝ) + 1) ^ 3) ^ 2 *
          Real.sqrt (((towerLevelChain G P E₀ D d).edges : ℝ) *
            ((towerLevelChain G P E₀ D d).verts : ℝ)) +
        4 * ((towerLevelChain G P E₀ D d).edges : ℝ) / (γ * ((d : ℝ) + 1) ^ 3) := by
    intro d hd
    rw [towerLevelChain_of_le (Nat.le_of_lt (Finset.mem_range.mp hd)),
      towerLevel_edges, towerLevel_verts]
    exact herr d hd
  have hin' : ∀ d ∈ Finset.range D, (inL d : ℝ) ≤ (errL d : ℝ) +
      C * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 * ((towerLevelChain G P E₀ D d).verts : ℝ)) := by
    intro d hd
    rw [towerLevelChain_of_le (Nat.le_of_lt (Finset.mem_range.mp hd)), towerLevel_verts]
    exact hin d hd
  have hn0 : (towerLevelChain G P E₀ D 0).verts = P.card := by
    rw [towerLevelChain_of_le (Nat.zero_le D)]
    exact towerLevel_verts_zero G P E₀
  have hm0 : (towerLevelChain G P E₀ D 0).edges = E₀.card := by
    rw [towerLevelChain_of_le (Nat.zero_le D)]
    exact towerLevel_edges_zero G P E₀
  have hF : ((phaseChain G E₀ 2).card : ℝ) ≤ (P.card : ℝ) := by
    have h := lvlForest_card_le_lvlVerts (G := G) (P := P) (E₀ := E₀) hPE 0
    rw [lvlForest_zero] at h
    have h0 : (lvlVerts G P E₀ 0).card = P.card := by simp [lvlVerts, lvlData]
    rw [h0] at h
    exact_mod_cast h
  exact lemma12_bound_gen (n := P.card) (m := E₀.card) (Fc := (phaseChain G E₀ 2).card)
    (U := (towerU G E₀).card) (SE := (lvlE G P E₀ 1).card)
    (K := 40000 * (2 + Real.sqrt 2 * C))
    hγ hε hγε (by positivity) hnm hF
    (hrest_of_levels_rest (n := P.card) (m := E₀.card) hγ hC hstep hn0 hm0
      herr' hin' hnm hU hSE)

/-- **The §3.6 display in the paper's degree-`21` form at the §4 node.**  With the per-level input
count `A(d+1)²¹·n_d` (the p. 24 count `2t²(n−1) + t(n−1+r²n)` at `t = γ(d+1)³`, `r = 8t³`), the
node satisfies

`|F| + |U| + |kidE| ≤ ε|E₀| + (√2 + γ²·80000 + √2·A·202²¹·2)·√(|E₀|·|P|)`,

the same constant as `display_of_strategy_of_calls_poly_coef`. -/
theorem tower_display_poly {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    {D : ℕ}
    (hact : ∀ (d i : ℕ), d < D → i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    {γ ε A : ℝ} (hγ : 0 < γ) (hε : 0 < ε) (hγε : 16 ≤ ε * γ) (hA : 0 ≤ A)
    (hnm : (P.card : ℝ) ≤ 2 * (E₀.card : ℝ))
    {errL inL : ℕ → ℕ}
    (herr : ∀ d ∈ Finset.range D, (errL d : ℝ) ≤
      (γ * ((d : ℝ) + 1) ^ 3) ^ 2 *
          Real.sqrt (((lvlE G P E₀ d).card : ℝ) * ((lvlVerts G P E₀ d).card : ℝ)) +
        4 * ((lvlE G P E₀ d).card : ℝ) / (γ * ((d : ℝ) + 1) ^ 3))
    (hin : ∀ d ∈ Finset.range D, (inL d : ℝ) ≤ (errL d : ℝ) +
      A * ((d : ℝ) + 1) ^ 21 * ((lvlVerts G P E₀ d).card : ℝ))
    (hU : (towerU G E₀).card ≤ ∑ d ∈ Finset.range D, errL d)
    (hSE : (lvlE G P E₀ 1).card ≤ ∑ d ∈ Finset.range D, inL d) :
    ((phaseChain G E₀ 2).card : ℝ) + ((towerU G E₀).card : ℝ) +
        ((lvlE G P E₀ 1).card : ℝ) ≤
      ε * (E₀.card : ℝ) +
        (Real.sqrt 2 + γ ^ 2 * 80000 +
            Real.sqrt 2 * (A * ((202 : ℝ) ^ 21 * 2))) *
          Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) := by
  have hstep : ∀ d, Step (towerLevelChain G P E₀ D d) (towerLevelChain G P E₀ D (d + 1)) :=
    fun d => towerLevelChain_step hPE hact d
  have herr' : ∀ d ∈ Finset.range D, (errL d : ℝ) ≤
      (γ * ((d : ℝ) + 1) ^ 3) ^ 2 *
          Real.sqrt (((towerLevelChain G P E₀ D d).edges : ℝ) *
            ((towerLevelChain G P E₀ D d).verts : ℝ)) +
        4 * ((towerLevelChain G P E₀ D d).edges : ℝ) / (γ * ((d : ℝ) + 1) ^ 3) := by
    intro d hd
    rw [towerLevelChain_of_le (Nat.le_of_lt (Finset.mem_range.mp hd)),
      towerLevel_edges, towerLevel_verts]
    exact herr d hd
  have hin' : ∀ d ∈ Finset.range D, (inL d : ℝ) ≤ (errL d : ℝ) +
      A * ((d : ℝ) + 1) ^ 21 * ((towerLevelChain G P E₀ D d).verts : ℝ) := by
    intro d hd
    rw [towerLevelChain_of_le (Nat.le_of_lt (Finset.mem_range.mp hd)), towerLevel_verts]
    exact hin d hd
  have hn0 : (towerLevelChain G P E₀ D 0).verts = P.card := by
    rw [towerLevelChain_of_le (Nat.zero_le D)]
    exact towerLevel_verts_zero G P E₀
  have hm0 : (towerLevelChain G P E₀ D 0).edges = E₀.card := by
    rw [towerLevelChain_of_le (Nat.zero_le D)]
    exact towerLevel_edges_zero G P E₀
  have hF : ((phaseChain G E₀ 2).card : ℝ) ≤ (P.card : ℝ) := by
    have h := lvlForest_card_le_lvlVerts (G := G) (P := P) (E₀ := E₀) hPE 0
    rw [lvlForest_zero G P E₀] at h
    have h0 : (lvlVerts G P E₀ 0).card = P.card := by simp [lvlVerts, lvlData]
    rw [h0] at h
    exact_mod_cast h
  exact lemma12_bound_extra (n := P.card) (m := E₀.card) (Fc := (phaseChain G E₀ 2).card)
    (U := (towerU G E₀).card) (SE := (lvlE G P E₀ 1).card)
    (K := 80000) (E := A * ((202 : ℝ) ^ 21 * 2))
    hγ hε hγε (by norm_num) (by positivity) hnm hF
    (hrest_of_levels_poly (n := P.card) (m := E₀.card) hγ hA hstep hn0 hm0
      herr' hin' hU hSE)

/-! ## The assembled theorem -/

/-- **§4 and §3.6 at the same node.**  One theorem, one instance, both analyses:

* §4: the depth-`D` tower's answer is the instance's MSF, its weight telescopes over the levels,
  it is a forest (`|answer| ≤ |P| − 1`), the vertex levels shrink by `4` above `D`, and the
  counting work is `3·totalWork ≤ 4|P| + 3D|E₀|` (`tower_stop_display`);
* §3.6: the node's display `|F| + |U| + |kidE| ≤ ε|E₀| + C_ε·√(|E₀|·|P|)` in the paper's
  degree-`21` form (`tower_display_poly`).

Activation is bounded above `D` throughout, so neither half is vacuous. -/
theorem tower_e2e {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card) {D : ℕ}
    (hact : ∀ (d i : ℕ), d < D → i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (hstop : (lvlVerts G P E₀ D).card ≤ 1)
    {γ ε A : ℝ} (hγ : 0 < γ) (hε : 0 < ε) (hγε : 16 ≤ ε * γ) (hA : 0 ≤ A)
    (hnm : (P.card : ℝ) ≤ 2 * (E₀.card : ℝ))
    {errL inL : ℕ → ℕ}
    (herr : ∀ d ∈ Finset.range D, (errL d : ℝ) ≤
      (γ * ((d : ℝ) + 1) ^ 3) ^ 2 *
          Real.sqrt (((lvlE G P E₀ d).card : ℝ) * ((lvlVerts G P E₀ d).card : ℝ)) +
        4 * ((lvlE G P E₀ d).card : ℝ) / (γ * ((d : ℝ) + 1) ^ 3))
    (hin : ∀ d ∈ Finset.range D, (inL d : ℝ) ≤ (errL d : ℝ) +
      A * ((d : ℝ) + 1) ^ 21 * ((lvlVerts G P E₀ d).card : ℝ))
    (hU : (towerU G E₀).card ≤ ∑ d ∈ Finset.range D, errL d)
    (hSE : (lvlE G P E₀ 1).card ≤ ∑ d ∈ Finset.range D, inL d) :
    IsMSFOf G E₀ (answer G P E₀ D ∅) ∧
      wsum G (answer G P E₀ D ∅) =
        Finset.sum (Finset.range D) (fun j => wsum G (lvlForest G P E₀ j)) ∧
      (answer G P E₀ D ∅).card ≤ P.card - 1 ∧
      (∀ j, j < D → 4 * (lvlVerts G P E₀ (j + 1)).card ≤ (lvlVerts G P E₀ j).card) ∧
      3 * totalWork (G := G) P E₀ D ≤ 4 * P.card + 3 * (D * E₀.card) ∧
      ((phaseChain G E₀ 2).card : ℝ) + ((towerU G E₀).card : ℝ) +
          ((lvlE G P E₀ 1).card : ℝ) ≤
        ε * (E₀.card : ℝ) +
          (Real.sqrt 2 + γ ^ 2 * 80000 +
              Real.sqrt 2 * (A * ((202 : ℝ) ^ 21 * 2))) *
            Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := tower_stop_display (G := G) (P := P) (E₀ := E₀) hPE hP D hact hstop
  exact ⟨h1, h2, h3, h4, h5,
    tower_display_poly (G := G) (P := P) (E₀ := E₀) hPE hact hγ hε hγε hA hnm
      herr hin hU hSE⟩

/-- **The assembled theorem is not vacuous**: on the four-vertex witness (`D = 1`, `γ = ε = 4`,
`A = 0`, constant level counts `4`) all hypotheses hold, and the conclusion's MSF, counting-work and
display conjuncts come out. -/
theorem tower_e2e_witness :
    IsMSFOf G4 (Finset.univ : Finset (Fin 3))
        (answer G4 (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 3)) 1 ∅) ∧
      3 * totalWork (G := G4) (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 3)) 1 ≤
        4 * (Finset.univ : Finset (Fin 4)).card +
          3 * (1 * (Finset.univ : Finset (Fin 3)).card) ∧
      ((phaseChain G4 (Finset.univ : Finset (Fin 3)) 2).card : ℝ) +
          ((towerU G4 (Finset.univ : Finset (Fin 3))).card : ℝ) +
          ((lvlE G4 (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 3)) 1).card : ℝ) ≤
        4 * ((Finset.univ : Finset (Fin 3)).card : ℝ) +
          (Real.sqrt 2 + 4 ^ 2 * 80000 +
              Real.sqrt 2 * (0 * ((202 : ℝ) ^ 21 * 2))) *
            Real.sqrt (((Finset.univ : Finset (Fin 3)).card : ℝ) *
              ((Finset.univ : Finset (Fin 4)).card : ℝ)) := by
  have hcardE : (Finset.univ : Finset (Fin 3)).card = 3 := by decide
  have hcardV : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
  have hE0 : (lvlE G4 (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 3)) 0)
      = Finset.univ := rfl
  have hV0 : (lvlVerts G4 (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 3)) 0)
      = Finset.univ := rfl
  have h3 : (3 : ℝ) ≤ Real.sqrt 12 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hroot := tower_e2e (G := G4) (P := Finset.univ) (E₀ := Finset.univ)
    stop_hPE stop_hP (D := 1) stop_hact stop_hstop
    (γ := 4) (ε := 4) (A := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [hcardE, hcardV]; norm_num)
    (errL := fun _ => 4) (inL := fun _ => 4)
    (fun d hd => by
      have hd0 : d = 0 := by simpa using hd
      subst hd0
      rw [hE0, hV0]
      simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat]
      nlinarith [Real.sqrt_nonneg 12])
    (fun d hd => by
      have hd0 : d = 0 := by simpa using hd
      subst hd0
      rw [hV0]
      simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat]
      nlinarith)
    (by
      show (towerU G4 (Finset.univ : Finset (Fin 3))).card ≤ ∑ d ∈ Finset.range 1, 4
      rw [Finset.sum_range_one]
      calc (towerU G4 (Finset.univ : Finset (Fin 3))).card ≤ 3 := by
            have h := Finset.card_le_card (towerU_subset G4 Finset.univ)
            simpa [hcardE] using h
        _ ≤ 4 := by norm_num)
    (by
      show (lvlE G4 (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 3)) 1).card ≤
        ∑ d ∈ Finset.range 1, 4
      rw [Finset.sum_range_one]
      calc (lvlE G4 (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 3)) 1).card ≤ 3 := by
            have h := Finset.card_le_card (towerKidE_subset_unsupp G4 Finset.univ Finset.univ)
            have h2 := Finset.card_le_card (towerU_subset G4 (Finset.univ : Finset (Fin 3)))
            omega
        _ ≤ 4 := by norm_num)
  obtain ⟨h1, -, -, -, h5, h6⟩ := hroot
  exact ⟨h1, h5, h6⟩

end DLMST
