import DLMST.ContractStrategy

/-!
# §4 at a self-chosen stopping depth

`Tower.lean` proves the tower under **unbounded** activation: every level, every phase, every
vertex has a leaving edge.  `ContractStrategy.activated_false_of_pos` shows that hypothesis is
inconsistent — the measure forces the bottom level to one vertex, where no phase can run.  The
honest interfaces are the *stopping* ones (`tower_msf_of_stop`), where activation is asked only
strictly above a depth `D` at which the instance has collapsed.

This file makes the depth choice part of the theorem rather than a hypothesis:

* `four_pow_mul_lvlVerts_le_of_lt` — the quartering `4^d · |verts| ≤ |P|` for every `d ≤ D`,
  consuming activation only at the levels below `D` (the induction in
  `four_pow_mul_lvlVerts_le` already only used `hact n` at each step, but its statement quantified
  over all depths);
* `lvlVerts_card_le_one_of_le_pow` — `|P| ≤ 4^D` forces the bottom (`|verts at D| ≤ 1`) from the
  bounded measure, so the stopping hypothesis `hstop` of `mst_main_stop` is *derived*, not assumed;
* `mst_stop_depth` / `mst_stop_depth_card` / `mst_stop_depth_three_fourths` — the §4 answer at
  `D = log₄|P| + 1` is an MSF with at most `|P| - 1` edges, hence `3|F| ≤ 4|P|`;
* `mst_stop_depth_weight` — the level-forest weight telescope at the same depth.

The activation hypothesis below `D` is still a hypothesis (and is genuinely satisfiable only when
the instance collapses at a level boundary — see `TowerUncond.lean`, which removes it entirely and
derives the stopping depth from connectivity alone).  What is unconditional here is the *measure*
at the chosen depth, which is what the paper's §4 display consumes.

Everything is counting: no cost model, no executable program (boundary B2).
-/

open Classical

namespace DLMST

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]

/-! ## The quartering below the stopping depth -/

/-- **The measure at depths below a bound.**  The induction of `four_pow_mul_lvlVerts_le` uses the
activation hypothesis only at the level being quartered, so a bounded activation hypothesis gives
the measure for every depth up to the bound. -/
theorem four_pow_mul_lvlVerts_le_of_lt {G : WGraph V E} {P : Finset V} {E₀ : Finset E} {D : ℕ}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hact : ∀ (d i : ℕ), d < D → i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e) :
    ∀ d, d ≤ D → 4 ^ d * (lvlVerts G P E₀ d).card ≤ P.card := by
  intro d
  induction d with
  | zero =>
      intro _
      simp [lvlVerts, lvlData]
  | succ n ih =>
      intro hd
      have hnD : n < D := Nat.lt_of_succ_le hd
      have h4 : 4 * (lvlVerts G P E₀ (n + 1)).card ≤ (lvlVerts G P E₀ n).card := by
        rw [lvlVerts_succ_chain]
        exact four_mul_repSet_card_le (G := lvlGraph G P E₀ n) (P := lvlVerts G P E₀ n) 2
          (by norm_num) (lvlE G P E₀ n) (phaseChain (lvlGraph G P E₀ n) (lvlE G P E₀ n))
          rfl (fun i => rfl) (lvl_hPE hPE n) (fun i hi => hact n i hnD hi)
      calc 4 ^ (n + 1) * (lvlVerts G P E₀ (n + 1)).card
          = 4 ^ n * (4 * (lvlVerts G P E₀ (n + 1)).card) := by
            rw [pow_succ]; ring
        _ ≤ 4 ^ n * (lvlVerts G P E₀ n).card := Nat.mul_le_mul_left _ h4
        _ ≤ P.card := ih (Nat.le_of_succ_le hd)

/-- **The corner below the bound collapses.**  `4^D · |verts at D| ≤ |P| ≤ 4^D` leaves at most one
vertex, so the stopping condition of `tower_msf_of_stop` is a consequence of the bounded measure. -/
theorem lvlVerts_card_le_one_of_le_pow {G : WGraph V E} {P : Finset V} {E₀ : Finset E} {D : ℕ}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hact : ∀ (d i : ℕ), d < D → i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (hd : P.card ≤ 4 ^ D) : (lvlVerts G P E₀ D).card ≤ 1 := by
  have h4 := four_pow_mul_lvlVerts_le_of_lt hPE hact D le_rfl
  have hpow : 0 < 4 ^ D := Nat.pow_pos (by norm_num)
  have hle : 4 ^ D * (lvlVerts G P E₀ D).card ≤ 4 ^ D * 1 := by
    calc 4 ^ D * (lvlVerts G P E₀ D).card ≤ P.card := h4
      _ ≤ 4 ^ D := hd
      _ = 4 ^ D * 1 := (Nat.mul_one _).symm
  exact Nat.le_of_mul_le_mul_left hle hpow

/-! ## The §4 answer at the self-chosen depth -/

/-- **§4 terminates at `log₄|P| + 1`**, with activation only strictly above that depth and the
stopping condition derived from the bounded measure.  The answer is an MSF with at most `|P| - 1`
edges. -/
theorem mst_stop_depth {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), d < Nat.log 4 P.card + 1 → i < 2 →
      ∀ v ∈ lvlVerts G P E₀ d,
        ∃ e ∈ lvlE G P E₀ d,
          leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e) :
    ∃ F : Finset E, IsMSFOf G E₀ F ∧ F.card ≤ P.card - 1 := by
  have hstop := lvlVerts_card_le_one_of_le_pow (D := Nat.log 4 P.card + 1) hPE hact
    (card_le_pow_log P.card)
  exact ⟨answer G P E₀ (Nat.log 4 P.card + 1) ∅,
    tower_msf_of_stop hPE hP _ hact hstop,
    tower_msf_of_stop_card hPE hP _ hact hstop⟩

/-- **The `4/3` size bound at the self-chosen depth**, from the forest bound `|F| ≤ |P| - 1`. -/
theorem mst_stop_depth_three_fourths {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), d < Nat.log 4 P.card + 1 → i < 2 →
      ∀ v ∈ lvlVerts G P E₀ d,
        ∃ e ∈ lvlE G P E₀ d,
          leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e) :
    ∃ F : Finset E, IsMSFOf G E₀ F ∧ 3 * F.card ≤ 4 * P.card := by
  obtain ⟨F, hF, hcard⟩ := mst_stop_depth hPE hP hact
  exact ⟨F, hF, by omega⟩

/-- **The weight telescope at the self-chosen depth**: the answer weighs exactly the sum of the
level forests, because the bottom call returns the empty forest.  No hypothesis: the telescope is
about the level data alone. -/
theorem mst_stop_depth_weight (G : WGraph V E) (P : Finset V) (E₀ : Finset E) :
    wsum G (answer G P E₀ (Nat.log 4 P.card + 1) ∅) =
      Finset.sum (Finset.range (Nat.log 4 P.card + 1))
        (fun j => wsum G (lvlForest G P E₀ j)) := by
  have h := tower_wsum (G := G) (P := P) (E₀ := E₀) (Nat.log 4 P.card + 1) ∅
    (Finset.empty_subset _)
  simpa [wsum] using h

/-- **The whole §4 account at the self-chosen depth**, in one statement: correctness, the size
bound, and the weight telescope. -/
theorem mst_stop_depth_package {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), d < Nat.log 4 P.card + 1 → i < 2 →
      ∀ v ∈ lvlVerts G P E₀ d,
        ∃ e ∈ lvlE G P E₀ d,
          leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e) :
    IsMSFOf G E₀ (answer G P E₀ (Nat.log 4 P.card + 1) ∅) ∧
      (answer G P E₀ (Nat.log 4 P.card + 1) ∅).card ≤ P.card - 1 ∧
      3 * (answer G P E₀ (Nat.log 4 P.card + 1) ∅).card ≤ 4 * P.card ∧
      4 ^ (Nat.log 4 P.card + 1) * (lvlVerts G P E₀ (Nat.log 4 P.card + 1)).card ≤ P.card ∧
      wsum G (answer G P E₀ (Nat.log 4 P.card + 1) ∅) =
        Finset.sum (Finset.range (Nat.log 4 P.card + 1))
          (fun j => wsum G (lvlForest G P E₀ j)) := by
  have hstop := lvlVerts_card_le_one_of_le_pow (D := Nat.log 4 P.card + 1) hPE hact
    (card_le_pow_log P.card)
  have hmsf := tower_msf_of_stop hPE hP _ hact hstop
  have hcard := tower_msf_of_stop_card hPE hP _ hact hstop
  have hmeasure := four_pow_mul_lvlVerts_le_of_lt hPE hact _ le_rfl
  exact ⟨hmsf, hcard, by omega, hmeasure, mst_stop_depth_weight G P E₀⟩

end DLMST