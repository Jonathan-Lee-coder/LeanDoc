import DLMST.Main
import DLMST.StopWitness

/-!
# The stopping interface at the paper's `4/3`

`mst_main_stop` (the satisfiable stopping form of §4) returns an MSF with `|F| ≤ |P| − 1`.
The paper's display `3|F| ≤ 4|P|` is a consequence, but the entailment had not been written down
(`mst_main_root_conn` states `4/3` directly, `mst_main_stop` only `|P| − 1`).  This file supplies it:

* `answer_three_fourths` — the telescope's own answer `answer G P E₀ D ∅` satisfies `3|F| ≤ 4|P|`;
* `mst_main_stop_three_fourths` — the `∃ F` form, in the same shape as `mst_main_root_conn`;
* `stop_witness_three_fourths` — the concrete four-vertex instance of `StopWitness`, so the `4/3`
  form is non-vacuous at the same witness that discharges `mst_main_stop`.
-/

namespace DLMST

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]

/-- **`4/3` at the telescope's answer**: the stopping interface's `|F| ≤ |P| − 1` implies the
paper's `3|F| ≤ 4|P|` (for `0 < |P|`). -/
theorem answer_three_fourths (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (D : ℕ)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), d < D → i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (hstop : (lvlVerts G P E₀ D).card ≤ 1) :
    3 * (answer G P E₀ D ∅).card ≤ 4 * P.card := by
  have h := tower_msf_of_stop_card (G := G) (P := P) (E₀ := E₀) hPE hP D hact hstop
  omega

/-- **The stopping interface at `4/3`**: same hypotheses as `mst_main_stop`, conclusion
`∃ F, IsMSFOf G E₀ F ∧ 3|F| ≤ 4|P|`. -/
theorem mst_main_stop_three_fourths (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (D : ℕ)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), d < D → i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (hstop : (lvlVerts G P E₀ D).card ≤ 1) :
    ∃ F : Finset E, IsMSFOf G E₀ F ∧ 3 * F.card ≤ 4 * P.card :=
  ⟨answer G P E₀ D ∅, tower_msf_of_stop hPE hP D hact hstop,
    answer_three_fourths G P E₀ D hPE hP hact hstop⟩

/-- **Non-vacuity of the `4/3` form**: the four-vertex witness of `StopWitness`. -/
theorem stop_witness_three_fourths :
    ∃ F : Finset (Fin 3), IsMSFOf G4 (Finset.univ : Finset (Fin 3)) F
      ∧ 3 * F.card ≤ 4 * (Finset.univ : Finset (Fin 4)).card :=
  mst_main_stop_three_fourths G4 (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 3)) 1
    stop_hPE stop_hP stop_hact stop_hstop

end DLMST