/-
The §4 result as one theorem: a structure collecting every input the contraction recursion needs,
and a statement producing an MSF of the instance with the `4/3` size bound and the level-forest
weight identity.  The assumptions are data — nothing is hidden in the statement.

**Boundary.**  The unbounded activation field is inconsistent (see `towerInputs_false`): the
measure forces the bottom level to one vertex, where no phase can be active.  The theorems above
are therefore vacuously true.  `mst_main_stop` is the satisfiable interface: activation is only
required above a stopping depth `D` where the instance has collapsed, and the size bound is the
forest bound `|P| - 1`.
-/
import DLMST.ContractStrategy

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]

namespace DLMST

open Classical

/-- Everything the §4 recursion needs from an instance, in one record: endpoints inside `P`, `P`
nonempty, every component of every level has an outgoing edge, and the depth is large enough for the
instance to terminate. -/
structure TowerInputs (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (d : ℕ) : Prop where
  hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P
  hP : 0 < P.card
  hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
    ∃ e ∈ lvlE G P E₀ d,
      leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e
  hd : P.card ≤ 4 ^ d

/-- **The main theorem, packaged**: under `TowerInputs` the instance has an MSF of at most `4/3` its
vertex count. -/
theorem mst_main (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (d : ℕ)
    (h : TowerInputs G P E₀ d) :
    ∃ F : Finset E, IsMSFOf G E₀ F ∧ 3 * F.card ≤ 4 * P.card :=
  ⟨answer G P E₀ d ∅, (contractDisplay h.hPE h.hP h.hact d h.hd).1,
    (contractDisplay h.hPE h.hP h.hact d h.hd).2.2.1⟩

/-- The weight of the produced MSF is exactly the sum of the level forests. -/
theorem mst_main_weight (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (d : ℕ)
    (h : TowerInputs G P E₀ d) :
    wsum G (answer G P E₀ d ∅)
      = Finset.sum (Finset.range d) (fun j => wsum G (lvlForest G P E₀ j)) :=
  (contractDisplay h.hPE h.hP h.hact d h.hd).2.1

/-- **The main theorem with no depth parameter**: the recursion runs to depth `log₄|P| + 1`, and its
answer is an MSF of at most `4/3` the vertex count. -/
theorem mst_main_log (G : WGraph V E) (P : Finset V) (E₀ : Finset E)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e) :
    ∃ F : Finset E, IsMSFOf G E₀ F ∧ 3 * F.card ≤ 4 * P.card :=
  ⟨answer G P E₀ (Nat.log 4 P.card + 1) ∅,
    (contractDisplay_log hPE hP hact).1, (contractDisplay_log hPE hP hact).2.2.1⟩

/-- **The main theorem from root connectivity**: no depth, no per-level connectivity, no activation —
connectivity of `E₀` on `P` plus per-phase component counts. -/
theorem mst_main_root_conn (G : WGraph V E) (P : Finset V) (E₀ : Finset E)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hconn : ∀ u ∈ P, ∀ w ∈ P, Conn G E₀ u w)
    (hc : ∀ (d i : ℕ), i < 2 →
      2 ≤ compCountOn (lvlGraph G P E₀ d) (lvlVerts G P E₀ d)
        (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i)) :
    ∃ F : Finset E, IsMSFOf G E₀ F ∧ 3 * F.card ≤ 4 * P.card :=
  ⟨answer G P E₀ (Nat.log 4 P.card + 1) ∅,
    tower_terminates_log_root_conn hPE hP hconn hc,
    (contractDisplay_log hPE hP (tower_hact_of_root_conn hPE hconn hc)).2.2.1⟩

/-- **`TowerInputs` is inconsistent.**  Unbounded activation contradicts the measure, so every
theorem conditioned on it is vacuously true.  The content lives in `tower_sound` /
`mst_main_stop`, whose assumptions are satisfiable. -/
theorem towerInputs_false (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (d : ℕ)
    (h : TowerInputs G P E₀ d) : False :=
  activated_false_of_pos h.hPE h.hP h.hact

/-- The hypotheses of `mst_main_log` are inconsistent as well (they include unbounded activation). -/
theorem mst_main_log_hypotheses_false (G : WGraph V E) (P : Finset V) (E₀ : Finset E)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e) :
    False :=
  activated_false_of_pos hPE hP hact

/-- The hypotheses of `mst_main_root_conn` are inconsistent as well: they derive activation. -/
theorem mst_main_root_conn_hypotheses_false (G : WGraph V E) (P : Finset V) (E₀ : Finset E)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hconn : ∀ u ∈ P, ∀ w ∈ P, Conn G E₀ u w)
    (hc : ∀ (d i : ℕ), i < 2 →
      2 ≤ compCountOn (lvlGraph G P E₀ d) (lvlVerts G P E₀ d)
        (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i)) :
    False :=
  root_conn_false_of_pos hPE hP hconn hc

/-- **The satisfiable §4 interface**: the recursion stops at a depth `D` where the instance has at
most one vertex, and activation is required only strictly above `D`.  The answer is an MSF with at
most `|P| - 1` edges.  The `4/3` bound is not claimed: the measure needs the phases at the bottom
level, which cannot exist. -/
theorem mst_main_stop (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (D : ℕ)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), d < D → i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (hstop : (lvlVerts G P E₀ D).card ≤ 1) :
    ∃ F : Finset E, IsMSFOf G E₀ F ∧ F.card ≤ P.card - 1 :=
  ⟨answer G P E₀ D ∅, tower_msf_of_stop hPE hP D hact hstop,
    tower_msf_of_stop_card hPE hP D hact hstop⟩

end DLMST
