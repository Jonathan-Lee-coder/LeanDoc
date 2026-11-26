import DLMST.ProcChain

/-!
# A witness: the level-chain structure is inhabited

`ProcChain` bundles a projection chain with the per-level facts a real run supplies (`Consistent`
history, `project` at the assigned slot, frozen spokes, the child's return, Claim 3.6's hypotheses).
A structure with this many interacting fields is only meaningful if it can be inhabited; this file
builds the smallest instance:

* one edge, two vertices: `V = Fin 2`, `E = Fin 1`, the edge joining `0` and `1` with weight `0`;
* a history of length `t = 1`, constant spoke `σ ≡ 0`, empty forests, action row `project`;
* the constant projection chain `lev j = ⟨0, {0}⟩`, child instance `{0}`, lifted path `[0]`.

The edge prefers `project` in the empty forest (both ends have spokes, the portals `1` and `0`
differ, and nothing joins the ends below `p(e) = 0`), so the history is consistent with the action
row; the child instance's MSF is the edge itself, and the lifted path `1 -- 0` is the edge `[0]`.
Every field of `ProcChain` is discharged, so `ProcChain` is not vacuously unsatisfiable.
-/

namespace DLMST

namespace Witness

abbrev Vw : Type := Fin 2
abbrev Ew : Type := Fin 1

/-- The graph: one edge joining the two vertices, weight zero. -/
def Gw : WGraph Vw Ew where
  endpoints := fun _ => (0, 1)
  weight := fun _ => 0

/-- The history: empty forests, the only spokes, and the action `project`. -/
def Hw : History Vw Ew 1 where
  spoke := fun _ _ _ => (0 : Ew)
  forest := fun _ _ => ∅
  pref := fun _ _ _ => Pref.project

theorem portal_zero : portal Gw (fun _ => (0 : Ew)) (0 : Vw) = 1 := by
  simp [portal, other, Gw, WGraph.src, WGraph.dst]

theorem portal_one : portal Gw (fun _ => (0 : Ew)) (1 : Vw) = 0 := by
  simp [portal, other, Gw, WGraph.src]

theorem edge_ne : Gw.src (0 : Ew) ≠ Gw.dst (0 : Ew) := by
  simp [Gw, WGraph.src, WGraph.dst]

/-- In the empty forest the edge prefers `project`. -/
theorem not_prefFind : ¬ prefFind Gw (fun _ => (0 : Ew)) ∅ (0 : Ew) := by
  intro h
  rcases h with h1 | h2 | h3 | h4
  · exact h1 (Or.inl rfl)
  · exact h2 (Or.inr rfl)
  · simp [portal, other, Gw, WGraph.src, WGraph.dst] at h3
  · simp only [belowLe, Finset.filter_empty] at h4
    exact absurd (conn_empty_eq h4) (by decide)

theorem actOf_eq : actOf Gw (fun _ => (0 : Ew)) ∅ (0 : Ew) = Pref.project := by
  simp [actOf, not_prefFind]

theorem consistent : Hw.Consistent (G := Gw) := by
  intro e b i
  have he : e = (0 : Ew) := Subsingleton.elim e 0
  subst he
  simp [Hw, actOf, not_prefFind]

/-- The single edge is an MSF of its own instance. -/
theorem msf : IsMSFOf Gw ({0} : Finset Ew) ({0} : Finset Ew) := by
  have h01 : Gw.src (0 : Ew) ≠ Gw.dst (0 : Ew) := edge_ne
  have hnc : ¬ Conn Gw (∅ : Finset Ew) (Gw.src (0 : Ew)) (Gw.dst (0 : Ew)) :=
    fun h => h01 (conn_empty_eq h)
  have hforest : IsForest Gw ({0} : Finset Ew) := IsForest.add IsForest.empty h01 hnc
  refine ⟨⟨hforest, Finset.singleton_subset_iff.mpr (Finset.mem_singleton_self 0), ?_⟩, ?_⟩
  · intro e he _
    obtain rfl : e = 0 := Finset.mem_singleton.mp he
    exact Conn.step 0 (Finset.mem_singleton_self 0)
  · intro T' hT'
    have hsub := hT'.2.1
    have hspan := hT'.2.2
    have hconn := hspan (0 : Ew) (Finset.mem_singleton_self 0) h01
    have hmem : (0 : Ew) ∈ T' := by
      by_contra hnot
      have hempty : T' = ∅ := by
        rw [← Finset.not_nonempty_iff_eq_empty]
        rintro ⟨x, hx⟩
        have hx0 : x = 0 := Finset.mem_singleton.mp (hsub hx)
        exact hnot (hx0 ▸ hx)
      rw [hempty] at hconn
      exact h01 (conn_empty_eq hconn)
    have hTeq : T' = {0} :=
      Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hmem)
    rw [hTeq]

theorem lifts : LiftsLe Gw (fun _ => (0 : Ew)) ({0} : Finset Ew) 0 1 [0] 0 :=
  LiftsLe.step ⟨portal_zero, portal_one, Or.inl ⟨rfl, rfl⟩⟩
    ⟨Finset.mem_singleton_self 0, Finset.mem_singleton_self 0, Finset.mem_singleton_self 0⟩
    ⟨le_rfl, le_rfl, le_rfl⟩ LiftsLe.nil

/-- A genuine level chain: every field of `ProcChain` is satisfied. -/
noncomputable def chain : ProcChain (G := Gw) Hw (fun _ => (⟨0, ({0} : Finset Ew)⟩ : Lev Ew)) where
  slot := fun _ => (0, 0)
  hcons := consistent
  hproj := fun _ => rfl
  hfroz := fun _ _ => rfl
  hret := fun _ i hi => absurd hi (by have h2 := i.isLt; omega)
  hsub := fun _ => Finset.Subset.refl _
  S := fun _ => {0}
  es := fun _ => [0]
  hmsf := fun _ => msf
  hspoke := fun _ x => by
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  hlift := fun _ => by
    simpa [Hw, Lev.e, Gw, WGraph.src, WGraph.dst, portal, other] using lifts
  hσS := fun _ _ => Finset.mem_singleton_self _

theorem nonempty : Nonempty (ProcChain (G := Gw) Hw (fun _ => (⟨0, ({0} : Finset Ew)⟩ : Lev Ew))) :=
  ⟨chain⟩

end Witness

end DLMST