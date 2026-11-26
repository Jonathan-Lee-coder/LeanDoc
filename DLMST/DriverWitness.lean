import DLMST.DriverEvidence

/-!
# A concrete driver call: the interface is inhabited

`DriverCall` bundles five decisions (slot map, portals within budget, endpoint geometry, spoke
batches with a quota, and the batches' non-forest *supply*).  The supply field is the strong one, so
this file shows the whole record is inhabited: on the **two-vertex graph with five parallel edges**,
one round (`t = 1`), all edges in one slot, `B := univ` and no portals, every vertex keeps an
incident batch edge outside the scan forest — because the forest of a scan is a forest on two
vertices, so it holds at most one edge while each vertex sees all five.

The point is non-vacuity, not the algorithm's behaviour: `history_legalOn` (第一百一十五批) is then
instantiated at a real driver call, so the premise `LegalOn` of the instance-local Lemma 3.10/3.11
is met by an object that also satisfies `hsupply` — not only by the canonical constant history.
-/

namespace DLMST

open Classical

namespace DriverWitness

/-- The witness graph: two vertices, five parallel edges `0 … 4` from `0` to `1`. -/
def Gpar : WGraph (Fin 2) (Fin 5) where
  endpoints _ := (0, 1)
  weight e := ((e : ℕ) : ℝ)

/-- Every edge is incident to every vertex (both endpoints are `0` and `1`). -/
theorem incident_all (v : Fin 2) (e : Fin 5) : incident Gpar v e := by
  fin_cases v <;> simp [incident, WGraph.src, WGraph.dst, Gpar]

/-- The one-slot map used by the witness. -/
def slotPar : Fin 5 → Fin (1 ^ 2) := fun _ => 0

/-- The scan forest of the witness holds at most one edge (a forest on `2` vertices). -/
theorem preF_par_card_le :
    (preF (G := Gpar) (scanOfSlot (t := 1) slotPar (Finset.univ : Finset (Fin 2))
      (Finset.univ : Finset (Fin 5))) (1 ^ 2)).card ≤ 1 := by
  have h := card_le_card_sub_one_of_isForest_of_ends (G := Gpar)
    (isForest_preF (G := Gpar)
      (scanOfSlot (t := 1) slotPar (Finset.univ : Finset (Fin 2))
        (Finset.univ : Finset (Fin 5))) (1 ^ 2))
    (fun _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩)
    (by simp : 0 < (Finset.univ : Finset (Fin 2)).card)
  simpa using h

/-- The witness call: instance `(univ, univ)`, one round, one slot, no portals, batch `univ`. -/
noncomputable def callPar : DriverCall Gpar (Finset.univ : Finset (Fin 2))
    (Finset.univ : Finset (Fin 5)) 1 where
  slot := slotPar
  Pp := ∅
  hP' := Finset.empty_subset _
  hbudget := by simp
  hends := by intro e _; exact ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  B := fun _ _ => Finset.univ
  quota := 1
  hquota := le_refl 1
  hsupply := by
    intro _ _ v
    have hnot : ¬ (Finset.univ : Finset (Fin 5)) ⊆
        preF (G := Gpar) (scanOfSlot (t := 1) slotPar (Finset.univ : Finset (Fin 2))
          (Finset.univ : Finset (Fin 5))) (1 ^ 2) := by
      intro hsub
      have hc := Finset.card_le_card hsub
      have h5 : (Finset.univ : Finset (Fin 5)).card = 5 := by simp
      have h2 := preF_par_card_le
      omega
    obtain ⟨e, _, hepre⟩ := Finset.not_subset.mp hnot
    exact ⟨e, by rw [mem_Bv]; exact ⟨Finset.mem_univ _, incident_all v e⟩, hepre⟩

/-- The interface is inhabited: `hsupply` and the other four decisions coexist. -/
theorem callPar_nonempty : Nonempty (DriverCall Gpar (Finset.univ : Finset (Fin 2))
    (Finset.univ : Finset (Fin 5)) 1) :=
  ⟨callPar⟩

/-- The witness call's history is a legal instance history (`LegalOn`), so `history_legalOn`'s
premises (`hB`, `hP0`) are dischargeable at a real driver call, not only at `canonicalHistory`. -/
theorem callPar_legalOn :
    LegalOn (G := Gpar) (Finset.univ : Finset (Fin 2)) (Finset.univ : Finset (Fin 5))
      (0 : Fin 5) callPar.history :=
  DriverCall.history_legalOn callPar (0 : Fin 5) (fun _ _ => Finset.subset_univ _) (by simp)

end DriverWitness

end DLMST