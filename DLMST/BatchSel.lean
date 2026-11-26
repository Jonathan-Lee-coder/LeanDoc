import DLMST.Batch

/-!
# A `BatchSpec` really exists: the `k` lightest representatives

`Batch.lean` takes the selection `sel` as an interface (`BatchSpec`).  This file supplies a witness:
at every vertex keep the lightest `k` representatives of the batch groups seen from that vertex, in
the tie-broken linear order.  The five `BatchSpec` fields are then exactly the properties of a
sorted list cut after `k` elements: the cut is a subsingleton of the batch, has at most `k` entries,
its entries are representatives, a representative left out forces a full quota, and everything kept
is at most everything dropped.

Not formalised: that Lemma 3.3's search *finds* these representatives within the stated comparison
budget (the budget itself is `Halving.lemma33_comparisons`; `Selection.lean` has the search's
correctness statement).
-/

namespace DLMST
open Classical
set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {G : WGraph V E} [LinearOrder E]

/-- The representatives of the batch seen from `v`: the lightest admissible edge of every group. -/
noncomputable def repsAt (G : WGraph V E) (B : Finset E) (adm : E → Prop) (v : V) : Finset E :=
  (Bv G v B).filter (fun e => IsRep (other G v) adm (Bv G v B) e)

/-- The representatives sorted in the tie-broken order — the sequence Lemma 3.3's search walks. -/
noncomputable def sortReps (G : WGraph V E) (B : Finset E) (adm : E → Prop) (v : V) : List E :=
  (repsAt G B adm v).sort (fun a b : E => a ≤ b)

/-- The declared set from `v`: the `k` lightest representatives. -/
noncomputable def selAt (G : WGraph V E) (B : Finset E) (adm : E → Prop) (k : ℕ) (v : V) :
    Finset E :=
  (sortReps G B adm v).take k |>.toFinset

theorem mem_repsAt {B : Finset E} {adm : E → Prop} {v : V} {e : E} :
    e ∈ repsAt G B adm v ↔ e ∈ Bv G v B ∧ IsRep (other G v) adm (Bv G v B) e := by
  simp [repsAt]

theorem mem_sortReps {B : Finset E} {adm : E → Prop} {v : V} {e : E} :
    e ∈ sortReps G B adm v ↔ e ∈ repsAt G B adm v :=
  Finset.mem_sort (fun a b : E => a ≤ b)

theorem sortReps_nodup {B : Finset E} {adm : E → Prop} {v : V} :
    (sortReps G B adm v).Nodup :=
  Finset.sort_nodup (repsAt G B adm v) (fun a b : E => a ≤ b)

theorem sortReps_pairwise {B : Finset E} {adm : E → Prop} {v : V} :
    (sortReps G B adm v).Pairwise (fun a b : E => a < b) :=
  (Finset.sortedLT_sort (repsAt G B adm v)).pairwise

theorem mem_selAt {B : Finset E} {adm : E → Prop} {k : ℕ} {v : V} {e : E} :
    e ∈ selAt G B adm k v ↔ e ∈ (sortReps G B adm v).take k :=
  List.mem_toFinset

/-- **Lemma 3.3's selection exists.**  Cutting the sorted representatives at `k` satisfies the whole
`BatchSpec`: nothing outside the batch, quota respected, only representatives, a left-out
representative means the quota is full, and kept edges are at most dropped ones. -/
theorem batchSpec_selAt (G : WGraph V E) (B : Finset E) (adm : E → Prop) (k : ℕ) :
    BatchSpec G B adm k (selAt G B adm k) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v e he
    have hfl : e ∈ sortReps G B adm v := List.mem_of_mem_take (mem_selAt.mp he)
    exact (mem_repsAt.mp (mem_sortReps.mp hfl)).1
  · intro v
    have h1 : (selAt G B adm k v).card ≤ ((sortReps G B adm v).take k).length :=
      List.toFinset_card_le ((sortReps G B adm v).take k)
    have h2 : ((sortReps G B adm v).take k).length = min k (sortReps G B adm v).length :=
      List.length_take
    omega
  · intro v f hf
    have hfl : f ∈ sortReps G B adm v := List.mem_of_mem_take (mem_selAt.mp hf)
    exact (mem_repsAt.mp (mem_sortReps.mp hfl)).2
  · intro v e he
    have hR : e ∈ repsAt G B adm v := mem_repsAt.mpr ⟨he.1, he⟩
    have hel : e ∈ sortReps G B adm v := mem_sortReps.mpr hR
    by_cases hmem : e ∈ (sortReps G B adm v).take k
    · exact Or.inl (mem_selAt.mpr hmem)
    · refine Or.inr ?_
      obtain ⟨j, hj, hgetj⟩ := List.getElem_of_mem hel
      have hkj : k ≤ j := by
        by_contra hlt
        have hlt2 : j < k := by omega
        have hltlen : j < ((sortReps G B adm v).take k).length := by
          rw [List.length_take]
          exact lt_min hlt2 hj
        have h1 : ((sortReps G B adm v).take k)[j] = e := by
          rw [List.getElem_take]
          exact hgetj
        exact hmem (List.mem_of_getElem h1)
      have hnodup : ((sortReps G B adm v).take k).Nodup :=
        List.Sublist.nodup (List.take_sublist k _) sortReps_nodup
      rw [selAt, List.toFinset_card_of_nodup hnodup, List.length_take,
        Nat.min_eq_left (le_trans hkj (le_of_lt hj))]
  · intro v f hf e he heNot
    have hftake : f ∈ (sortReps G B adm v).take k := mem_selAt.mp hf
    have hfl : f ∈ sortReps G B adm v := List.mem_of_mem_take hftake
    have hR : e ∈ repsAt G B adm v := mem_repsAt.mpr ⟨he.1, he⟩
    have hel : e ∈ sortReps G B adm v := mem_sortReps.mpr hR
    obtain ⟨i, hi, hgeti⟩ := List.getElem_of_mem hfl
    obtain ⟨j, hj, hgetj⟩ := List.getElem_of_mem hel
    have hik : i < k := by
      obtain ⟨i', hi', hgeti'⟩ := List.getElem_of_mem hftake
      have hlen_le : ((sortReps G B adm v).take k).length ≤ (sortReps G B adm v).length := by
        rw [List.length_take]
        exact Nat.min_le_right _ _
      have hi'k : i' < k := by
        rw [List.length_take] at hi'
        exact lt_of_lt_of_le hi' (Nat.min_le_left _ _)
      have heq : (sortReps G B adm v)[i'] = (sortReps G B adm v)[i] := by
        have h1 : ((sortReps G B adm v).take k)[i'] = (sortReps G B adm v)[i'] :=
          List.getElem_take
        rw [h1] at hgeti'
        exact hgeti'.trans hgeti.symm
      have hinj := (List.Nodup.getElem_inj sortReps_nodup).mp heq
      omega
    have hkj : k ≤ j := by
      by_contra hlt
      have hlt2 : j < k := by omega
      have hltlen : j < ((sortReps G B adm v).take k).length := by
        rw [List.length_take]
        exact lt_min hlt2 hj
      have h1 : ((sortReps G B adm v).take k)[j] = e := by
        rw [List.getElem_take]
        exact hgetj
      exact heNot (mem_selAt.mpr (List.mem_of_getElem h1))
    have hij : i < j := lt_of_lt_of_le hik hkj
    have hlt : (sortReps G B adm v)[i] < (sortReps G B adm v)[j] :=
      sortReps_pairwise.rel_get_of_lt (show (⟨i, hi⟩ : Fin _) < ⟨j, hj⟩ from hij)
    rw [← hgeti, ← hgetj]
    exact le_of_lt hlt

theorem exists_batchSpec (G : WGraph V E) (B : Finset E) (adm : E → Prop) (k : ℕ) :
    ∃ sel : V → Finset E, BatchSpec G B adm k sel :=
  ⟨selAt G B adm k, batchSpec_selAt G B adm k⟩

/-- **The spoke update exists.**  Given the portal covering and a total incident "old" spoke map,
choose at each full vertex the candidate `exists_cnd` supplies and keep the lighter of it and the old
spoke.  The three `SpokeSpec` fields are then transparent; the only content is that the candidate is
an incident edge of `sel v`, hence of `Bv`. -/
theorem exists_spokeSpec {P : Finset V} {sel : V → Finset E} (hsel : BatchSpec G B adm k sel)
    (hcover : ∀ v, k ≤ (Sv G v sel).card → ∃ x ∈ Sv G v sel, x ∈ P)
    [Nonempty E] (σold : V → E) (hspold : ∀ v, incident G v (σold v)) :
    ∃ cnd σ : V → E, SpokeSpec G sel k P cnd σ := by
  classical
  have hwit : ∀ v, (sel v).card = k → ∃ f ∈ sel v, other G v f ∈ P :=
    fun v hv => exists_cnd hsel P hcover v hv
  let cnd : V → E := fun v =>
    if hv : (sel v).card = k then (hwit v hv).choose else Classical.arbitrary E
  have hcnd_in : ∀ v, (sel v).card = k → cnd v ∈ sel v := by
    intro v hv
    show (if hv' : (sel v).card = k then (hwit v hv').choose else Classical.arbitrary E) ∈ sel v
    rw [dite_eq_left hv]
    exact (hwit v hv).choose_spec.1
  have hcnd_P : ∀ v, (sel v).card = k → other G v (cnd v) ∈ P := by
    intro v hv
    show other G v (if hv' : (sel v).card = k then (hwit v hv').choose else
      Classical.arbitrary E) ∈ P
    rw [dite_eq_left hv]
    exact (hwit v hv).choose_spec.2
  let σ : V → E := fun v =>
    if hv : (sel v).card = k then
      if G.weight (σold v) ≤ G.weight (cnd v) then σold v else cnd v
    else σold v
  refine ⟨cnd, σ, hcnd_in, hcnd_P, ?_⟩
  intro v hv
  show incident G v (if hv' : (sel v).card = k then
      if G.weight (σold v) ≤ G.weight (cnd v) then σold v else cnd v
    else σold v) ∧
    G.weight (if hv' : (sel v).card = k then
      if G.weight (σold v) ≤ G.weight (cnd v) then σold v else cnd v
    else σold v) ≤ G.weight (cnd v)
  rw [dite_eq_left hv]
  by_cases hw : G.weight (σold v) ≤ G.weight (cnd v)
  · rw [ite_eq_left hw]
    exact ⟨hspold v, hw⟩
  · rw [ite_eq_right hw]
    have hmem := hsel.sel_sub v (hcnd_in v hv)
    exact ⟨(mem_Bv.mp hmem).2, le_rfl⟩

end DLMST