import DLMST.Driver

/-!
# Dispatching edges to rounds

§3's procedure schedules every edge to exactly one of the `t²` rounds (Lemma 3.7's "each edge is
processed once"), and within a round classifies it as dropped (supported), kept in `F`, kept in
`U(F)`, or shipped to one sub-instance.  `Driver.lean` proves the two global facts this needs:
the partition identity and the round-sum.  Here the *round-indexed* data are wired in: fibers of a
schedule function, their disjointness and cardinality, the assembled partition theorem, and the
composition of the per-round comparison budgets with `round_budget_sum_paper`.
-/

namespace DLMST
open Classical
set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] {G : WGraph V E}

/-! ## Fibers of a schedule -/

/-- The edges scheduled to round `r`. -/
def rEdges (sched : E → ℕ) (r : ℕ) : Finset E :=
  Finset.univ.filter (fun e => sched e = r)

theorem mem_rEdges {sched : E → ℕ} {r : ℕ} {e : E} : e ∈ rEdges sched r ↔ sched e = r := by
  simp [rEdges]

theorem rEdges_disjoint {sched : E → ℕ} {r r' : ℕ} (h : r ≠ r') :
    Disjoint (rEdges sched r) (rEdges sched r') := by
  rw [Finset.disjoint_left]
  intro e he he'
  rw [mem_rEdges] at he he'
  exact h (he.symm.trans he')

/-- Every edge is processed in exactly one round: the fiber cardinalities sum to `|E|`. -/
theorem sum_rEdges_card {t : ℕ} (sched : E → ℕ) (hbound : ∀ e, sched e < t ^ 2) :
    (∑ r ∈ Finset.range (t ^ 2), (rEdges sched r).card) = Fintype.card E := by
  have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset E))
    (t := Finset.range (t ^ 2)) (f := sched) (fun e _ => Finset.mem_range.mpr (hbound e))
  simpa [rEdges] using this.symm

/-- Two pieces living in different rounds are disjoint. -/
theorem disjoint_of_rEdges_subset {sched : E → ℕ} {A B : Finset E} {r r' : ℕ}
    (hA : A ⊆ rEdges sched r) (hB : B ⊆ rEdges sched r') (h : r ≠ r') : Disjoint A B := by
  rw [Finset.disjoint_left]
  intro e he he'
  have h1 : sched e = r := mem_rEdges.mp (hA he)
  have h2 : sched e = r' := mem_rEdges.mp (hB he')
  exact h (h1.symm.trans h2)

/-! ## Assembling the rounds into one partition -/

/-- **The round-indexed partition identity.**  A schedule sends every edge to a round below `t²`.
If in every round the forest piece `F r`, the rejected piece `U r` and the child inputs `inp r i`
lie in that round's fiber, are pairwise disjoint, and cover the fiber, then the paper's display
sums distinct edges:
`|F| + |U| + Σ_{r,i} |inp r i| = |E|`. -/
theorem driver_partition {t : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (sched : E → ℕ) (hbound : ∀ e, sched e < t ^ 2)
    (F U : Fin (t ^ 2) → Finset E) (inp : Fin (t ^ 2) → ι → Finset E)
    (hFsub : ∀ r, F r ⊆ rEdges sched (r : ℕ))
    (hUsub : ∀ r, U r ⊆ rEdges sched (r : ℕ))
    (hinpsub : ∀ r i, inp r i ⊆ rEdges sched (r : ℕ))
    (hFU : ∀ r, Disjoint (F r) (U r))
    (hFi : ∀ r i, Disjoint (F r) (inp r i))
    (hUi : ∀ r i, Disjoint (U r) (inp r i))
    (hii : ∀ r, Set.PairwiseDisjoint (↑(Finset.univ : Finset ι)) (inp r))
    (hcov : ∀ r : Fin (t ^ 2), rEdges sched (r : ℕ) ⊆ F r ∪ U r ∪ Finset.univ.biUnion (inp r)) :
    (Finset.univ.biUnion F).card + (Finset.univ.biUnion U).card
      + ∑ r, ∑ i, (inp r i).card = Fintype.card E := by
  let inpg : Fin (t ^ 2) × ι → Finset E := fun p => inp p.1 p.2
  have hFUg : Disjoint (Finset.univ.biUnion F) (Finset.univ.biUnion U) := by
    rw [Finset.disjoint_biUnion_left]
    intro r _
    rw [Finset.disjoint_biUnion_right]
    intro r' _
    rcases eq_or_ne r r' with rfl | hne
    · exact hFU r
    · exact disjoint_of_rEdges_subset (hFsub r) (hUsub r') (fun h => hne (Fin.ext h))
  have hFig : ∀ p : Fin (t ^ 2) × ι, Disjoint (Finset.univ.biUnion F) (inpg p) := by
    rintro ⟨r', i'⟩
    rw [Finset.disjoint_biUnion_left]
    intro r _
    rcases eq_or_ne r r' with rfl | hne
    · exact hFi r i'
    · exact disjoint_of_rEdges_subset (hFsub r) (hinpsub r' i') (fun h => hne (Fin.ext h))
  have hUig : ∀ p : Fin (t ^ 2) × ι, Disjoint (Finset.univ.biUnion U) (inpg p) := by
    rintro ⟨r', i'⟩
    rw [Finset.disjoint_biUnion_left]
    intro r _
    rcases eq_or_ne r r' with rfl | hne
    · exact hUi r i'
    · exact disjoint_of_rEdges_subset (hUsub r) (hinpsub r' i') (fun h => hne (Fin.ext h))
  have hiig : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin (t ^ 2) × ι))) inpg := by
    rintro ⟨r, i⟩ _ ⟨r', i'⟩ _ hne
    show Disjoint (inp r i) (inp r' i')
    rw [Finset.disjoint_left]
    intro e he he'
    rcases eq_or_ne r r' with rfl | hrr
    · have hii' : i ≠ i' := by
        intro h
        exact hne (by rw [h])
      exact (Finset.disjoint_left.mp ((hii r) (Finset.mem_univ i) (Finset.mem_univ i') hii')) he he'
    · exact Finset.disjoint_left.mp
        (disjoint_of_rEdges_subset (hinpsub r i) (hinpsub r' i') (fun h => hrr (Fin.ext h))) he he'
  have hcovg : Finset.univ.biUnion F ∪ Finset.univ.biUnion U ∪ Finset.univ.biUnion inpg
      = Finset.univ := by
    ext e
    constructor
    · intro _
      exact Finset.mem_univ e
    · intro _
      let rf : Fin (t ^ 2) := ⟨sched e, hbound e⟩
      have he : e ∈ rEdges sched (rf : ℕ) := mem_rEdges.mpr (by simp [rf])
      have hmem : e ∈ F rf ∪ U rf ∪ Finset.univ.biUnion (inp rf) := hcov rf he
      rw [Finset.mem_union] at hmem
      rcases hmem with hFU' | hI
      · rw [Finset.mem_union] at hFU'
        rcases hFU' with hF | hU
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
            (Or.inl (Finset.mem_biUnion.mpr ⟨rf, Finset.mem_univ _, hF⟩))))
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
            (Or.inr (Finset.mem_biUnion.mpr ⟨rf, Finset.mem_univ _, hU⟩))))
      · rw [Finset.mem_biUnion] at hI
        obtain ⟨i, _, hi⟩ := hI
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
          ⟨(rf, i), Finset.mem_univ _, hi⟩))
  have hmain := card_partition_eq (E := E) (ι := Fin (t ^ 2) × ι)
    (F := Finset.univ.biUnion F) (U := Finset.univ.biUnion U) (inp := inpg)
    hFUg hFig hUig hiig hcovg
  rw [Fintype.sum_prod_type] at hmain
  simpa [inpg] using hmain

/-! ## The comparison budget over the rounds -/

/-- **The driver's comparison count.**  If round `i` costs at most `C·(n + t√(mᵢn))` on its own
`mᵢ` scheduled edges, then the whole run costs at most `C·t²·(n + √(mn))` — §3.5's closing
computation, with the fiber sizes supplied by the schedule rather than assumed. -/
theorem driver_comparisons {t n : ℕ} {C : ℝ} {budget : ℕ → ℝ} (sched : E → ℕ)
    (hbound : ∀ e, sched e < t ^ 2) (hC : 0 ≤ C)
    (hbudget : ∀ i ∈ Finset.range (t ^ 2),
      budget i ≤ C * ((n : ℝ) + (t : ℝ) * Real.sqrt (((rEdges sched i).card : ℝ) * (n : ℝ)))) :
    (∑ i ∈ Finset.range (t ^ 2), budget i)
      ≤ C * ((t : ℝ) ^ 2 * ((n : ℝ) + Real.sqrt ((Fintype.card E : ℝ) * (n : ℝ)))) := by
  refine round_budget_sum_paper (m := Fintype.card E) (mL := fun i => (rEdges sched i).card)
    hC ?_ hbudget
  rw [← Nat.cast_sum, sum_rEdges_card sched hbound]

/-! ## The instance-relative driver: fibers inside a fixed edge set `E₀` -/

/-- The edges *of `E₀`* scheduled to round `r`.  A single instance of the recursion (with edge set
`E₀`) runs the same driver, but only sees its own edges; the counts must therefore total `|E₀|`,
not `|E|`. -/
def rEdgesIn (E₀ : Finset E) (sched : E → ℕ) (r : ℕ) : Finset E :=
  E₀.filter (fun e => sched e = r)

theorem mem_rEdgesIn {E₀ : Finset E} {sched : E → ℕ} {r : ℕ} {e : E} :
    e ∈ rEdgesIn E₀ sched r ↔ e ∈ E₀ ∧ sched e = r := by
  simp [rEdgesIn]

theorem rEdgesIn_subset (E₀ : Finset E) (sched : E → ℕ) (r : ℕ) :
    rEdgesIn E₀ sched r ⊆ E₀ :=
  Finset.filter_subset _ _

/-- Two pieces living in different rounds are disjoint (instance-relative fibers). -/
theorem disjoint_of_rEdgesIn_subset {E₀ : Finset E} {sched : E → ℕ} {A B : Finset E} {r r' : ℕ}
    (hA : A ⊆ rEdgesIn E₀ sched r) (hB : B ⊆ rEdgesIn E₀ sched r') (h : r ≠ r') :
    Disjoint A B := by
  rw [Finset.disjoint_left]
  intro e he he'
  exact h ((mem_rEdgesIn.mp (hA he)).2.symm.trans (mem_rEdgesIn.mp (hB he')).2)

/-- Every edge of `E₀` is processed in exactly one round: the instance-relative fiber
cardinalities sum to `|E₀|`. -/
theorem sum_rEdgesIn_card {t : ℕ} (E₀ : Finset E) (sched : E → ℕ)
    (hbound : ∀ e ∈ E₀, sched e < t ^ 2) :
    (∑ r ∈ Finset.range (t ^ 2), (rEdgesIn E₀ sched r).card) = E₀.card := by
  have := Finset.card_eq_sum_card_fiberwise (s := E₀)
    (t := Finset.range (t ^ 2)) (f := sched) (fun e he => Finset.mem_range.mpr (hbound e he))
  simpa [rEdgesIn] using this.symm

/-- **The round-indexed partition identity for one instance.**  Identical to `driver_partition`,
but every fiber lives inside `E₀`, the covering requirement is over `E₀`, and the total is
`|E₀|`. -/
theorem driver_partition_in {t : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E₀ : Finset E) (sched : E → ℕ) (hbound : ∀ e ∈ E₀, sched e < t ^ 2)
    (F U : Fin (t ^ 2) → Finset E) (inp : Fin (t ^ 2) → ι → Finset E)
    (hFsub : ∀ r, F r ⊆ rEdgesIn E₀ sched (r : ℕ))
    (hUsub : ∀ r, U r ⊆ rEdgesIn E₀ sched (r : ℕ))
    (hinpsub : ∀ r i, inp r i ⊆ rEdgesIn E₀ sched (r : ℕ))
    (hFU : ∀ r, Disjoint (F r) (U r))
    (hFi : ∀ r i, Disjoint (F r) (inp r i))
    (hUi : ∀ r i, Disjoint (U r) (inp r i))
    (hii : ∀ r, Set.PairwiseDisjoint (↑(Finset.univ : Finset ι)) (inp r))
    (hcov : ∀ r : Fin (t ^ 2), rEdgesIn E₀ sched (r : ℕ) ⊆ F r ∪ U r ∪ Finset.univ.biUnion (inp r)) :
    (Finset.univ.biUnion F).card + (Finset.univ.biUnion U).card
      + ∑ r, ∑ i, (inp r i).card = E₀.card := by
  let inpg : Fin (t ^ 2) × ι → Finset E := fun p => inp p.1 p.2
  have hFUg : Disjoint (Finset.univ.biUnion F) (Finset.univ.biUnion U) := by
    rw [Finset.disjoint_biUnion_left]
    intro r _
    rw [Finset.disjoint_biUnion_right]
    intro r' _
    rcases eq_or_ne r r' with rfl | hne
    · exact hFU r
    · exact disjoint_of_rEdgesIn_subset (hFsub r) (hUsub r') (fun h => hne (Fin.ext h))
  have hFig : ∀ p : Fin (t ^ 2) × ι, Disjoint (Finset.univ.biUnion F) (inpg p) := by
    rintro ⟨r', i'⟩
    rw [Finset.disjoint_biUnion_left]
    intro r _
    rcases eq_or_ne r r' with rfl | hne
    · exact hFi r i'
    · exact disjoint_of_rEdgesIn_subset (hFsub r) (hinpsub r' i') (fun h => hne (Fin.ext h))
  have hUig : ∀ p : Fin (t ^ 2) × ι, Disjoint (Finset.univ.biUnion U) (inpg p) := by
    rintro ⟨r', i'⟩
    rw [Finset.disjoint_biUnion_left]
    intro r _
    rcases eq_or_ne r r' with rfl | hne
    · exact hUi r i'
    · exact disjoint_of_rEdgesIn_subset (hUsub r) (hinpsub r' i') (fun h => hne (Fin.ext h))
  have hiig : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin (t ^ 2) × ι))) inpg := by
    rintro ⟨r, i⟩ _ ⟨r', i'⟩ _ hne
    show Disjoint (inp r i) (inp r' i')
    rw [Finset.disjoint_left]
    intro e he he'
    rcases eq_or_ne r r' with rfl | hrr
    · have hii' : i ≠ i' := by
        intro h
        exact hne (by rw [h])
      exact (Finset.disjoint_left.mp ((hii r) (Finset.mem_univ i) (Finset.mem_univ i') hii')) he he'
    · exact Finset.disjoint_left.mp
        (disjoint_of_rEdgesIn_subset (hinpsub r i) (hinpsub r' i') (fun h => hrr (Fin.ext h))) he he'
  have hcovg : Finset.univ.biUnion F ∪ Finset.univ.biUnion U ∪ Finset.univ.biUnion inpg
      = E₀ := by
    ext e
    constructor
    · intro hmem
      rcases Finset.mem_union.mp hmem with hFU' | hI
      · rcases Finset.mem_union.mp hFU' with hF | hU
        · obtain ⟨r, _, hr⟩ := Finset.mem_biUnion.mp hF
          exact rEdgesIn_subset E₀ sched (r : ℕ) (hFsub r hr)
        · obtain ⟨r, _, hr⟩ := Finset.mem_biUnion.mp hU
          exact rEdgesIn_subset E₀ sched (r : ℕ) (hUsub r hr)
      · obtain ⟨⟨r, i⟩, _, hi⟩ := Finset.mem_biUnion.mp hI
        exact rEdgesIn_subset E₀ sched (r : ℕ) (hinpsub r i hi)
    · intro he₀
      let rf : Fin (t ^ 2) := ⟨sched e, hbound e he₀⟩
      have he : e ∈ rEdgesIn E₀ sched (rf : ℕ) := mem_rEdgesIn.mpr ⟨he₀, by simp [rf]⟩
      have hmem : e ∈ F rf ∪ U rf ∪ Finset.univ.biUnion (inp rf) := hcov rf he
      rw [Finset.mem_union] at hmem
      rcases hmem with hFU' | hI
      · rw [Finset.mem_union] at hFU'
        rcases hFU' with hF | hU
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
            (Or.inl (Finset.mem_biUnion.mpr ⟨rf, Finset.mem_univ _, hF⟩))))
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
            (Or.inr (Finset.mem_biUnion.mpr ⟨rf, Finset.mem_univ _, hU⟩))))
      · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hI
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
          ⟨(rf, i), Finset.mem_univ _, hi⟩))
  have hmain := card_partition_eq_of_subset (S := E₀) (ι := Fin (t ^ 2) × ι)
    (F := Finset.univ.biUnion F) (U := Finset.univ.biUnion U) (inp := inpg)
    hFUg hFig hUig hiig hcovg
  rw [Fintype.sum_prod_type] at hmain
  simpa [inpg] using hmain

/-- **The instance's comparison count.**  Round `i` costs at most `C·(n + t√(mᵢn))` on the `mᵢ`
edges of `E₀` scheduled to it; then the instance's run costs at most `C·t²·(n + √(|E₀|n))`. -/
theorem driver_comparisons_in {t n : ℕ} {C : ℝ} {budget : ℕ → ℝ} (E₀ : Finset E) (sched : E → ℕ)
    (hbound : ∀ e ∈ E₀, sched e < t ^ 2) (hC : 0 ≤ C)
    (hbudget : ∀ i ∈ Finset.range (t ^ 2),
      budget i ≤ C * ((n : ℝ) + (t : ℝ) * Real.sqrt (((rEdgesIn E₀ sched i).card : ℝ) * (n : ℝ)))) :
    (∑ i ∈ Finset.range (t ^ 2), budget i)
      ≤ C * ((t : ℝ) ^ 2 * ((n : ℝ) + Real.sqrt ((E₀.card : ℝ) * (n : ℝ)))) := by
  refine round_budget_sum_paper (m := E₀.card) (mL := fun i => (rEdgesIn E₀ sched i).card)
    hC ?_ hbudget
  rw [← Nat.cast_sum, sum_rEdgesIn_card E₀ sched hbound]

end DLMST