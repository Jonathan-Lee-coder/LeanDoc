import DLMST.Filtering

/-!
# The certificate call's global bookkeeping

Lemma 1.2's display `|F| + |U(F)| + Σ_i |E_i|` counts *distinct* edges of `E(G)`: the forest the
certificate procedure returns, the unsupported edges, and the inputs of the exact MSF calls are
pairwise disjoint, and (in the equality form) cover the edge set.  This is the global reading of
Lemma 3.7 that `Section36.lean` carries as `hrest`; here it is proved as finite-set arithmetic.

The second part is §3.5's closing computation for the comparison count: `t²` rounds each spending
`O(n + t√(mᵢn))` on `mᵢ` edges with `Σ mᵢ ≤ m` cost `O(t²n + t²√(mn))` in total.  The only
inequality of substance is Cauchy–Schwarz for `Σ √(mᵢn)` (`Real.sum_sqrt_mul_sqrt_le`).
-/

namespace DLMST
open Classical
set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] {G : WGraph V E}

/-! ## Every edge is classified exactly once -/

/-- **The partition identity.**  If `F`, `U` and the child inputs `inp i` are pairwise disjoint
and cover `E`, then `|F| + |U| + Σ_i |inp i| = |E|`.  This is why the display of Lemma 1.2
sums distinct edges rather than running over the edges `E(G)` with multiplicity. -/
theorem card_partition_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F U : Finset E} {inp : ι → Finset E}
    (hFU : Disjoint F U)
    (hFi : ∀ i, Disjoint F (inp i))
    (hUi : ∀ i, Disjoint U (inp i))
    (hii : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι)) inp)
    (hcover : F ∪ U ∪ Finset.univ.biUnion inp = Finset.univ) :
    F.card + U.card + ∑ i, (inp i).card = Fintype.card E := by
  have hUnion : Disjoint (F ∪ U) (Finset.univ.biUnion inp) := by
    rw [Finset.disjoint_biUnion_right]
    intro i _
    rw [Finset.disjoint_union_left]
    exact ⟨hFi i, hUi i⟩
  have h1 : (F ∪ U ∪ Finset.univ.biUnion inp).card
      = F.card + U.card + (Finset.univ.biUnion inp).card := by
    rw [Finset.card_union_of_disjoint hUnion, Finset.card_union_of_disjoint hFU]
  have h2 : (Finset.univ.biUnion inp).card = ∑ i, (inp i).card :=
    Finset.card_biUnion hii
  have h3 : Fintype.card E = F.card + U.card + (Finset.univ.biUnion inp).card := by
    rw [← h1, hcover, Finset.card_univ]
  omega

/-- **The partition identity over a base set.**  The same count with `E` replaced by a finite set `S`:
if `F`, `U` and the child inputs are pairwise disjoint and their union is `S`, then
`|F| + |U| + Σᵢ|inp i| = |S|`.  This is the form a single *instance* of the recursion needs: its
edges are `E₀`, not all of `E(G)`. -/
theorem card_partition_eq_of_subset {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S F U : Finset E} {inp : ι → Finset E}
    (hFU : Disjoint F U)
    (hFi : ∀ i, Disjoint F (inp i))
    (hUi : ∀ i, Disjoint U (inp i))
    (hii : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι)) inp)
    (hcover : F ∪ U ∪ Finset.univ.biUnion inp = S) :
    F.card + U.card + ∑ i, (inp i).card = S.card := by
  have hUnion : Disjoint (F ∪ U) (Finset.univ.biUnion inp) := by
    rw [Finset.disjoint_biUnion_right]
    intro i _
    rw [Finset.disjoint_union_left]
    exact ⟨hFi i, hUi i⟩
  have h1 : (F ∪ U ∪ Finset.univ.biUnion inp).card
      = F.card + U.card + (Finset.univ.biUnion inp).card := by
    rw [Finset.card_union_of_disjoint hUnion, Finset.card_union_of_disjoint hFU]
  have h2 : (Finset.univ.biUnion inp).card = ∑ i, (inp i).card :=
    Finset.card_biUnion hii
  rw [hcover] at h1
  omega

/-- **The inequality version** — the only direction the cost account needs: no covering
hypothesis, just pairwise disjointness. -/
theorem card_partition_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F U : Finset E} {inp : ι → Finset E}
    (hFU : Disjoint F U)
    (hFi : ∀ i, Disjoint F (inp i))
    (hUi : ∀ i, Disjoint U (inp i))
    (hii : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι)) inp) :
    F.card + U.card + ∑ i, (inp i).card ≤ Fintype.card E := by
  have hUnion : Disjoint (F ∪ U) (Finset.univ.biUnion inp) := by
    rw [Finset.disjoint_biUnion_right]
    intro i _
    rw [Finset.disjoint_union_left]
    exact ⟨hFi i, hUi i⟩
  have h1 : (F ∪ U ∪ Finset.univ.biUnion inp).card
      = F.card + U.card + (Finset.univ.biUnion inp).card := by
    rw [Finset.card_union_of_disjoint hUnion, Finset.card_union_of_disjoint hFU]
  have h2 : (Finset.univ.biUnion inp).card = ∑ i, (inp i).card :=
    Finset.card_biUnion hii
  have hle : (F ∪ U ∪ Finset.univ.biUnion inp).card ≤ Fintype.card E := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ _)
  omega

/-- The certificate call's bookkeeping with `U` read as the paper's `U(F) = unsupp G F`
(always disjoint from `F`, `Filtering.disjoint_unsupp`). -/
theorem certificate_partition_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : Finset E} {inp : ι → Finset E}
    (hFi : ∀ i, Disjoint F (inp i))
    (hUi : ∀ i, Disjoint (unsupp G F) (inp i))
    (hii : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι)) inp) :
    F.card + (unsupp G F).card + ∑ i, (inp i).card ≤ Fintype.card E :=
  card_partition_le disjoint_unsupp hFi hUi hii

/-! ## §3.5's closing sum: `t²` rounds × `O(n + t√(mᵢn))` -/

/-- **The round-sum.**  A call runs `t²` rounds; round `i` spends at most `C·(n + t·√(mᵢn))`
comparisons on `mᵢ` edges, and `Σ mᵢ ≤ m`.  Then the call spends at most
`C·(t²n + t·√(t²mn))` comparisons outside the exact MSF calls.  Cauchy–Schwarz on
`Σ √(mᵢn)` is the only inequality of substance. -/
theorem round_budget_sum {t m n : ℕ} {C : ℝ} {budget : ℕ → ℝ} {mL : ℕ → ℕ}
    (hC : 0 ≤ C)
    (hsum : (∑ i ∈ Finset.range (t ^ 2), (mL i : ℝ)) ≤ (m : ℝ))
    (hbudget : ∀ i ∈ Finset.range (t ^ 2),
      budget i ≤ C * ((n : ℝ) + (t : ℝ) * Real.sqrt ((mL i : ℝ) * (n : ℝ)))) :
    (∑ i ∈ Finset.range (t ^ 2), budget i)
      ≤ C * ((t : ℝ) ^ 2 * (n : ℝ) +
          (t : ℝ) * Real.sqrt ((t : ℝ) ^ 2 * (m : ℝ) * (n : ℝ))) := by
  have hkey : (∑ i ∈ Finset.range (t ^ 2), Real.sqrt ((mL i : ℝ) * (n : ℝ)))
      ≤ Real.sqrt ((t : ℝ) ^ 2 * (m : ℝ) * (n : ℝ)) := by
    have h1 := Real.sum_sqrt_mul_sqrt_le (Finset.range (t ^ 2))
      (f := fun i => (mL i : ℝ)) (g := fun _ => (n : ℝ))
      (fun i => Nat.cast_nonneg _) (fun i => Nat.cast_nonneg _)
    have h3 : (∑ _i ∈ Finset.range (t ^ 2), (n : ℝ)) = (t : ℝ) ^ 2 * (n : ℝ) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow]
    have h4 : Real.sqrt ((∑ i ∈ Finset.range (t ^ 2), (mL i : ℝ)) *
          ((t : ℝ) ^ 2 * (n : ℝ)))
        ≤ Real.sqrt ((t : ℝ) ^ 2 * (m : ℝ) * (n : ℝ)) := by
      refine Real.sqrt_le_sqrt ?_
      have := mul_le_mul_of_nonneg_right hsum
        (show (0 : ℝ) ≤ (t : ℝ) ^ 2 * (n : ℝ) by positivity)
      nlinarith
    calc (∑ i ∈ Finset.range (t ^ 2), Real.sqrt ((mL i : ℝ) * (n : ℝ)))
        = ∑ i ∈ Finset.range (t ^ 2),
            Real.sqrt ((mL i : ℝ)) * Real.sqrt ((n : ℝ)) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Real.sqrt_mul (Nat.cast_nonneg _)]
      _ = ∑ i ∈ Finset.range (t ^ 2),
            Real.sqrt ((mL i : ℝ)) * Real.sqrt ((n : ℝ)) := rfl
      _ ≤ Real.sqrt ((∑ i ∈ Finset.range (t ^ 2), (mL i : ℝ)) *
            ((t : ℝ) ^ 2 * (n : ℝ))) := by
          rw [Real.sqrt_mul (show (0 : ℝ) ≤ ∑ i ∈ Finset.range (t ^ 2), (mL i : ℝ)
            by positivity)]
          rw [h3] at h1
          exact h1
      _ ≤ Real.sqrt ((t : ℝ) ^ 2 * (m : ℝ) * (n : ℝ)) := h4
  have hmain : (∑ i ∈ Finset.range (t ^ 2),
        ((n : ℝ) + (t : ℝ) * Real.sqrt ((mL i : ℝ) * (n : ℝ))))
      ≤ (t : ℝ) ^ 2 * (n : ℝ) +
          (t : ℝ) * Real.sqrt ((t : ℝ) ^ 2 * (m : ℝ) * (n : ℝ)) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.mul_sum]
    have hcard : (((t ^ 2 : ℕ) : ℝ)) = (t : ℝ) ^ 2 := by
      rw [Nat.cast_pow]
    have := mul_le_mul_of_nonneg_left hkey (Nat.cast_nonneg t)
    nlinarith
  calc (∑ i ∈ Finset.range (t ^ 2), budget i)
      ≤ ∑ i ∈ Finset.range (t ^ 2),
          C * ((n : ℝ) + (t : ℝ) * Real.sqrt ((mL i : ℝ) * (n : ℝ))) :=
        Finset.sum_le_sum hbudget
    _ = C * ∑ i ∈ Finset.range (t ^ 2),
          ((n : ℝ) + (t : ℝ) * Real.sqrt ((mL i : ℝ) * (n : ℝ))) := by
        rw [Finset.mul_sum]
    _ ≤ C * ((t : ℝ) ^ 2 * (n : ℝ) +
          (t : ℝ) * Real.sqrt ((t : ℝ) ^ 2 * (m : ℝ) * (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hmain hC

/-- **The paper's form of the round-sum**: `t·√(t²mn) = t²·√(mn)`, so the per-call budget is
`C·t²·(n + √(mn))` — literally the `Σᵢ O(n + t√(mᵢn)) = O(t²n + t²√(mn))` of §3.5. -/
theorem round_budget_sum_paper {t m n : ℕ} {C : ℝ} {budget : ℕ → ℝ} {mL : ℕ → ℕ}
    (hC : 0 ≤ C)
    (hsum : (∑ i ∈ Finset.range (t ^ 2), (mL i : ℝ)) ≤ (m : ℝ))
    (hbudget : ∀ i ∈ Finset.range (t ^ 2),
      budget i ≤ C * ((n : ℝ) + (t : ℝ) * Real.sqrt ((mL i : ℝ) * (n : ℝ)))) :
    (∑ i ∈ Finset.range (t ^ 2), budget i)
      ≤ C * ((t : ℝ) ^ 2 * ((n : ℝ) + Real.sqrt ((m : ℝ) * (n : ℝ)))) := by
  refine le_trans (round_budget_sum hC hsum hbudget) ?_
  have hsq : (t : ℝ) * Real.sqrt ((t : ℝ) ^ 2 * (m : ℝ) * (n : ℝ))
      = (t : ℝ) ^ 2 * Real.sqrt ((m : ℝ) * (n : ℝ)) := by
    rw [show (t : ℝ) ^ 2 * (m : ℝ) * (n : ℝ) = (t : ℝ) ^ 2 * ((m : ℝ) * (n : ℝ)) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (Nat.cast_nonneg t)]
    ring
  rw [hsq]
  ring_nf
  rfl

end DLMST