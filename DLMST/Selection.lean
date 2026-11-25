import Mathlib

/-!
# §3.2–§3.3, Lemma 3.3: picking the `k` lightest representatives

Lemma 3.3 claims that from `m` edges partitioned into groups, the `k` lightest group representatives
(the *minimum weight admissible edge* of a group) cost only `O(k log(m+1))` successful admissibility
tests plus `O(m)` weight comparisons.  The procedure is a median split, and this file checks the two
combinatorics facts the recursion rests on, together with the arithmetic of the cost bound that §3.2
performs when it sums the per-vertex estimates.

* `IsRep.of_lower` / `IsRep.mono` — why recursing is sound.  Because the lower half `L` is an
  *initial segment* of the tie-broken order, a group that has an admissible edge in `L` has its
  representative in `L` (nothing outside `L` can beat it), and deleting the edges of the groups that
  already passed cannot move the remaining representatives.
* `reps_below_of_not_lower` — the counting form of the same fact, and the one the paper actually uses:
  if `k` groups pass inside `L`, every representative outside `L` is beaten by at least `k`
  representatives, so the `k` lightest ones are all inside `L`.
* `log_one_add_le_two_sqrt`, `test_budget`, `sum_fiber_card`, `sum_degree` — the §3.2 summation
  `Σᵥ O(k log(deg(v)+1)) ≤ O(r² √(n|B|))`: the per-vertex logarithmic bound, Cauchy–Schwarz, and the
  handshake identity `Σᵥ deg(v) = 2|B|` that turns the degrees into `|B|`.

Two things the paper does not spell out and this file therefore states explicitly.  First, the split
must be an initial segment of the *tie-broken* order, not merely of weight: with equal weights, a
group's lightest admissible edge could sit in either half, and the conclusion fails; the paper's
"using the fixed edge order to break weight ties" is exactly this hypothesis (`hlow` below).
Second, `log(x+1) ≤ √x` (the bound quoted after Lemma 3.3) is true but needs a polynomial lower bound
for `exp`; only the weaker `log(1+x) ≤ 2√x` is proved here, which changes no `O`-count.

What is *not* formalised here is the cost of the recursion itself: the `O(m)` comparisons per level,
the fact that the halves really do shrink by a factor of two (`[BFP+72]` median selection), and the
accounting that the quota-1 searches run on disjoint inputs.  Only the *summed* bound that §3.2
derives from them is checked.  Nor is the connection to the batch procedure: that the groups really
are the neighbour classes of a vertex in a batch, and that a passed test is what `IsRep` records.
-/

namespace DLMST

/-! ## The representative, and why the recursion into the lower half is sound -/

variable {E ι : Type*} [LinearOrder E]

/-- **Representative of a group** (§3.2): the lightest admissible edge of `U` in `e`'s group.  "Lightest"
is read in the order with which the median split breaks weight ties, so a group has at most one. -/
def IsRep (grp : E → ι) (adm : E → Prop) (U : Finset E) (e : E) : Prop :=
  e ∈ U ∧ adm e ∧ ∀ f ∈ U, grp f = grp e → adm f → e ≤ f

variable {grp : E → ι} {adm : E → Prop}

theorem IsRep.unique (he : IsRep grp adm U e) (hf : IsRep grp adm U f)
    (hgrp : grp e = grp f) : e = f :=
  le_antisymm (he.2.2 f hf.1 hgrp.symm hf.2.1) (hf.2.2 e he.1 hgrp he.2.1)

/-- A group that has an admissible edge in the lower half has its representative there: an edge of
`U \ L` is heavier than every edge of `L`, so it cannot be the lightest admissible one. -/
theorem IsRep.of_lower {U L : Finset E} (hL : L ⊆ U)
    (hlow : ∀ e ∈ L, ∀ f ∈ U, f ∉ L → e < f) (he : IsRep grp adm U e)
    (hmeet : ∃ f ∈ L, grp f = grp e ∧ adm f) : IsRep grp adm L e := by
  obtain ⟨f, hfL, hfg, hfa⟩ := hmeet
  refine ⟨by
    by_contra hne
    exact lt_irrefl f (lt_of_lt_of_le (hlow f hfL e he.1 hne) (he.2.2 f (hL hfL) hfg hfa)),
    he.2.1, fun g hgL hgg hga => he.2.2 g (hL hgL) hgg hga⟩

/-- Removing the edges of the other groups does not move a representative: as long as every admissible
`U`-edge of `e`'s own group survives in `V`, `e` is still the lightest one in `V`.  This is what lets
the recursion continue on `H` with the passed groups' edges deleted. -/
theorem IsRep.mono {U V : Finset E} (hVU : V ⊆ U) (e : E)
    (hsame : ∀ f ∈ U, grp f = grp e → adm f → f ∈ V) (he : IsRep grp adm U e) :
    IsRep grp adm V e :=
  ⟨hsame e he.1 rfl he.2.1, he.2.1, fun f hfV hfg hfa => he.2.2 f (hVU hfV) hfg hfa⟩

/-- **§3.3's justification of the quota** (`bad_card_le`'s analogue for the selection procedure): if at
least `k` groups have an admissible edge in `L`, then any representative of `U` outside `L` is beaten
by at least `k` representatives of `U`.  So the `k` lightest representatives — the ones the procedure
must return — all lie in `L`, and recursing on `L` with quota `k` loses nothing. -/
theorem reps_below_of_not_lower {U L R R' : Finset E} (hL : L ⊆ U)
    (hlow : ∀ e ∈ L, ∀ f ∈ U, f ∉ L → e < f) {k : ℕ}
    (hR : ∀ e, e ∈ R ↔ IsRep grp adm U e) (hR' : ∀ e, e ∈ R' ↔ IsRep grp adm L e)
    (hk : k ≤ R'.card) (e : E) (he : IsRep grp adm U e) (hne : e ∉ L) :
    k ≤ (R.filter fun x => x < e).card := by
  classical
  refine Nat.le_trans hk (Finset.card_le_card (Finset.subset_iff.mpr fun x hx => ?_))
  obtain ⟨hxL, hxa, hxmin⟩ := (hR' x).mp hx
  refine Finset.mem_filter.mpr ⟨(hR x).mpr ⟨hL hxL, hxa, fun f hfU hgf hfa => ?_⟩,
    hlow x hxL e he.1 hne⟩
  by_cases hfL : f ∈ L
  · exact hxmin f hfL hgf hfa
  · exact (hlow x hxL f hfU hfL).le

/-! ## Summing the per-vertex test budgets -/

/-- `log (1 + x) ≤ 2 √x` for `x ≥ 0`.  The paper quotes `log(x+1) ≤ √x`; the constant is immaterial for
the `O`-bound, and the sharper statement needs more about `exp` than is developed here. -/
theorem log_one_add_le_two_sqrt {x : ℝ} (hx : 0 ≤ x) : Real.log (1 + x) ≤ 2 * Real.sqrt x := by
  have hs : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  by_cases h : x ≤ 1
  · have h1 : Real.log (1 + x) ≤ x := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + x by linarith)
      linarith
    have h2 : x ≤ Real.sqrt x := (Real.le_sqrt hx hx).mpr (by nlinarith)
    nlinarith
  · have hgt : 1 ≤ x := by linarith
    have h0 : (0 : ℝ) < x := by linarith
    have h2 : Real.log (1 + x) ≤ Real.log (2 * x) :=
      Real.log_le_log (by linarith) (by nlinarith)
    have h3 : Real.log (2 * x) = Real.log 2 + Real.log x :=
      Real.log_mul (by norm_num) (by linarith)
    have h4 : Real.log 2 ≤ (1 : ℝ) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    have h5 : Real.log x ≤ 2 * (Real.sqrt x - 1) := by
      have hlog : Real.log x = 2 * Real.log (Real.sqrt x) := by
        calc Real.log x = 2 * (Real.log x / 2) := by ring
          _ = 2 * Real.log (Real.sqrt x) := by rw [Real.log_sqrt hx]
      have hs1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
        Real.log_le_sub_one_of_pos ((Real.sqrt_pos.mpr h0))
      linarith
    nlinarith

/-- The same bound in the orientation the degrees are written in. -/
theorem log_add_one_le_two_sqrt {x : ℝ} (hx : 0 ≤ x) : Real.log (x + 1) ≤ 2 * Real.sqrt x := by
  have hkey := log_one_add_le_two_sqrt hx
  rwa [add_comm]

/-- **§3.2's summed test budget**: Cauchy–Schwarz turns `Σᵥ 2k √(deg v)` into `2k √(n Σᵥ deg v)`. -/
theorem test_budget {α : Type*} [Fintype α] (d : α → ℕ) (k : ℕ) :
    (∑ v : α, (k : ℝ) * Real.log ((d v : ℝ) + 1)) ≤
      2 * (k : ℝ) * Real.sqrt ((Fintype.card α : ℝ) * ∑ v : α, (d v : ℝ)) := by
  classical
  have hCS : (∑ v : α, Real.sqrt (d v : ℝ)) ≤
      Real.sqrt ((Fintype.card α : ℝ) * ∑ v : α, (d v : ℝ)) := by
    refine (Real.le_sqrt (Finset.sum_nonneg fun v _ => Real.sqrt_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun v _ => Nat.cast_nonneg _))).mpr ?_
    have hsq := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset α))
      (f := fun v => Real.sqrt (d v : ℝ))
    have hcard : ((Finset.univ : Finset α).card : ℝ) = (Fintype.card α : ℝ) := by
      rw [Finset.card_univ]
    calc (∑ v : α, Real.sqrt (d v : ℝ)) ^ 2
        ≤ ((Finset.univ : Finset α).card : ℝ) * ∑ v : α, (Real.sqrt (d v : ℝ)) ^ 2 := by
          convert hsq using 1
      _ ≤ (Fintype.card α : ℝ) * ∑ v : α, (d v : ℝ) := by
          rw [hcard]
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          refine le_of_eq (Finset.sum_congr rfl (fun v _ => Real.sq_sqrt (Nat.cast_nonneg _)))
  have hgroup : (∑ v : α, (k : ℝ) * (2 * Real.sqrt (d v : ℝ)))
      = 2 * (k : ℝ) * ∑ v : α, Real.sqrt (d v : ℝ) := by
    have h1 : (∑ v : α, (k : ℝ) * (2 * Real.sqrt (d v : ℝ)))
        = ∑ v : α, Real.sqrt (d v : ℝ) * (2 * (k : ℝ)) :=
      Finset.sum_congr rfl (fun v _ => by ring)
    rw [h1, ← Finset.sum_mul (Finset.univ : Finset α) (fun v => Real.sqrt (d v : ℝ))
      (2 * (k : ℝ))]
    ring
  refine calc (∑ v : α, (k : ℝ) * Real.log ((d v : ℝ) + 1))
      ≤ ∑ v : α, (k : ℝ) * (2 * Real.sqrt (d v : ℝ)) :=
        Finset.sum_le_sum (fun v _ =>
          mul_le_mul_of_nonneg_left (log_add_one_le_two_sqrt (Nat.cast_nonneg _))
            (Nat.cast_nonneg _))
    _ = 2 * (k : ℝ) * ∑ v : α, Real.sqrt (d v : ℝ) := hgroup
    _ ≤ 2 * (k : ℝ) * Real.sqrt ((Fintype.card α : ℝ) * ∑ v : α, (d v : ℝ)) :=
        mul_le_mul_of_nonneg_left hCS (by positivity)

/-- Hand-shaking over one endpoint map: summing, over all vertices, the number of edges sent to that
vertex counts every edge once. -/
theorem sum_fiber_card {α V : Type*} [Fintype V] [DecidableEq V] (f : α → V) (B : Finset α) :
    ∑ v : V, (B.filter fun e => f e = v).card = B.card := by
  classical
  have h1 : (∑ v : V, (B.filter fun e => f e = v).card)
      = Finset.sum (Finset.univ : Finset V)
        (fun v => Finset.sum B (fun e => if f e = v then (1 : ℕ) else 0)) := by
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have h2 : Finset.sum (Finset.univ : Finset V)
        (fun v => Finset.sum B (fun e => if f e = v then (1 : ℕ) else 0))
      = Finset.sum B (fun e => Finset.sum (Finset.univ : Finset V)
        (fun v => if f e = v then (1 : ℕ) else 0)) := Finset.sum_comm
  have h3 : Finset.sum B (fun e => Finset.sum (Finset.univ : Finset V)
        (fun v => if f e = v then (1 : ℕ) else 0))
      = Finset.sum B (fun _ => (1 : ℕ)) := by
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [Finset.sum_ite_eq]
    simp
  rw [h1, h2, h3, Finset.card_eq_sum_ones]

/-- **`Σᵥ deg_B(v) = 2|B|`** (§3.2, "the total number of comparisons is bounded by
`Σᵥ O(deg_B(v)) = O(|B|)`").  An edge is counted at both of its endpoints, loops included. -/
theorem sum_degree {V E : Type*} [Fintype V] [DecidableEq V] (src dst : E → V) (B : Finset E) :
    ∑ v : V, ((B.filter fun e => src e = v).card + (B.filter fun e => dst e = v).card)
      = 2 * B.card := by
  classical
  rw [Finset.sum_add_distrib, sum_fiber_card src, sum_fiber_card dst]
  omega

/-- **The batch's test count** (§3.2, the display after Lemma 3.3): with quota `k` at every vertex and
`D` the total degree in the batch, the number of successful admissibility tests is at most
`2k √(n · 2D)`; taking `k = r²` and `D = |B|` is the paper's `O(r² √(n|B|))`. -/
theorem tests_le_sqrt {V : Type*} [Fintype V] [DecidableEq V] (d : V → ℕ) (k D : ℕ)
    (hdeg : ∑ v : V, (d v : ℝ) = (D : ℝ)) :
    (∑ v : V, (k : ℝ) * Real.log ((d v : ℝ) + 1)) ≤
      2 * (k : ℝ) * Real.sqrt ((Fintype.card V : ℝ) * (D : ℝ)) := by
  rw [← hdeg]
  exact test_budget d k

end DLMST
