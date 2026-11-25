import DLMST.HistoryCount

/-!
# The paper's two constants, sharp: `log(1+x) ≤ √x` and Fact 2.1's `2√(mn)`

`Selection.log_one_add_le_two_sqrt` proves `log(1+x) ≤ 2√x`, and `HistoryCount.log_choose_le`
restates Fact 2.1 with constant `4` as a consequence.  Both losses are only a factor `2`; the paper's
constants need nothing beyond a quadratic lower bound for `exp`, which this file supplies.

* `log_one_add_le_sqrt`: at `t = √x`, the five-term Taylor sum gives `1 + t² ≤ exp t`, hence
  `log(1+x) ≤ t = √x`.  (The elementary route used in `Selection.lean` would need the
  `exp`-comparison this replaces.)
* `log_choose_le_two`: Fact 2.1 verbatim, `log C(a+b,b) ≤ 2√(ab)`.  This is
  `HistoryCount.log_choose_le`'s product form `C(a+b,b) = ∏_{i<b} (a+i+1)/(i+1)` with the sharp term
  bound `log(1 + a/i) ≤ √(a/i)` and the same telescoping `Σ_{i<b} 1/√(i+1) ≤ 2√b`.

The downstream `O(t²√(mn))` statements keep the coarser constants they were proved with — a constant
factor changes no `O`-statement, and rerunning `Section36`'s numerical chain is not needed for that.
What those constants were blocking was the *faithfulness* of Fact 2.1 itself, which is what this file
settles: the paper's Fact 2.1 now holds at its stated constant.
-/

namespace DLMST

/-- **`log (1 + x) ≤ √x`** for `x ≥ 0`, the bound the paper quotes after Lemma 3.3. -/
theorem log_one_add_le_sqrt {x : ℝ} (hx : 0 ≤ x) : Real.log (1 + x) ≤ Real.sqrt x := by
  set t := Real.sqrt x with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg x
  have hx2 : x = t ^ 2 := (Real.sq_sqrt hx).symm
  have hsum : (∑ i ∈ Finset.range 5, t ^ i / (Nat.factorial i : ℝ)) =
      1 + t + t ^ 2 / 2 + t ^ 3 / 6 + t ^ 4 / 24 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  have hmid : 1 + t ^ 2 ≤ ∑ i ∈ Finset.range 5, t ^ i / (Nat.factorial i : ℝ) := by
    rw [hsum]
    have hnon : 0 ≤ t * (t ^ 3 + 4 * t ^ 2 - 12 * t + 24) := by
      have hinner : 0 ≤ t ^ 3 + 4 * t ^ 2 - 12 * t + 24 := by
        nlinarith [pow_nonneg ht0 3, sq_nonneg (t - 3 / 2)]
      exact mul_nonneg ht0 hinner
    nlinarith [hnon]
  have hexp : 1 + x ≤ Real.exp t := by
    rw [hx2]
    linarith [Real.sum_le_exp_of_nonneg ht0 5]
  calc Real.log (1 + x) ≤ Real.log (Real.exp t) :=
        Real.log_le_log (by linarith) hexp
    _ = t := Real.log_exp t
    _ = Real.sqrt x := rfl

/-- **Fact 2.1 at the paper's constant**: `log C(a+b, b) ≤ 2√(ab)`. -/
lemma log_choose_le_two (a b : ℕ) :
    Real.log ((a + b).choose b : ℝ) ≤ 2 * Real.sqrt ((a : ℝ) * (b : ℝ)) := by
  rw [choose_eq_prod_range]
  have hne : ∀ i ∈ Finset.range b, ((a + i + 1 : ℕ) : ℝ) / ((i + 1 : ℕ) : ℝ) ≠ 0 := by
    intro i _
    positivity
  rw [Real.log_prod hne]
  have hterm : ∀ i ∈ Finset.range b,
      Real.log (((a + i + 1 : ℕ) : ℝ) / ((i + 1 : ℕ) : ℝ)) ≤
        Real.sqrt (a : ℝ) * (1 / Real.sqrt ((i + 1 : ℕ) : ℝ)) := by
    intro i _
    have hpos : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
    have h1 : ((a + i + 1 : ℕ) : ℝ) / ((i + 1 : ℕ) : ℝ) =
        1 + (a : ℝ) / ((i + 1 : ℕ) : ℝ) := by
      push_cast
      field_simp
      ring
    have h2 : Real.sqrt ((a : ℝ) / ((i + 1 : ℕ) : ℝ)) =
        Real.sqrt (a : ℝ) * (1 / Real.sqrt ((i + 1 : ℕ) : ℝ)) := by
      rw [Real.sqrt_div (by positivity), mul_one_div]
    rw [h1, ← h2]
    exact log_one_add_le_sqrt (by positivity)
  calc ∑ i ∈ Finset.range b, Real.log (((a + i + 1 : ℕ) : ℝ) / ((i + 1 : ℕ) : ℝ))
      ≤ ∑ i ∈ Finset.range b, Real.sqrt (a : ℝ) * (1 / Real.sqrt ((i + 1 : ℕ) : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = Real.sqrt (a : ℝ) * ∑ i ∈ Finset.range b, 1 / Real.sqrt ((i + 1 : ℕ) : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ Real.sqrt (a : ℝ) * (2 * Real.sqrt (b : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_range_one_div_sqrt_succ_le b) (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt ((a : ℝ) * (b : ℝ)) := by
        rw [Real.sqrt_mul (by positivity)]
        ring

end DLMST