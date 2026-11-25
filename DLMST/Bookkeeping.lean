import Mathlib

/-!
# The `√(m·n')` slack term

The certificate procedure (their Lemma 1.2) delivers, for each fixed `ε > 0`, a forest `F` and
subinstances `E₁ … E_ℓ` with

    |F| + |U(F)| + Σⱼ |E_j|  ≤  ε·m + C_ε·√(m·n).                                    (∗)

Because `n ≤ 2m`, the right hand side of (∗) is only `O(m)` — **not** `o(m)` — so (∗) by itself
cannot shrink the recursion.  The paper's fix is to run `k` Borůvka phases first, halving the
vertex count each time (`n' ≤ n/2^k`), and to choose `k` with `C_{1/8}·2^{(1-k)/2} ≤ 3/8`, turning
(∗) into `≤ m/8 + 3m/8 = m/2`.

This is the one place where a slipped constant would silently destroy the linear bound, so it is
worth having a machine agree with it.  Checked below: the vertex-halving arithmetic
(`sqrt_shrink`), that a suitable phase count exists (`exists_phase`), and the final bookkeeping
(`closure`).  Note that `sqrt_shrink` bounds `√(m·2m/2^k)` by `2m/2^j` for `k = 2j`, which is
slightly looser than the paper's `m·2^{(1-k)/2}` but enough for the recursion — the looseness is
absorbed by the freedom in choosing `k`.
-/

namespace DLMST

private lemma one_le_two_pow (j : ℕ) : (1 : ℝ) ≤ (2 : ℝ) ^ j := by
  induction j with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ]
      linarith [ih]

/-- `j ≤ 2^j`, over the reals. -/
private lemma nat_le_two_pow (j : ℕ) : (j : ℝ) ≤ (2 : ℝ) ^ j := by
  induction j with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ]
      push_cast
      linarith [ih, one_le_two_pow k]

/-- `n ≤ 2m`, and `2j` Borůvka phases replace `n` by `n/2^{2j}`, so the `√(m·n')` slack of (∗) is
at most `2m/2^j`. -/
theorem sqrt_shrink (m j : ℕ) :
    Real.sqrt ((m : ℝ) * (2 * (m : ℝ) / (2 : ℝ) ^ (2 * j))) ≤ 2 * (m : ℝ) / (2 : ℝ) ^ j := by
  classical
  set A : ℝ := (2 : ℝ) ^ j with hA
  have hpow : (2 : ℝ) ^ (2 * j) = A ^ 2 := by
    rw [show (2 : ℝ) ^ (2 * j) = (2 : ℝ) ^ (j + j) by rw [Nat.two_mul j], pow_add]
    ring
  have hA0 : (0 : ℝ) < A := by
    rw [hA]
    exact pow_pos (by norm_num) j
  rw [hpow, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 : (m : ℝ) * (2 * (m : ℝ) / A ^ 2) = 2 * (m : ℝ) ^ 2 / A ^ 2 := by ring
  have h2 : (2 * (m : ℝ) / A) ^ 2 = 4 * (m : ℝ) ^ 2 / A ^ 2 := by
    rw [pow_two]
    ring
  rw [h1, h2]
  have hM : (0 : ℝ) ≤ (m : ℝ) ^ 2 := by positivity
  refine (div_le_div_iff₀ (by positivity) (by positivity)).2 ?_
  exact mul_le_mul_of_nonneg_right (by linarith [hM]) (by positivity)

/-- A phase count large enough to absorb any constant `C_ε` — the `k` whose existence the paper
asserts without comment. -/
theorem exists_phase (C : ℝ) : ∃ j : ℕ, C * 2 / (2 : ℝ) ^ j ≤ 3 / 8 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : ℕ, ((16 : ℝ) / 3 * C + 1) ≤ (j : ℝ) := exists_nat_ge _
  have hp : (j : ℝ) ≤ (2 : ℝ) ^ j := nat_le_two_pow j
  have h1 : (16 : ℝ) / 3 * C ≤ (2 : ℝ) ^ j := by linarith
  refine ⟨j, ?_⟩
  refine (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 8)).2 ?_
  linarith [h1]

/-- **The closing inequality.**  With `ε = 1/8` and `k = 2j` Borůvka phases, the total size of the
recursive subinstances is at most `m/2` — which is what `Recurrence.recurrence_linear` consumes. -/
theorem closure (m : ℕ) (C : ℝ) (j : ℕ) (hC : 0 ≤ C) (hCj : C * 2 / (2 : ℝ) ^ j ≤ 3 / 8) :
    (m : ℝ) / 8 + C * Real.sqrt ((m : ℝ) * (2 * (m : ℝ) / (2 : ℝ) ^ (2 * j))) ≤ (m : ℝ) / 2 := by
  classical
  have h1 : C * Real.sqrt ((m : ℝ) * (2 * (m : ℝ) / (2 : ℝ) ^ (2 * j)))
      ≤ C * (2 * (m : ℝ) / (2 : ℝ) ^ j) :=
    mul_le_mul_of_nonneg_left (sqrt_shrink m j) hC
  have h2 : C * (2 * (m : ℝ) / (2 : ℝ) ^ j) = (C * 2 / (2 : ℝ) ^ j) * (m : ℝ) := by ring
  have h3 : (C * 2 / (2 : ℝ) ^ j) * (m : ℝ) ≤ (3 / 8 : ℝ) * (m : ℝ) :=
    mul_le_mul_of_nonneg_right hCj (Nat.cast_nonneg m)
  have h4 : (m : ℝ) / 8 + (3 / 8 : ℝ) * (m : ℝ) = (m : ℝ) / 2 := by ring
  linarith

/-- The two lemmas above combined: the recursion closes for every constant `C_ε`. -/
theorem closure_exists (m : ℕ) (C : ℝ) (hC : 0 < C) :
    ∃ j : ℕ,
      (m : ℝ) / 8 + C * Real.sqrt ((m : ℝ) * (2 * (m : ℝ) / (2 : ℝ) ^ (2 * j))) ≤ (m : ℝ) / 2 := by
  classical
  obtain ⟨j, hj⟩ := exists_phase C
  exact ⟨j, closure m C j (le_of_lt hC) hj⟩

end DLMST
