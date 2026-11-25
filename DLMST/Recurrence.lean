import Mathlib

/-!
# The recursion that closes Theorem 4.1

`Certificate` returns a forest `F`, a rejected set, and subinstances `E₁ … E_ℓ` with

    |F| + |U(F)| + Σ |E_i|  ≤  ε·m + C_ε·√(m·n'),

and each `E_i` is handled by the same routine.  The paper first spends `k` Borůvka phases so that
`n' ≤ n/2^k ≤ 2m/2^k`, turning `√(m·n')` into `m·2^{(1-k)/2}`; then `ε = 1/8` with `k` large gives
`m/8 + 3m/8 = m/2`.  Two things can go wrong there and both are checked:

* the arithmetic of the slack term (`Bookkeeping.lean`);
* that `T(m) ≤ Σ T(m_i) + O(m)` with `Σ m_i ≤ m/2` really solves to `O(m)` (this file).
-/

namespace DLMST

/-- Sum monotonicity for lists, over ℝ. -/
private lemma list_sum_le_sum {l : List ℕ} {f g : ℕ → ℝ}
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
      rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
      refine add_le_add (h a (by simp))
        (ih fun x hx => h x (by simp [hx]))

/-- Every entry of a list of naturals is at most the list's sum. -/
private lemma le_sum : ∀ (l : List ℕ) (x : ℕ), x ∈ l → x ≤ l.sum := by
  intro l
  induction l with
  | nil => intro x hx; cases hx
  | cons a as ih =>
      intro x hx
      rw [List.sum_cons]
      simp [List.mem_cons] at hx
      rcases hx with rfl | hx
      · omega
      · have := ih x hx
        omega

/-- **Master form.**  If every instance of size `m` splits into subinstances `sub m` whose sizes
sum to at most `m/2`, at cost `c·m`, then the total cost is at most `2·c·m`.

This is exactly the shape of the paper's final recurrence `T(m) ≤ Σᵢ T(mᵢ) + O(m)` with
`Σᵢ mᵢ ≤ m/2`, from which they read off `T(m) = O(m)`.  Note the role of `hT0`: the induction needs
a base at `m = 0` that does not come from the recurrence itself, since `sub 0` may be non-empty —
harmless for MST (no edges, no comparisons), but the paper does not state it. -/
theorem recurrence_linear
    (T : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c) (sub : ℕ → List ℕ)
    (hT0 : T 0 ≤ 0)
    (hrec : ∀ m, T m ≤ ((sub m).map T).sum + c * m)
    (hsum : ∀ m, (sub m).sum ≤ m / 2) :
    ∀ m, T m ≤ 2 * c * m := by
  classical
  -- `Σ x ≤ m/2` with `m ≥ 1` forces every subinstance to be strictly smaller.  This is precisely
  -- where a slack term that is merely `O(m)` rather than `o(m)` would break the argument, and why
  -- the paper has to run Borůvka phases first — see `Bookkeeping.lean`.
  have hbdd : ∀ m, 1 ≤ m → ∀ x ∈ sub m, x < m := by
    intro m hm x hx
    have hx' : x ≤ (sub m).sum := le_sum _ _ hx
    have := hsum m
    omega
  have main : ∀ B m, m ≤ B → T m ≤ 2 * c * m := by
    intro B
    induction B with
    | zero =>
        intro m hm
        have h0 : m = 0 := by omega
        subst h0
        simpa using hT0
    | succ B ih =>
        intro m hm
        rcases m.eq_zero_or_pos with rfl | hpos
        · simpa using hT0
        · have hlt : ∀ x ∈ sub m, x < m := hbdd m hpos
          have hboundT : ((sub m).map T).sum ≤ ((sub m).map (fun x : ℕ => 2 * c * (x : ℝ))).sum := by
            refine list_sum_le_sum fun x hx => ih x ?_
            have hxm : x < m := hlt x hx
            omega
          have hsumx : ((sub m).map (fun x : ℕ => (x : ℝ))).sum ≤ (m : ℝ) / 2 := by
            have hcast : ((sub m).map (fun x : ℕ => (x : ℝ))).sum = ((sub m).sum : ℝ) := by
              induction sub m with
              | nil => rfl
              | cons a as ih' => rw [List.map_cons, List.sum_cons, ih', List.sum_cons]; simp
            rw [hcast]
            have h1 : ((sub m).sum : ℝ) ≤ (m / 2 : ℕ) := by exact_mod_cast hsum m
            have h2 : (2 : ℝ) * (m / 2 : ℕ) ≤ (m : ℝ) := by exact_mod_cast Nat.mul_div_le m 2
            linarith
          have hfac : ((sub m).map (fun x : ℕ => (2 : ℝ) * c * (x : ℝ))).sum
              = (2 : ℝ) * c * ((sub m).map (fun x : ℕ => (x : ℝ))).sum := by
            induction sub m with
            | nil => simp
            | cons a as ih' => simp only [List.map_cons, List.sum_cons, ih']; ring
          have hmul : (2 : ℝ) * c * ((sub m).map (fun x : ℕ => (x : ℝ))).sum
              ≤ (2 : ℝ) * c * ((m : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left hsumx (by linarith)
          have hhalf : (2 : ℝ) * c * ((m : ℝ) / 2) = c * m := by ring
          have hrec' : T m ≤ ((sub m).map T).sum + c * m := hrec m
          linarith
  intro m
  exact main m m (le_refl m)

/-- The paper's bound, read off the master form: linear worst-case comparison count. -/
theorem mst_linear_bound
    (T : ℕ → ℝ) (c : ℝ) (hc : 0 < c) (sub : ℕ → List ℕ)
    (hT0 : T 0 ≤ 0)
    (hrec : ∀ m, T m ≤ ((sub m).map T).sum + c * m)
    (hsum : ∀ m, (sub m).sum ≤ m / 2) :
    ∃ c' : ℝ, 0 ≤ c' ∧ ∀ m, T m ≤ c' * m :=
  ⟨2 * c, by linarith, recurrence_linear T c hc.le sub hT0 hrec hsum⟩

end DLMST
