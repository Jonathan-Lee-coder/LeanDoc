import DLMST.Filtering
import DLMST.LightSpan
import DLMST.HistoryCount
import DLMST.ForestCard

/-!
# §3.6 "Putting the Pieces Together": the numerical end of Lemma 3.1 = Lemma 1.2

Lemma 3.1 (= 1.2) claims, for one invocation of the certificate procedure on `n` vertices, `m` edges:

> `|F| + |U(F)| + Σᵢ|Eᵢ| ≤ ε·m + C_ε·√(mn)`.

The paper's proof is §3.6, and it is pure bookkeeping on top of the §3 lemmas already checked here
(`Portals.portal_bound`, `Rounds.lemma37`, `History.lemma311`, `Sampling.claim312`, …):

1. **Portal shrink.**  One call runs `t` batch processings, each producing at most `2n/r` portals,
   and makes `t²` child calls; with `r = 8t³` the children together see only `n/4` vertices
   (`children_vertices_le`).  Hence level `d` has `n_d ≤ n/4^{d-1}` vertices, `m_d ≤ m` edges.
2. **Claim 3.13.**  `Σ_calls poly(d_c)(n_c + √(m_c n_c)) = O_γ(√(mn))` by Cauchy–Schwarz plus the
   geometric decay above.  We keep the paper's `poly(d) ≤ (γd³)²` and produce an explicit constant:
   the whole sum is at most `γ²·40000·√(mn)` (`claim_3_13`, using `sum_pow6_div_two_pow_le`).
3. **Errors.**  Per call `#errors ≤ O(t²√(m_c n_c)) + 4m_c/t_c` (Lemmas 3.10+3.11 give the first
   term, §3.5 the second), and `Σ_d 4m_d/(γd³) ≤ 8m/γ` because `Σ_{d≥1} 1/d³ ≤ 2`
   (`sum_inv_cube_le_two`).  Both the unsupported edges (Lemma 3.7) and the edges handed to child
   MSF calls pay this same price, which is where the paper's `16m/γ` comes from
   (`errors_levels`).
4. **Assembly.**  `|F| ≤ n ≤ √(2mn)` since a forest has at most `n-1` edges and there are no isolated
   vertices (`n ≤ 2m`), and `16m/γ ≤ εm` once `γ ≥ 16/ε`; so the display holds with
   `C_ε = √2 + 40000γ²` (`lemma12_bound`).

What is still *not* machine-checked here is what the paper itself defers: the comparison count of
the procedure (§3), the fact that every edge lands in exactly one of `F`, `U(F)`, a child instance
(the global reading of `Rounds.lemma37`), and `|F| ≤ n - 1` for a forest — all stated as explicit
hypotheses of the final theorem, in the same style as `Certificate.lean`.

`sanity`: the *existence* half of Lemma 3.1 is free — an MSF supports every edge
(`unsupp_msf_eq_empty`), so the real content of Lemma 3.1 is cheapness, not the inequality.
-/

namespace DLMST

set_option linter.unusedSectionVars false

open Classical

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] {G : WGraph V E}

/-! ## 1. The portal shrink and the vertex/edge decay across levels -/

/-- **§3.6, first paragraph.**  One call runs `t` batch processings, each producing at most `2n/r`
portals, and then `t²` child calls, each on at most that many vertices.  With `r = 8t³` the total
number of child vertices is `t² · (t · 2n/r) = n/4`. -/
theorem children_vertices_le {t n : ℕ} (ht : 0 < t) :
    (t : ℝ) ^ 2 * ((t : ℝ) * (2 * (n : ℝ) / (8 * (t : ℝ) ^ 3))) = (n : ℝ) / 4 := by
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  field_simp
  ring

/-- An edge is counted once: `m_d ≤ m` at every recursion level.  Stated so that the level data can
be planted in `claim_3_13`/`errors_levels` without repeating the paper's sentence. -/
theorem level_edges_le {D m : ℕ} {mL : ℕ → ℕ}
    (hm : ∀ i ∈ Finset.range D, mL i ≤ m) :
    ∀ i ∈ Finset.range D, (mL i : ℝ) ≤ (m : ℝ) :=
  fun i hi => by exact_mod_cast hm i hi

/-! ## 2. The two sums of §3.6 -/

/-- **`Σ_{d ≥ 1} 1/d³ ≤ 2`.**  The paper writes `Σ_{d≥1} 4m_d/(γd³) ≤ 8m/γ` and leaves the
convergence implicit; `1/d³ ≤ 1/d² ≤ 2/(d(d+1))`, and the last sum telescopes to `2`. -/
theorem sum_inv_cube_le_two (D : ℕ) :
    (∑ d ∈ Finset.range D, (1 : ℝ) / ((d : ℝ) + 1) ^ 3) ≤ 2 := by
  have hpoint : ∀ d ∈ Finset.range D, (1 : ℝ) / ((d : ℝ) + 1) ^ 3 ≤
      2 / (((d : ℝ) + 1) * ((d : ℝ) + 2)) := by
    intro d _
    have hA : (0 : ℝ) < (d : ℝ) + 1 := by positivity
    have hB : (0 : ℝ) < (d : ℝ) + 2 := by positivity
    rw [div_le_iff₀ (pow_pos hA 3)]
    have hprod : 2 / (((d : ℝ) + 1) * ((d : ℝ) + 2)) * ((d : ℝ) + 1) ^ 3 =
        2 * ((d : ℝ) + 1) ^ 2 / ((d : ℝ) + 2) := by
      field_simp
    rw [hprod, le_div_iff₀ hB]
    nlinarith [hA]
  have htel : (∑ d ∈ Finset.range D, 2 / (((d : ℝ) + 1) * ((d : ℝ) + 2))) =
      2 - 2 / ((D : ℝ) + 1) := by
    have h := Finset.sum_range_sub (fun k : ℕ => 2 / ((k : ℝ) + 1)) D
    have h' : (∑ i ∈ Finset.range D, -(2 / (((i : ℝ) + 1) + 1) - 2 / ((i : ℝ) + 1))) =
        -(2 / ((D : ℝ) + 1) - 2 / ((0 : ℝ) + 1)) := by
      have := congrArg Neg.neg h
      rw [← Finset.sum_neg_distrib] at this
      simpa [Nat.cast_add, Nat.cast_one] using this
    have hcongr : (∑ d ∈ Finset.range D, 2 / (((d : ℝ) + 1) * ((d : ℝ) + 2))) =
        ∑ i ∈ Finset.range D, -(2 / (((i : ℝ) + 1) + 1) - 2 / ((i : ℝ) + 1)) := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp
      ring
    rw [hcongr, h']
    ring
  calc (∑ d ∈ Finset.range D, (1 : ℝ) / ((d : ℝ) + 1) ^ 3)
      ≤ ∑ d ∈ Finset.range D, 2 / (((d : ℝ) + 1) * ((d : ℝ) + 2)) :=
        Finset.sum_le_sum hpoint
    _ = 2 - 2 / ((D : ℝ) + 1) := htel
    _ ≤ 2 := by
        have : (0 : ℝ) ≤ 2 / ((D : ℝ) + 1) := by positivity
        linarith

/-- The ratio behind Claim 3.13: from `d = 11` on, `f d = (d+1)^6/2^d` shrinks by at least `13/16`
per step, because `((d+2)/(d+1))^6 ≤ (13/12)^6 ≤ 13/8`. -/
theorem pow6_ratio {d : ℕ} (hd : 11 ≤ d) :
    ((d : ℝ) + 2) ^ 6 / 2 ^ (d + 1) ≤ (13 / 16) * (((d : ℝ) + 1) ^ 6 / 2 ^ d) := by
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hdR : (11 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hle : ((d : ℝ) + 2) / ((d : ℝ) + 1) ≤ 13 / 12 := by
    rw [div_le_iff₀ hd1]
    nlinarith
  have hpow : (((d : ℝ) + 2) / ((d : ℝ) + 1)) ^ 6 ≤ 13 / 8 := by
    calc (((d : ℝ) + 2) / ((d : ℝ) + 1)) ^ 6 ≤ (13 / 12) ^ 6 :=
      pow_le_pow_left₀ (by positivity) hle 6
      _ ≤ 13 / 8 := by norm_num
  have hpow' : ((d : ℝ) + 2) ^ 6 / ((d : ℝ) + 1) ^ 6 ≤ 13 / 8 := by
    rw [← div_pow]
    exact hpow
  have hkey : ((d : ℝ) + 2) ^ 6 ≤ (13 / 8) * ((d : ℝ) + 1) ^ 6 := by
    have h := mul_le_mul_of_nonneg_right hpow' (pow_nonneg hd1.le 6)
    rwa [div_mul_cancel₀ _ (pow_ne_zero 6 hd1.ne')] at h
  have hrhs : (13 / 16) * (((d : ℝ) + 1) ^ 6 / 2 ^ d) * 2 ^ (d + 1) =
      (13 / 8) * ((d : ℝ) + 1) ^ 6 := by
    rw [pow_succ]
    field_simp
    ring
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ (d + 1)), hrhs]
  exact hkey

/-- A geometric tail: if `g (k+1) ≤ c·g k` with `0 ≤ c < 1`, the total mass is at most `g 0/(1-c)`.
The invariant carried through the induction is `S n·(1-c) ≤ g 0·(1-c^n)`. -/
theorem geom_sum_le {g : ℕ → ℝ} {c : ℝ} (hg : 0 ≤ g 0) (hc : 0 ≤ c) (hc1 : c < 1)
    (hratio : ∀ k, g (k + 1) ≤ c * g k) (n : ℕ) :
    (∑ k ∈ Finset.range n, g k) ≤ g 0 / (1 - c) := by
  have hcpos : (0 : ℝ) < 1 - c := by linarith
  have hgn : ∀ k, g k ≤ g 0 * c ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc g (k + 1) ≤ c * g k := hratio k
          _ ≤ c * (g 0 * c ^ k) := mul_le_mul_of_nonneg_left ih hc
          _ = g 0 * c ^ (k + 1) := by rw [pow_succ]; ring
  have hinv : ∀ n, (∑ k ∈ Finset.range n, g k) * (1 - c) ≤ g 0 * (1 - c ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, add_mul]
        have h1 : g n * (1 - c) ≤ g 0 * c ^ n * (1 - c) :=
          mul_le_mul_of_nonneg_right (hgn n) hcpos.le
        have h2 : g 0 * (1 - c ^ n) + g 0 * c ^ n * (1 - c) = g 0 * (1 - c ^ (n + 1)) := by
          rw [pow_succ]
          ring
        linarith
  rw [le_div_iff₀ hcpos]
  have hcnonneg : (0 : ℝ) ≤ c ^ n := pow_nonneg hc n
  nlinarith [hinv n]

/-- **The convergence hidden in Claim 3.13:** `Σ_{d ≥ 1} d^6/2^{d-1} ≤ 40000` (with `d = i+1` the
summands are `(i+1)^6/2^i`).  On `d ≤ 11` every term is at most `2048`; from `d = 12` the ratio
estimate `pow6_ratio` and the geometric sum give `1458·16/3 ≤ 8000` for the whole tail. -/
theorem sum_pow6_div_two_pow_le (D : ℕ) :
    (∑ i ∈ Finset.range D, ((i : ℝ) + 1) ^ 6 / 2 ^ i) ≤ 40000 := by
  have hterm2048 : ∀ k ∈ Finset.range 11, ((k : ℝ) + 1) ^ 6 / 2 ^ k ≤ 2076 := by
    intro k hk
    have hk' : k < 11 := Finset.mem_range.mp hk
    interval_cases k <;> norm_num
  have hhead : (∑ k ∈ Finset.range 11, ((k : ℝ) + 1) ^ 6 / 2 ^ k) ≤ 22836 := by
    calc (∑ k ∈ Finset.range 11, ((k : ℝ) + 1) ^ 6 / 2 ^ k)
        ≤ ∑ k ∈ Finset.range 11, (2076 : ℝ) := Finset.sum_le_sum hterm2048
      _ = 22836 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  have htail : (∑ k ∈ Finset.Ico 11 D, ((k : ℝ) + 1) ^ 6 / 2 ^ k) ≤ 8000 := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hratio : ∀ k, (((11 + (k + 1) : ℕ) : ℝ) + 1) ^ 6 / 2 ^ (11 + (k + 1)) ≤
        (13 / 16) * ((((11 + k : ℕ) : ℝ) + 1) ^ 6 / 2 ^ (11 + k)) := by
      intro k
      have h := pow6_ratio (d := 11 + k) (by omega)
      convert h using 2
      push_cast
      ring
    have hg : (0 : ℝ) ≤ (((11 + 0 : ℕ) : ℝ) + 1) ^ 6 / 2 ^ (11 + 0) := by positivity
    have hbound := geom_sum_le (g := fun k => (((11 + k : ℕ) : ℝ) + 1) ^ 6 / 2 ^ (11 + k))
      (c := 13 / 16) hg (by norm_num) (by norm_num) hratio (D - 11)
    have hconst : ((((11 : ℕ) : ℝ) + 1) ^ 6 / 2 ^ (11 : ℕ)) / (1 - 13 / 16) ≤ 8000 := by
      norm_num
    calc (∑ k ∈ Finset.range (D - 11), (((11 + k : ℕ) : ℝ) + 1) ^ 6 / 2 ^ (11 + k))
        ≤ ((((11 + 0 : ℕ) : ℝ) + 1) ^ 6 / 2 ^ (11 + 0)) / (1 - 13 / 16) := hbound
      _ = ((((11 : ℕ) : ℝ) + 1) ^ 6 / 2 ^ (11 : ℕ)) / (1 - 13 / 16) := by norm_num
      _ ≤ 8000 := hconst
  rcases le_or_gt D 11 with hD | hD
  · have hsub : Finset.range D ⊆ Finset.range 11 := fun k hk =>
      Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) hD)
    have hmono : (∑ k ∈ Finset.range D, ((k : ℝ) + 1) ^ 6 / 2 ^ k) ≤
        ∑ k ∈ Finset.range 11, ((k : ℝ) + 1) ^ 6 / 2 ^ k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro k _ _
      positivity
    linarith
  · have hsplit := Finset.sum_range_add_sum_Ico
      (f := fun k => ((k : ℝ) + 1) ^ 6 / 2 ^ k) hD.le
    rw [← hsplit]
    linarith

/-! ## 3. Claim 3.13 and the per-level error account -/

/-- `√(4^i) = 2^i`, needed to split `√(m·n/4^i)` below (`Real.sqrt_pow` is absent here). -/
theorem sqrt_four_pow (i : ℕ) : Real.sqrt ((4 : ℝ) ^ i) = 2 ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]
      have : Real.sqrt (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [this]

/-- **Claim 3.13, with the paper's `poly(d) = (γd³)²` and an explicit constant.**  If level `i`
(standing for recursion depth `i+1`) has `n_i·4^i ≤ n` vertices and `m_i ≤ m` edges, then the
geometric-level contribution of all calls is at most `γ²·40000·√(mn)`. -/
theorem claim_3_13 {n m : ℕ} {γ : ℝ} (_hγ : 0 ≤ γ) {D : ℕ} {nL mL : ℕ → ℕ}
    (hn : ∀ i ∈ Finset.range D, (nL i : ℝ) * 4 ^ i ≤ (n : ℝ))
    (hm : ∀ i ∈ Finset.range D, (mL i : ℝ) ≤ (m : ℝ)) :
    (∑ i ∈ Finset.range D,
        (γ * ((i : ℝ) + 1) ^ 3) ^ 2 * Real.sqrt ((mL i : ℝ) * (nL i : ℝ)))
      ≤ γ ^ 2 * 40000 * Real.sqrt ((m : ℝ) * (n : ℝ)) := by
  have hterm : ∀ i ∈ Finset.range D,
      (γ * ((i : ℝ) + 1) ^ 3) ^ 2 * Real.sqrt ((mL i : ℝ) * (nL i : ℝ)) ≤
        (γ ^ 2 * (((i : ℝ) + 1) ^ 6 / 2 ^ i)) * Real.sqrt ((m : ℝ) * (n : ℝ)) := by
    intro i hi
    have h4 : (0 : ℝ) < 4 ^ i := by positivity
    have hn' : (nL i : ℝ) ≤ (n : ℝ) / 4 ^ i := by
      rw [le_div_iff₀ h4]
      linarith [hn i hi]
    have hprod : (mL i : ℝ) * (nL i : ℝ) ≤ (m : ℝ) * ((n : ℝ) / 4 ^ i) :=
      mul_le_mul (hm i hi) hn' (by positivity) (by positivity)
    have hsqrt := Real.sqrt_le_sqrt hprod
    have hsplit : Real.sqrt ((m : ℝ) * ((n : ℝ) / 4 ^ i)) =
        Real.sqrt ((m : ℝ) * (n : ℝ)) / 2 ^ i := by
      rw [mul_div_assoc', Real.sqrt_div (by positivity)]
      congr 1
      exact sqrt_four_pow i
    rw [hsplit] at hsqrt
    have hcoef : (γ * ((i : ℝ) + 1) ^ 3) ^ 2 = γ ^ 2 * ((i : ℝ) + 1) ^ 6 := by
      rw [mul_pow]
      congr 1
      ring
    calc (γ * ((i : ℝ) + 1) ^ 3) ^ 2 * Real.sqrt ((mL i : ℝ) * (nL i : ℝ))
        ≤ (γ * ((i : ℝ) + 1) ^ 3) ^ 2 *
            (Real.sqrt ((m : ℝ) * (n : ℝ)) / 2 ^ i) :=
          mul_le_mul_of_nonneg_left hsqrt (by positivity)
      _ = (γ ^ 2 * (((i : ℝ) + 1) ^ 6 / 2 ^ i)) * Real.sqrt ((m : ℝ) * (n : ℝ)) := by
          rw [hcoef]
          field_simp
  calc (∑ i ∈ Finset.range D,
        (γ * ((i : ℝ) + 1) ^ 3) ^ 2 * Real.sqrt ((mL i : ℝ) * (nL i : ℝ)))
      ≤ ∑ i ∈ Finset.range D,
          (γ ^ 2 * (((i : ℝ) + 1) ^ 6 / 2 ^ i)) * Real.sqrt ((m : ℝ) * (n : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = (γ ^ 2 * Real.sqrt ((m : ℝ) * (n : ℝ))) *
          ∑ i ∈ Finset.range D, (((i : ℝ) + 1) ^ 6 / 2 ^ i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ ≤ (γ ^ 2 * Real.sqrt ((m : ℝ) * (n : ℝ))) * 40000 := by
        apply mul_le_mul_of_nonneg_left (sum_pow6_div_two_pow_le D)
        positivity
    _ = γ ^ 2 * 40000 * Real.sqrt ((m : ℝ) * (n : ℝ)) := by ring

/-- **The error account of §3.6.**  Each level's errors and the edges it hands to child MSF calls
cost `O(t²√(m_c n_c)) + 4m_c/t_c`; summed over the levels this is
`γ²·40000·√(mn) + 16m/γ`.  (The paper's `4+4` split between errors and child inputs.) -/
theorem errors_levels {n m : ℕ} {γ : ℝ} (hγ : 0 < γ) {D : ℕ} {nL mL errL inL : ℕ → ℕ}
    (hn : ∀ i ∈ Finset.range D, (nL i : ℝ) * 4 ^ i ≤ (n : ℝ))
    (hm : ∀ i ∈ Finset.range D, (mL i : ℝ) ≤ (m : ℝ))
    (herr : ∀ i ∈ Finset.range D, (errL i : ℝ) ≤
      (γ * ((i : ℝ) + 1) ^ 3) ^ 2 * Real.sqrt ((mL i : ℝ) * (nL i : ℝ)) +
        4 * (mL i : ℝ) / (γ * ((i : ℝ) + 1) ^ 3))
    (hin : ∀ i ∈ Finset.range D, (inL i : ℝ) ≤
        4 * (mL i : ℝ) / (γ * ((i : ℝ) + 1) ^ 3)) :
    ((∑ i ∈ Finset.range D, (errL i : ℝ)) + ∑ i ∈ Finset.range D, (inL i : ℝ))
      ≤ γ ^ 2 * 40000 * Real.sqrt ((m : ℝ) * (n : ℝ)) + 16 * (m : ℝ) / γ := by
  have hgeometric :
      (∑ i ∈ Finset.range D,
        (γ * ((i : ℝ) + 1) ^ 3) ^ 2 * Real.sqrt ((mL i : ℝ) * (nL i : ℝ)))
        ≤ γ ^ 2 * 40000 * Real.sqrt ((m : ℝ) * (n : ℝ)) :=
    claim_3_13 hγ.le hn hm
  have hcubic : (∑ i ∈ Finset.range D, 8 * (mL i : ℝ) / (γ * ((i : ℝ) + 1) ^ 3))
      ≤ 16 * (m : ℝ) / γ := by
    have hstep : ∀ i ∈ Finset.range D,
        8 * (mL i : ℝ) / (γ * ((i : ℝ) + 1) ^ 3) ≤
          (8 * (m : ℝ) / γ) * (1 / ((i : ℝ) + 1) ^ 3) := by
      intro i hi
      have hden : (0 : ℝ) < γ * ((i : ℝ) + 1) ^ 3 := by positivity
      rw [div_le_iff₀ hden]
      rw [show (8 * (m : ℝ) / γ) * (1 / ((i : ℝ) + 1) ^ 3) * (γ * ((i : ℝ) + 1) ^ 3) =
          8 * (m : ℝ) by field_simp]
      linarith [hm i hi]
    calc (∑ i ∈ Finset.range D, 8 * (mL i : ℝ) / (γ * ((i : ℝ) + 1) ^ 3))
        ≤ ∑ i ∈ Finset.range D, (8 * (m : ℝ) / γ) * (1 / ((i : ℝ) + 1) ^ 3) :=
          Finset.sum_le_sum hstep
      _ = (8 * (m : ℝ) / γ) * ∑ i ∈ Finset.range D, (1 / ((i : ℝ) + 1) ^ 3) := by
          rw [Finset.mul_sum]
      _ ≤ (8 * (m : ℝ) / γ) * 2 := by
          apply mul_le_mul_of_nonneg_left (sum_inv_cube_le_two D)
          positivity
      _ = 16 * (m : ℝ) / γ := by ring
  have htotal : ((∑ i ∈ Finset.range D, (errL i : ℝ)) + ∑ i ∈ Finset.range D, (inL i : ℝ))
      ≤ (∑ i ∈ Finset.range D,
            (γ * ((i : ℝ) + 1) ^ 3) ^ 2 * Real.sqrt ((mL i : ℝ) * (nL i : ℝ))) +
          ∑ i ∈ Finset.range D, (8 * (mL i : ℝ) / (γ * ((i : ℝ) + 1) ^ 3)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have h1 := herr i hi
    have h2 := hin i hi
    have : 4 * (mL i : ℝ) / (γ * ((i : ℝ) + 1) ^ 3) +
        4 * (mL i : ℝ) / (γ * ((i : ℝ) + 1) ^ 3) =
        8 * (mL i : ℝ) / (γ * ((i : ℝ) + 1) ^ 3) := by ring
    linarith
  linarith

/-! ### The paper's honest per-call "rest": a `t²n` term

§3.6 bounds a call's *errors* by `O(t²√(m_c n_c)) + 4m_c/t_c`, and charges both `|U(F)|` and the child
calls that.  But the input size of a call's exact MSF calls also contains the per-round calls on the
old forest and the child forest, `2t²(n_c − 1)` edges each, and the per-block call,
`t_c(n_c − 1 + r_c² n_c)` — a `t²·n`-shaped term, not a `m/t` one.  Absorbing `r_c²` and the numeric
constants into a factor `C`, the child-call total of one instance is `≤ errF + C·t_c²·n_c`.

Level `d` has `n_d ≤ n/4^{d-1}` vertices, so the extra piece decays by `4^{-d}`
(`sum_pow6_div_four_pow_le`), and `n ≤ √2·√(mn)` (no isolated vertices) moves it into the `√(mn)`
term; the two `4m_d/t_d` sums still produce the paper's `16m/γ`.  This is the accounting the paper
actually needs — `inL ≤ 4m/t` alone covers only the rejected edges, not the per-round MSF calls. -/

/-- **The geometric factor with the `4^d` decay:** `Σ_{d ≥ 1} d^6/4^{d-1} ≤ 40000`, since each
`4^{-i}` is at most `2^{-i}`.  This is what a `t²·n` per-call term decays by, because the vertices
shrink by `4` per level. -/
theorem sum_pow6_div_four_pow_le (D : ℕ) :
    (∑ i ∈ Finset.range D, ((i : ℝ) + 1) ^ 6 / 4 ^ i) ≤ 40000 := by
  refine le_trans (Finset.sum_le_sum ?_) (sum_pow6_div_two_pow_le D)
  intro i _
  have h2 : (0 : ℝ) < 2 ^ i := by positivity
  have h4 : (0 : ℝ) < 4 ^ i := by positivity
  have h24 : (2 : ℝ) ^ i ≤ 4 ^ i := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have h6 : (0 : ℝ) ≤ ((i : ℝ) + 1) ^ 6 := by positivity
  rw [div_le_iff₀ h4, div_mul_eq_mul_div, le_div_iff₀ h2]
  exact mul_le_mul_of_nonneg_left h24 h6

/-- **`Σ_d 4m_d/(γd³) ≤ 8m/γ`**, the `4m/t` half of the error account, isolated so that the honest
per-call "rest" below can charge it a second time. -/
theorem sum_cubic_le {γ : ℝ} (hγ : 0 < γ) {D m : ℕ} {mL : ℕ → ℕ}
    (hm : ∀ i ∈ Finset.range D, (mL i : ℝ) ≤ (m : ℝ)) :
    (∑ i ∈ Finset.range D, 4 * (mL i : ℝ) / (γ * ((i : ℝ) + 1) ^ 3)) ≤ 8 * (m : ℝ) / γ := by
  have hstep : ∀ i ∈ Finset.range D,
      4 * (mL i : ℝ) / (γ * ((i : ℝ) + 1) ^ 3) ≤
        (4 * (m : ℝ) / γ) * (1 / ((i : ℝ) + 1) ^ 3) := by
    intro i hi
    have hden : (0 : ℝ) < γ * ((i : ℝ) + 1) ^ 3 := by positivity
    rw [div_le_iff₀ hden]
    rw [show (4 * (m : ℝ) / γ) * (1 / ((i : ℝ) + 1) ^ 3) * (γ * ((i : ℝ) + 1) ^ 3) =
        4 * (m : ℝ) by field_simp]
    linarith [hm i hi]
  calc (∑ i ∈ Finset.range D, 4 * (mL i : ℝ) / (γ * ((i : ℝ) + 1) ^ 3))
      ≤ ∑ i ∈ Finset.range D, (4 * (m : ℝ) / γ) * (1 / ((i : ℝ) + 1) ^ 3) :=
        Finset.sum_le_sum hstep
    _ = (4 * (m : ℝ) / γ) * ∑ i ∈ Finset.range D, (1 / ((i : ℝ) + 1) ^ 3) := by
        rw [Finset.mul_sum]
    _ ≤ (4 * (m : ℝ) / γ) * 2 := by
        apply mul_le_mul_of_nonneg_left (sum_inv_cube_le_two D)
        positivity
    _ = 8 * (m : ℝ) / γ := by ring

/-- **§3.6's error account with the honest per-call "rest".**  Per call,
`inF ≤ errF + C·t_c²·n_c` (the rejected edges' `4m/t` part plus the per-round MSF calls' `t²n` part),
`errF ≤ t_c²√(m_c n_c) + 4m_c/t_c`, and level `d` has `n_d·4^d ≤ n`, `m_d ≤ m`, `n ≤ 2m`.  Then

`Σ errL + Σ inL ≤ γ²·40000·(2 + √2·C)·√(mn) + 16m/γ`

— the paper's `16m/γ` survives untouched, and the `t²n` piece moves into the `√(mn)` term. -/
theorem errors_levels_rest {n m : ℕ} {γ : ℝ} (hγ : 0 < γ) {D : ℕ} {nL mL errL inL : ℕ → ℕ}
    {C : ℝ} (hC : 0 ≤ C)
    (hn : ∀ i ∈ Finset.range D, (nL i : ℝ) * 4 ^ i ≤ (n : ℝ))
    (hm : ∀ i ∈ Finset.range D, (mL i : ℝ) ≤ (m : ℝ))
    (hnm : (n : ℝ) ≤ 2 * (m : ℝ))
    (herr : ∀ i ∈ Finset.range D, (errL i : ℝ) ≤
      (γ * ((i : ℝ) + 1) ^ 3) ^ 2 * Real.sqrt ((mL i : ℝ) * (nL i : ℝ)) +
        4 * (mL i : ℝ) / (γ * ((i : ℝ) + 1) ^ 3))
    (hin : ∀ i ∈ Finset.range D, (inL i : ℝ) ≤ (errL i : ℝ) +
      C * ((γ * ((i : ℝ) + 1) ^ 3) ^ 2 * (nL i : ℝ))) :
    ((∑ i ∈ Finset.range D, (errL i : ℝ)) + ∑ i ∈ Finset.range D, (inL i : ℝ))
      ≤ γ ^ 2 * 40000 * (2 + Real.sqrt 2 * C) * Real.sqrt ((m : ℝ) * (n : ℝ)) +
        16 * (m : ℝ) / γ := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hn_sqrt : (n : ℝ) ≤ Real.sqrt 2 * Real.sqrt ((m : ℝ) * (n : ℝ)) := by
    have hsq : (n : ℝ) * (n : ℝ) ≤ (2 * (m : ℝ)) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hnm hn0
    have h1 : (n : ℝ) ≤ Real.sqrt (2 * (m : ℝ) * (n : ℝ)) := by
      rw [Real.le_sqrt (by positivity) (by positivity)]
      nlinarith
    calc (n : ℝ) ≤ Real.sqrt (2 * (m : ℝ) * (n : ℝ)) := h1
      _ = Real.sqrt 2 * Real.sqrt ((m : ℝ) * (n : ℝ)) := by
          rw [show (2 : ℝ) * (m : ℝ) * (n : ℝ) = 2 * ((m : ℝ) * (n : ℝ)) by ring,
            Real.sqrt_mul (by norm_num)]
  have hgeo := claim_3_13 (n := n) (m := m) (γ := γ) hγ.le (D := D) (nL := nL) (mL := mL) hn hm
  have hcub := sum_cubic_le (γ := γ) hγ (D := D) (m := m) (mL := mL) hm
  have hquad : (∑ i ∈ Finset.range D, C * ((γ * ((i : ℝ) + 1) ^ 3) ^ 2 * (nL i : ℝ)))
      ≤ γ ^ 2 * 40000 * (Real.sqrt 2 * C) * Real.sqrt ((m : ℝ) * (n : ℝ)) := by
    have hpoint : ∀ i ∈ Finset.range D,
        C * ((γ * ((i : ℝ) + 1) ^ 3) ^ 2 * (nL i : ℝ)) ≤
          (C * γ ^ 2 * (((i : ℝ) + 1) ^ 6 / 4 ^ i)) *
            (Real.sqrt 2 * Real.sqrt ((m : ℝ) * (n : ℝ))) := by
      intro i hi
      have h4 : (0 : ℝ) < 4 ^ i := by positivity
      have hni : (nL i : ℝ) ≤ (n : ℝ) / 4 ^ i := by
        rw [le_div_iff₀ h4]
        linarith [hn i hi]
      have hni' : (nL i : ℝ) ≤
          (Real.sqrt 2 * Real.sqrt ((m : ℝ) * (n : ℝ))) / 4 ^ i :=
        le_trans hni (div_le_div_of_nonneg_right hn_sqrt h4.le)
      have hcoef : (γ * ((i : ℝ) + 1) ^ 3) ^ 2 = γ ^ 2 * ((i : ℝ) + 1) ^ 6 := by
        rw [mul_pow]
        congr 1
        ring
      calc C * ((γ * ((i : ℝ) + 1) ^ 3) ^ 2 * (nL i : ℝ))
          = C * γ ^ 2 * ((i : ℝ) + 1) ^ 6 * (nL i : ℝ) := by rw [hcoef]; ring
        _ ≤ C * γ ^ 2 * ((i : ℝ) + 1) ^ 6 *
              ((Real.sqrt 2 * Real.sqrt ((m : ℝ) * (n : ℝ))) / 4 ^ i) :=
            mul_le_mul_of_nonneg_left hni' (by positivity)
        _ = (C * γ ^ 2 * (((i : ℝ) + 1) ^ 6 / 4 ^ i)) *
              (Real.sqrt 2 * Real.sqrt ((m : ℝ) * (n : ℝ))) := by ring
    calc (∑ i ∈ Finset.range D, C * ((γ * ((i : ℝ) + 1) ^ 3) ^ 2 * (nL i : ℝ)))
        ≤ ∑ i ∈ Finset.range D,
            (C * γ ^ 2 * (((i : ℝ) + 1) ^ 6 / 4 ^ i)) *
              (Real.sqrt 2 * Real.sqrt ((m : ℝ) * (n : ℝ))) := Finset.sum_le_sum hpoint
      _ = ∑ i ∈ Finset.range D,
            (C * γ ^ 2 * (Real.sqrt 2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) *
              (((i : ℝ) + 1) ^ 6 / 4 ^ i) :=
          Finset.sum_congr rfl (fun i _ => by ring)
      _ = C * γ ^ 2 * (Real.sqrt 2 * Real.sqrt ((m : ℝ) * (n : ℝ))) *
            ∑ i ∈ Finset.range D, (((i : ℝ) + 1) ^ 6 / 4 ^ i) := by
          rw [Finset.mul_sum]
      _ ≤ C * γ ^ 2 * (Real.sqrt 2 * Real.sqrt ((m : ℝ) * (n : ℝ))) * 40000 := by
          apply mul_le_mul_of_nonneg_left (sum_pow6_div_four_pow_le D)
          have := Real.sqrt_nonneg 2
          have := Real.sqrt_nonneg ((m : ℝ) * (n : ℝ))
          positivity
      _ = γ ^ 2 * 40000 * (Real.sqrt 2 * C) * Real.sqrt ((m : ℝ) * (n : ℝ)) := by ring
  have hsum_err : (∑ i ∈ Finset.range D, (errL i : ℝ)) ≤
      (∑ i ∈ Finset.range D,
          (γ * ((i : ℝ) + 1) ^ 3) ^ 2 * Real.sqrt ((mL i : ℝ) * (nL i : ℝ))) +
        ∑ i ∈ Finset.range D, 4 * (mL i : ℝ) / (γ * ((i : ℝ) + 1) ^ 3) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum herr
  have hsum_in : (∑ i ∈ Finset.range D, (inL i : ℝ)) ≤
      (∑ i ∈ Finset.range D, (errL i : ℝ)) +
        ∑ i ∈ Finset.range D, C * ((γ * ((i : ℝ) + 1) ^ 3) ^ 2 * (nL i : ℝ)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hin
  have hsplit : γ ^ 2 * 40000 * (2 + Real.sqrt 2 * C) * Real.sqrt ((m : ℝ) * (n : ℝ)) +
        16 * (m : ℝ) / γ =
      (γ ^ 2 * 40000 * Real.sqrt ((m : ℝ) * (n : ℝ)) +
          γ ^ 2 * 40000 * Real.sqrt ((m : ℝ) * (n : ℝ))) +
        (8 * (m : ℝ) / γ + 8 * (m : ℝ) / γ) +
        γ ^ 2 * 40000 * (Real.sqrt 2 * C) * Real.sqrt ((m : ℝ) * (n : ℝ)) := by ring
  rw [hsplit]
  linarith [hgeo, hcub, hquad, hsum_err, hsum_in]

/-! ## 4. Assembly: the display of Lemma 3.1 -/

/-- **`lemma12_bound` with the `√(mn)` constant left open.**  The proof only ever uses `40000` as a
nonnegative factor of `γ²√(mn)`, so the honest per-call account
(`errors_levels_rest`, constant `40000·(2 + √2·C)`) can be plugged in unchanged. -/
theorem lemma12_bound_gen {n m Fc U SE : ℕ} {γ ε K : ℝ} (hγ : 0 < γ) (_hε : 0 < ε)
    (hγε : 16 ≤ ε * γ) (_hK : 0 ≤ K) (hnm : (n : ℝ) ≤ 2 * (m : ℝ))
    (hF : (Fc : ℝ) ≤ (n : ℝ))
    (hrest : (U : ℝ) + (SE : ℝ) ≤
      γ ^ 2 * K * Real.sqrt ((m : ℝ) * (n : ℝ)) + 16 * (m : ℝ) / γ) :
    (Fc : ℝ) + (U : ℝ) + (SE : ℝ) ≤
      ε * (m : ℝ) + (Real.sqrt 2 + γ ^ 2 * K) * Real.sqrt ((m : ℝ) * (n : ℝ)) := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hn_sqrt : (n : ℝ) ≤ Real.sqrt 2 * Real.sqrt ((m : ℝ) * (n : ℝ)) := by
    have hsq : (n : ℝ) * (n : ℝ) ≤ (2 * (m : ℝ)) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hnm hn0
    have h1 : (n : ℝ) ≤ Real.sqrt (2 * (m : ℝ) * (n : ℝ)) := by
      rw [Real.le_sqrt (by positivity) (by positivity)]
      nlinarith
    calc (n : ℝ) ≤ Real.sqrt (2 * (m : ℝ) * (n : ℝ)) := h1
      _ = Real.sqrt 2 * Real.sqrt ((m : ℝ) * (n : ℝ)) := by
          rw [show (2 : ℝ) * (m : ℝ) * (n : ℝ) = 2 * ((m : ℝ) * (n : ℝ)) by ring,
            Real.sqrt_mul (by norm_num)]
  have hlast : 16 * (m : ℝ) / γ ≤ ε * (m : ℝ) := by
    rw [div_le_iff₀ hγ]
    have h := mul_le_mul_of_nonneg_right hγε hm0
    nlinarith
  have hrest' : (U : ℝ) + (SE : ℝ) ≤
      γ ^ 2 * K * Real.sqrt ((m : ℝ) * (n : ℝ)) + ε * (m : ℝ) := by linarith
  have hF' : (Fc : ℝ) ≤ Real.sqrt 2 * Real.sqrt ((m : ℝ) * (n : ℝ)) := le_trans hF hn_sqrt
  nlinarith

/-- **Lemma 3.1 / Lemma 1.2, the display `|F| + |U(F)| + Σᵢ|Eᵢ| ≤ εm + C_ε√(mn)`.**

The three inputs are the paper's own remaining obligations, stated as hypotheses rather than
hidden: `hF` is `|F| ≤ n` (a forest has at most `n-1` edges; not yet formalised), `hnm` is `n ≤ 2m`
(no isolated vertices, `Selection.sum_degree` gives it), and `hrest` is the §3.6 account proved in
`errors_levels` — `|U(F)|` pays it by Lemma 3.7 and the child MSF calls pay it again.  With
`γ ≥ 16/ε` the `16m/γ` term is absorbed into `εm`, leaving `C_ε = √2 + 40000γ²`. -/
theorem lemma12_bound {n m Fc U SE : ℕ} {γ ε : ℝ} (hγ : 0 < γ) (_hε : 0 < ε)
    (hγε : 16 ≤ ε * γ) (hnm : (n : ℝ) ≤ 2 * (m : ℝ))
    (hF : (Fc : ℝ) ≤ (n : ℝ))
    (hrest : (U : ℝ) + (SE : ℝ) ≤
      γ ^ 2 * 40000 * Real.sqrt ((m : ℝ) * (n : ℝ)) + 16 * (m : ℝ) / γ) :
    (Fc : ℝ) + (U : ℝ) + (SE : ℝ) ≤
      ε * (m : ℝ) + (Real.sqrt 2 + γ ^ 2 * 40000) * Real.sqrt ((m : ℝ) * (n : ℝ)) :=
  lemma12_bound_gen (K := (40000 : ℝ)) hγ _hε hγε (by norm_num) hnm hF hrest

/-! ## 4b. Discharging `n ≤ 2m` from "no isolated vertices"

Lemma 1.2 is stated for graphs with no isolated vertices, and `n ≤ 2m` is where that hypothesis is
used.  Degree counting: every vertex contributes at least `1` to `Σ deg(v)`, while the handshake
bound (`sum_degV_le_two_mul`) caps the sum by `2|E|`. -/

/-- **`n ≤ 2m`.**  A graph on `V` with no isolated vertices has at most twice as many edges as
vertices — the numeric hypothesis `lemma12_bound.hnm`. -/
theorem card_le_two_mul_of_no_isolated (hno : ∀ v : V, 1 ≤ degV G v) :
    (Fintype.card V : ℝ) ≤ 2 * (Fintype.card E : ℝ) := by
  have h1 : (Fintype.card V : ℕ) ≤ ∑ v : V, degV G v := by
    calc (Fintype.card V : ℕ) = ∑ _v : V, 1 := by simp
      _ ≤ ∑ v : V, degV G v := Finset.sum_le_sum (fun v _ => hno v)
  have h2 := sum_degV_le_two_mul (G := G)
  exact_mod_cast le_trans h1 h2

/-- With no isolated vertices there is at least one edge. -/
theorem nonempty_edge_of_no_isolated [Nonempty V] (hno : ∀ v : V, 1 ≤ degV G v) :
    Nonempty E := by
  have h1 : 1 ≤ (Finset.univ.filter (incident G (Classical.arbitrary V))).card := by
    simpa [degV] using hno (Classical.arbitrary V)
  obtain ⟨e, -⟩ := Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one h1)
  exact ⟨e⟩

/-- With no isolated vertices some incident edge can be assigned to every vertex — the total spoke
map §3.2's update starts from. -/
theorem exists_incident_map (hno : ∀ v : V, 1 ≤ degV G v) :
    ∃ σ : V → E, ∀ v, incident G v (σ v) := by
  have h : ∀ v : V, (Finset.univ.filter (incident G v)).Nonempty := fun v => by
    have h1 : 1 ≤ (Finset.univ.filter (incident G v)).card := by
      simpa [degV] using hno v
    exact Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one h1)
  choose σ hσ using h
  exact ⟨σ, fun v => (Finset.mem_filter.mp (hσ v)).2⟩

/-- **Lemma 3.1 = 1.2 with "no isolated vertices" instead of `n ≤ 2m`.**  Same conclusion, with
`n = |V|`, `m = |E|` and `hnm` supplied by `card_le_two_mul_of_no_isolated`. -/
theorem lemma12_bound_card {Fc U SE : ℕ} {γ ε : ℝ} (hγ : 0 < γ) (hε : 0 < ε)
    (hγε : 16 ≤ ε * γ) (hno : ∀ v : V, 1 ≤ degV G v)
    (hF : (Fc : ℝ) ≤ (Fintype.card V : ℝ))
    (hrest : (U : ℝ) + (SE : ℝ) ≤
      γ ^ 2 * 40000 * Real.sqrt ((Fintype.card E : ℝ) * (Fintype.card V : ℝ)) +
        16 * (Fintype.card E : ℝ) / γ) :
    (Fc : ℝ) + (U : ℝ) + (SE : ℝ) ≤
      ε * (Fintype.card E : ℝ) +
        (Real.sqrt 2 + γ ^ 2 * 40000) * Real.sqrt ((Fintype.card E : ℝ) * (Fintype.card V : ℝ)) :=
  lemma12_bound hγ hε hγε
    (card_le_two_mul_of_no_isolated (G := G) hno) hF hrest

/-- **Lemma 3.1 = 1.2 with `|F| ≤ n` discharged as well.**  For an acyclic edge set `F`
(`IsForest`, which is what the certificate procedure returns), the forest-size hypothesis of
`lemma12_bound_card` is a theorem now — `ForestCard.card_le_card_of_isForest`. -/
theorem lemma12_bound_of_forest {F : Finset E} {U SE : ℕ} {γ ε : ℝ} (hγ : 0 < γ) (hε : 0 < ε)
    (hγε : 16 ≤ ε * γ) (hno : ∀ v : V, 1 ≤ degV G v) (hF : IsForest G F)
    (hrest : (U : ℝ) + (SE : ℝ) ≤
      γ ^ 2 * 40000 * Real.sqrt ((Fintype.card E : ℝ) * (Fintype.card V : ℝ)) +
        16 * (Fintype.card E : ℝ) / γ) :
    (F.card : ℝ) + (U : ℝ) + (SE : ℝ) ≤
      ε * (Fintype.card E : ℝ) +
        (Real.sqrt 2 + γ ^ 2 * 40000) * Real.sqrt ((Fintype.card E : ℝ) * (Fintype.card V : ℝ)) :=
  lemma12_bound_card (G := G) hγ hε hγε hno
    (by exact_mod_cast card_le_card_of_isForest (G := G) hF) hrest

/-! ## 5. Sanity: an MSF supports everything

The inequality of Lemma 3.1 is *satisfiable without any procedure*: take `F` to be an MSF.  By the
cycle property every edge is supported by it, so `U(F) = ∅`, and `|F| ≤ n ≤ √2·√(mn)`.  Thus the
content of Lemma 3.1 is not the inequality but the `O_ε(m)` comparison procedure that reaches it. -/

/-- **`U(MSF) = ∅`.**  Every edge is supported by a minimum spanning forest: `IsMSFOf.below_span`
(Fact 2.5) applied to the trivially supported edge set `E(G)` itself. -/
theorem unsupp_msf_eq_empty {T : Finset E} (hT : IsMSF G T) : unsupp G T = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  intro hne
  obtain ⟨e, he⟩ := hne
  rw [mem_unsupp] at he
  exact he (IsMSFOf.supported_of (IsMSF.msfof_univ hT)
    (Conn.step e (belowLe_mem.mpr ⟨Finset.mem_univ e, le_refl _⟩)))

end DLMST