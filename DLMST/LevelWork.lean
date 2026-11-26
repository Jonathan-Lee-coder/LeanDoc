import DLMST.LevelLinear
import DLMST.Section36

/-!
# §3.6: from the per-call counts to linear total work on the levels

`LevelLinear.lean` proves that the level model's total work `Σ_d (|V_d| + |E_d|)` is linear *given a
per-level display with one uniform constant* `C`.  The paper's per-call counts, however, carry the
level's own parameter `t_d = γ(d+1)³`: the retained set is `10t_d²√(m_c n_c) + 4m_c/t_d`, and the
child input adds `2t_d²(n_c−1) + t_d(n_c−1 + r_d² n_c)` with `r_d = 8t_d³`, i.e. coefficients
`γ²(d+1)⁶` and `64γ⁷(d+1)²¹` that *grow with the level*.  A level-uniform `C` therefore does not
follow from these counts; what does follow is the level sum, because the vertex totals shrink by `4`
per level — the paper's own accounting (`Section36.claim_3_13`, `sum_pow6_div_four_pow_le`,
`sum_pow21_mul_le`).

This file closes exactly that step:

* `chain_edges_display` — one level's edge total, from the per-call counts at the level's `t_d`
  (level Cauchy–Schwarz `Level.errors_le_coef`, the `t²n` pieces gathered);
* `level_work_poly` — the arithmetic core: a recursion
  `m_{d+1} ≤ 10γ²(d+1)⁶√(m_d n_d) + 4m_d/(γ(d+1)³) + (2γ²(d+1)⁶ + γ(d+1)³ + 64γ⁷(d+1)²¹)·n_d`
  with `n_d·4^d ≤ N` and `m_d ≤ M` has `Σ_d(n_d + m_d) ≤ 4N/3 + (4/3)(M + R)`, where
  `R = 10γ²·40000·√(MN) + (64γ⁷·202²¹·2 + 2·40000γ² + 40000γ)·N`;
* `chain_work_linear_counts` — the two combined: **the §3.5/§3.6 per-call counts at each level's own
  `t_d`, plus the level geometry, give linear total work** — no uniform `C`, no `hshr`, no `htd`.

The only data left are the per-call numeric bounds themselves (the paper's §3.5 estimate and p. 24
input count), which enter exactly as in `Procedure.hrest_of_levels`.
-/

namespace DLMST

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

/-! ## 1. One level's edge total, from the calls' own counts -/

/-- **A level's edge total from the per-call §3.5/§3.6 counts.**  Each call `a` at depth `d` has
`|U(F)| ≤ 10t_d²√(m_a n_a) + 4m_a/t_d` and hands its children at most
`|U(F)| + 2t_d²(n_a−1) + t_d(n_a−1+r_d²n_a)` edges, `t_d = γ(d+1)³`, `r_d = 8t_d³`.  Then the level's
edge total (the next level's input) is at most
`10t_d²√(m_d n_d) + 4m_d/t_d + (2t_d² + t_d + 64t_d⁷)·n_d` — the level form of the paper's account.
The `(n_a − 1)` are majorized by `n_a`, which is where the constants `2, 1, 64` come from. -/
theorem chain_edges_display (P : Finset V) (E₀ : Finset E) (S : Strategy G) (hS : Strategy.Wf S)
    {γ : ℝ} (hγ : 16 ≤ γ)
    (hU : ∀ (d : ℕ), ∀ a ∈ (Level.chain P E₀ S hS d).insts,
      (((S a.1 a.2).2.U).card : ℝ) ≤
        10 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 *
            Real.sqrt ((a.2.card : ℝ) * (a.1.card : ℝ))) +
          4 * (a.2.card : ℝ) / (γ * ((d : ℝ) + 1) ^ 3))
    (hrnd : ∀ (d : ℕ), ∀ a ∈ (Level.chain P E₀ S hS d).insts,
      ((∑ i, ((S a.1 a.2).2.kidE i).card : ℕ) : ℝ) ≤
        (((S a.1 a.2).2.U).card : ℝ) +
          2 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 * (((a.1.card - 1 : ℕ) : ℝ))) +
            (γ * ((d : ℝ) + 1) ^ 3) *
              ((((a.1.card - 1 : ℕ) : ℝ)) +
                (8 * (γ * ((d : ℝ) + 1) ^ 3) ^ 3) ^ 2 * (a.1.card : ℝ)))
    (d : ℕ) :
    ((Level.chain P E₀ S hS (d + 1)).edges : ℝ) ≤
      10 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 *
          Real.sqrt (((Level.chain P E₀ S hS d).edges : ℝ) *
            ((Level.chain P E₀ S hS d).verts : ℝ))) +
        4 * ((Level.chain P E₀ S hS d).edges : ℝ) / (γ * ((d : ℝ) + 1) ^ 3) +
          (2 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2) + (γ * ((d : ℝ) + 1) ^ 3) +
            64 * (γ * ((d : ℝ) + 1) ^ 3) ^ 7) *
            ((Level.chain P E₀ S hS d).verts : ℝ) := by
  classical
  set L := Level.chain P E₀ S hS d with hL
  set t : ℝ := γ * ((d : ℝ) + 1) ^ 3 with ht
  have hγ0 : (0 : ℝ) < γ := by linarith
  have htpos : (0 : ℝ) < t := by rw [ht]; positivity
  have hcast : (((Level.chain P E₀ S hS (d + 1)).edges : ℕ) : ℝ) =
      ∑ a ∈ L.insts, ∑ i, (((S a.1 a.2).2.kidE i).card : ℝ) := by
    rw [LevelChain.chain_edges_succ P E₀ S hS d]
    push_cast
    rfl
  have herrL := Level.errors_le_coef (K := 10) (t := t) (by norm_num) htpos L
    (fun a => ((S a.1 a.2).2.U).card) (fun a ha => by
      have := hU d a ha
      simpa only [← ht] using this)
  have hVsum : (∑ a ∈ L.insts, (a.1.card : ℝ)) = (L.verts : ℝ) := by
    rw [Level.verts]
    exact (Nat.cast_sum _ _).symm
  have hper : ∀ a ∈ L.insts,
      (∑ i, (((S a.1 a.2).2.kidE i).card : ℝ)) ≤
        (((S a.1 a.2).2.U).card : ℝ) + 2 * t ^ 2 * (a.1.card : ℝ) +
          t * (1 + 64 * t ^ 6) * (a.1.card : ℝ) := by
    intro a ha
    have h := hrnd d a ha
    simp only [← ht] at h
    rw [Nat.cast_sum] at h
    have hpred : ((a.1.card - 1 : ℕ) : ℝ) ≤ (a.1.card : ℝ) := by
      exact_mod_cast Nat.sub_le a.1.card 1
    have hstep1 : 2 * t ^ 2 * ((a.1.card - 1 : ℕ) : ℝ) ≤ 2 * t ^ 2 * (a.1.card : ℝ) :=
      mul_le_mul_of_nonneg_left hpred (by positivity)
    have h8 : (8 * t ^ 3) ^ 2 = 64 * t ^ 6 := by ring
    have hstep2 : ((a.1.card - 1 : ℕ) : ℝ) + (8 * t ^ 3) ^ 2 * (a.1.card : ℝ) ≤
        (a.1.card : ℝ) + 64 * t ^ 6 * (a.1.card : ℝ) := by
      have h9 : ((a.1.card - 1 : ℕ) : ℝ) + (8 * t ^ 3) ^ 2 * (a.1.card : ℝ) ≤
          (a.1.card : ℝ) + (8 * t ^ 3) ^ 2 * (a.1.card : ℝ) := by linarith
      have h10 : (a.1.card : ℝ) + (8 * t ^ 3) ^ 2 * (a.1.card : ℝ) =
          (a.1.card : ℝ) + 64 * t ^ 6 * (a.1.card : ℝ) := by rw [h8]
      linarith
    have hstep3 : t * (((a.1.card - 1 : ℕ) : ℝ) + (8 * t ^ 3) ^ 2 * (a.1.card : ℝ)) ≤
        t * ((a.1.card : ℝ) + 64 * t ^ 6 * (a.1.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hstep2 htpos.le
    have hstep4 : t * ((a.1.card : ℝ) + 64 * t ^ 6 * (a.1.card : ℝ)) =
        t * (1 + 64 * t ^ 6) * (a.1.card : ℝ) := by ring
    linarith
  have hsum : (∑ a ∈ L.insts, ∑ i, (((S a.1 a.2).2.kidE i).card : ℝ)) ≤
      (∑ a ∈ L.insts, (((S a.1 a.2).2.U).card : ℝ)) + 2 * t ^ 2 * (L.verts : ℝ) +
        t * (1 + 64 * t ^ 6) * (L.verts : ℝ) := by
    calc (∑ a ∈ L.insts, ∑ i, (((S a.1 a.2).2.kidE i).card : ℝ))
        ≤ ∑ a ∈ L.insts, ((((S a.1 a.2).2.U).card : ℝ) + 2 * t ^ 2 * (a.1.card : ℝ) +
            t * (1 + 64 * t ^ 6) * (a.1.card : ℝ)) := Finset.sum_le_sum hper
      _ = (∑ a ∈ L.insts, (((S a.1 a.2).2.U).card : ℝ)) + 2 * t ^ 2 * (L.verts : ℝ) +
            t * (1 + 64 * t ^ 6) * (L.verts : ℝ) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum, hVsum]
  have herrL' : (∑ a ∈ L.insts, (((S a.1 a.2).2.U).card : ℝ)) ≤
      10 * (t ^ 2 * Real.sqrt ((L.edges : ℝ) * (L.verts : ℝ))) +
        4 * (L.edges : ℝ) / t := herrL
  rw [hcast]
  calc (∑ a ∈ L.insts, ∑ i, (((S a.1 a.2).2.kidE i).card : ℝ))
      ≤ (∑ a ∈ L.insts, (((S a.1 a.2).2.U).card : ℝ)) + 2 * t ^ 2 * (L.verts : ℝ) +
          t * (1 + 64 * t ^ 6) * (L.verts : ℝ) := hsum
    _ ≤ (10 * (t ^ 2 * Real.sqrt ((L.edges : ℝ) * (L.verts : ℝ))) +
          4 * (L.edges : ℝ) / t) + 2 * t ^ 2 * (L.verts : ℝ) +
            t * (1 + 64 * t ^ 6) * (L.verts : ℝ) := by linarith [herrL']
    _ = 10 * (t ^ 2 * Real.sqrt ((L.edges : ℝ) * (L.verts : ℝ))) +
          4 * (L.edges : ℝ) / t + (2 * t ^ 2 + t + 64 * t ^ 7) * (L.verts : ℝ) := by ring

/-! ## 2. The arithmetic core: per-level coefficients absorbed by the `4^{-d}` vertex decay -/

/-- **The level recursion with the paper's level-stamped coefficients.**  `m 0 = M`, `m d ≤ M`,
`n d` shrinks by `4` (`n d · 4^d ≤ N`), and each level obeys
`m (d+1) ≤ 10γ²(d+1)⁶√(m_d n_d) + 4m_d/(γ(d+1)³) + (2γ²(d+1)⁶ + γ(d+1)³ + 64γ⁷(d+1)²¹)·n_d`
with `γ ≥ 16`.  Then the total work over the levels is linear:
`Σ_d(n_d + m_d) ≤ 4N/3 + (4/3)(M + R)`, `R` the three geometric accounts of `Section36`. -/
theorem level_work_poly {m n : ℕ → ℝ} {M N γ : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hγ : 16 ≤ γ) (hv4le : ∀ d, n d * (4 : ℝ) ^ d ≤ N) (hmM : ∀ d, m d ≤ M)
    (hm0 : m 0 = M) (hnnn : ∀ d, 0 ≤ n d) (hmnn : ∀ d, 0 ≤ m d)
    (hstep : ∀ d, m (d + 1) ≤
      10 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 * Real.sqrt (m d * n d)) +
        4 * m d / (γ * ((d : ℝ) + 1) ^ 3) +
          (2 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2) + (γ * ((d : ℝ) + 1) ^ 3) +
            64 * (γ * ((d : ℝ) + 1) ^ 3) ^ 7) * n d) :
    ∀ D : ℕ, (∑ d ∈ Finset.range D, (n d + m d)) ≤
      4 / 3 * N + 4 / 3 * (M +
        (10 * (γ ^ 2 * 40000 * Real.sqrt (M * N)) +
          (64 * γ ^ 7 * ((202 : ℝ) ^ 21 * 2) + 2 * (40000 * γ ^ 2) + 40000 * γ) * N)) := by
  intro D
  have hγ0 : (0 : ℝ) < γ := by linarith
  -- `n d ≤ N/4^d`
  have hnd : ∀ d, n d ≤ N / (4 : ℝ) ^ d := by
    intro d
    have h4 : (0 : ℝ) < (4 : ℝ) ^ d := by positivity
    rw [le_div_iff₀ h4]
    exact hv4le d
  -- the `√` account: `Σ 10γ²(d+1)⁶√(m_d n_d) ≤ 10γ²·40000·√(MN)`
  have hA : (∑ d ∈ Finset.range D,
      10 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 * Real.sqrt (m d * n d))) ≤
      10 * (γ ^ 2 * 40000 * Real.sqrt (M * N)) := by
    have hpoint : ∀ (d : ℕ), (γ * ((d : ℝ) + 1) ^ 3) ^ 2 * Real.sqrt (m d * n d) ≤
        γ ^ 2 * (((d : ℝ) + 1) ^ 6 / 2 ^ d) * Real.sqrt (M * N) := by
      intro d
      have h4 : (0 : ℝ) < (4 : ℝ) ^ d := by positivity
      have hmn : m d * n d ≤ M * N / (4 : ℝ) ^ d := by
        calc m d * n d ≤ M * (N / (4 : ℝ) ^ d) :=
              mul_le_mul (hmM d) (hnd d) (hnnn d) hM
          _ = M * N / (4 : ℝ) ^ d := by ring
      have hsq : Real.sqrt (m d * n d) ≤ Real.sqrt (M * N) / 2 ^ d := by
        have h1 : Real.sqrt (M * N / (4 : ℝ) ^ d) = Real.sqrt (M * N) / 2 ^ d := by
          rw [div_eq_mul_inv, Real.sqrt_mul (by positivity), Real.sqrt_inv, sqrt_four_pow]
          ring
        exact le_trans (Real.sqrt_le_sqrt hmn) (le_of_eq h1)
      calc (γ * ((d : ℝ) + 1) ^ 3) ^ 2 * Real.sqrt (m d * n d)
          ≤ (γ * ((d : ℝ) + 1) ^ 3) ^ 2 * (Real.sqrt (M * N) / 2 ^ d) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = γ ^ 2 * (((d : ℝ) + 1) ^ 6 / 2 ^ d) * Real.sqrt (M * N) := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            ring
    have hsum := Finset.sum_le_sum (fun d (_ : d ∈ Finset.range D) =>
      mul_le_mul_of_nonneg_left (hpoint d) (by norm_num : (0 : ℝ) ≤ 10))
    have hfac : (∑ d ∈ Finset.range D,
        10 * (γ ^ 2 * (((d : ℝ) + 1) ^ 6 / 2 ^ d) * Real.sqrt (M * N))) =
        10 * (γ ^ 2 * Real.sqrt (M * N)) * ∑ d ∈ Finset.range D, ((d : ℝ) + 1) ^ 6 / 2 ^ d := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      ring
    have hp6 := sum_pow6_div_two_pow_le D
    calc (∑ d ∈ Finset.range D,
          10 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 * Real.sqrt (m d * n d)))
        ≤ ∑ d ∈ Finset.range D,
            10 * (γ ^ 2 * (((d : ℝ) + 1) ^ 6 / 2 ^ d) * Real.sqrt (M * N)) := hsum
      _ = 10 * (γ ^ 2 * Real.sqrt (M * N)) *
            ∑ d ∈ Finset.range D, ((d : ℝ) + 1) ^ 6 / 2 ^ d := hfac
      _ ≤ 10 * (γ ^ 2 * Real.sqrt (M * N)) * 40000 :=
          mul_le_mul_of_nonneg_left hp6 (by positivity)
      _ = 10 * (γ ^ 2 * 40000 * Real.sqrt (M * N)) := by ring
  -- the `4m/t` account: absorbed into `(4/γ)Σm ≤ (1/4)Σm`
  have hB : (∑ d ∈ Finset.range D, 4 * m d / (γ * ((d : ℝ) + 1) ^ 3)) ≤
      (4 / γ) * ∑ d ∈ Finset.range D, m d := by
    have hcub : ∀ d, 4 * m d / (γ * ((d : ℝ) + 1) ^ 3) ≤ (4 / γ) * m d := by
      intro d
      have htpos : (0 : ℝ) < γ * ((d : ℝ) + 1) ^ 3 := by positivity
      have h1 : (1 : ℝ) ≤ ((d : ℝ) + 1) ^ 3 := one_le_pow₀ (by linarith)
      have h2 : γ ≤ γ * ((d : ℝ) + 1) ^ 3 := by
        simpa using mul_le_mul_of_nonneg_left h1 hγ0.le
      calc 4 * m d / (γ * ((d : ℝ) + 1) ^ 3) ≤ 4 * m d / γ :=
            div_le_div_of_nonneg_left (by linarith [hmnn d]) hγ0 h2
        _ = (4 / γ) * m d := by ring
    calc (∑ d ∈ Finset.range D, 4 * m d / (γ * ((d : ℝ) + 1) ^ 3))
        ≤ ∑ d ∈ Finset.range D, (4 / γ) * m d := Finset.sum_le_sum (fun d _ => hcub d)
      _ = (4 / γ) * ∑ d ∈ Finset.range D, m d := by rw [Finset.mul_sum]
  -- the `2γ²(d+1)⁶ n_d` account
  have hC1 : (∑ d ∈ Finset.range D, 2 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2) * n d) ≤
      2 * (40000 * γ ^ 2) * N := by
    have hpoint : ∀ (d : ℕ), 2 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2) * n d ≤
        (2 * γ ^ 2 * N) * (((d : ℝ) + 1) ^ 6 / 4 ^ d) := by
      intro d
      have h4 : (0 : ℝ) < (4 : ℝ) ^ d := by positivity
      have hnn : 0 ≤ n d := hnnn d
      calc 2 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2) * n d
          = (2 * γ ^ 2 * ((d : ℝ) + 1) ^ 6) * n d := by ring
        _ ≤ (2 * γ ^ 2 * ((d : ℝ) + 1) ^ 6) * (N / 4 ^ d) :=
            mul_le_mul_of_nonneg_left (hnd d) (by positivity)
        _ = (2 * γ ^ 2 * N) * (((d : ℝ) + 1) ^ 6 / 4 ^ d) := by ring
    have hsum := Finset.sum_le_sum (fun d (_ : d ∈ Finset.range D) => hpoint d)
    have hfac : (∑ d ∈ Finset.range D, (2 * γ ^ 2 * N) * (((d : ℝ) + 1) ^ 6 / 4 ^ d)) =
        (2 * γ ^ 2 * N) * ∑ d ∈ Finset.range D, ((d : ℝ) + 1) ^ 6 / 4 ^ d := by
      rw [Finset.mul_sum]
    have hp6 := sum_pow6_div_four_pow_le D
    calc (∑ d ∈ Finset.range D, 2 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2) * n d)
        ≤ ∑ d ∈ Finset.range D, (2 * γ ^ 2 * N) * (((d : ℝ) + 1) ^ 6 / 4 ^ d) := hsum
      _ = (2 * γ ^ 2 * N) * ∑ d ∈ Finset.range D, ((d : ℝ) + 1) ^ 6 / 4 ^ d := hfac
      _ ≤ (2 * γ ^ 2 * N) * 40000 := mul_le_mul_of_nonneg_left hp6 (by positivity)
      _ = 2 * (40000 * γ ^ 2) * N := by ring
  -- the `γ(d+1)³ n_d` account
  have hC2 : (∑ d ∈ Finset.range D, (γ * ((d : ℝ) + 1) ^ 3) * n d) ≤ 40000 * γ * N := by
    have hpoint : ∀ (d : ℕ), (γ * ((d : ℝ) + 1) ^ 3) * n d ≤
        (γ * N) * (((d : ℝ) + 1) ^ 6 / 4 ^ d) := by
      intro d
      have h4 : (0 : ℝ) < (4 : ℝ) ^ d := by positivity
      have h15 : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith
      have hpow : ((d : ℝ) + 1) ^ 3 ≤ ((d : ℝ) + 1) ^ 6 :=
        pow_le_pow_right₀ h15 (by norm_num)
      calc (γ * ((d : ℝ) + 1) ^ 3) * n d
          ≤ (γ * ((d : ℝ) + 1) ^ 6) * n d :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hγ0.le) (hnnn d)
        _ ≤ (γ * ((d : ℝ) + 1) ^ 6) * (N / 4 ^ d) :=
            mul_le_mul_of_nonneg_left (hnd d) (by positivity)
        _ = (γ * N) * (((d : ℝ) + 1) ^ 6 / 4 ^ d) := by ring
    have hsum := Finset.sum_le_sum (fun d (_ : d ∈ Finset.range D) => hpoint d)
    have hfac : (∑ d ∈ Finset.range D, (γ * N) * (((d : ℝ) + 1) ^ 6 / 4 ^ d)) =
        (γ * N) * ∑ d ∈ Finset.range D, ((d : ℝ) + 1) ^ 6 / 4 ^ d := by
      rw [Finset.mul_sum]
    have hp6 := sum_pow6_div_four_pow_le D
    calc (∑ d ∈ Finset.range D, (γ * ((d : ℝ) + 1) ^ 3) * n d)
        ≤ ∑ d ∈ Finset.range D, (γ * N) * (((d : ℝ) + 1) ^ 6 / 4 ^ d) := hsum
      _ = (γ * N) * ∑ d ∈ Finset.range D, ((d : ℝ) + 1) ^ 6 / 4 ^ d := hfac
      _ ≤ (γ * N) * 40000 := mul_le_mul_of_nonneg_left hp6 (by positivity)
      _ = 40000 * γ * N := by ring
  -- the `64γ⁷(d+1)²¹ n_d` account
  have hC3 : (∑ d ∈ Finset.range D, 64 * (γ * ((d : ℝ) + 1) ^ 3) ^ 7 * n d) ≤
      64 * γ ^ 7 * ((202 : ℝ) ^ 21 * 2) * N := by
    have hpoint : ∀ (d : ℕ), 64 * (γ * ((d : ℝ) + 1) ^ 3) ^ 7 * n d ≤
        (64 * γ ^ 7 * N) * (((d : ℝ) + 1) ^ 21 / 4 ^ d) := by
      intro d
      have h4 : (0 : ℝ) < (4 : ℝ) ^ d := by positivity
      have hre : 64 * (γ * ((d : ℝ) + 1) ^ 3) ^ 7 * n d =
          (64 * γ ^ 7 * ((d : ℝ) + 1) ^ 21) * n d := by ring
      rw [hre]
      calc (64 * γ ^ 7 * ((d : ℝ) + 1) ^ 21) * n d
          ≤ (64 * γ ^ 7 * ((d : ℝ) + 1) ^ 21) * (N / 4 ^ d) :=
            mul_le_mul_of_nonneg_left (hnd d) (by positivity)
        _ = (64 * γ ^ 7 * N) * (((d : ℝ) + 1) ^ 21 / 4 ^ d) := by ring
    have hsum := Finset.sum_le_sum (fun d (_ : d ∈ Finset.range D) => hpoint d)
    have hfac : (∑ d ∈ Finset.range D, (64 * γ ^ 7 * N) * (((d : ℝ) + 1) ^ 21 / 4 ^ d)) =
        (64 * γ ^ 7 * N) * ∑ d ∈ Finset.range D, ((d : ℝ) + 1) ^ 21 / 4 ^ d := by
      rw [Finset.mul_sum]
    have hp := sum_pow21_div_four_pow_le D
    calc (∑ d ∈ Finset.range D, 64 * (γ * ((d : ℝ) + 1) ^ 3) ^ 7 * n d)
        ≤ ∑ d ∈ Finset.range D, (64 * γ ^ 7 * N) * (((d : ℝ) + 1) ^ 21 / 4 ^ d) := hsum
      _ = (64 * γ ^ 7 * N) * ∑ d ∈ Finset.range D, ((d : ℝ) + 1) ^ 21 / 4 ^ d := hfac
      _ ≤ (64 * γ ^ 7 * N) * ((202 : ℝ) ^ 21 * 2) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
      _ = 64 * γ ^ 7 * ((202 : ℝ) ^ 21 * 2) * N := by ring
  -- assemble: the recursion summed over the levels, with the RHS split
  have hsteps := Finset.sum_le_sum (fun d (_ : d ∈ Finset.range D) => hstep d)
  have hsplit : (∑ d ∈ Finset.range D,
      (10 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 * Real.sqrt (m d * n d)) +
        4 * m d / (γ * ((d : ℝ) + 1) ^ 3) +
          (2 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2) + (γ * ((d : ℝ) + 1) ^ 3) +
            64 * (γ * ((d : ℝ) + 1) ^ 3) ^ 7) * n d)) =
      (∑ d ∈ Finset.range D,
          10 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 * Real.sqrt (m d * n d))) +
        (∑ d ∈ Finset.range D, 4 * m d / (γ * ((d : ℝ) + 1) ^ 3)) +
          (∑ d ∈ Finset.range D,
            (2 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2) + (γ * ((d : ℝ) + 1) ^ 3) +
              64 * (γ * ((d : ℝ) + 1) ^ 3) ^ 7) * n d) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hsplit2 : (∑ d ∈ Finset.range D,
      (2 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2) + (γ * ((d : ℝ) + 1) ^ 3) +
        64 * (γ * ((d : ℝ) + 1) ^ 3) ^ 7) * n d) =
      (∑ d ∈ Finset.range D, 2 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2) * n d) +
        (∑ d ∈ Finset.range D, (γ * ((d : ℝ) + 1) ^ 3) * n d) +
          (∑ d ∈ Finset.range D, 64 * (γ * ((d : ℝ) + 1) ^ 3) ^ 7 * n d) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun d _ => by ring)
  have hmain : (∑ d ∈ Finset.range D, m (d + 1)) ≤
      10 * (γ ^ 2 * 40000 * Real.sqrt (M * N)) + (4 / γ) * (∑ d ∈ Finset.range D, m d) +
        (2 * (40000 * γ ^ 2) * N + 40000 * γ * N + 64 * γ ^ 7 * ((202 : ℝ) ^ 21 * 2) * N) := by
    have h1 : (∑ d ∈ Finset.range D, m (d + 1)) ≤
        (∑ d ∈ Finset.range D,
          10 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 * Real.sqrt (m d * n d))) +
          (∑ d ∈ Finset.range D, 4 * m d / (γ * ((d : ℝ) + 1) ^ 3)) +
            (∑ d ∈ Finset.range D,
              (2 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2) + (γ * ((d : ℝ) + 1) ^ 3) +
                64 * (γ * ((d : ℝ) + 1) ^ 3) ^ 7) * n d) := by
      rw [← hsplit]
      exact hsteps
    rw [hsplit2] at h1
    linarith [hA, hB, h1, hC1, hC2, hC3]
  -- the shift `Σ m(d+1) = Σ m d − M + m D`
  have hshift : (∑ d ∈ Finset.range D, m (d + 1)) =
      (∑ d ∈ Finset.range D, m d) - M + m D := by
    have h1 : (∑ k ∈ Finset.range (D + 1), m k) =
        (∑ k ∈ Finset.range D, m (k + 1)) + m 0 := Finset.sum_range_succ' (f := m) D
    have h2 : (∑ k ∈ Finset.range (D + 1), m k) =
        (∑ k ∈ Finset.range D, m k) + m D := by
      rw [Finset.sum_range_succ]
    rw [hm0] at h1
    linarith
  have hSD : (∑ d ∈ Finset.range D, m d) - M ≤ (∑ d ∈ Finset.range D, m (d + 1)) := by
    rw [hshift]
    linarith [hmnn D]
  have hSnonneg : (0 : ℝ) ≤ ∑ d ∈ Finset.range D, m d :=
    Finset.sum_nonneg (fun d _ => hmnn d)
  have hquarter : (4 / γ) * (∑ d ∈ Finset.range D, m d) ≤
      (1 / 4) * (∑ d ∈ Finset.range D, m d) := by
    apply mul_le_mul_of_nonneg_right _ hSnonneg
    rw [div_le_iff₀ hγ0]
    linarith
  have hS : (∑ d ∈ Finset.range D, m d) ≤
      4 / 3 * (M + (10 * (γ ^ 2 * 40000 * Real.sqrt (M * N)) +
        (64 * γ ^ 7 * ((202 : ℝ) ^ 21 * 2) + 2 * (40000 * γ ^ 2) + 40000 * γ) * N)) := by
    linarith [hmain, hSD, hquarter]
  -- the vertex total
  have hV : (∑ d ∈ Finset.range D, n d) ≤ 4 / 3 * N := by
    refine level_verts_summable (n := n) (N := N) hN ?_ D
    intro d
    have hdiv : N * (1 / 4 : ℝ) ^ d = N / (4 : ℝ) ^ d := by
      rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, inv_pow, div_eq_mul_inv]
    rw [hdiv]
    exact hnd d
  rw [Finset.sum_add_distrib]
  linarith [hV, hS]

set_option maxHeartbeats 1000000 in
/-- **§3.6's total work, from the per-call counts alone.**  Per call at depth `d`: the retained set
obeys `|U| ≤ 10t_d²√(m n) + 4m/t_d` and the children receive at most
`|U| + 2t_d²(n−1) + t_d(n−1+r_d²n)` edges (`t_d = γ(d+1)³`, `r_d = 8t_d³`, `γ ≥ 16`).  Then the
strategy's chain has *linear* total work: for every depth `D`,
`Σ_{d<D} (|V_d| + |E_d|) ≤ (4/3)|P| + (4/3)(|E₀| + R)` with
`R = 10γ²·40000·√(|P||E₀|) + (64γ⁷·202²¹·2 + 2·40000γ² + 40000γ)|P|`.
The level-growing coefficients `γ²(d+1)⁶`, `γ⁷(d+1)²¹` are absorbed by the `4^{-d}` vertex decay —
no level-uniform `C`, no edge halving, no `htd`. -/
theorem chain_work_linear_counts (P : Finset V) (E₀ : Finset E) (S : Strategy G)
    (hS : Strategy.Wf S) {γ : ℝ} (hγ : 16 ≤ γ)
    (hU : ∀ (d : ℕ), ∀ a ∈ (Level.chain P E₀ S hS d).insts,
      (((S a.1 a.2).2.U).card : ℝ) ≤
        10 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 *
            Real.sqrt ((a.2.card : ℝ) * (a.1.card : ℝ))) +
          4 * (a.2.card : ℝ) / (γ * ((d : ℝ) + 1) ^ 3))
    (hrnd : ∀ (d : ℕ), ∀ a ∈ (Level.chain P E₀ S hS d).insts,
      ((∑ i, ((S a.1 a.2).2.kidE i).card : ℕ) : ℝ) ≤
        (((S a.1 a.2).2.U).card : ℝ) +
          2 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 * (((a.1.card - 1 : ℕ) : ℝ))) +
            (γ * ((d : ℝ) + 1) ^ 3) *
              ((((a.1.card - 1 : ℕ) : ℝ)) +
                (8 * (γ * ((d : ℝ) + 1) ^ 3) ^ 3) ^ 2 * (a.1.card : ℝ))) :
    ∀ D : ℕ, (∑ d ∈ Finset.range D,
        (((Level.chain P E₀ S hS d).verts : ℝ) +
          ((Level.chain P E₀ S hS d).edges : ℝ))) ≤
      4 / 3 * (P.card : ℝ) + 4 / 3 * ((E₀.card : ℝ) +
        (10 * (γ ^ 2 * 40000 * Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ))) +
          (64 * γ ^ 7 * ((202 : ℝ) ^ 21 * 2) + 2 * (40000 * γ ^ 2) + 40000 * γ) *
            (P.card : ℝ))) := by
  classical
  have hverts : ∀ d : ℕ,
      ((Level.chain P E₀ S hS d).verts : ℝ) * (4 : ℝ) ^ d ≤ (P.card : ℝ) := by
    intro d
    have h := LevelChain.verts (L := Level.chain P E₀ S hS)
      (LevelChain.chain_step P E₀ S hS) (LevelChain.chain_verts P E₀ S hS) d
    exact_mod_cast h
  exact level_work_poly (m := fun d => ((Level.chain P E₀ S hS d).edges : ℝ))
    (n := fun d => ((Level.chain P E₀ S hS d).verts : ℝ))
    (M := (E₀.card : ℝ)) (N := (P.card : ℝ)) (γ := γ)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hγ hverts
    (fun d => chain_edges_cast_le P E₀ S hS d)
    (by
      show ((Level.chain P E₀ S hS 0).edges : ℝ) = (E₀.card : ℝ)
      rw [LevelChain.chain_edges])
    (fun d => Nat.cast_nonneg _) (fun d => Nat.cast_nonneg _)
    (chain_edges_display P E₀ S hS hγ hU hrnd)

/-- **Bounded-depth hypotheses suffice.**  The paper's per-call counts are asserted along the
recursion only as deep as the edge count allows (`d ≤ |E₀|`), which is the form all of
`display_of_strategy_of_calls_count`/`display_of_strategy_of_counts` take.  Strict decrease plus the
leaf condition make every deeper level empty (`LevelChain.chain_insts_empty_of_le`), so an
instance-free statement holds there vacuously. -/
theorem forall_chain_of_le_card (P : Finset V) (E₀ : Finset E) (S : Strategy G) (hS : Strategy.Wf S)
    (hstr : Strategy.Strict S) (hleaf : Strategy.Leaf S) {Q : ℕ → Inst V E → Prop}
    (h : ∀ d, d ≤ E₀.card → ∀ a ∈ (Level.chain P E₀ S hS d).insts, Q d a) :
    ∀ d, ∀ a ∈ (Level.chain P E₀ S hS d).insts, Q d a := by
  intro d
  by_cases hd : d ≤ E₀.card
  · exact h d hd
  · have hempty := LevelChain.chain_insts_empty_of_le P E₀ S hS hstr hleaf d (by omega)
    intro a ha
    rw [hempty] at ha
    simp at ha

/-- **§3.6's total work, with the counts asserted only down to depth `|E₀|`.**  The paper states its
per-call estimates along the recursion where there are calls to make; `chain_work_linear_counts`
asks for them at every level.  `forall_chain_of_le_card` bridges the two (strict decrease + leaf
empty out the deeper levels), so the linear total-work bound follows from exactly the premises of
`display_of_strategy_of_calls_count`: the two quantitative outputs of one call, at the level's own
`t_d = γ(d+1)³`. -/
theorem chain_work_linear_of_counts_bounded (P : Finset V) (E₀ : Finset E) (S : Strategy G)
    (hS : Strategy.Wf S) (hstr : Strategy.Strict S) (hleaf : Strategy.Leaf S)
    {γ : ℝ} (hγ : 16 ≤ γ)
    (hU : ∀ d, d ≤ E₀.card → ∀ a ∈ (Level.chain P E₀ S hS d).insts,
      (((S a.1 a.2).2.U).card : ℝ) ≤
        10 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 *
            Real.sqrt ((a.2.card : ℝ) * (a.1.card : ℝ))) +
          4 * (a.2.card : ℝ) / (γ * ((d : ℝ) + 1) ^ 3))
    (hrnd : ∀ d, d ≤ E₀.card → ∀ a ∈ (Level.chain P E₀ S hS d).insts,
      ((∑ i, ((S a.1 a.2).2.kidE i).card : ℕ) : ℝ) ≤
        (((S a.1 a.2).2.U).card : ℝ) +
          2 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 * (((a.1.card - 1 : ℕ) : ℝ))) +
            (γ * ((d : ℝ) + 1) ^ 3) *
              ((((a.1.card - 1 : ℕ) : ℝ)) +
                (8 * (γ * ((d : ℝ) + 1) ^ 3) ^ 3) ^ 2 * (a.1.card : ℝ))) :
    ∀ D : ℕ, (∑ d ∈ Finset.range D,
        (((Level.chain P E₀ S hS d).verts : ℝ) +
          ((Level.chain P E₀ S hS d).edges : ℝ))) ≤
      4 / 3 * (P.card : ℝ) + 4 / 3 * ((E₀.card : ℝ) +
        (10 * (γ ^ 2 * 40000 * Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ))) +
          (64 * γ ^ 7 * ((202 : ℝ) ^ 21 * 2) + 2 * (40000 * γ ^ 2) + 40000 * γ) *
            (P.card : ℝ))) :=
  chain_work_linear_counts P E₀ S hS hγ
    (forall_chain_of_le_card P E₀ S hS hstr hleaf hU)
    (forall_chain_of_le_card P E₀ S hS hstr hleaf hrnd)

/-- **The p. 24 input count's polynomial consequence.**  If the child total obeys the paper's
count with the honest natural-number subtraction `(n−1:ℕ) ≤ n`, then it is bounded by
`errF + A·(d+1)²¹·n` with `A = 2γ² + γ + 64γ⁷`, which is the form the level accounting consumes
(`display_of_strategy_of_calls_poly_coef`).  The two `(d+1)` powers `3` and `6` are dominated by
`21` because `d+1 ≥ 1`. -/
theorem input_poly_of_nat {γ B u n : ℝ} (hγ1 : 1 ≤ γ) (hB1 : 1 ≤ B)
    (hu0 : 0 ≤ u) (hn : 0 ≤ n) (hun : u ≤ n) :
    2 * ((γ * B ^ 3) ^ 2 * u) + (γ * B ^ 3) * (u + (8 * (γ * B ^ 3) ^ 3) ^ 2 * n) ≤
      (2 * γ ^ 2 + γ + 64 * γ ^ 7) * B ^ 21 * n := by
  have hγ0 : (0 : ℝ) ≤ γ := le_trans zero_le_one hγ1
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  have hB3 : B ^ 3 ≤ B ^ 21 := pow_le_pow_right₀ hB1 (by norm_num)
  have hB6 : B ^ 6 ≤ B ^ 21 := pow_le_pow_right₀ hB1 (by norm_num)
  have hB32 : (B ^ 3) ^ 2 ≤ B ^ 21 := by
    calc (B ^ 3) ^ 2 = B ^ 6 := by ring
      _ ≤ B ^ 21 := hB6
  have hsq : (γ * B ^ 3) ^ 2 ≤ γ ^ 2 * B ^ 21 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hB32 (pow_nonneg hγ0 2)
  have h1 : 2 * ((γ * B ^ 3) ^ 2 * u) ≤ 2 * γ ^ 2 * B ^ 21 * n := by
    have hstep : (2 * (γ * B ^ 3) ^ 2) * u ≤ (2 * (γ ^ 2 * B ^ 21)) * n :=
      mul_le_mul (mul_le_mul_of_nonneg_left hsq (by norm_num)) hun hu0 (by positivity)
    calc 2 * ((γ * B ^ 3) ^ 2 * u) = (2 * (γ * B ^ 3) ^ 2) * u := by ring
      _ ≤ (2 * (γ ^ 2 * B ^ 21)) * n := hstep
      _ = 2 * γ ^ 2 * B ^ 21 * n := by ring
  have h2 : (γ * B ^ 3) * u ≤ γ * B ^ 21 * n := by
    have hTu : (γ * B ^ 3) * u ≤ (γ * B ^ 3) * n :=
      mul_le_mul_of_nonneg_left hun (mul_nonneg hγ0 (pow_nonneg hB0 3))
    have hBn : (γ * B ^ 3) * n ≤ (γ * B ^ 21) * n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB3 hγ0) hn
    calc (γ * B ^ 3) * u ≤ (γ * B ^ 3) * n := hTu
      _ ≤ (γ * B ^ 21) * n := hBn
      _ = γ * B ^ 21 * n := by ring
  have h3 : (γ * B ^ 3) * ((8 * (γ * B ^ 3) ^ 3) ^ 2 * n) = 64 * γ ^ 7 * B ^ 21 * n := by
    ring
  have hsum := add_le_add (add_le_add h1 h2) (le_of_eq h3)
  have hsplit : 2 * ((γ * B ^ 3) ^ 2 * u) +
      (γ * B ^ 3) * (u + (8 * (γ * B ^ 3) ^ 3) ^ 2 * n) =
      2 * ((γ * B ^ 3) ^ 2 * u) + (γ * B ^ 3) * u +
        (γ * B ^ 3) * ((8 * (γ * B ^ 3) ^ 3) ^ 2 * n) := by ring
  have hcoef : 2 * γ ^ 2 * B ^ 21 * n + γ * B ^ 21 * n + 64 * γ ^ 7 * B ^ 21 * n =
      (2 * γ ^ 2 + γ + 64 * γ ^ 7) * B ^ 21 * n := by ring
  rw [hsplit, ← hcoef]
  exact hsum

set_option maxHeartbeats 1000000 in
/-- **The display from the p. 24 count in natural-number subtraction.**  `display_of_strategy_of_counts`
reads the paper's `n−1` as a real subtraction, which is unsatisfiable for the degenerate `(∅, ∅)`
instances `Level.allChildren` produces (`n − 1 = −1` there); the honest form is `((n−1:ℕ):ℝ) ≤ n`.
`input_poly_of_nat` converts that count into the degree-`21` input account, so the display holds
with the same constant and no nonemptiness premise. -/
theorem display_of_strategy_of_nat_counts (P : Finset V) (E₀ : Finset E) (S : Strategy G)
    (hS : Strategy.Wf S)
    {γ ε : ℝ} (hγ1 : 1 ≤ γ) (hε : 0 < ε) (hγε : 16 ≤ ε * γ)
    (hnm : ((S P E₀).2.P.card : ℝ) ≤ 2 * ((S P E₀).2.E₀.card : ℝ))
    (herrU : ∀ d, d ≤ E₀.card → ∀ a ∈ (Level.chain P E₀ S hS d).insts,
      (((S a.1 a.2).2.U).card : ℝ) ≤
        10 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 * Real.sqrt ((a.2.card : ℝ) * (a.1.card : ℝ))) +
          4 * (a.2.card : ℝ) / (γ * ((d : ℝ) + 1) ^ 3))
    (hrounds : ∀ d, d ≤ E₀.card → ∀ a ∈ (Level.chain P E₀ S hS d).insts,
      ((∑ i, ((S a.1 a.2).2.kidE i).card : ℕ) : ℝ) ≤
        (((S a.1 a.2).2.U).card : ℝ) +
          2 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 * (((a.1.card - 1 : ℕ) : ℝ))) +
            (γ * ((d : ℝ) + 1) ^ 3) *
              ((((a.1.card - 1 : ℕ) : ℝ)) +
                (8 * (γ * ((d : ℝ) + 1) ^ 3) ^ 3) ^ 2 * (a.1.card : ℝ))) :
    ((S P E₀).2.F.card : ℝ) + (((S P E₀).2.U).card : ℝ) +
        ((∑ i, ((S P E₀).2.kidE i).card : ℕ) : ℝ) ≤
      ε * ((S P E₀).2.E₀.card : ℝ) +
        (Real.sqrt 2 + γ ^ 2 * 800000 +
            Real.sqrt 2 * ((2 * γ ^ 2 + γ + 64 * γ ^ 7) * ((202 : ℝ) ^ 21 * 2))) *
          Real.sqrt (((S P E₀).2.E₀.card : ℝ) * ((S P E₀).2.P.card : ℝ)) := by
  have hγ0 : (0 : ℝ) < γ := by linarith
  have hA : (0 : ℝ) ≤ 2 * γ ^ 2 + γ + 64 * γ ^ 7 := by
    have h0 : (0 : ℝ) ≤ γ := le_of_lt hγ0
    have h2 : (0 : ℝ) ≤ γ ^ 2 := pow_nonneg h0 2
    have h7 : (0 : ℝ) ≤ γ ^ 7 := pow_nonneg h0 7
    linarith
  have hinF : ∀ d, d ≤ E₀.card → ∀ a ∈ (Level.chain P E₀ S hS d).insts,
      ((∑ i, ((S a.1 a.2).2.kidE i).card : ℕ) : ℝ) ≤
        (((S a.1 a.2).2.U).card : ℝ) +
          (2 * γ ^ 2 + γ + 64 * γ ^ 7) * ((d : ℝ) + 1) ^ 21 * (a.1.card : ℝ) := by
    intro d hd a ha
    have h := hrounds d hd a ha
    have hstep := input_poly_of_nat (γ := γ) (B := (d : ℝ) + 1)
      (u := ((a.1.card - 1 : ℕ) : ℝ)) (n := (a.1.card : ℝ))
      hγ1 (by linarith [show (0 : ℝ) ≤ (d : ℝ) from Nat.cast_nonneg d])
      (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (by
        have hcd : ((a.1.card - 1 : ℕ) : ℝ) ≤ (a.1.card : ℝ) :=
          Nat.cast_le.mpr (Nat.sub_le a.1.card 1)
        exact hcd)
    linarith
  have key := display_of_strategy_of_calls_poly_coef P E₀ S hS
    (γ := γ) (ε := ε) (A := 2 * γ ^ 2 + γ + 64 * γ ^ 7) (K := 10)
    hγ0 hε hγε hA (by norm_num) hnm
    (fun a => ((S a.1 a.2).2.U).card)
    (fun a => ∑ i, ((S a.1 a.2).2.kidE i).card)
    herrU hinF (fun _ _ _ _ => le_refl _) (fun _ _ _ _ => le_refl _)
  rw [show γ ^ 2 * (80000 * (10 : ℝ)) = γ ^ 2 * 800000 by norm_num] at key
  exact key

/-- **§3.6 end to end from the two numeric outputs of one call.**  Per instance down to depth
`|E₀|`: the retained set `|U| ≤ 10t_d²√(mn) + 4m/t_d` and the p. 24 input count
`Σ|Eᵢ| ≤ |U| + 2t_d²(n−1) + t_d(n−1+r_d²n)` in natural-number subtraction (`r_d = 8t_d³`).
Then **both** §3.6 conclusions hold simultaneously: the root's display (with `ε` and
`C_ε = √2 + γ²·800000 + √2(2γ²+γ+64γ⁷)·202²¹·2`, via `display_of_strategy_of_nat_counts`),
**and** linear total work over all levels (with constant `4/3·(|E₀| + R) + 4/3·|P|`, via
`chain_work_linear_of_counts_bounded`).  The two conclusions consume the identical premise set —
no nonemptiness assumption is needed on the instances. -/
theorem strategy_display_and_work (P : Finset V) (E₀ : Finset E) (S : Strategy G)
    (hS : Strategy.Wf S) (hstr : Strategy.Strict S) (hleaf : Strategy.Leaf S)
    {γ ε : ℝ} (hγ1 : 1 ≤ γ) (hγ16 : 16 ≤ γ) (hε : 0 < ε) (hγε : 16 ≤ ε * γ)
    (hnm : ((S P E₀).2.P.card : ℝ) ≤ 2 * ((S P E₀).2.E₀.card : ℝ))
    (herrU : ∀ d, d ≤ E₀.card → ∀ a ∈ (Level.chain P E₀ S hS d).insts,
      (((S a.1 a.2).2.U).card : ℝ) ≤
        10 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 *
            Real.sqrt ((a.2.card : ℝ) * (a.1.card : ℝ))) +
          4 * (a.2.card : ℝ) / (γ * ((d : ℝ) + 1) ^ 3))
    (hrounds : ∀ d, d ≤ E₀.card → ∀ a ∈ (Level.chain P E₀ S hS d).insts,
      ((∑ i, ((S a.1 a.2).2.kidE i).card : ℕ) : ℝ) ≤
        (((S a.1 a.2).2.U).card : ℝ) +
          2 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 * (((a.1.card - 1 : ℕ) : ℝ))) +
            (γ * ((d : ℝ) + 1) ^ 3) *
              ((((a.1.card - 1 : ℕ) : ℝ)) +
                (8 * (γ * ((d : ℝ) + 1) ^ 3) ^ 3) ^ 2 * (a.1.card : ℝ))) :
    (((S P E₀).2.F.card : ℝ) + (((S P E₀).2.U).card : ℝ) +
        ((∑ i, ((S P E₀).2.kidE i).card : ℕ) : ℝ) ≤
      ε * ((S P E₀).2.E₀.card : ℝ) +
        (Real.sqrt 2 + γ ^ 2 * 800000 +
            Real.sqrt 2 * ((2 * γ ^ 2 + γ + 64 * γ ^ 7) * ((202 : ℝ) ^ 21 * 2))) *
          Real.sqrt (((S P E₀).2.E₀.card : ℝ) * ((S P E₀).2.P.card : ℝ))) ∧
      ∀ D : ℕ, (∑ d ∈ Finset.range D,
        (((Level.chain P E₀ S hS d).verts : ℝ) +
          ((Level.chain P E₀ S hS d).edges : ℝ))) ≤
        4 / 3 * (P.card : ℝ) + 4 / 3 * ((E₀.card : ℝ) +
          (10 * (γ ^ 2 * 40000 * Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ))) +
            (64 * γ ^ 7 * ((202 : ℝ) ^ 21 * 2) + 2 * (40000 * γ ^ 2) + 40000 * γ) *
              (P.card : ℝ))) := by
  exact ⟨display_of_strategy_of_nat_counts P E₀ S hS hγ1 hε hγε hnm herrU hrounds,
    chain_work_linear_of_counts_bounded P E₀ S hS hstr hleaf hγ16 herrU hrounds⟩

end DLMST