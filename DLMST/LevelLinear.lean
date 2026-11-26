import DLMST.Procedure

/-!
# §3.6's linear total work on the level chain

The tower (`LinearTime.lean`) rescans `E₀` at every level, so its own account is `d·m`; §3.6's
procedure does not.  Each call hands its children only the edges that leave its forest, the *vertex*
totals shrink by `4` per level (`Step.shrink`, the paper's `t²·2nt/r = n/4`), and the display
`m_{d+1} ≤ ε·m_d + C·√(m_d·n_d)` holds at every level.  The geometric decay of `n_d` makes the `√`
term summable, so the **total** work `Σ_d (n_d + m_d)` is linear — with no per-level edge halving
anywhere.

This is the paper's actual linear accounting (total size of all subinstances over all levels), unlike
the tower's count.  The arithmetic core is `level_edges_summable`/`level_verts_summable`/
`level_work_linear`; `chain_verts_cast_le`/`chain_edges_cast_le` read the measure on the strategy's
own chain, and `chain_work_linear` is the resulting statement.  The per-level display is the numeric
output of §3.1–§3.5; `Procedure.errors_gather`/`inputs_gather` turn per-call bounds into it.
-/

namespace DLMST

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

/-! ## The arithmetic core -/

/-- **Edge totals are summable.**  If `m_d ≤ M`, `n_d ≤ N·4^{-d}`, and every level satisfies the
display `m_{d+1} ≤ ε·m_d + C·√(m_d·n_d)` with `ε ≤ 1/4`, then the edge totals over all levels sum to
at most `M/(1-ε) + 8·C·√(M·N)`.  The `8` is the induction constant `4` times `Σ 2^{-d} ≤ 2`. -/
theorem level_edges_summable {m n : ℕ → ℝ} {M N ε C : ℝ}
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hC : 0 ≤ C) (hε0 : 0 ≤ ε) (hε4 : ε ≤ 1 / 4)
    (hm0 : m 0 = M) (hmM : ∀ d, m d ≤ M)
    (hnle : ∀ d, n d ≤ N * (1 / 4 : ℝ) ^ d) (hnnn : ∀ d, 0 ≤ n d)
    (hdisp : ∀ d, m (d + 1) ≤ ε * m d + C * Real.sqrt (m d * n d)) :
    ∀ D : ℕ, (∑ d ∈ Finset.range D, m d) ≤ M / (1 - ε) + 8 * C * Real.sqrt (M * N) := by
  have hMN : 0 ≤ M * N := mul_nonneg hM hN
  have hsMN : 0 ≤ Real.sqrt (M * N) := Real.sqrt_nonneg _
  have hsq : ∀ d : ℕ, (1 / 4 : ℝ) ^ d = ((1 / 2 : ℝ) ^ d) ^ 2 := by
    intro d
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, ← pow_mul, mul_comm 2 d, pow_mul]
  have hsqrt : ∀ d, Real.sqrt (m d * n d) ≤ Real.sqrt (M * N) * (1 / 2 : ℝ) ^ d := by
    intro d
    have hmn : m d * n d ≤ M * N * ((1 / 2 : ℝ) ^ d) ^ 2 := by
      calc m d * n d ≤ M * (N * (1 / 4 : ℝ) ^ d) :=
            mul_le_mul (hmM d) (hnle d) (hnnn d) hM
        _ = M * N * (1 / 4 : ℝ) ^ d := by ring
        _ = M * N * ((1 / 2 : ℝ) ^ d) ^ 2 := by rw [hsq]
    calc Real.sqrt (m d * n d) ≤ Real.sqrt (M * N * ((1 / 2 : ℝ) ^ d) ^ 2) :=
          Real.sqrt_le_sqrt hmn
      _ = Real.sqrt (M * N) * (1 / 2 : ℝ) ^ d := by
          rw [Real.sqrt_mul hMN, Real.sqrt_sq (pow_nonneg (by norm_num) d)]
  have hC0 : 0 ≤ C * Real.sqrt (M * N) := mul_nonneg hC hsMN
  have hbound : ∀ d, m d ≤ ε ^ d * M + 4 * C * Real.sqrt (M * N) * (1 / 2 : ℝ) ^ d := by
    intro d
    induction d with
    | zero =>
        rw [hm0]
        have hA : 0 ≤ 4 * C * Real.sqrt (M * N) := by
          have := mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hC0
          linarith
        simpa using add_le_add_left hA M
    | succ d ih =>
        have hstep := hdisp d
        have hs := hsqrt d
        have hpow : (1 / 2 : ℝ) ^ (d + 1) = (1 / 2 : ℝ) ^ d / 2 := by
          rw [pow_succ]; ring
        have hεd : 0 ≤ ε ^ d * M := mul_nonneg (pow_nonneg hε0 d) hM
        have hA : 0 ≤ C * Real.sqrt (M * N) * (1 / 2 : ℝ) ^ d :=
          mul_nonneg hC0 (pow_nonneg (by norm_num) d)
        have h1 : ε * m d ≤ ε * (ε ^ d * M + 4 * C * Real.sqrt (M * N) * (1 / 2 : ℝ) ^ d) :=
          mul_le_mul_of_nonneg_left ih hε0
        have h2 : C * Real.sqrt (m d * n d) ≤ C * (Real.sqrt (M * N) * (1 / 2 : ℝ) ^ d) :=
          mul_le_mul_of_nonneg_left hs hC
        have h3 : ε * (ε ^ d * M + 4 * C * Real.sqrt (M * N) * (1 / 2 : ℝ) ^ d) +
              C * (Real.sqrt (M * N) * (1 / 2 : ℝ) ^ d) =
            ε ^ (d + 1) * M + (4 * ε + 1) * C * Real.sqrt (M * N) * (1 / 2 : ℝ) ^ d := by
          rw [pow_succ]; ring
        have h4 : (4 * ε + 1) * C * Real.sqrt (M * N) * (1 / 2 : ℝ) ^ d ≤
            4 * C * Real.sqrt (M * N) * (1 / 2 : ℝ) ^ (d + 1) := by
          rw [hpow]
          nlinarith [hA, hε4]
        calc m (d + 1) ≤ ε * m d + C * Real.sqrt (m d * n d) := hstep
          _ ≤ ε * (ε ^ d * M + 4 * C * Real.sqrt (M * N) * (1 / 2 : ℝ) ^ d) +
                C * (Real.sqrt (M * N) * (1 / 2 : ℝ) ^ d) := by linarith
          _ = ε ^ (d + 1) * M + (4 * ε + 1) * C * Real.sqrt (M * N) * (1 / 2 : ℝ) ^ d := h3
          _ ≤ ε ^ (d + 1) * M + 4 * C * Real.sqrt (M * N) * (1 / 2 : ℝ) ^ (d + 1) := by
              linarith
  intro D
  have hg1 : (0 : ℝ) ≤ ε ^ (0 : ℕ) * M := by simpa using hM
  have h1 : (∑ d ∈ Finset.range D, ε ^ d * M) ≤ M / (1 - ε) := by
    have h := geom_sum_le (g := fun d => ε ^ d * M) (c := ε) hg1 hε0 (by linarith)
      (fun k => by
        have hh : ε ^ (k + 1) * M = ε * (ε ^ k * M) := by rw [pow_succ]; ring
        exact le_of_eq hh) D
    have h0 : ε ^ (0 : ℕ) * M = M := by rw [pow_zero, one_mul]
    rwa [h0] at h
  have hg2 : (0 : ℝ) ≤ 4 * C * Real.sqrt (M * N) * (1 / 2 : ℝ) ^ (0 : ℕ) := by
    have h2 : (0 : ℝ) ≤ 4 * C * Real.sqrt (M * N) :=
      mul_nonneg (mul_nonneg (by norm_num) hC) hsMN
    simpa using h2
  have h2 : (∑ d ∈ Finset.range D, 4 * C * Real.sqrt (M * N) * (1 / 2 : ℝ) ^ d)
      ≤ 8 * C * Real.sqrt (M * N) := by
    have h := geom_sum_le (g := fun d => 4 * C * Real.sqrt (M * N) * (1 / 2 : ℝ) ^ d)
      (c := 1 / 2) hg2 (by norm_num) (by norm_num)
      (fun k => by
        have hh : 4 * C * Real.sqrt (M * N) * (1 / 2 : ℝ) ^ (k + 1) =
            1 / 2 * (4 * C * Real.sqrt (M * N) * (1 / 2 : ℝ) ^ k) := by
          rw [pow_succ]; ring
        exact le_of_eq hh) D
    have hden : 4 * C * Real.sqrt (M * N) * (1 / 2 : ℝ) ^ (0 : ℕ) / (1 - 1 / 2) =
        8 * C * Real.sqrt (M * N) := by
      ring
    rwa [hden] at h
  calc (∑ d ∈ Finset.range D, m d)
      ≤ ∑ d ∈ Finset.range D, (ε ^ d * M + 4 * C * Real.sqrt (M * N) * (1 / 2 : ℝ) ^ d) :=
        Finset.sum_le_sum (fun d _ => hbound d)
    _ = (∑ d ∈ Finset.range D, ε ^ d * M) +
          ∑ d ∈ Finset.range D, 4 * C * Real.sqrt (M * N) * (1 / 2 : ℝ) ^ d :=
        Finset.sum_add_distrib
    _ ≤ M / (1 - ε) + 8 * C * Real.sqrt (M * N) := by linarith

/-- **Vertex totals are summable** — this uses only the quartering, no display: `n_d ≤ N·4^{-d}`
gives `Σ_d n_d ≤ 4N/3`. -/
theorem level_verts_summable {n : ℕ → ℝ} {N : ℝ} (hN : 0 ≤ N)
    (hnle : ∀ d, n d ≤ N * (1 / 4 : ℝ) ^ d) :
    ∀ D : ℕ, (∑ d ∈ Finset.range D, n d) ≤ 4 / 3 * N := by
  intro D
  have h := geom_sum_le (g := fun d => N * (1 / 4 : ℝ) ^ d) (c := 1 / 4)
    (by simpa using hN) (by norm_num) (by norm_num)
    (fun k => by
      have hh : N * (1 / 4 : ℝ) ^ (k + 1) = 1 / 4 * (N * (1 / 4 : ℝ) ^ k) := by
        rw [pow_succ]; ring
      exact le_of_eq hh) D
  have h0 : N * (1 / 4 : ℝ) ^ (0 : ℕ) = N := by rw [pow_zero, mul_one]
  rw [h0] at h
  have hden : N / (1 - 1 / 4) = 4 / 3 * N := by ring
  calc (∑ d ∈ Finset.range D, n d) ≤ ∑ d ∈ Finset.range D, N * (1 / 4 : ℝ) ^ d :=
        Finset.sum_le_sum (fun d _ => hnle d)
    _ ≤ N / (1 - 1 / 4) := h
    _ = 4 / 3 * N := hden

/-- **Total work is linear in the level model.**  Summing the two bounds and using the paper's
`N ≤ 2M`: `Σ_d (n_d + m_d) ≤ (8/3 + 1/(1-ε) + 8√2·C)·(N + M)`. -/
theorem level_work_linear {m n : ℕ → ℝ} {M N ε C : ℝ}
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hC : 0 ≤ C) (hε0 : 0 ≤ ε) (hε4 : ε ≤ 1 / 4)
    (hnm : N ≤ 2 * M)
    (hm0 : m 0 = M) (hmM : ∀ d, m d ≤ M)
    (hnle : ∀ d, n d ≤ N * (1 / 4 : ℝ) ^ d) (hnnn : ∀ d, 0 ≤ n d)
    (hdisp : ∀ d, m (d + 1) ≤ ε * m d + C * Real.sqrt (m d * n d)) :
    (0 : ℝ) ≤ 8 / 3 + 1 / (1 - ε) + 8 * Real.sqrt 2 * C ∧
      ∀ D : ℕ, (∑ d ∈ Finset.range D, (n d + m d)) ≤
        (8 / 3 + 1 / (1 - ε) + 8 * Real.sqrt 2 * C) * (N + M) := by
  have hpos : (0 : ℝ) < 1 - ε := by linarith
  have hK : 0 ≤ 8 / 3 + 1 / (1 - ε) + 8 * Real.sqrt 2 * C := by
    have h1 : 0 ≤ 1 / (1 - ε) := by positivity
    have h2 : 0 ≤ 8 * Real.sqrt 2 * C :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg 2)) hC
    linarith
  refine ⟨hK, fun D => ?_⟩
  have hE := level_edges_summable hM hN hC hε0 hε4 hm0 hmM hnle hnnn hdisp D
  have hV := level_verts_summable hN hnle D
  have hsqrt2 : Real.sqrt (M * N) ≤ Real.sqrt 2 * M := by
    have h : M * N ≤ M * (2 * M) := mul_le_mul_of_nonneg_left hnm hM
    have hs := Real.sqrt_le_sqrt h
    have h2 : Real.sqrt (M * (2 * M)) = Real.sqrt 2 * M := by
      rw [show M * (2 * M) = 2 * M ^ 2 by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hM]
    linarith
  have hMle : M ≤ N + M := by linarith
  have hsum : (∑ d ∈ Finset.range D, (n d + m d)) =
      (∑ d ∈ Finset.range D, n d) + ∑ d ∈ Finset.range D, m d := Finset.sum_add_distrib
  rw [hsum]
  have hVN : (∑ d ∈ Finset.range D, n d) ≤ 8 / 3 * M := by
    have : 4 / 3 * N ≤ 8 / 3 * M := by linarith
    linarith
  have hEM : (∑ d ∈ Finset.range D, m d) ≤ M / (1 - ε) + 8 * C * (Real.sqrt 2 * M) := by
    have h := mul_le_mul_of_nonneg_left hsqrt2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hC)
    linarith
  have hKM : 8 / 3 * M + (M / (1 - ε) + 8 * C * (Real.sqrt 2 * M)) =
      (8 / 3 + 1 / (1 - ε) + 8 * Real.sqrt 2 * C) * M := by
    field_simp
    ring
  have hstep : (∑ d ∈ Finset.range D, n d) + ∑ d ∈ Finset.range D, m d ≤
      (8 / 3 + 1 / (1 - ε) + 8 * Real.sqrt 2 * C) * M := by
    linarith
  calc (∑ d ∈ Finset.range D, n d) + ∑ d ∈ Finset.range D, m d
      ≤ (8 / 3 + 1 / (1 - ε) + 8 * Real.sqrt 2 * C) * M := hstep
    _ ≤ (8 / 3 + 1 / (1 - ε) + 8 * Real.sqrt 2 * C) * (N + M) :=
        mul_le_mul_of_nonneg_left hMle hK

/-! ## Reading the measure on the strategy's own chain -/

/-- The level's vertex total is at most `|P|·4^{-d}` (`LevelChain.verts`, cast to `ℝ`). -/
theorem chain_verts_cast_le (P : Finset V) (E₀ : Finset E) (S : Strategy G) (hS : Strategy.Wf S)
    (d : ℕ) :
    ((Level.chain P E₀ S hS d).verts : ℝ) ≤ (P.card : ℝ) * (1 / 4 : ℝ) ^ d := by
  have h := LevelChain.verts (L := Level.chain P E₀ S hS)
    (LevelChain.chain_step P E₀ S hS) (LevelChain.chain_verts P E₀ S hS) d
  have h' : ((Level.chain P E₀ S hS d).verts : ℝ) * (4 : ℝ) ^ d ≤ (P.card : ℝ) := by
    exact_mod_cast h
  have h4 : (0 : ℝ) < (4 : ℝ) ^ d := pow_pos (by norm_num) d
  have hdiv : (P.card : ℝ) * (1 / 4 : ℝ) ^ d = (P.card : ℝ) / (4 : ℝ) ^ d := by
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, inv_pow, div_eq_mul_inv]
  rw [hdiv, le_div_iff₀ h4]
  exact h'

/-- The level's edge total is at most `|E₀|` (`LevelChain.edges`, cast to `ℝ`). -/
theorem chain_edges_cast_le (P : Finset V) (E₀ : Finset E) (S : Strategy G) (hS : Strategy.Wf S)
    (d : ℕ) :
    ((Level.chain P E₀ S hS d).edges : ℝ) ≤ (E₀.card : ℝ) := by
  have h := LevelChain.edges (L := Level.chain P E₀ S hS)
    (LevelChain.chain_step P E₀ S hS) (LevelChain.chain_edges P E₀ S hS) d
  exact_mod_cast h

/-- **§3.6's total work is linear on the level chain.**  With the per-level display and the root's
`|P| ≤ 2|E₀|`, the sum over all levels of `(vertices + edges)` is at most a constant times
`|P| + |E₀|`; the constant is `8/3 + 1/(1-ε) + 8√2·C`, and no level-by-level edge halving is used. -/
theorem chain_work_linear (P : Finset V) (E₀ : Finset E) (S : Strategy G)
    (hS : Strategy.Wf S) {ε C : ℝ} (hε0 : 0 ≤ ε) (hε4 : ε ≤ 1 / 4) (hC : 0 ≤ C)
    (hnm : (P.card : ℝ) ≤ 2 * (E₀.card : ℝ))
    (hdisp : ∀ d : ℕ,
      ((Level.chain P E₀ S hS (d + 1)).edges : ℝ) ≤
        ε * ((Level.chain P E₀ S hS d).edges : ℝ) +
          C * Real.sqrt (((Level.chain P E₀ S hS d).edges : ℝ) *
            ((Level.chain P E₀ S hS d).verts : ℝ))) :
    ∀ D : ℕ, (∑ d ∈ Finset.range D,
        (((Level.chain P E₀ S hS d).verts : ℝ) +
          ((Level.chain P E₀ S hS d).edges : ℝ))) ≤
      (8 / 3 + 1 / (1 - ε) + 8 * Real.sqrt 2 * C) * ((P.card : ℝ) + (E₀.card : ℝ)) := by
  have hM : 0 ≤ (E₀.card : ℝ) := Nat.cast_nonneg _
  have hN : 0 ≤ (P.card : ℝ) := Nat.cast_nonneg _
  have hm0 : ((Level.chain P E₀ S hS 0).edges : ℝ) = (E₀.card : ℝ) := by
    rw [LevelChain.chain_edges]
  have hwork := level_work_linear (m := fun d => ((Level.chain P E₀ S hS d).edges : ℝ))
    (n := fun d => ((Level.chain P E₀ S hS d).verts : ℝ))
    (M := (E₀.card : ℝ)) (N := (P.card : ℝ)) hM hN hC hε0 hε4 hnm
    hm0 (fun d => chain_edges_cast_le P E₀ S hS d)
    (fun d => chain_verts_cast_le P E₀ S hS d) (fun d => Nat.cast_nonneg _) hdisp
  exact hwork.2

set_option maxHeartbeats 1000000 in
/-- **The per-level display follows from the per-instance display.**  If every call's children total
obeys `Σ|kidE| ≤ ε·|E| + C·√(|E|·|P|)` with the *same* `ε, C` — the paper's "the same procedure runs
on every subproblem" — then the strategy's chain satisfies the display at every level.  The level
total is `chain_edges_succ`, and the square roots combine by Cauchy–Schwarz on the level's instances.
This is where §3.6's per-node numeric output (the children-only form of `sum_kidE_le_paper_bound`)
enters `chain_work_linear`. -/
theorem chain_display_of_calls (P : Finset V) (E₀ : Finset E) (S : Strategy G) (hS : Strategy.Wf S)
    {ε C : ℝ} (hC : 0 ≤ C)
    (hcall : ∀ (P' : Finset V) (E₀' : Finset E),
      ((∑ i, ((S P' E₀').2.kidE i).card : ℕ) : ℝ) ≤
        ε * (E₀'.card : ℝ) + C * Real.sqrt ((E₀'.card : ℝ) * (P'.card : ℝ))) :
    ∀ d : ℕ,
      ((Level.chain P E₀ S hS (d + 1)).edges : ℝ) ≤
        ε * ((Level.chain P E₀ S hS d).edges : ℝ) +
          C * Real.sqrt (((Level.chain P E₀ S hS d).edges : ℝ) *
            ((Level.chain P E₀ S hS d).verts : ℝ)) := by
  intro d
  set A := Level.chain P E₀ S hS d with hA
  have hcast : ((Level.chain P E₀ S hS (d + 1)).edges : ℝ) =
      ∑ a ∈ A.insts, ((∑ i, ((S a.1 a.2).2.kidE i).card : ℕ) : ℝ) := by
    rw [LevelChain.chain_edges_succ]
    push_cast
    rfl
  have hEcast : (A.edges : ℝ) = ∑ a ∈ A.insts, (a.2.card : ℝ) := by
    rw [Level.edges]; push_cast; rfl
  have hVcast : (A.verts : ℝ) = ∑ a ∈ A.insts, (a.1.card : ℝ) := by
    rw [Level.verts]; push_cast; rfl
  have hcs : (∑ a ∈ A.insts, Real.sqrt ((a.2.card : ℝ) * (a.1.card : ℝ))) ≤
      Real.sqrt ((A.edges : ℝ) * (A.verts : ℝ)) := by
    have h := Real.sum_sqrt_mul_sqrt_le A.insts
      (f := fun a => (a.2.card : ℝ)) (g := fun a => (a.1.card : ℝ))
      (fun a => Nat.cast_nonneg _) (fun a => Nat.cast_nonneg _)
    have hmul : (∑ a ∈ A.insts, Real.sqrt (a.2.card : ℝ) * Real.sqrt (a.1.card : ℝ)) ≤
        Real.sqrt (∑ a ∈ A.insts, (a.2.card : ℝ)) *
          Real.sqrt (∑ a ∈ A.insts, (a.1.card : ℝ)) := h
    have hjoin : Real.sqrt (∑ a ∈ A.insts, (a.2.card : ℝ)) *
          Real.sqrt (∑ a ∈ A.insts, (a.1.card : ℝ)) =
        Real.sqrt ((∑ a ∈ A.insts, (a.2.card : ℝ)) *
          (∑ a ∈ A.insts, (a.1.card : ℝ))) :=
      (Real.sqrt_mul (Finset.sum_nonneg (fun a _ => Nat.cast_nonneg _)) _).symm
    have hsq : (∑ a ∈ A.insts, Real.sqrt ((a.2.card : ℝ) * (a.1.card : ℝ))) =
        ∑ a ∈ A.insts, Real.sqrt (a.2.card : ℝ) * Real.sqrt (a.1.card : ℝ) := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      exact Real.sqrt_mul (Nat.cast_nonneg _) _
    calc (∑ a ∈ A.insts, Real.sqrt ((a.2.card : ℝ) * (a.1.card : ℝ)))
        = ∑ a ∈ A.insts, Real.sqrt (a.2.card : ℝ) * Real.sqrt (a.1.card : ℝ) := hsq
      _ ≤ Real.sqrt (∑ a ∈ A.insts, (a.2.card : ℝ)) *
            Real.sqrt (∑ a ∈ A.insts, (a.1.card : ℝ)) := hmul
      _ = Real.sqrt ((∑ a ∈ A.insts, (a.2.card : ℝ)) *
            (∑ a ∈ A.insts, (a.1.card : ℝ))) := hjoin
      _ = Real.sqrt ((A.edges : ℝ) * (A.verts : ℝ)) := by rw [← hEcast, ← hVcast]
  calc ((Level.chain P E₀ S hS (d + 1)).edges : ℝ)
      = ∑ a ∈ A.insts, ((∑ i, ((S a.1 a.2).2.kidE i).card : ℕ) : ℝ) := hcast
    _ ≤ ∑ a ∈ A.insts,
          (ε * (a.2.card : ℝ) + C * Real.sqrt ((a.2.card : ℝ) * (a.1.card : ℝ))) :=
        Finset.sum_le_sum (fun a _ => hcall a.1 a.2)
    _ = ε * (A.edges : ℝ) +
          C * ∑ a ∈ A.insts, Real.sqrt ((a.2.card : ℝ) * (a.1.card : ℝ)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hEcast]
    _ ≤ ε * (A.edges : ℝ) + C * Real.sqrt ((A.edges : ℝ) * (A.verts : ℝ)) := by
        have := mul_le_mul_of_nonneg_left hcs hC
        linarith

/-- **§3.6's total work from the per-instance display.**  `chain_work_linear` with its per-level
display discharged by `chain_display_of_calls`: the only numeric input left is the paper's per-call
children bound. -/
theorem chain_work_linear_of_calls (P : Finset V) (E₀ : Finset E) (S : Strategy G)
    (hS : Strategy.Wf S) {ε C : ℝ} (hε0 : 0 ≤ ε) (hε4 : ε ≤ 1 / 4) (hC : 0 ≤ C)
    (hnm : (P.card : ℝ) ≤ 2 * (E₀.card : ℝ))
    (hcall : ∀ (P' : Finset V) (E₀' : Finset E),
      ((∑ i, ((S P' E₀').2.kidE i).card : ℕ) : ℝ) ≤
        ε * (E₀'.card : ℝ) + C * Real.sqrt ((E₀'.card : ℝ) * (P'.card : ℝ))) :
    ∀ D : ℕ, (∑ d ∈ Finset.range D,
        (((Level.chain P E₀ S hS d).verts : ℝ) +
          ((Level.chain P E₀ S hS d).edges : ℝ))) ≤
      (8 / 3 + 1 / (1 - ε) + 8 * Real.sqrt 2 * C) * ((P.card : ℝ) + (E₀.card : ℝ)) :=
  chain_work_linear P E₀ S hS hε0 hε4 hC hnm
    (chain_display_of_calls P E₀ S hS hC hcall)

end DLMST