import DLMST.HistoryOfRounds
import DLMST.Queries

/-!
# Claim 3.12's total: the sampling cost is `O(t²√(mn))`

`Queries.lean` computed the sample (`sampleSets`) and its size per round
(`sampleSets_card : |S r| ≤ 2t·(⌈log |A r|⌉ + 1)`); `GeometricHistory.lean` bounded the logarithm
(`log_geomFamily_le : log |A r| ≤ 4√(2n·m_r)`).  This file multiplies the two:

* **`geomFamily_log_ceil_le`** — `⌈log |A r|⌉ + 1 ≤ 4√(2n·m_r) + 2`, the per-round factor in reals;
* **`sum_sqrt_card_fibre_le`** — `∑_r √(m_r) ≤ t·√m`: Cauchy–Schwarz
  (`Real.sum_sqrt_mul_sqrt_le`) on the partition of `E` into the slot fibres, with `∑_r m_r = m`;
* **`sampleSets_geomFamily_sum_le`** — the total sample, i.e. the number of queries of §3.5:
  `∑_r |S r| ≤ 8t²√(2nm) + 4t³` for the driver's own history (`historyOfRoundData`), so the
  per-round forests are free;
* **`sampleSets_geomFamily_sum_le_sqrt`** — in the paper's regime `t ≤ √(mn)` the `4t³` term is
  absorbed: `∑_r |S r| ≤ (8√2 + 4)·t²·√(mn)`, the paper's "`O(t²√(mn))` queries".

Nothing here needs the truth membership `htruth` or `hFsp`: the sampling cost counts the family's
size only.
-/

namespace DLMST
open Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

/-- **The per-round sampling factor in reals**: `⌈log |A r|⌉ + 1 ≤ 4√(2n·m_r) + 2`. -/
theorem geomFamily_log_ceil_le {t : ℕ} (H : History V E t) (slot : E → Fin t × Fin t)
    (eN : ∀ (b i : Fin t), Ground G (H.spoke b i) (H.forest b i) ≃
      Fin (Fintype.card (Ground G (H.spoke b i) (H.forest b i))))
    (hF : ∀ b i, IsForest G (H.forest b i)) {n : ℕ} (hV : Fintype.card V ≤ n)
    (r : Fin t × Fin t) :
    ((Nat.ceil (Real.log ((geomFamily (G := G) H slot eN r).card : ℝ)) : ℝ) + 1) ≤
      4 * Real.sqrt ((2 * n : ℝ) * (Fintype.card {e : E // slot e = r} : ℝ)) + 2 := by
  have hlog := log_geomFamily_le (G := G) H slot eN r (hF r.1 r.2) hV
  have hnonneg : 0 ≤ Real.log ((geomFamily (G := G) H slot eN r).card : ℝ) := by
    rcases Nat.eq_zero_or_pos (geomFamily (G := G) H slot eN r).card with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hceil := Nat.ceil_lt_add_one hnonneg
  linarith

/-- **Cauchy–Schwarz on the slot partition**: `∑_r √(m_r) ≤ t·√m`. -/
theorem sum_sqrt_card_fibre_le {t : ℕ} (slot : E → Fin t × Fin t) :
    (∑ r : Fin t × Fin t, Real.sqrt (Fintype.card {e : E // slot e = r})) ≤
      (t : ℝ) * Real.sqrt (Fintype.card E) := by
  classical
  have hcs := Real.sum_sqrt_mul_sqrt_le (s := (Finset.univ : Finset (Fin t × Fin t)))
    (f := fun r => (Fintype.card {e : E // slot e = r} : ℝ)) (g := fun _ => (1 : ℝ))
    (fun _ => by positivity) (fun _ => zero_le_one)
  simp only [Real.sqrt_one, mul_one] at hcs
  have hcard : (∑ r : Fin t × Fin t, (Fintype.card {e : E // slot e = r} : ℝ)) =
      (Fintype.card E : ℝ) := by
    have hpart := Finset.card_eq_sum_card_fiberwise (f := slot)
      (s := (Finset.univ : Finset E)) (t := (Finset.univ : Finset (Fin t × Fin t)))
      (fun e _ => Finset.mem_univ _)
    rw [Finset.card_univ] at hpart
    rw [hpart, Nat.cast_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Fintype.card_subtype]
  have hconst : (∑ _r : Fin t × Fin t, (1 : ℝ)) = (t : ℝ) * t := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]
    simp only [Fintype.card_fin]
    push_cast
    ring
  have hsum1 : Real.sqrt (∑ _r : Fin t × Fin t, (1 : ℝ)) = (t : ℝ) := by
    rw [hconst, Real.sqrt_mul_self (by positivity)]
  rw [hcard, hsum1] at hcs
  calc (∑ r : Fin t × Fin t, Real.sqrt (Fintype.card {e : E // slot e = r}))
      ≤ Real.sqrt (Fintype.card E) * (t : ℝ) := hcs
    _ = (t : ℝ) * Real.sqrt (Fintype.card E) := mul_comm _ _

/-- **The per-round query count**: a round's sample has at most `2t(4√(2n·m_r) + 2)` coordinates. -/
theorem sampleSets_geomFamily_card_le {t : ℕ} (H : History V E t) (slot : E → Fin t × Fin t)
    (eN : ∀ (b i : Fin t), Ground G (H.spoke b i) (H.forest b i) ≃
      Fin (Fintype.card (Ground G (H.spoke b i) (H.forest b i))))
    (hF : ∀ b i, IsForest G (H.forest b i)) {n : ℕ} (hV : Fintype.card V ≤ n) (ht : 2 ≤ t)
    (r : Fin t × Fin t) :
    ((sampleSets ht slot (geomFamily (G := G) H slot eN) r).card : ℝ) ≤
      2 * (t : ℝ) * (4 * Real.sqrt ((2 * n : ℝ) * (Fintype.card {e : E // slot e = r} : ℝ))
        + 2) := by
  have hlog := geomFamily_log_ceil_le (G := G) H slot eN hF hV r
  have h1 : ((sampleSets ht slot (geomFamily (G := G) H slot eN) r).card : ℝ) ≤
      2 * (t : ℝ) * ((Nat.ceil (Real.log ((geomFamily (G := G) H slot eN r).card : ℝ)) : ℝ)
        + 1) := by
    have h := sampleSets_card ht slot (geomFamily (G := G) H slot eN) r
    have hcast : ((2 * t * (Nat.ceil (Real.log ((geomFamily (G := G) H slot eN r).card : ℝ))
        + 1) : ℕ) : ℝ) =
        2 * (t : ℝ) * ((Nat.ceil (Real.log ((geomFamily (G := G) H slot eN r).card : ℝ)) : ℝ)
          + 1) := by
      push_cast
      ring
    calc ((sampleSets ht slot (geomFamily (G := G) H slot eN) r).card : ℝ)
        ≤ ((2 * t * (Nat.ceil (Real.log ((geomFamily (G := G) H slot eN r).card : ℝ))
            + 1) : ℕ) : ℝ) := by exact_mod_cast h
      _ = 2 * (t : ℝ) * ((Nat.ceil (Real.log ((geomFamily (G := G) H slot eN r).card : ℝ)) : ℝ)
            + 1) := hcast
  nlinarith [h1, hlog]

/-- **The number of queries of §3.5** for the driver's own history: `∑_r |S r| ≤ 8t²√(2nm) + 4t³`,
where `m = |E|` and the forest invariant is derived from the round data. -/
theorem sampleSets_geomFamily_sum_le {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ}
    {P : Finset V} {E₀ : Finset E} (D : CallOut.RoundData G P E₀ ι t)
    (σ : Fin t → Fin t → V → E) (slot : E → Fin t × Fin t)
    (eN : ∀ (b i : Fin t), Ground G (σ b i) (forestUpTo D (b, i)) ≃
      Fin (Fintype.card (Ground G (σ b i) (forestUpTo D (b, i)))))
    (ht : 2 ≤ t) {n : ℕ} (hV : Fintype.card V ≤ n) :
    (∑ r : Fin t × Fin t,
        ((sampleSets ht slot
          (geomFamily (G := G) (historyOfRoundData D σ) slot (fun b i => eN b i)) r).card : ℝ)) ≤
      8 * (t : ℝ) ^ 2 * Real.sqrt ((2 * n : ℝ) * (Fintype.card E : ℝ)) +
        4 * (t : ℝ) ^ 3 := by
  classical
  set A : ∀ r : Fin t × Fin t, Finset ({e : E // slot e = r} → Pref) :=
    geomFamily (G := G) (historyOfRoundData D σ) slot (fun b i => eN b i) with hA
  have hlog : ∀ r : Fin t × Fin t,
      ((Nat.ceil (Real.log ((A r).card : ℝ)) : ℝ) + 1) ≤
        4 * Real.sqrt ((2 * n : ℝ) * (Fintype.card {e : E // slot e = r} : ℝ)) + 2 :=
    fun r => geomFamily_log_ceil_le (H := historyOfRoundData D σ) slot (fun b i => eN b i)
      (isForest_historyOfRoundData D σ) hV r
  have hcard : ∀ r : Fin t × Fin t,
      ((sampleSets ht slot A r).card : ℝ) ≤
        2 * (t : ℝ) * (4 * Real.sqrt ((2 * n : ℝ) * (Fintype.card {e : E // slot e = r} : ℝ))
          + 2) :=
    fun r => sampleSets_geomFamily_card_le (H := historyOfRoundData D σ) slot (fun b i => eN b i)
      (isForest_historyOfRoundData D σ) hV ht r
  have hsqrt : ∀ r : Fin t × Fin t,
      Real.sqrt ((2 * n : ℝ) * (Fintype.card {e : E // slot e = r} : ℝ)) =
        Real.sqrt (2 * n : ℝ) * Real.sqrt (Fintype.card {e : E // slot e = r} : ℝ) :=
    fun r => Real.sqrt_mul (by positivity) _
  have hsplit : (∑ r : Fin t × Fin t,
        (4 * Real.sqrt ((2 * n : ℝ) * (Fintype.card {e : E // slot e = r} : ℝ)) + 2)) =
      4 * (Real.sqrt (2 * n : ℝ) *
          (∑ r : Fin t × Fin t, Real.sqrt (Fintype.card {e : E // slot e = r} : ℝ)))
        + 2 * ((t : ℝ) * t) := by
    have h1 : (∑ r : Fin t × Fin t,
          4 * Real.sqrt ((2 * n : ℝ) * (Fintype.card {e : E // slot e = r} : ℝ))) =
        4 * (Real.sqrt (2 * n : ℝ) *
          (∑ r : Fin t × Fin t, Real.sqrt (Fintype.card {e : E // slot e = r} : ℝ))) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ => by rw [hsqrt r]
    have h2 : (∑ _r : Fin t × Fin t, (2 : ℝ)) = 2 * ((t : ℝ) * t) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]
      simp only [Fintype.card_fin]
      push_cast
      ring
    rw [Finset.sum_add_distrib, h1, h2]
  have hsum_sqrt := sum_sqrt_card_fibre_le (E := E) slot
  calc (∑ r : Fin t × Fin t, ((sampleSets ht slot A r).card : ℝ))
      ≤ ∑ r : Fin t × Fin t,
          2 * (t : ℝ) * (4 * Real.sqrt ((2 * n : ℝ) *
            (Fintype.card {e : E // slot e = r} : ℝ)) + 2) :=
        Finset.sum_le_sum fun r _ => hcard r
    _ = 2 * (t : ℝ) * (4 * (Real.sqrt (2 * n : ℝ) *
          (∑ r : Fin t × Fin t, Real.sqrt (Fintype.card {e : E // slot e = r} : ℝ)))
        + 2 * ((t : ℝ) * t)) := by
        rw [← Finset.mul_sum, hsplit]
    _ ≤ 2 * (t : ℝ) * (4 * (Real.sqrt (2 * n : ℝ) *
          ((t : ℝ) * Real.sqrt (Fintype.card E))) + 2 * ((t : ℝ) * t)) := by
        gcongr
    _ = 8 * (t : ℝ) ^ 2 * Real.sqrt ((2 * n : ℝ) * (Fintype.card E : ℝ)) +
          4 * (t : ℝ) ^ 3 := by
        have hstep : Real.sqrt (2 * n : ℝ) * ((t : ℝ) * Real.sqrt (Fintype.card E : ℝ)) =
            (t : ℝ) * Real.sqrt ((2 * n : ℝ) * (Fintype.card E : ℝ)) := by
          rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * n)]
          ring
        rw [hstep]
        ring

/-- **The paper's shape**: when `t ≤ √(mn)` the `4t³` term is absorbed and the total query count is
`(8√2 + 4)·t²·√(mn)` — §3.5's "`O(t²√(mn))` queries". -/
theorem sampleSets_geomFamily_sum_le_sqrt {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ}
    {P : Finset V} {E₀ : Finset E} (D : CallOut.RoundData G P E₀ ι t)
    (σ : Fin t → Fin t → V → E) (slot : E → Fin t × Fin t)
    (eN : ∀ (b i : Fin t), Ground G (σ b i) (forestUpTo D (b, i)) ≃
      Fin (Fintype.card (Ground G (σ b i) (forestUpTo D (b, i)))))
    (ht : 2 ≤ t) {n : ℕ} (hV : Fintype.card V ≤ n)
    (hreg : (t : ℝ) ≤ Real.sqrt ((Fintype.card E : ℝ) * (n : ℝ))) :
    (∑ r : Fin t × Fin t,
        ((sampleSets ht slot
          (geomFamily (G := G) (historyOfRoundData D σ) slot (fun b i => eN b i)) r).card : ℝ)) ≤
      (8 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 *
        Real.sqrt ((Fintype.card E : ℝ) * (n : ℝ)) := by
  have hmain := sampleSets_geomFamily_sum_le D σ slot eN ht hV
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  have hsq : (0 : ℝ) ≤ (t : ℝ) ^ 2 := sq_nonneg _
  have h1 : Real.sqrt ((2 * n : ℝ) * (Fintype.card E : ℝ)) =
      Real.sqrt 2 * Real.sqrt ((Fintype.card E : ℝ) * (n : ℝ)) := by
    rw [show (2 * (n : ℝ)) * (Fintype.card E : ℝ) =
        2 * ((n : ℝ) * (Fintype.card E : ℝ)) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
      show (n : ℝ) * (Fintype.card E : ℝ) = (Fintype.card E : ℝ) * (n : ℝ) by ring]
  have h2 : 4 * (t : ℝ) ^ 3 ≤ 4 * (t : ℝ) ^ 2 *
      Real.sqrt ((Fintype.card E : ℝ) * (n : ℝ)) := by
    have h : (t : ℝ) ^ 3 = (t : ℝ) ^ 2 * (t : ℝ) := by ring
    rw [h]
    nlinarith [mul_le_mul_of_nonneg_left hreg hsq]
  rw [h1] at hmain
  nlinarith [hmain, h2]

end DLMST