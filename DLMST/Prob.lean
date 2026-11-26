import DLMST.History
import DLMST.Sampling

/-!
# B4: the probability layer behind §3.4–§3.5

`History.lean` and `Sampling.lean` prove Lemma 3.11 and Claim 3.12 by replacing "random" with exact
finite counts: the average over all `(t²)^m` schedules, and the number of bad `k`-tuples.  That is
the paper's *existence* argument, and it is machine-checked.  What it does not expose is the
probability language the paper actually writes in: uniform distributions, expectations, Markov's
inequality, and the phrases "with probability at least …".

This file supplies that layer, on finite types, without measure theory.  Events are `Finset`s (so
no decidability enters the statements), and the ambient space is a `Fintype`:

* `unifProb`/`unifExpect` — uniform probability of an event and expectation of a real statistic;
* `unifProb_mono`, `unifProb_compl`, `exists_of_unifProb_pos`, and **`markov`**:
  `P[a ≤ f] ≤ E[f]/a` for nonnegative `f`;
* **`History.unifExpect_two_pow_lost_le`** — the paper's `E[2^{X_H}] ≤ (1 + 2/t)^m`, from the
  counting identity `History.weighted_sum_le`;
* **`History.lost_tail_prob`** — the high-probability form of Lemma 3.11:
  `P[X_H ≥ s] ≤ e^{2m/t} / 2^s`, the statement the counting route never made explicit;
* **`bad_prob_le`** — Claim 3.12's union bound as a probability:
  `P[Bad] ≤ |A|² (1 − 1/t)^k`;
* **`sample_budget_exp`** — `N²(1 − 1/t)^k ≤ e^{−2}` at the paper's `k = 2t(⌈log N⌉ + 1)`;
* **`claim312_success_prob`** — hence the random sample is good with probability at least
  `1 − e^{−2}`, and **`claim312_exists_via_prob`** re-derives the existence of a separating sample
  from that positive probability.

Still outside this file (boundary B4 unchanged): the final algorithm is *deterministic*, as the
paper insists ("we are not permitted to use randomness here") — randomness only proves that good
schedules and samples exist; the algorithm finds them by exhaustive search.  Nothing here claims a
randomized running time, and Lemma 3.10's history count remains obligation 4.
-/

namespace DLMST

open Classical

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- **Uniform probability** of a finite event. -/
noncomputable def unifProb {Ω : Type*} [Fintype Ω] (S : Finset Ω) : ℝ :=
  (S.card : ℝ) / (Fintype.card Ω : ℝ)

/-- **Uniform expectation** of a real statistic on a finite type. -/
noncomputable def unifExpect {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / (Fintype.card Ω : ℝ)

theorem unifProb_nonneg {Ω : Type*} [Fintype Ω] (S : Finset Ω) : 0 ≤ unifProb S := by
  unfold unifProb
  positivity

/-- Probability is monotone in the event. -/
theorem unifProb_mono {Ω : Type*} [Fintype Ω] {S T : Finset Ω} (h : S ⊆ T) :
    unifProb S ≤ unifProb T := by
  unfold unifProb
  exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card h) (by positivity)

/-- The probability of an event and of its complement add to one. -/
theorem unifProb_compl {Ω : Type*} [Fintype Ω] [Nonempty Ω] {S T : Finset Ω}
    (hd : Disjoint S T) (hu : S ∪ T = Finset.univ) : unifProb S + unifProb T = 1 := by
  unfold unifProb
  have hN : (0 : ℝ) < (Fintype.card Ω : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hsplit : S.card + T.card = Fintype.card Ω := by
    rw [← Finset.card_union_of_disjoint hd, hu, Finset.card_univ]
  rw [← add_div, div_eq_one_iff_eq hN.ne']
  exact_mod_cast hsplit

/-- A nonempty event has positive probability: the contrapositive form used to extract witnesses. -/
theorem exists_of_unifProb_pos {Ω : Type*} [Fintype Ω] {S : Finset Ω}
    (hp : 0 < unifProb S) : S.Nonempty := by
  rw [← Finset.ne_empty_iff_nonempty]
  intro h
  unfold unifProb at hp
  rw [h] at hp
  simp at hp

/-- **Markov's inequality** on a finite uniform space: for `f ≥ 0` and `a > 0`,
`P[a ≤ f] ≤ E[f]/a`. -/
theorem markov {Ω : Type*} [Fintype Ω] [Nonempty Ω] {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω)
    {a : ℝ} (ha : 0 < a) :
    unifProb (Finset.univ.filter (fun ω => a ≤ f ω)) ≤ unifExpect f / a := by
  have hN : (0 : ℝ) < (Fintype.card Ω : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hNa : (0 : ℝ) < (Fintype.card Ω : ℝ) * a := mul_pos hN ha
  have hstep : a * ((Finset.univ.filter (fun ω => a ≤ f ω)).card : ℝ) ≤ ∑ ω, f ω := by
    have h1 : a * ((Finset.univ.filter (fun ω => a ≤ f ω)).card : ℝ) =
        ∑ ω ∈ Finset.univ.filter (fun ω => a ≤ f ω), a := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    rw [h1]
    calc ∑ ω ∈ Finset.univ.filter (fun ω => a ≤ f ω), a
        ≤ ∑ ω ∈ Finset.univ.filter (fun ω => a ≤ f ω), f ω :=
          Finset.sum_le_sum (fun ω hω => (Finset.mem_filter.mp hω).2)
      _ ≤ ∑ ω, f ω :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun ω _ _ => hf ω)
  calc unifProb (Finset.univ.filter (fun ω => a ≤ f ω))
      = a * ((Finset.univ.filter (fun ω => a ≤ f ω)).card : ℝ) /
          ((Fintype.card Ω : ℝ) * a) := by
        unfold unifProb
        field_simp
    _ ≤ (∑ ω, f ω) / ((Fintype.card Ω : ℝ) * a) :=
        div_le_div_of_nonneg_right hstep hNa.le
    _ = unifExpect f / a := by
        unfold unifExpect
        rw [div_div]

/-- Expectation is monotone. -/
theorem unifExpect_mono {Ω : Type*} [Fintype Ω] {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    unifExpect f ≤ unifExpect g := by
  unfold unifExpect
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun ω _ => h ω) (by positivity)

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] {G : WGraph V E}
  [LinearOrder E]

namespace History

/-- **The paper's `E[2^{X_H}] ≤ (1 + 2/t)^m`, as an expectation.**  `weighted_sum_le` bounds the
sum of `2^{X_H}` over all schedules by `(t² + 2t)^m`; dividing by the `(t²)^m` schedules gives the
paper's bound with no slack lost. -/
theorem unifExpect_two_pow_lost_le {t : ℕ} (ht : 2 ≤ t) (H : History V E t) :
    unifExpect (fun ρ : Sched E t => (2 : ℝ) ^ H.lost ρ) ≤
      (1 + 2 / (t : ℝ)) ^ Fintype.card E := by
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hN : (Fintype.card (Sched E t) : ℝ) = ((t : ℝ) * t) ^ Fintype.card E := by
    simp [Sched, Fintype.card_prod]
  have hNpos : (0 : ℝ) < (Fintype.card (Sched E t) : ℝ) := by
    rw [hN]; positivity
  have hcast : (∑ ρ : Sched E t, (2 : ℝ) ^ H.lost ρ) =
      ((∑ ρ : Sched E t, (2 : ℕ) ^ H.lost ρ : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun ρ _ => by rw [Nat.cast_pow]; norm_num
  have hsum : (∑ ρ : Sched E t, (2 : ℝ) ^ H.lost ρ) ≤
      (((t * t + 2 * t : ℕ)) : ℝ) ^ Fintype.card E := by
    rw [hcast]
    exact_mod_cast History.weighted_sum_le H
  have hratio : (((t * t + 2 * t : ℕ)) : ℝ) ^ Fintype.card E /
      (Fintype.card (Sched E t) : ℝ) = (1 + 2 / (t : ℝ)) ^ Fintype.card E := by
    rw [hN, ← div_pow]
    congr 1
    have h1 : (((t * t + 2 * t : ℕ)) : ℝ) = (t : ℝ) * ((t : ℝ) + 2) := by
      push_cast
      ring
    rw [h1]
    field_simp
  have hAeq : (((t * t + 2 * t : ℕ)) : ℝ) ^ Fintype.card E =
      (1 + 2 / (t : ℝ)) ^ Fintype.card E * (Fintype.card (Sched E t) : ℝ) := by
    calc (((t * t + 2 * t : ℕ)) : ℝ) ^ Fintype.card E
        = (((t * t + 2 * t : ℕ)) : ℝ) ^ Fintype.card E /
            (Fintype.card (Sched E t) : ℝ) * (Fintype.card (Sched E t) : ℝ) :=
          (div_mul_cancel₀ _ hNpos.ne').symm
      _ = (1 + 2 / (t : ℝ)) ^ Fintype.card E * (Fintype.card (Sched E t) : ℝ) := by
          rw [hratio]
  unfold unifExpect
  rw [div_le_iff₀ hNpos]
  linarith [hsum, hAeq]

/-- **Lemma 3.11 in tail form**: under a uniformly random schedule the number of badly scheduled
edges exceeds `s` with probability at most `e^{2m/t}/2^s`.  This is the "with high probability"
statement behind the paper's averaged argument; `lemma311` is its deterministic-selection
counterpart. -/
theorem lost_tail_prob {t : ℕ} (ht : 2 ≤ t) (H : History V E t) (s : ℕ) :
    unifProb (Finset.univ.filter (fun ρ : Sched E t => s ≤ H.lost ρ)) ≤
      Real.exp (2 * (Fintype.card E : ℝ) / (t : ℝ)) / (2 : ℝ) ^ s := by
  haveI : Nonempty (Sched E t) :=
    ⟨fun _ => (⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  -- `(1 + 2/t)^m ≤ e^{2m/t}`
  have hexp : (1 + 2 / (t : ℝ)) ^ Fintype.card E ≤
      Real.exp (2 * (Fintype.card E : ℝ) / (t : ℝ)) := by
    have h1 : (1 + 2 / (t : ℝ)) ≤ Real.exp (2 / (t : ℝ)) := by
      simpa [add_comm] using Real.add_one_le_exp (2 / (t : ℝ))
    have hm : (1 + 2 / (t : ℝ)) ^ Fintype.card E ≤
        Real.exp (2 / (t : ℝ)) ^ Fintype.card E :=
      pow_le_pow_left₀ (by positivity) h1 _
    have h2 : Real.exp (2 / (t : ℝ)) ^ Fintype.card E =
        Real.exp (2 * (Fintype.card E : ℝ) / (t : ℝ)) := by
      rw [← Real.exp_natCast_mul]
      congr 1
      ring
    linarith [h2]
  have hsub : Finset.univ.filter (fun ρ : Sched E t => s ≤ H.lost ρ) ⊆
      Finset.univ.filter (fun ρ : Sched E t => (2 : ℝ) ^ s ≤ (2 : ℝ) ^ H.lost ρ) := by
    intro ρ hρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
    exact pow_le_pow_right₀ (by norm_num) hρ
  have hmono := unifProb_mono hsub
  have hmk : unifProb (Finset.univ.filter
        (fun ρ : Sched E t => (2 : ℝ) ^ s ≤ (2 : ℝ) ^ H.lost ρ)) ≤
      unifExpect (fun ρ : Sched E t => (2 : ℝ) ^ H.lost ρ) / (2 : ℝ) ^ s :=
    markov (f := fun ρ : Sched E t => (2 : ℝ) ^ H.lost ρ) (fun ρ => by positivity)
      (show (0 : ℝ) < (2 : ℝ) ^ s by positivity)
  have hexp2 := H.unifExpect_two_pow_lost_le ht
  calc unifProb (Finset.univ.filter (fun ρ : Sched E t => s ≤ H.lost ρ))
      ≤ unifProb (Finset.univ.filter
          (fun ρ : Sched E t => (2 : ℝ) ^ s ≤ (2 : ℝ) ^ H.lost ρ)) := hmono
    _ ≤ unifExpect (fun ρ : Sched E t => (2 : ℝ) ^ H.lost ρ) / (2 : ℝ) ^ s := hmk
    _ ≤ (1 + 2 / (t : ℝ)) ^ Fintype.card E / (2 : ℝ) ^ s :=
        div_le_div_of_nonneg_right hexp2 (by positivity)
    _ ≤ Real.exp (2 * (Fintype.card E : ℝ) / (t : ℝ)) / (2 : ℝ) ^ s :=
        div_le_div_of_nonneg_right hexp (by positivity)

/-- **The per-edge factor at an arbitrary base `lam ≥ 1`.**  `lam^{[bad]}` sums to
`t² + (#bad)·(lam − 1)`, so `#bad ≤ 2t` gives `t² + 2t(lam − 1)`.  At `lam = 2` this is `genEdge_le`. -/
theorem genEdge_le_real (H : History V E t) (e : E) {lam : ℝ} (hlam : 1 ≤ lam) :
    (∑ r : Fin t × Fin t, lam ^ (if H.badFor e r then (1 : ℕ) else 0)) ≤
      (t : ℝ) * t + 2 * (t : ℝ) * (lam - 1) := by
  classical
  have hterm : ∀ r : Fin t × Fin t,
      lam ^ (if H.badFor e r then (1 : ℕ) else 0) =
        1 + (if H.badFor e r then (lam - 1) else 0) := by
    intro r
    by_cases h : H.badFor e r <;> simp [h]
  have hcard : (Finset.univ : Finset (Fin t × Fin t)).card = t * t := by simp
  have hsum1 : (∑ _r : Fin t × Fin t, (1 : ℝ)) = (t : ℝ) * t := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_one]
    push_cast
    ring
  have hbool : (∑ r : Fin t × Fin t, (if H.badFor e r then (lam - 1) else 0)) =
      (((Finset.univ : Finset (Fin t × Fin t)).filter (H.badFor e)).card : ℝ) * (lam - 1) := by
    have h1 : ∀ r : Fin t × Fin t,
        (if H.badFor e r then (lam - 1) else 0) =
          (if H.badFor e r then (1 : ℝ) else 0) * (lam - 1) := by
      intro r
      by_cases h : H.badFor e r <;> simp [h]
    calc (∑ r : Fin t × Fin t, (if H.badFor e r then (lam - 1) else 0))
        = ∑ r : Fin t × Fin t, (if H.badFor e r then (1 : ℝ) else 0) * (lam - 1) :=
          Finset.sum_congr rfl fun r _ => h1 r
      _ = (∑ r : Fin t × Fin t, (if H.badFor e r then (1 : ℝ) else 0)) * (lam - 1) :=
          (Finset.sum_mul _ _ _).symm
      _ = (((Finset.univ : Finset (Fin t × Fin t)).filter (H.badFor e)).card : ℝ) * (lam - 1) := by
          rw [Finset.sum_boole]
  calc (∑ r : Fin t × Fin t, lam ^ (if H.badFor e r then (1 : ℕ) else 0))
      = ∑ r : Fin t × Fin t, (1 + (if H.badFor e r then (lam - 1) else 0)) :=
        Finset.sum_congr rfl fun r _ => hterm r
    _ = (∑ _r : Fin t × Fin t, (1 : ℝ)) +
          ∑ r : Fin t × Fin t, (if H.badFor e r then (lam - 1) else 0) :=
        Finset.sum_add_distrib
    _ = (t : ℝ) * t + (((Finset.univ : Finset (Fin t × Fin t)).filter (H.badFor e)).card : ℝ) *
          (lam - 1) := by rw [hsum1, hbool]
    _ ≤ (t : ℝ) * t + 2 * (t : ℝ) * (lam - 1) := by
        have hb : (((Finset.univ : Finset (Fin t × Fin t)).filter (H.badFor e)).card : ℝ) ≤
            2 * (t : ℝ) := by exact_mod_cast H.badFor_card_le e
        have hlam0 : (0 : ℝ) ≤ lam - 1 := by linarith
        nlinarith [mul_le_mul_of_nonneg_right hb hlam0]

/-- **Lemma 3.11's engine at base `lam`**: for every real `lam ≥ 1`,
`∑_ρ lam^{X_H(ρ)} ≤ (t² + 2t(lam − 1))^m`; the factorisation over edges is the same
`Finset.sum_prod_piFinset` independence as `weighted_sum_le`. -/
theorem weighted_sum_le_real (H : History V E t) {lam : ℝ} (hlam : 1 ≤ lam) :
    (∑ ρ : Sched E t, lam ^ H.lost ρ) ≤
      ((t : ℝ) * t + 2 * (t : ℝ) * (lam - 1)) ^ Fintype.card E := by
  classical
  have hfactor : ∀ ρ : Sched E t,
      lam ^ H.lost ρ = ∏ e : E, lam ^ (if H.badFor e (ρ e) then (1 : ℕ) else 0) := by
    intro ρ
    have h1 : H.lost ρ = ∑ e : E, (if H.badFor e (ρ e) then 1 else 0) := by
      unfold History.lost
      simp [Finset.sum_boole]
    rw [h1, Finset.prod_pow_eq_pow_sum]
  have hpi : (∑ ρ : Sched E t, ∏ e : E, lam ^ (if H.badFor e (ρ e) then (1 : ℕ) else 0)) =
      ∏ e : E, ∑ r : Fin t × Fin t, lam ^ (if H.badFor e r then (1 : ℕ) else 0) := by
    have h := Finset.sum_prod_piFinset (s := (Finset.univ : Finset (Fin t × Fin t)))
      (g := fun (e : E) (r : Fin t × Fin t) => lam ^ (if H.badFor e r then (1 : ℕ) else 0))
    simpa [Sched, Fintype.piFinset_univ] using h
  calc (∑ ρ : Sched E t, lam ^ H.lost ρ)
      = ∑ ρ : Sched E t, ∏ e : E, lam ^ (if H.badFor e (ρ e) then (1 : ℕ) else 0) :=
        Finset.sum_congr rfl fun ρ _ => hfactor ρ
    _ = ∏ e : E, ∑ r : Fin t × Fin t, lam ^ (if H.badFor e r then (1 : ℕ) else 0) := hpi
    _ ≤ ∏ _e : E, ((t : ℝ) * t + 2 * (t : ℝ) * (lam - 1)) := by
        have ht0 : (0 : ℝ) ≤ (t : ℝ) := by positivity
        have hlam0 : (0 : ℝ) ≤ lam - 1 := by linarith
        have hC0 : (0 : ℝ) ≤ (t : ℝ) * t + 2 * (t : ℝ) * (lam - 1) := by nlinarith
        have hfac : ∀ e : E,
            (∑ r : Fin t × Fin t, lam ^ (if H.badFor e r then (1 : ℕ) else 0)) ≤
              (t : ℝ) * t + 2 * (t : ℝ) * (lam - 1) := fun e => H.genEdge_le_real e hlam
        have hnonneg : ∀ e : E, (0 : ℝ) ≤
            ∑ r : Fin t × Fin t, lam ^ (if H.badFor e r then (1 : ℕ) else 0) :=
          fun e => Finset.sum_nonneg fun r _ => by positivity
        have key : ∀ s : Finset E,
            (∏ e ∈ s, (∑ r : Fin t × Fin t, lam ^ (if H.badFor e r then (1 : ℕ) else 0))) ≤
              ∏ _e ∈ s, ((t : ℝ) * t + 2 * (t : ℝ) * (lam - 1)) := by
          intro s
          induction s using Finset.induction_on with
          | empty => simp
          | insert a s ha ih =>
              rw [Finset.prod_insert ha, Finset.prod_insert ha]
              exact mul_le_mul (hfac a) ih (Finset.prod_nonneg fun e _ => hnonneg e) hC0
        simpa using key Finset.univ
    _ = ((t : ℝ) * t + 2 * (t : ℝ) * (lam - 1)) ^ Fintype.card E := by simp

/-- **The generating-function bound as an expectation.**  For `lam ≥ 1`,
`E[lam^{X_H}] ≤ (1 + 2(lam − 1)/t)^m`; `lam = 2` is `unifExpect_two_pow_lost_le`, and larger `lam`
gives the Chernoff-rate family used below. -/
theorem unifExpect_mgf_le {t : ℕ} (ht : 2 ≤ t) (H : History V E t) {lam : ℝ} (hlam : 1 ≤ lam) :
    unifExpect (fun ρ : Sched E t => lam ^ H.lost ρ) ≤
      (1 + 2 * (lam - 1) / (t : ℝ)) ^ Fintype.card E := by
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hN : (Fintype.card (Sched E t) : ℝ) = ((t : ℝ) * t) ^ Fintype.card E := by
    simp [Sched, Fintype.card_prod]
  have hNpos : (0 : ℝ) < (Fintype.card (Sched E t) : ℝ) := by
    rw [hN]; positivity
  have hsum := H.weighted_sum_le_real hlam
  have hratio : ((t : ℝ) * t + 2 * (t : ℝ) * (lam - 1)) ^ Fintype.card E /
      (Fintype.card (Sched E t) : ℝ) = (1 + 2 * (lam - 1) / (t : ℝ)) ^ Fintype.card E := by
    rw [hN, ← div_pow]
    congr 1
    field_simp
  have hAeq : ((t : ℝ) * t + 2 * (t : ℝ) * (lam - 1)) ^ Fintype.card E =
      (1 + 2 * (lam - 1) / (t : ℝ)) ^ Fintype.card E * (Fintype.card (Sched E t) : ℝ) := by
    calc ((t : ℝ) * t + 2 * (t : ℝ) * (lam - 1)) ^ Fintype.card E
        = ((t : ℝ) * t + 2 * (t : ℝ) * (lam - 1)) ^ Fintype.card E /
            (Fintype.card (Sched E t) : ℝ) * (Fintype.card (Sched E t) : ℝ) :=
          (div_mul_cancel₀ _ hNpos.ne').symm
      _ = (1 + 2 * (lam - 1) / (t : ℝ)) ^ Fintype.card E * (Fintype.card (Sched E t) : ℝ) := by
          rw [hratio]
  unfold unifExpect
  rw [div_le_iff₀ hNpos]
  linarith [hsum, hAeq]

/-- **Chernoff tail at base `lam > 1`**: `P[X_H ≥ s] ≤ (1 + 2(lam − 1)/t)^m / lam^s`.  Markov applied to
`lam^{X_H}`; at `lam = 2` this recovers `lost_tail_prob`, and optimising `lam` over `s` is the usual
Chernoff step. -/
theorem chernoff_tail {t : ℕ} (ht : 2 ≤ t) (H : History V E t) {lam : ℝ} (hlam : 1 < lam) (s : ℕ) :
    unifProb (Finset.univ.filter (fun ρ : Sched E t => s ≤ H.lost ρ)) ≤
      (1 + 2 * (lam - 1) / (t : ℝ)) ^ Fintype.card E / lam ^ s := by
  haveI : Nonempty (Sched E t) :=
    ⟨fun _ => (⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hsub : Finset.univ.filter (fun ρ : Sched E t => s ≤ H.lost ρ) ⊆
      Finset.univ.filter (fun ρ : Sched E t => lam ^ s ≤ lam ^ H.lost ρ) := by
    intro ρ hρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
    exact pow_le_pow_right₀ hlam.le hρ
  have hmk := markov (f := fun ρ : Sched E t => lam ^ H.lost ρ) (fun ρ => by positivity)
    (show (0 : ℝ) < lam ^ s by positivity)
  exact (unifProb_mono hsub).trans (hmk.trans
    (div_le_div_of_nonneg_right (H.unifExpect_mgf_le ht hlam.le) (by positivity)))

/-- **Expected lost count.**  `E[X_H] ≤ E[2^{X_H}] ≤ (1 + 2/t)^m`, using `n ≤ 2^n`; the paper's
Lemma 3.11 conclusion at the level of the mean rather than a single schedule. -/
theorem unifExpect_lost_le {t : ℕ} (ht : 2 ≤ t) (H : History V E t) :
    unifExpect (fun ρ : Sched E t => (H.lost ρ : ℝ)) ≤
      (1 + 2 / (t : ℝ)) ^ Fintype.card E := by
  have hpt : ∀ ρ : Sched E t, (H.lost ρ : ℝ) ≤ (2 : ℝ) ^ H.lost ρ := by
    intro ρ
    have h := Nat.lt_two_pow_self (n := H.lost ρ)
    have h' : ((H.lost ρ : ℕ) : ℝ) < (((2 : ℕ) ^ H.lost ρ : ℕ) : ℝ) := by exact_mod_cast h
    simpa using h'.le
  exact (unifExpect_mono hpt).trans (H.unifExpect_two_pow_lost_le ht)

/-- **At least half of all schedules are good.**  With `B = (1 + 2/t)^m ≥ E[X_H]`, Markov on
`X_H ≥ 0` at `a = 2B` gives `P[X_H ≥ 2B] ≤ 1/2`; the complement is the displayed event (written in
the negated form to keep the `Finset` free of a decidability rewrite).  This is the exact
"exhaustive search finds one" statement behind the paper's deterministic selection: good schedules
form a majority of the search space. -/
theorem half_schedules_good {t : ℕ} (ht : 2 ≤ t) (H : History V E t) :
    (1 : ℝ) / 2 ≤
      unifProb (Finset.univ.filter (fun ρ : Sched E t =>
        ¬ 2 * (1 + 2 / (t : ℝ)) ^ Fintype.card E ≤ (H.lost ρ : ℝ))) := by
  classical
  haveI : Nonempty (Sched E t) :=
    ⟨fun _ => (⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  set B : ℝ := (1 + 2 / (t : ℝ)) ^ Fintype.card E with hB
  have hBpos : (0 : ℝ) < B := by rw [hB]; positivity
  have hcompl := unifProb_compl
    (S := Finset.univ.filter (fun ρ : Sched E t => 2 * B ≤ (H.lost ρ : ℝ)))
    (T := Finset.univ.filter (fun ρ : Sched E t => ¬ 2 * B ≤ (H.lost ρ : ℝ)))
    (by exact Finset.disjoint_filter.mpr (fun ρ _ h1 h2 => h2 h1))
    (by rw [Finset.filter_union_filter_not_eq])
  have hmk : unifProb (Finset.univ.filter (fun ρ : Sched E t => 2 * B ≤ (H.lost ρ : ℝ))) ≤
      1 / 2 := by
    have h1 := markov (f := fun ρ : Sched E t => (H.lost ρ : ℝ)) (fun ρ => by positivity)
      (show (0 : ℝ) < 2 * B by positivity)
    have h2 : unifExpect (fun ρ : Sched E t => (H.lost ρ : ℝ)) ≤ B := by
      rw [hB]; exact H.unifExpect_lost_le ht
    calc unifProb (Finset.univ.filter (fun ρ : Sched E t => 2 * B ≤ (H.lost ρ : ℝ)))
        ≤ unifExpect (fun ρ : Sched E t => (H.lost ρ : ℝ)) / (2 * B) := h1
      _ ≤ B / (2 * B) := div_le_div_of_nonneg_right h2 (by positivity)
      _ = 1 / 2 := by field_simp
  linarith

/-- **Lemma 3.11's tail form with the paper's threshold**: for a nonempty family `Hs` of histories,
`P[X_H ≥ ⌈(log|Hs| + 2m/t)/log 2⌉] ≤ 1/|Hs|` under a uniformly random schedule — the bound that
makes "almost every schedule is good for the whole family" quantitative.  This is `lost_tail_prob`
at `s = ⌈(log|Hs| + 2m/t)/log 2⌉`, where `e^{2m/t}/2^s ≤ 1/|Hs|`. -/
theorem lost_tail_prob_paper {t : ℕ} (ht : 2 ≤ t) (H : History V E t)
    {Hs : Finset (History V E t)} (hne : Hs.Nonempty) :
    unifProb (Finset.univ.filter (fun ρ : Sched E t =>
      Nat.ceil ((Real.log (Hs.card : ℝ) + 2 * (Fintype.card E : ℝ) / (t : ℝ)) / Real.log 2)
        ≤ H.lost ρ)) ≤
      1 / (Hs.card : ℝ) := by
  have htail := H.lost_tail_prob ht
    (Nat.ceil ((Real.log (Hs.card : ℝ) + 2 * (Fintype.card E : ℝ) / (t : ℝ)) / Real.log 2))
  refine htail.trans ?_
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hHs : (0 : ℝ) < (Hs.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hne
  set x : ℝ := (Real.log (Hs.card : ℝ) + 2 * (Fintype.card E : ℝ) / (t : ℝ)) / Real.log 2
    with hx
  have hxle : x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil x
  have hmul : x * Real.log 2 = Real.log (Hs.card : ℝ) + 2 * (Fintype.card E : ℝ) / (t : ℝ) := by
    rw [hx]
    field_simp
  have hpow : Real.exp (Real.log (Hs.card : ℝ) + 2 * (Fintype.card E : ℝ) / (t : ℝ)) ≤
      (2 : ℝ) ^ (Nat.ceil x) := by
    have h1 : Real.exp ((x * Real.log 2)) ≤ Real.exp ((Nat.ceil x : ℝ) * Real.log 2) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hxle hlog2.le)
    rw [hmul, Real.exp_natCast_mul, Real.exp_log (by norm_num)] at h1
    exact h1
  have hrest : Real.exp (2 * (Fintype.card E : ℝ) / (t : ℝ)) * (Hs.card : ℝ) =
      Real.exp (Real.log (Hs.card : ℝ) + 2 * (Fintype.card E : ℝ) / (t : ℝ)) := by
    rw [Real.exp_add, Real.exp_log hHs]
    ring
  have h2s : (0 : ℝ) < (2 : ℝ) ^ Nat.ceil x := by positivity
  calc Real.exp (2 * (Fintype.card E : ℝ) / (t : ℝ)) / (2 : ℝ) ^ Nat.ceil x
      = (Real.exp (2 * (Fintype.card E : ℝ) / (t : ℝ)) * (Hs.card : ℝ)) /
          ((Hs.card : ℝ) * (2 : ℝ) ^ Nat.ceil x) := by
        field_simp
    _ ≤ (2 : ℝ) ^ Nat.ceil x / ((Hs.card : ℝ) * (2 : ℝ) ^ Nat.ceil x) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        rw [hrest]
        exact hpow
    _ = 1 / (Hs.card : ℝ) := by
        field_simp

end History

/-! ## Claim 3.12 as a success probability -/

/-- **The analytic core at the paper's `k`**: `N²(1 − 1/t)^{2t(⌈log N⌉+1)} ≤ e^{−2}`.
This is the chain of `Sampling.sample_budget` stopped one step earlier. -/
theorem sample_budget_exp {t N : ℕ} (ht : 2 ≤ t) (hN : 1 ≤ N) :
    (N : ℝ) * N * (1 - 1 / (t : ℝ)) ^ (2 * t * (Nat.ceil (Real.log (N : ℝ)) + 1)) ≤
      Real.exp (-2) := by
  classical
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hbase : (0 : ℝ) < 1 - 1 / (t : ℝ) := by
    have : 1 / (t : ℝ) < 1 := by
      rw [div_lt_one ht0]; exact_mod_cast (by omega : 1 < t)
    linarith
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hA : (1 - 1 / (t : ℝ)) ^ (2 * t * (Nat.ceil (Real.log (N : ℝ)) + 1)) ≤
      Real.exp (-((2 * t * (Nat.ceil (Real.log (N : ℝ)) + 1) : ℕ) : ℝ) / (t : ℝ)) := by
    have hlog : Real.log (1 - 1 / (t : ℝ)) ≤ -(1 / (t : ℝ)) := by
      have h := Real.log_le_sub_one_of_pos hbase
      linarith
    calc (1 - 1 / (t : ℝ)) ^ (2 * t * (Nat.ceil (Real.log (N : ℝ)) + 1))
        = Real.exp (((2 * t * (Nat.ceil (Real.log (N : ℝ)) + 1) : ℕ) : ℝ) *
            Real.log (1 - 1 / (t : ℝ))) := by
          rw [Real.exp_natCast_mul, Real.exp_log hbase]
      _ ≤ Real.exp (((2 * t * (Nat.ceil (Real.log (N : ℝ)) + 1) : ℕ) : ℝ) *
            (-(1 / (t : ℝ)))) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlog (by positivity))
      _ = Real.exp (-((2 * t * (Nat.ceil (Real.log (N : ℝ)) + 1) : ℕ) : ℝ) / (t : ℝ)) := by
          congr 1
          ring
  have hkB : ((2 * t * (Nat.ceil (Real.log (N : ℝ)) + 1) : ℕ) : ℝ) / (t : ℝ) =
      2 * ((Nat.ceil (Real.log (N : ℝ)) : ℝ) + 1) := by
    push_cast
    field_simp
  have hB : Real.exp (-((2 * t * (Nat.ceil (Real.log (N : ℝ)) + 1) : ℕ) : ℝ) / (t : ℝ)) ≤
      Real.exp (-(2 * (Real.log (N : ℝ) + 1))) := by
    apply Real.exp_le_exp.mpr
    have hneg : -((2 * t * (Nat.ceil (Real.log (N : ℝ)) + 1) : ℕ) : ℝ) / (t : ℝ) =
        -(((2 * t * (Nat.ceil (Real.log (N : ℝ)) + 1) : ℕ) : ℝ) / (t : ℝ)) := by ring
    rw [hneg, hkB]
    have hc := Nat.le_ceil (Real.log (N : ℝ))
    linarith
  have hC : Real.exp (-(2 * (Real.log (N : ℝ) + 1))) =
      (N : ℝ)⁻¹ ^ 2 * Real.exp (-2) := by
    have hsplit : -(2 * (Real.log (N : ℝ) + 1)) = 2 * (-Real.log (N : ℝ)) + (-2) := by ring
    rw [hsplit, Real.exp_add]
    have h2 : Real.exp (2 * (-Real.log (N : ℝ))) = (N : ℝ)⁻¹ ^ 2 := by
      rw [show (2 : ℝ) * (-Real.log (N : ℝ)) = ((2 : ℕ) : ℝ) * (-Real.log (N : ℝ)) by
        norm_num]
      rw [Real.exp_natCast_mul, Real.exp_neg, Real.exp_log hN0]
    rw [h2]
  have hchain : (1 - 1 / (t : ℝ)) ^ (2 * t * (Nat.ceil (Real.log (N : ℝ)) + 1)) ≤
      (N : ℝ)⁻¹ ^ 2 * Real.exp (-2) :=
    hA.trans (hB.trans (le_of_eq hC))
  calc (N : ℝ) * N * (1 - 1 / (t : ℝ)) ^ (2 * t * (Nat.ceil (Real.log (N : ℝ)) + 1))
      ≤ (N : ℝ) * N * ((N : ℝ)⁻¹ ^ 2 * Real.exp (-2)) :=
        mul_le_mul_of_nonneg_left hchain (by positivity)
    _ = Real.exp (-2) := by
        field_simp

variable {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]

/-- **Claim 3.12's union bound in probability form**: for a uniformly random `k`-tuple of
coordinates, the probability that some pair of candidate vectors differs in more than `q`
coordinates yet agrees on the sample is at most `|A|² (M − q − 1)^k / M^k ≤ |A|²(1 − 1/t)^k`.
This is `card_bad_le` divided by the number `M^k` of tuples. -/
theorem bad_prob_le (A : Finset (α → β)) {t q k : ℕ} (ht : 2 ≤ t)
    (hM : 1 ≤ Fintype.card α) (_hk : 1 ≤ k) (hq : q = Fintype.card α / t) :
    unifProb (Finset.univ.filter (fun s : Fin k → α => Bad A q k s)) ≤
      (A.card : ℝ) ^ 2 * (1 - 1 / (t : ℝ)) ^ k := by
  classical
  set M := Fintype.card α with hMdef
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have ht1 : (1 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 1 < t)
  have hN : (Fintype.card (Fin k → α) : ℝ) = (M : ℝ) ^ k := by
    simp [M]
  have hNpos : (0 : ℝ) < (Fintype.card (Fin k → α) : ℝ) := by
    rw [hN]; positivity
  -- the counting bound, cast to ℝ
  have hcount : ((Finset.univ.filter (fun s : Fin k → α => Bad A q k s)).card : ℝ) ≤
      (A.card : ℝ) * (A.card : ℝ) * (((M - q - 1 : ℕ)) : ℝ) ^ k := by
    calc ((Finset.univ.filter (fun s : Fin k → α => Bad A q k s)).card : ℝ)
        ≤ ((A.card * A.card * (M - q - 1) ^ k : ℕ) : ℝ) := by
          exact_mod_cast card_bad_le A q k
      _ = (A.card : ℝ) * (A.card : ℝ) * (((M - q - 1 : ℕ)) : ℝ) ^ k := by
          push_cast
          ring
  -- the base inequality: agreement count ≤ (1 − 1/t)·M
  have hbase : (((M - q - 1 : ℕ)) : ℝ) ^ k ≤ (1 - 1 / (t : ℝ)) ^ k * (M : ℝ) ^ k := by
    have hbase_le : (((M - q - 1 : ℕ)) : ℝ) ≤ (1 - 1 / (t : ℝ)) * (M : ℝ) := by
      by_cases hqM : q < M
      · -- `M ≤ (q+1)·t`, so `M/t ≤ q+1`
        have hdecomp : t * q + M % t = M := by
          rw [hq]
          exact Nat.div_add_mod M t
        have hmod : M % t < t := Nat.mod_lt _ (by omega)
        have hmcast : (M : ℝ) = (t : ℝ) * (q : ℝ) + ((M % t : ℕ) : ℝ) := by
          have h' : ((t * q + M % t : ℕ) : ℝ) = (M : ℝ) := by exact_mod_cast hdecomp
          push_cast at h'
          linarith
        have hrcast : ((M % t : ℕ) : ℝ) < (t : ℝ) := by exact_mod_cast hmod
        have hdiv : (M : ℝ) / (t : ℝ) ≤ (q : ℝ) + 1 := by
          rw [div_le_iff₀ ht0]
          nlinarith
        have hqle : q + 1 ≤ M := by omega
        have hcast : (((M - q - 1 : ℕ)) : ℝ) = (M : ℝ) - ((q : ℝ) + 1) := by
          rw [Nat.sub_sub, Nat.cast_sub hqle]
          push_cast
          ring
        rw [hcast]
        have hmul : ((q : ℝ) + 1) * (t : ℝ) ≥ (M : ℝ) := by
          rw [ge_iff_le]
          rw [div_le_iff₀ ht0] at hdiv
          linarith
        have : (M : ℝ) - ((q : ℝ) + 1) ≤ (M : ℝ) - (M : ℝ) / (t : ℝ) := by
          linarith
        have hone : (1 - 1 / (t : ℝ)) * (M : ℝ) = (M : ℝ) - (M : ℝ) / (t : ℝ) := by ring
        linarith
      · -- `q ≥ M`: both sides are zero
        have h0 : M - q - 1 = 0 := by omega
        rw [h0]
        simp only [Nat.cast_zero]
        have : (0 : ℝ) ≤ (1 - 1 / (t : ℝ)) * (M : ℝ) := by
          have h1 : (0 : ℝ) ≤ 1 - 1 / (t : ℝ) := by
            have : 1 / (t : ℝ) < 1 := by rw [div_lt_one ht0]; exact ht1
            linarith
          positivity
        simpa using this
    calc (((M - q - 1 : ℕ)) : ℝ) ^ k
        ≤ ((1 - 1 / (t : ℝ)) * (M : ℝ)) ^ k :=
          pow_le_pow_left₀ (by positivity) hbase_le k
      _ = (1 - 1 / (t : ℝ)) ^ k * (M : ℝ) ^ k := by rw [mul_pow]
  unfold unifProb
  rw [div_le_iff₀ hNpos, hN]
  calc ((Finset.univ.filter (fun s : Fin k → α => Bad A q k s)).card : ℝ)
      ≤ (A.card : ℝ) * (A.card : ℝ) * (((M - q - 1 : ℕ)) : ℝ) ^ k := hcount
    _ ≤ (A.card : ℝ) * (A.card : ℝ) * ((1 - 1 / (t : ℝ)) ^ k * (M : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = (A.card : ℝ) ^ 2 * (1 - 1 / (t : ℝ)) ^ k * (M : ℝ) ^ k := by ring

/-- **Claim 3.12 with probability at least `1 − e^{−2}`**: at the paper's sample size
`k = 2t(⌈log |A|⌉ + 1)`, a uniformly random `k`-tuple is *good* (no badly-differing pair agrees on
it) with probability at least `1 − e^{−2} ≈ 0.865`. -/
theorem claim312_success_prob (A : Finset (α → β)) {t : ℕ} (ht : 2 ≤ t)
    (hM : 1 ≤ Fintype.card α) (hA : 1 ≤ A.card) :
    1 - Real.exp (-2) ≤
      unifProb (Finset.univ.filter
        (fun s : Fin (2 * t * (Nat.ceil (Real.log (A.card : ℝ)) + 1)) → α =>
          ¬ Bad A (Fintype.card α / t)
            (2 * t * (Nat.ceil (Real.log (A.card : ℝ)) + 1)) s)) := by
  classical
  haveI : Nonempty (Fin (2 * t * (Nat.ceil (Real.log (A.card : ℝ)) + 1)) → α) :=
    Fintype.card_pos_iff.mp (by
      rw [Fintype.card_fun]
      have hM0 : (0 : ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast (by omega : 0 < Fintype.card α)
      positivity)
  set k := 2 * t * (Nat.ceil (Real.log (A.card : ℝ)) + 1) with hk
  have hk1 : 1 ≤ k := by
    have : 1 ≤ 2 * t := by omega
    have : 1 ≤ Nat.ceil (Real.log (A.card : ℝ)) + 1 := by omega
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hfail : unifProb (Finset.univ.filter (fun s : Fin k → α => Bad A (Fintype.card α / t) k s)) ≤
      (A.card : ℝ) ^ 2 * (1 - 1 / (t : ℝ)) ^ k :=
    bad_prob_le A ht hM hk1 (q := Fintype.card α / t) rfl
  have hbudget : (A.card : ℝ) ^ 2 * (1 - 1 / (t : ℝ)) ^ k ≤ Real.exp (-2) := by
    have h := sample_budget_exp (t := t) (N := A.card) ht hA
    simpa [k, pow_two] using h
  have hcompl : unifProb (Finset.univ.filter (fun s : Fin k → α => Bad A (Fintype.card α / t) k s)) +
      unifProb (Finset.univ.filter
        (fun s : Fin k → α => ¬ Bad A (Fintype.card α / t) k s)) = 1 := by
    refine unifProb_compl (S := Finset.univ.filter (fun s : Fin k → α => Bad A (Fintype.card α / t) k s))
      (T := Finset.univ.filter (fun s : Fin k → α => ¬ Bad A (Fintype.card α / t) k s)) ?_ ?_
    · exact Finset.disjoint_filter.mpr (fun s _ h1 h2 => h2 h1)
    · rw [Finset.filter_union_filter_not_eq]
  linarith

/-- **Existence of a separating sample, from positive probability.**  The random sample is good
with positive probability, so a good sample exists — Claim 3.12's conclusion reached through the
probability layer rather than through the bad-tuple count. -/
theorem claim312_exists_via_prob (A : Finset (α → β)) {t : ℕ} (ht : 2 ≤ t)
    (hM : 1 ≤ Fintype.card α) (hA : 1 ≤ A.card) :
    ∃ s : Fin (2 * t * (Nat.ceil (Real.log (A.card : ℝ)) + 1)) → α,
      ¬ Bad A (Fintype.card α / t) (2 * t * (Nat.ceil (Real.log (A.card : ℝ)) + 1)) s := by
  have hpos : (0 : ℝ) < 1 - Real.exp (-2) := by
    have h1 : Real.exp (-2) < 1 := by
      rw [Real.exp_lt_one_iff]; norm_num
    linarith
  have hne := exists_of_unifProb_pos
    (S := Finset.univ.filter
      (fun s : Fin (2 * t * (Nat.ceil (Real.log (A.card : ℝ)) + 1)) → α =>
        ¬ Bad A (Fintype.card α / t)
          (2 * t * (Nat.ceil (Real.log (A.card : ℝ)) + 1)) s))
    (lt_of_lt_of_le hpos (claim312_success_prob A ht hM hA))
  obtain ⟨s, hs⟩ := hne
  exact ⟨s, by simpa using hs⟩

end DLMST