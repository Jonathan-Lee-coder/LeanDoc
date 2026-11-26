import DLMST.DriverCall

/-!
# Instance-local counts: §3.3–§3.5 with `m = |E₀|`

`DriverCall.lean` proved §3.5's count with `m := |E|`, the *ambient* edge type.  The display, however,
needs it at each call's own instance: a strict child has `E₀ ⊊ E`, and its error budget is
`10t²√(|E₀||P|) + 4|E₀|/t` — summing `√(|E||P_a|)` over a level's children would be too big.

Every ingredient of the global count is already a statement about `E₀`-edges only, except the two
counting facts, which filter `Finset.univ`:

* Lemma 3.11's `lost` (`History.lost`) counts bad rounds of *all* edges of the type;
* the sampling's `#mis ≤ |E|/t` counts mis-estimates of all edges in the round's fibre.

This file redoes the two counts against a set of edges `E₀`:

* **`History.lostOn`** — `lost` restricted to `E₀`, and **`lemma311_on`**: the same averaging argument
  with the generating function's product restricted to `E₀`, giving
  `lostOn·log 2 ≤ log|Hs| + 2|E₀|/t`.  The engine is `weighted_sum_le_on`: the schedules of the edges
  *outside* `E₀` contribute only the factor `(t²)^{|E|-|E₀|}`, which cancels against the same factor
  in the number of schedules — this is why no schedule on the subtype is needed.
* **`card_mis_leOn`** — the fibrewise identity `∑_r #(E₀ ∩ round r) = #(E₀ ∩ wrong)` gives
  `#(E₀ ∩ wrong) ≤ |E₀|/t` from precisely the per-round allowances it already has, with `hsum` read
  at `|E₀|` instead of `|E|`.

The geometric family `A r` and the sample are still over the round's fibre of *all* edges; restricting
them to `E₀`'s edges is the remaining step, recorded in the file's last section as the honest gap.
-/

namespace DLMST

open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] {G : WGraph V E}
  [LinearOrder E]

/-! ## Lemma 3.11 restricted to a set of edges -/

namespace History

/-- **`X_H(ρ)` on the instance's edges**: the number of edges of `E₀` whose assigned round is bad for
them.  This is the quantity §3.3 charges to `lost`; the history itself lives on the ambient `E`. -/
noncomputable def lostOn {t : ℕ} (H : History V E t) (E₀ : Finset E) (ρ : Sched E t) : ℕ :=
  (E₀.filter fun e => H.badFor e (ρ e)).card

theorem lostOn_le_lost {t : ℕ} (H : History V E t) (E₀ : Finset E) (ρ : Sched E t) :
    H.lostOn E₀ ρ ≤ H.lost ρ := by
  rw [lostOn, lost_def]
  exact Finset.card_le_card (fun e he =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp he).2⟩)

/-- **The engine, restricted**: `∑_ρ 2^{X_H^{E₀}(ρ)} ≤ (t² + 2t)^{|E₀|} · (t²)^{|E|-|E₀|}`.  Edges
outside `E₀` are scheduled too, but their factor is constantly `1` in the generating function, so they
only contribute the count `t²` each — exactly what cancels against `|Sched| = (t²)^{|E|}`. -/
theorem weighted_sum_le_on {t : ℕ} (H : History V E t) (E₀ : Finset E) :
    (∑ ρ : Sched E t, (2 : ℕ) ^ H.lostOn E₀ ρ) ≤
      (t * t + 2 * t) ^ E₀.card * (t * t) ^ (Fintype.card E - E₀.card) := by
  classical
  have hfactor : ∀ ρ : Sched E t,
      (2 : ℕ) ^ H.lostOn E₀ ρ =
        ∏ e : E, (if e ∈ E₀ then
          (2 : ℕ) ^ (if H.badFor e (ρ e) then 1 else 0) else 1) := by
    intro ρ
    have hcount : H.lostOn E₀ ρ = ∑ e ∈ E₀, (if H.badFor e (ρ e) then 1 else 0) := by
      rw [lostOn, Finset.card_filter]
    rw [hcount, ← Finset.prod_pow_eq_pow_sum, Finset.prod_ite_mem]
    rw [Finset.univ_inter]
  have hpi : (∑ ρ : Sched E t,
        ∏ e : E, (if e ∈ E₀ then
          (2 : ℕ) ^ (if H.badFor e (ρ e) then 1 else 0) else 1)) =
      ∏ e : E, ∑ r : Fin t × Fin t,
        (if e ∈ E₀ then (2 : ℕ) ^ (if H.badFor e r then 1 else 0) else 1) := by
    have h := Finset.sum_prod_piFinset (s := (Finset.univ : Finset (Fin t × Fin t)))
      (g := fun (e : E) (r : Fin t × Fin t) =>
        if e ∈ E₀ then (2 : ℕ) ^ (if H.badFor e r then 1 else 0) else 1)
    simpa [Sched, Fintype.piFinset_univ] using h
  have hstep : ∀ e : E,
      (∑ r : Fin t × Fin t,
        (if e ∈ E₀ then (2 : ℕ) ^ (if H.badFor e r then 1 else 0) else 1)) ≤
        if e ∈ E₀ then t * t + 2 * t else t * t := by
    intro e
    by_cases he : e ∈ E₀
    · have hite : (∑ r : Fin t × Fin t,
          (if e ∈ E₀ then (2 : ℕ) ^ (if H.badFor e r then 1 else 0) else 1)) =
          ∑ r : Fin t × Fin t, (2 : ℕ) ^ (if H.badFor e r then 1 else 0) :=
        Finset.sum_congr rfl fun r _ => by rw [ite_eq_left he]
      rw [hite, ite_eq_left he]
      exact H.genEdge_le e
    · have hite : (∑ r : Fin t × Fin t,
          (if e ∈ E₀ then (2 : ℕ) ^ (if H.badFor e r then 1 else 0) else 1)) =
          ∑ r : Fin t × Fin t, 1 :=
        Finset.sum_congr rfl fun r _ => by rw [ite_eq_right he]
      rw [hite, ite_eq_right he, Finset.sum_const, Finset.card_univ]
      simp
  have hprod : (∏ e : E, (if e ∈ E₀ then t * t + 2 * t else t * t)) =
      (t * t + 2 * t) ^ E₀.card * (t * t) ^ (Fintype.card E - E₀.card) := by
    have hsplit : (∏ e : E, (if e ∈ E₀ then t * t + 2 * t else t * t)) =
        (∏ e : E, (if e ∈ E₀ then t * t + 2 * t else 1)) *
          (∏ e : E, (if e ∈ E₀ then 1 else t * t)) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun e _ => by by_cases he : e ∈ E₀ <;> simp [he]
    have h1 : (∏ e : E, (if e ∈ E₀ then t * t + 2 * t else 1)) =
        (t * t + 2 * t) ^ E₀.card := by
      rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
    have h2 : (∏ e : E, (if e ∈ E₀ then 1 else t * t)) =
        (t * t) ^ (Fintype.card E - E₀.card) := by
      have hcongr : (∏ e : E, (if e ∈ E₀ then 1 else t * t)) =
          ∏ e : E, (if e ∈ (Finset.univ \ E₀ : Finset E) then t * t else 1) :=
        Finset.prod_congr rfl fun e _ => by
          by_cases he : e ∈ E₀
          · rw [ite_eq_left he, ite_eq_right (by simp [he])]
          · rw [ite_eq_right he, ite_eq_left (by simp [he])]
      rw [hcongr, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const, Finset.card_sdiff]
      congr 1
      simp
    rw [hsplit, h1, h2]
  calc (∑ ρ : Sched E t, (2 : ℕ) ^ H.lostOn E₀ ρ)
      = ∑ ρ : Sched E t, ∏ e : E, (if e ∈ E₀ then
          (2 : ℕ) ^ (if H.badFor e (ρ e) then 1 else 0) else 1) :=
        Finset.sum_congr rfl fun ρ _ => hfactor ρ
    _ = ∏ e : E, ∑ r : Fin t × Fin t,
        (if e ∈ E₀ then (2 : ℕ) ^ (if H.badFor e r then 1 else 0) else 1) := hpi
    _ ≤ ∏ e : E, (if e ∈ E₀ then t * t + 2 * t else t * t) :=
        Finset.prod_le_prod fun e _ => hstep e
    _ = (t * t + 2 * t) ^ E₀.card * (t * t) ^ (Fintype.card E - E₀.card) := hprod

/-- **Lemma 3.11 on a set of edges.**  One deterministic schedule `ρ` bounds, for every history in
`Hs` simultaneously, the bad-round count *of the instance's edges*:
`X_H^{E₀}(ρ)·log 2 ≤ log|Hs| + 2|E₀|/t`.  This is the form a strict child's display needs: the
per-call error budget is stated with `m := |E₀|`, not with the ambient `|E|`.

The proof is `lemma311`'s, with `(t²+2t)^{|E|}` replaced by `(t²+2t)^{|E₀|}·(t²)^{|E|-|E₀|}`; dividing
by `|Sched| = (t²)^{|E|}` leaves exactly `(1+2/t)^{|E₀|}`. -/
theorem lemma311_on {t : ℕ} (ht : 2 ≤ t) (Hs : Finset (History V E t)) (E₀ : Finset E) :
    ∃ ρ : Sched E t, ∀ H ∈ Hs,
      (H.lostOn E₀ ρ : ℝ) * Real.log 2 ≤
        Real.log (Hs.card : ℝ) + 2 * (E₀.card : ℝ) / (t : ℝ) := by
  classical
  by_cases hne : Hs.Nonempty
  · obtain ⟨ρ, hρ⟩ := exists_le_average
      ⟨fun _ => (⟨0, by omega⟩, ⟨0, by omega⟩)⟩
      (fun ρ : Sched E t => ∑ H ∈ Hs, (2 : ℝ) ^ H.lostOn E₀ ρ)
    refine ⟨ρ, fun H hH => ?_⟩
    have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
    have hHs : (0 : ℝ) < (Hs.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hne
    have hm : (0 : ℝ) ≤ (E₀.card : ℝ) := by positivity
    have hN : (Fintype.card (Sched E t) : ℝ) = ((t : ℝ) * t) ^ Fintype.card E := by
      simp [Sched, Fintype.card_prod]
    have hsum : (∑ ρ : Sched E t, ∑ H ∈ Hs, (2 : ℝ) ^ H.lostOn E₀ ρ) ≤
        (Hs.card : ℝ) * ((((t * t + 2 * t : ℕ) : ℝ)) ^ E₀.card *
          (((t * t : ℕ) : ℝ)) ^ (Fintype.card E - E₀.card)) := by
      calc (∑ ρ : Sched E t, ∑ H ∈ Hs, (2 : ℝ) ^ H.lostOn E₀ ρ)
          = ∑ H ∈ Hs, ∑ ρ : Sched E t, (2 : ℝ) ^ H.lostOn E₀ ρ := Finset.sum_comm
        _ ≤ ∑ _H ∈ Hs, ((((t * t + 2 * t : ℕ) : ℝ)) ^ E₀.card *
              (((t * t : ℕ) : ℝ)) ^ (Fintype.card E - E₀.card)) :=
            Finset.sum_le_sum fun H _ => by
              exact_mod_cast History.weighted_sum_le_on H E₀
        _ = (Hs.card : ℝ) * ((((t * t + 2 * t : ℕ) : ℝ)) ^ E₀.card *
              (((t * t : ℕ) : ℝ)) ^ (Fintype.card E - E₀.card)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hratio : ((((t * t + 2 * t : ℕ) : ℝ)) ^ E₀.card *
          (((t * t : ℕ) : ℝ)) ^ (Fintype.card E - E₀.card)) /
        (Fintype.card (Sched E t) : ℝ) = (1 + 2 / (t : ℝ)) ^ E₀.card := by
      have hB : (((t * t : ℕ) : ℝ)) = (t : ℝ) * t := by push_cast; ring
      have hpow : ((t : ℝ) * t) ^ Fintype.card E =
          ((t : ℝ) * t) ^ E₀.card * ((t : ℝ) * t) ^ (Fintype.card E - E₀.card) := by
        rw [← pow_add, Nat.add_sub_cancel' (Finset.card_le_univ E₀)]
      have hBt : (t : ℝ) * t ≠ 0 := by positivity
      rw [hN, hB, hpow, mul_div_mul_right _ _ (pow_ne_zero _ hBt), ← div_pow]
      congr 1
      have h1 : (((t * t + 2 * t : ℕ) : ℝ)) = (t : ℝ) * ((t : ℝ) + 2) := by
        push_cast; ring
      rw [h1]
      field_simp
    have havg : (2 : ℝ) ^ H.lostOn E₀ ρ ≤
        (Hs.card : ℝ) * (1 + 2 / (t : ℝ)) ^ E₀.card := by
      refine le_trans ?_ (le_trans hρ ?_)
      · exact Finset.single_le_sum
          (f := fun H' : History V E t => (2 : ℝ) ^ H'.lostOn E₀ ρ)
          (fun _ _ => by positivity) hH
      · calc (∑ ρ : Sched E t, ∑ H ∈ Hs, (2 : ℝ) ^ H.lostOn E₀ ρ) /
              (Fintype.card (Sched E t) : ℝ)
            ≤ ((Hs.card : ℝ) * ((((t * t + 2 * t : ℕ) : ℝ)) ^ E₀.card *
                (((t * t : ℕ) : ℝ)) ^ (Fintype.card E - E₀.card))) /
                (Fintype.card (Sched E t) : ℝ) :=
              div_le_div_of_nonneg_right hsum (by positivity)
          _ = (Hs.card : ℝ) * (1 + 2 / (t : ℝ)) ^ E₀.card := by
              rw [mul_div_assoc, hratio]
    have hlog := Real.log_le_log (by positivity) havg
    rw [Real.log_pow, Real.log_mul hHs.ne' (by positivity), Real.log_pow] at hlog
    have hlog2 : Real.log (1 + 2 / (t : ℝ)) ≤ 2 / (t : ℝ) := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 2 / (t : ℝ))
      linarith
    have hmul := mul_le_mul_of_nonneg_left hlog2 hm
    have hcast : (E₀.card : ℝ) * (2 / (t : ℝ)) = 2 * (E₀.card : ℝ) / (t : ℝ) := by ring
    linarith
  · refine ⟨fun _ => (⟨0, by omega⟩, ⟨0, by omega⟩), ?_⟩
    intro H hH
    exact absurd ⟨H, hH⟩ hne

end History

/-! ## The sampling on the instance's own fibres

Claim 3.12 is applied per round to the coordinates *of the instance* — `{e // e ∈ E₀ ∧ slot e = r}`
— not to every edge of the type that happens to fall in round `r`.  Everything below is the
corresponding re-run of `EstimateBound`/`Queries`: the statements are identical, only the fibre
type is the instance's. -/

/-- **`card_mis_le` on the instance.**  The fibrewise identity `∑_r #(E₀ ∩ wrong ∩ round r) =
#(E₀ ∩ wrong)`, so per-round allowances totalling `|E₀|` give `#(E₀ ∩ wrong) ≤ |E₀|/t`. -/
theorem card_mis_leOn {σ : Type*} [Fintype σ] [DecidableEq σ] {t : ℕ} (slot : E → σ)
    (E₀ : Finset E) (wrong : E → Prop) [DecidablePred wrong] (m : σ → ℕ)
    (hper : ∀ r, ((E₀.filter fun e => wrong e ∧ slot e = r).card : ℝ) ≤
      (m r : ℝ) / (t : ℝ))
    (hsum : (∑ r, m r) ≤ E₀.card) :
    ((E₀.filter wrong).card : ℝ) ≤ (E₀.card : ℝ) / (t : ℝ) := by
  classical
  have hsplit : (E₀.filter wrong).card =
      ∑ r : σ, (E₀.filter fun e => wrong e ∧ slot e = r).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := slot) (t := Finset.univ)
      (s := E₀.filter wrong) (fun e _ => Finset.mem_univ _)]
    exact Finset.sum_congr rfl fun r _ => by
      rw [Finset.filter_filter]
  have h1 : ((E₀.filter wrong).card : ℝ) =
      ∑ r : σ, ((E₀.filter fun e => wrong e ∧ slot e = r).card : ℝ) := by
    rw [hsplit]
    push_cast
    rfl
  rw [h1]
  calc ∑ r : σ, ((E₀.filter fun e => wrong e ∧ slot e = r).card : ℝ)
      ≤ ∑ r : σ, (m r : ℝ) / (t : ℝ) := Finset.sum_le_sum fun r _ => hper r
    _ = ((∑ r : σ, m r : ℕ) : ℝ) / (t : ℝ) := by
        rw [← Finset.sum_div]
        push_cast
        rfl
    _ ≤ (E₀.card : ℝ) / (t : ℝ) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hsum) (by positivity)

/-- **Claim 3.12's sample on the instance's fibres.**  Same sample as `sampleSets`, applied to the
candidate family indexed by `{e // e ∈ E₀ ∧ slot e = r}`. -/
noncomputable def sampleSetsOn {σ : Type*} [Fintype σ] [DecidableEq σ] {t : ℕ} (E₀ : Finset E)
    (ht : 2 ≤ t) (slot : E → σ)
    (A : ∀ r : σ, Finset ({e : E // e ∈ E₀ ∧ slot e = r} → Pref)) :
    ∀ r : σ, Finset {e : E // e ∈ E₀ ∧ slot e = r} :=
  fun r => Classical.choose
    (claim312 (A r) t (Fintype.card {e : E // e ∈ E₀ ∧ slot e = r} / t) ht rfl)

theorem sampleSetsOn_card {σ : Type*} [Fintype σ] [DecidableEq σ] {t : ℕ} (E₀ : Finset E)
    (ht : 2 ≤ t) (slot : E → σ)
    (A : ∀ r : σ, Finset ({e : E // e ∈ E₀ ∧ slot e = r} → Pref)) (r : σ) :
    (sampleSetsOn E₀ ht slot A r).card ≤
      2 * t * (Nat.ceil (Real.log ((A r).card : ℝ)) + 1) :=
  (Classical.choose_spec
    (claim312 (A r) t (Fintype.card {e : E // e ∈ E₀ ∧ slot e = r} / t) ht rfl)).1

theorem sampleSetsOn_sep {σ : Type*} [Fintype σ] [DecidableEq σ] {t : ℕ} (E₀ : Finset E)
    (ht : 2 ≤ t) (slot : E → σ)
    (A : ∀ r : σ, Finset ({e : E // e ∈ E₀ ∧ slot e = r} → Pref)) (r : σ) :
    ∀ a ∈ A r, ∀ b ∈ A r, (∀ x ∈ sampleSetsOn E₀ ht slot A r, a x = b x) →
      (Finset.univ.filter fun x : {e : E // e ∈ E₀ ∧ slot e = r} => a x ≠ b x).card ≤
        Fintype.card {e : E // e ∈ E₀ ∧ slot e = r} / t :=
  (Classical.choose_spec
    (claim312 (A r) t (Fintype.card {e : E // e ∈ E₀ ∧ slot e = r} / t) ht rfl)).2

/-- **A round's mis-estimates, on the instance.**  Agreement on the sample bounds the mis-estimated
edges *of the instance* in round `r` by `#(E₀ ∩ round r)/t`. -/
theorem per_round_misOn {σ : Type*} [Fintype σ] [DecidableEq σ] {t : ℕ} (E₀ : Finset E)
    (ht : 2 ≤ t) (slot : E → σ)
    (A : ∀ r : σ, Finset ({e : E // e ∈ E₀ ∧ slot e = r} → Pref)) (truth est : E → Pref)
    (htruth : ∀ r, (fun x : {e : E // e ∈ E₀ ∧ slot e = r} => truth x.1) ∈ A r)
    (hest : ∀ r, (fun x : {e : E // e ∈ E₀ ∧ slot e = r} => est x.1) ∈ A r)
    (hagree : ∀ (r : σ) (x : {e : E // e ∈ E₀ ∧ slot e = r}),
      x ∈ sampleSetsOn E₀ ht slot A r → est x.1 = truth x.1)
    (r : σ) :
    ((E₀.filter fun e => est e ≠ truth e ∧ slot e = r).card : ℝ) ≤
      ((E₀.filter fun e => slot e = r).card : ℝ) / (t : ℝ) := by
  classical
  have hsep := sampleSetsOn_sep E₀ ht slot A r
    (fun x : {e : E // e ∈ E₀ ∧ slot e = r} => truth x.1) (htruth r)
    (fun x : {e : E // e ∈ E₀ ∧ slot e = r} => est x.1) (hest r)
    (fun x hx => (hagree r x hx).symm)
  have hfilter : (Finset.univ.filter fun x : {e : E // e ∈ E₀ ∧ slot e = r} =>
        est x.1 ≠ truth x.1) =
      (Finset.univ.filter fun x : {e : E // e ∈ E₀ ∧ slot e = r} => truth x.1 ≠ est x.1) := by
    refine Finset.filter_congr fun x _ => ?_
    exact ne_comm
  have h' : ((Finset.univ.filter fun x : {e : E // e ∈ E₀ ∧ slot e = r} =>
        est x.1 ≠ truth x.1).card : ℝ) ≤
      (Fintype.card {e : E // e ∈ E₀ ∧ slot e = r} : ℝ) / (t : ℝ) := by
    have h1 : ((Finset.univ.filter fun x : {e : E // e ∈ E₀ ∧ slot e = r} =>
          est x.1 ≠ truth x.1).card : ℝ) ≤
        ((Fintype.card {e : E // e ∈ E₀ ∧ slot e = r} / t : ℕ) : ℝ) := by
      rw [hfilter]
      exact_mod_cast hsep
    exact le_trans h1 Nat.cast_div_le
  have hbij : (Finset.univ.filter fun x : {e : E // e ∈ E₀ ∧ slot e = r} =>
        est x.1 ≠ truth x.1).card =
      (E₀.filter fun e => est e ≠ truth e ∧ slot e = r).card := by
    refine Finset.card_bij (fun (x : {e : E // e ∈ E₀ ∧ slot e = r}) _ => x.1) ?_ ?_ ?_
    · intro x hx
      exact Finset.mem_filter.mpr ⟨x.2.1, (Finset.mem_filter.mp hx).2, x.2.2⟩
    · intro x₁ _ x₂ _ h
      exact Subtype.ext h
    · intro e he
      obtain ⟨hE, hne, hslot⟩ := Finset.mem_filter.mp he
      exact ⟨⟨e, hE, hslot⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩, rfl⟩
  have hcard : (Fintype.card {e : E // e ∈ E₀ ∧ slot e = r} : ℝ) =
      ((E₀.filter fun e => slot e = r).card : ℝ) := by
    have hset : (Finset.univ.filter fun e : E => e ∈ E₀ ∧ slot e = r) =
        (E₀.filter fun e => slot e = r) := by
      ext e
      simp [and_comm]
    rw [Fintype.card_subtype, hset]
  rw [hbij, hcard] at h'
  exact h'

/-- **The instance's mis-estimate total.**  Summing the per-round counts over the instance's
`E₀`-fibres gives `#(E₀ ∩ mis) ≤ |E₀|/t`, with `mᵢ` the instance's own round sizes. -/
theorem mis_count_of_sampleOn {σ : Type*} [Fintype σ] [DecidableEq σ] {t : ℕ} (E₀ : Finset E)
    (ht : 2 ≤ t) (slot : E → σ)
    (A : ∀ r : σ, Finset ({e : E // e ∈ E₀ ∧ slot e = r} → Pref)) (truth est : E → Pref)
    (htruth : ∀ r, (fun x : {e : E // e ∈ E₀ ∧ slot e = r} => truth x.1) ∈ A r)
    (hest : ∀ r, (fun x : {e : E // e ∈ E₀ ∧ slot e = r} => est x.1) ∈ A r)
    (hagree : ∀ (r : σ) (x : {e : E // e ∈ E₀ ∧ slot e = r}),
      x ∈ sampleSetsOn E₀ ht slot A r → est x.1 = truth x.1) :
    ((E₀.filter fun e => est e ≠ truth e).card : ℝ) ≤ (E₀.card : ℝ) / (t : ℝ) := by
  classical
  refine card_mis_leOn slot E₀ (fun e => est e ≠ truth e)
    (fun r => (E₀.filter fun e => slot e = r).card) ?_ ?_
  · intro r
    exact per_round_misOn E₀ ht slot A truth est htruth hest hagree r
  · rw [Finset.card_eq_sum_card_fiberwise (f := slot) (s := (E₀ : Finset E))
      (t := (Finset.univ : Finset σ)) (fun e he => Finset.mem_univ _)]

/-! ## The estimate read off the instance's family

A per-round candidate on the instance's fibres is not a function of all `E`; the §3.3 predicates want
one.  `estOfOn` extends it by a fixed default outside `E₀`, where no count ever looks. -/

/-- The global estimate induced by a per-round instance family: the chosen candidate on the instance,
an arbitrary `Pref` elsewhere. -/
noncomputable def estOfOn {t : ℕ} (E₀ : Finset E) (slot : E → Fin t × Fin t)
    (c : ∀ r : Fin t × Fin t, {e : E // e ∈ E₀ ∧ slot e = r} → Pref) : E → Pref :=
  fun e => if h : e ∈ E₀ then c (slot e) ⟨e, h, rfl⟩ else Pref.find

theorem estOfOn_of_mem {t : ℕ} (E₀ : Finset E) (slot : E → Fin t × Fin t)
    (c : ∀ r : Fin t × Fin t, {e : E // e ∈ E₀ ∧ slot e = r} → Pref) {e : E} (he : e ∈ E₀) :
    estOfOn E₀ slot c e = c (slot e) ⟨e, he, rfl⟩ := by
  unfold estOfOn
  rw [dite_eq_left he]

/-! ## The geometric family on the instance's fibres -/

/-- **The paper's family `A`, restricted to the instance's edges of each round.**  Same decoding as
`geomFamily`, with the coordinate type `{e // e ∈ E₀ ∧ slot e = r}`. -/
noncomputable def geomFamilyOn {t : ℕ} (H : History V E t) (slot : E → Fin t × Fin t)
    (E₀ : Finset E)
    (eN : ∀ (b i : Fin t), Ground G (H.spoke b i) (H.forest b i) ≃
      Fin (Fintype.card (Ground G (H.spoke b i) (H.forest b i))))
    (r : Fin t × Fin t) : Finset ({e : E // e ∈ E₀ ∧ slot e = r} → Pref) :=
  roundCand (G := G) (σ := H.spoke r.1 r.2) (F := H.forest r.1 r.2)
    (ιE := fun x : {e : E // e ∈ E₀ ∧ slot e = r} => x.1) (eN r.1 r.2)

/-- **`htruth` on the instance.**  The truth restricted to the instance's fibre lies in the
instance's family. -/
theorem truth_of_historyOn {t : ℕ} (H : History V E t) (E₀ : Finset E)
    (hcons : H.Consistent (G := G))
    (hF : ∀ b i, IsForest G (H.forest b i))
    (hFsp : ∀ (b i : Fin t) (g : E), g ∈ H.forest b i → ¬ IsSpoke (H.spoke b i) g)
    (slot : E → Fin t × Fin t)
    (eN : ∀ (b i : Fin t), Ground G (H.spoke b i) (H.forest b i) ≃
      Fin (Fintype.card (Ground G (H.spoke b i) (H.forest b i)))) :
    ∀ r : Fin t × Fin t,
      (fun x : {e : E // e ∈ E₀ ∧ slot e = r} => H.pref x.1 r.1 r.2) ∈
        geomFamilyOn (G := G) H slot E₀ eN r := by
  intro r
  have hmem := truth_mem_roundCand (G := G) (σ := H.spoke r.1 r.2) (F := H.forest r.1 r.2)
    (hF r.1 r.2) (hFsp r.1 r.2)
    (fun x : {e : E // e ∈ E₀ ∧ slot e = r} => x.1) (eN r.1 r.2)
  have hv : (fun x : {e : E // e ∈ E₀ ∧ slot e = r} => H.pref x.1 r.1 r.2)
      = (fun x : {e : E // e ∈ E₀ ∧ slot e = r}
          => actOf G (H.spoke r.1 r.2) (H.forest r.1 r.2) x.1) :=
    funext fun x => hcons x.1 r.1 r.2
  rw [hv]
  exact hmem

/-- **`hest` on the instance.**  The estimate read off one candidate per round restricts, on the
instance's fibre, to that candidate. -/
theorem est_of_choiceOn {t : ℕ} (H : History V E t) (slot : E → Fin t × Fin t) (E₀ : Finset E)
    (eN : ∀ (b i : Fin t), Ground G (H.spoke b i) (H.forest b i) ≃
      Fin (Fintype.card (Ground G (H.spoke b i) (H.forest b i))))
    (c : ∀ r : Fin t × Fin t, {e : E // e ∈ E₀ ∧ slot e = r} → Pref)
    (hc : ∀ r, c r ∈ geomFamilyOn (G := G) H slot E₀ eN r) :
    ∀ r : Fin t × Fin t,
      (fun x : {e : E // e ∈ E₀ ∧ slot e = r} => estOfOn E₀ slot c x.1) ∈
        geomFamilyOn (G := G) H slot E₀ eN r := by
  intro r
  have hv : (fun x : {e : E // e ∈ E₀ ∧ slot e = r} => estOfOn E₀ slot c x.1) = c r := by
    funext x
    obtain ⟨e', hE, he⟩ := x
    rw [estOfOn_of_mem E₀ slot c hE]
    cases he
    rfl
  rw [hv]
  exact hc r

/-- The truth membership in the shape the driver uses, `H.pref · (slot ·)`. -/
theorem truth_of_history_slotOn {t : ℕ} (H : History V E t) (E₀ : Finset E)
    (hcons : H.Consistent (G := G))
    (hF : ∀ b i, IsForest G (H.forest b i))
    (hFsp : ∀ (b i : Fin t) (g : E), g ∈ H.forest b i → ¬ IsSpoke (H.spoke b i) g)
    (slot : E → Fin t × Fin t)
    (eN : ∀ (b i : Fin t), Ground G (H.spoke b i) (H.forest b i) ≃
      Fin (Fintype.card (Ground G (H.spoke b i) (H.forest b i)))) :
    ∀ r : Fin t × Fin t,
      (fun x : {e : E // e ∈ E₀ ∧ slot e = r} => H.pref x.1 (slot x.1).1 (slot x.1).2) ∈
        geomFamilyOn (G := G) H slot E₀ eN r := by
  intro r
  have hmem := truth_of_historyOn (G := G) H E₀ hcons hF hFsp slot eN r
  have hv : (fun x : {e : E // e ∈ E₀ ∧ slot e = r} => H.pref x.1 (slot x.1).1 (slot x.1).2)
      = (fun x : {e : E // e ∈ E₀ ∧ slot e = r} => H.pref x.1 r.1 r.2) := by
    funext x
    obtain ⟨e', hE, he⟩ := x
    cases he
    rfl
  rw [hv]
  exact hmem

/-! ## §3.3's instance bound with the instance-local counts -/

namespace CallOut

namespace RoundData

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ} {P : Finset V} {E₀ : Finset E}

/-- **The two halves with `lostOn`.**  `card_U_le_bad_add_mis` with the bad half read as the
instance's own `lostOn`. -/
theorem card_U_le_lost_add_misOn (D : RoundData G P E₀ ι t) {s : ℕ} (H : History V E s)
    (est : E → Pref) (slot : E → Fin s × Fin s)
    (h : ∀ e ∈ E₀, ¬ supported G D.F e → H.errOf est e (slot e)) :
    D.U.card ≤ H.lostOn E₀ slot +
      (E₀.filter fun e => est e ≠ H.pref e (slot e).1 (slot e).2).card :=
  D.card_U_le_bad_add_mis H est slot h

/-- **§3.3's instance bound, local in `m = |E₀|`.**  Same as `card_U_le_number_bound_of_all_mis`
with `lost` replaced by `lostOn`, `hmE : |E₀| ≤ m`, and the mis-estimate count on `E₀` alone. -/
theorem card_U_le_number_bound_of_all_misOn (D : RoundData G P E₀ ι t) {s : ℕ}
    (H : History V E s) (est : E → Pref) (slot : E → Fin s × Fin s) {m n : ℝ} (ht : 0 < t)
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hmE : (E₀.card : ℝ) ≤ m)
    (h : ∀ e ∈ E₀, ¬ supported G D.F e → H.errOf est e (slot e))
    (hlost : (H.lostOn E₀ slot : ℝ) * Real.log 2 ≤
      (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 * Real.sqrt (m * n) + 2 * m / (t : ℝ))
    (hmis : ((E₀.filter fun e => est e ≠ H.pref e (slot e).1 (slot e).2).card : ℝ) ≤
      (E₀.card : ℝ) / (t : ℝ)) :
    (D.U.card : ℝ) ≤ 10 * (t : ℝ) ^ 2 * Real.sqrt (m * n) + 4 * m / (t : ℝ) := by
  have ht' : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hmis' : ((E₀.filter fun e => est e ≠ H.pref e (slot e).1 (slot e).2).card : ℝ) ≤
      m / (t : ℝ) :=
    le_trans hmis (div_le_div_of_nonneg_right hmE ht'.le)
  have hU : (D.U.card : ℝ) ≤ (H.lostOn E₀ slot : ℝ) +
      ((E₀.filter fun e => est e ≠ H.pref e (slot e).1 (slot e).2).card : ℝ) := by
    have hsplit := D.card_U_le_lost_add_misOn H est slot h
    calc (D.U.card : ℝ) ≤ ((H.lostOn E₀ slot +
          (E₀.filter fun e => est e ≠ H.pref e (slot e).1 (slot e).2).card : ℕ) : ℝ) := by
          exact_mod_cast hsplit
      _ = (H.lostOn E₀ slot : ℝ) +
          ((E₀.filter fun e => est e ≠ H.pref e (slot e).1 (slot e).2).card : ℝ) := by
          push_cast; ring
  exact error_count_le_of_U_add (U := (D.U.card : ℝ)) (lost := (H.lostOn E₀ slot : ℝ))
    (err2 := ((E₀.filter fun e => est e ≠ H.pref e (slot e).1 (slot e).2).card : ℝ))
    (t := (t : ℝ)) ht' hm hn hU hlost hmis'

/-- **§3.3's instance error premise, local in `m = |E₀|`, with the sample computed.**  The
`_on` version of `card_U_le_number_bound_of_queries`: the candidate family, its coverage, the
estimate and the sample all live on `{e // e ∈ E₀ ∧ slot e = r}`, so the budget is stated with
`m := |E₀|`. -/
theorem card_U_le_number_bound_of_queriesOn (D : RoundData G P E₀ ι t) {s : ℕ}
    (H : History V E s) (est : E → Pref) (slot : E → Fin s × Fin s) {m n : ℝ} (ht : 2 ≤ t)
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hmE : (E₀.card : ℝ) ≤ m)
    (A : ∀ r : Fin s × Fin s, Finset ({e : E // e ∈ E₀ ∧ slot e = r} → Pref))
    (htruth : ∀ r : Fin s × Fin s,
      (fun x : {e : E // e ∈ E₀ ∧ slot e = r} => H.pref x.1 (slot x.1).1 (slot x.1).2) ∈ A r)
    (hest : ∀ r : Fin s × Fin s, (fun x : {e : E // e ∈ E₀ ∧ slot e = r} => est x.1) ∈ A r)
    (hagree : ∀ (r : Fin s × Fin s) (x : {e : E // e ∈ E₀ ∧ slot e = r}),
      x ∈ sampleSetsOn E₀ ht slot A r → est x.1 = H.pref x.1 (slot x.1).1 (slot x.1).2)
    (h : ∀ e ∈ E₀, ¬ supported G D.F e → H.errOf est e (slot e))
    (hlost : (H.lostOn E₀ slot : ℝ) * Real.log 2 ≤
      (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 * Real.sqrt (m * n) + 2 * m / (t : ℝ)) :
    (D.U.card : ℝ) ≤ 10 * (t : ℝ) ^ 2 * Real.sqrt (m * n) + 4 * m / (t : ℝ) := by
  have hmis : ((E₀.filter fun e => est e ≠ H.pref e (slot e).1 (slot e).2).card : ℝ) ≤
      (E₀.card : ℝ) / (t : ℝ) :=
    mis_count_of_sampleOn E₀ ht slot A (fun e => H.pref e (slot e).1 (slot e).2) est
      htruth hest hagree
  exact D.card_U_le_number_bound_of_all_misOn H est slot (by omega) hm hn hmE h hlost hmis

end RoundData

end CallOut

/-! ## The table history, with the instance-local budget -/

section HistoryOfTable

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ} {P : Finset V} {E₀ : Finset E}

/-- **§3.5's bound for the table-driven history at the instance's own `m = |E₀|`.**  Everything the
`geomFamily` layer supplies is derived on the instance's fibres (`truth_of_history_slotOn`,
`est_of_choiceOn`), `hFsp` comes from the spoke rule, and the sample is `sampleSetsOn` — computed from
the instance's family before any query.  The hypotheses left are the consistency `hc`, Lemma 3.7's
per-edge premise, Lemma 3.11's `lostOn` bound, the batches' supply and the numbers. -/
theorem card_U_le_number_bound_of_tableOn (D : CallOut.RoundData G P E₀ ι t)
    (B : Fin t → Fin t → Finset E) (k : ℕ) [Nonempty E] (hk : 1 ≤ k)
    (hadm : ∀ (i j : Fin t) (v : V), ∃ e ∈ Bv G v (B i j), e ∉ D.F)
    (slot : E → Fin t × Fin t)
    (eN : ∀ (b i : Fin t), Ground G (spokeTable (G := G) B (fun x => x ∉ D.F) k b i)
      (forestUpTo D (b, i)) ≃
        Fin (Fintype.card (Ground G (spokeTable (G := G) B (fun x => x ∉ D.F) k b i)
          (forestUpTo D (b, i)))))
    (c : ∀ r : Fin t × Fin t, {e : E // e ∈ E₀ ∧ slot e = r} → Pref)
    (hc : ∀ r, c r ∈ geomFamilyOn (G := G)
      (historyOfTable D B (fun x => x ∉ D.F) k) slot E₀ (fun b i => eN b i) r)
    (ht : 2 ≤ t)
    (h : ∀ e ∈ E₀, ¬ supported G D.F e →
      (historyOfTable D B (fun x => x ∉ D.F) k).errOf (estOfOn E₀ slot c) e (slot e))
    (hlost : ((historyOfTable D B (fun x => x ∉ D.F) k).lostOn E₀ slot : ℝ) * Real.log 2 ≤
      (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 * Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) +
        2 * (E₀.card : ℝ) / (t : ℝ))
    (hagree : ∀ (r : Fin t × Fin t) (x : {e : E // e ∈ E₀ ∧ slot e = r}),
      x ∈ sampleSetsOn E₀ ht slot
        (geomFamilyOn (G := G) (historyOfTable D B (fun x => x ∉ D.F) k) slot E₀
          (fun b i => eN b i)) r →
      c (slot x.1) ⟨x.1, x.2.1, rfl⟩ =
        (historyOfTable D B (fun x => x ∉ D.F) k).pref x.1 r.1 r.2) :
    ((D.toCall.U).card : ℝ) ≤ 10 * (t : ℝ) ^ 2 * Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) +
      4 * (E₀.card : ℝ) / (t : ℝ) := by
  set H := historyOfTable D B (fun x => x ∉ D.F) k with hH
  set A := geomFamilyOn (G := G) H slot E₀ (fun b i => eN b i) with hA
  have htr : ∀ r : Fin t × Fin t,
      (fun x : {e : E // e ∈ E₀ ∧ slot e = r} => H.pref x.1 (slot x.1).1 (slot x.1).2) ∈ A r :=
    truth_of_history_slotOn (G := G) H E₀
      (historyOfRoundData_consistent D (spokeTable (G := G) B (fun x => x ∉ D.F) k))
      (isForest_historyOfRoundData D (spokeTable (G := G) B (fun x => x ∉ D.F) k))
      (hFsp_historyOfTable D B k hk hadm) slot (fun b i => eN b i)
  have hest : ∀ r : Fin t × Fin t,
      (fun x : {e : E // e ∈ E₀ ∧ slot e = r} => estOfOn E₀ slot c x.1) ∈ A r :=
    est_of_choiceOn (G := G) H slot E₀ (fun b i => eN b i) c hc
  have hagree' : ∀ (r : Fin t × Fin t) (x : {e : E // e ∈ E₀ ∧ slot e = r}),
      x ∈ sampleSetsOn E₀ ht slot A r →
        estOfOn E₀ slot c x.1 = H.pref x.1 (slot x.1).1 (slot x.1).2 := by
    intro r x hx
    obtain ⟨e', hE, he⟩ := x
    rw [estOfOn_of_mem E₀ slot c hE]
    cases he
    exact hagree (slot e') ⟨e', hE, rfl⟩ hx
  have hmain := CallOut.RoundData.card_U_le_number_bound_of_queriesOn (D := D) H
    (estOfOn E₀ slot c) slot ht (Nat.cast_nonneg _) (Nat.cast_nonneg _) le_rfl A htr hest
    hagree' h hlost
  rw [congrArg Finset.card (CallOut.RoundData.toCall_U_eq D)]
  exact hmain

end HistoryOfTable

/-! ## The driver's evidence at the instance's own `m` -/

namespace DriverCall

variable {P : Finset V} {E₀ : Finset E} {t : ℕ} [Nonempty E]

/-- **The sampling evidence of one call, local in the instance.**  Same fields as `Evidence`, but the
candidate family, the estimate and Lemma 3.11's count are all on `E₀`'s edges of each round, so the
budget `hlost` is stated with `|E₀|` — the shape a strict child's display needs. -/
structure EvidenceOn (R : DriverCall G P E₀ t) where
  c : (r : Fin t × Fin t) → {e : E // e ∈ E₀ ∧ R.sched e = r} → Pref
  hc : ∀ r, c r ∈ geomFamilyOn (G := G) R.history R.sched E₀ R.eN r
  edge_ok : ∀ e ∈ E₀, ¬ supported G R.roundData.F e →
    R.history.errOf (estOfOn E₀ R.sched c) e (R.sched e)
  hlost : (R.history.lostOn E₀ R.sched : ℝ) * Real.log 2 ≤
    (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 * Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) +
      2 * (E₀.card : ℝ) / (t : ℝ)

/-- **§3.5's per-call count with `m := |E₀|` and `n := |P|`.**  `m` is the instance's own edge count,
so `hmE` is `le_rfl`; the truth, the estimate, `hFsp` and the sample are derived, and the remaining
inputs are the evidence `EvOn` and the algorithm's agreement with its own queries. -/
theorem EvidenceOn.card_U_le_number_bound {R : DriverCall G P E₀ t} (Ev : EvidenceOn R)
    (ht : 2 ≤ t)
    (agree : ∀ (r : Fin t × Fin t) (x : {e : E // e ∈ E₀ ∧ R.sched e = r}),
      x ∈ sampleSetsOn E₀ ht R.sched (geomFamilyOn (G := G) R.history R.sched E₀ R.eN) r →
      Ev.c (R.sched x.1) ⟨x.1, x.2.1, rfl⟩ = R.history.pref x.1 r.1 r.2) :
    ((R.roundData.toCall.U).card : ℝ) ≤
      10 * (t : ℝ) ^ 2 * Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) +
        4 * (E₀.card : ℝ) / (t : ℝ) := by
  have hadm : ∀ (i j : Fin t) (v : V), ∃ e ∈ Bv G v (R.B i j), e ∉ R.roundData.F := by
    intro i j v
    obtain ⟨e, he, hne⟩ := R.hsupply i j v
    exact ⟨e, he, by rw [roundData_F]; exact hne⟩
  exact card_U_le_number_bound_of_tableOn R.roundData R.B R.quota R.hquota hadm R.sched R.eN
    Ev.c Ev.hc ht Ev.edge_ok Ev.hlost agree

end DriverCall

/-! ## The driver scheme's per-instance §3.5 count at `m := |E₀|`

This is `display_of_driver`'s `herrU` premise, produced instead of assumed. -/

namespace DriverCall

section Scheme

variable [Nonempty E] {tOf : Finset V → Finset E → ℕ}

/-- **§3.5's count at every instance, with `m := |E₀|`.**  Exactly `display_of_driver`'s `herrU`
hypothesis: per instance `(P', E₀')` the call's retained set is at most
`10t²√(|E₀'||P'|) + 4|E₀'|/t`, with `t := tOf P' E₀'` and `m` the instance's own edge count. -/
theorem driverScheme_herrU_on
    (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀))
    (EvOn : ∀ (P : Finset V) (E₀ : Finset E), DriverCall.EvidenceOn (DR P E₀))
    (htOf : ∀ (P : Finset V) (E₀ : Finset E), 2 ≤ tOf P E₀)
    (agree : ∀ (P : Finset V) (E₀ : Finset E) (r : Fin (tOf P E₀) × Fin (tOf P E₀))
      (x : {e : E // e ∈ E₀ ∧ (DR P E₀).sched e = r}),
      x ∈ sampleSetsOn E₀ (htOf P E₀) (DR P E₀).sched
        (geomFamilyOn (G := G) (DR P E₀).history (DR P E₀).sched E₀ (DR P E₀).eN) r →
      (EvOn P E₀).c ((DR P E₀).sched x.1) ⟨x.1, x.2.1, rfl⟩ =
        (DR P E₀).history.pref x.1 r.1 r.2) :
    ∀ (P' : Finset V) (E₀' : Finset E), (((driverRoundData DR P' E₀').toCall.U).card : ℝ) ≤
      10 * ((tOf P' E₀' : ℝ) ^ 2 * Real.sqrt ((E₀'.card : ℝ) * (P'.card : ℝ))) +
        4 * (E₀'.card : ℝ) / (tOf P' E₀' : ℝ) := by
  intro P' E₀'
  change (((DR P' E₀').roundData.toCall.U).card : ℝ) ≤
    10 * ((tOf P' E₀' : ℝ) ^ 2 * Real.sqrt ((E₀'.card : ℝ) * (P'.card : ℝ))) +
      4 * (E₀'.card : ℝ) / (tOf P' E₀' : ℝ)
  simpa [mul_assoc] using (EvOn P' E₀').card_U_le_number_bound (htOf P' E₀') (agree P' E₀')

end Scheme

end DriverCall

end DLMST