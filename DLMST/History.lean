import DLMST.Rounds

/-!
# §3.4, Definition 3.8 and Lemma 3.11: histories and a schedule good for all of them

`Rounds.lean` says what a round *does* to one edge (`actOf`, `prefFind`, `MonoRow`, Claims 3.5–3.6 and
Lemma 3.7).  §3.4 turns that per-edge view into a global object: the **history** of a whole call.

* **Definition 3.8** is `History`: per round `(b, i)`, the spoke vector `σ`, the forest `F`, and the
  true preferred-action vector `a`, the last one written per edge as `pref : E → Fin t → Fin t → Pref`
  because each edge only ever asks about its own entry.  `History.Consistent` is the sentence that makes
  `pref` a *history* rather than arbitrary data — `pref e b i = actOf G (σ b i) (F b i) e` — and
  `History.badFor` is Definition 3.4 read inside a history.  The paper's "the history completely
  determines which rounds are good or bad for each edge" is then `badFor_def` plus
  `badFor_card_le`: the same `≤ 2t` count of `Schedule.lean`, but now stated per edge of a history.
  `History.monoRow_of_grow` pins the link back to `Rounds.lean`: a consistent history whose spokes are
  frozen in each block and whose forests grow has `PPPPFFF` rows.

* **Lemma 3.11** (`lemma311`): there is one schedule `ρ : E → [t²]` under which, for *every* history in
  a finite family `Hs`, at most `log |Hs| + 2m/(t log 2)` edges are scheduled in a bad round.  The
  paper proves this by the probabilistic method: a uniformly random schedule, `E[2^{X_H}] ≤
  (1 + 2/t)^m`, and averaging over the `|Hs|` histories.  The formal proof replaces "random" by the
  finite average over all `(t²)^m` schedules, which is the same statement: the two ingredients are the
  per-edge generating-function bound `History.genEdge_le` (`∑_r 2^{[r bad]} ≤ t² + 2t`, i.e. the `≤ 2t`
  count) and the product-over-functions identity `History.weighted_sum_le`
  (`∑_ρ 2^{X_H(ρ)} = ∏_e ∑_r 2^{[r bad for e]} ≤ (t² + 2t)^m`).  `exists_le_average` is the
  "average is attained" step; no measure theory is needed, and the resulting bound has no slack
  beyond the paper's own `(1 + 2/t)^m ≤ e^{2m/t}` (`Real.log_le_sub_one_of_pos`).

Not formalised here: **Lemma 3.10**, the count `log |H| = O(t²√(mn))` of *how many* histories there
are.  That is a separate combinatorial statement, and its middle step is Lemma 3.9 (Fredman's
`C(n+m-1, m)` bound, obligation 4).  `lemma311` takes the family `Hs` as data precisely so that the
two halves can be checked independently; §3.3's Lemma 3.7 then consumes the conclusion with
`Hs := H` the history set.  Also not here: Claim 3.12 (the sampling of preferred actions), which is
the next file.
-/

namespace DLMST

set_option linter.unusedSectionVars false

open Classical

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] {G : WGraph V E}
  [LinearOrder E]

/-! ## Definition 3.8: the history of a call -/

/-- **Definition 3.8 (History).**  Rounds are indexed by `Fin t × Fin t` (block, round-in-block), and
the history records, at the *start* of each round: the spoke vector `spoke`, the forest `forest`, and
the true preferred action of every edge, `pref`.  Indexing `spoke` and `forest` by the pair is
faithful to the paper's `(σ_i, F_i, a_i)_{i ∈ [t²]}`; "spokes are frozen inside a block" is then a
*property* (`History.monoRow_of_grow` below) instead of a built-in restriction. -/
structure History (V E : Type*) (t : ℕ) where
  spoke : Fin t → Fin t → V → E
  forest : Fin t → Fin t → Finset E
  pref : E → Fin t → Fin t → Pref

variable {t : ℕ}

namespace History

/-- **A consistent history**: its action vector really is the preferred action of the round state,
i.e. §3.1's rule applied to the recorded spokes and forest (`Rounds.actOf`).  This is the only
condition tying Definition 3.8's three components together. -/
def Consistent (H : History V E t) : Prop :=
  ∀ e (b i : Fin t), H.pref e b i = actOf G (H.spoke b i) (H.forest b i) e

/-- **Definition 3.4 inside a history**: `(b, i)` is bad for `e` according to `e`'s own action row. -/
def badFor (H : History V E t) (e : E) (p : Fin t × Fin t) : Prop := bad (H.pref e) p

/-- "The history completely determines which rounds are good or bad for each edge" — the definition of
`badFor` is the only input. -/
theorem badFor_def (H : History V E t) (e : E) (p : Fin t × Fin t) :
    H.badFor e p ↔ bad (H.pref e) p := Iff.rfl

/-- The other side of the same sentence: a round is *good* for `e` when it is not bad. -/
def goodFor (H : History V E t) (e : E) (p : Fin t × Fin t) : Prop := ¬ H.badFor e p

theorem goodFor_iff (H : History V E t) (e : E) (p : Fin t × Fin t) :
    H.goodFor e p ↔ ¬ bad (H.pref e) p := Iff.rfl

/-- **Definition 3.4's count, per edge of a history**: at most `2t` bad rounds, from
`Schedule.bad_card_le`.  This is the `Pr[Y_e = 1] ≤ 2t/t²` input to Lemma 3.11. -/
theorem badFor_card_le (H : History V E t) (e : E) :
    ((Finset.univ : Finset (Fin t × Fin t)).filter (H.badFor e)).card ≤ 2 * t :=
  bad_card_le (H.pref e) _ fun p => by
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ p, h⟩⟩

/-- **§3.3's block monotonicity, for a history.**  If a consistent history freezes the spokes inside
each block and only grows the forest, then for every edge the action row of every block is `PPPPFFF`
— `Rounds.MonoRow`, derived here from Definition 3.8 rather than assumed. -/
theorem monoRow_of_grow (H : History V E t) (hcons : H.Consistent (G := G))
    (hfreeze : ∀ b : Fin t, ∃ σ : V → E, ∀ i, H.spoke b i = σ)
    (hgrow : ∀ (b : Fin t) (i j : Fin t), i ≤ j → H.forest b i ⊆ H.forest b j)
    (b : Fin t) (e : E) :
    MonoRow (fun _ i => H.pref e b i) := by
  obtain ⟨σ, hσ⟩ := hfreeze b
  have hpref : ∀ i, H.pref e b i = actOf G σ (H.forest b i) e := by
    intro i
    rw [hcons e b i, hσ i]
  intro _ i j hij hfind
  have hfind' : actOf G σ (H.forest b i) e = Pref.find := by
    rw [← hpref i]
    exact hfind
  have himp := connImproves_of_grow (G := G) (F := fun i => H.forest b i) (hgrow b)
    (θ := pE G σ e) (u := G.src e) (v := G.dst e)
  -- the first three clauses do not mention the forest, so they hold at `j` unchanged; the fourth
  -- is where the forest has to grow
  have hj : actOf G σ (H.forest b j) e = Pref.find := by
    apply actOf_find
    obtain h1 | h2 | h3 | h4 := prefFind_of_actOf_find hfind'
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (himp i j hij h4)))
  show H.pref e b j = Pref.find
  rw [hpref j]
  exact hj

end History

/-! ## Lemma 3.11: one schedule good for every history -/

/-- A deterministic schedule: each edge is assigned one round. -/
abbrev Sched (E : Type*) (t : ℕ) := E → Fin t × Fin t

namespace History

/-- **`X_H(ρ)`** (Lemma 3.11): the number of edges whose assigned round is bad for them under `H`. -/
noncomputable def lost (H : History V E t) (ρ : Sched E t) : ℕ :=
  ((Finset.univ : Finset E).filter fun e => H.badFor e (ρ e)).card

theorem lost_def (H : History V E t) (ρ : Sched E t) :
    H.lost ρ = ((Finset.univ : Finset E).filter fun e => H.badFor e (ρ e)).card := rfl

/-- **`|U(F)| ≤ lost`.**  If every edge that `F` leaves unsupported has its assigned round bad for it —
Lemma 3.7's conclusion compiled against one fixed schedule — then the retained set of an instance is no
larger than the history's lost count.  This is where §3.3's `U(F)` meets §3.5's `lost`. -/
theorem card_unsupp_le_lost {F : Finset E} (H : History V E t) (ρ : Sched E t)
    (h : ∀ e : E, ¬ supported G F e → H.badFor e (ρ e)) :
    (unsupp G F).card ≤ H.lost ρ := by
  rw [lost_def]
  exact Finset.card_le_card (fun e he =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, h e (mem_unsupp.mp he)⟩)

/-- **The per-edge factor** of Lemma 3.11's generating function.  Over all `t²` rounds, the weighted
number `∑_r 2^{[r bad for e]}` is `t² + (#bad rounds) ≤ t² + 2t`: this is where Definition 3.4's
count — the paper's `Pr[Y_e = 1] ≤ 2/t` — is consumed. -/
theorem genEdge_le (H : History V E t) (e : E) :
    (∑ r : Fin t × Fin t, (2 : ℕ) ^ (if H.badFor e r then 1 else 0)) ≤ t * t + 2 * t := by
  classical
  have hstep : ∀ r : Fin t × Fin t,
      (2 : ℕ) ^ (if H.badFor e r then 1 else 0) = 1 + (if H.badFor e r then 1 else 0) := by
    intro r
    by_cases h : H.badFor e r <;> simp [h]
  calc (∑ r : Fin t × Fin t, (2 : ℕ) ^ (if H.badFor e r then 1 else 0))
      = ∑ r : Fin t × Fin t, (1 + (if H.badFor e r then 1 else 0)) :=
        Finset.sum_congr rfl fun r _ => hstep r
    _ = (Finset.univ : Finset (Fin t × Fin t)).card +
          ((Finset.univ : Finset (Fin t × Fin t)).filter (H.badFor e)).card := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_boole]
        simp
    _ ≤ t * t + 2 * t := by
        have hc : (Finset.univ : Finset (Fin t × Fin t)).card = t * t := by simp
        have hb := H.badFor_card_le e
        omega

/-- **Lemma 3.11's engine.**  For a fixed history, the generating function over *all* schedules
factorises: `∑_ρ 2^{X_H(ρ)} = ∏_e ∑_r 2^{[r bad for e]} ≤ (t² + 2t)^m`.  The first equality is the
independence of the paper's random assignments, made exact by `Finset.sum_prod_piFinset`. -/
theorem weighted_sum_le (H : History V E t) :
    (∑ ρ : Sched E t, (2 : ℕ) ^ H.lost ρ) ≤ (t * t + 2 * t) ^ Fintype.card E := by
  classical
  have hfactor : ∀ ρ : Sched E t,
      (2 : ℕ) ^ H.lost ρ = ∏ e : E, (2 : ℕ) ^ (if H.badFor e (ρ e) then 1 else 0) := by
    intro ρ
    have h1 : H.lost ρ = ∑ e : E, (if H.badFor e (ρ e) then 1 else 0) := by
      unfold History.lost
      simp [Finset.sum_boole]
    rw [h1, Finset.prod_pow_eq_pow_sum]
  have hpi : (∑ ρ : Sched E t, ∏ e : E, (2 : ℕ) ^ (if H.badFor e (ρ e) then 1 else 0)) =
      ∏ e : E, ∑ r : Fin t × Fin t, (2 : ℕ) ^ (if H.badFor e r then 1 else 0) := by
    have h := Finset.sum_prod_piFinset (s := (Finset.univ : Finset (Fin t × Fin t)))
      (g := fun (e : E) (r : Fin t × Fin t) => (2 : ℕ) ^ (if H.badFor e r then 1 else 0))
    simpa [Sched, Fintype.piFinset_univ] using h
  calc (∑ ρ : Sched E t, (2 : ℕ) ^ H.lost ρ)
      = ∑ ρ : Sched E t, ∏ e : E, (2 : ℕ) ^ (if H.badFor e (ρ e) then 1 else 0) :=
        Finset.sum_congr rfl fun ρ _ => hfactor ρ
    _ = ∏ e : E, ∑ r : Fin t × Fin t, (2 : ℕ) ^ (if H.badFor e r then 1 else 0) := hpi
    _ ≤ ∏ _e : E, (t * t + 2 * t) :=
        Finset.prod_le_prod fun e _ => H.genEdge_le e
    _ = (t * t + 2 * t) ^ Fintype.card E := by simp

end History

/-- **The average is attained.**  For a nonempty finite type, some point is no larger than the mean —
the "by averaging" step of Lemma 3.11, with the mean written as `(∑ f)/|ι|`. -/
theorem exists_le_average {ι : Type*} [Fintype ι] (hne : Nonempty ι) (f : ι → ℝ) :
    ∃ x, f x ≤ (∑ x, f x) / (Fintype.card ι : ℝ) := by
  classical
  by_contra h
  simp only [not_exists, not_le] at h
  have hlt : (∑ _x : ι, (∑ x, f x) / (Fintype.card ι : ℝ)) < ∑ x : ι, f x :=
    Finset.sum_lt_sum (fun x _ => le_of_lt (h x))
      ⟨hne.some, Finset.mem_univ _, h hne.some⟩
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hlt
  have hpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos_iff.mpr hne
  have hcancel : (Fintype.card ι : ℝ) * ((∑ x, f x) / (Fintype.card ι : ℝ)) = ∑ x, f x :=
    mul_div_cancel₀ _ hpos.ne'
  linarith

/-- **Lemma 3.11, machine-checked.**  There is a single deterministic schedule `ρ` that bounds, for
*every* history in a finite family `Hs` simultaneously, the number of edges scheduled in a bad round:
`X_H(ρ) · log 2 ≤ log |Hs| + 2m/t`, which is the paper's `X_H(ρ*) ≤ (log |H| + 2m/t)/log 2`.

The paper's random schedule is here the uniform average over all `(t²)^m` schedules
(`exists_le_average`); the right-hand side `(1 + 2/t)^m` then comes from `m log(1 + 2/t) ≤ 2m/t`
(`Real.log_le_sub_one_of_pos`) exactly as in the paper, so no constant is lost. -/
theorem lemma311 (ht : 2 ≤ t) (Hs : Finset (History V E t)) :
    ∃ ρ : Sched E t, ∀ H ∈ Hs,
      (H.lost ρ : ℝ) * Real.log 2 ≤
        Real.log (Hs.card : ℝ) + 2 * (Fintype.card E : ℝ) / (t : ℝ) := by
  classical
  by_cases hne : Hs.Nonempty
  · obtain ⟨ρ, hρ⟩ := exists_le_average
      ⟨fun _ => (⟨0, by omega⟩, ⟨0, by omega⟩)⟩
      (fun ρ : Sched E t => ∑ H ∈ Hs, (2 : ℝ) ^ H.lost ρ)
    refine ⟨ρ, fun H hH => ?_⟩
    have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
    have hHs : (0 : ℝ) < (Hs.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hne
    have hm : (0 : ℝ) ≤ (Fintype.card E : ℝ) := by positivity
    -- the number of schedules is `(t²)^m`
    have hN : (Fintype.card (Sched E t) : ℝ) = ((t : ℝ) * t) ^ Fintype.card E := by
      simp [Sched, Fintype.card_prod]
    -- bound the averaged generating function
    have hsum : (∑ ρ : Sched E t, ∑ H ∈ Hs, (2 : ℝ) ^ H.lost ρ) ≤
        (Hs.card : ℝ) * (((t * t + 2 * t : ℕ) : ℝ)) ^ Fintype.card E := by
      calc (∑ ρ : Sched E t, ∑ H ∈ Hs, (2 : ℝ) ^ H.lost ρ)
          = ∑ H ∈ Hs, ∑ ρ : Sched E t, (2 : ℝ) ^ H.lost ρ := Finset.sum_comm
        _ ≤ ∑ _H ∈ Hs, (((t * t + 2 * t : ℕ) : ℝ)) ^ Fintype.card E :=
            Finset.sum_le_sum fun H _ => by exact_mod_cast History.weighted_sum_le H
        _ = (Hs.card : ℝ) * (((t * t + 2 * t : ℕ) : ℝ)) ^ Fintype.card E := by
            rw [Finset.sum_const, nsmul_eq_mul]
    -- divide by the number of schedules: `((t² + 2t)/t²)^m = (1 + 2/t)^m`
    have hratio : (((t * t + 2 * t : ℕ) : ℝ)) ^ Fintype.card E /
        (Fintype.card (Sched E t) : ℝ) = (1 + 2 / (t : ℝ)) ^ Fintype.card E := by
      rw [hN, ← div_pow]
      congr 1
      have h1 : (((t * t + 2 * t : ℕ) : ℝ)) = (t : ℝ) * ((t : ℝ) + 2) := by
        push_cast; ring
      rw [h1]
      field_simp
    -- the pointwise bound from the average
    have havg : (2 : ℝ) ^ H.lost ρ ≤
        (Hs.card : ℝ) * (1 + 2 / (t : ℝ)) ^ Fintype.card E := by
      refine le_trans ?_ (le_trans hρ ?_)
      · exact Finset.single_le_sum
          (f := fun H' : History V E t => (2 : ℝ) ^ H'.lost ρ)
          (fun _ _ => by positivity) hH
      · calc (∑ ρ : Sched E t, ∑ H ∈ Hs, (2 : ℝ) ^ H.lost ρ) / (Fintype.card (Sched E t) : ℝ)
            ≤ ((Hs.card : ℝ) * (((t * t + 2 * t : ℕ) : ℝ)) ^ Fintype.card E) /
                (Fintype.card (Sched E t) : ℝ) :=
              div_le_div_of_nonneg_right hsum (by positivity)
          _ = (Hs.card : ℝ) * (1 + 2 / (t : ℝ)) ^ Fintype.card E := by
              rw [mul_div_assoc, hratio]
    -- logarithms
    have hlog := Real.log_le_log (by positivity) havg
    rw [Real.log_pow, Real.log_mul hHs.ne' (by positivity), Real.log_pow] at hlog
    have hlog2 : Real.log (1 + 2 / (t : ℝ)) ≤ 2 / (t : ℝ) := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 2 / (t : ℝ))
      linarith
    have hmul := mul_le_mul_of_nonneg_left hlog2 hm
    have hcast : (Fintype.card E : ℝ) * (2 / (t : ℝ)) =
        2 * (Fintype.card E : ℝ) / (t : ℝ) := by ring
    linarith
  · refine ⟨fun _ => (⟨0, by omega⟩, ⟨0, by omega⟩), ?_⟩
    intro H hH
    exact absurd ⟨H, hH⟩ hne

end DLMST