import DLMST.SmallInstance

/-!
# Lemma 3.7's conclusion, in `bad` terms

With the truth candidate, the estimate at `e`'s own round *is* the history's preference, so
`errOf`'s second disjunct is false and per-edge error collapses to "`e`'s own round is bad for `e`"
(`errOf_truth_iff`).  That is exactly Lemma 3.7's statement — an unsupported instance edge has a bad
round at its own slot — with no estimate left in it.

The rest of the file restates §3.5's per-call count and the evidence constructor with this
hypothesis, so the single remaining premise of the driver is literally

`¬ supported G R.roundData.F e → R.history.badFor e (R.sched e)` for `e ∈ E₀`.
-/

namespace DLMST

open Classical

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

namespace DriverCall

variable {P : Finset V} {E₀ : Finset E} {t : ℕ} [Nonempty E]

/-- **`errOf` at the truth estimate is `badFor`**: at `e`'s own round, the truth candidate predicts
`e`'s own preference, so only the bad-round disjunct survives. -/
theorem errOf_truth_iff (R : DriverCall G P E₀ t) {e : E} (he : e ∈ E₀) :
    R.history.errOf (estOfOn E₀ R.sched (truthCand R)) e (R.sched e) ↔
      R.history.badFor e (R.sched e) := by
  unfold History.errOf
  rw [estOfOn_of_mem E₀ R.sched (truthCand R) he]
  simp [truthCand]

/-- **Evidence with the truth candidate and Lemma 3.7 in `bad` form.**  Same as
`evidenceOn_of_good_schedule`, with `edge_ok` stated as "an unsupported instance edge is bad at its
own round". -/
noncomputable def evidenceOn_of_good_schedule_badFor (R : DriverCall G P E₀ t) (e₀ : E)
    (hB : ∀ i j, R.B i j ⊆ E₀) (hP0 : 0 < P.card)
    (hgood : ∀ H : History V E t, LegalOn (G := G) P E₀ e₀ H →
      (H.lostOn E₀ R.sched : ℝ) * Real.log 2 ≤
        (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 *
            Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) + 2 * (E₀.card : ℝ) / (t : ℝ))
    (hbad : ∀ e ∈ E₀, ¬ supported G R.roundData.F e → R.history.badFor e (R.sched e)) :
    EvidenceOn R :=
  evidenceOn_of_good_schedule R e₀ hB hP0 hgood
    (fun e he hnot => (errOf_truth_iff R he).mpr (hbad e he hnot))

/-- **§3.5's per-call count from Lemma 3.7 in `bad` terms.** -/
theorem card_U_le_number_bound_of_badFor (R : DriverCall G P E₀ t) (e₀ : E)
    (hB : ∀ i j, R.B i j ⊆ E₀) (hP0 : 0 < P.card) (ht : 2 ≤ t)
    (hgood : ∀ H : History V E t, LegalOn (G := G) P E₀ e₀ H →
      (H.lostOn E₀ R.sched : ℝ) * Real.log 2 ≤
        (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 *
            Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) + 2 * (E₀.card : ℝ) / (t : ℝ))
    (hbad : ∀ e ∈ E₀, ¬ supported G R.roundData.F e → R.history.badFor e (R.sched e)) :
    ((R.roundData.toCall.U).card : ℝ) ≤
      10 * (t : ℝ) ^ 2 * Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) +
        4 * (E₀.card : ℝ) / (t : ℝ) :=
  EvidenceOn.card_U_le_number_bound (R := R)
    (evidenceOn_of_good_schedule_badFor R e₀ hB hP0 hgood hbad) ht (agree_truthOn R ht)

end DriverCall

end DLMST