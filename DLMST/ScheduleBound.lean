import DLMST.HistoryCount

/-!
# §3.4's schedule: `O(m/t + t²√(mn))` edges in bad rounds

`History.lemma311` produces one deterministic schedule `ρ` that is good for *every* history in a
family `Hs`, with the bad-round count bounded by `(log |Hs| + 2m/t)/log 2`; `HistoryCount`'s
`log_card_histories_le` bounds `log |Hs|` by `t²(2√(2mn) + 4√(m(n-1)))` for legal histories.  The
paper's §3.4 sentence — "we can deterministically decide on a schedule which will not schedule more
than `O(m/t + t²√(mn))` many edges in bad rounds" — is the composition of the two, which is what
`exists_schedule_lost_le` (the sharp constants) and `exists_schedule_lost_paper` (the shape
`C·t²·√(mn) + 2m/t`) record.

No probability is used anywhere: `lemma311` already replaced the random schedule by an exact average
over all `(t²)^m` schedules.
-/

namespace DLMST

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] {G : WGraph V E}
  [LinearOrder E] {t : ℕ}

/-- **Composing Lemma 3.11 with Lemma 3.10.**  For a nonempty family of legal histories there is one
schedule under which every history has at most
`(t²(2√(2mn) + 4√(m(n−1))) + 2m/t)/log 2` edges scheduled in a bad round. -/
theorem exists_schedule_lost_le {e₀ : E} (ht : 2 ≤ t) (Hs : Finset (History V E t))
    (hleg : ∀ H ∈ Hs, Legal (G := G) e₀ (Fintype.card V) H) (hpos : 0 < Hs.card) :
    ∃ ρ : Sched E t, ∀ H ∈ Hs,
      (H.lost ρ : ℝ) * Real.log 2 ≤
        (t : ℝ) ^ 2 *
            (2 * Real.sqrt (2 * (Fintype.card E : ℝ) * (Fintype.card V : ℝ)) +
              4 * Real.sqrt ((Fintype.card E : ℝ) * (((Fintype.card V - 1 : ℕ)) : ℝ))) +
          2 * (Fintype.card E : ℝ) / (t : ℝ) := by
  obtain ⟨ρ, hρ⟩ := lemma311 ht Hs
  refine ⟨ρ, fun H hH => ?_⟩
  have hlog := log_card_histories_le e₀ Hs hleg hpos
  linarith [hρ H hH]

/-- **The paper's shape.**  The same schedule, with `√(m(n−1)) ≤ √(mn)` and
`√(2mn) = √2·√(mn)` collapsed into one factor: `(2√2 + 4)·t²·√(mn) + 2m/t`. -/
theorem exists_schedule_lost_paper {e₀ : E} (ht : 2 ≤ t) (Hs : Finset (History V E t))
    (hleg : ∀ H ∈ Hs, Legal (G := G) e₀ (Fintype.card V) H) (hpos : 0 < Hs.card) :
    ∃ ρ : Sched E t, ∀ H ∈ Hs,
      (H.lost ρ : ℝ) * Real.log 2 ≤
        (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 *
            Real.sqrt ((Fintype.card E : ℝ) * (Fintype.card V : ℝ)) +
          2 * (Fintype.card E : ℝ) / (t : ℝ) := by
  obtain ⟨ρ, hρ⟩ := exists_schedule_lost_le ht Hs hleg hpos
  refine ⟨ρ, fun H hH => ?_⟩
  have h1 := hρ H hH
  have hm : (0 : ℝ) ≤ (Fintype.card E : ℝ) := Nat.cast_nonneg _
  have hn1 : (((Fintype.card V - 1 : ℕ)) : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast Nat.sub_le (Fintype.card V) 1
  have hsq : Real.sqrt ((Fintype.card E : ℝ) * (((Fintype.card V - 1 : ℕ)) : ℝ)) ≤
      Real.sqrt ((Fintype.card E : ℝ) * (Fintype.card V : ℝ)) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hn1 hm)
  have hsq2 : Real.sqrt (2 * (Fintype.card E : ℝ) * (Fintype.card V : ℝ)) =
      Real.sqrt 2 * Real.sqrt ((Fintype.card E : ℝ) * (Fintype.card V : ℝ)) := by
    rw [show 2 * (Fintype.card E : ℝ) * (Fintype.card V : ℝ) =
        2 * ((Fintype.card E : ℝ) * (Fintype.card V : ℝ)) by ring]
    exact Real.sqrt_mul (by norm_num) _
  have hkey : 2 * Real.sqrt (2 * (Fintype.card E : ℝ) * (Fintype.card V : ℝ)) +
        4 * Real.sqrt ((Fintype.card E : ℝ) * (((Fintype.card V - 1 : ℕ)) : ℝ)) ≤
      (2 * Real.sqrt 2 + 4) * Real.sqrt ((Fintype.card E : ℝ) * (Fintype.card V : ℝ)) := by
    rw [hsq2]
    nlinarith [hsq]
  have ht2 : (0 : ℝ) ≤ (t : ℝ) ^ 2 := sq_nonneg _
  have hscale : (t : ℝ) ^ 2 *
        (2 * Real.sqrt (2 * (Fintype.card E : ℝ) * (Fintype.card V : ℝ)) +
          4 * Real.sqrt ((Fintype.card E : ℝ) * (((Fintype.card V - 1 : ℕ)) : ℝ))) ≤
      (t : ℝ) ^ 2 *
        ((2 * Real.sqrt 2 + 4) * Real.sqrt ((Fintype.card E : ℝ) * (Fintype.card V : ℝ))) :=
    mul_le_mul_of_nonneg_left hkey ht2
  have hflip : (t : ℝ) ^ 2 *
        ((2 * Real.sqrt 2 + 4) * Real.sqrt ((Fintype.card E : ℝ) * (Fintype.card V : ℝ))) =
      (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 *
        Real.sqrt ((Fintype.card E : ℝ) * (Fintype.card V : ℝ)) := by ring
  linarith [h1, hscale, hflip.le, hflip.ge]

end DLMST