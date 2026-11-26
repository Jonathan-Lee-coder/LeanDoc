import DLMST.DriverEvidence
import DLMST.DriverWitness

/-!
# The good-schedule premise is automatic on small instances

`evidenceOn_of_good_schedule` (and `card_U_le_number_bound_of_truth`) take the schedule's average
bound as a hypothesis: the call's *own* `sched` must have `lostOn·log 2` below
`(2√2+4)t²√(|E₀||P|) + 2|E₀|/t`.  This file records the base case of the recursion, where that
hypothesis needs no averaging at all:

* `History.lostOn_le_card` — a lost count is a filtered subset of `E₀`, so it is `≤ |E₀|`;
* `lostOn_log_le_of_bound` — consequently, whenever the instance is small enough that
  `|E₀|·log 2 ≤ (2√2+4)t²√(|E₀||P|) + 2|E₀|/t`, **every** schedule is good;
* `callPar2`, `callPar2_hbig`, `callPar2_card_U` — the two-vertex five-parallel-edge driver, now with
  `t = 2`, is such an instance: the whole §3.5 machinery (instance-local Lemma 3.10/3.11 with the
  truth candidate, agreement, and the per-call count) runs with `edge_ok` the only premise left.

So B6 ("the call's schedule happens to be good") is not an issue in the base case; it is a genuinely
large-instance constraint.
-/

namespace DLMST

open Classical

namespace History

/-- A lost count only counts edges of `E₀`. -/
theorem lostOn_le_card {V E : Type*} {t : ℕ} (H : History V E t) (E₀ : Finset E) (ρ : Sched E t) :
    H.lostOn E₀ ρ ≤ E₀.card :=
  Finset.card_filter_le _ _

end History

/-- **Every schedule is good when the bound dominates `|E₀| log 2`.**  No averaging needed: the lost
count is at most `|E₀|` (`History.lostOn_le_card`). -/
theorem lostOn_log_le_of_bound {V E : Type*} {t : ℕ} {E₀ : Finset E} {B : ℝ}
    (hB : (E₀.card : ℝ) * Real.log 2 ≤ B) (H : History V E t) (ρ : Sched E t) :
    (H.lostOn E₀ ρ : ℝ) * Real.log 2 ≤ B := by
  have h1 : (H.lostOn E₀ ρ : ℝ) ≤ (E₀.card : ℝ) := by
    exact_mod_cast History.lostOn_le_card H E₀ ρ
  have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc (H.lostOn E₀ ρ : ℝ) * Real.log 2 ≤ (E₀.card : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_right h1 h2
    _ ≤ B := hB

namespace DriverWitness

/-- Every one-slot-forest of the parallel-edge witness has at most one edge, at any `t`. -/
theorem preF_par_card_le_t {t : ℕ} (slot : Fin 5 → Fin (t ^ 2)) :
    (preF (G := Gpar) (scanOfSlot (t := t) slot (Finset.univ : Finset (Fin 2))
      (Finset.univ : Finset (Fin 5))) (t ^ 2)).card ≤ 1 := by
  have h := card_le_card_sub_one_of_isForest_of_ends (G := Gpar)
    (isForest_preF (G := Gpar) (scanOfSlot (t := t) slot (Finset.univ : Finset (Fin 2))
      (Finset.univ : Finset (Fin 5))) (t ^ 2))
    (fun _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩)
    (by simp : 0 < (Finset.univ : Finset (Fin 2)).card)
  simpa using h

/-- The two-slot map used by the `t = 2` witness. -/
def slotPar2 : Fin 5 → Fin (2 ^ 2) := fun _ => 0

/-- The `t = 2` witness call: same geometry, four rounds' worth of slots all collapsed into slot `0`,
batch `univ`, one quota. -/
noncomputable def callPar2 : DriverCall Gpar (Finset.univ : Finset (Fin 2))
    (Finset.univ : Finset (Fin 5)) 2 where
  slot := slotPar2
  Pp := ∅
  hP' := Finset.empty_subset _
  hbudget := by simp
  hends := by intro e _; exact ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  B := fun _ _ => Finset.univ
  quota := 1
  hquota := le_refl 1
  hsupply := by
    intro _ _ v
    have hnot : ¬ (Finset.univ : Finset (Fin 5)) ⊆
        preF (G := Gpar) (scanOfSlot (t := 2) slotPar2 (Finset.univ : Finset (Fin 2))
          (Finset.univ : Finset (Fin 5))) (2 ^ 2) := by
      intro hsub
      have hc := Finset.card_le_card hsub
      have h5 : (Finset.univ : Finset (Fin 5)).card = 5 := by simp
      have h2 := preF_par_card_le_t (t := 2) slotPar2
      omega
    obtain ⟨e, _, hepre⟩ := Finset.not_subset.mp hnot
    exact ⟨e, by rw [mem_Bv]; exact ⟨Finset.mem_univ _, incident_all v e⟩, hepre⟩

/-- **The average bound is `≥ |E₀| log 2` on the witness**: `5·log 2 ≤ 4·(2√2+4)·√10 + 5`. -/
theorem callPar2_hbig :
    ((Finset.univ : Finset (Fin 5)).card : ℝ) * Real.log 2 ≤
      (2 * Real.sqrt 2 + 4) * ((2 : ℕ) : ℝ) ^ 2 *
          Real.sqrt (((Finset.univ : Finset (Fin 5)).card : ℝ) *
            ((Finset.univ : Finset (Fin 2)).card : ℝ)) +
        2 * ((Finset.univ : Finset (Fin 5)).card : ℝ) / (2 : ℝ) := by
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have h2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h10 : (0 : ℝ) ≤ Real.sqrt 10 := Real.sqrt_nonneg 10
  have h210 : (0 : ℝ) ≤ Real.sqrt 2 * Real.sqrt 10 := mul_nonneg h2 h10
  have hsqrt : Real.sqrt (((Finset.univ : Finset (Fin 5)).card : ℝ) *
      ((Finset.univ : Finset (Fin 2)).card : ℝ)) = Real.sqrt 10 := by
    norm_num
  rw [hsqrt]
  simp only [Finset.card_univ, Fintype.card_fin]
  norm_num
  nlinarith [hlog, h210, h10]

/-- **The witness's own schedule is good**, unconditionally: the instance is small enough for
`lostOn_log_le_of_bound`. -/
theorem callPar2_good (H : History (Fin 2) (Fin 5) 2) (ρ : Sched (Fin 5) 2) :
    (H.lostOn (Finset.univ : Finset (Fin 5)) ρ : ℝ) * Real.log 2 ≤
      (2 * Real.sqrt 2 + 4) * ((2 : ℕ) : ℝ) ^ 2 *
          Real.sqrt (((Finset.univ : Finset (Fin 5)).card : ℝ) *
            ((Finset.univ : Finset (Fin 2)).card : ℝ)) +
        2 * ((Finset.univ : Finset (Fin 5)).card : ℝ) / (2 : ℝ) :=
  lostOn_log_le_of_bound callPar2_hbig H ρ

/-- **§3.5 on the witness, with `edge_ok` the only premise**: the evidence of the `t = 2` call,
with `hc`, `agree` and `hlost` all discharged from the call's own data. -/
noncomputable def callPar2_evidence
    (hedge : ∀ e ∈ (Finset.univ : Finset (Fin 5)),
      ¬ supported Gpar callPar2.roundData.F e →
      callPar2.history.errOf (estOfOn (Finset.univ : Finset (Fin 5)) callPar2.sched
        (DriverCall.truthCand callPar2)) e (callPar2.sched e)) :
    DriverCall.EvidenceOn callPar2 :=
  DriverCall.evidenceOn_of_good_schedule callPar2 (0 : Fin 5)
    (fun _ _ => Finset.subset_univ _) (by simp) (fun H _ => callPar2_good H callPar2.sched) hedge

/-- **The witness's per-call count**: `|U| ≤ 10·4·√10 + 10`, with `edge_ok` the only premise. -/
theorem callPar2_card_U
    (hedge : ∀ e ∈ (Finset.univ : Finset (Fin 5)),
      ¬ supported Gpar callPar2.roundData.F e →
      callPar2.history.errOf (estOfOn (Finset.univ : Finset (Fin 5)) callPar2.sched
        (DriverCall.truthCand callPar2)) e (callPar2.sched e)) :
    ((callPar2.roundData.toCall.U).card : ℝ) ≤
      10 * ((2 : ℕ) : ℝ) ^ 2 *
          Real.sqrt (((Finset.univ : Finset (Fin 5)).card : ℝ) *
            ((Finset.univ : Finset (Fin 2)).card : ℝ)) +
        4 * ((Finset.univ : Finset (Fin 5)).card : ℝ) / (2 : ℝ) :=
  DriverCall.card_U_le_number_bound_of_truth callPar2 (0 : Fin 5)
    (fun _ _ => Finset.subset_univ _) (by simp) (by norm_num : 2 ≤ (2 : ℕ))
    (fun H _ => callPar2_good H callPar2.sched) hedge

end DriverWitness

end DLMST