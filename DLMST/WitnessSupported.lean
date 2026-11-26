import DLMST.Lemma37Bad

/-!
# The parallel-edge witness: every edge is supported

On the `DriverCall` witness of `DriverWitness` (two vertices, five parallel edges, weights `0…4`)
the scan of round `0` is the whole instance in weight order, and Kruskal keeps its first (lightest)
element.  Since the weights are the indices, that element is the lightest edge overall, hence the
threshold filter `F.filter (· ≤ w e)` always contains a `0 → 1` edge — every instance edge is
`supported` by the returned forest.

Consequently `U = unsupp G F ∩ E₀ = ∅`, the per-edge premise of Lemma 3.7 is vacuous, and the whole
§3.5 chain (`EvidenceOn`, `|U|` bound) holds on this call with no premise left.  Note the honest
reading: on this witness the numerical bound carries no content because `U` is empty; what the
statement certifies is that the `EvidenceOn` interface — including `edge_ok` and the loss bound —
is inhabited, not merely consistent.
-/

open Classical

namespace DLMST

namespace DriverWitness

/-- Round `0` of the witness's schedule scans the whole instance, weight-sorted. -/
theorem scan_zero_eq :
    scanOfSlot (t := 2) slotPar2 (Finset.univ : Finset (Fin 2)) (Finset.univ : Finset (Fin 5)) 0 =
      (Finset.univ : Finset (Fin 5)).sort (· ≤ ·) := by
  unfold scanOfSlot slotPar2
  simp

theorem sort_univ_ne_nil : (Finset.univ : Finset (Fin 5)).sort (· ≤ ·) ≠ [] := by
  intro h
  have hlen := Finset.length_sort (s := (Finset.univ : Finset (Fin 5))) (r := (· ≤ ·))
  rw [h] at hlen
  simp at hlen

/-- The witness's weight is monotone in the `Fin` order. -/
theorem weight_le_of_fin_le {a b : Fin 5} (h : a ≤ b) : Gpar.weight a ≤ Gpar.weight b := by
  have hv : (a : ℕ) ≤ (b : ℕ) := h
  show ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ)
  exact_mod_cast hv

theorem eq_of_conn_empty {u v : Fin 2} (h : Conn Gpar ∅ u v) : u = v := by
  induction h with
  | refl => rfl
  | step e he => exact absurd he (by simp)
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem not_conn_empty : ¬ Conn Gpar ∅ (0 : Fin 2) (1 : Fin 2) := by
  intro hc
  exact absurd (eq_of_conn_empty hc) (by decide)

/-- **Kruskal keeps the lightest scanned edge.**  The scan list is the instance sorted by weight, so
its head is an edge of the returned prefix forest whose weight is at most that of every edge. -/
theorem head_kept :
    ∃ a ∈ preF (G := Gpar) (scanOfSlot (t := 2) slotPar2 (Finset.univ : Finset (Fin 2))
        (Finset.univ : Finset (Fin 5))) (2 ^ 2),
      ∀ e : Fin 5, Gpar.weight a ≤ Gpar.weight e := by
  obtain ⟨a, bs, hcons⟩ := List.exists_cons_of_ne_nil sort_univ_ne_nil
  have hpair : List.Pairwise (· ≤ ·) (a :: bs) := by
    rw [← hcons]
    exact Finset.pairwise_sort (s := (Finset.univ : Finset (Fin 5))) (r := (· ≤ ·))
  have hlight : ∀ e : Fin 5, Gpar.weight a ≤ Gpar.weight e := by
    intro e
    by_cases he : e = a
    · subst he
      exact le_refl _
    · have hb : e ∈ bs := by
        have hm : e ∈ (Finset.univ : Finset (Fin 5)).sort (· ≤ ·) :=
          (Finset.mem_sort (s := (Finset.univ : Finset (Fin 5))) (r := (· ≤ ·))).mpr
            (Finset.mem_univ e)
        rw [hcons, List.mem_cons] at hm
        tauto
      exact weight_le_of_fin_le ((List.pairwise_cons.mp hpair).1 e hb)
  refine ⟨a, ?_, hlight⟩
  have hstep : preF (G := Gpar) (scanOfSlot (t := 2) slotPar2 (Finset.univ : Finset (Fin 2))
        (Finset.univ : Finset (Fin 5))) 1
      = K Gpar (a :: bs) ∅ := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, preF_succ, preF_zero, scan_zero_eq, hcons]
  have hno : ¬ Conn Gpar ∅ (Gpar.src a) (Gpar.dst a) := by
    simpa [Gpar, WGraph.src, WGraph.dst] using not_conn_empty
  have h1 : a ∈ preF (G := Gpar) (scanOfSlot (t := 2) slotPar2 (Finset.univ : Finset (Fin 2))
        (Finset.univ : Finset (Fin 5))) 1 := by
    rw [hstep, K_cons, step_accept Gpar ∅ a hno]
    exact K_mono (G := Gpar) bs (insert a ∅) (Finset.mem_insert_self a ∅)
  exact preF_mono (G := Gpar) (scanOfSlot (t := 2) slotPar2 (Finset.univ : Finset (Fin 2))
    (Finset.univ : Finset (Fin 5))) (by decide : 1 ≤ 2 ^ 2) h1

/-- **Every instance edge is supported** by the witness call's returned forest. -/
theorem all_supported :
    ∀ e ∈ (Finset.univ : Finset (Fin 5)), supported Gpar callPar2.roundData.F e := by
  intro e _
  obtain ⟨a, ha, hlight⟩ := head_kept
  have hF : callPar2.roundData.F
      = preF (G := Gpar) (scanOfSlot (t := 2) slotPar2 (Finset.univ : Finset (Fin 2))
          (Finset.univ : Finset (Fin 5))) (2 ^ 2) :=
    DriverCall.roundData_F callPar2
  have hmem : a ∈ callPar2.roundData.F.filter (fun g => Gpar.weight g ≤ Gpar.weight e) := by
    rw [hF]
    exact Finset.mem_filter.mpr ⟨ha, hlight e⟩
  have hconn : Conn Gpar (callPar2.roundData.F.filter (fun g => Gpar.weight g ≤ Gpar.weight e))
      (Gpar.src a) (Gpar.dst a) :=
    Conn.step (G := Gpar) a hmem
  simpa [supported, Gpar, WGraph.src, WGraph.dst] using hconn

/-- Lemma 3.7's per-edge premise is vacuous on the witness. -/
theorem badFor_vacuous (e : Fin 5) (he : e ∈ (Finset.univ : Finset (Fin 5)))
    (hns : ¬ supported Gpar callPar2.roundData.F e) :
    callPar2.history.badFor e (callPar2.sched e) :=
  absurd (all_supported e he) hns

/-- `EvidenceOn` is inhabited with no premise: the truth candidate plus vacuous `edge_ok`. -/
noncomputable def callPar2_evidence_uncond : DriverCall.EvidenceOn callPar2 :=
  DriverCall.evidenceOn_of_good_schedule_badFor callPar2 (0 : Fin 5)
    (fun _ _ => Finset.subset_univ _) (by simp) (fun H _ => callPar2_good H callPar2.sched)
    badFor_vacuous

theorem callPar2_unsupp_empty : unsupp Gpar callPar2.roundData.F = ∅ := by
  rw [unsupp, Finset.filter_eq_empty_iff]
  intro e _ h
  exact h (all_supported e (Finset.mem_univ e))

theorem callPar2_U_eq_empty : callPar2.roundData.toCall.U = ∅ := by
  show unsupp Gpar callPar2.roundData.F ∩ (Finset.univ : Finset (Fin 5)) = ∅
  rw [callPar2_unsupp_empty, Finset.empty_inter]

/-- The numerical per-call bound holds with no premise (trivially: `U` is empty). -/
theorem callPar2_card_U_uncond :
    ((callPar2.roundData.toCall.U).card : ℝ) ≤
      10 * ((2 : ℕ) : ℝ) ^ 2 *
          Real.sqrt (((Finset.univ : Finset (Fin 5)).card : ℝ) *
            ((Finset.univ : Finset (Fin 2)).card : ℝ)) +
        4 * ((Finset.univ : Finset (Fin 5)).card : ℝ) / 2 :=
  DriverCall.card_U_le_number_bound_of_badFor callPar2 (0 : Fin 5)
    (fun _ _ => Finset.subset_univ _) (by simp) (by decide)
    (fun H _ => callPar2_good H callPar2.sched) badFor_vacuous

end DriverWitness

end DLMST