import DLMST.Lemma37Bad
import DLMST.ProcChain

/-!
# The per-edge `badFor` premise: single-round calls, and the process chains

`Lemma37Bad` reduced the driver's `edge_ok` to the paper's per-edge sentence

`¬ supported G R.roundData.F e → R.history.badFor e (R.sched e)`   (`e ∈ E₀`),

and `ProcChain.unSupp_errOf` proves the same sentence from one level chain per edge.  This file joins
the two, and isolates the one general case where the sentence is *automatic*:

* `History.badFor_one` — on a single-round call (`t = 1`) Definition 3.4 declares **every** round bad
  for **every** edge: `badProject`'s "every later round of the block prefers `find`" and `badFind`'s
  "every later block is all `find`" both quantify over an empty range.
* `DriverCall.badFor_of_unsupp_one` — hence for `DriverCall G P E₀ 1` the per-edge premise of
  Lemma 3.7 holds for **every** graph, instance and returned forest, with no hypothesis at all.
* `DriverCall.evidenceOn_of_good_schedule_one` — consequently `EvidenceOn` at `t = 1` needs only the
  good-schedule premise (B6), `hB : B ⊆ E₀` and `0 < |P|`: Lemma 3.7's process side has disappeared.
  (The numeric per-call bound is unavailable at `t = 1`, since the estimate counts require `2 ≤ t`.)

For general `t` the process side stays a hypothesis, but only of the shape the algorithm actually
supplies: `DriverCall.badFor_of_procChains` takes one `ProcChain` per edge — the level chain of the
edge's projections in the real recursion, with the level-`0` forest the call's own forest and the
level-`0` slot the call's own schedule — and yields the per-edge sentence; `evidenceOn_of_procChains`
and `card_U_le_number_bound_of_procChains` then run the whole §3.5 chain on it.  Two of the
`ProcChain` fields are *not* process assumptions for a driver call: consistency is
`R.history_consistent` and spoke-incidence is `DriverCall.history_spoke_incident` (derived from the
batch supply through `historyOfTable_spoke_incident`).  What remains for the algorithm to discharge is
`hproj` (an edge passed to a child was preferred `project` at its assigned round), the frozen-spoke and
return facts `hfroz`/`hret`/`hsub`, and the child-call facts `hmsf`/`hlift`/`hσS`.
-/

namespace DLMST

open Classical

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [LinearOrder E] {G : WGraph V E}

namespace History

/-- **On a single-round call every round is bad for every edge.**  `t = 1` leaves `badProject`'s and
`badFind`'s universal tails without any instance. -/
theorem badFor_one (H : History V E 1) (e : E) (p : Fin 1 × Fin 1) : H.badFor e p := by
  obtain ⟨b, i⟩ := p
  have hb : b = 0 := Fin.ext (Nat.lt_one_iff.mp b.isLt)
  have hi : i = 0 := Fin.ext (Nat.lt_one_iff.mp i.isLt)
  rw [hb, hi]
  have hlt : ∀ j : Fin 1, ¬ ((0 : Fin 1) < j) := by
    intro j
    have h' : ¬ ((0 : ℕ) < (j : ℕ)) := by
      rw [Nat.lt_one_iff.mp j.isLt]
      exact Nat.lt_irrefl 0
    exact h'
  unfold History.badFor bad badProject badFind
  cases H.pref e 0 0 with
  | find => exact Or.inr ⟨rfl, fun c hc => absurd hc (hlt c)⟩
  | project => exact Or.inl ⟨rfl, fun j hj => absurd hj (hlt j)⟩

end History

namespace DriverCall

variable {P : Finset V} {E₀ : Finset E} {t : ℕ} [Nonempty E]

/-- **Lemma 3.7's per-edge premise is automatic on single-round calls.** -/
theorem badFor_of_unsupp_one (R : DriverCall G P E₀ 1) :
    ∀ e ∈ E₀, ¬ supported G R.roundData.F e → R.history.badFor e (R.sched e) :=
  fun e _ _ => History.badFor_one R.history e (R.sched e)

/-- **`EvidenceOn` at `t = 1` needs no process premise at all**: the per-edge sentence is automatic,
so only the good-schedule premise (B6), `hB` and `0 < |P|` remain. -/
noncomputable def evidenceOn_of_good_schedule_one (R : DriverCall G P E₀ 1) (e₀ : E)
    (hB : ∀ i j, R.B i j ⊆ E₀) (hP0 : 0 < P.card)
    (hgood : ∀ H : History V E 1, LegalOn (G := G) P E₀ e₀ H →
      (H.lostOn E₀ R.sched : ℝ) * Real.log 2 ≤
        (2 * Real.sqrt 2 + 4) * ((1 : ℕ) : ℝ) ^ 2 *
            Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) + 2 * (E₀.card : ℝ) / ((1 : ℕ) : ℝ)) :
    EvidenceOn R :=
  evidenceOn_of_good_schedule_badFor R e₀ hB hP0 hgood (badFor_of_unsupp_one R)

/-- **Spoke incidence for the call's history**, derived from the batch supply: the spoke table picks
each spoke from the round's batch, and the batches are incident at their vertices.  This is the
`hspoke` field of a `ProcChain` at a driver call, so the chain construction never assumes it. -/
theorem history_spoke_incident (R : DriverCall G P E₀ t) :
    ∀ (b i : Fin t) (v : V), incident G v (R.history.spoke b i v) :=
  historyOfTable_spoke_incident R.roundData R.B (fun e => e ∉ R.roundData.F) R.quota
    R.hquota
    (fun i j v => by
      obtain ⟨e, he, hne⟩ := R.hsupply i j v
      exact ⟨e, he, by rw [roundData_F]; exact hne⟩)

/-- **The per-edge sentence from one level chain per edge.**  Each chain starts at the call's own
forest and its own schedule and terminates in a supported depth-one projection; with the truth
candidate the estimate never disagrees, so `unSupp_errOf`'s `errOf` is `badFor`. -/
theorem badFor_of_procChains (R : DriverCall G P E₀ t) (lev : E → ℕ → Lev E)
    (C : ∀ e, ProcChain (G := G) R.history (lev e))
    (h0e : ∀ e, (lev e 0).e = e) (h0F : ∀ e, (lev e 0).F = R.roundData.F)
    (hslot : ∀ e, (C e).slot 0 = R.sched e) (hchild : ∀ e, Lev.supp G (lev e 1)) :
    ∀ e ∈ E₀, ¬ supported G R.roundData.F e → R.history.badFor e (R.sched e) := by
  intro e he hns
  have h := ProcChain.unSupp_errOf (G := G) (H := R.history) R.sched
    (estOfOn E₀ R.sched (truthCand R)) lev C h0e h0F hslot hchild e hns
  exact (errOf_truth_iff R he).mp h

/-- **`EvidenceOn` from the process chains**: `edge_ok` is discharged by `badFor_of_procChains`; what
is left is the good-schedule premise, `hB` and `0 < |P|`. -/
noncomputable def evidenceOn_of_procChains (R : DriverCall G P E₀ t) (lev : E → ℕ → Lev E)
    (C : ∀ e, ProcChain (G := G) R.history (lev e))
    (h0e : ∀ e, (lev e 0).e = e) (h0F : ∀ e, (lev e 0).F = R.roundData.F)
    (hslot : ∀ e, (C e).slot 0 = R.sched e) (hchild : ∀ e, Lev.supp G (lev e 1))
    (e₀ : E) (hB : ∀ i j, R.B i j ⊆ E₀) (hP0 : 0 < P.card)
    (hgood : ∀ H : History V E t, LegalOn (G := G) P E₀ e₀ H →
      (H.lostOn E₀ R.sched : ℝ) * Real.log 2 ≤
        (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 *
            Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) + 2 * (E₀.card : ℝ) / (t : ℝ)) :
    EvidenceOn R :=
  evidenceOn_of_good_schedule_badFor R e₀ hB hP0 hgood
    (badFor_of_procChains R lev C h0e h0F hslot hchild)

/-- **§3.5's per-call bound with the per-edge premise discharged by the process chains.** -/
theorem card_U_le_number_bound_of_procChains (R : DriverCall G P E₀ t) (lev : E → ℕ → Lev E)
    (C : ∀ e, ProcChain (G := G) R.history (lev e))
    (h0e : ∀ e, (lev e 0).e = e) (h0F : ∀ e, (lev e 0).F = R.roundData.F)
    (hslot : ∀ e, (C e).slot 0 = R.sched e) (hchild : ∀ e, Lev.supp G (lev e 1))
    (e₀ : E) (hB : ∀ i j, R.B i j ⊆ E₀) (hP0 : 0 < P.card) (ht : 2 ≤ t)
    (hgood : ∀ H : History V E t, LegalOn (G := G) P E₀ e₀ H →
      (H.lostOn E₀ R.sched : ℝ) * Real.log 2 ≤
        (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 *
            Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) + 2 * (E₀.card : ℝ) / (t : ℝ)) :
    ((R.roundData.toCall.U).card : ℝ) ≤
      10 * (t : ℝ) ^ 2 * Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) +
        4 * (E₀.card : ℝ) / (t : ℝ) :=
  card_U_le_number_bound_of_badFor R e₀ hB hP0 ht hgood
    (badFor_of_procChains R lev C h0e h0F hslot hchild)

end DriverCall


namespace DriverWitness

/-- **The `t = 1` witness is small enough for the average bound**: `5·log 2 ≤ (2√2+4)·√10 + 10`. -/
theorem callPar_one_hbig :
    ((Finset.univ : Finset (Fin 5)).card : ℝ) * Real.log 2 ≤
      (2 * Real.sqrt 2 + 4) * ((1 : ℕ) : ℝ) ^ 2 *
          Real.sqrt (((Finset.univ : Finset (Fin 5)).card : ℝ) *
            ((Finset.univ : Finset (Fin 2)).card : ℝ)) +
        2 * ((Finset.univ : Finset (Fin 5)).card : ℝ) / ((1 : ℕ) : ℝ) := by
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

/-- **The `t = 1` witness's own schedule is good**, unconditionally. -/
theorem callPar_one_good (H : History (Fin 2) (Fin 5) 1) (ρ : Sched (Fin 5) 1) :
    (H.lostOn (Finset.univ : Finset (Fin 5)) ρ : ℝ) * Real.log 2 ≤
      (2 * Real.sqrt 2 + 4) * ((1 : ℕ) : ℝ) ^ 2 *
          Real.sqrt (((Finset.univ : Finset (Fin 5)).card : ℝ) *
            ((Finset.univ : Finset (Fin 2)).card : ℝ)) +
        2 * ((Finset.univ : Finset (Fin 5)).card : ℝ) / ((1 : ℕ) : ℝ) :=
  lostOn_log_le_of_bound callPar_one_hbig H ρ

/-- **`EvidenceOn` for the `t = 1` witness, with no premise at all**: `edge_ok` is
`badFor_of_unsupp_one` and the good schedule is the small-instance bound. -/
noncomputable def callPar_evidence_uncond : DriverCall.EvidenceOn callPar :=
  DriverCall.evidenceOn_of_good_schedule_one callPar (0 : Fin 5)
    (fun _ _ => Finset.subset_univ _) (by simp) (fun H _ => callPar_one_good H callPar.sched)

end DriverWitness

end DLMST
