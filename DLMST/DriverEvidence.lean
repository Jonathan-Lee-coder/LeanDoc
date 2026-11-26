import DLMST.InstanceHistory
import DLMST.DriverCall
import DLMST.InputCount

/-!
# The driver's evidence, built from truth

`DriverCall.EvidenceOn` has four fields: the per-round candidate `c` (with its family membership
`hc`), the per-edge error statement `edge_ok` (Lemma 3.7), and Lemma 3.11's `lost` bound `hlost`.
`InstanceHistory.exists_schedule_lostOn_paper` now *proves* the instance-local Lemma 3.11 from
Lemma 3.10, so `hlost` can follow from a schedule that is good for the instance's legal histories;
and taking `c` to be the history's **true preference vector** makes `hc`
(`truth_of_historyOn`) and the sampling agreement (`agree`) theorems, while reducing `edge_ok` to
"an unsupported edge's own slot is bad for it" (Lemma 3.7's per-edge conclusion).

This file performs that reduction:

* `history_legalOn` — a driver whose batches lie in `E₀` (`hB`) induces a *legal instance history*
  (`LegalOn`): spokes are selected batch edges (hence instance edges incident at the vertex), forests
  are round prefixes of `F ⊆ E₀` with at most `|P|−1` edges.
* `truthCand`, `evidenceOn_of_good_schedule` — the evidence with `c` the truth, `hc` from
  `truth_of_historyOn`, `hlost` from a good-schedule hypothesis, `edge_ok` taken as Lemma 3.7's
  per-edge output.
* `agree_truthOn` — Claim 3.12's agreement is trivial for the truth candidate.
* `card_U_le_number_bound_of_truth` — §3.5's per-call count with `m := |E₀|`, `n := |P|` and **no**
  `agree` premise.
* `exists_good_schedule` — the schedule existence for a driver's instance (`R.hends` supplies the
  endpoint geometry).

**Boundary.**  `evidenceOn_of_good_schedule` takes the good-schedule statement *at the call's own
schedule* `R.sched`: `exists_good_schedule` produces *some* schedule good for all legal histories, but
nothing here proves that the call's own schedule (which also has to satisfy the supply hypothesis
`hsupply`, a property of the chosen rounds) is that one.  Connecting the two is the algorithm's
joint choice of schedule and batches — the remaining gap, see `CORRESPONDENCE.md`.
-/

namespace DLMST

open Classical

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

namespace DriverCall

variable {P : Finset V} {E₀ : Finset E} {t : ℕ} [Nonempty E]

/-- **The driver's history is legal on the instance**, provided its batches are subsets of `E₀`
(`hB`, the paper's "the batches are instance edges").  Spokes are selected representatives of the
batches, hence `E₀`-edges incident at their vertex; forests are round prefixes of the kept forest
`F ⊆ E₀`, and a forest with both endpoints in `P` has at most `|P|−1` edges. -/
theorem history_legalOn (R : DriverCall G P E₀ t) (e₀ : E)
    (hB : ∀ i j, R.B i j ⊆ E₀) (hP0 : 0 < P.card) :
    LegalOn (G := G) P E₀ e₀ R.history := by
  refine ⟨R.history_consistent, ?_, ?_⟩
  · intro b i v
    have hadm : ∀ (i j : Fin t) (v : V), ∃ e ∈ Bv G v (R.B i j), e ∉ R.roundData.F := by
      intro i j v
      obtain ⟨e, he, hne⟩ := R.hsupply i j v
      exact ⟨e, he, by rw [roundData_F]; exact hne⟩
    have hne := selAt_nonempty_of_adm (G := G) (B := R.B b i)
      (adm := fun e => e ∉ R.roundData.F) R.hquota (hadm b i v)
    have hmem : R.history.spoke b i v ∈
        selAt G (R.B b i) (fun e => e ∉ R.roundData.F) R.quota v :=
      spokeTable_mem (G := G) R.B (fun e => e ∉ R.roundData.F) R.quota b i v hne
    have hBv := (batchSpec_selAt G (R.B b i) (fun e => e ∉ R.roundData.F) R.quota).sel_sub v hmem
    exact Or.inr ⟨hB b i (mem_Bv.mp hBv).1, (mem_Bv.mp hBv).2⟩
  · intro b i
    have hsub : R.history.forest b i ⊆ R.roundData.F := by
      change forestUpTo R.roundData (b, i) ⊆ R.roundData.F
      exact forestUpTo_sub R.roundData (b, i)
    refine ⟨hsub.trans R.roundData_F_sub, ?_⟩
    exact card_le_card_sub_one_of_isForest_of_ends (R.history_isForest b i)
      (fun e he => R.hends e (R.roundData_F_sub (hsub he))) hP0

/-- **The truth candidate on the instance**: each round's candidate assigns every edge its own
preference in that round. -/
noncomputable def truthCand (R : DriverCall G P E₀ t) :
    (r : Fin t × Fin t) → {e : E // e ∈ E₀ ∧ R.sched e = r} → Pref :=
  fun r x => R.history.pref x.1 r.1 r.2

/-- **Evidence with the truth candidate.**  `hc` is `truth_of_historyOn`, `hlost` is the good-schedule
hypothesis at the call's own schedule (produced by `exists_schedule_lostOn_paper` for a schedule
chosen to be good for all legal histories), and `edge_ok` is Lemma 3.7's per-edge output, taken as
a hypothesis. -/
noncomputable def evidenceOn_of_good_schedule (R : DriverCall G P E₀ t) (e₀ : E)
    (hB : ∀ i j, R.B i j ⊆ E₀) (hP0 : 0 < P.card)
    (hgood : ∀ H : History V E t, LegalOn (G := G) P E₀ e₀ H →
      (H.lostOn E₀ R.sched : ℝ) * Real.log 2 ≤
        (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 *
            Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) + 2 * (E₀.card : ℝ) / (t : ℝ))
    (hedge : ∀ e ∈ E₀, ¬ supported G R.roundData.F e →
      R.history.errOf (estOfOn E₀ R.sched (truthCand R)) e (R.sched e)) :
    EvidenceOn R :=
  { c := truthCand R
    hc := truth_of_historyOn R.history E₀ R.history_consistent R.history_isForest
      R.history_hFsp R.sched R.eN
    edge_ok := hedge
    hlost := hgood R.history (history_legalOn R e₀ hB hP0) }

/-- **Claim 3.12's agreement holds trivially for the truth candidate**: the algorithm's estimate and
the history's own preference coincide by definition. -/
theorem agree_truthOn (R : DriverCall G P E₀ t) (ht : 2 ≤ t) :
    ∀ (r : Fin t × Fin t) (x : {e : E // e ∈ E₀ ∧ R.sched e = r}),
      x ∈ sampleSetsOn E₀ ht R.sched (geomFamilyOn (G := G) R.history R.sched E₀ R.eN) r →
      truthCand R (R.sched x.1) ⟨x.1, x.2.1, rfl⟩ = R.history.pref x.1 r.1 r.2 := by
  intro r x _
  show R.history.pref x.1 (R.sched x.1).1 (R.sched x.1).2 = R.history.pref x.1 r.1 r.2
  rw [x.2.2]

/-- **§3.5's per-call count with the truth evidence, and no agreement premise.**  The remaining
inputs are the endpoint geometry (`R.hends`), the numbers (`ht`), the good-schedule statement at the
call's own schedule and Lemma 3.7's per-edge step. -/
theorem card_U_le_number_bound_of_truth (R : DriverCall G P E₀ t) (e₀ : E)
    (hB : ∀ i j, R.B i j ⊆ E₀) (hP0 : 0 < P.card) (ht : 2 ≤ t)
    (hgood : ∀ H : History V E t, LegalOn (G := G) P E₀ e₀ H →
      (H.lostOn E₀ R.sched : ℝ) * Real.log 2 ≤
        (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 *
            Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) + 2 * (E₀.card : ℝ) / (t : ℝ))
    (hedge : ∀ e ∈ E₀, ¬ supported G R.roundData.F e →
      R.history.errOf (estOfOn E₀ R.sched (truthCand R)) e (R.sched e)) :
    ((R.roundData.toCall.U).card : ℝ) ≤
      10 * (t : ℝ) ^ 2 * Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) +
        4 * (E₀.card : ℝ) / (t : ℝ) :=
  EvidenceOn.card_U_le_number_bound (R := R)
    (evidenceOn_of_good_schedule R e₀ hB hP0 hgood hedge) ht (agree_truthOn R ht)

/-- **A good schedule exists for the call's instance**: one schedule on which *every* legal instance
history has at most `(2√2+4)t²√(|E₀||P|)/log 2 + 2|E₀|/(t log 2)` bad-round edges.  The endpoint
geometry is the call's own `R.hends`. -/
theorem exists_good_schedule (R : DriverCall G P E₀ t) (e₀ : E) (ht : 2 ≤ t) :
    ∃ ρ : Sched E t, ∀ H : History V E t, LegalOn (G := G) P E₀ e₀ H →
      (H.lostOn E₀ ρ : ℝ) * Real.log 2 ≤
        (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 *
            Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) + 2 * (E₀.card : ℝ) / (t : ℝ) :=
  exists_good_scheduleOn P E₀ e₀ R.hends ht

end DriverCall

end DLMST