import DLMST.SpokeAvoid
import DLMST.ScanOfSlot

/-!
# The driver call: one invocation produces round data *and* a history

§3.6 asks a recursive procedure to return, per instance `(P, E₀)`, the call's batches, its shared
portal set, and the kept forest; §3.3's sampling then reads a history (spokes, forest prefixes, actions)
off the *same* rounds.  The pieces were built separately: `RoundScan.ofScan` turns batches + a
classification + portals into `RoundData`, `HistoryOfRounds.historyOfTable` turns `RoundData` + spoke
batches into a `History`, `SpokeAvoid` derives `hFsp` from the spoke rule, and
`SpokeAvoid.card_U_le_number_bound_of_table` produces §3.5's count for that history.

This file composes them into **one object**: a `DriverCall` carries exactly the data a recursive
invocation decides — the schedule's flat slot map, the portal set, the spoke batches (with their
quota), and the batches' non-forest supply — and every other ingredient is derived:

* `DriverCall.roundData` — the call's `RoundData` (children indexed by `Fin 1`: one recursive call per
  round);
* `DriverCall.roundData_F` — its forest is the scan's prefix forest `preF sc t²`, so `F` is the
  `Finset` the §3.5 per-edge premise and `hFsp` talk about;
* `DriverCall.history` — the §3.3 history of the same rounds, consistent, forest-valued, and with
  `hFsp` derived from the supply hypothesis (`history_hFsp`);
* `DriverCall.eN` — the ground-set enumerations the geometric family `A r` needs;
* `Evidence` — the sampling evidence the algorithm attaches to one call (its chosen candidate, the
  candidate's family membership, the per-edge error statement, Lemma 3.11's `lost` count);
* `Evidence.card_U_le_display` — §3.5's per-call bound `|U(F)| ≤ 10t²√(|E₀||P|) + 4|E₀|/t` in the
  display's shape, with `m := |E|`, `n := |P|` already instantiated and the dominance `E₀ ⊆ E` used;
* `driverRoundData` / `driverHistory` / `driverStrategy` — the instance-wise scheme, feeding
  `Strategy.ofRoundDataT` with `k = 1`, together with the reindexing coherence and
  `display_of_driver`, which is `Strategy.display_of_roundData_sampling` with the derived `herrU`.
-/

namespace DLMST

open Classical

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

/-- **One invocation of the driver's recursion** on the instance `(P, E₀)` with `t` rounds per block.

The data are exactly what a call decides: where each edge of the instance is scheduled (`slot`, the
flat form of `ρ : E → [t]×[t]`), the shared portal set `Pp` (within budget), the per-round spoke
batches `B` with their quota, and the batches' *supply*: at every vertex and in every round, an
incident edge of the batch that the kept forest does not contain.  The supply is what makes the
spokes avoid `F`, hence `hFsp` (`history_hFsp`); everything else the call needs is derived below. -/
structure DriverCall (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (t : ℕ) where
  /-- The schedule, read as a flat slot index (round `(a, b)` is `roundIdx t (a, b)`). -/
  slot : E → Fin (t ^ 2)
  /-- The call's shared portal set `P′`. -/
  Pp : Finset V
  hP' : Pp ⊆ P
  hbudget : 4 * (Fintype.card (Fin (t ^ 2)) * Pp.card) ≤ P.card
  hends : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P
  /-- The per-round spoke batches. -/
  B : Fin t → Fin t → Finset E
  quota : ℕ
  hquota : 1 ≤ quota
  /-- Non-forest supply: every round's batch has, at every vertex, an incident edge outside `F`. -/
  hsupply : ∀ (i j : Fin t) (v : V), ∃ e ∈ Bv G v (B i j),
    e ∉ preF (G := G) (scanOfSlot slot P E₀) (t ^ 2)

namespace DriverCall

variable {P : Finset V} {E₀ : Finset E} {t : ℕ}

/-- The rounds' batch lists: round `k` scans the instance's edges of slot `k`, in weight order. -/
noncomputable def sc (R : DriverCall G P E₀ t) : ℕ → List E :=
  scanOfSlot R.slot P E₀

theorem sc_sub (R : DriverCall G P E₀ t) {k : ℕ} {e : E} (he : e ∈ R.sc k) : e ∈ E₀ :=
  scanOfSlot_sub R.slot P E₀ k he

theorem sc_cover (R : DriverCall G P E₀ t) {e : E} (he : e ∈ E₀) :
    ∃ k, k < t ^ 2 ∧ e ∈ R.sc k :=
  scanOfSlot_cover R.slot P E₀ he

/-- The classification the batches induce, into the single child of each round (`Fin 1`). -/
noncomputable def cls (R : DriverCall G P E₀ t) : E → Option (Fin (t ^ 2) × Fin 1) :=
  fun e => (Strategy.clsOf R.sc t e).map (fun r => (r, 0))

theorem cls_total (R : DriverCall G P E₀ t) {e : E} (he : e ∈ E₀) :
    ∃ p : Fin (t ^ 2) × Fin 1, R.cls e = some p := by
  obtain ⟨k, hk, hmem⟩ := R.sc_cover he
  have hex : ∃ k, k < t ^ 2 ∧ e ∈ R.sc k := ⟨k, hk, hmem⟩
  have hsome : ∃ p : Fin (t ^ 2), Strategy.clsOf R.sc t e = some p := by
    unfold Strategy.clsOf
    rw [dite_eq_left hex]
    exact ⟨_, rfl⟩
  obtain ⟨p, hp⟩ := hsome
  refine ⟨(p, 0), ?_⟩
  rw [cls, hp]
  rfl

/-- **The call's round data**: the scan's batches, the batch-induced classification, and the call's
portal set.  Children are indexed by `Fin 1` — each round makes one recursive call. -/
noncomputable def roundData (R : DriverCall G P E₀ t) : CallOut.RoundData G P E₀ (Fin 1) t :=
  CallOut.RoundData.ofScan (G := G) R.sc (fun k e he => R.sc_sub he) R.Pp R.cls R.hP'
    (by simpa using R.hbudget) R.hends (fun e he _ _ => R.cls_total he)

/-- The round data's forest is the scan's prefix forest at `t²` — the `F` of §3.5's per-edge premise
and of the spoke-avoidance statement. -/
theorem roundData_F (R : DriverCall G P E₀ t) :
    R.roundData.F = preF (G := G) R.sc (t ^ 2) := by
  show Finset.univ.biUnion (fun r : Fin (t ^ 2) => preF (G := G) R.sc ((r : ℕ) + 1))
      = preF (G := G) R.sc (t ^ 2)
  exact biUnion_preF (sc := R.sc) t

theorem roundData_F_sub (R : DriverCall G P E₀ t) : R.roundData.F ⊆ E₀ := by
  rw [roundData_F]
  exact preF_subset_of_scan (fun k e he => R.sc_sub he) (t ^ 2)

/-- The retained set lies in the instance. -/
theorem roundData_U_sub (R : DriverCall G P E₀ t) : R.roundData.toCall.U ⊆ E₀ :=
  Finset.inter_subset_right

section History

variable [Nonempty E]

/-- The schedule as the paper's pair index `ρ : E → [t]×[t]`, the shape the history and the
geometric family are stated at.  It is the inverse flattening of `slot`, so `sched_slot` holds. -/
noncomputable def sched (R : DriverCall G P E₀ t) : E → Fin t × Fin t :=
  fun e => (roundIdx t).symm (R.slot e)

theorem sched_slot (R : DriverCall G P E₀ t) (e : E) : roundIdx t (R.sched e) = R.slot e :=
  Equiv.apply_symm_apply (roundIdx t) (R.slot e)

/-- **The call's history**, read off the round data and the spoke batches; the spokes are required to
avoid the call's forest. -/
noncomputable def history (R : DriverCall G P E₀ t) : History V E t :=
  historyOfTable R.roundData R.B (fun e => e ∉ R.roundData.F) R.quota

theorem history_consistent (R : DriverCall G P E₀ t) : R.history.Consistent (G := G) :=
  historyOfRoundData_consistent R.roundData _

theorem history_isForest (R : DriverCall G P E₀ t) :
    ∀ b i, IsForest G (R.history.forest b i) :=
  isForest_historyOfRoundData R.roundData _

/-- **`hFsp` for the call's history**, from the batches' supply: with `adm := (· ∉ F)` every table
entry is a representative of the batch, hence admissible, hence outside the kept forest. -/
theorem history_hFsp (R : DriverCall G P E₀ t) :
    ∀ (b i : Fin t) (g : E), g ∈ R.history.forest b i → ¬ IsSpoke (R.history.spoke b i) g :=
  hFsp_historyOfTable R.roundData R.B R.quota R.hquota (by
    intro i j v
    obtain ⟨e, he, hne⟩ := R.hsupply i j v
    exact ⟨e, he, by rw [roundData_F]; exact hne⟩)

/-- The ground-set enumerations the geometric family `A r` decodes against. -/
noncomputable def eN (R : DriverCall G P E₀ t) (b i : Fin t) :
    Ground G (R.history.spoke b i) (R.history.forest b i) ≃
      Fin (Fintype.card (Ground G (R.history.spoke b i) (R.history.forest b i))) :=
  Fintype.equivFin _

/-- **The sampling evidence of one call.**  The candidate the algorithm picks for each round, its
membership in the geometric family (the enumerated, computable `A r`), the per-edge error statement of
Lemma 3.7 (produced by the level chains, `ProcChain.unSupp_errOf`), and Lemma 3.11's `lost` count.
Claim 3.12's agreement is about the sample the algorithm *queries*, so it stays a hypothesis of the
counting theorems rather than a field. -/
structure Evidence (R : DriverCall G P E₀ t) where
  c : (r : Fin t × Fin t) → {e : E // R.sched e = r} → Pref
  hc : ∀ r, c r ∈ geomFamily (G := G) R.history R.sched R.eN r
  edge_ok : ∀ e ∈ E₀, ¬ supported G R.roundData.F e →
    R.history.errOf (fun e => c (R.sched e) ⟨e, rfl⟩) e (R.sched e)
  hlost : (R.history.lost R.sched : ℝ) * Real.log 2 ≤
    (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 *
      Real.sqrt ((Fintype.card E : ℝ) * (P.card : ℝ)) + 2 * (Fintype.card E : ℝ) / (t : ℝ)

/-- **§3.5's per-call count, with `m` and `n` instantiated.**  The only numeric hypothesis left is
`2 ≤ t`: `m := |E|` (`hmE` is `le_rfl`) and `n := |P|`.  The truth/estimate/`hFsp` premises are
derived, the sample is `sampleSets`, and the remaining inputs are the evidence `Ev` and the algorithm's
agreement with its own queries (`agree`). -/
theorem Evidence.card_U_le_number_bound {R : DriverCall G P E₀ t} (Ev : Evidence R) (ht : 2 ≤ t)
    (agree : ∀ (r : Fin t × Fin t) (x : {e : E // R.sched e = r}),
      x ∈ sampleSets ht R.sched (geomFamily (G := G) R.history R.sched R.eN) r →
      Ev.c (R.sched x.1) ⟨x.1, rfl⟩ = R.history.pref x.1 r.1 r.2) :
    ((R.roundData.toCall.U).card : ℝ) ≤
      10 * (t : ℝ) ^ 2 * Real.sqrt ((Fintype.card E : ℝ) * (P.card : ℝ)) +
        4 * (Fintype.card E : ℝ) / (t : ℝ) := by
  have hadm : ∀ (i j : Fin t) (v : V), ∃ e ∈ Bv G v (R.B i j), e ∉ R.roundData.F := by
    intro i j v
    obtain ⟨e, he, hne⟩ := R.hsupply i j v
    exact ⟨e, he, by rw [roundData_F]; exact hne⟩
  exact card_U_le_number_bound_of_table R.roundData R.B R.quota R.hquota hadm R.sched R.eN
    Ev.c Ev.hc ht (Nat.cast_nonneg _) (Nat.cast_nonneg _) le_rfl Ev.edge_ok Ev.hlost agree

/-- **§3.5's count at the root instance.**  On `E₀ = univ` the instance's `m` *is* the global `|E|`,
so `card_U_le_number_bound` is already the display's per-instance premise, with `(univ : Finset E).card`
spelled out.  For a strict child `E₀ ⊊ univ` the sampling chain's count is only the global-`m` one —
`|E|`, not `|E₀|` — which is the honest boundary of what this layer proves. -/
theorem Evidence.card_U_le_root {R : DriverCall G P (Finset.univ : Finset E) t} (Ev : Evidence R)
    (ht : 2 ≤ t)
    (agree : ∀ (r : Fin t × Fin t) (x : {e : E // R.sched e = r}),
      x ∈ sampleSets ht R.sched (geomFamily (G := G) R.history R.sched R.eN) r →
      Ev.c (R.sched x.1) ⟨x.1, rfl⟩ = R.history.pref x.1 r.1 r.2) :
    ((R.roundData.toCall.U).card : ℝ) ≤
      10 * ((t : ℝ) ^ 2 * Real.sqrt (((Finset.univ : Finset E).card : ℝ) * (P.card : ℝ))) +
        4 * ((Finset.univ : Finset E).card : ℝ) / (t : ℝ) := by
  have h := Ev.card_U_le_number_bound ht agree
  simpa [mul_assoc, Finset.card_univ] using h

end History

section Scheme

variable [Nonempty E] {tOf : Finset V → Finset E → ℕ}

/-- The instance-wise round data of the driver's recursion. -/
noncomputable def driverRoundData
    (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀)) :
    ∀ (P : Finset V) (E₀ : Finset E), CallOut.RoundData G P E₀ (Fin 1) (tOf P E₀) :=
  fun P E₀ => (DR P E₀).roundData

/-- The instance-wise histories of the same recursion. -/
noncomputable def driverHistory
    (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀)) :
    ∀ (P : Finset V) (E₀ : Finset E), History V E (tOf P E₀) :=
  fun P E₀ => (DR P E₀).history

/-- **The synthesized strategy**: each instance is answered by its own call's round data, with the
`Fin (t² × 1)` children recoded to `Fin (t²)`. -/
noncomputable def driverStrategy
    (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀)) : Strategy G :=
  Strategy.ofRoundDataT tOf (driverRoundData DR)

theorem driverStrategy_wf
    (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀)) :
    Strategy.Wf (driverStrategy DR) :=
  Strategy.ofRoundDataT_wf tOf (driverRoundData DR)

/-- The synthesized strategy's call is the round data's call, reindexed — the coherence the §3.5/§3.6
counts travel through. -/
theorem driverStrategy_call
    (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀))
    (P : Finset V) (E₀ : Finset E) :
    (driverStrategy DR P E₀).2 =
      ((driverRoundData DR P E₀).toCall).reindex finProdFinEquiv := rfl

theorem driverStrategy_F
    (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀))
    (P : Finset V) (E₀ : Finset E) :
    ((driverStrategy DR P E₀).2).F = ((driverRoundData DR P E₀).toCall).F := by
  rw [driverStrategy_call]
  exact CallOut.reindex_F finProdFinEquiv _

theorem driverStrategy_U
    (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀))
    (P : Finset V) (E₀ : Finset E) :
    ((driverStrategy DR P E₀).2).U = ((driverRoundData DR P E₀).toCall).U := by
  rw [driverStrategy_call]
  exact CallOut.reindex_U finProdFinEquiv _

/-- **§3.5's count at every instance, in the strongest shape this layer proves.**  Per instance,
`Evidence` plus the query agreement give `|U(F)| ≤ 10t²√(mn) + 4m/t` with `m := |E|` — the sampling
chain's global edge count.  At the root instance (`E₀ = univ`) this is exactly the display's
per-instance premise (`Evidence.card_U_le_root`); a strict child's own `|E₀|` is smaller, and
replacing `|E|` by it is the remaining gap. -/
theorem driverScheme_herrU
    (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀))
    (Ev : ∀ (P : Finset V) (E₀ : Finset E), DriverCall.Evidence (DR P E₀))
    (htOf : ∀ (P : Finset V) (E₀ : Finset E), 2 ≤ tOf P E₀)
    (agree : ∀ (P : Finset V) (E₀ : Finset E) (r : Fin (tOf P E₀) × Fin (tOf P E₀))
      (x : {e : E // (DR P E₀).sched e = r}),
      x ∈ sampleSets (htOf P E₀) (DR P E₀).sched
        (geomFamily (G := G) (DR P E₀).history (DR P E₀).sched (DR P E₀).eN) r →
      (Ev P E₀).c ((DR P E₀).sched x.1) ⟨x.1, rfl⟩ =
        (DR P E₀).history.pref x.1 r.1 r.2) :
    ∀ (P' : Finset V) (E₀' : Finset E), (((driverRoundData DR P' E₀').toCall.U).card : ℝ) ≤
      10 * ((tOf P' E₀' : ℝ) ^ 2 * Real.sqrt ((Fintype.card E : ℝ) * (P'.card : ℝ))) +
        4 * (Fintype.card E : ℝ) / (tOf P' E₀' : ℝ) := by
  intro P' E₀'
  change (((DR P' E₀').roundData.toCall.U).card : ℝ) ≤
    10 * ((tOf P' E₀' : ℝ) ^ 2 * Real.sqrt ((Fintype.card E : ℝ) * (P'.card : ℝ))) +
      4 * (Fintype.card E : ℝ) / (tOf P' E₀' : ℝ)
  simpa [mul_assoc] using (Ev P' E₀').card_U_le_number_bound (htOf P' E₀') (agree P' E₀')

/-- **The root call's §3.5 count in the display's exact shape**: `|U(F)| ≤
10t²√(|E||P|) + 4|E|/t` with `|E|` written as `(univ : Finset E).card`. -/
theorem driverScheme_herrU_root
    (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀))
    (Ev : ∀ (P : Finset V) (E₀ : Finset E), DriverCall.Evidence (DR P E₀))
    (htOf : ∀ (P : Finset V) (E₀ : Finset E), 2 ≤ tOf P E₀)
    (agree : ∀ (P : Finset V) (E₀ : Finset E) (r : Fin (tOf P E₀) × Fin (tOf P E₀))
      (x : {e : E // (DR P E₀).sched e = r}),
      x ∈ sampleSets (htOf P E₀) (DR P E₀).sched
        (geomFamily (G := G) (DR P E₀).history (DR P E₀).sched (DR P E₀).eN) r →
      (Ev P E₀).c ((DR P E₀).sched x.1) ⟨x.1, rfl⟩ =
        (DR P E₀).history.pref x.1 r.1 r.2)
    (P : Finset V) :
    (((driverRoundData DR P (Finset.univ : Finset E)).toCall.U).card : ℝ) ≤
      10 * ((tOf P Finset.univ : ℝ) ^ 2 *
          Real.sqrt (((Finset.univ : Finset E).card : ℝ) * (P.card : ℝ))) +
        4 * ((Finset.univ : Finset E).card : ℝ) / (tOf P Finset.univ : ℝ) :=
  (Ev P Finset.univ).card_U_le_root (htOf P Finset.univ) (agree P Finset.univ)

/-- **The driver's per-instance numeric interface**, packaged for `Strategy.display_of_counts`: each
call's retained set is bounded by itself and its child input by the sum of its children — the
transport `counts_of_roundDataT` runs through the `Fin (t²)` reindexing. -/
noncomputable def driverScheme_counts
    (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀)) :
    ∀ (P : Finset V) (E₀ : Finset E), Strategy.Counts (driverStrategy DR) P E₀ :=
  Strategy.counts_of_roundDataT tOf (driverRoundData DR)
    (fun P E₀ => ((driverRoundData DR P E₀).toCall.U).card)
    (fun P E₀ => ∑ i, ((driverRoundData DR P E₀).toCall.kidE i).card)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl)

/-- **§4's root display for the synthesized strategy.**  `Strategy.display_of_roundData_sampling` read
on the driver's own round data: the strategy, its well-formedness and the `Fin (t²)` reindexing are the
synthesized ones, and the three numeric premises are stated directly on `driverRoundData` — the
instance-local §3.5 count (`herrU`, at the root instance supplied by `driverScheme_herrU_root`), §3.6's
per-call input count (`hrnd`), and the level ladder's geometric `t` (`htd`). -/
theorem display_of_driver
    (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀))
    (P : Finset V) (E₀ : Finset E) {γ ε : ℝ}
    (hγ1 : 1 ≤ γ) (hε : 0 < ε) (hγε : 16 ≤ ε * γ)
    (hnm : (P.card : ℝ) ≤ 2 * (E₀.card : ℝ))
    (hnpos : ∀ (P' : Finset V), 1 ≤ P'.card)
    (herrU : ∀ (P' : Finset V) (E₀' : Finset E), (((driverRoundData DR P' E₀').toCall.U).card : ℝ) ≤
      10 * ((tOf P' E₀' : ℝ) ^ 2 * Real.sqrt ((E₀'.card : ℝ) * (P'.card : ℝ))) +
        4 * (E₀'.card : ℝ) / (tOf P' E₀' : ℝ))
    (hrnd : ∀ (P' : Finset V) (E₀' : Finset E),
      (∑ i, ((driverRoundData DR P' E₀').toCall.kidE i).card) ≤
        ((driverRoundData DR P' E₀').toCall.U).card + 2 * (tOf P' E₀') ^ 2 * (P'.card - 1) +
          (tOf P' E₀') * ((P'.card - 1) + (8 * (tOf P' E₀') ^ 3) ^ 2 * P'.card))
    (htd : ∀ (d : ℕ), d ≤ E₀.card → ∀ a ∈ (Level.chain P E₀
        (Strategy.ofRoundDataT tOf (driverRoundData DR))
        (Strategy.ofRoundDataT_wf tOf (driverRoundData DR)) d).insts,
      (tOf a.1 a.2 : ℝ) = γ * ((d : ℝ) + 1) ^ 3) :
    ((driverStrategy DR P E₀).2.F.card : ℝ) +
        (((driverStrategy DR P E₀).2.U).card : ℝ) +
        (((∑ i, ((driverStrategy DR P E₀).2.kidE i).card) : ℕ) : ℝ) ≤
      ε * (E₀.card : ℝ) +
        (Real.sqrt 2 + γ ^ 2 * 800000 +
            Real.sqrt 2 * ((2 * γ ^ 2 + γ + 64 * γ ^ 7) * ((202 : ℝ) ^ 21 * 2))) *
          Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) := by
  show ((Strategy.ofRoundDataT tOf (driverRoundData DR) P E₀).2.F.card : ℝ) +
        (((Strategy.ofRoundDataT tOf (driverRoundData DR) P E₀).2.U).card : ℝ) +
        (((∑ i, ((Strategy.ofRoundDataT tOf (driverRoundData DR) P E₀).2.kidE i).card) : ℕ) : ℝ) ≤
      ε * (E₀.card : ℝ) +
        (Real.sqrt 2 + γ ^ 2 * 800000 +
            Real.sqrt 2 * ((2 * γ ^ 2 + γ + 64 * γ ^ 7) * ((202 : ℝ) ^ 21 * 2))) *
          Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ))
  exact Strategy.display_of_roundData_sampling tOf (driverRoundData DR) P E₀ hγ1 hε hγε hnm hnpos
    herrU hrnd htd

end Scheme

end DriverCall

end DLMST