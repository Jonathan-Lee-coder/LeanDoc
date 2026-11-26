import DLMST.DriverCall

/-!
# Choosing the driver's data, and termination

`DriverCall.lean` packaged one invocation as a single object; this file *chooses* that object on
every instance and proves the synthesized strategy terminates.

## The data

`DriverCall.ofSlot` builds a call from the four decisions alone: a slot map, a portal set within
budget, the batch family, and the quota.  The batches are taken to be **all of `E`** and the quota
`1`, so the only constraint the batches carry is the supply.

* `slotFirst` — a slot map exists as soon as `t ≥ 1` (everything scheduled in round `0`).  Which
  round each edge *should* land in is §3.3's schedule, and `ScanOfSlot.exists_schedule_strategy`
  produces one schedule that serves both the scans and Lemma 3.11 at once; the slot's content enters
  only through the §3.5 counts.
* `ofSlot_noPortal` — the empty portal set, always within budget.
* `ofSlot_portals` — the paper's block-wise portal union `portalsOf`, within budget by
  `portalsOf_budget` from the per-block counts `8t³|Q_b| ≤ 2n`.
* `firstCall` — the two combined: a definite call on every instance with `t ≥ 1`.

## The one data-level fact

The supply — at every vertex, an edge outside the kept forest — is a hypothesis, not a consequence
of the other fields, and cannot be derived: the spoke table is total on `V`, so a vertex whose
incident edges are all kept has no admissible spoke, and its table entry is an arbitrary edge that
`hFsp` would reject.  In the paper this is exactly Claim 3.6's condition on the spokes ("the spokes
avoid `F`"), so `ofSlot` takes it as the single input beyond the endpoint geometry `hends`; the §3.5
chain consumes it through `DriverCall.history_hFsp`.

## Termination

* `F_nonempty` — a nonempty instance's scan forest is nonempty (`preF_nonempty_of_mem`: a non-loop
  edge is kept or its ends were already joined).
* `kidE_card_lt` — a child receives no forest edge, so its input misses one edge of the instance.
* `driverStrategy_strict` — hence every child of a nonempty instance is strictly smaller.
* `driverStrategyLeaf` — the synthesized call is `RoundData`-shaped and keeps its `t² · 1` children
  even at `E₀ = ∅`; the leaf-aware variant answers the empty instance by the childless call
  (`Strategy.leafCall`), is `Wf`, `Strict` and `Leaf`, and agrees with `driverStrategy` on every
  nonempty instance (`driverStrategyLeaf_eq`).
* `driverScheme_chain_empty` — with `Wf`/`Strict`/`Leaf`, every level beyond `|E₀|` is empty, so
  §3.6's sums over the levels account for *all* edges (`LevelChain.chain_insts_empty_of_le`).
-/

namespace DLMST

open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

namespace DriverCall

variable {P : Finset V} {E₀ : Finset E} {t : ℕ}

/-! ## Termination of one call -/

/-- **A nonempty instance's scan forest is nonempty.**  An edge of the instance is scanned in some
round; a non-loop edge is either kept or rejected because its ends were already joined, and joining
two distinct vertices takes an accepted edge. -/
theorem F_nonempty (R : DriverCall G P E₀ t) (hne : E₀.Nonempty)
    (hnoloop : ∀ e ∈ E₀, G.src e ≠ G.dst e) : R.roundData.F.Nonempty := by
  obtain ⟨e₀, he₀⟩ := hne
  obtain ⟨k, hk, hmem⟩ := R.sc_cover he₀
  obtain ⟨f, hf⟩ := preF_nonempty_of_mem (G := G) (sc := R.sc) hk hmem (hnoloop e₀ he₀)
  exact ⟨f, by rw [roundData_F]; exact hf⟩

/-- **A forest edge shrinks every child.**  The child's input lies in the instance and misses `f`,
which the instance contains (`toCall_kidE_card_lt`). -/
theorem kidE_card_lt (R : DriverCall G P E₀ t) {f : E} (hf : f ∈ R.roundData.F)
    (p : Fin (t ^ 2) × Fin 1) : (R.roundData.toCall.kidE p).card < E₀.card :=
  R.roundData.toCall_kidE_card_lt hf p

/-- **Every child of a nonempty instance is strictly smaller**, with the forest's existence derived. -/
theorem kidE_card_lt_of_nonempty (R : DriverCall G P E₀ t) (hne : E₀.Nonempty)
    (hnoloop : ∀ e ∈ E₀, G.src e ≠ G.dst e) (p : Fin (t ^ 2) × Fin 1) :
    (R.roundData.toCall.kidE p).card < E₀.card := by
  obtain ⟨f, hf⟩ := R.F_nonempty hne hnoloop
  exact R.kidE_card_lt hf p

/-! ## Choosing the data: slot, portal set, batches, quota -/

/-- **A slot map, for every `t ≥ 1`**: everything in round `0`.  The schedule's *content* (which
round each edge lands in) is §3.3's and is supplied by `ScanOfSlot.exists_schedule_strategy`; for the
existence of a call any map into `Fin (t²)` serves. -/
noncomputable def slotFirst (h : 0 < t ^ 2) : E → Fin (t ^ 2) := fun _ => ⟨0, h⟩

/-- **The call of a slot map and a portal set.**  The batches are all of `E` (a vertex with any
incident edge has one in every batch), the quota is `1`, and `hsup` is the supply: at every vertex,
an edge outside the kept forest.  That is the paper's Claim 3.6 condition on the spokes; it is data
because the spoke table is total on `V` and a vertex all of whose edges are kept admits no spoke
outside the forest. -/
noncomputable def ofSlot (slot : E → Fin (t ^ 2)) (Pp : Finset V) (hP' : Pp ⊆ P)
    (hbudget : 4 * (Fintype.card (Fin (t ^ 2)) * Pp.card) ≤ P.card)
    (hends : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hsup : ∀ v : V, ∃ e ∈ (Finset.univ : Finset E), incident G v e ∧
      e ∉ preF (G := G) (scanOfSlot slot P E₀) (t ^ 2)) :
    DriverCall G P E₀ t where
  slot := slot
  Pp := Pp
  hP' := hP'
  hbudget := hbudget
  hends := hends
  B := fun _ _ => Finset.univ
  quota := 1
  hquota := le_rfl
  hsupply := by
    intro i j v
    obtain ⟨e, he, hinc, hF⟩ := hsup v
    exact ⟨e, mem_Bv.mpr ⟨he, hinc⟩, hF⟩

/-- **The call with the empty portal set** — always within budget. -/
noncomputable def ofSlot_noPortal (slot : E → Fin (t ^ 2))
    (hends : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hsup : ∀ v : V, ∃ e ∈ (Finset.univ : Finset E), incident G v e ∧
      e ∉ preF (G := G) (scanOfSlot slot P E₀) (t ^ 2)) :
    DriverCall G P E₀ t :=
  ofSlot slot ∅ (Finset.empty_subset _) (by simp) hends hsup

/-- **The call with the paper's portal set**: the union of the blocks' portals, within budget by
`portalsOf_budget` from the per-block counts. -/
noncomputable def ofSlot_portals (ht : 0 < t) (slot : E → Fin (t ^ 2))
    (Pset : Finset V → Finset E → ℕ → Finset V)
    (hPsub : ∀ (P : Finset V) (E₀ : Finset E) (b : ℕ), Pset P E₀ b ⊆ P)
    (hportal : ∀ (P : Finset V) (E₀ : Finset E) (b : ℕ), b ∈ Finset.range t →
      8 * t ^ 3 * (Pset P E₀ b).card ≤ 2 * P.card)
    (hends : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hsup : ∀ v : V, ∃ e ∈ (Finset.univ : Finset E), incident G v e ∧
      e ∉ preF (G := G) (scanOfSlot slot P E₀) (t ^ 2)) :
    DriverCall G P E₀ t :=
  ofSlot slot (portalsOf (t := t) Pset P E₀) (portalsOf_sub Pset hPsub P E₀)
    (portalsOf_budget ht Pset hportal P E₀) hends hsup

/-- **A definite call on every instance** with `t ≥ 1`: no portals, everything in round `0`, all
edges as batches, quota `1`.  Only the supply is assumed. -/
noncomputable def firstCall (ht : 0 < t)
    (hends : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hsup : ∀ v : V, ∃ e ∈ (Finset.univ : Finset E), incident G v e ∧
      e ∉ preF (G := G) (scanOfSlot (slotFirst (t := t) (Nat.pow_pos ht)) P E₀) (t ^ 2)) :
    DriverCall G P E₀ t :=
  ofSlot_noPortal (slotFirst (t := t) (Nat.pow_pos ht)) hends hsup

variable {tOf : Finset V → Finset E → ℕ}

/-- **The driver's data, chosen on every instance.**  With `t ≥ 1` everywhere, the endpoint geometry
and the supply, each instance is answered by `firstCall`; this is the `DR` that the synthesized
strategy, the §3.5 counts and the display consume. -/
noncomputable def driverCallFirst (htOf : ∀ (P : Finset V) (E₀ : Finset E), 0 < tOf P E₀)
    (hends : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hsup : ∀ (P : Finset V) (E₀ : Finset E) (v : V),
      ∃ e ∈ (Finset.univ : Finset E), incident G v e ∧
        e ∉ preF (G := G)
          (scanOfSlot (slotFirst (t := tOf P E₀) (Nat.pow_pos (htOf P E₀))) P E₀) (tOf P E₀ ^ 2)) :
    ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀) :=
  fun P E₀ => firstCall (htOf P E₀) (hends P E₀) (hsup P E₀)

/-! ## Termination of the scheme -/

/-- **The synthesized strategy terminates**: every child of a nonempty instance is strictly smaller,
because the call's forest is nonempty and no child receives a forest edge. -/
theorem driverStrategy_strict
    (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀))
    (hnoloop : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ≠ G.dst e) :
    Strategy.Strict (driverStrategy DR) := by
  intro P E₀ hne i
  obtain ⟨f, hf⟩ := (DR P E₀).F_nonempty hne (hnoloop P E₀)
  have h := (DR P E₀).kidE_card_lt hf (finProdFinEquiv.symm i)
  change ((CallOut.reindex finProdFinEquiv (DR P E₀).roundData.toCall).kidE i).card < E₀.card
  exact h

/-- **The leaf-aware driver strategy**: the synthesized rounds on nonempty instances, the childless
call on the empty one.  `driverStrategy`'s call is `RoundData`-shaped and keeps its `t² · 1` children
even at `E₀ = ∅`; this is the paper's base case, and it agrees with `driverStrategy` elsewhere
(`driverStrategyLeaf_eq`). -/
noncomputable def driverStrategyLeaf
    (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀)) : Strategy G :=
  fun P E₀ =>
    if h : E₀ = ∅ then ⟨0, Strategy.leafCall (G := G) P⟩ else driverStrategy DR P E₀

theorem driverStrategyLeaf_wf
    (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀)) :
    Strategy.Wf (driverStrategyLeaf DR) := by
  intro P E₀
  unfold driverStrategyLeaf
  by_cases h : E₀ = ∅
  · subst h
    rw [dite_eq_left rfl]
    exact ⟨rfl, rfl⟩
  · rw [dite_eq_right h]
    exact Strategy.ofRoundDataT_wf tOf (driverRoundData DR) P E₀

theorem driverStrategyLeaf_strict
    (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀))
    (hnoloop : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ≠ G.dst e) :
    Strategy.Strict (driverStrategyLeaf DR) := by
  intro P E₀ hne i
  revert i
  unfold driverStrategyLeaf
  rw [dite_eq_right (Finset.ne_empty_iff_nonempty.mpr hne)]
  intro i
  exact driverStrategy_strict DR hnoloop P E₀ hne i

theorem driverStrategyLeaf_leaf
    (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀)) :
    Strategy.Leaf (driverStrategyLeaf DR) := by
  intro P
  unfold driverStrategyLeaf
  rw [dite_eq_left rfl]

/-- The leaf-aware variant is the synthesized strategy off the empty instance. -/
theorem driverStrategyLeaf_eq
    (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀))
    (P : Finset V) (E₀ : Finset E) (h : E₀ ≠ ∅) :
    driverStrategyLeaf DR P E₀ = driverStrategy DR P E₀ := by
  unfold driverStrategyLeaf
  rw [dite_eq_right h]

/-- **Termination, packaged**: well-formed, strictly decreasing, and childless at `E₀ = ∅`. -/
theorem driverScheme_terminates
    (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀))
    (hnoloop : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ≠ G.dst e) :
    Strategy.Wf (driverStrategyLeaf DR) ∧ Strategy.Strict (driverStrategyLeaf DR) ∧
      Strategy.Leaf (driverStrategyLeaf DR) :=
  ⟨driverStrategyLeaf_wf DR, driverStrategyLeaf_strict DR hnoloop, driverStrategyLeaf_leaf DR⟩

/-- **The recursion stops**: every level beyond `|E₀|` is empty, so §3.6's level sums cover all
edges and not only those down to a chosen depth. -/
theorem driverScheme_chain_empty
    (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀))
    (hnoloop : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ≠ G.dst e)
    (P : Finset V) (E₀ : Finset E) (d : ℕ) (hd : E₀.card + 1 ≤ d) :
    (Level.chain P E₀ (driverStrategyLeaf DR) (driverStrategyLeaf_wf DR) d).insts = ∅ :=
  LevelChain.chain_insts_empty_of_le P E₀ _ (driverStrategyLeaf_wf DR)
    (driverStrategyLeaf_strict DR hnoloop) (driverStrategyLeaf_leaf DR) d hd

/-! ## The call of §3.3's schedule -/

/-- **The call of a §3.3 schedule.**  `schedToSlot` reads the pair index `ρ : E → [t]×[t]` as the
flat slot, and the history layer's `sched` inverts it exactly (`sched_ofSchedule`) — so the §3.5
evidence attached to a call of this kind speaks about the very `ρ` that Lemma 3.11 was proved for. -/
noncomputable def ofSchedule (ρ : Sched E t) (Pp : Finset V) (hP' : Pp ⊆ P)
    (hbudget : 4 * (Fintype.card (Fin (t ^ 2)) * Pp.card) ≤ P.card)
    (hends : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hsup : ∀ v : V, ∃ e ∈ (Finset.univ : Finset E), incident G v e ∧
      e ∉ preF (G := G) (scanOfSlot (schedToSlot ρ) P E₀) (t ^ 2)) :
    DriverCall G P E₀ t :=
  ofSlot (schedToSlot ρ) Pp hP' hbudget hends hsup

section Schedule

variable [Nonempty E]

/-- **The call built from `ρ` reads back `ρ`.**  This is the coherence that lets the §3.5 hypotheses
of `Evidence` (`hc`, the per-edge premise, `lost`) be stated about the schedule Lemma 3.11 produced. -/
theorem sched_ofSchedule (ρ : Sched E t) (Pp : Finset V) (hP' : Pp ⊆ P)
    (hbudget : 4 * (Fintype.card (Fin (t ^ 2)) * Pp.card) ≤ P.card)
    (hends : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hsup : ∀ v : V, ∃ e ∈ (Finset.univ : Finset E), incident G v e ∧
      e ∉ preF (G := G) (scanOfSlot (schedToSlot ρ) P E₀) (t ^ 2)) :
    (ofSchedule ρ Pp hP' hbudget hends hsup).sched = ρ := by
  funext e
  show (roundIdx t).symm (schedToSlot ρ e) = ρ e
  rw [Equiv.symm_apply_eq]
  simp [schedToSlot, roundIdx, Equiv.trans_apply]

end Schedule

end DriverCall

end DLMST