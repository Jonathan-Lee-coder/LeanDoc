import DLMST.CallFromRounds

/-!
# The first process-level identification: the level chain read off the rounds

`Rounds.lemma37_error` speaks about an abstract action table `act : ℕ → Fin t → Fin t → Pref`: at every
recursion level `j` it needs `act j b i` to be the preferred action of the tracked edge in the round-`i`
state, and it concludes that an unsupported root either is supported or has paid an error
`error (act j) (est j) (slot j)`.  In an actual run the table is not free data: `History` (Definition 3.8)
records, for every edge and every slot, the spoke vector, the forest and the true preferred action, and
`History.Consistent` says the record is `actOf`-of-the-state.

This file *identifies* the abstract table with the history's record, so that the per-level hypotheses of
Lemma 3.7 become statements about the rounds a real run performs:

* `ProcChain` — the level chain of the tracked edge (`Rounds.Lev`) together with, per level, its assigned
  slot `(b, r)` in that level's call and the round-level facts the process supplies: the edge's true
  action at its assigned round is `project` (that is why it is passed to the child), the spokes are frozen
  inside the block `b`, the child's returned forest is inside every later round's forest of that block,
  the child's forest is inside the level's returned forest, and on return the child's forest already
  connects the ends at `max{w(e), p(e)}` (Claim 3.6 — `claim_3_6` proves it from the paper's hypotheses).
* `ProcChain.hpref` / `ProcChain.haction` — `Consistent` plus frozen spokes turn the level's true action
  row into `actOf G σ (H.forest b i) e`, and the process's decision to project the edge gives
  `¬ prefFind` at the assigned round: the hypotheses `hact` and `hpref` of `lemma37_project_error` are
  *derived* here, not assumed.
* `ProcChain.level_error` / `ProcChain.errorOr_unsupp` — the level step in the direction the count
  consumes: if the level's returned forest does not support the edge and the child's does, then the
  assigned slot is an error — `H.badFor` (a bad round) or a wrong estimate, both in the history's own
  vocabulary.
* `ProcChain.lemma37_error_proc` — the whole chain: an unsupported root forces an error at *some* level's
  assigned slot.  Level `j > 0`'s slot lives in the child call's schedule, which is the honest content of
  "an unsupported edge can be charged to an error"; §3.5 counts each call's errors in that call's own
  schedule (`RoundData.card_U_le_number_bound`, `EstimateBound.card_mis_le`).  The estimate is one
  predicted action per **edge** (`est : ℕ → E → Pref`), the coordinate type Claim 3.12 counts; level `j`
  reads it at the tracked edge, `est j (lev j).e`, which `Rounds.error` receives as the constant vector
  `fun _ => est j (lev j).e`.
* `ProcChain.errOf_or_unsupp_child` / `ProcChain.errOf_of_supp_child` / `ProcChain.unSupp_errOf` — the
  per-edge premise at the *root* call in the forms the count needs: either the root slot is an error, or
  the projection is unsupported at depth one; when the projection is supported there, the root slot is an
  error outright.  `unSupp_errOf` packages that for a whole schedule `ρ` as
  `∀ e, ¬supported G F₀ e → H.errOf est e (ρ e)` — the per-edge hypothesis of
  `CallOut.RoundData.card_U_le_number_bound` with `F₀ = D.F`.
-/

namespace DLMST

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
variable {G : WGraph V E} {t : ℕ}

/-- **The level chain of one edge, as the rounds deliver it.**  `lev j` is the projection living at
recursion level `j`; `slot j` is the round it was assigned in *that level's* call.  The fields are exactly
the paper's per-level facts: the assigned round prefers `project`, the spokes are frozen in its block, the
child's returned forest has been incorporated from the next round on, it is inside the level's returned
forest, and Claim 3.6's own hypotheses — the child call is an MSF of its instance, the spokes are
incident edges inside that instance, and the lifted portal path exists — from which the return
connection is *derived* (`ProcChain.conn`). -/
structure ProcChain (G : WGraph V E) (H : History V E t) (lev : ℕ → Lev E) where
  /-- the round assigned to the tracked edge in this level's call -/
  slot : ℕ → Fin t × Fin t
  /-- the recorded action vectors really are the preferred actions of the round states -/
  hcons : H.Consistent (G := G)
  /-- the true action at the assigned round is `project`: the edge is passed to the child -/
  hproj : ∀ j, H.pref (lev j).e (slot j).1 (slot j).2 = Pref.project
  /-- spokes are frozen inside a block (§3.1's `(σ_i, F_i)` with `σ` fixed over the block) -/
  hfroz : ∀ j i, H.spoke (slot j).1 i = H.spoke (slot j).1 (slot j).2
  /-- "at the end of that round the edge returns from the recursive call and is incorporated into the
  forest": every later round of the block starts from a forest containing the child's -/
  hret : ∀ j i, ((slot j).2.val + 1 : ℕ) ≤ i.val →
    (lev (j + 1)).F ⊆ H.forest (slot j).1 i
  /-- the child's returned forest sits inside the forest this level returns -/
  hsub : ∀ j, (lev (j + 1)).F ⊆ (lev j).F
  /-- the child call's instance: the edge set its MSF call was run on -/
  S : ℕ → Finset E
  /-- the lifted child path Claim 3.6 reads back -/
  es : ℕ → List E
  /-- the child's returned forest is an MSF of its own instance (the child call is correct) -/
  hmsf : ∀ j, IsMSFOf G (S j) (lev (j + 1)).F
  /-- spokes are incident edges (the process picks them at their own vertex) -/
  hspoke : ∀ j x, incident G x (H.spoke (slot j).1 (slot j).2 x)
  /-- Claim 3.6's hypothesis: the child supports the projection on the level's edge — a child path
  between the two portals, with all its edges and both spokes inside the child's instance and no
  heavier than `w(e)` -/
  hlift : ∀ j, LiftsLe G (H.spoke (slot j).1 (slot j).2) (S j) (G.weight (lev j).e)
    (portal G (H.spoke (slot j).1 (slot j).2) (G.src (lev j).e)) (es j)
    (portal G (H.spoke (slot j).1 (slot j).2) (G.dst (lev j).e))
  /-- the spokes used here are part of the child's instance -/
  hσS : ∀ j x, H.spoke (slot j).1 (slot j).2 x ∈ S j

namespace ProcChain

variable {H : History V E t} {lev : ℕ → Lev E}

/-- **Claim 3.6, applied inside the chain.**  The child call's own data — an MSF of its instance, incident
spokes inside that instance, and the lifted portal path — give the return connection, so the `Conn` used
by Lemma 3.7 is *derived* rather than assumed.  (The conclusion is unconditional in the child's support
of `Lev.supp`; the earlier `hconn` field demanded it only because that was the use site.) -/
theorem conn (C : ProcChain (G := G) H lev) (j : ℕ) :
    Conn G (belowLe G ((lev (j + 1)).F)
        (max (G.weight (lev j).e) (pE G (H.spoke (C.slot j).1 (C.slot j).2) (lev j).e)))
      (G.src (lev j).e) (G.dst (lev j).e) :=
  claim_3_6 (C.hmsf j) (C.hspoke j) (C.hlift j) (C.hσS j)

/-- **`hpref` of Lemma 3.7, derived.**  The process projects the edge at its assigned round; consistency
says the recorded action there is `actOf` of the state; hence the preferred action is `project`, i.e. the
edge is *not* already joined below `p(e)`. -/
theorem hpref (C : ProcChain (G := G) H lev) (j : ℕ) :
    ¬ prefFind G (H.spoke (C.slot j).1 (C.slot j).2) (H.forest (C.slot j).1 (C.slot j).2) (lev j).e := by
  have h : actOf G (H.spoke (C.slot j).1 (C.slot j).2) (H.forest (C.slot j).1 (C.slot j).2) (lev j).e
      = Pref.project :=
    (C.hcons (lev j).e (C.slot j).1 (C.slot j).2).symm.trans (C.hproj j)
  intro hf
  rw [actOf_find hf] at h
  exact Pref.noConfusion h

/-- **`hact` of Lemma 3.7, derived.**  On the assigned block the whole action row of the tracked edge is
`actOf` applied to the block's frozen spoke vector and the round's forest. -/
theorem haction (C : ProcChain (G := G) H lev) (j : ℕ) :
    ∀ i, H.pref (lev j).e (C.slot j).1 i
      = actOf G (H.spoke (C.slot j).1 (C.slot j).2) (H.forest (C.slot j).1 i) (lev j).e := by
  intro i
  rw [C.hcons (lev j).e (C.slot j).1 i, C.hfroz j i]

/-- **The per-level identification.**  From the round data, `lemma37_project_error` fires: if the level's
returned forest fails to support the edge while the child's supports it, then the assigned slot is an
error.  This replaces Lemma 3.7's abstract `act j` by the history's own entries. -/
theorem level_error (C : ProcChain (G := G) H lev) (est : ℕ → E → Pref) {j : ℕ}
    (hchild : Lev.supp G (lev (j + 1))) (hnot : ¬ Lev.supp G (lev j)) :
    error (H.pref (lev j).e) (fun _ => est j (lev j).e) (C.slot j) :=
  lemma37_project_error (F₁ := (lev j).F) (Fre := (lev (j + 1)).F)
    (σ := H.spoke (C.slot j).1 (C.slot j).2) (F := H.forest (C.slot j).1)
    (e := (lev j).e) (b := (C.slot j).1) (r := (C.slot j).2)
    (H.pref (lev j).e) (fun _ => est j (lev j).e) (C.haction j) (C.hpref j) (C.hret j) (C.hsub j)
    (C.conn j) hnot

/-- The same step with `error` unfolded into the two cases §3.5 counts: a round that is bad for the edge,
or an estimate that differs from its true preferred action.  The estimate is one action per edge
(`est j : E → Pref`), so `est j (lev j).e` is the predicted action of the tracked edge at this level. -/
theorem errorOr_unsupp (C : ProcChain (G := G) H lev) (est : ℕ → E → Pref) {j : ℕ}
    (hchild : Lev.supp G (lev (j + 1))) (hnot : ¬ Lev.supp G (lev j)) :
    H.badFor (lev j).e (C.slot j) ∨
      est j (lev j).e ≠ H.pref (lev j).e (C.slot j).1 (C.slot j).2 := by
  simpa [error, History.badFor] using C.level_error est hchild hnot

/-- The step in the shape `lemma37_error` consumes. -/
theorem supp_or_error (C : ProcChain (G := G) H lev) (est : ℕ → E → Pref) (j : ℕ)
    (hchild : Lev.supp G (lev (j + 1))) :
    Lev.supp G (lev j) ∨ error (H.pref (lev j).e) (fun _ => est j (lev j).e) (C.slot j) := by
  by_cases h : Lev.supp G (lev j)
  · exact Or.inl h
  · exact Or.inr (C.level_error est hchild h)

/-- **Lemma 3.7's second sentence, read off the process.**  An edge rejected at this level — its
assigned-round action estimated as `project` while the level's spokes make `p(e) > w(e)` — pays an
error at that slot: were the estimate right, the child's return would already join the ends below
`p(e)` in every later round of the block (`hret` + Claim 3.6), so those rounds prefer `find` and the
assigned round is bad. -/
theorem rejected_error (C : ProcChain (G := G) H lev) (est : ℕ → E → Pref) {j : ℕ}
    (hchild : Lev.supp G (lev (j + 1))) (hest : est j (lev j).e = Pref.project)
    (hlt : G.weight (lev j).e < pE G (H.spoke (C.slot j).1 (C.slot j).2) (lev j).e) :
    error (H.pref (lev j).e) (fun _ => est j (lev j).e) (C.slot j) := by
  refine lemma37_rejected_error (act := H.pref (lev j).e) (est := fun _ => est j (lev j).e)
    hest (fun i hi => ?_)
  rw [C.haction j i]
  refine actOf_find (Or.inr (Or.inr (Or.inr ?_)))
  have hc := C.conn j
  rw [max_eq_right hlt.le] at hc
  exact hc.mono (belowLe_subset (C.hret j i hi) _)

/-- **Lemma 3.7 along the process's level chain.**  Every level of `C` is a real call with its own
schedule; if the deepest level supports the tracked projection and the root's forest does not, then some
level's assigned slot is an error — recorded as `H.badFor` or as a wrong estimate against the history's
true preference. -/
theorem lemma37_error_proc (C : ProcChain (G := G) H lev)
    (est : ℕ → E → Pref) {d : ℕ} (hfind : ∀ j, d ≤ j → Lev.supp G (lev j)) :
    Lev.supp G (lev 0) ∨ ∃ j, j < d ∧
      error (H.pref (lev j).e) (fun _ => est j (lev j).e) (C.slot j) :=
  lemma37_error (act := fun j => H.pref (lev j).e) (est := fun j => fun _ => est j (lev j).e)
    (slot := C.slot) hfind (fun j _ hchild => C.supp_or_error est j hchild)

/-- **Lemma 3.7 in summation-ready form.**  If the tracked projections are supported from depth `d` on
but the level-`0` edge is not, some level `j < d` pays an error at its own slot — for the edge tracked
at that level.  This per-level charge is what `CallOut.RoundData.card_U_le_sum_levels` sums over the
levels of a chain. -/
theorem exists_level_error (C : ProcChain (G := G) H lev) (est : ℕ → E → Pref) {d : ℕ}
    (hfind : ∀ j, d ≤ j → Lev.supp G (lev j)) (hnot : ¬ Lev.supp G (lev 0)) :
    ∃ j, j < d ∧ (H.badFor (lev j).e (C.slot j) ∨
      est j (lev j).e ≠ H.pref (lev j).e (C.slot j).1 (C.slot j).2) := by
  rcases C.lemma37_error_proc est hfind with hsupp | ⟨j, hj, herr⟩
  · exact absurd hsupp hnot
  · exact ⟨j, hj, by simpa [error, History.badFor] using herr⟩

/-- **The root-call form, honest about depth.**  If the root forest does not support the edge, then either
the edge's own assigned slot at the root is an error, or its projection is already unsupported at depth
one (so the error, if any, is paid in the child's schedule). -/
theorem errOf_or_unsupp_child (C : ProcChain (G := G) H lev) (est : ℕ → E → Pref)
    {F₀ : Finset E} {e : E} {ρ : Fin t × Fin t} (hlev0 : lev 0 = ⟨e, F₀⟩) (hslot0 : C.slot 0 = ρ)
    (hnot : ¬ supported G F₀ e) :
    H.errOf (est 0) e ρ ∨ ¬ Lev.supp G (lev 1) := by
  have hnot' : ¬ Lev.supp G (lev 0) := by
    rw [hlev0]
    exact hnot
  by_cases hc : Lev.supp G (lev 1)
  · left
    have h := C.errorOr_unsupp est hc hnot'
    rw [hlev0] at h
    rw [hslot0] at h
    simpa [History.errOf] using h
  · exact Or.inr hc

/-- **The per-edge premise at the root call.**  When the projection is supported at depth one, the root
slot is an error outright: this is the per-edge hypothesis of `card_U_le_number_bound`, derived from the
rounds rather than assumed. -/
theorem errOf_of_supp_child (C : ProcChain (G := G) H lev) (est : ℕ → E → Pref)
    {F₀ : Finset E} {e : E} {ρ : Fin t × Fin t} (hlev0 : lev 0 = ⟨e, F₀⟩) (hslot0 : C.slot 0 = ρ)
    (hchild : Lev.supp G (lev 1)) (hnot : ¬ supported G F₀ e) :
    H.errOf (est 0) e ρ := by
  have hnot' : ¬ Lev.supp G (lev 0) := by
    rw [hlev0]
    exact hnot
  have h := C.errorOr_unsupp est hchild hnot'
  rw [hlev0] at h
  rw [hslot0] at h
  simpa [History.errOf] using h

/-- **The rejected-edge half at the root call.**  An edge rejected at its own assigned root round —
the estimate says `project` and `p(e) > w(e)` — is an error there outright, no support hypothesis. -/
theorem errOf_of_rejected_root (C : ProcChain (G := G) H lev) (est : ℕ → E → Pref)
    {F₀ : Finset E} {e : E} {ρ : Fin t × Fin t} (hlev0 : lev 0 = ⟨e, F₀⟩) (hslot0 : C.slot 0 = ρ)
    (hchild : Lev.supp G (lev 1)) (hest : est 0 e = Pref.project)
    (hlt : G.weight e < pE G (H.spoke ρ.1 ρ.2) e) :
    H.errOf (est 0) e ρ := by
  have hlt' : G.weight (lev 0).e < pE G (H.spoke (C.slot 0).1 (C.slot 0).2) (lev 0).e := by
    rw [hlev0, hslot0]
    exact hlt
  have hest' : est 0 (lev 0).e = Pref.project := by
    rw [hlev0]
    exact hest
  have h := C.rejected_error est hchild hest' hlt'
  rw [hlev0] at h
  rw [hslot0] at h
  simpa [error, History.errOf, History.badFor] using h

/-- **The count's per-edge hypothesis, from the process.**  A level chain for every edge of the call,
each terminating at a supported depth-one projection and each starting with the level-0 slot `ρ e`,
yields `∀ e, ¬supported G F₀ e → H.errOf est e (ρ e)` — the hypothesis of
`RoundData.card_U_le_number_bound` with `F₀ = D.F`. -/
theorem unSupp_errOf (ρ : E → Fin t × Fin t) (est : E → Pref) (lev : E → ℕ → Lev E)
    (C : ∀ e, ProcChain (G := G) H (lev e)) {F₀ : Finset E}
    (h0e : ∀ e, (lev e 0).e = e) (h0F : ∀ e, (lev e 0).F = F₀)
    (hslot : ∀ e, (C e).slot 0 = ρ e) (hchild : ∀ e, Lev.supp G (lev e 1)) :
    ∀ e, ¬ supported G F₀ e → H.errOf est e (ρ e) := by
  intro e hnot
  have hnot' : ¬ Lev.supp G (lev e 0) := by
    show ¬ supported G (lev e 0).F (lev e 0).e
    rw [h0F, h0e]
    exact hnot
  have h := (C e).errorOr_unsupp (fun _ => est) (hchild e) hnot'
  rw [h0e] at h
  rw [hslot e] at h
  simpa [History.errOf] using h

/-- **The instance bound with the per-edge premise no longer assumed.**  `card_U_le_number_bound`
consumes `∀ e ∈ E₀, ¬supported G D.F e → H.errOf est e (ρ e)`; `unSupp_errOf` produces it from one
level chain per edge, each starting at the call's forest `D.F` and terminating in a supported
depth-one projection.  With Lemma 3.11's `lost` bound and §3.5's per-round mis-estimate allowances as
the only remaining inputs, §3.3's instance error premise
`|U(F)| ≤ 10t²√(mn) + 4m/t` follows from the rounds.

The hypothesis `hchild` is the one place the chain does *not* settle the root: an edge whose
projection is unsupported at depth one is not charged at this call's slot but in the child call's
(`errOf_or_unsupp_child`'s second disjunct), which is the summation over calls that
`Procedure`/`CallPart` account for.  For the edges it covers, the root slot is proved to be an error,
so nothing per-edge is assumed here. -/
theorem card_U_le_number_bound_of_chains {P : Finset V} {E₀ : Finset E} {ι : Type*}
    [Fintype ι] [DecidableEq ι] {t s : ℕ} (D : CallOut.RoundData G P E₀ ι t)
    (H : History V E s) (est : E → Pref) (ρ : E → Fin s × Fin s)
    (lev : E → ℕ → Lev E) (C : ∀ e, ProcChain G H (lev e)) (mOf : Fin s × Fin s → ℕ)
    {m n : ℝ} (ht : 0 < t) (hm : 0 ≤ m) (hn : 0 ≤ n) (hmE : (Fintype.card E : ℝ) ≤ m)
    (h0e : ∀ e, (lev e 0).e = e) (h0F : ∀ e, (lev e 0).F = D.F)
    (hslot : ∀ e, (C e).slot 0 = ρ e) (hchild : ∀ e, Lev.supp G (lev e 1))
    (hlost : (H.lost ρ : ℝ) * Real.log 2 ≤
      (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 * Real.sqrt (m * n) + 2 * m / (t : ℝ))
    (hper : ∀ r : Fin s × Fin s,
      ((Finset.univ.filter fun e =>
        est e ≠ H.pref e (ρ e).1 (ρ e).2 ∧ ρ e = r).card : ℝ) ≤
        (mOf r : ℝ) / (t : ℝ))
    (hsum : (∑ r, mOf r) ≤ Fintype.card E) :
    (D.U.card : ℝ) ≤ 10 * (t : ℝ) ^ 2 * Real.sqrt (m * n) + 4 * m / (t : ℝ) :=
  D.card_U_le_number_bound H est ρ mOf ht hm hn hmE
    (fun e _ hns => unSupp_errOf ρ est lev C h0e h0F hslot hchild e hns) hlost hper hsum

/-- **The per-call count without the `hchild` assumption.**  Dropping "every depth-one projection is
supported" costs exactly the edges whose projection is not: those are the edges the paper's per-call
summation charges in the *child* call (`errOf_or_unsupp_child`'s second disjunct).  Machine form of
the honest per-call statement `|U(F)| ≤ lost + #mis + #(E₀ with unsupported depth-one projection)`.
On the first two sets the root slot is proved to be an error, so no per-edge hypothesis is assumed
anywhere; the third set is carried forward as-is and is what the child calls' own `|U|` accounts for. -/
theorem card_U_le_lost_add_mis_add_child_fail {P : Finset V} {E₀ : Finset E} {ι : Type*}
    [Fintype ι] [DecidableEq ι] {t s : ℕ} (D : CallOut.RoundData G P E₀ ι t)
    (H : History V E s) (lev : E → ℕ → Lev E) [DecidablePred fun e => Lev.supp G (lev e 1)]
    (est : E → Pref) (ρ : E → Fin s × Fin s) (C : ∀ e, ProcChain G H (lev e))
    (h0e : ∀ e, (lev e 0).e = e) (h0F : ∀ e, (lev e 0).F = D.F)
    (hslot : ∀ e, (C e).slot 0 = ρ e) :
    D.U.card ≤ H.lost ρ +
      (E₀.filter fun e => est e ≠ H.pref e (ρ e).1 (ρ e).2).card +
      (E₀.filter fun e => ¬ Lev.supp G (lev e 1)).card := by
  classical
  have hP₀ : ∀ e ∈ E₀, Lev.supp G (lev e 1) → ¬ supported G D.F e → H.errOf est e (ρ e) := by
    intro e hE hsupp hns
    have hnot' : ¬ Lev.supp G (lev e 0) := by
      show ¬ supported G (lev e 0).F (lev e 0).e
      rw [h0F, h0e]
      exact hns
    have h := (C e).errorOr_unsupp (fun _ => est) hsupp hnot'
    rw [h0e] at h
    rw [hslot e] at h
    simpa [History.errOf] using h
  set P₁ : Finset E := E₀.filter fun e => Lev.supp G (lev e 1) with hP₁
  set P₂ : Finset E := E₀.filter fun e => ¬ Lev.supp G (lev e 1) with hP₂
  have hUsub : D.U ⊆ E₀ := Finset.inter_subset_right
  have hUP : D.U = (D.U ∩ P₁) ∪ (D.U ∩ P₂) := by
    ext e
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro he
      by_cases hc : Lev.supp G (lev e 1)
      · exact Or.inl ⟨he, by rw [hP₁]; exact Finset.mem_filter.mpr ⟨hUsub he, hc⟩⟩
      · exact Or.inr ⟨he, by rw [hP₂]; exact Finset.mem_filter.mpr ⟨hUsub he, hc⟩⟩
    · rintro (⟨he, -⟩ | ⟨he, -⟩) <;> exact he
  have hdisj : Disjoint (D.U ∩ P₁) (D.U ∩ P₂) := by
    refine Finset.disjoint_left.mpr ?_
    intro e he₁ he₂
    have hP : e ∈ P₂ := (Finset.mem_inter.mp he₂).2
    rw [hP₂] at hP
    have hsupp : Lev.supp G (lev e 1) := (Finset.mem_filter.mp (Finset.mem_inter.mp he₁).2).2
    exact (Finset.mem_filter.mp hP).2 hsupp
  have hUP₁ : (D.U ∩ P₁).card ≤
      H.lost ρ + (E₀.filter fun e => est e ≠ H.pref e (ρ e).1 (ρ e).2).card := by
    have hsub₁ : D.U ∩ P₁ ⊆ (P₁.filter fun e => H.badFor e (ρ e)) ∪
        (P₁.filter fun e => est e ≠ H.pref e (ρ e).1 (ρ e).2) := by
      intro e he
      obtain ⟨hU, hP⟩ := Finset.mem_inter.mp he
      have hns : ¬ supported G D.F e := mem_unsupp.mp (Finset.mem_inter.mp hU).1
      have hsupp : Lev.supp G (lev e 1) := (Finset.mem_filter.mp hP).2
      have hE : e ∈ E₀ := (Finset.mem_filter.mp hP).1
      rcases hP₀ e hE hsupp hns with hb | hm
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hP, hb⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hP, hm⟩)
    refine le_trans (Finset.card_le_card hsub₁) ?_
    refine le_trans (Finset.card_union_le _ _) ?_
    refine Nat.add_le_add ?_ ?_
    · rw [History.lost_def]
      exact Finset.card_le_card (fun e he =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2⟩)
    · exact Finset.card_le_card (fun e he => by
        obtain ⟨hP, hm⟩ := Finset.mem_filter.mp he
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hP).1, hm⟩)
  have hUP₂ : (D.U ∩ P₂).card ≤ P₂.card := Finset.card_le_card Finset.inter_subset_right
  calc D.U.card = ((D.U ∩ P₁) ∪ (D.U ∩ P₂)).card := congrArg Finset.card hUP
    _ = (D.U ∩ P₁).card + (D.U ∩ P₂).card := Finset.card_union_of_disjoint hdisj
    _ ≤ (H.lost ρ +
          (E₀.filter fun e => est e ≠ H.pref e (ρ e).1 (ρ e).2).card) + P₂.card :=
        Nat.add_le_add hUP₁ hUP₂
    _ = H.lost ρ +
          (E₀.filter fun e => est e ≠ H.pref e (ρ e).1 (ρ e).2).card +
          (E₀.filter fun e => ¬ Lev.supp G (lev e 1)).card := by
        rw [hP₂]

/-- **The instance error premise from the process in full.**  Both halves of §3.3's budget are now
produced: the per-edge premise `¬supported → errOf` comes from the level chains (`unSupp_errOf`), and
the mis-estimate count `#mis ≤ |E|/t` comes from §3.5's sampling (`card_mis_le_of_claim312`) through
`card_U_le_number_bound_of_sampling`.  The only remaining inputs are Lemma 3.11's `lost` bound, one
level chain per edge ending in a supported depth-one projection, and the driver's sampling facts
(`A`, `htruth`, `hest`, and the agreement on the queried sample `S`). -/
theorem card_U_le_number_bound_of_sampling_chains {P : Finset V} {E₀ : Finset E} {ι : Type*}
    [Fintype ι] [DecidableEq ι] {t s : ℕ} (D : CallOut.RoundData G P E₀ ι t)
    (H : History V E s) (est : E → Pref) (ρ : E → Fin s × Fin s)
    (lev : E → ℕ → Lev E) (C : ∀ e, ProcChain G H (lev e))
    {m n : ℝ} (ht : 2 ≤ t) (hm : 0 ≤ m)
    (hn : 0 ≤ n) (hmE : (Fintype.card E : ℝ) ≤ m)
    (h0e : ∀ e, (lev e 0).e = e) (h0F : ∀ e, (lev e 0).F = D.F)
    (hslot : ∀ e, (C e).slot 0 = ρ e) (hchild : ∀ e, Lev.supp G (lev e 1))
    (hlost : (H.lost ρ : ℝ) * Real.log 2 ≤
      (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 * Real.sqrt (m * n) + 2 * m / (t : ℝ))
    (A : ∀ r : Fin s × Fin s, Finset ({e : E // ρ e = r} → Pref))
    (htruth : ∀ r : Fin s × Fin s,
      (fun x : {e : E // ρ e = r} => H.pref x.1 (ρ x.1).1 (ρ x.1).2) ∈ A r)
    (hest : ∀ r : Fin s × Fin s, (fun x : {e : E // ρ e = r} => est x.1) ∈ A r) :
    ∃ S : ∀ r : Fin s × Fin s, Finset {e : E // ρ e = r},
      (∀ r, (S r).card ≤ 2 * t * (Nat.ceil (Real.log ((A r).card : ℝ)) + 1)) ∧
      ((∀ r (x : {e : E // ρ e = r}), x ∈ S r → est x.1 = H.pref x.1 r.1 r.2) →
        (D.U.card : ℝ) ≤ 10 * (t : ℝ) ^ 2 * Real.sqrt (m * n) + 4 * m / (t : ℝ)) :=
  D.card_U_le_number_bound_of_sampling H est ρ ht hm hn hmE
    (fun e _ hns => unSupp_errOf ρ est lev C h0e h0F hslot hchild e hns) hlost A htruth hest

end ProcChain


end DLMST
