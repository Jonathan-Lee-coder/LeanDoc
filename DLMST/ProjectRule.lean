import DLMST.OneStep

/-!
# The projection rule: unsupported + light spokes + distinct portals ⇒ `project`

`StepData.hproj` — "the edge's preferred action at its assigned round is `project`" — is the one field
of the single-level interface that the state decides rather than the record delivers.  This file derives
it from the preference rules of §3.1.  `prefFind` has four disjuncts; for an edge `e` whose two spokes

* are incident (the process picks spokes at their own vertex),
* are no heavier than `e` (Claim 3.5's `admOut_spokes`), and
* do not meet at a common portal (Lemma 3.2's dichotomy),

the first three fail outright, and the fourth — "`F≤p(e)` already joins the ends" — would make `e`
supported, since `p(e) ≤ w(e)`.  So an unsupported edge **is** projected at that state; no estimate, no
schedule freedom.

* `not_prefFind_of_unsupp` — the state-level rule.
* `DriverCall.pref_project_of_unsupp` — the same for the driver's own record at `e`'s slot.
* `StepData.ofDriver` — builds the level data with the interface-supplied fields (`hcons`, `hfroz` from
  block-frozen batches, `hspoke`) filled automatically.
* `DriverCall.badFor_of_stepObligations` / `card_U_le_number_bound_of_stepObligations` — per-edge
  obligations (one level: `hproj`, `hret`, `hsub`, `S`, `es`, `hmsf`, `hlift`, `hσS`) ⇒ `badFor`, and
  §3.5's per-call bound.
-/

namespace DLMST

open Classical

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

/-- **The projection rule.**  If both spokes of `e` are incident, meet at distinct portals, and are no
heavier than `e`, then an unsupported edge does not take `find`: the fourth clause of `prefFind` would
already support it. -/
theorem not_prefFind_of_unsupp {σ : V → E} {F : Finset E} {e : E}
    (hsp : ∀ x, incident G x (σ x))
    (hne : portal G σ (G.src e) ≠ portal G σ (G.dst e))
    (hwu : G.weight (σ (G.src e)) ≤ G.weight e)
    (hwv : G.weight (σ (G.dst e)) ≤ G.weight e)
    (hnot : ¬ supported G F e) : ¬ prefFind G σ F e := by
  intro h
  rcases h with h1 | h2 | h3 | h4
  · exact h1 (hsp _)
  · exact h2 (hsp _)
  · exact hne h3
  · exact hnot (Conn.mono (belowLe_mono (max_le hwu hwv)) h4)

/-- Support survives enlarging the forest. -/
theorem supported_mono {F F' : Finset E} (h : F ⊆ F') {e : E} (hs : supported G F e) :
    supported G F' e :=
  Conn.mono (fun _ hx => Finset.mem_filter.mpr
    ⟨h (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩) hs

namespace DriverCall

variable {P : Finset V} {E₀ : Finset E} {t : ℕ} [Nonempty E]

/-- **The record's action at `e`'s own slot is `project`, derived.**  Consistency turns the record into
`actOf` of the round state; the projection rule then applies to an unsupported edge. -/
theorem pref_project_of_unsupp (R : DriverCall G P E₀ t) {e : E}
    (hsp : ∀ x, incident G x (R.history.spoke (R.sched e).1 (R.sched e).2 x))
    (hne : portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.src e) ≠
      portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.dst e))
    (hwu : G.weight (R.history.spoke (R.sched e).1 (R.sched e).2 (G.src e)) ≤ G.weight e)
    (hwv : G.weight (R.history.spoke (R.sched e).1 (R.sched e).2 (G.dst e)) ≤ G.weight e)
    (hnot : ¬ supported G R.roundData.F e) :
    R.history.pref e (R.sched e).1 (R.sched e).2 = Pref.project := by
  have hround : ¬ supported G (R.history.forest (R.sched e).1 (R.sched e).2) e :=
    fun hs => hnot (supported_mono (forestUpTo_sub R.roundData _) hs)
  rw [R.history_consistent e (R.sched e).1 (R.sched e).2]
  exact actOf_project (not_prefFind_of_unsupp hsp hne hwu hwv hround)

/-- **A level's data with the interface-supplied fields filled in.**  `hcons`, `hfroz` (block-frozen
batches), and `hspoke` come from the driver call; the algorithmic obligations stay premises. -/
def StepData.ofDriver (R : DriverCall G P E₀ t) {e : E} {F F₁ : Finset E}
    (hBfroz : ∀ b i j, R.B b i = R.B b j)
    (hproj : R.history.pref e (R.sched e).1 (R.sched e).2 = Pref.project)
    (hret : ∀ i, (((R.sched e).2).val + 1 : ℕ) ≤ i.val →
      F₁ ⊆ R.history.forest (R.sched e).1 i)
    (hsub : F₁ ⊆ F)
    (S : Finset E) (es : List E)
    (hmsf : IsMSFOf G S F₁)
    (hlift : LiftsLe G (R.history.spoke (R.sched e).1 (R.sched e).2) S (G.weight e)
      (portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.src e)) es
      (portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.dst e)))
    (hσS : ∀ x, R.history.spoke (R.sched e).1 (R.sched e).2 x ∈ S) :
    StepData (G := G) R.history e F F₁ (R.sched e).1 (R.sched e).2 where
  hcons := R.history_consistent
  hproj := hproj
  hfroz := fun i => R.history_spoke_frozen hBfroz (R.sched e).1 i (R.sched e).2
  hret := hret
  hsub := hsub
  S := S
  es := es
  hmsf := hmsf
  hspoke := fun x => R.history_spoke_incident (R.sched e).1 (R.sched e).2 x
  hlift := hlift
  hσS := hσS

/-- **The per-edge sentence from one level's obligations.**  `hcons`／`hfroz`／`hspoke` are interface
facts; the premises are the algorithmic data of `e`'s own round. -/
theorem badFor_of_stepObligations (R : DriverCall G P E₀ t)
    (hBfroz : ∀ b i j, R.B b i = R.B b j) (F₁ : E → Finset E)
    (hproj : ∀ e ∈ E₀, R.history.pref e (R.sched e).1 (R.sched e).2 = Pref.project)
    (hret : ∀ e ∈ E₀, ∀ i, (((R.sched e).2).val + 1 : ℕ) ≤ i.val →
      F₁ e ⊆ R.history.forest (R.sched e).1 i)
    (hsub : ∀ e ∈ E₀, F₁ e ⊆ R.roundData.F)
    (S : E → Finset E) (es : E → List E)
    (hmsf : ∀ e ∈ E₀, IsMSFOf G (S e) (F₁ e))
    (hlift : ∀ e ∈ E₀, LiftsLe G (R.history.spoke (R.sched e).1 (R.sched e).2) (S e) (G.weight e)
      (portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.src e)) (es e)
      (portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.dst e)))
    (hσS : ∀ e ∈ E₀, ∀ x, R.history.spoke (R.sched e).1 (R.sched e).2 x ∈ S e) :
    ∀ e ∈ E₀, ¬ supported G R.roundData.F e → R.history.badFor e (R.sched e) :=
  fun e he hnot =>
    (StepData.ofDriver (F := R.roundData.F) (F₁ := F₁ e) R hBfroz (hproj e he) (hret e he)
      (hsub e he) (S e) (es e) (hmsf e he) (hlift e he) (hσS e he)).badFor hnot

/-- **`EvidenceOn` from one level's obligations per edge.** -/
noncomputable def evidenceOn_of_stepObligations (R : DriverCall G P E₀ t)
    (hBfroz : ∀ b i j, R.B b i = R.B b j) (F₁ : E → Finset E)
    (hproj : ∀ e ∈ E₀, R.history.pref e (R.sched e).1 (R.sched e).2 = Pref.project)
    (hret : ∀ e ∈ E₀, ∀ i, (((R.sched e).2).val + 1 : ℕ) ≤ i.val →
      F₁ e ⊆ R.history.forest (R.sched e).1 i)
    (hsub : ∀ e ∈ E₀, F₁ e ⊆ R.roundData.F)
    (S : E → Finset E) (es : E → List E)
    (hmsf : ∀ e ∈ E₀, IsMSFOf G (S e) (F₁ e))
    (hlift : ∀ e ∈ E₀, LiftsLe G (R.history.spoke (R.sched e).1 (R.sched e).2) (S e) (G.weight e)
      (portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.src e)) (es e)
      (portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.dst e)))
    (hσS : ∀ e ∈ E₀, ∀ x, R.history.spoke (R.sched e).1 (R.sched e).2 x ∈ S e)
    (e₀ : E) (hB : ∀ i j, R.B i j ⊆ E₀) (hP0 : 0 < P.card)
    (hgood : ∀ H : History V E t, LegalOn (G := G) P E₀ e₀ H →
      (H.lostOn E₀ R.sched : ℝ) * Real.log 2 ≤
        (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 *
            Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) + 2 * (E₀.card : ℝ) / (t : ℝ)) :
    EvidenceOn R :=
  evidenceOn_of_good_schedule_badFor R e₀ hB hP0 hgood
    (badFor_of_stepObligations R hBfroz F₁ hproj hret hsub S es hmsf hlift hσS)

/-- **§3.5's per-call bound from one level's obligations per edge.** -/
theorem card_U_le_number_bound_of_stepObligations (R : DriverCall G P E₀ t)
    (hBfroz : ∀ b i j, R.B b i = R.B b j) (F₁ : E → Finset E)
    (hproj : ∀ e ∈ E₀, R.history.pref e (R.sched e).1 (R.sched e).2 = Pref.project)
    (hret : ∀ e ∈ E₀, ∀ i, (((R.sched e).2).val + 1 : ℕ) ≤ i.val →
      F₁ e ⊆ R.history.forest (R.sched e).1 i)
    (hsub : ∀ e ∈ E₀, F₁ e ⊆ R.roundData.F)
    (S : E → Finset E) (es : E → List E)
    (hmsf : ∀ e ∈ E₀, IsMSFOf G (S e) (F₁ e))
    (hlift : ∀ e ∈ E₀, LiftsLe G (R.history.spoke (R.sched e).1 (R.sched e).2) (S e) (G.weight e)
      (portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.src e)) (es e)
      (portal G (R.history.spoke (R.sched e).1 (R.sched e).2) (G.dst e)))
    (hσS : ∀ e ∈ E₀, ∀ x, R.history.spoke (R.sched e).1 (R.sched e).2 x ∈ S e)
    (e₀ : E) (hB : ∀ i j, R.B i j ⊆ E₀) (hP0 : 0 < P.card) (ht : 2 ≤ t)
    (hgood : ∀ H : History V E t, LegalOn (G := G) P E₀ e₀ H →
      (H.lostOn E₀ R.sched : ℝ) * Real.log 2 ≤
        (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 *
            Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) + 2 * (E₀.card : ℝ) / (t : ℝ)) :
    ((R.roundData.toCall.U).card : ℝ) ≤
      10 * (t : ℝ) ^ 2 * Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) +
        4 * (E₀.card : ℝ) / (t : ℝ) :=
  card_U_le_number_bound_of_badFor R e₀ hB hP0 ht hgood
    (badFor_of_stepObligations R hBfroz F₁ hproj hret hsub S es hmsf hlift hσS)

end DriverCall

end DLMST