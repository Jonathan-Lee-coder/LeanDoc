import DLMST.ChainShape

/-!
# One level is enough: the step interface

`ProcChain` carries the whole chain `ℕ → Lev E`, and batch 123 showed that its `hproj : ∀ j` plus the
per-level MSF call force a nonempty child forest at every depth — an infinite, self-supporting object that
the paper's finite chain (project for `j < d`, then `hfind`) does not provide.  Reading the proof, though,
the per-edge work is a *single* level: `errorOr_unsupp` only reads the fields at index `j`.

This file replaces the chain by one level of data (`StepData`), and drops a premise that turns out to be
redundant.  `ProcChain.level_error` takes `hchild : Lev.supp G (lev (j+1))` but never uses it: the step's
`hconn` comes from `claim_3_6`, whose hypotheses `hmsf`／`hspoke`／`hlift`／`hσS` already say that the
child supports the projection (as a *lifted path*).  The paper's "if the child recursion supports the
edge" is the hypothesis `hlift`, not a separate support fact — so:

* `StepData` — the level's slot `(b, r)`, level forest `F`, child forest `F₁`, child instance `S`, lifted
  path `es`, and the level fields of `ProcChain` at that one level.  No `ℕ`-indexed object.
* `StepData.step_error` / `StepData.badFor` — unsupported level forest ⇒ the slot is an error; with the
  truth estimate the estimate disjunct vanishes, so the slot is a bad round.  **No support premise.**
* `ProcChain.stepData` — a chain still yields this data at every level.
* `DriverCall.badFor_of_stepsOn` — one `StepData` per instance edge ⇒ the per-edge sentence.
* `DriverCall.badFor_of_procChains_noChild` — the same for the chain route, recording that batch 122's
  `hchild` was redundant.
* `evidenceOn_of_steps`, `card_U_le_number_bound_of_steps` — §3.5's bound with only `2 ≤ t`, `hB`,
  `0 < |P|` and the good-schedule premise left.
-/

namespace DLMST

open Classical

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

/-- **One level of one edge's projection**: the edge `e` is processed in round `(b, r)` with forest `F`,
the child call returns `F₁` (an MSF of its instance `S`), and `es` lifts the child's portal path to
parent edges below `w(e)`.  This is `ProcChain`'s data at a single index. -/
structure StepData (G : WGraph V E) (H : History V E t) (e : E) (F F₁ : Finset E)
    (b : Fin t) (r : Fin t) where
  hcons : H.Consistent (G := G)
  hproj : H.pref e b r = Pref.project
  hfroz : ∀ i, H.spoke b i = H.spoke b r
  hret : ∀ i, ((r.val + 1 : ℕ) ≤ i.val) → F₁ ⊆ H.forest b i
  hsub : F₁ ⊆ F
  S : Finset E
  es : List E
  hmsf : IsMSFOf G S F₁
  hspoke : ∀ x, incident G x (H.spoke b r x)
  hlift : LiftsLe G (H.spoke b r) S (G.weight e)
    (portal G (H.spoke b r) (G.src e)) es (portal G (H.spoke b r) (G.dst e))
  hσS : ∀ x, H.spoke b r x ∈ S

namespace StepData

variable {t : ℕ} {H : History V E t} {e : E} {F F₁ : Finset E} {b r : Fin t}

/-- The recorded action at the slot is the preferred action of the round state. -/
theorem hpref (D : StepData (G := G) H e F F₁ b r) :
    ¬ prefFind G (H.spoke b r) (H.forest b r) e := by
  have h : actOf G (H.spoke b r) (H.forest b r) e = Pref.project :=
    (D.hcons e b r).symm.trans D.hproj
  intro hf
  rw [actOf_find hf] at h
  exact Pref.noConfusion h

/-- On the slot's block the whole action row of `e` is `actOf` of the frozen spoke vector. -/
theorem haction (D : StepData (G := G) H e F F₁ b r) :
    ∀ i, H.pref e b i = actOf G (H.spoke b r) (H.forest b i) e := by
  intro i
  rw [D.hcons e b i, D.hfroz i]

/-- Claim 3.6 inside the step: the child's data give the return connection. -/
theorem conn (D : StepData (G := G) H e F F₁ b r) :
    Conn G (belowLe G F₁ (max (G.weight e) (pE G (H.spoke b r) e))) (G.src e) (G.dst e) :=
  claim_3_6 D.hmsf D.hspoke D.hlift D.hσS

/-- **The per-level identification, single level.**  If the level's forest does not support `e`, the
assigned slot `(b, r)` is an error — no hypothesis on the child's support is needed. -/
theorem step_error (D : StepData (G := G) H e F F₁ b r) (est : E → Pref)
    (hnot : ¬ supported G F e) :
    error (H.pref e) (fun _ => est e) (b, r) :=
  lemma37_project_error (F₁ := F) (Fre := F₁) (σ := H.spoke b r) (F := H.forest b)
    (e := e) (b := b) (r := r) (H.pref e) (fun _ => est e)
    D.haction D.hpref D.hret D.hsub D.conn hnot

/-- **The slot is a bad round.**  With the truth estimate the estimate disjunct is `a ≠ a`, so the step
yields `badFor` outright — Lemma 3.7's conclusion, one level of data, no chain, no child-support premise. -/
theorem badFor (D : StepData (G := G) H e F F₁ b r) (hnot : ¬ supported G F e) :
    H.badFor e (b, r) := by
  rcases D.step_error (fun e' => H.pref e' b r) hnot with h | h
  · exact h
  · exact absurd rfl h

end StepData

namespace ProcChain

variable {t : ℕ} {H : History V E t} {lev : ℕ → Lev E}

/-- **A chain yields one level's data**, so `StepData` is the weaker interface. -/
def stepData (C : ProcChain (G := G) H lev) (j : ℕ) :
    StepData (G := G) H (lev j).e (lev j).F (lev (j + 1)).F (C.slot j).1 (C.slot j).2 where
  hcons := C.hcons
  hproj := C.hproj j
  hfroz := C.hfroz j
  hret := C.hret j
  hsub := C.hsub j
  S := C.S j
  es := C.es j
  hmsf := C.hmsf j
  hspoke := C.hspoke j
  hlift := C.hlift j
  hσS := C.hσS j

end ProcChain

namespace DriverCall

variable {P : Finset V} {E₀ : Finset E} {t : ℕ} [Nonempty E]

/-- **The per-edge sentence from one level of data per edge.**  For each `e ∈ E₀` a `StepData` at `e`'s
own scheduled round, with `R.roundData.F` as the level forest. -/
theorem badFor_of_stepsOn (R : DriverCall G P E₀ t) (F₁ : E → Finset E)
    (D : ∀ (e : E), e ∈ E₀ →
      StepData (G := G) R.history e R.roundData.F (F₁ e) (R.sched e).1 (R.sched e).2) :
    ∀ e ∈ E₀, ¬ supported G R.roundData.F e → R.history.badFor e (R.sched e) :=
  fun e he hnot => (D e he).badFor hnot

/-- **The chain route without `hchild`**: batch 122's premise is redundant, since the level step never
reads it (`StepData` has no such field). -/
theorem badFor_of_procChains_noChild (R : DriverCall G P E₀ t) (lev : E → ℕ → Lev E)
    (C : ∀ e, ProcChain (G := G) R.history (lev e))
    (h0e : ∀ e, (lev e 0).e = e) (h0F : ∀ e, (lev e 0).F = R.roundData.F)
    (hslot : ∀ e, (C e).slot 0 = R.sched e) :
    ∀ e ∈ E₀, ¬ supported G R.roundData.F e → R.history.badFor e (R.sched e) := by
  intro e he hnot
  have hnot' : ¬ supported G (lev e 0).F (lev e 0).e := by rw [h0F, h0e]; exact hnot
  have h := (C e).stepData 0 |>.badFor (F₁ := (lev e 1).F) hnot'
  rw [h0e] at h
  rw [hslot e] at h
  exact h

/-- **`EvidenceOn` from per-edge level data.** -/
noncomputable def evidenceOn_of_steps (R : DriverCall G P E₀ t) (F₁ : E → Finset E)
    (D : ∀ (e : E), e ∈ E₀ →
      StepData (G := G) R.history e R.roundData.F (F₁ e) (R.sched e).1 (R.sched e).2)
    (e₀ : E) (hB : ∀ i j, R.B i j ⊆ E₀) (hP0 : 0 < P.card)
    (hgood : ∀ H : History V E t, LegalOn (G := G) P E₀ e₀ H →
      (H.lostOn E₀ R.sched : ℝ) * Real.log 2 ≤
        (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 *
            Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) + 2 * (E₀.card : ℝ) / (t : ℝ)) :
    EvidenceOn R :=
  evidenceOn_of_good_schedule_badFor R e₀ hB hP0 hgood
    (badFor_of_stepsOn R F₁ D)

/-- **§3.5's per-call bound from per-edge level data.** -/
theorem card_U_le_number_bound_of_steps (R : DriverCall G P E₀ t) (F₁ : E → Finset E)
    (D : ∀ (e : E), e ∈ E₀ →
      StepData (G := G) R.history e R.roundData.F (F₁ e) (R.sched e).1 (R.sched e).2)
    (e₀ : E) (hB : ∀ i j, R.B i j ⊆ E₀) (hP0 : 0 < P.card) (ht : 2 ≤ t)
    (hgood : ∀ H : History V E t, LegalOn (G := G) P E₀ e₀ H →
      (H.lostOn E₀ R.sched : ℝ) * Real.log 2 ≤
        (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 *
            Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) + 2 * (E₀.card : ℝ) / (t : ℝ)) :
    ((R.roundData.toCall.U).card : ℝ) ≤
      10 * (t : ℝ) ^ 2 * Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) +
        4 * (E₀.card : ℝ) / (t : ℝ) :=
  card_U_le_number_bound_of_badFor R e₀ hB hP0 ht hgood
    (badFor_of_stepsOn R F₁ D)

end DriverCall

end DLMST