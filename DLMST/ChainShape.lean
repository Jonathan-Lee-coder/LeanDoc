import DLMST.ChainDriver

/-!
# The shape of a level chain: it never terminates

`ProcChain` (from `Rounds.lean`) indexes the levels of one edge's projection chain by `ℕ` and asks for
the projection step at *every* level (`hproj : ∀ j`), plus an MSF call and a lifted child path at every
level (`hmsf`, `hlift`, `hσS`).  The paper's own backward induction (`lemma37_error`) instead runs to a
*fixed depth* `d` and is handed `hfind`: past `d` the edge is never passed down again.  This file records
the difference as a theorem rather than a remark:

* `ProcChain.childF_nonempty` — in a graph without loops, **no level can have an empty child forest**:
  the child forest `(lev (j+1)).F` spans the level's declared set `S j`, the spoke `σ` of the level is
  in `S j`, and a non-loop spoke cannot be connected by `∅` (only `Conn.refl` lives there), so spanning
  would force its two ends equal.  Hence `ProcChain` is a chain of *perpetual* projection, not the
  paper's finite chain: an edge that stops being passed down cannot be represented.
* `not_chain_of_eventually_empty` — consequently any level chain whose child forests are eventually
  empty does not carry a `ProcChain` at all.

Downstream use stays sound (premises are premises), but the chain route of `ProcDriver.lean` /
`ChainDriver.lean` proves a *sufficient* certificate, not the paper's process; the faithful route needs
the per-call recursion.  The last two theorems are the driver-shaped end-to-end statement: `EvidenceOn`
and §3.5's numerical bound with only the algorithmic obligations left.
-/

namespace DLMST

open Classical

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

namespace ProcChain

variable {t : ℕ} {H : History V E t} {lev : ℕ → Lev E}

/-- **Every level has a nonempty child forest** (loop-free `G`). -/
theorem childF_nonempty (C : ProcChain (G := G) H lev)
    (hloop : ∀ f : E, G.src f ≠ G.dst f) (j : ℕ) : ((lev (j + 1)).F).Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  set σ : V → E := H.spoke (C.slot j).1 (C.slot j).2 with hσ
  have hspan := (C.hmsf j).1.2.2
  have hmem : σ (G.src (lev j).e) ∈ C.S j := C.hσS j (G.src (lev j).e)
  have hne : G.src (σ (G.src (lev j).e)) ≠ G.dst (σ (G.src (lev j).e)) := hloop _
  have hconn := hspan _ hmem hne
  rw [hempty] at hconn
  exact hne (conn_empty_eq hconn)

/-- **A level chain cannot have an empty child forest at any depth** — the paper's chain stops with
`hfind` at some depth `d`, and such a stopping point cannot be a level of a `ProcChain`. -/
theorem not_chain_of_empty_child (hloop : ∀ f : E, G.src f ≠ G.dst f) {J : ℕ}
    (hJ : (lev (J + 1)).F = ∅) : ¬ Nonempty (ProcChain (G := G) H lev) := by
  rintro ⟨C⟩
  have hne := C.childF_nonempty hloop J
  rw [hJ] at hne
  exact absurd hne (by simp)

/-- **A level chain cannot have eventually empty child forests**: `ProcChain` asks for MSF calls and
spokes at every level, which needs a nonempty child forest each time. -/
theorem not_chain_of_eventually_empty (hloop : ∀ f : E, G.src f ≠ G.dst f) {J : ℕ}
    (hJ : ∀ j, J ≤ j → (lev (j + 1)).F = ∅) : ¬ Nonempty (ProcChain (G := G) H lev) := by
  rintro ⟨C⟩
  have hne := C.childF_nonempty hloop J
  rw [hJ J le_rfl] at hne
  exact absurd hne (by simp)

end ProcChain

namespace DriverCall

variable {P : Finset V} {E₀ : Finset E} {t : ℕ} [Nonempty E]

/-- **`EvidenceOn` from driver-shaped chain data.**  The per-edge premise is discharged by
`badFor_of_driverChains`; what is left is the good-schedule premise, `hB` and `0 < |P|`. -/
noncomputable def evidenceOn_of_driverChains (R : DriverCall G P E₀ t)
    (hBfroz : ∀ b i j, R.B b i = R.B b j)
    (lev : E → ℕ → Lev E) (slot : E → ℕ → Fin t × Fin t)
    (hproj : ∀ e j, R.history.pref (lev e j).e (slot e j).1 (slot e j).2 = Pref.project)
    (hret : ∀ (e : E) (j : ℕ) (i : Fin t), ((slot e j).2.val + 1 : ℕ) ≤ i.val →
      (lev e (j + 1)).F ⊆ R.history.forest (slot e j).1 i)
    (hsub : ∀ e j, (lev e (j + 1)).F ⊆ (lev e j).F)
    (S : E → ℕ → Finset E) (es : E → ℕ → List E)
    (hmsf : ∀ (e : E) (j : ℕ), IsMSFOf G (S e j) (lev e (j + 1)).F)
    (hlift : ∀ e j, LiftsLe G (R.history.spoke (slot e j).1 (slot e j).2) (S e j)
      (G.weight (lev e j).e)
      (portal G (R.history.spoke (slot e j).1 (slot e j).2) (G.src (lev e j).e)) (es e j)
      (portal G (R.history.spoke (slot e j).1 (slot e j).2) (G.dst (lev e j).e)))
    (hσS : ∀ (e : E) (j : ℕ) (x : V), R.history.spoke (slot e j).1 (slot e j).2 x ∈ S e j)
    (h0e : ∀ e ∈ E₀, (lev e 0).e = e) (h0F : ∀ e ∈ E₀, (lev e 0).F = R.roundData.F)
    (hslot0 : ∀ (e : E) (_he : e ∈ E₀), slot e 0 = R.sched e)
    (hchild : ∀ e ∈ E₀, Lev.supp G (lev e 1))
    (e₀ : E) (hB : ∀ i j, R.B i j ⊆ E₀) (hP0 : 0 < P.card)
    (hgood : ∀ H : History V E t, LegalOn (G := G) P E₀ e₀ H →
      (H.lostOn E₀ R.sched : ℝ) * Real.log 2 ≤
        (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 *
            Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) + 2 * (E₀.card : ℝ) / (t : ℝ)) :
    EvidenceOn R :=
  evidenceOn_of_good_schedule_badFor R e₀ hB hP0 hgood
    (badFor_of_driverChains R hBfroz lev slot hproj hret hsub S es hmsf hlift hσS
      h0e h0F hslot0 hchild)

/-- **§3.5's per-call bound with the per-edge premise discharged by driver-shaped chains.** -/
theorem card_U_le_number_bound_of_driverChains (R : DriverCall G P E₀ t)
    (hBfroz : ∀ b i j, R.B b i = R.B b j)
    (lev : E → ℕ → Lev E) (slot : E → ℕ → Fin t × Fin t)
    (hproj : ∀ e j, R.history.pref (lev e j).e (slot e j).1 (slot e j).2 = Pref.project)
    (hret : ∀ (e : E) (j : ℕ) (i : Fin t), ((slot e j).2.val + 1 : ℕ) ≤ i.val →
      (lev e (j + 1)).F ⊆ R.history.forest (slot e j).1 i)
    (hsub : ∀ e j, (lev e (j + 1)).F ⊆ (lev e j).F)
    (S : E → ℕ → Finset E) (es : E → ℕ → List E)
    (hmsf : ∀ (e : E) (j : ℕ), IsMSFOf G (S e j) (lev e (j + 1)).F)
    (hlift : ∀ e j, LiftsLe G (R.history.spoke (slot e j).1 (slot e j).2) (S e j)
      (G.weight (lev e j).e)
      (portal G (R.history.spoke (slot e j).1 (slot e j).2) (G.src (lev e j).e)) (es e j)
      (portal G (R.history.spoke (slot e j).1 (slot e j).2) (G.dst (lev e j).e)))
    (hσS : ∀ (e : E) (j : ℕ) (x : V), R.history.spoke (slot e j).1 (slot e j).2 x ∈ S e j)
    (h0e : ∀ e ∈ E₀, (lev e 0).e = e) (h0F : ∀ e ∈ E₀, (lev e 0).F = R.roundData.F)
    (hslot0 : ∀ (e : E) (_he : e ∈ E₀), slot e 0 = R.sched e)
    (hchild : ∀ e ∈ E₀, Lev.supp G (lev e 1))
    (e₀ : E) (hB : ∀ i j, R.B i j ⊆ E₀) (hP0 : 0 < P.card) (ht : 2 ≤ t)
    (hgood : ∀ H : History V E t, LegalOn (G := G) P E₀ e₀ H →
      (H.lostOn E₀ R.sched : ℝ) * Real.log 2 ≤
        (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 *
            Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) + 2 * (E₀.card : ℝ) / (t : ℝ)) :
    ((R.roundData.toCall.U).card : ℝ) ≤
      10 * (t : ℝ) ^ 2 * Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) +
        4 * (E₀.card : ℝ) / (t : ℝ) :=
  card_U_le_number_bound_of_badFor R e₀ hB hP0 ht hgood
    (badFor_of_driverChains R hBfroz lev slot hproj hret hsub S es hmsf hlift hσS
      h0e h0F hslot0 hchild)

end DriverCall

end DLMST