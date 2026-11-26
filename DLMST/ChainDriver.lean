import DLMST.ProcDriver

/-!
# The chain interface on a driver call: instance-only chains, and the fields the interface supplies

`ProcDriver.badFor_of_procChains` asks for a `ProcChain` at **every** edge.  Two refinements make the
interface match what a call actually owes:

* `ProcChain.unSupp_errOf_on` / `DriverCall.badFor_of_procChainsOn` — chains are only needed for the
  *instance's* edges (`e ∈ E₀`); the per-call count never looks outside `E₀`.
* `DriverCall.history_spoke_frozen` — if the batches are frozen inside each block
  (`R.B b i = R.B b j`), the driver's spoke vector is frozen there too: `spokeTable` reads only the
  batch *set*, so equal batches give equal spokes.  This discharges `ProcChain.hfroz` for a driver
  call, as `history_consistent` already discharged `hcons` and `history_spoke_incident` discharged
  `hspoke`.

`ProcChain.ofDriver` packages a chain at a driver call with exactly those three fields derived, and
`DriverCall.badFor_of_driverChains` writes the per-edge sentence with only the algorithmic premises
left: the projection fact `hproj`, the frozen-spoke/return geometry `hret`/`hsub`, and the child-call
facts `hmsf`/`hlift`/`hσS` — plus frozen batches and the root identifications (`lev · 0` is `⟨e, D.F⟩`,
slot `0` is the call's schedule, depth-one projections supported).
-/

namespace DLMST

open Classical

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

namespace ProcChain

variable {t : ℕ} {H : History V E t} {lev : ℕ → Lev E}

/-- **Chains only on the instance.**  Same as `unSupp_errOf` with `C` required only for `e ∈ E₀` and
the root identifications restricted accordingly. -/
theorem unSupp_errOf_on {E₀ : Finset E} (ρ : E → Fin t × Fin t) (est : E → Pref)
    (lev : E → ℕ → Lev E) (C : ∀ e, e ∈ E₀ → ProcChain (G := G) H (lev e)) {F₀ : Finset E}
    (h0e : ∀ e ∈ E₀, (lev e 0).e = e) (h0F : ∀ e ∈ E₀, (lev e 0).F = F₀)
    (hslot : ∀ (e : E) (he : e ∈ E₀), (C e he).slot 0 = ρ e)
    (hchild : ∀ e ∈ E₀, Lev.supp G (lev e 1)) :
    ∀ e ∈ E₀, ¬ supported G F₀ e → H.errOf est e (ρ e) := by
  intro e he hnot
  have hnot' : ¬ Lev.supp G (lev e 0) := by
    show ¬ supported G (lev e 0).F (lev e 0).e
    rw [h0F e he, h0e e he]
    exact hnot
  have h := (C e he).errorOr_unsupp (fun _ => est) (hchild e he) hnot'
  rw [h0e e he] at h
  rw [hslot e he] at h
  simpa [History.errOf] using h

end ProcChain

namespace DriverCall

variable {P : Finset V} {E₀ : Finset E} {t : ℕ} [Nonempty E]

/-- **The driver's spokes are frozen inside a block when the batches are.**  `spokeTable` reads only
the batch set and the quota, so equal batches give an equal spoke vector. -/
theorem history_spoke_frozen (R : DriverCall G P E₀ t) (hB : ∀ b i j, R.B b i = R.B b j)
    (b i j : Fin t) : R.history.spoke b i = R.history.spoke b j := by
  funext v
  show spokeOf (G := G) (R.B b i) (fun e => e ∉ R.roundData.F) R.quota v =
    spokeOf (G := G) (R.B b j) (fun e => e ∉ R.roundData.F) R.quota v
  rw [hB b i j]

/-- **The per-edge sentence with chains only on the instance.** -/
theorem badFor_of_procChainsOn (R : DriverCall G P E₀ t) (lev : E → ℕ → Lev E)
    (C : ∀ e, e ∈ E₀ → ProcChain (G := G) R.history (lev e))
    (h0e : ∀ e ∈ E₀, (lev e 0).e = e) (h0F : ∀ e ∈ E₀, (lev e 0).F = R.roundData.F)
    (hslot : ∀ (e : E) (he : e ∈ E₀), (C e he).slot 0 = R.sched e)
    (hchild : ∀ e ∈ E₀, Lev.supp G (lev e 1)) :
    ∀ e ∈ E₀, ¬ supported G R.roundData.F e → R.history.badFor e (R.sched e) := by
  intro e he hns
  have h := ProcChain.unSupp_errOf_on (G := G) (H := R.history) R.sched
    (estOfOn E₀ R.sched (truthCand R)) lev C h0e h0F hslot hchild e he hns
  exact (errOf_truth_iff R he).mp h

end DriverCall

namespace ProcChain

variable {P : Finset V} {E₀ : Finset E} {t : ℕ}

/-- **A `ProcChain` at a driver call**, with `hcons`, `hfroz` and `hspoke` derived from the call's
data: consistency from `history_consistent`, frozen spokes from frozen batches, incidence from the
batch supply.  The remaining fields are the algorithmic premises. -/
def ofDriver (R : DriverCall G P E₀ t) [Nonempty E] (hBfroz : ∀ b i j, R.B b i = R.B b j)
    (lev : ℕ → Lev E) (slot : ℕ → Fin t × Fin t)
    (hproj : ∀ j, R.history.pref (lev j).e (slot j).1 (slot j).2 = Pref.project)
    (hret : ∀ j i, ((slot j).2.val + 1 : ℕ) ≤ i.val →
      (lev (j + 1)).F ⊆ R.history.forest (slot j).1 i)
    (hsub : ∀ j, (lev (j + 1)).F ⊆ (lev j).F)
    (S : ℕ → Finset E) (es : ℕ → List E)
    (hmsf : ∀ j, IsMSFOf G (S j) (lev (j + 1)).F)
    (hlift : ∀ j, LiftsLe G (R.history.spoke (slot j).1 (slot j).2) (S j) (G.weight (lev j).e)
      (portal G (R.history.spoke (slot j).1 (slot j).2) (G.src (lev j).e)) (es j)
      (portal G (R.history.spoke (slot j).1 (slot j).2) (G.dst (lev j).e)))
    (hσS : ∀ j x, R.history.spoke (slot j).1 (slot j).2 x ∈ S j) :
    ProcChain (G := G) R.history lev where
  slot := slot
  hcons := R.history_consistent
  hproj := hproj
  hfroz := fun j i => R.history_spoke_frozen hBfroz (slot j).1 i (slot j).2
  hret := hret
  hsub := hsub
  S := S
  es := es
  hmsf := hmsf
  hspoke := fun j x => R.history_spoke_incident (slot j).1 (slot j).2 x
  hlift := hlift
  hσS := hσS

end ProcChain

namespace DriverCall

variable {P : Finset V} {E₀ : Finset E} {t : ℕ} [Nonempty E]

/-- **The per-edge sentence from driver-shaped chain data.**  Everything the call's interface supplies
is derived (`ProcChain.ofDriver`); the remaining premises are the algorithmic ones, listed per edge. -/
theorem badFor_of_driverChains (R : DriverCall G P E₀ t) (hBfroz : ∀ b i j, R.B b i = R.B b j)
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
    (hchild : ∀ e ∈ E₀, Lev.supp G (lev e 1)) :
    ∀ e ∈ E₀, ¬ supported G R.roundData.F e → R.history.badFor e (R.sched e) :=
  badFor_of_procChainsOn R lev
    (fun e _ => ProcChain.ofDriver R hBfroz (lev e) (slot e) (hproj e) (hret e) (hsub e)
      (S e) (es e) (hmsf e) (hlift e) (hσS e))
    h0e h0F hslot0 hchild

end DriverCall

end DLMST