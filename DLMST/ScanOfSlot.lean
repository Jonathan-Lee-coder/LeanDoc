import DLMST.RoundScan
import DLMST.Queries

/-!
# The driver, part 1: the scan tables are read off the schedule

`RoundScan.ofBatches` turned "batches + geometry" into a procedure; the batches themselves were
still data.  This file supplies them.  §3.3's rounds are indexed by the `t²` pairs of `[t]×[t]`, and
the paper's round scans *the edges scheduled in it*, in increasing weight order.  So from a schedule

  `ρ : Sched E t = E → Fin t × Fin t`   (equivalently a slot map `E → Fin (t²)`)

the batches are read off by filtering the instance's edge set and sorting:

  `scanOfSlot slot P E₀ k = (E₀.filter (slot · = k)).sort (· ≤ ·)`.

Everything `ofBatches` asks of its batches is then immediate:

* `scanOfSlot_sub` — a scanned edge belongs to the instance;
* `scanOfSlot_slot` — an edge scanned in round `k` *is* scheduled in round `k`;
* `scanOfSlot_cover` — every edge of the instance is scanned in its own round.

With the geometric hypotheses (`hends`, `hnoloop`) and any portal choice `Pp` within budget, this
gives a `Strategy` that is well-formed and strictly shrinking (`Strategy.ofSlot`,
`Strategy.ofSlot_wf`, `Strategy.ofSlot_strict`), and with the no-isolated-vertices invariant also
vertex-to-edge bounded (`Strategy.ofSlot_hnm`).

`Strategy.ofSlotLeaf` adds the base case: on `E₀ = ∅` the scan returns the empty call
(`CallOut.ofForest`), so the strategy has no children there — exactly `Strategy.Leaf`, which
`CostLinear.cost_linear` needs (`ofScan`'s own `t²` children at `E₀ = ∅` are all empty but still
enumerated, so `Leaf` fails for it).  `Strategy.exists_ofSlot` packages the four properties.

`Strategy.exists_schedule_strategy` ties the schedule to Lemma 3.11: **one** `ρ` serves both the
scans of the strategy and the loss bound `X_H(ρ)·log 2 ≤ log|H| + 2m/t` for every history in a
finite family.

**Still not machine-checked here** (honest): the *choice* of `Pp` from the incident-spoke structure
(`Portals.portal_bound` gives a portal set of size `≤ 2|U|/r²`, but the spokes come from
`BatchSel.exists_spokeSpec` and the coupling of the two is a data construction, not yet a `def`),
the per-instance display of §3.5 (needs the candidate family `A` and Lemma 3.10's `log|A| = O(√(mn))`),
and the post-phase vertex bound `hn` of `cost_linear_of_nodes`.
-/

namespace DLMST

open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

/-! ## The slot map of a schedule -/

/-- A schedule read as a slot index: `(i, j) ∈ [t]×[t]` becomes the index `it + j` of `[t²]`. -/
noncomputable def schedToSlot {t : ℕ} (ρ : Sched E t) : E → Fin (t ^ 2) :=
  fun e => Fin.cast (Nat.pow_two t).symm (finProdFinEquiv (ρ e))

/-- **The round's batch.**  In round `k` the scan visits the edges of the instance that are
scheduled there, in increasing weight order.  (Out-of-range indices scan nothing; the strategy only
uses `k < t²`.) -/
noncomputable def scanOfSlot {t : ℕ} (slot : E → Fin (t ^ 2)) :
    Finset V → Finset E → ℕ → List E :=
  fun _P E₀ k =>
    if h : k < t ^ 2 then (E₀.filter (fun e => slot e = ⟨k, h⟩)).sort (· ≤ ·) else []

/-- A scanned edge is an edge of the instance. -/
theorem scanOfSlot_sub {t : ℕ} (slot : E → Fin (t ^ 2)) (P : Finset V) (E₀ : Finset E) (k : ℕ)
    {e : E} (he : e ∈ scanOfSlot slot P E₀ k) : e ∈ E₀ := by
  unfold scanOfSlot at he
  split at he
  · exact (Finset.mem_filter.mp ((Finset.mem_sort _).mp he)).1
  · exact absurd he List.not_mem_nil

/-- An edge scanned in round `k` is scheduled in round `k`. -/
theorem scanOfSlot_slot {t : ℕ} (slot : E → Fin (t ^ 2)) (P : Finset V) (E₀ : Finset E) (k : ℕ)
    {e : E} (he : e ∈ scanOfSlot slot P E₀ k) : ∃ h : k < t ^ 2, slot e = ⟨k, h⟩ := by
  unfold scanOfSlot at he
  split at he
  · rename_i h
    exact ⟨h, (Finset.mem_filter.mp ((Finset.mem_sort _).mp he)).2⟩
  · exact absurd he List.not_mem_nil

/-- **Every edge of the instance is scanned**, in the round it is scheduled in. -/
theorem scanOfSlot_cover {t : ℕ} (slot : E → Fin (t ^ 2)) (P : Finset V) (E₀ : Finset E) {e : E}
    (he : e ∈ E₀) : ∃ k, k < t ^ 2 ∧ e ∈ scanOfSlot slot P E₀ k := by
  refine ⟨(slot e).val, (slot e).isLt, ?_⟩
  unfold scanOfSlot
  rw [dite_eq_left (slot e).isLt, Finset.mem_sort]
  exact Finset.mem_filter.mpr ⟨he, by simp⟩

/-! ## The portal set, from the per-block portal counts

§3.6's call shares one portal set `P′` among its children, built block by block: block `b` declares
at most `n/(8t³)` portals (paper Lemma 3.2, "selects at most `2n/r` portals" with `r = 8t³`), and
the union of the `t` blocks gives the budget `4t²|P′| ≤ n`.  `portalsOf` is that union and
`portalsOf_budget` is the arithmetic (`Portals.portals_shrink`), so with
`Strategy.exists_ofSlot_ofPortals` the budget hypothesis of `ofSlot` is **derived** from the
per-block counts that `Portals.portal_bound` supplies once each block's spoke family is fixed. -/
/-- The portal set of a call: the union of the `t` blocks' portal sets. -/
noncomputable def portalsOf {t : ℕ} (Pset : Finset V → Finset E → ℕ → Finset V) :
    Finset V → Finset E → Finset V :=
  fun P E₀ => (Finset.range t).biUnion (fun b => Pset P E₀ b)

theorem portalsOf_sub {t : ℕ} (Pset : Finset V → Finset E → ℕ → Finset V)
    (hPsub : ∀ (P : Finset V) (E₀ : Finset E) (b : ℕ), Pset P E₀ b ⊆ P)
    (P : Finset V) (E₀ : Finset E) : portalsOf (t := t) Pset P E₀ ⊆ P := by
  intro v hv
  obtain ⟨b, -, hvb⟩ := Finset.mem_biUnion.mp hv
  exact hPsub P E₀ b hvb

/-- **The portal budget, from the per-block counts.**  If block `b` declares a set with
`8t³·|Q_b| ≤ 2n`, then the union over the `t` blocks satisfies `4t²·|P′| ≤ n` — the paper's
`t²·2nt/r = n/4` (`Portals.portals_shrink`). -/
theorem portalsOf_budget {t : ℕ} (ht : 0 < t) (Pset : Finset V → Finset E → ℕ → Finset V)
    (hportal : ∀ (P : Finset V) (E₀ : Finset E) (b : ℕ), b ∈ Finset.range t →
      8 * t ^ 3 * (Pset P E₀ b).card ≤ 2 * P.card)
    (P : Finset V) (E₀ : Finset E) :
    4 * (Fintype.card (Fin (t ^ 2)) * (portalsOf (t := t) Pset P E₀).card) ≤ P.card := by
  have h1 : (portalsOf (t := t) Pset P E₀).card ≤
      ∑ b ∈ Finset.range t, (Pset P E₀ b).card := Finset.card_biUnion_le
  have hsh := portals_shrink (t := t) (n := P.card)
    (P' := ∑ b ∈ Finset.range t, (Pset P E₀ b).card) ht
    (fun b hb => hportal P E₀ b hb) le_rfl
  have hcard : Fintype.card (Fin (t ^ 2)) = t ^ 2 := Fintype.card_fin _
  calc 4 * (Fintype.card (Fin (t ^ 2)) * (portalsOf (t := t) Pset P E₀).card)
      = 4 * (t ^ 2 * (portalsOf (t := t) Pset P E₀).card) := by rw [hcard]
    _ ≤ 4 * (t ^ 2 * (∑ b ∈ Finset.range t, (Pset P E₀ b).card)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
    _ = 4 * t ^ 2 * (∑ b ∈ Finset.range t, (Pset P E₀ b).card) := by ring
    _ ≤ P.card := hsh

namespace Strategy

/-! ## The strategy of a slot map -/

/-- **The procedure a schedule induces.**  Batches `scanOfSlot slot`, the classification derived
from them (`ofBatches`), a portal choice `Pp` within budget. -/
noncomputable def ofSlot {t : ℕ} (slot : E → Fin (t ^ 2))
    (Pp : Finset V → Finset E → Finset V)
    (hP' : ∀ (P : Finset V) (E₀ : Finset E), Pp P E₀ ⊆ P)
    (hbudget : ∀ (P : Finset V) (E₀ : Finset E),
      4 * (Fintype.card (Fin (t ^ 2)) * (Pp P E₀).card) ≤ P.card)
    (hends : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P) :
    Strategy G :=
  ofBatches (scanOfSlot slot) (fun _ _ _ _ he => scanOfSlot_sub slot _ _ _ he) Pp hP' hbudget hends
    (fun P E₀ e he => scanOfSlot_cover slot P E₀ he)

/-- The schedule-induced procedure answers about the instance it was asked about. -/
theorem ofSlot_wf {t : ℕ} (slot : E → Fin (t ^ 2))
    (Pp : Finset V → Finset E → Finset V)
    (hP' : ∀ (P : Finset V) (E₀ : Finset E), Pp P E₀ ⊆ P)
    (hbudget : ∀ (P : Finset V) (E₀ : Finset E),
      4 * (Fintype.card (Fin (t ^ 2)) * (Pp P E₀).card) ≤ P.card)
    (hends : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P) :
    Wf (ofSlot slot Pp hP' hbudget hends) :=
  ofBatches_wf (scanOfSlot slot) (fun _ _ _ _ he => scanOfSlot_sub slot _ _ _ he) Pp hP' hbudget
    hends (fun P E₀ e he => scanOfSlot_cover slot P E₀ he)

/-- The schedule-induced procedure shrinks strictly (batches cover, no loops). -/
theorem ofSlot_strict {t : ℕ} (slot : E → Fin (t ^ 2))
    (Pp : Finset V → Finset E → Finset V)
    (hP' : ∀ (P : Finset V) (E₀ : Finset E), Pp P E₀ ⊆ P)
    (hbudget : ∀ (P : Finset V) (E₀ : Finset E),
      4 * (Fintype.card (Fin (t ^ 2)) * (Pp P E₀).card) ≤ P.card)
    (hends : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hnoloop : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ≠ G.dst e) :
    Strict (ofSlot slot Pp hP' hbudget hends) :=
  ofBatches_strict (scanOfSlot slot) (fun _ _ _ _ he => scanOfSlot_sub slot _ _ _ he) Pp hP' hbudget
    hends (fun P E₀ e he => scanOfSlot_cover slot P E₀ he) hnoloop

/-- The schedule-induced procedure satisfies the display's vertex-to-edge premise. -/
theorem ofSlot_hnm {t : ℕ} (slot : E → Fin (t ^ 2))
    (Pp : Finset V → Finset E → Finset V)
    (hP' : ∀ (P : Finset V) (E₀ : Finset E), Pp P E₀ ⊆ P)
    (hbudget : ∀ (P : Finset V) (E₀ : Finset E),
      4 * (Fintype.card (Fin (t ^ 2)) * (Pp P E₀).card) ≤ P.card)
    (hends : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (huse : ∀ (P : Finset V) (E₀ : Finset E) (v : V), v ∈ P →
      ∃ e ∈ E₀, G.src e = v ∨ G.dst e = v) :
    ∀ (P : Finset V) (E₀ : Finset E),
      (((ofSlot slot Pp hP' hbudget hends P E₀).2.P.card : ℕ) : ℝ) ≤
        2 * (((ofSlot slot Pp hP' hbudget hends P E₀).2.E₀.card : ℕ) : ℝ) :=
  ofBatches_hnm (scanOfSlot slot) (fun _ _ _ _ he => scanOfSlot_sub slot _ _ _ he) Pp hP' hbudget
    hends (fun P E₀ e he => scanOfSlot_cover slot P E₀ he) huse

/-! ## The base case: an edge-free instance has no children -/

/-- The empty call: no children, `F = ∅`.  This is the paper's base case (`CallOut.ofForest`). -/
noncomputable def leafCall (P : Finset V) : CallOut G (Fin 0) :=
  CallOut.reindex (Fintype.equivFin Empty)
    (CallOut.ofForest (G := G) P ∅ (F := ∅) (by simp) IsForest.empty (by simp) (by simp))

/-- **The schedule-induced procedure with its base case.**  On an edge-free instance the scan's `t²`
rounds are all empty but still enumerated, so `Leaf` fails for `ofSlot`; this variant returns the
empty call there and the scan elsewhere.  `Leaf` is the only property `ofSlot` lacks, and the
branches agree on every nonempty instance. -/
noncomputable def ofSlotLeaf {t : ℕ} (slot : E → Fin (t ^ 2))
    (Pp : Finset V → Finset E → Finset V)
    (hP' : ∀ (P : Finset V) (E₀ : Finset E), Pp P E₀ ⊆ P)
    (hbudget : ∀ (P : Finset V) (E₀ : Finset E),
      4 * (Fintype.card (Fin (t ^ 2)) * (Pp P E₀).card) ≤ P.card)
    (hends : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P) :
    Strategy G :=
  fun P E₀ =>
    if h : E₀ = ∅ then ⟨0, leafCall (G := G) P⟩ else ofSlot slot Pp hP' hbudget hends P E₀

theorem ofSlotLeaf_wf {t : ℕ} (slot : E → Fin (t ^ 2))
    (Pp : Finset V → Finset E → Finset V)
    (hP' : ∀ (P : Finset V) (E₀ : Finset E), Pp P E₀ ⊆ P)
    (hbudget : ∀ (P : Finset V) (E₀ : Finset E),
      4 * (Fintype.card (Fin (t ^ 2)) * (Pp P E₀).card) ≤ P.card)
    (hends : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P) :
    Wf (ofSlotLeaf slot Pp hP' hbudget hends) := by
  intro P E₀
  unfold ofSlotLeaf
  by_cases h : E₀ = ∅
  · subst h
    rw [dite_eq_left rfl]
    exact ⟨rfl, rfl⟩
  · rw [dite_eq_right h]
    exact ofSlot_wf slot Pp hP' hbudget hends P E₀

theorem ofSlotLeaf_strict {t : ℕ} (slot : E → Fin (t ^ 2))
    (Pp : Finset V → Finset E → Finset V)
    (hP' : ∀ (P : Finset V) (E₀ : Finset E), Pp P E₀ ⊆ P)
    (hbudget : ∀ (P : Finset V) (E₀ : Finset E),
      4 * (Fintype.card (Fin (t ^ 2)) * (Pp P E₀).card) ≤ P.card)
    (hends : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hnoloop : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ≠ G.dst e) :
    Strict (ofSlotLeaf slot Pp hP' hbudget hends) := by
  intro P E₀ hne i
  revert i
  unfold ofSlotLeaf
  rw [dite_eq_right (Finset.ne_empty_iff_nonempty.mpr hne)]
  intro i
  exact ofSlot_strict slot Pp hP' hbudget hends hnoloop P E₀ hne i

theorem ofSlotLeaf_leaf {t : ℕ} (slot : E → Fin (t ^ 2))
    (Pp : Finset V → Finset E → Finset V)
    (hP' : ∀ (P : Finset V) (E₀ : Finset E), Pp P E₀ ⊆ P)
    (hbudget : ∀ (P : Finset V) (E₀ : Finset E),
      4 * (Fintype.card (Fin (t ^ 2)) * (Pp P E₀).card) ≤ P.card)
    (hends : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P) :
    Leaf (ofSlotLeaf slot Pp hP' hbudget hends) := by
  intro P
  unfold ofSlotLeaf
  rw [dite_eq_left rfl]

theorem ofSlotLeaf_hnm {t : ℕ} (slot : E → Fin (t ^ 2))
    (Pp : Finset V → Finset E → Finset V)
    (hP' : ∀ (P : Finset V) (E₀ : Finset E), Pp P E₀ ⊆ P)
    (hbudget : ∀ (P : Finset V) (E₀ : Finset E),
      4 * (Fintype.card (Fin (t ^ 2)) * (Pp P E₀).card) ≤ P.card)
    (hends : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (huse : ∀ (P : Finset V) (E₀ : Finset E) (v : V), v ∈ P →
      ∃ e ∈ E₀, G.src e = v ∨ G.dst e = v) :
    ∀ (P : Finset V) (E₀ : Finset E),
      (((ofSlotLeaf slot Pp hP' hbudget hends P E₀).2.P.card : ℕ) : ℝ) ≤
        2 * (((ofSlotLeaf slot Pp hP' hbudget hends P E₀).2.E₀.card : ℕ) : ℝ) := by
  intro P E₀
  unfold ofSlotLeaf
  by_cases h : E₀ = ∅
  · subst h
    rw [dite_eq_left rfl]
    have hempty : P = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨v, hv⟩
      obtain ⟨e, he, -⟩ := huse P ∅ v hv
      exact absurd he (by simp)
    rw [hempty]
    show ((0 : ℕ) : ℝ) ≤ 2 * (((∅ : Finset E).card : ℕ) : ℝ)
    simp
  · rw [dite_eq_right h]
    exact ofSlot_hnm slot Pp hP' hbudget hends huse P E₀

/-- **The four properties together**: a well-formed, strictly shrinking, leaved, vertex-bounded
procedure — the hypothesis bundle `CostLinear.cost_linear_of_display` consumes. -/
theorem exists_ofSlot {t : ℕ} (slot : E → Fin (t ^ 2))
    (Pp : Finset V → Finset E → Finset V)
    (hP' : ∀ (P : Finset V) (E₀ : Finset E), Pp P E₀ ⊆ P)
    (hbudget : ∀ (P : Finset V) (E₀ : Finset E),
      4 * (Fintype.card (Fin (t ^ 2)) * (Pp P E₀).card) ≤ P.card)
    (hends : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hnoloop : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ≠ G.dst e)
    (huse : ∀ (P : Finset V) (E₀ : Finset E) (v : V), v ∈ P →
      ∃ e ∈ E₀, G.src e = v ∨ G.dst e = v) :
    ∃ S : Strategy G, Wf S ∧ Strict S ∧ Leaf S ∧
      ∀ (P : Finset V) (E₀ : Finset E),
        (((S P E₀).2.P.card : ℕ) : ℝ) ≤ 2 * (((S P E₀).2.E₀.card : ℕ) : ℝ) :=
  ⟨ofSlotLeaf slot Pp hP' hbudget hends, ofSlotLeaf_wf slot Pp hP' hbudget hends,
    ofSlotLeaf_strict slot Pp hP' hbudget hends hnoloop,
    ofSlotLeaf_leaf slot Pp hP' hbudget hends,
    ofSlotLeaf_hnm slot Pp hP' hbudget hends huse⟩

/-- **No portal choice needed.**  With `Pp = ∅` the budget `4·t²·|Pp| ≤ |P|` is free, so the
strategy exists for every schedule and every graph with the endpoint geometry alone.  (The empty
portal set is the degenerate choice: the paper's portals exist to keep `|P'| ≤ 2|U(F)|/r²`, which
`Portals.portal_bound` supplies once the spokes are chosen.) -/
theorem exists_ofSlot_noPortal {t : ℕ} (slot : E → Fin (t ^ 2))
    (hends : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hnoloop : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ≠ G.dst e)
    (huse : ∀ (P : Finset V) (E₀ : Finset E) (v : V), v ∈ P →
      ∃ e ∈ E₀, G.src e = v ∨ G.dst e = v) :
    ∃ S : Strategy G, Wf S ∧ Strict S ∧ Leaf S ∧
      ∀ (P : Finset V) (E₀ : Finset E),
        (((S P E₀).2.P.card : ℕ) : ℝ) ≤ 2 * (((S P E₀).2.E₀.card : ℕ) : ℝ) :=
  exists_ofSlot slot (fun _ _ => ∅) (fun _ _ => Finset.empty_subset _) (fun _ _ => by simp)
    hends hnoloop huse

/-- **The four properties, with the portal budget derived from the per-block portal counts.**  This
is `exists_ofSlot` with `Pp := portalsOf Pset`: the only portal hypotheses are `Pset ⊆ P` and the
per-block counts `8t³·|Q_b| ≤ 2n` that `Portals.portal_bound` supplies for the block's spoke
family. -/
theorem exists_ofSlot_ofPortals {t : ℕ} (ht : 0 < t) (slot : E → Fin (t ^ 2))
    (Pset : Finset V → Finset E → ℕ → Finset V)
    (hPsub : ∀ (P : Finset V) (E₀ : Finset E) (b : ℕ), Pset P E₀ b ⊆ P)
    (hportal : ∀ (P : Finset V) (E₀ : Finset E) (b : ℕ), b ∈ Finset.range t →
      8 * t ^ 3 * (Pset P E₀ b).card ≤ 2 * P.card)
    (hends : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hnoloop : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ≠ G.dst e)
    (huse : ∀ (P : Finset V) (E₀ : Finset E) (v : V), v ∈ P →
      ∃ e ∈ E₀, G.src e = v ∨ G.dst e = v) :
    ∃ S : Strategy G, Wf S ∧ Strict S ∧ Leaf S ∧
      ∀ (P : Finset V) (E₀ : Finset E),
        (((S P E₀).2.P.card : ℕ) : ℝ) ≤ 2 * (((S P E₀).2.E₀.card : ℕ) : ℝ) :=
  exists_ofSlot slot (portalsOf Pset) (portalsOf_sub Pset hPsub)
    (portalsOf_budget ht Pset hportal) hends hnoloop huse

/-- **One schedule serves the scans and Lemma 3.11 together.**  For `2 ≤ t`, any finite family of
histories admits a schedule `ρ` with `X_H(ρ)·log 2 ≤ log|Hs| + 2m/t` for every `H ∈ Hs`
(`lemma311`), and the same `ρ` (read as a slot map) induces a procedure satisfying all four
properties above.  This is the paper's "fix one schedule": §3.3's rounds, §3.5's sample and the loss
count all use it. -/
theorem exists_schedule_strategy {t : ℕ} (ht : 2 ≤ t) (Hs : Finset (History V E t))
    (Pp : Finset V → Finset E → Finset V)
    (hP' : ∀ (P : Finset V) (E₀ : Finset E), Pp P E₀ ⊆ P)
    (hbudget : ∀ (P : Finset V) (E₀ : Finset E),
      4 * (Fintype.card (Fin (t ^ 2)) * (Pp P E₀).card) ≤ P.card)
    (hends : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hnoloop : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ≠ G.dst e)
    (huse : ∀ (P : Finset V) (E₀ : Finset E) (v : V), v ∈ P →
      ∃ e ∈ E₀, G.src e = v ∨ G.dst e = v) :
    ∃ (ρ : Sched E t) (S : Strategy G), Wf S ∧ Strict S ∧ Leaf S ∧
      (∀ (P : Finset V) (E₀ : Finset E),
        (((S P E₀).2.P.card : ℕ) : ℝ) ≤ 2 * (((S P E₀).2.E₀.card : ℕ) : ℝ)) ∧
      ∀ H ∈ Hs,
        (H.lost ρ : ℝ) * Real.log 2 ≤
          Real.log (Hs.card : ℝ) + 2 * (Fintype.card E : ℝ) / (t : ℝ) := by
  obtain ⟨ρ, hρ⟩ := lemma311 ht Hs
  obtain ⟨S, hwf, hstr, hleaf, hnm⟩ :=
    exists_ofSlot (schedToSlot ρ) Pp hP' hbudget hends hnoloop huse
  exact ⟨ρ, S, hwf, hstr, hleaf, hnm, hρ⟩

end Strategy

end DLMST