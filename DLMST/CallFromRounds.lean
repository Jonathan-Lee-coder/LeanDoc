import DLMST.Procedure
import DLMST.Dispatch
import DLMST.EstimateBound

/-!
# A call, from the round data — and the strategy they define

`CallOut.ofClass` reduces a call to three objects: the returned forest `F`, the shared portal set
`P'`, and a classification `cls : E → Option ι` of every input edge (kept/retained, or sent to one
child).  This file produces that classification from the *round data* of §3: each round contributes
a forest piece `Fr r` and child inputs `inp r i`, and the instance's forest is their union
`F = ⋃ r, Fr r`.

The interesting content is not the packaging — `ofClass` handles it — but the *identification* of
the call's outputs with the round data:

* `F` is the union of the round forests, so `IsForest` and `|F| ≤ |P|` are properties of the
  rounds' own output (taken here as data: they are what the algorithm's rounds must establish);
* every child of the call is *inside* the round input it was cut from (`kidE p ⊆ inp p`), so the
  paper's per-round counting of "edges sent to sub-instances" bounds the call's Σ|Eᵢ| directly;
* consequently the call's "rest" is `|U| + Σ|Eᵢ| = |E₀| − |F|` — the §3.6 quantity, expressed in
  the rounds' terms.

`cls` is defined by *choosing* a round child that contains the edge (`Classical.choose`), so no
edge is ever lost: an edge is `none` exactly when it is kept (`F`) or retained (`U(F)`), and
`some p` only when it genuinely lies in `inp p`.  Edges that the rounds place in a child *and* that
are retained stay retained — coverage is a disjunction, not a partition, which is why the
children's inputs need not be disjoint from `U`.

Since `P` and `E₀` are *parameters* of `RoundData`, a family of round data with one member per
instance is exactly a `Strategy` (`Strategy.ofRoundData`), and it is well-formed by construction
(`Strategy.ofRoundData_wf`).  That is the whole gap between §3's rounds and §3.6's level chain.
-/

namespace DLMST
open Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

namespace History

/-- **The per-edge error of §3.3**, for a history: the slot assigned to `e` is bad for it, or the
estimate *made for `e`* differs from `e`'s own preferred action at that slot.  This is `Rounds.error`
with the history's per-edge action row — the form Lemma 3.7's conclusion takes (`lemma37_error`).

The estimate is one predicted action per **edge** (`E → Pref`), which is what Claim 3.12 counts in
`EstimateBound.lean` (coordinates are edges, values are `Pref`); a slot-indexed estimate would be
constant on each fiber and could not tell two edges of the same slot apart. -/
def errOf {s : ℕ} (H : History V E s) (est : E → Pref) (e : E) (p : Fin s × Fin s) : Prop :=
  H.badFor e p ∨ est e ≠ H.pref e p.1 p.2

end History

namespace CallOut

/-- **The round data of one instance.**  `t²` rounds, each returning a forest piece `Fr r` and
dispatching edges to `ι` children with inputs `inp r i`; every edge of `E₀` is kept, retained,
supported by the returned forest (so it may be discarded), or lies in some child's input; the
children's inputs are pairwise disjoint; the union of the round forests is a forest of at most `|P|`
edges; `P'` is the shared portal set within the portal budget.  `P` and `E₀` are parameters, so the
data can be attached to the instance it belongs to. -/
structure RoundData (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (ι : Type*)
    [Fintype ι] [DecidableEq ι] (t : ℕ) where
  Fr : Fin (t ^ 2) → Finset E
  inp : Fin (t ^ 2) → ι → Finset E
  P' : Finset V
  hsubF : (Finset.univ.biUnion Fr) ⊆ E₀
  hforest : IsForest G (Finset.univ.biUnion Fr)
  hFcard : (Finset.univ.biUnion Fr).card ≤ P.card
  hP' : P' ⊆ P
  hbudget : 4 * (Fintype.card (Fin (t ^ 2) × ι) * P'.card) ≤ P.card
  hcover : ∀ e ∈ E₀, e ∈ Finset.univ.biUnion Fr ∨
    e ∈ unsupp G (Finset.univ.biUnion Fr) ∨
    supported G (Finset.univ.biUnion Fr) e ∨ ∃ p : Fin (t ^ 2) × ι, e ∈ inp p.1 p.2
  hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin (t ^ 2) × ι)))
    (fun p : Fin (t ^ 2) × ι => inp p.1 p.2)

namespace RoundData

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ} {P : Finset V} {E₀ : Finset E}
  (D : RoundData G P E₀ ι t)

/-- The forest the call returns: the union of the rounds' forest pieces. -/
noncomputable def F : Finset E := Finset.univ.biUnion D.Fr

/-- The instance's retained edges — the paper's `U(F)`, restricted to this instance. -/
noncomputable def U : Finset E := unsupp G D.F ∩ E₀

/-- **The retained set is covered by the error slots.**  If every retained edge is assigned to a slot
the algorithm got wrong — Lemma 3.7 read as a statement about error slots — then `|U(F)|` is at most
the number of edges sitting in wrong slots. -/
theorem card_U_le_error_slot {σ : Type*} [Fintype σ] [DecidableEq σ]
    (slot : E → σ) (err : σ → Prop) [DecidablePred err]
    (h : ∀ e ∈ E₀, ¬ supported G D.F e → err (slot e)) :
    D.U.card ≤ (E₀.filter fun e => err (slot e)).card := by
  refine Finset.card_le_card (fun e he => ?_)
  obtain ⟨hU, hE⟩ := Finset.mem_inter.mp he
  exact Finset.mem_filter.mpr ⟨hE, h e hE (mem_unsupp.mp hU)⟩

/-- **The retained set against a schedule**: the paper's `lost` count is `#{e : badFor e (ρ e)}`, so
Lemma 3.7's conclusion in the per-edge form `¬supported → badFor` bounds the instance's retained set by
it.  This is the §3.3 ↔ §3.5 join consumed by `error_count_le`. -/
theorem card_U_le_lost {s : ℕ} (H : History V E s) (ρ : Sched E s)
    (h : ∀ e ∈ E₀, ¬ supported G D.F e → H.badFor e (ρ e)) :
    D.U.card ≤ H.lost ρ := by
  refine Finset.card_le_card (fun e he => ?_)
  obtain ⟨hU, hE⟩ := Finset.mem_inter.mp he
  simpa [History.lost_def] using h e hE (mem_unsupp.mp hU)

/-- **`|U(F)|` is bounded by any per-edge predicate covering the unsupported edges.**  This is
`card_U_le_error_slot` with the predicate allowed to depend on the edge itself, which is the form the
history's bad-round / mis-estimate split needs. -/
theorem card_U_le_pred (r : E → Prop) [DecidablePred r]
    (h : ∀ e ∈ E₀, ¬ supported G D.F e → r e) :
    D.U.card ≤ (E₀.filter r).card := by
  refine Finset.card_le_card (fun e he => ?_)
  obtain ⟨hU, hE⟩ := Finset.mem_inter.mp he
  exact Finset.mem_filter.mpr ⟨hE, h e hE (mem_unsupp.mp hU)⟩

/-- **Slot weights**: splitting the error-slot count over the slots it selects, `|U(F)|` is at most
the sum of the sizes of the edge fibres of the *wrong* slots,
`Σ_{p ∈ error} #{e ∈ E₀ : slot e = p}`.  This is the shape §3.3's estimate pays in: a rejected edge
buys the round it was assigned to. -/
theorem card_U_le_sum_slot {σ : Type*} [Fintype σ] [DecidableEq σ]
    (slot : E → σ) (err : σ → Prop) [DecidablePred err]
    (h : ∀ e ∈ E₀, ¬ supported G D.F e → err (slot e)) :
    D.U.card ≤ ∑ p ∈ Finset.univ.filter err, (E₀.filter fun e => slot e = p).card := by
  refine le_trans (D.card_U_le_error_slot slot err h) ?_
  have hfib := Finset.card_eq_sum_card_fiberwise
    (s := E₀.filter (fun e => err (slot e))) (t := Finset.univ.filter err) (f := slot)
    (fun e he => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2⟩)
  rw [hfib]
  exact Finset.sum_le_sum (fun p _ => Finset.card_le_card (fun e he => by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp he
    obtain ⟨h1a, -⟩ := Finset.mem_filter.mp h1
    exact Finset.mem_filter.mpr ⟨h1a, h2⟩))

/-- The children as a single family indexed by `(round, child)`. -/
def inp' : Fin (t ^ 2) × ι → Finset E := fun p => D.inp p.1 p.2

theorem inp'_mem {p : Fin (t ^ 2) × ι} {e : E} : e ∈ D.inp' p ↔ e ∈ D.inp p.1 p.2 := Iff.rfl

/-- The child holding `e`, if any — an actual witness, not a default. -/
noncomputable def childOf (e : E) : Option (Fin (t ^ 2) × ι) :=
  if h : ∃ p, e ∈ D.inp' p then some (Classical.choose h) else none

theorem childOf_mem {e : E} {p : Fin (t ^ 2) × ι} (h : D.childOf e = some p) : e ∈ D.inp' p := by
  unfold childOf at h
  split at h
  next h' =>
    rw [← Option.some.inj h]
    exact Classical.choose_spec h'
  next h' => exact absurd h (by simp)

theorem childOf_eq_none {e : E} (h : D.childOf e = none) : ¬∃ p, e ∈ D.inp' p := by
  intro h'
  unfold childOf at h
  split at h
  next _ => exact absurd h (by simp)
  next h'' => exact h'' h'

/-- The classification: `none` for the kept or retained edges, `some p` for an edge dispatched to
the child `p` that really contains it. -/
noncomputable def cls (e : E) : Option (Fin (t ^ 2) × ι) :=
  if e ∈ D.F ∨ e ∈ D.U then none else D.childOf e

theorem cls_eq_childOf {e : E} {p : Fin (t ^ 2) × ι} (h : D.cls e = some p) :
    D.childOf e = some p := by
  unfold cls at h
  split at h
  next _ => exact absurd h (by simp)
  next _ => exact h

/-- **The call assembled from the round data.**  The kept edges are the round forests, the children
get the dispatched edges, and every edge the rounds did not keep, did not reject and did not hand to a
child becomes the call's discarded bucket (`CallOut.ofClass` derives it from `cls = none`). -/
noncomputable def toCall : CallOut G (Fin (t ^ 2) × ι) :=
  ofClass P E₀ D.F D.P' D.cls D.hsubF D.hforest D.hFcard D.hP' D.hbudget
    (by
      intro e he p hcl
      unfold cls at hcl
      split at hcl
      next _ => exact absurd hcl (by simp)
      next h =>
        refine ⟨fun hF => h (Or.inl hF), fun hU => h (Or.inr (Finset.mem_inter.mpr ⟨hU, he⟩))⟩)

/-- **Every child of the call lies in the round input it was cut from.**  This is what lets the
paper's per-round count of dispatched edges bound `Σᵢ|Eᵢ|`. -/
theorem kidE_subset_input (p : Fin (t ^ 2) × ι) : D.toCall.kidE p ⊆ D.inp' p := by
  intro e he
  have he' : e ∈ E₀.filter (fun e => D.cls e = some p) := he
  exact D.childOf_mem (D.cls_eq_childOf (Finset.mem_filter.mp he').2)

/-- The call's total child input is at most the rounds' total dispatched edges. -/
theorem sum_kidE_le_sum_input :
    (∑ p : Fin (t ^ 2) × ι, (D.toCall.kidE p).card) ≤ ∑ p : Fin (t ^ 2) × ι, (D.inp' p).card :=
  Finset.sum_le_sum (fun p _ => Finset.card_le_card (D.kidE_subset_input p))

/-- **§3.6's second count on the round data.**  The children's inputs are the fiber family `inp'`, which
is pairwise disjoint for free (`D.hdisj`), so `sum_card_kid_le_inputs` gives the call's total child
input `Σᵢ|Eᵢ| ≤ |Rej| + 2t²(n−1) + t(n−1+r²n)` from the paper's per-round / per-block input sizes and a
containment `inp' ⊆ Rej ∪ ⋃roundIn ∪ ⋃blkIn`.  The containment is the only procedure-specific input —
the remaining second process-level identification — while disjointness and the numeric half are free
(`sum_kidE_le_sum_input`, `msf_input_count`). -/
theorem sum_kidE_le_inputs {Rej : Finset E} {roundIn : Fin (t ^ 2) → Finset E}
    {blkIn : Fin t → Finset E} {r n rej : ℕ}
    (hsub : ∀ p : Fin (t ^ 2) × ι,
      D.inp' p ⊆ Rej ∪ (Finset.univ.biUnion roundIn ∪ Finset.univ.biUnion blkIn))
    (hround : ∀ i, (roundIn i).card ≤ 2 * (n - 1))
    (hblk : ∀ b, (blkIn b).card ≤ (n - 1) + r ^ 2 * n)
    (hrej : Rej.card ≤ rej) :
    (∑ p : Fin (t ^ 2) × ι, (D.toCall.kidE p).card) ≤
      rej + 2 * t ^ 2 * (n - 1) + t * ((n - 1) + r ^ 2 * n) :=
  le_trans D.sum_kidE_le_sum_input
    (sum_card_kid_le_inputs (kid := D.inp')
      (fun i j hij => D.hdisj.disjoint_of_ne (Finset.mem_univ i) (Finset.mem_univ j) hij)
      hsub hround hblk hrej)

/-- The round input total is the double sum over rounds and children. -/
theorem sum_input_eq :
    (∑ p : Fin (t ^ 2) × ι, (D.inp' p).card) = ∑ r, ∑ i, (D.inp r i).card :=
  Fintype.sum_prod_type (f := fun p : Fin (t ^ 2) × ι => (D.inp' p).card)

/-- **§3.6's display data in the rounds' terms**: the call's kept, retained, discarded and
dispatched pieces partition its input edge set. -/
theorem partition :
    D.F.card + (D.toCall.U).card + D.toCall.drop.card + ∑ p, (D.toCall.kidE p).card
      = E₀.card :=
  CallOut.partition_eq D.toCall

/-- **The "rest" of one instance**: everything not kept is retained, discarded or dispatched, so
`|U| + Σᵢ|Eᵢ| ≤ |E₀| − |F|`, with the discarded supported edges as slack.  This is the quantity
§3.6 bounds per level. -/
theorem U_add_kids :
    (D.toCall.U).card + ∑ p, (D.toCall.kidE p).card ≤ E₀.card - D.F.card := by
  have h := D.partition
  omega

/-- **The four-bucket identity of one call**: the children's inputs together with the discarded
supported edges carry exactly the edges that were neither kept nor retained,
`Σᵢ|Eᵢ| + |drop| = |E₀| − |F| − |U(F)|`.

This is where the model matches the paper.  The paper's procedure discards every edge that the
returned forest *supports* (`U(F)` is only the unsupported edges), which is what makes the display
`|F| + |U| + Σᵢ|Eᵢ| ≤ εm + C√(mn)` smaller than `m`.  In a three-bucket model `drop` would be forced
to `∅`, the display's left-hand side would equal `|E₀|`, and the paper's per-call bound on
`Σᵢ|Eᵢ|` would become a hypothesis on the instance rather than a property of the algorithm;
`CallOut.partition_eq` now carries the fourth bucket, and this theorem exhibits the slack. -/
theorem sum_kidE :
    ∑ p, (D.toCall.kidE p).card + D.toCall.drop.card
      = E₀.card - D.F.card - (D.toCall.U).card := by
  have h := D.partition
  rw [Nat.sub_sub]
  exact Nat.eq_sub_of_add_eq (by omega)

/-- **A nonempty round forest shrinks every child's input.**  An edge of `F` lies in `E₀` and in no
child (`hFkid`), so the child's input misses a genuine edge of the instance. -/
theorem toCall_kidE_card_lt {f : E} (hf : f ∈ D.F) (p : Fin (t ^ 2) × ι) :
    (D.toCall.kidE p).card < E₀.card := by
  have hfE : f ∈ E₀ := by
    rw [RoundData.F, Finset.mem_biUnion] at hf
    exact D.hsubF (Finset.mem_biUnion.mpr hf)
  have hnot : f ∉ D.toCall.kidE p := by
    intro hmem
    have hdisj := D.toCall.hFkid p
    exact (Finset.disjoint_left.mp hdisj) hf hmem
  exact CallOut.kidE_card_lt D.toCall p hfE hnot

/-- The rounds' union is a forest as soon as the kept edges satisfy the Kruskal-order criterion —
the selection rule the certificate procedure's rounds implement (`isForest_of_forall_not_conn_below`).
Establishing that criterion from the rounds' own acceptance test is the remaining part of this
identification; `RoundData` carries forestness as data until then. -/
theorem isForest_F
    (h : ∀ e ∈ D.F, ¬ Conn G (D.F.filter (fun f => f < e)) (G.src e) (G.dst e)) :
    IsForest G D.F :=
  isForest_of_forall_not_conn_below h

/-! ## §3.3's error count, split into its two numeric halves -/

/-- **`|U(F)|` paid by per-edge errors.**  Lemma 3.7's per-edge conclusion bounds the retained set by
the number of input edges whose assigned slot is an error for them. -/
theorem card_U_le_errOf {s : ℕ} (H : History V E s) (est : E → Pref)
    (slot : E → Fin s × Fin s)
    (h : ∀ e ∈ E₀, ¬ supported G D.F e → H.errOf est e (slot e)) :
    D.U.card ≤ (E₀.filter fun e => H.errOf est e (slot e)).card :=
  D.card_U_le_pred _ h

/-- **The error count splits into its bad-slot half and its mis-estimate half** (§3.3).  The set of
edges sitting in an error slot is covered by those whose slot is bad and those whose estimate is
wrong, so `|U(F)|` is at most the sum of the two counts. -/
theorem card_U_le_bad_add_mis {s : ℕ} (H : History V E s) (est : E → Pref)
    (slot : E → Fin s × Fin s)
    (h : ∀ e ∈ E₀, ¬ supported G D.F e → H.errOf est e (slot e)) :
    D.U.card ≤ (E₀.filter fun e => H.badFor e (slot e)).card +
      (E₀.filter fun e => est e ≠ H.pref e (slot e).1 (slot e).2).card := by
  refine le_trans (D.card_U_le_pred
    (fun e => H.badFor e (slot e) ∨ est e ≠ H.pref e (slot e).1 (slot e).2) ?_)
    (card_filter_or_le E₀ (fun e => H.badFor e (slot e))
      (fun e => est e ≠ H.pref e (slot e).1 (slot e).2))
  intro e he hns
  simpa [History.errOf] using h e he hns

/-- **The bad half is the §3.5 `lost` count.**  `lost` filters over *all* edges, and the instance's
edges are a subset, so restricting to `E₀` only shrinks it. -/
theorem card_filter_bad_le_lost {s : ℕ} (H : History V E s) (ρ : Sched E s) :
    (E₀.filter fun e => H.badFor e (ρ e)).card ≤ H.lost ρ := by
  rw [History.lost_def]
  refine Finset.card_le_card (fun e he => ?_)
  obtain ⟨-, hb⟩ := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩

/-- **The whole instance error count in the two halves §3.3 pays for**: `|U(F)| ≤ lost + #mis`, where
`lost` is the §3.5 bad-round count (Lemma 3.11 gives `lost·log 2 ≤ (2√2+4)t²√(mn) + 2m/t`) and `#mis`
is the number of edges whose assigned slot's estimate was wrong (Claim 3.12 pays this by `m/t`).  This
is the shape `error_count_le` consumes, with no per-edge premise left beyond Lemma 3.7's conclusion. -/
theorem card_U_le_lost_add_mis {s : ℕ} (H : History V E s) (est : E → Pref)
    (slot : E → Fin s × Fin s)
    (h : ∀ e ∈ E₀, ¬ supported G D.F e → H.errOf est e (slot e)) :
    D.U.card ≤ H.lost slot +
      (E₀.filter fun e => est e ≠ H.pref e (slot e).1 (slot e).2).card :=
  le_trans (D.card_U_le_bad_add_mis H est slot h)
    (Nat.add_le_add_right (card_filter_bad_le_lost (E₀ := E₀) H slot) _)

/-! ## The cross-call summation

An edge whose projection is unsupported at depth one is not charged at its own call's slot: by
`ProcChain.errOf_or_unsupp_child` the error, if any, is paid in the child call's schedule.  The
summation below is the machine form of the paper's per-call account: if every unsupported edge pays
its error at one of `J` levels (each level a call with its own schedule `ρ j` and estimate `estL j`),
then the instance's retained set is at most the total of the levels' own `lost + #mis` charges. -/

/-- **One level's charge.**  The `E₀`-edges whose error is paid at this level split into the level's
bad-round count and its mis-estimate count, exactly as in `card_U_le_lost_add_mis` but for the
restricted set `E₀.filter errOf` rather than the whole retained set. -/
theorem card_filter_errOf_le {s : ℕ} (H : History V E s) (est : E → Pref)
    (ρ : Sched E s) :
    (E₀.filter fun e => H.errOf est e (ρ e)).card ≤
      H.lost ρ + (E₀.filter fun e => est e ≠ H.pref e (ρ e).1 (ρ e).2).card := by
  classical
  have hsub : E₀.filter (fun e => H.errOf est e (ρ e)) ⊆
      (Finset.univ.filter fun e => H.badFor e (ρ e)) ∪
        (E₀.filter fun e => est e ≠ H.pref e (ρ e).1 (ρ e).2) := by
    intro e he
    obtain ⟨hE, herr⟩ := Finset.mem_filter.mp he
    rcases herr with hb | hm
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hE, hm⟩)
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  rw [History.lost_def]

/-- **The cross-call summation.**  If every input edge unsupported by the call's forest pays its
error at one of the levels `j < J` — level `j` being a call with its own schedule `ρ j` and estimate
`estL j` — then the retained set is at most the sum over levels of each level's `lost + #mis`
charge.  This is the form §3.6 needs: an edge unsupported at depth one is charged in the child call,
and summing the per-call counts over the chain bounds their union. -/
theorem card_U_le_sum_levels {s J : ℕ} (H : History V E s)
    (ρ : ℕ → Sched E s) (estL : ℕ → E → Pref)
    (hpay : ∀ e ∈ E₀, ¬ supported G D.F e →
      ∃ j ∈ Finset.range J, H.errOf (estL j) e (ρ j e)) :
    D.U.card ≤ ∑ j ∈ Finset.range J,
      (H.lost (ρ j) +
        (E₀.filter fun e => estL j e ≠ H.pref e (ρ j e).1 (ρ j e).2).card) := by
  classical
  refine le_trans (D.card_U_le_pred
    (fun e => ∃ j ∈ Finset.range J, H.errOf (estL j) e (ρ j e)) hpay) ?_
  have hsub : E₀.filter (fun e => ∃ j ∈ Finset.range J, H.errOf (estL j) e (ρ j e)) ⊆
      (Finset.range J).biUnion (fun j => E₀.filter fun e => H.errOf (estL j) e (ρ j e)) := by
    intro e he
    obtain ⟨hE, j, hj, herr⟩ := Finset.mem_filter.mp he
    exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_filter.mpr ⟨hE, herr⟩⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun j _ => ?_)
  exact card_filter_errOf_le H (estL j) (ρ j)

/-- **The summation against a uniform per-level charge.**  If every level's `lost + #mis` is at most
`B`, the instance's retained set is at most `J · B` — the per-call bound multiplied by the number of
calls along the chains. -/
theorem card_U_le_mul_of_sum_levels {s J : ℕ} (H : History V E s)
    (ρ : ℕ → Sched E s) (estL : ℕ → E → Pref)
    (hpay : ∀ e ∈ E₀, ¬ supported G D.F e →
      ∃ j ∈ Finset.range J, H.errOf (estL j) e (ρ j e))
    {B : ℝ} (hB : ∀ j ∈ Finset.range J,
      (H.lost (ρ j) : ℝ) +
        ((E₀.filter fun e => estL j e ≠ H.pref e (ρ j e).1 (ρ j e).2).card : ℝ) ≤ B) :
    (D.U.card : ℝ) ≤ J * B := by
  have h := D.card_U_le_sum_levels H ρ estL hpay
  have hcast : (D.U.card : ℝ) ≤
      ((∑ j ∈ Finset.range J, (H.lost (ρ j) +
        (E₀.filter fun e => estL j e ≠ H.pref e (ρ j e).1 (ρ j e).2).card) : ℕ) : ℝ) := by
    exact_mod_cast h
  refine le_trans hcast ?_
  have hsum : ((∑ j ∈ Finset.range J, (H.lost (ρ j) +
      (E₀.filter fun e => estL j e ≠ H.pref e (ρ j e).1 (ρ j e).2).card) : ℕ) : ℝ) ≤
      ∑ j ∈ Finset.range J, B := by
    push_cast
    exact Finset.sum_le_sum hB
  refine le_trans hsum ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **The instance's error premise, from the rounds and the sampling.**  §3.3's per-edge conclusion
(`¬supported → error`, i.e. Lemma 3.7) plus the two numeric halves — Lemma 3.11's `lost` bound and
§3.5's per-round mis-estimate allowances (`card_mis_le`) — give
`|U(F)| ≤ 10t²√(mn) + 4m/t` in ℝ.  This is the `errF` premise of
`Procedure.display_of_strategy_of_counts`, now produced rather than assumed. -/
theorem card_U_le_number_bound {s t : ℕ} (H : History V E s) (est : E → Pref)
    (slot : E → Fin s × Fin s) (mOf : Fin s × Fin s → ℕ) {m n : ℝ} (ht : 0 < t) (hm : 0 ≤ m)
    (hn : 0 ≤ n) (hmE : (Fintype.card E : ℝ) ≤ m)
    (h : ∀ e ∈ E₀, ¬ supported G D.F e → H.errOf est e (slot e))
    (hlost : (H.lost slot : ℝ) * Real.log 2 ≤
      (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 * Real.sqrt (m * n) + 2 * m / (t : ℝ))
    (hper : ∀ r : Fin s × Fin s,
      ((Finset.univ.filter fun e =>
        est e ≠ H.pref e (slot e).1 (slot e).2 ∧ slot e = r).card : ℝ) ≤
        (mOf r : ℝ) / (t : ℝ))
    (hsum : (∑ r, mOf r) ≤ Fintype.card E) :
    (D.U.card : ℝ) ≤ 10 * (t : ℝ) ^ 2 * Real.sqrt (m * n) + 4 * m / (t : ℝ) := by
  have ht' : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hmis : ((E₀.filter fun e => est e ≠ H.pref e (slot e).1 (slot e).2).card : ℝ) ≤
      m / (t : ℝ) := by
    have hsub : (E₀.filter (fun e => est e ≠ H.pref e (slot e).1 (slot e).2)).card ≤
        (Finset.univ.filter fun e => est e ≠ H.pref e (slot e).1 (slot e).2).card :=
      Finset.card_le_card (fun e he =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2⟩)
    have h1 := card_mis_le (E := E) (t := t) slot
      (fun e => est e ≠ H.pref e (slot e).1 (slot e).2) mOf hper hsum
    refine le_trans (by exact_mod_cast hsub) (le_trans h1 ?_)
    exact div_le_div_of_nonneg_right hmE ht'.le
  have hU : (D.U.card : ℝ) ≤ (H.lost slot : ℝ) +
      ((E₀.filter fun e => est e ≠ H.pref e (slot e).1 (slot e).2).card : ℝ) := by
    have hsplit := D.card_U_le_lost_add_mis H est slot h
    calc (D.U.card : ℝ) ≤ ((H.lost slot +
          (E₀.filter fun e => est e ≠ H.pref e (slot e).1 (slot e).2).card : ℕ) : ℝ) := by
          exact_mod_cast hsplit
      _ = (H.lost slot : ℝ) +
          ((E₀.filter fun e => est e ≠ H.pref e (slot e).1 (slot e).2).card : ℝ) := by
          push_cast; ring
  exact error_count_le_of_U_add (U := (D.U.card : ℝ)) (lost := (H.lost slot : ℝ))
    (err2 := ((E₀.filter fun e => est e ≠ H.pref e (slot e).1 (slot e).2).card : ℝ))
    (t := (t : ℝ)) ht' hm hn hU hlost hmis

/-- **The instance bound from the global mis-estimate count.**  `card_U_le_number_bound` assembles its
`hmis` half from per-round fiber allowances; the *global* count `#mis ≤ |E|/t` — what the sampling
produces in one piece (`card_mis_le_of_claim312`) — is enough: restricting to `E₀` only shrinks it,
and `|E| ≤ m` absorbs the last step. -/
theorem card_U_le_number_bound_of_all_mis {s t : ℕ} (H : History V E s)
    (est : E → Pref) (slot : E → Fin s × Fin s) {m n : ℝ} (ht : 0 < t) (hm : 0 ≤ m)
    (hn : 0 ≤ n) (hmE : (Fintype.card E : ℝ) ≤ m)
    (h : ∀ e ∈ E₀, ¬ supported G D.F e → H.errOf est e (slot e))
    (hlost : (H.lost slot : ℝ) * Real.log 2 ≤
      (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 * Real.sqrt (m * n) + 2 * m / (t : ℝ))
    (hmis : ((Finset.univ.filter fun e =>
      est e ≠ H.pref e (slot e).1 (slot e).2).card : ℝ) ≤
      (Fintype.card E : ℝ) / (t : ℝ)) :
    (D.U.card : ℝ) ≤ 10 * (t : ℝ) ^ 2 * Real.sqrt (m * n) + 4 * m / (t : ℝ) := by
  have ht' : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hmis' : ((E₀.filter fun e => est e ≠ H.pref e (slot e).1 (slot e).2).card : ℝ) ≤
      m / (t : ℝ) := by
    have hsub : (E₀.filter (fun e => est e ≠ H.pref e (slot e).1 (slot e).2)).card ≤
        (Finset.univ.filter fun e => est e ≠ H.pref e (slot e).1 (slot e).2).card :=
      Finset.card_le_card (fun e he =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2⟩)
    refine le_trans (by exact_mod_cast hsub) (le_trans hmis ?_)
    exact div_le_div_of_nonneg_right hmE ht'.le
  have hU : (D.U.card : ℝ) ≤ (H.lost slot : ℝ) +
      ((E₀.filter fun e => est e ≠ H.pref e (slot e).1 (slot e).2).card : ℝ) := by
    have hsplit := D.card_U_le_lost_add_mis H est slot h
    calc (D.U.card : ℝ) ≤ ((H.lost slot +
          (E₀.filter fun e => est e ≠ H.pref e (slot e).1 (slot e).2).card : ℕ) : ℝ) := by
          exact_mod_cast hsplit
      _ = (H.lost slot : ℝ) +
          ((E₀.filter fun e => est e ≠ H.pref e (slot e).1 (slot e).2).card : ℝ) := by
          push_cast; ring
  exact error_count_le_of_U_add (U := (D.U.card : ℝ)) (lost := (H.lost slot : ℝ))
    (err2 := ((E₀.filter fun e => est e ≠ H.pref e (slot e).1 (slot e).2).card : ℝ))
    (t := (t : ℝ)) ht' hm hn hU hlost hmis'

/-- **§3.3's instance error premise, with the estimate accounted for by §3.5's sampling.**  Beyond
Lemma 3.7's per-edge conclusion and Lemma 3.11's `lost` bound, the only inputs are the driver's
sampling facts: per round, the true preference vector `H.pref · —` and the per-edge estimate `est` are
both members of a candidate family `A r`, and the estimate agrees with the truth on Claim 3.12's
sample `S r` (the queried edges).  Then `|U(F)| ≤ 10t²√(mn) + 4m/t`, and `err2 ≤ m/t` is no longer
assumed anywhere: `card_mis_le_of_claim312` produces the count.  The estimate is per edge, exactly the
coordinate type of Claim 3.12. -/
theorem card_U_le_number_bound_of_sampling {s t : ℕ} (H : History V E s)
    (est : E → Pref) (slot : E → Fin s × Fin s) {m n : ℝ} (ht : 2 ≤ t) (hm : 0 ≤ m)
    (hn : 0 ≤ n) (hmE : (Fintype.card E : ℝ) ≤ m)
    (h : ∀ e ∈ E₀, ¬ supported G D.F e → H.errOf est e (slot e))
    (hlost : (H.lost slot : ℝ) * Real.log 2 ≤
      (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 * Real.sqrt (m * n) + 2 * m / (t : ℝ))
    (A : ∀ r : Fin s × Fin s, Finset ({e : E // slot e = r} → Pref))
    (htruth : ∀ r : Fin s × Fin s,
      (fun x : {e : E // slot e = r} => H.pref x.1 (slot x.1).1 (slot x.1).2) ∈ A r)
    (hest : ∀ r : Fin s × Fin s, (fun x : {e : E // slot e = r} => est x.1) ∈ A r) :
    ∃ S : ∀ r : Fin s × Fin s, Finset {e : E // slot e = r},
      (∀ r, (S r).card ≤ 2 * t * (Nat.ceil (Real.log ((A r).card : ℝ)) + 1)) ∧
      ((∀ r (x : {e : E // slot e = r}), x ∈ S r → est x.1 = H.pref x.1 r.1 r.2) →
        (D.U.card : ℝ) ≤ 10 * (t : ℝ) ^ 2 * Real.sqrt (m * n) + 4 * m / (t : ℝ)) := by
  obtain ⟨S, hScard, hcount⟩ :=
    card_mis_le_of_claim312 ht slot (fun e => H.pref e (slot e).1 (slot e).2)
      est A htruth hest
  refine ⟨S, hScard, fun hagree => ?_⟩
  refine D.card_U_le_number_bound_of_all_mis H est slot (by omega) hm hn hmE h hlost ?_
  refine hcount (fun r x hx => ?_)
  rw [x.2]
  exact hagree r x hx

end RoundData

/-- **Reindexing the children.**  A call's children can be relabelled along any equivalence of
their index type; every field is a transport of the corresponding field.  This is what turns the
`(round, child)` index of `RoundData.toCall` into the `Fin N` index a `Strategy` wants. -/
def reindex {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι') (O : CallOut G ι) :
    CallOut G ι' where
  P := O.P
  E₀ := O.E₀
  F := O.F
  kidE := fun i => O.kidE (e.symm i)
  kidV := fun i => O.kidV (e.symm i)
  drop := O.drop
  hFsub := O.hFsub
  hforest := O.hforest
  hFcard := O.hFcard
  hkidE := fun i => O.hkidE (e.symm i)
  hkidV := fun i => O.hkidV (e.symm i)
  hkidEdisj := fun i j hij =>
    O.hkidEdisj _ _ (fun h => hij (e.symm.injective h))
  hFkid := fun i => O.hFkid (e.symm i)
  hUkid := fun i => O.hUkid (e.symm i)
  hdropE := O.hdropE
  hdrop_supp := O.hdrop_supp
  hFdrop := O.hFdrop
  hUdrop := O.hUdrop
  hkid_drop := fun i => O.hkid_drop (e.symm i)
  hcover := by
    intro x hx
    rcases O.hcover x hx with hF | hU | hS | ⟨i, hi⟩
    · exact Or.inl hF
    · exact Or.inr (Or.inl hU)
    · exact Or.inr (Or.inr (Or.inl hS))
    · exact Or.inr (Or.inr (Or.inr ⟨e i, by simpa using hi⟩))
  hshrink := by
    have h : (∑ i : ι', (O.kidV (e.symm i)).card) = ∑ j : ι, (O.kidV j).card :=
      Equiv.sum_comp e.symm (fun j => (O.kidV j).card)
    rw [h]
    exact O.hshrink

end CallOut

namespace Strategy

/-- **Any family of round data, one per instance, is a well-formed strategy.**  The children are
indexed by `Fin (t² · k)` (a `(round, child)` pair recoded), and the call at `(P, E₀)` answers
about that very instance by construction.  This is the last packaging step between §3's rounds and
§3.6's level chain: the numeric content of the rounds enters only through `errF`/`inF` in
`display_of_strategy_of_calls`. -/
noncomputable def ofRoundData {k t : ℕ}
    (RD : ∀ (P : Finset V) (E₀ : Finset E), CallOut.RoundData G P E₀ (Fin k) t) : Strategy G :=
  fun P E₀ => ⟨t ^ 2 * k, (RD P E₀).toCall.reindex finProdFinEquiv⟩

theorem ofRoundData_wf {k t : ℕ}
    (RD : ∀ (P : Finset V) (E₀ : Finset E), CallOut.RoundData G P E₀ (Fin k) t) :
    Wf (ofRoundData RD) :=
  fun P E₀ => ⟨rfl, rfl⟩

end Strategy

end DLMST