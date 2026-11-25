import DLMST.Procedure
import DLMST.Dispatch

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

namespace CallOut

/-- **The round data of one instance.**  `t²` rounds, each returning a forest piece `Fr r` and
dispatching edges to `ι` children with inputs `inp r i`; every edge of `E₀` is kept, retained, or
lies in some child's input; the children's inputs are pairwise disjoint; the union of the round
forests is a forest of at most `|P|` edges; `P'` is the shared portal set within the portal budget.
`P` and `E₀` are parameters, so the data can be attached to the instance it belongs to. -/
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
    e ∈ unsupp G (Finset.univ.biUnion Fr) ∨ ∃ p : Fin (t ^ 2) × ι, e ∈ inp p.1 p.2
  hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin (t ^ 2) × ι)))
    (fun p : Fin (t ^ 2) × ι => inp p.1 p.2)

namespace RoundData

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ} {P : Finset V} {E₀ : Finset E}
  (D : RoundData G P E₀ ι t)

/-- The forest the call returns: the union of the rounds' forest pieces. -/
noncomputable def F : Finset E := Finset.univ.biUnion D.Fr

/-- The instance's retained edges — the paper's `U(F)`, restricted to this instance. -/
noncomputable def U : Finset E := unsupp G D.F ∩ E₀

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

/-- **The call assembled from the round data.** -/
noncomputable def toCall : CallOut G (Fin (t ^ 2) × ι) :=
  ofClass P E₀ D.F D.P' D.cls D.hsubF D.hforest D.hFcard D.hP' D.hbudget
    (by
      intro e he hcl
      unfold cls at hcl
      split at hcl
      next h =>
        rcases h with hF | hU
        · exact Or.inl hF
        · exact Or.inr (Finset.mem_inter.mp hU).1
      next h =>
        have hno := D.childOf_eq_none hcl
        rcases D.hcover e he with hF | hU | hE
        · exact absurd (Or.inl hF) h
        · exact absurd (Or.inr (Finset.mem_inter.mpr ⟨hU, he⟩)) h
        · exact absurd hE hno)
    (by
      intro e he p hcl
      unfold cls at hcl
      split at hcl
      next _ => exact absurd hcl (by simp)
      next h =>
        refine ⟨fun hF => h (Or.inl hF), fun hU => ?_⟩
        exact h (Or.inr (Finset.mem_inter.mpr ⟨hU, he⟩)))

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

/-- The round input total is the double sum over rounds and children. -/
theorem sum_input_eq :
    (∑ p : Fin (t ^ 2) × ι, (D.inp' p).card) = ∑ r, ∑ i, (D.inp r i).card :=
  Fintype.sum_prod_type (f := fun p : Fin (t ^ 2) × ι => (D.inp' p).card)

/-- **§3.6's display data in the rounds' terms**: the call's kept, retained and dispatched pieces
partition its input edge set. -/
theorem partition :
    D.F.card + (D.toCall.U).card + ∑ p, (D.toCall.kidE p).card = E₀.card :=
  CallOut.partition_eq D.toCall

/-- **The "rest" of one instance**: everything not kept is either retained or dispatched, so
`|U| + Σᵢ|Eᵢ| = |E₀| − |F|`.  This is the quantity §3.6 bounds per level. -/
theorem U_add_kids :
    (D.toCall.U).card + ∑ p, (D.toCall.kidE p).card = E₀.card - D.F.card := by
  have h := D.partition
  have hsub : D.F.card ≤ E₀.card := Finset.card_le_card D.hsubF
  omega

/-- The rounds' union is a forest as soon as the kept edges satisfy the Kruskal-order criterion —
the selection rule the certificate procedure's rounds implement (`isForest_of_forall_not_conn_below`).
Establishing that criterion from the rounds' own acceptance test is the remaining part of this
identification; `RoundData` carries forestness as data until then. -/
theorem isForest_F
    (h : ∀ e ∈ D.F, ¬ Conn G (D.F.filter (fun f => f < e)) (G.src e) (G.dst e)) :
    IsForest G D.F :=
  isForest_of_forall_not_conn_below h

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
  hFsub := O.hFsub
  hforest := O.hforest
  hFcard := O.hFcard
  hkidE := fun i => O.hkidE (e.symm i)
  hkidV := fun i => O.hkidV (e.symm i)
  hkidEdisj := fun i j hij =>
    O.hkidEdisj _ _ (fun h => hij (e.symm.injective h))
  hFkid := fun i => O.hFkid (e.symm i)
  hUkid := fun i => O.hUkid (e.symm i)
  hcover := by
    intro x hx
    rcases O.hcover x hx with hF | hU | ⟨i, hi⟩
    · exact Or.inl hF
    · exact Or.inr (Or.inl hU)
    · exact Or.inr (Or.inr ⟨e i, by simpa using hi⟩)
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