import DLMST.Filtering

/-!
# The fourth bucket: dropping the edges the forest supports

`CallOut` (in `Procedure.lean`) classifies every input edge into exactly three buckets — kept in the
forest, retained (`U(F)`), or dispatched to a child.  The paper's procedure has **four**: every edge
that the returned forest *supports* and that is not kept is simply discarded, and only rejected edges
are propagated.  That difference is not cosmetic: with three buckets the display's left-hand side
`|F| + |U(F)| + Σᵢ|Eᵢ|` equals `|E₀|` (`CallFromRounds.sum_kidE`), so the bound `εm + C√(mn)` can
only hold when the instance itself is small, while the paper's whole point is that the two large
buckets — supported-and-dropped — are paid for by nothing.

This file states the accounting with the missing bucket so that the claim is visible and checkable:

* `CallPart` — the four buckets plus the disjointness and cover fields, with the one new hypothesis
  that a dropped edge is supported by the kept forest (the paper's "filter out every supported edge
  outside `F`");
* `CallPart.partition` — `|F| + |U| + |drop| + Σ|kid| = |E₀|`;
* `CallPart.lhs_le` — the display's left-hand side is at most `|E₀|`, with the deficit exactly the
  dropped edges, so it can be far smaller than `m` — which is what the paper's count needs.

Not here: the procedure that produces the four buckets (the model gap `CallFromRounds` documents).
-/

namespace DLMST

open Classical

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] {G : WGraph V E}

/-- **A four-bucket accounting of one call.**  `F` is the returned forest, `U` the retained set, `kid`
the children's inputs, and `drop` the edges discarded because `F` already supports them.  The cover is
partitional: each edge of the instance lies in exactly one bucket. -/
structure CallPart (G : WGraph V E) (E₀ : Finset E) (ι : Type*) where
  F : Finset E
  U : Finset E
  kid : ι → Finset E
  drop : Finset E
  hFsub : F ⊆ E₀
  hUsub : U ⊆ E₀
  hkidsub : ∀ i, kid i ⊆ E₀
  hdropsub : drop ⊆ E₀
  hFdisjU : Disjoint F U
  hFdisjK : ∀ i, Disjoint F (kid i)
  hUdisjK : ∀ i, Disjoint U (kid i)
  hFdisjD : Disjoint F drop
  hUdisjD : Disjoint U drop
  hKdisjD : ∀ i, Disjoint (kid i) drop
  hKdisj : ∀ i j, i ≠ j → Disjoint (kid i) (kid j)
  hcover : ∀ e ∈ E₀, e ∈ F ∨ e ∈ U ∨ e ∈ drop ∨ ∃ i, e ∈ kid i
  hdrop_supported : ∀ e ∈ drop, supported G F e

namespace CallPart

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E₀ : Finset E} (C : CallPart G E₀ ι)

/-- The instance is the disjoint union of the four buckets. -/
theorem cover_eq : E₀ = C.F ∪ C.U ∪ C.drop ∪ Finset.univ.biUnion C.kid := by
  ext e
  constructor
  · intro he
    rcases C.hcover e he with hF | hU | hD | ⟨i, hi⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hF))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hU))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hD)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩)
  · intro he
    rcases Finset.mem_union.mp he with h | hk
    · rcases Finset.mem_union.mp h with h | hD
      · rcases Finset.mem_union.mp h with hF | hU
        · exact C.hFsub hF
        · exact C.hUsub hU
      · exact C.hdropsub hD
    · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hk
      exact C.hkidsub i hi

/-- **The four-bucket partition identity.** -/
theorem partition :
    C.F.card + C.U.card + C.drop.card + ∑ i, (C.kid i).card = E₀.card := by
  have hD1 : Disjoint (C.F ∪ C.U) C.drop :=
    Finset.disjoint_union_left.mpr ⟨C.hFdisjD, C.hUdisjD⟩
  have hFUK : Disjoint (C.F ∪ C.U) (Finset.univ.biUnion C.kid) := by
    rw [Finset.disjoint_left]
    intro x hx hxk
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hxk
    rcases Finset.mem_union.mp hx with hF | hU
    · exact Finset.disjoint_left.mp (C.hFdisjK i) hF hi
    · exact Finset.disjoint_left.mp (C.hUdisjK i) hU hi
  have hDK : Disjoint C.drop (Finset.univ.biUnion C.kid) := by
    rw [Finset.disjoint_left]
    intro x hx hxk
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hxk
    exact Finset.disjoint_left.mp (C.hKdisjD i) hi hx
  have hD2 : Disjoint ((C.F ∪ C.U) ∪ C.drop) (Finset.univ.biUnion C.kid) :=
    Finset.disjoint_union_left.mpr ⟨hFUK, hDK⟩
  have hKcard : (Finset.univ.biUnion C.kid).card = ∑ i, (C.kid i).card := by
    rw [Finset.card_biUnion]
    intro i _ j _ hij
    exact C.hKdisj i j hij
  calc C.F.card + C.U.card + C.drop.card + ∑ i, (C.kid i).card
      = C.F.card + C.U.card + C.drop.card + (Finset.univ.biUnion C.kid).card := by
        rw [hKcard]
    _ = (C.F ∪ C.U).card + C.drop.card + (Finset.univ.biUnion C.kid).card := by
        rw [Finset.card_union_of_disjoint C.hFdisjU]
    _ = ((C.F ∪ C.U) ∪ C.drop).card + (Finset.univ.biUnion C.kid).card := by
        rw [Finset.card_union_of_disjoint hD1]
    _ = (((C.F ∪ C.U) ∪ C.drop) ∪ Finset.univ.biUnion C.kid).card := by
        rw [Finset.card_union_of_disjoint hD2]
    _ = E₀.card := by rw [← C.cover_eq]

/-- **The display's left-hand side in the paper's accounting**: it is at most the instance's size, with
the gap exactly the edges discarded as supported.  In the three-bucket model `drop = ∅` and this is an
equality (`CallFromRounds.sum_kidE`); the paper's saving is precisely `drop`. -/
theorem lhs_le : C.F.card + C.U.card + ∑ i, (C.kid i).card ≤ E₀.card := by
  have h := C.partition
  omega

/-- **The three-bucket model is the `drop = ∅` case** of this accounting: if nothing is discarded, the
left-hand side is the whole input, which is the identity `CallFromRounds.sum_kidE` makes explicit. -/
theorem lhs_eq_of_no_drop (hempty : C.drop = ∅) :
    C.F.card + C.U.card + ∑ i, (C.kid i).card = E₀.card := by
  have h := C.partition
  rw [hempty] at h
  simpa using h

end CallPart

end DLMST