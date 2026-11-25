import Mathlib

/-!
# Lemma 3.2, first sentence: `|D| ≤ r²n` declared edges, `|P′| ≤ 2n/r` portals

§3.2 processes a batch `B` of edges.  For every vertex `v` it keeps the `k = r²` lightest
*representatives* of the groups of incident batch edges and writes `Sv` for the neighbours they
reach.  Two counting claims follow:

* `|D| ≤ kn = r²n`, because each of the `n` vertices declares at most `k` edges (`declared_card`);
* the portal set `P′` has `|P′| ≤ 2n/r` (`portal_bound`).

The second is the only non-trivial combinatorics in §3.2, and the paper's justification is one
paragraph: *while some vertex lies in at least `r` uncovered sets, select it as a portal.  Each
selection covers at least `r` additional sets, so this step selects at most `n/r` portals.  At
termination each vertex belongs to fewer than `r` uncovered sets, so the remaining sets have fewer
than `nr` incidences in total; each has size `k = r²`, so fewer than `n/r` sets remain, and one vertex
is selected from each.  Altogether `|P′| ≤ 2n/r`.*

This file checks that paragraph.  The loop is modelled by the inductive predicate `Greedy` — a set is
`Greedy 𝓢 S r P` if the loop could have produced `P` by repeated legal selections — and the three
steps of the paragraph become `Greedy.card_le` (at most `n/r` selections), `exists_greedy_maximal`
(termination really does give the `< r` bound) and `incidence` (the double count).

Two things the paragraph passes over in silence are made explicit:

1. the loop's output must be *maximal*, which the paper gets from "at termination" but which
   `Greedy` does not state, so it is recovered by taking a largest greedy set;
2. one vertex has to be *chosen* from each remaining uncovered set.  The formal statement asks only
   for the existence of a portal set with the two properties, which is all §3.2 and Lemma 3.2 use.

The bound is written `r * P'.card ≤ 2 * Fintype.card α`, i.e. `|P′| ≤ 2n/r`, so that no division and
no real arithmetic appear.  What is *not* formalised here: that `S` comes from batch representatives of
admissible edges, that sets of size `< k` are ignored, and everything about spokes and projections —
this file is only the counting.
-/

namespace DLMST

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α] {𝓢 : Finset α} {S : α → Finset α}

/-- **The uncovered sets** (paper, §3.2: a set `Sv` is "covered once it contains a selected portal"):
the members of the family `𝓢` whose set is still disjoint from the portals `P`. -/
def missed (𝓢 : Finset α) (S : α → Finset α) (P : Finset α) : Finset α :=
  𝓢.filter fun v => Disjoint (S v) P

theorem mem_missed {𝓢 : Finset α} {S : α → Finset α} {P : Finset α} {u : α} :
    u ∈ missed 𝓢 S P ↔ u ∈ 𝓢 ∧ Disjoint (S u) P := Finset.mem_filter

/-- **The §3.2 selection loop.**  `Greedy 𝓢 S r P` means "the loop can stop with portal set `P`":
either `P = ∅`, or `P = insert v Q` where `Q` is already greedy and `v` lay in at least `r` sets that
`Q` still leaves uncovered. -/
inductive Greedy (𝓢 : Finset α) (S : α → Finset α) (r : ℕ) : Finset α → Prop where
  | empty : Greedy 𝓢 S r ∅
  | step (P : Finset α) (hP : Greedy 𝓢 S r P) (v : α)
      (hv : r ≤ ((missed 𝓢 S P).filter fun u => v ∈ S u).card) : Greedy 𝓢 S r (insert v P)

/-- **"Each selection covers at least `r` additional sets, so this step selects at most `n/r`
portals"** (§3.2, machine-checked).  The invariant also charges the sets still uncovered, which is
what closes the induction: a selection trades `r` uncovered sets for one portal. -/
theorem Greedy.card_le (hr : 0 < r) {P : Finset α} (hP : Greedy 𝓢 S r P) :
    r * P.card + (missed 𝓢 S P).card ≤ 𝓢.card := by
  induction hP with
  | empty =>
      have h1 : (missed 𝓢 S (∅ : Finset α)).card ≤ 𝓢.card := Finset.card_filter_le _ _
      rw [Finset.card_empty, Nat.mul_zero, zero_add]
      exact h1
  | step P hP v hv ih =>
      classical
      -- a vertex already chosen covers every set containing it, so it is selected at most once
      obtain ⟨x, hx⟩ :=
        Finset.card_pos.mp (by omega : 0 < ((missed 𝓢 S P).filter fun y => v ∈ S y).card)
      obtain ⟨hxU, hxv⟩ := Finset.mem_filter.mp hx
      have hdis := (mem_missed.mp hxU).2
      have hvn : v ∉ P := fun hvP => (Finset.disjoint_left.mp hdis) hxv hvP
      -- the sets `v` newly covers are exactly the uncovered ones containing `v`
      have hEq : missed 𝓢 S (insert v P) = (missed 𝓢 S P).filter fun y => v ∉ S y := by
        ext w
        simp only [missed, Finset.mem_filter]
        rw [Finset.disjoint_insert_right]
        tauto
      have hsplit : ((missed 𝓢 S P).filter fun y => v ∈ S y).card
          + ((missed 𝓢 S P).filter fun y => v ∉ S y).card = (missed 𝓢 S P).card :=
        Finset.card_filter_add_card_filter_not (fun y => v ∈ S y)
      rw [hEq, Finset.card_insert_of_notMem hvn]
      simp only [Nat.mul_add, Nat.mul_one]
      omega

/-- **"At termination, each vertex belongs to fewer than `r` uncovered sets"** (§3.2,
machine-checked).  The loop description does not say the result is maximal, so it is recovered by
taking a largest greedy set: extending it would contradict maximality. -/
theorem exists_greedy_maximal (hr : 0 < r) :
    ∃ P : Finset α, Greedy 𝓢 S r P ∧
      ∀ v, ((missed 𝓢 S P).filter fun u => v ∈ S u).card < r := by
  classical
  obtain ⟨P, hPmem, hPmax⟩ :=
    Finset.exists_max_image (Finset.univ.filter fun P : Finset α => Greedy 𝓢 S r P)
      (fun P : Finset α => P.card)
      ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Greedy.empty⟩⟩
  obtain ⟨_, hPg⟩ := Finset.mem_filter.mp hPmem
  refine ⟨P, hPg, fun v => ?_⟩
  by_contra h
  have hge : r ≤ ((missed 𝓢 S P).filter fun u => v ∈ S u).card := by omega
  obtain ⟨x, hx⟩ :=
    Finset.card_pos.mp (by omega : 0 < ((missed 𝓢 S P).filter fun y => v ∈ S y).card)
  obtain ⟨hxU, hxv⟩ := Finset.mem_filter.mp hx
  have hdis := (mem_missed.mp hxU).2
  have hvn : v ∉ P := fun hvP => (Finset.disjoint_left.mp hdis) hxv hvP
  have hle := hPmax (insert v P)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Greedy.step P hPg v hge⟩)
  rw [Finset.card_insert_of_notMem hvn] at hle
  omega

/-- **The incidence double count** (paper, §3.2: "the remaining sets have fewer than `nr` incidences
in total", machine-checked): counting `{(u, x) | u ∈ U, x ∈ Su}` by rows and then by columns. -/
theorem incidence (U : Finset α) (S : α → Finset α) :
    U.sum (fun u => (S u).card) =
      (U.biUnion S).sum fun x => (U.filter fun u => x ∈ S u).card := by
  classical
  have h1 : ∀ u : α, (S u).card =
      (Finset.univ : Finset α).sum fun x => if x ∈ S u then (1 : ℕ) else 0 := by
    intro u
    have hf : (Finset.univ : Finset α).filter (fun x : α => x ∈ S u) = S u := by
      ext x
      simp only [Finset.mem_univ, Finset.mem_filter, true_and]
    rw [← Finset.sum_filter, hf, Finset.card_eq_sum_ones]
  have h2 : ∀ x : α, U.sum (fun u => if x ∈ S u then (1 : ℕ) else 0) =
      (U.filter fun u => x ∈ S u).card := by
    intro x
    rw [← Finset.sum_filter, Finset.card_eq_sum_ones]
  have hzero : ∀ x ∉ U.biUnion S, (U.filter fun u => x ∈ S u).card = 0 := by
    intro x hx
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro u hu huS
    exact hx (Finset.mem_biUnion.mpr ⟨u, hu, huS⟩)
  have hsd : ((Finset.univ : Finset α) \ U.biUnion S).sum
      (fun x => (U.filter fun u => x ∈ S u).card)
      + (U.biUnion S).sum (fun x => (U.filter fun u => x ∈ S u).card)
      = (Finset.univ : Finset α).sum (fun x => (U.filter fun u => x ∈ S u).card) :=
    Finset.sum_sdiff (Finset.subset_univ (U.biUnion S))
  have hz : ((Finset.univ : Finset α) \ U.biUnion S).sum
      (fun x => (U.filter fun u => x ∈ S u).card) = 0 :=
    Finset.sum_eq_zero fun x hx => hzero x (by simpa using hx)
  calc U.sum (fun u => (S u).card)
      = U.sum (fun u => (Finset.univ : Finset α).sum fun x => if x ∈ S u then (1 : ℕ) else 0) :=
        Finset.sum_congr rfl fun u _ => h1 u
    _ = (Finset.univ : Finset α).sum fun x => U.sum (fun u => if x ∈ S u then (1 : ℕ) else 0) :=
        Finset.sum_comm
    _ = (Finset.univ : Finset α).sum fun x => (U.filter fun u => x ∈ S u).card :=
        Finset.sum_congr rfl fun x _ => h2 x
    _ = (U.biUnion S).sum fun x => (U.filter fun u => x ∈ S u).card := by omega

/-- **`|D| ≤ kn`** (paper, Lemma 3.2: "each vertex selects at most `k` edges, so `|D| ≤ kn`",
machine-checked).  The declared set is the union over vertices of their chosen representatives. -/
theorem declared_card (𝓢 : Finset α) (sel : α → Finset α) (k : ℕ)
    (hsel : ∀ v ∈ 𝓢, (sel v).card ≤ k) : (𝓢.biUnion sel).card ≤ k * Fintype.card α := by
  have h1 : (𝓢.biUnion sel).card ≤ 𝓢.sum (fun v => (sel v).card) := Finset.card_biUnion_le
  have h2 : 𝓢.sum (fun v => (sel v).card) ≤ 𝓢.sum (fun _ => k) :=
    Finset.sum_le_sum fun v hv => hsel v hv
  have h3 : 𝓢.sum (fun _ => k) = 𝓢.card * k := Finset.sum_const_nat (fun _ _ => rfl)
  have h4 : 𝓢.card * k ≤ Fintype.card α * k := Nat.mul_le_mul_right _ (Finset.card_le_univ 𝓢)
  have h5 : Fintype.card α * k = k * Fintype.card α := Nat.mul_comm _ _
  omega

/-- **The portal bound** (paper, Lemma 3.2: "selects a set `P′` of at most `2n/r` portals",
machine-checked).  If every member of the family `𝓢` has at least `r²` elements, then some set of at
most `2n/r` vertices meets every member of `𝓢`.  The `r²` is the paper's `k = r²` representatives per
vertex and `n = Fintype.card α` its vertex count. -/
theorem portal_bound (hr : 0 < r) (hk : ∀ u ∈ 𝓢, r * r ≤ (S u).card) :
    ∃ P : Finset α, (∀ u ∈ 𝓢, (S u ∩ P).Nonempty) ∧ r * P.card ≤ 2 * Fintype.card α := by
  classical
  obtain ⟨P, hPg, hPmax⟩ := exists_greedy_maximal (𝓢 := 𝓢) (S := S) hr
  let U : Finset α := missed 𝓢 S P
  have hUsub : U ⊆ 𝓢 := Finset.filter_subset _ _
  have hUmax : ∀ x, (U.filter fun u => x ∈ S u).card < r := hPmax
  have hr2 : r ≤ r * r := Nat.le_mul_of_pos_right r hr
  -- every leftover set is large, so it has a vertex to patch with
  have hUex : ∀ u, u ∈ U → ∃ x, x ∈ S u := by
    intro u hu
    have hcard := hk u (hUsub hu)
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < (S u).card)
    exact ⟨x, hx⟩
  -- one vertex patched onto each leftover set
  let f : { u // u ∈ U } → α := fun w => Classical.choose (hUex w.1 w.2)
  let Q : Finset α := U.attach.image f
  have hQ : Q.card ≤ U.card := Nat.le_trans Finset.card_image_le (Nat.le_of_eq Finset.card_attach)
  refine ⟨P ∪ Q, ?_, ?_⟩
  · intro u hu
    by_cases huU : u ∈ U
    · have hmem : Classical.choose (hUex u huU) ∈ P ∪ Q :=
        Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
          ⟨⟨u, huU⟩, Finset.mem_attach U ⟨u, huU⟩, rfl⟩))
      exact ⟨Classical.choose (hUex u huU),
        Finset.mem_inter.mpr ⟨Classical.choose_spec (hUex u huU), hmem⟩⟩
    · have hdp : ¬ Disjoint (S u) P :=
        fun hh => huU (mem_missed.mpr ⟨hu, hh⟩)
      obtain ⟨x, hxS, hxP⟩ := Finset.not_disjoint_iff.mp hdp
      exact ⟨x, Finset.mem_inter.mpr ⟨hxS, Finset.mem_union.mpr (Or.inl hxP)⟩⟩
  · -- "this step selects at most `n/r` portals"
    have hp : r * P.card ≤ 𝓢.card := by
      have := Greedy.card_le hr hPg
      omega
    -- "each vertex belongs to fewer than `r` uncovered sets", so fewer than `nr` incidences
    have hdeg : ∀ x, (U.filter fun u => x ∈ S u).card ≤ r - 1 := by
      intro x
      have hx := hUmax x
      omega
    have hsum : U.card * (r * r) ≤ Fintype.card α * (r - 1) := by
      have h1 : U.card * (r * r) ≤ U.sum (fun u => (S u).card) := by
        have h : U.sum (fun _ => r * r) = U.card * (r * r) := Finset.sum_const_nat (fun _ _ => rfl)
        refine Nat.le_trans h.symm.le ?_
        exact Finset.sum_le_sum fun u hu => hk u (hUsub hu)
      have hd := incidence U S
      have h3 : (U.biUnion S).sum (fun x => (U.filter fun u => x ∈ S u).card)
          ≤ (U.biUnion S).sum (fun _ => r - 1) :=
        Finset.sum_le_sum fun x _ => hdeg x
      have h4 : (U.biUnion S).sum (fun _ => r - 1) = (U.biUnion S).card * (r - 1) :=
        Finset.sum_const_nat (fun _ _ => rfl)
      have h6 : (U.biUnion S).card * (r - 1) ≤ Fintype.card α * (r - 1) :=
        Nat.mul_le_mul_right _ (Finset.card_le_univ _)
      omega
    have hge : (U.card * r) * r ≤ Fintype.card α * r := by
      calc (U.card * r) * r = U.card * (r * r) := Nat.mul_assoc _ _ _
        _ ≤ Fintype.card α * (r - 1) := hsum
        _ ≤ Fintype.card α * r := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    have hU : U.card * r ≤ Fintype.card α := Nat.le_of_mul_le_mul_right hge hr
    calc r * (P ∪ Q).card ≤ r * (P.card + Q.card) :=
        Nat.mul_le_mul_left _ (Finset.card_union_le P Q)
      _ = r * P.card + r * Q.card := Nat.mul_add _ _ _
      _ ≤ 𝓢.card + Fintype.card α :=
        Nat.add_le_add hp (Nat.le_trans (Nat.mul_le_mul_left r hQ) (by rw [Nat.mul_comm]; exact hU))
      _ ≤ 2 * Fintype.card α := by
          have : 𝓢.card ≤ Fintype.card α := Finset.card_le_univ 𝓢
          omega

end DLMST
