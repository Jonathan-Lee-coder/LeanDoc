import Mathlib

/-!
# Lemma 3.9 of Khanna–Putterman–Song, "A Deterministic Linear Time Algorithm for MST"

The paper needs to bound how many different *vectors of maxima* can arise when, for each of `m`
edge sets, an element is chosen maximally under one of several tie-breaking orders.  Two
ingredients feed that bound:

1. (this file) the **count vector** of maximisers already pins down the maximiser vector;
2. (`maxima_vectors_card` below) at most `C(n+m-1, m)` vectors of maxima occur — Fredman's
   vector-of-maxima bound, which the paper cites as [GYY80].

We machine-check both.  For (1) the paper gives a digraph on the maximisers, observing that
equal in/out-degree holds (that is exactly the count-vector hypothesis) while all arcs descend in
one fixed order, which no non-empty Eulerian digraph admits.  We obtain the same statement from the
shorter "sum of ranks" argument.  Note what that proof does *not* use: the second order plays no
role, so the lemma is a little stronger than the paper's statement — a hint that Lemma 3.9 is not
where the real difficulty of the paper lives.  For (2) the count vector is the multiset of the
maximiser vector's values, so `a ↦ Multiset.map a univ` is injective into `Sym (Fin n) m`, which
Mathlib counts by stars and bars.

The hypothesis is written as equality of the two multisets of values `Multiset.map a univ` and
`Multiset.map b univ`, which is the count vector packaged as one object; the paper writes it as
the pointwise cardinality identity `(univ.filter (a = x)).card = (univ.filter (b = x)).card`, and
the two are interchangeable because a multiset is determined by its element counts.
-/

namespace DLMST

open Finset

/-- One strict coordinate makes the whole sum strict.  Written directly rather than via
`Finset.sum_lt_sum`, whose signature has moved across Mathlib versions. -/
private lemma sum_lt_sum_at {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : ι → ℕ) (i : ι) (hef : ∀ j, f j ≤ g j) (hgt : f i < g i) :
    univ.sum f < univ.sum g := by
  classical
  have hf : univ.sum f = (univ.erase i).sum f + f i := (Finset.sum_erase_add univ f (mem_univ i)).symm
  have hg : univ.sum g = (univ.erase i).sum g + g i := (Finset.sum_erase_add univ g (mem_univ i)).symm
  rw [hf, hg]
  have hle : (univ.erase i).sum f ≤ (univ.erase i).sum g := sum_le_sum fun _ _ => hef _
  omega

/-- **Paper, Lemma 3.9 (machine-checked).**

`S i` is a family of vertex sets, `a i` the largest member of `S i` in the order coded by the
ranking `r₁`, and `b i` the largest member in some other order.  If the two assignments realise the
same count vector, then `a = b` pointwise. -/
theorem maxima_vector_determined
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (S : ι → Finset (Fin n))
    (r₁ : Fin n ≃ Fin n)
    (a b : ι → Fin n)
    (hb : ∀ i, b i ∈ S i)
    (hmax : ∀ i x, x ∈ S i → r₁ x ≤ r₁ (a i))
    (hm : Multiset.map a univ.val = Multiset.map b univ.val) :
    ∀ i, a i = b i := by
  classical
  -- `a i` dominates `b i`, because `b i ∈ S i` and `a i` is the `r₁`-maximum of `S i`.
  have hle : ∀ i, (r₁ (b i) : ℕ) ≤ r₁ (a i) := fun i => hmax i (b i) (hb i)
  -- equal multisets of values ⟹ equal sums of ranks.
  have hsum : univ.sum (fun i => (r₁ (a i) : ℕ)) = univ.sum (fun i => (r₁ (b i) : ℕ)) := by
    have h := congrArg (Multiset.sum ∘ Multiset.map fun x => (r₁ x : ℕ)) hm
    simpa [Multiset.map_map] using h
  by_contra hne
  push Not at hne
  obtain ⟨i, hi⟩ := hne
  have hne' : (r₁ (b i) : ℕ) ≠ (r₁ (a i) : ℕ) := by
    intro hte
    exact hi ((r₁.injective (Fin.eq_of_val_eq hte)).symm)
  -- one index is strict and none reverses, so the two rank sums must differ.
  have hstrict : univ.sum (fun i => (r₁ (b i) : ℕ)) < univ.sum (fun i => (r₁ (a i) : ℕ)) :=
    sum_lt_sum_at (fun i => r₁ (b i)) (fun i => r₁ (a i)) i hle (Nat.lt_of_le_of_ne (hle i) hne')
  omega

/-- **The counting half of Lemma 3.9 (machine-checked).**  However the sets `S i` and the ranking
are chosen, at most `C(n + m - 1, m)` vectors of maxima can arise, `m` being the number of indices.

Nothing about maxima is needed: a vector of maxima is a function `ι → Fin n`, i.e. a list of `m`
values from `n` possibilities, and once the count vector is fixed the vector of maxima is fixed by
`maxima_vector_determined`.  So the map `a ↦ (the multiset of its values)` is injective, and its
target is `Sym (Fin n) m`, the multisets of size `m` over `n` letters, which Mathlib already counts
by stars and bars (`Sym.card_sym_eq_choose`).  The paper cites this as Fredman's bound [GYY80];
as a statement about count vectors it is the multiset count. -/
theorem maxima_vectors_card {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (S : ι → Finset (Fin n)) (r₁ : Fin n ≃ Fin n) :
    Fintype.card {a : ι → Fin n // ∀ i, a i ∈ S i ∧ ∀ x ∈ S i, r₁ x ≤ r₁ (a i)} ≤
      Nat.choose (n + Fintype.card ι - 1) (Fintype.card ι) := by
  classical
  -- `a ↦ its multiset of values`, as an element of `Sym (Fin n) m`
  let toSym : {a : ι → Fin n // ∀ i, a i ∈ S i ∧ ∀ x ∈ S i, r₁ x ≤ r₁ (a i)} →
      Sym (Fin n) (Fintype.card ι) := fun a =>
    ⟨Multiset.map a.1 Finset.univ.val, by simp⟩
  have hinj : Function.Injective toSym := by
    intro a b hab
    have hm : Multiset.map a.1 Finset.univ.val = Multiset.map b.1 Finset.univ.val :=
      Subtype.mk.inj hab
    apply Subtype.ext
    apply funext
    intro i
    exact maxima_vector_determined S r₁ a.1 b.1 (fun i => (b.2 i).1) (fun i x hx => (a.2 i).2 x hx)
      hm i
  calc Fintype.card {a : ι → Fin n // ∀ i, a i ∈ S i ∧ ∀ x ∈ S i, r₁ x ≤ r₁ (a i)} ≤
        Fintype.card (Sym (Fin n) (Fintype.card ι)) := Fintype.card_le_of_injective toSym hinj
    _ = Nat.choose (n + Fintype.card ι - 1) (Fintype.card ι) := by
        rw [Sym.card_sym_eq_choose, Fintype.card_fin]

end DLMST
