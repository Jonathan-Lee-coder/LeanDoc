import DLMST.HistoryCount
import DLMST.Schedule

/-!
# §3.5's candidate family `A`: the vectors a total order can realise

§3.5 conditions on the round's spokes `σ_i` and forest `F_i` and takes `A` to be the family of
*all* preference vectors that some weighting of the ground set could produce.  The paper counts it
(Lemma 3.10's third factor) as `C(m + 2n - 1, m)`: the preference of an edge `e` is
`find` iff the heaviest element of `S_e = {σ(u), σ(v)} ∪ (u–v path in F)` is a spoke, and Fredman's
vector-of-maxima bound limits the possible vectors of heaviest elements.

This file machine-checks that count in the form the development needs:

* `argmaxFamily` — the argmax vectors of `m` sets under *every* total order (a total order is a
  function `α → ℕ` with a fixed tie-breaking index, `keyOf`); `argmaxFamily_card_le` is the
  `C(|α| + m - 1, m)` bound.  The injection is into multisets: two argmax vectors with the same
  multiset of values coincide (`maxima_vector_determined_nat`, the `κ`-generalisation of
  `VectorMaxima.maxima_vector_determined` — note that the paper's Lemma 3.9 is only interesting
  over *all* orders, which is exactly this statement).
* `candFamily` — the induced family of `Pref`-vectors, with `candFamily_card_le` (the same bound,
  through the argmax family) and `log_candFamily_le` (`log |A| ≤ 4√(2nm)`, the paper's
  `O(√(mn))`).
* `rOf` / `exists_key_dominator_iff` — the tie-breaking convention of the paper ("spokes ranked
  higher than forest edges in case of ties"): a spoke dominates `S` under the weight-key iff some
  spoke is at least as heavy as every element of `S`.  This is what turns "the heaviest element of
  `S_e` is a spoke" into a statement about weights and, with `PrefTrail.prefFind_iff_trail_weight`,
  into the true preference vector.
* `mem_candFamily_of_trail_form` — any preference vector that has the trail form of the paper is a
  member of the family, so `truth ∈ A`.

Not formalised here: the geometric assembly that gives each round edge its `S_e` (spokes plus the
`F`-path) and the case analysis "no spoke / equal portals / not connected ⟹ preference determined";
that is the next step and uses `PrefTrail.prefFind_iff_trail_weight` plus `Path.path_of_conn`.
-/

namespace DLMST
open Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **The key of `x` under the order `r`**, with the tie-breaking index `eN` made explicit: a total
preorder `r : α → ℕ` becomes an injective key by appending the index.  Every total order on the
ground set is represented (`r` injective), and the tie-breaking within `r`-classes is the fixed
index order. -/
noncomputable def keyOf {α : Type*} [Fintype α] (eN : α ≃ Fin (Fintype.card α)) (r : α → ℕ)
    (x : α) : ℕ :=
  r x * Fintype.card α + (eN x : ℕ)

theorem keyOf_injective {α : Type*} [Fintype α] (eN : α ≃ Fin (Fintype.card α)) (r : α → ℕ) :
    Function.Injective (keyOf eN r) := by
  intro x y h
  have h' : r x * Fintype.card α + (eN x : ℕ) = r y * Fintype.card α + (eN y : ℕ) := h
  have hN : 0 < Fintype.card α := (eN x).pos
  have hdiv : r x = r y := by
    have h1 : (r x * Fintype.card α + (eN x : ℕ)) / Fintype.card α = r x := by
      rw [Nat.mul_comm (r x), Nat.mul_add_div hN, Nat.div_eq_of_lt (eN x).isLt, Nat.add_zero]
    have h2 : (r y * Fintype.card α + (eN y : ℕ)) / Fintype.card α = r y := by
      rw [Nat.mul_comm (r y), Nat.mul_add_div hN, Nat.div_eq_of_lt (eN y).isLt, Nat.add_zero]
    rw [← h1, h', h2]
  have hex : (eN x : ℕ) = (eN y : ℕ) := by
    rw [hdiv] at h'
    omega
  exact eN.injective (Fin.ext hex)

/-- One strict coordinate makes the whole sum strict. -/
private lemma sum_lt_sum_at' {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : ι → ℕ) (i : ι) (hef : ∀ j, f j ≤ g j) (hgt : f i < g i) :
    (Finset.univ.sum f) < (Finset.univ.sum g) := by
  classical
  have hf : Finset.univ.sum f =
      (Finset.univ.erase i).sum f + f i := (Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)).symm
  have hg : Finset.univ.sum g =
      (Finset.univ.erase i).sum g + g i := (Finset.sum_erase_add Finset.univ g (Finset.mem_univ i)).symm
  rw [hf, hg]
  have hle : (Finset.univ.erase i).sum f ≤ (Finset.univ.erase i).sum g :=
    Finset.sum_le_sum fun _ _ => hef _
  omega

/-- **Lemma 3.9 over all orders**: two vectors of maxima of the same sets with the same multiset of
values coincide.  Unlike `VectorMaxima.maxima_vector_determined` the order is an arbitrary key `κ`,
so this is the statement that makes the count of argmax vectors nontrivial. -/
theorem maxima_vector_determined_nat {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (S : ι → Finset α) (κ : α → ℕ) (hκ : Function.Injective κ) (a b : ι → α)
    (hb : ∀ i, b i ∈ S i) (hmax : ∀ i x, x ∈ S i → κ x ≤ κ (a i))
    (hm : Multiset.map a Finset.univ.val = Multiset.map b Finset.univ.val) :
    ∀ i, a i = b i := by
  classical
  have hle : ∀ i, κ (b i) ≤ κ (a i) := fun i => hmax i (b i) (hb i)
  have hsum : Finset.univ.sum (fun i => κ (a i)) = Finset.univ.sum (fun i => κ (b i)) := by
    have h := congrArg (Multiset.sum ∘ Multiset.map κ) hm
    simpa [Multiset.map_map] using h
  intro i
  have heq : κ (b i) = κ (a i) := by
    by_contra hne
    have hlt : κ (b i) < κ (a i) := lt_of_le_of_ne (hle i) hne
    have := sum_lt_sum_at' (fun j => κ (b j)) (fun j => κ (a j)) i hle hlt
    omega
  exact hκ heq.symm

/-- **The argmax vectors of `m` sets over all total orders.**  `a` is in the family when some order
`r` (keyed by `keyOf`) makes `a i` a maximum of `S i`. -/
noncomputable def argmaxFamily {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (S : ι → Finset α) (eN : α ≃ Fin (Fintype.card α)) : Finset (ι → α) :=
  Finset.univ.filter fun a => ∃ r : α → ℕ, ∀ i, a i ∈ S i ∧
    ∀ y ∈ S i, keyOf eN r y ≤ keyOf eN r (a i)

/-- The multiset of values of an argmax vector, as an element of `Sym α m`: the injection that
makes Fredman's bound a stars-and-bars count. -/
noncomputable def toSymMap {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (a : ι → α) : Sym α (Fintype.card ι) :=
  ⟨Multiset.map a Finset.univ.val, by simp⟩

/-- **Fredman's vector-of-maxima bound.**  However the `m` sets are chosen, at most
`C(|α| + m - 1, m)` vectors of maxima can arise over all total orders.  The injection is into the
multiset of values, by `maxima_vector_determined_nat`. -/
theorem argmaxFamily_card_le {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    [DecidableEq α] (S : ι → Finset α) (eN : α ≃ Fin (Fintype.card α)) :
    (argmaxFamily S eN).card ≤
      Nat.choose (Fintype.card α + Fintype.card ι - 1) (Fintype.card ι) := by
  classical
  have hinj : Set.InjOn (toSymMap (ι := ι) (α := α)) ↑(argmaxFamily S eN) := by
    intro a ha b hb hEq
    have hm : Multiset.map a Finset.univ.val = Multiset.map b Finset.univ.val := by
      have := congrArg Subtype.val hEq
      simpa [toSymMap] using this
    obtain ⟨ra, hra⟩ := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
    obtain ⟨rb, hrb⟩ := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
    funext i
    exact maxima_vector_determined_nat S (keyOf eN ra) (keyOf_injective eN ra) a b
      (fun i => (hrb i).1) (fun i x hx => (hra i).2 x hx) hm i
  calc (argmaxFamily S eN).card
      ≤ Fintype.card (Sym α (Fintype.card ι)) := by
        have h := Finset.card_le_card_of_injOn (toSymMap (ι := ι) (α := α))
          (fun a _ => Finset.mem_univ _) hinj
        rwa [Finset.card_univ] at h
    _ = Nat.choose (Fintype.card α + Fintype.card ι - 1) (Fintype.card ι) := by
        rw [Sym.card_sym_eq_choose (Fintype.card ι)]

/-- **§3.5's family `A`, for fixed per-edge data.**  For each round edge `i`, `S i` is the paper's
`S_e` (spokes and forest path) and `sp i` its two spokes; the preference vector is `find` exactly
when some spoke dominates all of `S i` under the unknown order.  The family contains one vector per
total order. -/
noncomputable def candFamily {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (S sp : ι → Finset α) (eN : α ≃ Fin (Fintype.card α)) : Finset (ι → Pref) :=
  Finset.univ.filter fun a => ∃ r : α → ℕ, ∀ i, a i =
    (if ∃ x ∈ sp i, ∀ y ∈ S i, keyOf eN r y ≤ keyOf eN r x then Pref.find else Pref.project)

/-- **`|A| ≤ C(|α| + m - 1, m)`.**  The pattern of a candidate is a function of its argmax vector,
so the family is the image of `argmaxFamily`. -/
theorem candFamily_card_le {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    [DecidableEq α] (S sp : ι → Finset α) (eN : α ≃ Fin (Fintype.card α))
    (hne : ∀ i, (S i).Nonempty) (hspS : ∀ i, sp i ⊆ S i) :
    (candFamily S sp eN).card ≤
      Nat.choose (Fintype.card α + Fintype.card ι - 1) (Fintype.card ι) := by
  classical
  have hsub : candFamily S sp eN ⊆ (argmaxFamily S eN).image
      (fun b i => if b i ∈ sp i then Pref.find else Pref.project) := by
    intro a ha
    unfold candFamily at ha
    obtain ⟨r, hr⟩ := (Finset.mem_filter.mp ha).2
    -- the argmax vector: the dominating spoke where there is one, the key-maximum otherwise
    have hmax : ∀ i, ∃ x ∈ S i, ∀ y ∈ S i, keyOf eN r y ≤ keyOf eN r x := by
      intro i
      obtain ⟨x, hxS, hx⟩ := Finset.exists_max_image (S i) (keyOf eN r) (hne i)
      exact ⟨x, hxS, fun y hy => hx y hy⟩
    let b : ι → α := fun i =>
      if h : ∃ x ∈ sp i, ∀ y ∈ S i, keyOf eN r y ≤ keyOf eN r x then h.choose
      else (hmax i).choose
    have hbS : ∀ i, b i ∈ S i := by
      intro i
      by_cases h : ∃ x ∈ sp i, ∀ y ∈ S i, keyOf eN r y ≤ keyOf eN r x
      · rw [show b i = h.choose from dif_pos h]
        exact hspS i (h.choose_spec).1
      · rw [show b i = (hmax i).choose from dif_neg h]
        exact (hmax i).choose_spec.1
    have hbmax : ∀ i y, y ∈ S i → keyOf eN r y ≤ keyOf eN r (b i) := by
      intro i y hy
      by_cases h : ∃ x ∈ sp i, ∀ y ∈ S i, keyOf eN r y ≤ keyOf eN r x
      · rw [show b i = h.choose from dif_pos h]
        exact (h.choose_spec).2 y hy
      · rw [show b i = (hmax i).choose from dif_neg h]
        exact (hmax i).choose_spec.2 y hy
    have hbFam : b ∈ argmaxFamily S eN :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, r, fun i => ⟨hbS i, hbmax i⟩⟩
    refine Finset.mem_image.mpr ⟨b, hbFam, ?_⟩
    funext i
    have hi := hr i
    by_cases h : ∃ x ∈ sp i, ∀ y ∈ S i, keyOf eN r y ≤ keyOf eN r x
    · have hbi : b i ∈ sp i := by
        rw [show b i = h.choose from dif_pos h]
        exact (h.choose_spec).1
      simp only [h, if_true] at hi
      simp only [hbi, if_true, hi]
    · have hbi : b i ∉ sp i := by
        intro hmem
        exact h ⟨b i, hmem, hbmax i⟩
      simp only [h, if_false] at hi
      simp only [hbi, if_false, hi]
  calc (candFamily S sp eN).card
      ≤ ((argmaxFamily S eN).image
          (fun b i => if b i ∈ sp i then Pref.find else Pref.project)).card :=
        Finset.card_le_card hsub
    _ ≤ (argmaxFamily S eN).card := Finset.card_image_le
    _ ≤ Nat.choose (Fintype.card α + Fintype.card ι - 1) (Fintype.card ι) :=
        argmaxFamily_card_le S eN

/-- **`log |A| = O(√(mn))`.**  With a ground set of size at most `2n` the bound reads
`log |A| ≤ 4√(2nm)` (the paper's `2√(2mn)` up to the constant of `log_choose_le`). -/
theorem log_candFamily_le {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    [DecidableEq α] (S sp : ι → Finset α) (eN : α ≃ Fin (Fintype.card α))
    (hne : ∀ i, (S i).Nonempty) (hspS : ∀ i, sp i ⊆ S i) {n : ℕ} (hα : Fintype.card α ≤ 2 * n) :
    Real.log ((candFamily S sp eN).card : ℝ) ≤
      4 * Real.sqrt ((2 * n : ℝ) * (Fintype.card ι : ℝ)) := by
  classical
  rcases Nat.eq_zero_or_pos (candFamily S sp eN).card with h0 | hpos
  · rw [h0]
    simp only [Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hcard := candFamily_card_le (ι := ι) (α := α) S sp eN hne hspS
  have hstep : Nat.choose (Fintype.card α + Fintype.card ι - 1) (Fintype.card ι) ≤
      Nat.choose (Fintype.card α + Fintype.card ι) (Fintype.card ι) :=
    Nat.choose_le_choose _ (by omega)
  have hle : (candFamily S sp eN).card ≤
      Nat.choose (Fintype.card α + Fintype.card ι) (Fintype.card ι) := hcard.trans hstep
  have hpos' : (0 : ℝ) < (Nat.choose (Fintype.card α + Fintype.card ι) (Fintype.card ι) : ℝ) := by
    have : 0 < Nat.choose (Fintype.card α + Fintype.card ι) (Fintype.card ι) :=
      Nat.choose_pos (by omega)
    exact_mod_cast this
  calc Real.log ((candFamily S sp eN).card : ℝ)
      ≤ Real.log (Nat.choose (Fintype.card α + Fintype.card ι) (Fintype.card ι) : ℝ) :=
        Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)
    _ ≤ 4 * Real.sqrt ((Fintype.card α : ℝ) * (Fintype.card ι : ℝ)) :=
        log_choose_le (Fintype.card α) (Fintype.card ι)
    _ ≤ 4 * Real.sqrt ((2 * n : ℝ) * (Fintype.card ι : ℝ)) := by
        have hNm : (Fintype.card α : ℝ) ≤ 2 * n := by exact_mod_cast hα
        have := Real.sqrt_le_sqrt
          (mul_le_mul_of_nonneg_right hNm (Nat.cast_nonneg (α := ℝ) (Fintype.card ι)))
        linarith

/-- **The weight order with the paper's spoke tie-break.**  `rOf w spk x = 2·#{y : w y < w x} + [x ∈
spk]` refines the weights and puts a spoke above every forest edge of equal weight, so that its
`keyOf`-maximum is a spoke whenever the weight-maximum is attained by one. -/
noncomputable def rOf {α : Type*} [Fintype α] [DecidableEq α] (w : α → ℝ)
    (spk : Finset α) (z : α) : ℕ :=
  2 * (Finset.univ.filter (fun y => w y < w z)).card + (if z ∈ spk then 1 else 0)

/-- A strictly heavier element has a strictly larger rank `#{y : w y < w ·}`. -/
theorem rOf_rank_lt {α : Type*} [Fintype α] {w : α → ℝ} {y x : α} (hyx : w y < w x) :
    (Finset.univ.filter (fun z => w z < w y)).card <
      (Finset.univ.filter (fun z => w z < w x)).card := by
  refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩)
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact lt_trans hz hyx
  · intro hEq
    have hy : y ∈ Finset.univ.filter (fun z => w z < w x) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hyx
    rw [← hEq] at hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    exact lt_irrefl _ hy

/-- `rOf` is strictly monotone in the weight. -/
theorem rOf_lt_of_lt {α : Type*} [Fintype α] [DecidableEq α] {w : α → ℝ} {spk : Finset α}
    {y x : α} (hyx : w y < w x) : rOf w spk y < rOf w spk x := by
  have h1 := rOf_rank_lt hyx
  unfold rOf
  have hy1 : (if y ∈ spk then 1 else 0) ≤ 1 := by split <;> omega
  omega

/-- At equal weights a spoke outranks a non-spoke. -/
theorem rOf_lt_of_eq_notMem_mem {α : Type*} [Fintype α] [DecidableEq α] {w : α → ℝ}
    {spk : Finset α} {y x : α} (heq : w y = w x) (hy : y ∉ spk) (hx : x ∈ spk) :
    rOf w spk y < rOf w spk x := by
  unfold rOf
  rw [heq, if_neg hy, if_pos hx]
  omega

/-- A strict rank gap gives a strict key gap, whatever the tie-breaking bijection. -/
theorem keyOf_lt_of_rOf_succ_le {α : Type*} [Fintype α] [DecidableEq α]
    (eN : α ≃ Fin (Fintype.card α))
    {w : α → ℝ} {spk : Finset α} {y x : α} (h : rOf w spk y + 1 ≤ rOf w spk x) :
    keyOf eN (rOf w spk) y < keyOf eN (rOf w spk) x := by
  have step1 : keyOf eN (rOf w spk) y < (rOf w spk y + 1) * Fintype.card α := by
    have hy : (eN y : ℕ) < Fintype.card α := (eN y).isLt
    unfold keyOf
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have step2 : (rOf w spk y + 1) * Fintype.card α ≤ rOf w spk x * Fintype.card α :=
    Nat.mul_le_mul_right _ h
  have step3 : rOf w spk x * Fintype.card α ≤ keyOf eN (rOf w spk) x := by
    unfold keyOf
    exact Nat.le_add_right _ _
  exact lt_of_lt_of_le step1 (le_trans step2 step3)

/-- Strictly heavier ⟹ strictly larger key. -/
theorem keyOf_lt_of_lt {α : Type*} [Fintype α] [DecidableEq α]
    (eN : α ≃ Fin (Fintype.card α)) {w : α → ℝ} {spk : Finset α} {y x : α}
    (hyx : w y < w x) : keyOf eN (rOf w spk) y < keyOf eN (rOf w spk) x :=
  keyOf_lt_of_rOf_succ_le eN (Nat.succ_le_of_lt (rOf_lt_of_lt (spk := spk) hyx))

/-- Equal weights, non-spoke beats spoke: the key gap is strict. -/
theorem keyOf_lt_of_eq_notMem_mem {α : Type*} [Fintype α] [DecidableEq α]
    (eN : α ≃ Fin (Fintype.card α)) {w : α → ℝ} {spk : Finset α} {y x : α}
    (heq : w y = w x) (hy : y ∉ spk) (hx : x ∈ spk) :
    keyOf eN (rOf w spk) y < keyOf eN (rOf w spk) x :=
  keyOf_lt_of_rOf_succ_le eN (Nat.succ_le_of_lt (rOf_lt_of_eq_notMem_mem heq hy hx))

/-- **The tie-breaking convention** ("spokes ranked higher than forest edges in case of ties").  For
`sp ⊆ spk`, `sp ⊆ S`, `S ∩ spk ⊆ sp` and `sp` nonempty, a spoke of `sp` dominates `S` under the
weight-key of `rOf` iff some spoke of `sp` is at least as heavy as every element of `S`.  (The
hypothesis `S ∩ spk ⊆ sp` is the paper's "the spokes of `S_e` are exactly `σ(u), σ(v)`": the path
edges are forest edges, not spokes.) -/
theorem exists_key_dominator_iff {α : Type*} [Fintype α] [DecidableEq α]
    (eN : α ≃ Fin (Fintype.card α)) (w : α → ℝ) (spk S sp : Finset α)
    (hspk : sp ⊆ spk) (hspS : sp ⊆ S) (hSk : ∀ x ∈ S, x ∈ spk → x ∈ sp) (hne : sp.Nonempty) :
    (∃ x ∈ sp, ∀ y ∈ S, keyOf eN (rOf w spk) y ≤ keyOf eN (rOf w spk) x) ↔
      ∃ x ∈ sp, ∀ y ∈ S, w y ≤ w x := by
  classical
  have hrank_mono : ∀ {y x : α}, w y < w x →
      (Finset.univ.filter (fun z => w z < w y)).card <
        (Finset.univ.filter (fun z => w z < w x)).card := by
    intro y x hyx
    refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩)
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact lt_trans hz hyx
    · intro hEq
      have hy : y ∈ Finset.univ.filter (fun z => w z < w x) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hyx
      rw [← hEq] at hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      exact lt_irrefl _ hy
  have hkey_of_lt : ∀ {y x : α}, rOf w spk y < rOf w spk x →
      keyOf eN (rOf w spk) y < keyOf eN (rOf w spk) x := by
    intro y x hlt
    have step1 : keyOf eN (rOf w spk) y < (rOf w spk y + 1) * Fintype.card α := by
      have hy : (eN y : ℕ) < Fintype.card α := (eN y).isLt
      unfold keyOf
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have step2 : (rOf w spk y + 1) * Fintype.card α ≤ rOf w spk x * Fintype.card α :=
      Nat.mul_le_mul_right _ (by omega)
    have step3 : rOf w spk x * Fintype.card α ≤ keyOf eN (rOf w spk) x := by
      unfold keyOf
      exact Nat.le_add_right _ _
    exact lt_of_lt_of_le step1 (le_trans step2 step3)
  constructor
  · rintro ⟨x, hxsp, hxdom⟩
    refine ⟨x, hxsp, fun y hy => ?_⟩
    by_contra hcon
    push Not at hcon
    have hlt : rOf w spk x < rOf w spk y := by
      have h1 := hrank_mono hcon
      unfold rOf
      have hx1 : (if x ∈ spk then 1 else 0) ≤ 1 := by split <;> omega
      omega
    exact absurd (hxdom y hy) (not_le.mpr (hkey_of_lt hlt))
  · rintro ⟨x0, hx0sp, hx0dom⟩
    -- among the spokes of maximum weight pick the one with the largest key
    have hTne : (sp.filter (fun z => w z = w x0)).Nonempty :=
      ⟨x0, Finset.mem_filter.mpr ⟨hx0sp, rfl⟩⟩
    obtain ⟨x, hxT, hxmax⟩ :=
      Finset.exists_max_image (sp.filter (fun z => w z = w x0)) (keyOf eN (rOf w spk)) hTne
    obtain ⟨hxsp, hxw⟩ := Finset.mem_filter.mp hxT
    refine ⟨x, hxsp, fun y hy => ?_⟩
    have hyx : w y ≤ w x := (hx0dom y hy).trans_eq hxw.symm
    rcases lt_or_eq_of_le hyx with hlt | heq
    · have hrlt : rOf w spk y < rOf w spk x := by
        have h1 := hrank_mono hlt
        unfold rOf
        have hy1 : (if y ∈ spk then 1 else 0) ≤ 1 := by split <;> omega
        omega
      exact le_of_lt (hkey_of_lt hrlt)
    · by_cases hspky : y ∈ spk
      · have hyT : y ∈ sp.filter (fun z => w z = w x0) :=
          Finset.mem_filter.mpr ⟨hSk y hy hspky, heq.trans hxw⟩
        exact hxmax y hyT
      · have hrlt : rOf w spk y < rOf w spk x := by
          have hrank_eq : (Finset.univ.filter (fun z => w z < w y)).card =
              (Finset.univ.filter (fun z => w z < w x)).card := by rw [heq]
          unfold rOf
          rw [hrank_eq, if_neg hspky, if_pos (hspk hxsp)]
          omega
        exact le_of_lt (hkey_of_lt hrlt)

/-- **`truth ∈ A` from the trail form.**  If a preference vector is `find` exactly when some spoke is
at least as heavy as every element of its `S_e`, then it is one of the family's members: the
tie-breaking order `rOf` of `exists_key_dominator_iff` witnesses it. -/
theorem mem_candFamily_of_trail_form {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    [DecidableEq α] (S sp : ι → Finset α) (eN : α ≃ Fin (Fintype.card α)) (w : α → ℝ)
    (spk : Finset α) (hspk : ∀ i, sp i ⊆ spk) (hSk : ∀ i, ∀ x ∈ S i, x ∈ spk → x ∈ sp i)
    (hne : ∀ i, (sp i).Nonempty) (hS : ∀ i, sp i ⊆ S i) (a : ι → Pref)
    (h : ∀ i, (a i = Pref.find) ↔ ∃ x ∈ sp i, ∀ y ∈ S i, w y ≤ w x) :
    a ∈ candFamily S sp eN := by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, rOf w spk, fun i => ?_⟩
  have hiff := exists_key_dominator_iff eN w spk (S i) (sp i) (hspk i) (hS i) (hSk i) (hne i)
  by_cases hc : ∃ x ∈ sp i, ∀ y ∈ S i, w y ≤ w x
  · rw [if_pos (hiff.mpr hc), (h i).mpr hc]
  · rw [if_neg (fun hk => hc (hiff.mp hk))]
    have hne' : a i ≠ Pref.find := fun heq => hc ((h i).mp heq)
    cases hv : a i
    · exact absurd hv hne'
    · rfl

end DLMST