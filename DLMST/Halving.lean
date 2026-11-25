import Mathlib
import DLMST.Recurrence

/-!
# §3.2, Lemma 3.3: the cost of the selection recursion

`Selection.lean` checks what the recursion *returns* (a lower half is an initial segment of the
tie-broken order, so the representatives it needs lie inside it) and the arithmetic §3.2 performs
afterwards (`Σᵥ k log(deg v + 1) = O(r² √(n·|B|))`).  `Recurrence.lean` checks the master form
`T m ≤ Σ T mᵢ + O(m)` with `Σ mᵢ ≤ m/2` ⟹ `O(m)`.  What is left — and what this file checks — is the
cost analysis inside Lemma 3.3 itself, which the paper writes in six sentences:

> At each level, the procedure performs `O(m)` comparisons and at most `k` successful admissibility
> tests.  Moreover, there is at most one recursive call with quota more than one, and the call contains
> at most half of the edges.  All other recursive calls are quota-1 group searches which operate on
> disjoint subsets of the discarded half.  Therefore, the main recursion uses `O(m)` comparisons and
> `O(k log m)` successful tests.  The quota-1 group searches contribute another `O(m)` comparisons
> since their inputs are disjoint, and `O(k log m)` successful tests since there are at most `k` group
> searches in total.

Read as arithmetic that is three claims and one trap.

* A halving sequence of level sizes has at most `⌊log₂ m⌋ + 1` non-empty levels and total size at most
  `2m`: `halving_le_div_pow`, `halving_zero`, `halving_sum_le`.  The first two use integer division and
  are the reason the *number* of tests is bounded at all — a real-valued geometric sum converges
  without ever reaching `0`.
* The quota-1 searches' inputs are pairwise disjoint subsets of the discarded half, so their sizes sum
  to at most `⌊m/2⌋`: `sum_card_disjoint_le`.  This is where the paper's "since their inputs are
  disjoint" becomes arithmetic.
* Comparisons are `O(m)` (`comparisons_main` for the path, `lemma33_comparisons` for the whole recursion,
  total `4·c·m`) and successful tests are `O(k log(m+1))` (`tests_main`, `tests_quota1`, `tests_total`,
  `tests_budget_real`).

The trap is the second sentence again.  The children of a node do *not* have sizes summing to `≤ m/2`:
the deep child takes half of the edges and the quota-1 searches take disjoint pieces of the other half,
so `Σ mᵢ ≤ m`, and `recurrence_linear` — which needs a strict contraction — does not apply to the full
child list.  The paper's own ordering of the sentences is what makes the argument work: a quota-1 search
"never starts another quota-1 group search", so it is *not* an instance of the same recursion, its cost
is `O(`its own size`)` by the geometric sum, and it belongs in the per-node term — leaving exactly one
contracting child.  `lemma33_comparisons` is that reading, with `2·c·u` as the cost of one quota-1
search on `u` edges.

Two facts are taken as hypotheses, and they are the only two the recursion uses: the split's lower half
has at most half the edges (`hdeep`, which is `[BFP+72]` selection rather than anything about spanning
trees), and the counting statements about tests and disjoint inputs (`htest`, `hempty`, `hsearch`).  The
matching *correctness* statement for the second of those is already verified — Selection's
`IsRep.of_lower` and `reps_below_of_not_lower` — but here they are assumptions on a cost function, and
what is checked is that the paper's numbers follow from them.
-/

namespace DLMST

/-! ## Halving sequences: depth and total size -/

/-- **A halving sequence of input sizes.**  `B 0` is the root's size and `B i` the size at level `i`;
each level keeps at most half the edges of the one above, in the integer sense `B (i+1) ≤ B i / 2`.
Lemma 3.3's "the call contains at most half of the edges" and `[BFP+72]`'s lower half of size `⌊m/2⌋`
are the two places this shape comes from. -/
def Halving (B : ℕ → ℕ) (m : ℕ) : Prop :=
  B 0 ≤ m ∧ ∀ i, B (i + 1) ≤ B i / 2

/-- **The same shape over `ℝ`**, where the per-level costs live. -/
def HalvingR (B : ℕ → ℝ) (m : ℝ) : Prop :=
  B 0 ≤ m ∧ ∀ i, B (i + 1) ≤ B i / 2

private theorem nat_div_two_le (x : ℕ) : ((x / 2 : ℕ) : ℝ) ≤ (x : ℝ) / 2 := by
  have h : (2 : ℝ) * ((x / 2 : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast Nat.mul_div_le x 2
  linarith

/-- An integer halving sequence is a real one: rounding down only makes the real inequality weaker, and
every use below is an upper bound. -/
theorem halvingR_of_nat {B : ℕ → ℕ} {m : ℕ} (hB : Halving B m) :
    HalvingR (fun i => (B i : ℝ)) (m : ℝ) := by
  refine ⟨?_, fun i => ?_⟩
  · show (B 0 : ℝ) ≤ (m : ℝ)
    exact_mod_cast hB.1
  · show (B (i + 1 : ℕ) : ℝ) ≤ (B i : ℝ) / 2
    exact le_trans (by exact_mod_cast (hB.2 i)) (nat_div_two_le (B i))

private theorem pow_halving_le {B : ℕ → ℕ} {m : ℕ} (hB : Halving B m) :
    ∀ i : ℕ, 2 ^ i * B i ≤ m := by
  intro i
  induction i with
  | zero => simpa using hB.1
  | succ i ih =>
      have h2 : 2 * B (i + 1) ≤ 2 * (B i / 2) := Nat.mul_le_mul_left _ (hB.2 i)
      have h1 : 2 * B (i + 1) ≤ B i := h2.trans (Nat.mul_div_le (B i) 2)
      calc 2 ^ (i + 1) * B (i + 1)
          = 2 ^ i * (2 * B (i + 1)) := by rw [Nat.pow_succ]; ring
        _ ≤ 2 ^ i * B i := Nat.mul_le_mul_left _ h1
        _ ≤ m := ih

/-- **Level `i` keeps at most `m / 2^i` edges.**  Stated multiplicatively first because that is the
form that survives odd sizes exactly: `2·⌊x/2⌋ ≤ x`. -/
theorem halving_le_div_pow {B : ℕ → ℕ} {m : ℕ} (hB : Halving B m) :
    ∀ i : ℕ, B i ≤ m / 2 ^ i := by
  intro i
  refine (Nat.le_div_iff_mul_le (show (0 : ℕ) < 2 ^ i by positivity)).2 ?_
  simpa [Nat.mul_comm] using pow_halving_le hB i

/-- **The path runs out of edges after `log₂ m` levels.**  Beyond that index a level contributes neither
comparisons nor tests, which is what makes the test count finite in the *integer* sense: the real
geometric sum of `halving_sum_le` bounds the comparisons without ever reaching `0`, so it cannot bound
`k·(#levels)`.  This is the paper's "O(k log m) successful tests", and the reason the split must halve
rather than merely shrink the input. -/
theorem halving_zero {B : ℕ → ℕ} {m : ℕ} (hB : Halving B m) :
    ∀ i : ℕ, Nat.log 2 m < i → B i = 0 := by
  intro i hi
  have hpow : m < 2 ^ i := Nat.lt_pow_of_log_lt (show (1 : ℕ) < 2 by omega) hi
  have hdiv : m / 2 ^ i = 0 := Nat.div_eq_of_lt hpow
  exact Nat.eq_zero_of_le_zero ((halving_le_div_pow hB i).trans (Nat.le_of_eq hdiv))

/-- **The geometric sum of a halving sequence** is at most twice its first term, with no assumption on
how many terms are summed.  Peel-first induction: the tail `i ↦ B (i+1)` is again halving, so the
induction hypothesis applies to it and `B 0 + Σ tail ≤ B 0 + 2·B 1 ≤ 2·B 0`.  This is the "the main
recursion uses `O(m)` comparisons" step, and the same computation bounds one quota-1 search by
`O(`its input`)` — which is what lets it be charged to the per-node term instead of to the recursion. -/
theorem halving_sum_le :
    ∀ (d : ℕ) (B : ℕ → ℝ), (∀ i, 0 ≤ B i) → (∀ i, B (i + 1) ≤ B i / 2) →
      (Finset.sum (Finset.range d) (fun i => B i)) ≤ 2 * B 0 := by
  intro d
  induction d with
  | zero => intro B h0 _; simpa using h0 0
  | succ d ih =>
      intro B h0 hB
      rw [Finset.sum_range_succ']
      have key := ih (fun i => B (i + 1)) (fun i => h0 (i + 1)) (fun i => hB (i + 1))
      have h1 : B 1 ≤ B 0 / 2 := hB 0
      nlinarith [h0 0, h0 1, key]

/-- **The main path's comparisons are linear** (Lemma 3.3: "the main recursion uses `O(m)`
comparisons"): level `i` costs `c·(size at level i)`, so any number of levels costs at most `2·c·m`.
The `2` is the geometric constant that the paper's `O` hides. -/
theorem comparisons_main (c : ℝ) (hc : 0 ≤ c) {B : ℕ → ℕ} {m : ℕ} (hB : Halving B m) :
    ∀ d : ℕ,
      (Finset.sum (Finset.range d) (fun i => c * (B i : ℝ))) ≤ 2 * c * (m : ℝ) := by
  intro d
  have hsum : (Finset.sum (Finset.range d) (fun i => (B i : ℝ))) ≤ 2 * (m : ℝ) :=
    le_trans (halving_sum_le d (fun i => (B i : ℝ)) (fun i => Nat.cast_nonneg _)
        (halvingR_of_nat hB).2)
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hB.1) (by linarith))
  calc (Finset.sum (Finset.range d) (fun i => c * (B i : ℝ)))
      = c * Finset.sum (Finset.range d) (fun i => (B i : ℝ)) := by rw [← Finset.mul_sum]
    _ ≤ c * (2 * (m : ℝ)) := mul_le_mul_of_nonneg_left hsum hc
    _ = 2 * c * (m : ℝ) := by ring

/-! ## The discarded half: disjoint inputs -/

/-- **Quota-1 searches consume disjoint inputs** (Lemma 3.3: "operate on disjoint subsets of the
discarded half"; "contribute another `O(m)` comparisons since their inputs are disjoint").  A pairwise
disjoint family of input sets inside a host of `M` edges has total size at most `M`.  Proved by
induction on the index set, using that the new set is disjoint from the union of the others, so
`|A| + |⋃| = |A ∪ ⋃| ≤ |U|`; this is the step that turns "disjoint" into the arithmetic hypothesis
`(search m).sum ≤ m/2` of `lemma33_comparisons`. -/
theorem sum_card_disjoint_le {α ι : Type*} [DecidableEq ι] [DecidableEq α] :
    ∀ (J : Finset ι) (s : ι → Finset α) (U : Finset α), J.biUnion s ⊆ U →
      (∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (s i) (s j)) →
      (Finset.sum J (fun i => (s i).card)) ≤ U.card := by
  intro J
  induction J using Finset.induction_on with
  | empty => intro s U _ _; simp
  | @insert a J has ih =>
      intro s U hsub hdisj
      have hne : ∀ i ∈ J, i ≠ a := fun i hi h => has (by rw [← h]; exact hi)
      have hd : Disjoint (s a) (J.biUnion s) := by
        refine Finset.disjoint_left.mpr (fun x hx1 hx2 => ?_)
        obtain ⟨i, hiJ, hxi⟩ := Finset.mem_biUnion.mp hx2
        exact Finset.disjoint_left.mp
          (hdisj a (Finset.mem_insert_self a J) i (Finset.mem_insert_of_mem hiJ)
            (fun hh => hne i hiJ hh.symm)) hx1 hxi
      have hcard : (s a ∪ J.biUnion s).card = (s a).card + (J.biUnion s).card := by
        have hsum := Finset.card_union_add_card_inter (s a) (J.biUnion s)
        have h2 : (s a ∩ J.biUnion s).card = 0 := by
          rw [Finset.disjoint_iff_inter_eq_empty.mp hd]
          exact Finset.card_empty
        rw [h2, Nat.add_zero] at hsum
        exact hsum
      have hU : s a ∪ J.biUnion s ⊆ U := by rw [← Finset.biUnion_insert]; exact hsub
      calc (Finset.sum (insert a J) (fun x => (s x).card))
          = (s a).card + Finset.sum J (fun x => (s x).card) := Finset.sum_insert has
        _ ≤ (s a).card + (J.biUnion s).card :=
            Nat.add_le_add_left
              (ih s (J.biUnion s) (Finset.Subset.refl _)
                (fun i hi j hj hne => hdisj i (Finset.mem_insert_of_mem hi)
                  j (Finset.mem_insert_of_mem hj) hne)) _
        _ = (s a ∪ J.biUnion s).card := hcard.symm
        _ ≤ U.card := Finset.card_le_card hU

/-! ## The successful admissibility tests -/

/-- **Successful tests along the main path: at most `k·(⌊log₂ m⌋ + 1)`.**  `t i` counts those run at
level `i`; `htest` is the paper's "at each level … at most `k` successful admissibility tests" and
`hempty` that an empty level runs none.  The split at `⌊log₂ m⌋ + 1` uses `halving_zero`, not the
geometric sum: this is a count of *events*, so it needs the path to actually terminate. -/
theorem tests_main (k m : ℕ) (B t : ℕ → ℕ) (hB : Halving B m)
    (htest : ∀ i, t i ≤ k) (hempty : ∀ i, B i = 0 → t i = 0) :
    ∀ d : ℕ, (Finset.sum (Finset.range d) (fun i => t i)) ≤ k * (Nat.log 2 m + 1) := by
  intro d
  have hconst : (Finset.sum (Finset.range (Nat.log 2 m + 1)) (fun i => k))
      = (Nat.log 2 m + 1) * k := by
    rw [Finset.sum_const_nat (fun i _ => rfl), Finset.card_range]
  have hhead : (Finset.sum (Finset.range (Nat.log 2 m + 1)) (fun i => t i)) ≤
      (Nat.log 2 m + 1) * k :=
    le_trans (Finset.sum_le_sum (fun i _ => htest i)) (le_of_eq hconst)
  have hhead' : (Finset.sum (Finset.range (Nat.log 2 m + 1)) (fun i => t i)) ≤
      k * (Nat.log 2 m + 1) := hhead.trans_eq (Nat.mul_comm _ _)
  by_cases hd : d ≤ Nat.log 2 m + 1
  · refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => Nat.zero_le _)) hhead'
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  · obtain ⟨e, rfl⟩ : ∃ e, (Nat.log 2 m + 1) + e = d := ⟨d - (Nat.log 2 m + 1), by omega⟩
    have htail : (Finset.sum (Finset.range e) (fun i => t ((Nat.log 2 m + 1) + i))) = 0 := by
      refine Finset.sum_eq_zero (fun x hx => hempty ((Nat.log 2 m + 1) + x) ?_)
      have hx' : x < e := Finset.mem_range.mp hx
      refine halving_zero hB ((Nat.log 2 m + 1) + x) ?_
      omega
    have hsplit : (Finset.sum (Finset.range ((Nat.log 2 m + 1) + e)) (fun i => t i))
        = (Finset.sum (Finset.range (Nat.log 2 m + 1)) (fun i => t i)) +
            Finset.sum (Finset.range e) (fun i => t ((Nat.log 2 m + 1) + i)) :=
      Finset.sum_range_add (fun i => t i) (Nat.log 2 m + 1) e
    rw [hsplit, htail, Nat.add_zero]
    exact hhead'

/-- **One quota-1 search: at most `⌊log₂ u⌋ + 1` successful tests** on an input of `u` edges — the
paper's "at each level … at most one successful admissibility test, and recurses on half of the edges",
i.e. `tests_main` with `k = 1`.  Recording it as an existential keeps the constant visible: the depth is
additive `+1`, which is what makes the bound `O(log(m+1))` rather than `O(log m)` at `m = 0`. -/
theorem tests_quota1_one (u : ℕ) :
    ∃ L : ℕ, ∀ (t : ℕ → ℕ) (B : ℕ → ℕ), Halving B u → (∀ i, t i ≤ 1) → (∀ i, B i = 0 → t i = 0) →
      ∀ d, (Finset.sum (Finset.range d) (fun i => t i)) ≤ L := by
  refine ⟨Nat.log 2 u + 1, fun t B hB ht hempty d => ?_⟩
  simpa using tests_main 1 u B t hB ht hempty d

/-- **The quota-1 searches together: at most `k·(⌊log₂ m⌋ + 1)` successful tests.**  "There are at most
`k` group searches in total", each running on at most `m` edges, and `Nat.log` is monotone — so the
paper's second `O(k log m)` term. -/
theorem tests_quota1 {ι : Type*} (J : Finset ι) (sz : ι → ℕ) (k m : ℕ)
    (hJ : J.card ≤ k) (hsz : ∀ j ∈ J, sz j ≤ m) :
    (Finset.sum J (fun j => Nat.log 2 (sz j) + 1)) ≤ k * (Nat.log 2 m + 1) := by
  have hle : (Finset.sum J (fun j => Nat.log 2 (sz j) + 1)) ≤
      Finset.sum J (fun j => Nat.log 2 m + 1) :=
    Finset.sum_le_sum (fun j hj =>
      Nat.add_le_add_right (Nat.log_mono_right (hsz j hj)) 1)
  have hconst : (Finset.sum J (fun j => Nat.log 2 m + 1)) = J.card * (Nat.log 2 m + 1) :=
    Finset.sum_const_nat (fun _ _ => rfl)
  rw [hconst] at hle
  exact hle.trans (Nat.mul_le_mul_right _ hJ)

/-- **Lemma 3.3's test count, both halves together**: the main path's `k` per level and the searches'
one per level add up to `2·k·(⌊log₂ m⌋ + 1)`, i.e. the paper's `O(k log m)` plus its "another
`O(k log m)`". -/
theorem tests_total {ι : Type*} (k m : ℕ) (B t : ℕ → ℕ) (J : Finset ι) (sz : ι → ℕ)
    (hB : Halving B m) (htest : ∀ i, t i ≤ k) (hempty : ∀ i, B i = 0 → t i = 0)
    (hJ : J.card ≤ k) (hsz : ∀ j ∈ J, sz j ≤ m) :
    ∀ d : ℕ,
      (Finset.sum (Finset.range d) (fun i => t i)) +
        (Finset.sum J (fun j => Nat.log 2 (sz j) + 1)) ≤ 2 * k * (Nat.log 2 m + 1) := by
  intro d
  have h1 := tests_main k m B t hB htest hempty d
  have h2 := tests_quota1 J sz k m hJ hsz
  have hnorm : k * (Nat.log 2 m + 1) + k * (Nat.log 2 m + 1) = 2 * k * (Nat.log 2 m + 1) := by ring
  rw [← hnorm]
  exact Nat.add_le_add h1 h2

/-! ## The comparison count, assembled -/

/-- **Lemma 3.3's comparison count, machine-checked.**  A node of size `m` spends `c·m` comparisons on
the median split and the scan (`hrec`'s `c * m`), makes one call whose quota still exceeds one and which
keeps at most half the edges (`hdeep` — the `[BFP+72]` fact), and fires quota-1 searches whose inputs
are disjoint subsets of the discarded half (`hsearch`, discharged by `sum_card_disjoint_le`).  Each
search on `u` edges costs `≤ 2·c·u` by `halving_sum_le`, so their total is the `(2*c)·Σ u` term.  Then
the whole call costs at most `4·c·m` comparisons.

The proof is `recurrence_linear` applied to the *single* deep child, with the searches' cost folded into
the per-node term: the children of a node have sizes summing to `≤ m`, not `≤ m/2`, so the master form
only becomes available after that folding — which is precisely the content of the paper's last two
sentences. -/
theorem lemma33_comparisons (T : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (deep : ℕ → ℕ) (search : ℕ → List ℕ)
    (hdeep : ∀ m, deep m ≤ m / 2) (hsearch : ∀ m, (search m).sum ≤ m / 2)
    (hT0 : T 0 ≤ 0)
    (hrec : ∀ m, T m ≤ T (deep m) + (2 * c) * ((search m).sum : ℝ) + c * m) :
    ∀ m, T m ≤ 4 * c * m := by
  have hc2 : (0 : ℝ) ≤ 2 * c := by linarith
  have hmap : ∀ m : ℕ, (([deep m] : List ℕ).map T).sum = T (deep m) := fun m => by
    simp
  have hrec' : ∀ m : ℕ, T m ≤ (([deep m] : List ℕ).map T).sum + (2 * c) * (m : ℝ) := by
    intro m
    have hle : ((search m).sum : ℝ) ≤ (m : ℝ) / 2 :=
      le_trans (by exact_mod_cast hsearch m) (nat_div_two_le m)
    have hmid : (2 * c) * ((m : ℝ) / 2) = c * (m : ℝ) := by ring
    have hsum : (2 * c) * ((search m).sum : ℝ) ≤ c * (m : ℝ) :=
      (mul_le_mul_of_nonneg_left hle hc2).trans_eq hmid
    rw [hmap]
    linarith [hrec m, hsum]
  have hsum' : ∀ m : ℕ, ([deep m] : List ℕ).sum ≤ m / 2 := fun m => by
    simpa using hdeep m
  intro m
  have h := recurrence_linear T (2 * c) hc2 (fun m => [deep m])
    (by simpa using hT0) hrec' hsum' m
  have h2 : (2 : ℝ) * (2 * c) * (m : ℝ) = 4 * c * m := by ring
  linarith

/-! ## Reading the discrete count as the paper's `O(k log (m+1))` -/

/-- **`log₂` against the natural logarithm**, by base change: `⌊log₂ m⌋ ≤ log(m+1) / log 2`.  The
`+1` inside the logarithm covers `m = 0`, where both sides are `0`. -/
theorem natLog_le_realLog (m : ℕ) :
    (Nat.log 2 m : ℝ) ≤ Real.log ((m : ℝ) + 1) / Real.log 2 := by
  have h20 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  rcases Nat.eq_zero_or_pos m with h | hm
  · rw [h, Nat.log_zero_right, Nat.cast_zero]
    have h1 : Real.log ((0 : ℝ) + 1) = 0 := by rw [zero_add, Real.log_one]
    rw [h1, zero_div]
  · have hpow : (2 : ℝ) ^ Nat.log 2 m ≤ (m : ℝ) :=
      by exact_mod_cast Nat.pow_log_le_self 2 (Nat.ne_of_gt hm)
    have hpos : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 m := by positivity
    have hlog : Real.log ((2 : ℝ) ^ Nat.log 2 m) ≤ Real.log ((m : ℝ) + 1) :=
      Real.log_le_log hpos (by linarith)
    have h2 : Real.log ((2 : ℝ) ^ Nat.log 2 m) = (Nat.log 2 m : ℝ) * Real.log 2 := by
      rw [Real.log_pow]
    rw [h2] at hlog
    exact (le_div_iff₀ h20).mpr hlog

/-- **Lemma 3.3's test count in the paper's notation.**  `2·k·(⌊log₂ m⌋+1) ≤ (2/log 2)·k·(log(m+1)+1)`,
which is `O(k log(m+1))` with the absolute constant `2 / log 2`.  Feeding this into
`log_add_one_le_two_sqrt` and `test_budget` of `Selection.lean` is what turns the per-vertex estimate
into the batch's `O(r² √(n·|B|))`. -/
theorem tests_budget_real (k m : ℕ) :
    (2 : ℝ) * (k : ℝ) * ((Nat.log 2 m : ℝ) + 1) ≤
      (2 / Real.log 2) * (k : ℝ) * (Real.log ((m : ℝ) + 1) + 1) := by
  have h20 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have h21 : Real.log 2 ≤ (1 : ℝ) := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ))
    linarith
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hA : (2 : ℝ) * (k : ℝ) * ((Nat.log 2 m : ℝ) + 1)
      = (2 * (Nat.log 2 m : ℝ)) * (k : ℝ) + 2 * (k : ℝ) := by ring
  have hB : 2 * (Nat.log 2 m : ℝ) ≤ (2 / Real.log 2) * Real.log ((m : ℝ) + 1) := by
    have h := natLog_le_realLog m
    have h2 : (2 : ℝ) * (Real.log ((m : ℝ) + 1) / Real.log 2)
        = (2 / Real.log 2) * Real.log ((m : ℝ) + 1) := by ring
    linarith
  have hC : (2 * (Nat.log 2 m : ℝ)) * (k : ℝ)
      ≤ (2 / Real.log 2) * (k : ℝ) * Real.log ((m : ℝ) + 1) :=
    (mul_le_mul_of_nonneg_right hB hk).trans_eq (by ring)
  have h3 : (2 : ℝ) * (k : ℝ) ≤ (2 / Real.log 2) * (k : ℝ) := by
    have hstep : (2 : ℝ) * (k : ℝ) ≤ (2 * (k : ℝ)) / Real.log 2 :=
      le_div_self (by positivity) h20 h21
    exact hstep.trans_eq (by ring)
  calc (2 : ℝ) * (k : ℝ) * ((Nat.log 2 m : ℝ) + 1)
      = (2 * (Nat.log 2 m : ℝ)) * (k : ℝ) + 2 * (k : ℝ) := hA
    _ ≤ (2 / Real.log 2) * (k : ℝ) * Real.log ((m : ℝ) + 1) + 2 * (k : ℝ) :=
        add_le_add hC (le_refl _)
    _ ≤ (2 / Real.log 2) * (k : ℝ) * (Real.log ((m : ℝ) + 1) + 1) := by
        rw [mul_add, mul_one]
        exact add_le_add (le_refl _) h3

end DLMST
