import DLMST.History

/-!
# §3.5, Claim 3.12: a small set of coordinates that separates preference vectors

`History.lean` produced, for every family of histories, one schedule that is good for all of them
(Lemma 3.11).  §3.5 turns to the *estimates*: in a round, the true preference vector `a_i` of the
round's edges has to be learned from a small number of queries, because the round cannot afford to
ask every edge.  Claim 3.12 is the combinatorial heart of that: whatever the finite family `A` of
candidate preference vectors is, there is a set `S` of coordinates of size `O(t log |A|)` such that

  any two vectors of `A` agreeing on `S` differ in at most `m_i / t` coordinates.

The paper's proof samples `k = 2t(log |A| + 1)` coordinates independently and uniformly, uses
`Pr[a, b agree on the sample] ≤ (1 - 1/t)^k` for a pair differing in more than `m_i/t` coordinates,
and a union bound over the `|A|²` pairs.  As in `History.lean` for Lemma 3.11, "random" is replaced
by the exact finite count over all `k`-tuples of coordinates: the set of *bad* tuples (those on which
some badly-differing pair agrees) has cardinality

  `|A|² · (m_i - m_i/t - 1)^k  <  m_i^k = #(all tuples)`,

so a good tuple exists, and its image `S` is the desired set (`|S| ≤ k`).  The only analytic input is
that `(m_i - m_i/t - 1)/m_i ≤ 1 - 1/t` together with `(1 - 1/t)^k ≤ e^{-k/t}` and `k/t ≥ 2(log|A|+1)`
— exactly the paper's `|A|² e^{-k/t} < 1`, with `k = 2t(⌈log|A|⌉+1)`: **no constant is lost**.

What is *not* here is Lemma 3.10's count `log |A| = O(t²√(mn))` (its middle step is Lemma 3.9, the
Fredman `C(n+m-1, m)` bound — still open, obligation 3): `claim312` takes the family `A` as data, so
the sampling half and the counting half are checked independently.  Instantiating `|A| = e^{O(√(mn))}` then gives the paper's
`|S*| = O(t√(mn))` with no further combinatorics.
-/

namespace DLMST

open Classical

set_option linter.unusedSectionVars false

variable {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]

/-! ## Tuples of coordinates and the count of bad ones -/

/-- The tuples of `k` coordinates on which `a` and `b` agree at every sampled coordinate.  This is
the set whose cardinality is `(#agreement)^k`, the exact "independent uniform sampling" count. -/
noncomputable def agreeTuples (k : ℕ) (a b : α → β) : Finset (Fin k → α) :=
  Fintype.piFinset fun _ => Finset.univ.filter (fun x => a x = b x)

theorem mem_agreeTuples {k : ℕ} {a b : α → β} {s : Fin k → α} :
    s ∈ agreeTuples k a b ↔ ∀ i, a (s i) = b (s i) := by
  rw [agreeTuples, Fintype.mem_piFinset]
  exact forall_congr' fun i => by simp

/-- The number of `k`-tuples agreeing everywhere is the `k`-th power of the number of agreement
coordinates — the independence of the paper's random sample, made exact. -/
theorem card_agreeTuples (k : ℕ) (a b : α → β) :
    (agreeTuples k a b).card = (Finset.univ.filter (fun x => a x = b x)).card ^ k := by
  rw [agreeTuples, Fintype.card_piFinset]
  simp

/-- A tuple is **bad** if some pair of candidate vectors differs in more than `q` coordinates yet
agrees on every sampled coordinate — the event of Claim 3.12's union bound. -/
def Bad (A : Finset (α → β)) (q k : ℕ) (s : Fin k → α) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, q < (Finset.univ.filter fun x => a x ≠ b x).card ∧ ∀ i, a (s i) = b (s i)

/-- **The union bound, as an exact count.**  The number of bad tuples is at most `|A|²` times the
number of `k`-tuples on which a fixed badly-differing pair agrees, which is at most
`(m - q - 1)^k`.  This is Claim 3.12's `|A|² e^{-k/t}`, still in integer form. -/
theorem card_bad_le (A : Finset (α → β)) (q k : ℕ) :
    ((Finset.univ : Finset (Fin k → α)).filter (fun s => Bad A q k s)).card
      ≤ A.card * A.card * (Fintype.card α - q - 1) ^ k := by
  classical
  by_cases hq : q < Fintype.card α
  · -- only the pairs that really differ in more than `q` coordinates can witness a bad tuple
    set P : Finset ((α → β) × (α → β)) :=
      (A.product A).filter (fun p => q < (Finset.univ.filter fun x => p.1 x ≠ p.2 x).card)
      with hP
    have hsub : (Finset.univ : Finset (Fin k → α)).filter (fun s => Bad A q k s)
        ⊆ P.biUnion (fun p : (α → β) × (α → β) => agreeTuples k p.1 p.2) := by
      intro s hs
      obtain ⟨-, a, ha, b, hb, hd, hag⟩ := Finset.mem_filter.mp hs
      rw [Finset.mem_biUnion]
      refine ⟨(a, b), ?_, mem_agreeTuples.mpr hag⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hd⟩
    have hpair : ∀ p ∈ P, (agreeTuples k p.1 p.2).card ≤ (Fintype.card α - q - 1) ^ k := by
      intro p hp
      obtain ⟨-, hd⟩ := Finset.mem_filter.mp hp
      rw [card_agreeTuples]
      -- `#agree = m - #disagree`, and `#disagree ≥ q + 1`
      have hde : (Finset.univ \ (Finset.univ.filter fun x => p.1 x ≠ p.2 x) : Finset α)
          = (Finset.univ.filter fun x => p.1 x = p.2 x) := by
        rw [Finset.sdiff_eq_filter]
        refine Finset.filter_congr fun x _ => ?_
        simp
      have hcard : (Finset.univ.filter fun x => p.1 x = p.2 x).card
          = Fintype.card α - (Finset.univ.filter fun x => p.1 x ≠ p.2 x).card := by
        rw [← hde, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_univ]
      have hagree : (Finset.univ.filter (fun x => p.1 x = p.2 x)).card
          ≤ Fintype.card α - q - 1 := by omega
      exact pow_le_pow_left₀ (Nat.zero_le _) hagree k
    calc ((Finset.univ : Finset (Fin k → α)).filter (fun s => Bad A q k s)).card
        ≤ (P.biUnion (fun p : (α → β) × (α → β) => agreeTuples k p.1 p.2)).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ p ∈ P, (agreeTuples k p.1 p.2).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ P, (Fintype.card α - q - 1) ^ k := Finset.sum_le_sum hpair
      _ = P.card • (Fintype.card α - q - 1) ^ k := Finset.sum_const _
      _ ≤ (A.card * A.card) • (Fintype.card α - q - 1) ^ k := by
          rw [nsmul_eq_mul, nsmul_eq_mul]
          refine Nat.mul_le_mul_right _ ?_
          calc P.card ≤ (A.product A).card := Finset.card_filter_le _ _
            _ = A.card * A.card := Finset.card_product _ _
      _ = A.card * A.card * (Fintype.card α - q - 1) ^ k := by
          rw [nsmul_eq_mul]; simp
  · -- if `q` is at least `m`, then no pair differs in more than `q` coordinates
    have hempty : (Finset.univ : Finset (Fin k → α)).filter (fun s => Bad A q k s) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro s _ hbad
      obtain ⟨a, -, b, -, hd, -⟩ := hbad
      have hle : (Finset.univ.filter fun x => a x ≠ b x).card ≤ Fintype.card α := by
        simpa using Finset.card_le_card
          (Finset.filter_subset (fun x => a x ≠ b x) (Finset.univ : Finset α))
      omega
    rw [hempty]
    simp


/-! ## The numeric budget `|A|² (1 - 1/t)^k < 1` -/

/-- **The analytic half of Claim 3.12.**  For `k = 2t(⌈log N⌉+1)` and `t ≥ 2`,
`N² (1 - 1/t)^k < 1`.  The paper writes this as `|A|² e^{-k/t} < 1` with `k = 2t(log|A|+1)`;
the only inequality used is `log(1 - 1/t) ≤ -1/t`, which is `Real.log_le_sub_one_of_pos`, so the
bound is exactly the paper's (with `⌈·⌉` the only slack). -/
theorem sample_budget {t : ℕ} (ht : 2 ≤ t) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) * N *
      (1 - 1 / (t : ℝ)) ^ (2 * t * (Nat.ceil (Real.log (N : ℝ)) + 1)) < 1 := by
  classical
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have ht1 : (1 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 1 < t)
  have hbase : (0 : ℝ) < 1 - 1 / (t : ℝ) := by
    have : 1 / (t : ℝ) < 1 := by
      rw [div_lt_one ht0]; exact ht1
    linarith
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  -- `(1 - 1/t)^k ≤ e^{-k/t}`, from `log(1 - 1/t) ≤ -1/t`
  have hA : (1 - 1 / (t : ℝ)) ^ (2 * t * (Nat.ceil (Real.log (N : ℝ)) + 1)) ≤
      Real.exp (-((2 * t * (Nat.ceil (Real.log (N : ℝ)) + 1) : ℕ) : ℝ) / (t : ℝ)) := by
    have hlog : Real.log (1 - 1 / (t : ℝ)) ≤ -(1 / (t : ℝ)) := by
      have h := Real.log_le_sub_one_of_pos hbase
      linarith
    calc (1 - 1 / (t : ℝ)) ^ (2 * t * (Nat.ceil (Real.log (N : ℝ)) + 1))
        = Real.exp (((2 * t * (Nat.ceil (Real.log (N : ℝ)) + 1) : ℕ) : ℝ) *
            Real.log (1 - 1 / (t : ℝ))) := by
          rw [Real.exp_natCast_mul, Real.exp_log hbase]
      _ ≤ Real.exp (((2 * t * (Nat.ceil (Real.log (N : ℝ)) + 1) : ℕ) : ℝ) *
            (-(1 / (t : ℝ)))) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlog (by positivity))
      _ = Real.exp (-((2 * t * (Nat.ceil (Real.log (N : ℝ)) + 1) : ℕ) : ℝ) / (t : ℝ)) := by
          congr 1
          ring
  -- `k/t = 2(⌈log N⌉+1) ≥ 2(log N + 1)`
  have hkB : ((2 * t * (Nat.ceil (Real.log (N : ℝ)) + 1) : ℕ) : ℝ) / (t : ℝ) =
      2 * ((Nat.ceil (Real.log (N : ℝ)) : ℝ) + 1) := by
    push_cast
    field_simp
  have hB : Real.exp (-((2 * t * (Nat.ceil (Real.log (N : ℝ)) + 1) : ℕ) : ℝ) / (t : ℝ)) ≤
      Real.exp (-(2 * (Real.log (N : ℝ) + 1))) := by
    apply Real.exp_le_exp.mpr
    have hneg : -((2 * t * (Nat.ceil (Real.log (N : ℝ)) + 1) : ℕ) : ℝ) / (t : ℝ) =
        -(((2 * t * (Nat.ceil (Real.log (N : ℝ)) + 1) : ℕ) : ℝ) / (t : ℝ)) := by ring
    rw [hneg, hkB]
    have hc := Nat.le_ceil (Real.log (N : ℝ))
    linarith
  -- `e^{-2(log N + 1)} = N⁻² e^{-2}`
  have hC : Real.exp (-(2 * (Real.log (N : ℝ) + 1))) =
      (N : ℝ)⁻¹ ^ 2 * Real.exp (-2) := by
    have hsplit : -(2 * (Real.log (N : ℝ) + 1)) = 2 * (-Real.log (N : ℝ)) + (-2) := by ring
    rw [hsplit, Real.exp_add]
    have h2 : Real.exp (2 * (-Real.log (N : ℝ))) = (N : ℝ)⁻¹ ^ 2 := by
      rw [show (2 : ℝ) * (-Real.log (N : ℝ)) = ((2 : ℕ) : ℝ) * (-Real.log (N : ℝ)) by
        norm_num]
      rw [Real.exp_natCast_mul, Real.exp_neg, Real.exp_log hN0]
    rw [h2]
  have hchain : (1 - 1 / (t : ℝ)) ^ (2 * t * (Nat.ceil (Real.log (N : ℝ)) + 1)) ≤
      (N : ℝ)⁻¹ ^ 2 * Real.exp (-2) :=
    hA.trans (hB.trans (le_of_eq hC))
  calc (N : ℝ) * N * (1 - 1 / (t : ℝ)) ^ (2 * t * (Nat.ceil (Real.log (N : ℝ)) + 1))
      ≤ (N : ℝ) * N * ((N : ℝ)⁻¹ ^ 2 * Real.exp (-2)) :=
        mul_le_mul_of_nonneg_left hchain (by positivity)
    _ = Real.exp (-2) := by
        field_simp
    _ < 1 := by
        rw [Real.exp_lt_one_iff]
        norm_num

/-! ## Claim 3.12 -/

/-- **Claim 3.12, machine-checked.**  For any finite family `A` of candidate preference vectors on
`Fintype α` and any `t ≥ 2`, there is a set `S` of coordinates of size at most
`2t(⌈log |A|⌉ + 1)` such that any two members of `A` agreeing on `S` differ on at most
`|α| / t` coordinates.

The paper's `m_i/t` is `q = Fintype.card α / t`; the paper's `|S*| = O(t√(mn))` follows by
instantiating `log |A| = O(√(mn))` (Lemma 3.10, not formalised here). -/
theorem claim312 (A : Finset (α → β)) (t q : ℕ) (ht : 2 ≤ t) (hq : q = Fintype.card α / t) :
    ∃ S : Finset α,
      S.card ≤ 2 * t * (Nat.ceil (Real.log (A.card : ℝ)) + 1) ∧
      ∀ a ∈ A, ∀ b ∈ A, (∀ x ∈ S, a x = b x) →
        (Finset.univ.filter (fun x => a x ≠ b x)).card ≤ q := by
  classical
  set k : ℕ := 2 * t * (Nat.ceil (Real.log (A.card : ℝ)) + 1) with hkdef
  have hkpos : 0 < k := by
    rw [hkdef]
    exact Nat.mul_pos (by omega) (by omega)
  by_cases hsmall : Fintype.card α = 0
  · refine ⟨∅, by simp, ?_⟩
    intro a _ b _ _
    have hempty : (Finset.univ : Finset α) = ∅ := Finset.card_eq_zero.mp (by simpa using hsmall)
    have : (Finset.univ.filter (fun x => a x ≠ b x) : Finset α) = ∅ := by
      rw [hempty]
      simp
    rw [this]
    simp
  · have hαpos : 0 < Fintype.card α := Nat.pos_of_ne_zero hsmall
    have hcount : A.card * A.card * (Fintype.card α - q - 1) ^ k < (Fintype.card α) ^ k := by
      by_cases hA0 : A.card = 0
      · rw [hA0]
        simp only [Nat.zero_mul]
        exact pow_pos hαpos k
      · have hN : 1 ≤ A.card := Nat.one_le_iff_ne_zero.mpr hA0
        by_cases hqα : q < Fintype.card α
        · have hbudget' : (A.card : ℝ) * A.card * (1 - 1 / (t : ℝ)) ^ k < 1 := by
            rw [hkdef]
            simpa using sample_budget (t := t) ht hN
          have hXle : ((Fintype.card α - q - 1 : ℕ) : ℝ) ≤
              (1 - 1 / (t : ℝ)) * (Fintype.card α : ℝ) := by
            have hqle : q + 1 ≤ Fintype.card α := by
              have hdiv : Fintype.card α / t < Fintype.card α :=
                Nat.div_lt_self hαpos (by omega)
              omega
            have hcast : ((Fintype.card α - q - 1 : ℕ) : ℝ) =
                (Fintype.card α : ℝ) - ((q : ℝ) + 1) := by
              rw [Nat.sub_sub, Nat.cast_sub hqle]
              push_cast
              ring
            rw [hcast]
            have hdecomp : t * q + Fintype.card α % t = Fintype.card α := by
              rw [hq]
              exact Nat.div_add_mod _ _
            have hmod : Fintype.card α % t < t := Nat.mod_lt _ (by omega)
            have hmcast : (Fintype.card α : ℝ) =
                (t : ℝ) * (q : ℝ) + ((Fintype.card α % t : ℕ) : ℝ) := by
              have h' : ((t * q + Fintype.card α % t : ℕ) : ℝ) = (Fintype.card α : ℝ) := by
                exact_mod_cast hdecomp
              push_cast at h'
              linarith
            have hrcast : ((Fintype.card α % t : ℕ) : ℝ) < (t : ℝ) := by
              exact_mod_cast hmod
            have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
            have hlt : (Fintype.card α : ℝ) < ((q : ℝ) + 1) * (t : ℝ) := by nlinarith
            have hdiv : (Fintype.card α : ℝ) / (t : ℝ) < (q : ℝ) + 1 := by
              rw [div_lt_iff₀ ht0]
              linarith
            have hstep : (Fintype.card α : ℝ) - ((q : ℝ) + 1) ≤
                (Fintype.card α : ℝ) - (Fintype.card α : ℝ) / (t : ℝ) := by linarith
            have heq : (Fintype.card α : ℝ) - (Fintype.card α : ℝ) / (t : ℝ) =
                (1 - 1 / (t : ℝ)) * (Fintype.card α : ℝ) := by
              field_simp
            linarith
          have hreal : ((A.card * A.card * (Fintype.card α - q - 1) ^ k : ℕ) : ℝ) <
              ((Fintype.card α ^ k : ℕ) : ℝ) := by
            push_cast
            have hmpos : (0 : ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast hαpos
            have hmul : (A.card : ℝ) * A.card * ((Fintype.card α - q - 1 : ℕ) : ℝ) ^ k ≤
                (A.card : ℝ) * A.card *
                  (((1 - 1 / (t : ℝ)) ^ k) * (Fintype.card α : ℝ) ^ k) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              calc ((Fintype.card α - q - 1 : ℕ) : ℝ) ^ k
                  ≤ ((1 - 1 / (t : ℝ)) * (Fintype.card α : ℝ)) ^ k :=
                    pow_le_pow_left₀ (by positivity) hXle k
                _ = ((1 - 1 / (t : ℝ)) ^ k) * (Fintype.card α : ℝ) ^ k := mul_pow _ _ k
            have hfin := mul_lt_mul_of_pos_right hbudget' (pow_pos hmpos k)
            calc (A.card : ℝ) * A.card * ((Fintype.card α - q - 1 : ℕ) : ℝ) ^ k
                ≤ (A.card : ℝ) * A.card *
                    (((1 - 1 / (t : ℝ)) ^ k) * (Fintype.card α : ℝ) ^ k) := hmul
              _ = ((A.card : ℝ) * A.card * (1 - 1 / (t : ℝ)) ^ k) *
                    (Fintype.card α : ℝ) ^ k := by ring
              _ < 1 * (Fintype.card α : ℝ) ^ k := hfin
              _ = (Fintype.card α : ℝ) ^ k := one_mul _
          exact_mod_cast hreal
        · have hX0 : Fintype.card α - q - 1 = 0 := by omega
          rw [hX0, Nat.zero_pow hkpos]
          simp only [Nat.mul_zero]
          exact pow_pos hαpos k
    have huniv : (Finset.univ : Finset (Fin k → α)).card = (Fintype.card α) ^ k := by
      simp
    have hlt : ((Finset.univ : Finset (Fin k → α)).filter (fun s => Bad A q k s)).card
        < (Finset.univ : Finset (Fin k → α)).card := by
      rw [huniv]
      exact lt_of_le_of_lt (card_bad_le A q k) hcount
    have hnotsub : ¬ (Finset.univ : Finset (Fin k → α)) ⊆
        (Finset.univ : Finset (Fin k → α)).filter (fun s => Bad A q k s) := by
      intro hsub
      have := Finset.card_le_card hsub
      omega
    obtain ⟨s, -, hs⟩ := Finset.not_subset.mp hnotsub
    refine ⟨Finset.image s Finset.univ, ?_, ?_⟩
    · have h : (Finset.image s (Finset.univ : Finset (Fin k))).card ≤ k := by
        have h1 : (Finset.image s (Finset.univ : Finset (Fin k))).card ≤
            (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
        simpa using h1
      simpa using h
    · intro a ha b hb hagree
      by_contra hcon
      have hd : q < (Finset.univ.filter fun x => a x ≠ b x).card := Nat.lt_of_not_le hcon
      exact hs (Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, ha, b, hb, hd,
        fun i => hagree (s i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩)

end DLMST