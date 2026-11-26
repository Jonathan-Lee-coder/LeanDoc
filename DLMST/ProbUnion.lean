import DLMST.Prob
import DLMST.Sampling

/-!
# B4 (continued): union bounds, independence, and the sample probability

`Prob.lean` supplies the finite-uniform probability layer.  This file adds the two *combinatorial*
operations the paper's §3.4–§3.5 actually use when several bad events must be avoided at once:

* `unifProb_union_le` / `unifProb_biUnion_le` — the union bound on finite uniform spaces;
* **`unifProb_all_good_ge`** — Bonferroni: if each of the events `Bᵢ` has probability `≤ δᵢ`, then all
  of them are avoided simultaneously with probability `≥ 1 − Σ δᵢ`;
* **`unifProb_indep`** — on a product space, the probability of the product event multiplies, the
  exact form of the paper's "the coordinates are sampled independently";
* **`unifProb_prod_two_good`** — consequence: two independent good events hold jointly with
  probability `≥ 1 − (δ + ε)`;
* **`claim312_four_fifths`** — the paper's `1 − e^{−2} ≥ 4/5`, a concrete guarantee for the sample;
* **`unifProb_agreeTuples` / `bad_prob_le_union`** — Claim 3.12 derived the paper's way: the
  probability that a random `k`-tuple agrees with a fixed pair is the `k`-th power of the
  single-coordinate agreement probability (`unifProb_agreeTuples`), a badly-differing pair agrees with
  probability `≤ (1 − 1/t)^k` (`unifProb_agreeTuples_le`), and the union bound over the `|A|²` pairs
  gives `P[bad] ≤ |A|² (1 − 1/t)^k` (`bad_prob_le_union`) — the probabilistic companion of
  `Sampling.bad_prob_le`, which counts the same quantity.

Everything is still a statement about exact finite counts; the algorithm remains deterministic
(boundary B4): these probabilities prove that good schedules and samples *exist*.
-/

namespace DLMST

open Classical

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-- **The union bound** on a finite uniform space. -/
theorem unifProb_union_le {Ω : Type*} [Fintype Ω] (S T : Finset Ω) :
    unifProb (S ∪ T) ≤ unifProb S + unifProb T := by
  have hN : (0 : ℝ) ≤ (Fintype.card Ω : ℝ) := by positivity
  have h : (((S ∪ T).card : ℕ) : ℝ) ≤ ((S.card + T.card : ℕ) : ℝ) := by
    exact_mod_cast Finset.card_union_le S T
  unfold unifProb
  calc ((S ∪ T).card : ℝ) / (Fintype.card Ω : ℝ)
      ≤ (((S.card + T.card : ℕ)) : ℝ) / (Fintype.card Ω : ℝ) :=
        div_le_div_of_nonneg_right (by simpa using h) hN
    _ = (S.card : ℝ) / (Fintype.card Ω : ℝ) + (T.card : ℝ) / (Fintype.card Ω : ℝ) := by
        push_cast
        ring

/-- **The union bound over a finite family**: `P[⋃ᵢ Bᵢ] ≤ Σᵢ P[Bᵢ]`. -/
theorem unifProb_biUnion_le {ι Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (t : Finset ι) (B : ι → Finset Ω) :
    unifProb (t.biUnion B) ≤ ∑ i ∈ t, unifProb (B i) := by
  have hNpos : (0 : ℝ) < (Fintype.card Ω : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hcard : ((t.biUnion B).card : ℝ) ≤ ∑ i ∈ t, ((B i).card : ℝ) := by
    calc ((t.biUnion B).card : ℝ) ≤ (((∑ i ∈ t, (B i).card : ℕ)) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ = ∑ i ∈ t, ((B i).card : ℝ) := by push_cast; ring
  have hsplit : (∑ i ∈ t, ((B i).card : ℝ) / (Fintype.card Ω : ℝ)) * (Fintype.card Ω : ℝ) =
      ∑ i ∈ t, ((B i).card : ℝ) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact div_mul_cancel₀ _ hNpos.ne'
  unfold unifProb
  rw [div_le_iff₀ hNpos]
  calc ((t.biUnion B).card : ℝ)
      ≤ ∑ i ∈ t, ((B i).card : ℝ) := hcard
    _ = (∑ i ∈ t, ((B i).card : ℝ) / (Fintype.card Ω : ℝ)) * (Fintype.card Ω : ℝ) :=
        hsplit.symm

/-- **Bonferroni's inequality** (the "bad events avoided simultaneously" union bound): if each of the
events `Bᵢ` has uniform probability at most `δᵢ`, then with probability at least `1 − Σ δᵢ` none of
them happens.  This is the shape of Claim 3.12's conclusion and of "all estimates are good at once"
in §3.5. -/
theorem unifProb_all_good_ge {ι Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (t : Finset ι) (B : ι → Finset Ω) (δ : ι → ℝ)
    (h : ∀ i ∈ t, unifProb (B i) ≤ δ i) :
    1 - ∑ i ∈ t, δ i ≤
      unifProb (Finset.univ.filter (fun ω => ∀ i ∈ t, ω ∉ B i)) := by
  classical
  set p : Ω → Prop := fun ω => ∀ i ∈ t, ω ∉ B i with hp
  have hcompl := unifProb_compl (S := Finset.univ.filter p)
    (T := Finset.univ.filter (fun ω => ¬ p ω))
    (by exact Finset.disjoint_filter.mpr (fun ω _ h1 h2 => h2 h1))
    (by rw [Finset.filter_union_filter_not_eq])
  have hsub : Finset.univ.filter (fun ω => ¬ p ω) ⊆ t.biUnion B := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    rw [hp] at hω
    rw [Finset.mem_biUnion]
    by_contra hc
    simp only [not_exists] at hc
    exact hω fun i hi hmem => hc i ⟨hi, hmem⟩
  have h1 : unifProb (Finset.univ.filter (fun ω => ¬ p ω)) ≤ unifProb (t.biUnion B) :=
    unifProb_mono hsub
  have h2 := unifProb_biUnion_le t B
  have h3 : ∑ i ∈ t, unifProb (B i) ≤ ∑ i ∈ t, δ i := Finset.sum_le_sum h
  linarith

/-- **Independence on a product space**: for independent uniform coordinates, the probability of the
product event is the product of the probabilities.  The paper's "each of the `k` sampled edges is
uniform and independent" is this identity, read at `Finset.product`. -/
theorem unifProb_indep {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]
    (S : Finset Ω₁) (T : Finset Ω₂) :
    unifProb (S ×ˢ T) = unifProb S * unifProb T := by
  by_cases h1 : (Fintype.card Ω₁) = 0
  · haveI : IsEmpty Ω₁ := Fintype.card_eq_zero_iff.mp h1
    simp [unifProb]
  · by_cases h2 : (Fintype.card Ω₂) = 0
    · haveI : IsEmpty Ω₂ := Fintype.card_eq_zero_iff.mp h2
      simp [unifProb]
    · have h1p : (0 : ℝ) < (Fintype.card Ω₁ : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero h1
      have h2p : (0 : ℝ) < (Fintype.card Ω₂ : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero h2
      unfold unifProb
      rw [Finset.card_product, Fintype.card_prod]
      push_cast
      field_simp

/-- **Two independent good events.**  If `S` holds with probability `≥ 1 − δ` and `T` with
probability `≥ 1 − ε`, then on the product space both hold with probability `≥ 1 − (δ + ε)` — the
joint form behind "one good schedule *and* one good sample". -/
theorem unifProb_prod_two_good {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]
    [Nonempty Ω₁] [Nonempty Ω₂] (S : Finset Ω₁) (T : Finset Ω₂) {δ ε : ℝ}
    (hδ0 : 0 ≤ δ) (hε0 : 0 ≤ ε) (hδ1 : δ ≤ 1) (hε1 : ε ≤ 1) (hS : 1 - δ ≤ unifProb S) (hT : 1 - ε ≤ unifProb T) :
    1 - (δ + ε) ≤ unifProb (S ×ˢ T) := by
  have hprod := unifProb_indep S T
  have hS1 : unifProb S ≤ 1 := by
    unfold unifProb
    rw [div_le_iff₀ (by exact_mod_cast Fintype.card_pos :
      (0 : ℝ) < (Fintype.card Ω₁))]
    simpa using (by exact_mod_cast Finset.card_le_univ S :
      ((S.card : ℕ) : ℝ) ≤ ((Fintype.card Ω₁ : ℕ) : ℝ))
  have hT1 : unifProb T ≤ 1 := by
    unfold unifProb
    rw [div_le_iff₀ (by exact_mod_cast Fintype.card_pos :
      (0 : ℝ) < (Fintype.card Ω₂))]
    simpa using (by exact_mod_cast Finset.card_le_univ T :
      ((T.card : ℕ) : ℝ) ≤ ((Fintype.card Ω₂ : ℕ) : ℝ))
  have h0 : 0 ≤ 1 - δ := by linarith
  have h1 : 0 ≤ 1 - ε := by linarith
  calc 1 - (δ + ε) ≤ (1 - δ) * (1 - ε) := by nlinarith
    _ ≤ unifProb S * unifProb T :=
        mul_le_mul hS hT h1 (by unfold unifProb; positivity)
    _ = unifProb (S ×ˢ T) := hprod.symm

/-- **The paper's constant, numerically**: `1 − e^{−2} ≥ 4/5`. -/
theorem claim312_four_fifths : (4 : ℝ) / 5 ≤ 1 - Real.exp (-2) := by
  have hexp2 : Real.exp 2 = Real.exp 1 ^ 2 := by
    have h : (2 : ℝ) = ((2 : ℕ) : ℝ) * 1 := by norm_num
    rw [h, Real.exp_natCast_mul]
  have hgt : (5 : ℝ) < Real.exp 2 := by
    rw [hexp2]
    nlinarith [Real.exp_one_gt_d9]
  have hinv : Real.exp (-2) ≤ (5 : ℝ)⁻¹ := by
    rw [Real.exp_neg]
    rw [inv_le_inv₀ (Real.exp_pos 2) (by norm_num)]
    linarith
  have h15 : (5 : ℝ)⁻¹ = 1 / 5 := by norm_num
  linarith

/-! ## Claim 3.12 through independence and the union bound -/

section SampleProb

variable {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β] [Nonempty α]

/-- **Independence of the sampled coordinates, as a probability**: the uniform probability that a
random `k`-tuple agrees with a fixed pair on every coordinate is the `k`-th power of the
single-coordinate agreement probability. -/
theorem unifProb_agreeTuples {k : ℕ} (a b : α → β) :
    unifProb (agreeTuples k a b) =
      (((Finset.univ.filter (fun x => a x = b x)).card : ℝ) / (Fintype.card α : ℝ)) ^ k := by
  have hN : Fintype.card (Fin k → α) = Fintype.card α ^ k := by
    rw [Fintype.card_fun]
    simp
  unfold unifProb
  rw [card_agreeTuples, hN]
  push_cast
  rw [← div_pow]

/-- **Per-pair probability at the paper's threshold**: a pair differing in more than `q = M/t`
coordinates agrees on a random `k`-tuple with probability at most `(1 − 1/t)^k`. -/
theorem unifProb_agreeTuples_le {t q k : ℕ} (ht : 2 ≤ t) (hq : q = Fintype.card α / t)
    (a b : α → β) (hd : q < (Finset.univ.filter fun x => a x ≠ b x).card) :
    unifProb (agreeTuples k a b) ≤ (1 - 1 / (t : ℝ)) ^ k := by
  classical
  rw [unifProb_agreeTuples]
  set M := Fintype.card α with hMdef
  have hM0 : (0 : ℝ) < (M : ℝ) := by
    rw [hMdef]; exact_mod_cast Fintype.card_pos
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  set dis := (Finset.univ.filter fun x => a x ≠ b x).card with hdisdef
  have hdisM : dis ≤ M := by
    rw [hdisdef, hMdef]; exact Finset.card_le_univ _
  have hde : (Finset.univ \ (Finset.univ.filter fun x => a x ≠ b x) : Finset α)
      = (Finset.univ.filter fun x => a x = b x) := by
    rw [Finset.sdiff_eq_filter]
    exact Finset.filter_congr fun x _ => by simp
  have hcard : (Finset.univ.filter fun x => a x = b x).card = M - dis := by
    rw [← hde, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_univ,
      hMdef, hdisdef]
  have hqle : q + 1 ≤ M := by omega
  have hagree : (Finset.univ.filter (fun x => a x = b x)).card ≤ M - q - 1 := by omega
  have hcastagree : ((Finset.univ.filter (fun x => a x = b x)).card : ℝ) ≤
      (M : ℝ) - ((q : ℝ) + 1) := by
    have hsub : (((M - q - 1 : ℕ)) : ℝ) = (M : ℝ) - ((q : ℝ) + 1) := by
      rw [Nat.sub_sub, Nat.cast_sub hqle]
      push_cast
      ring
    exact le_trans (by exact_mod_cast hagree) hsub.le
  have hdecomp : t * q + M % t = M := by
    rw [hq]; exact Nat.div_add_mod M t
  have hdiv : (M : ℝ) / (t : ℝ) ≤ (q : ℝ) + 1 := by
    have hmod : M % t < t := Nat.mod_lt _ (by omega)
    have hmcast : (M : ℝ) = (t : ℝ) * (q : ℝ) + ((M % t : ℕ) : ℝ) := by
      have h' : ((t * q + M % t : ℕ) : ℝ) = (M : ℝ) := by exact_mod_cast hdecomp
      push_cast at h'
      linarith
    have hrcast : ((M % t : ℕ) : ℝ) < (t : ℝ) := by exact_mod_cast hmod
    rw [div_le_iff₀ ht0]
    nlinarith
  have hgoal1 : 1 / (t : ℝ) ≤ ((q : ℝ) + 1) / (M : ℝ) := by
    have hMle : (M : ℝ) ≤ ((q : ℝ) + 1) * (t : ℝ) := by
      rw [div_le_iff₀ ht0] at hdiv
      linarith
    rw [div_le_div_iff₀ ht0 hM0]
    linarith
  have hstep : ((Finset.univ.filter (fun x => a x = b x)).card : ℝ) / (M : ℝ) ≤
      1 - 1 / (t : ℝ) := by
    have h1 : ((Finset.univ.filter (fun x => a x = b x)).card : ℝ) / (M : ℝ) ≤
        ((M : ℝ) - ((q : ℝ) + 1)) / (M : ℝ) :=
      div_le_div_of_nonneg_right hcastagree hM0.le
    have h2 : ((M : ℝ) - ((q : ℝ) + 1)) / (M : ℝ) = 1 - ((q : ℝ) + 1) / (M : ℝ) := by
      field_simp
    have h3 : 1 - ((q : ℝ) + 1) / (M : ℝ) ≤ 1 - 1 / (t : ℝ) := by linarith
    linarith
  exact pow_le_pow_left₀ (by positivity) hstep k

/-- **Claim 3.12 as a union bound over pairs**: the bad-tuple event is contained in the union, over
badly-differing pairs of candidates, of their agreement events; the union bound and the per-pair
bound `(1 − 1/t)^k` give the paper's sum. -/
theorem bad_prob_le_via_union (A : Finset (α → β)) {t q k : ℕ} (ht : 2 ≤ t)
    (hq : q = Fintype.card α / t) :
    unifProb (Finset.univ.filter (fun s : Fin k → α => Bad A q k s)) ≤
      ∑ _p ∈ (A ×ˢ A).filter (fun p : (α → β) × (α → β) =>
        q < (Finset.univ.filter fun x => p.1 x ≠ p.2 x).card),
        (1 - 1 / (t : ℝ)) ^ k := by
  classical
  haveI : Nonempty (Fin k → α) := ⟨fun _ => Classical.arbitrary α⟩
  set P : Finset ((α → β) × (α → β)) := (A ×ˢ A).filter (fun p =>
    q < (Finset.univ.filter fun x => p.1 x ≠ p.2 x).card) with hP
  have hsub : Finset.univ.filter (fun s : Fin k → α => Bad A q k s) ⊆
      P.biUnion (fun p : (α → β) × (α → β) => agreeTuples k p.1 p.2) := by
    intro s hs
    obtain ⟨-, a, ha, b, hb, hd, hag⟩ := Finset.mem_filter.mp hs
    rw [Finset.mem_biUnion]
    refine ⟨(a, b), ?_, mem_agreeTuples.mpr hag⟩
    rw [hP]
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hd⟩
  calc unifProb (Finset.univ.filter (fun s : Fin k → α => Bad A q k s))
      ≤ unifProb (P.biUnion (fun p : (α → β) × (α → β) => agreeTuples k p.1 p.2)) :=
        unifProb_mono hsub
    _ ≤ ∑ p ∈ P, unifProb (agreeTuples k p.1 p.2) := unifProb_biUnion_le P _
    _ ≤ ∑ p ∈ P, (1 - 1 / (t : ℝ)) ^ k := by
        refine Finset.sum_le_sum fun p hp => ?_
        exact unifProb_agreeTuples_le ht hq p.1 p.2 (Finset.mem_filter.mp hp).2

/-- **Claim 3.12's conclusion, via the union bound**: at most `|A|² (1 − 1/t)^k` of the `k`-tuples
are bad — the same bound as `bad_prob_le`, but derived through independence and a union bound over
pairs rather than by counting agreement tuples. -/
theorem bad_prob_le_union (A : Finset (α → β)) {t q k : ℕ} (ht : 2 ≤ t)
    (hq : q = Fintype.card α / t) :
    unifProb (Finset.univ.filter (fun s : Fin k → α => Bad A q k s)) ≤
      (A.card : ℝ) ^ 2 * (1 - 1 / (t : ℝ)) ^ k := by
  classical
  refine (bad_prob_le_via_union A ht hq).trans ?_
  set P : Finset ((α → β) × (α → β)) := (A ×ˢ A).filter (fun p =>
    q < (Finset.univ.filter fun x => p.1 x ≠ p.2 x).card) with hP
  have hPcard : P.card ≤ A.card * A.card := by
    calc P.card ≤ (A ×ˢ A).card := Finset.card_filter_le _ _
      _ = A.card * A.card := Finset.card_product A A
  have hsum : ∑ p ∈ P, (1 - 1 / (t : ℝ)) ^ k = (P.card : ℝ) * (1 - 1 / (t : ℝ)) ^ k := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hsum]
  have hpow0 : (0 : ℝ) ≤ (1 - 1 / (t : ℝ)) ^ k := by
    have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
    have h1t : 1 / (t : ℝ) < 1 := by
      rw [div_lt_one ht0]; exact_mod_cast (by omega : 1 < t)
    exact pow_nonneg (by linarith) k
  have hcast : (P.card : ℝ) ≤ (A.card : ℝ) * A.card := by exact_mod_cast hPcard
  calc (P.card : ℝ) * (1 - 1 / (t : ℝ)) ^ k
      ≤ ((A.card : ℝ) * A.card) * (1 - 1 / (t : ℝ)) ^ k :=
        mul_le_mul_of_nonneg_right hcast hpow0
    _ = (A.card : ℝ) ^ 2 * (1 - 1 / (t : ℝ)) ^ k := by ring

end SampleProb

end DLMST