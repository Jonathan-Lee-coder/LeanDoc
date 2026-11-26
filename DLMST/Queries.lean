import DLMST.EstimateBound
import DLMST.CallFromRounds

/-!
# §3.5's selection step: the sample is computed, the estimate interpolated

`EstimateBound.lean` reduced §3.5 to two facts about the driver: per round, the true preference
vector and the estimate are both members of the round's candidate family `A r`, and the estimate
agrees with the truth on Claim 3.12's sample `S r`.  The paper's §3.5 makes the sample and the
estimate *constructive*:

> Again, the algorithm can explicitly find such a set `S` by enumerating and checking, without making
> any comparisons.  It then queries the true preferred actions for edges in `S` and selects any vector
> in `A` consistent with the queried answers as the estimate.

The two steps have very different status, and this file separates them:

* `sampleSets` is Claim 3.12's sample, a function of `(A, t, slot)` alone — the truth is not used, so
  the algorithm really does fix its queries before asking anything (`sampleSets_card`,
  `sampleSets_sep`).  This is a construction, not a hypothesis.
* The *estimate* is any vector of `A` consistent with the queries.  Which one it is does not matter:
  `mis_count_of_sample` shows that **every** consistent candidate mis-estimates at most `Σ mᵢ/t = m/t`
  edges.  So there is nothing to choose — only consistency to check (`per_round_mis` is the per-round
  count for an arbitrary consistent `est`).

With that, §3.3's error premise needs only Lemma 3.7's per-edge conclusion for the estimate in use,
the family's coverage, and Lemma 3.11's `lost` bound (`card_U_le_number_bound_of_queries`,
`card_U_le_display_form_of_queries`); the sampling hypotheses `hest`/agreement of
`card_U_le_number_bound_of_sampling` remain, but the sample is no longer data — it is `sampleSets`.

The one fact that cannot come from `A` is `truth ∈ A r` (`htruth`): the family must contain the
vectors that can occur, which is the *definition* of `A` ("the family of all such vectors",
conditioned on the current forest and spokes), not a property of the sampling.  Its size
`log |A| = O(√(mn))` is Lemma 3.10's count, a separate object.
-/

namespace DLMST

open Classical

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] {G : WGraph V E}

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-! ## Claim 3.12's sample, computed from the family alone -/

/-- **The queried coordinates.**  Claim 3.12's sample for every round, computed from the candidate
family `A` and the round index only — no knowledge of the truth enters, which is the paper's "the
algorithm can explicitly find such a set `S` by enumerating and checking, without making any
comparisons". -/
noncomputable def sampleSets {t : ℕ} (ht : 2 ≤ t) (slot : E → σ)
    (A : ∀ r : σ, Finset ({e : E // slot e = r} → Pref)) : ∀ r : σ, Finset {e : E // slot e = r} :=
  fun r => Classical.choose (claim312 (A r) t (Fintype.card {e : E // slot e = r} / t) ht rfl)

/-- The sample is small: `|S r| ≤ 2t(⌈log|A r|⌉+1)`. -/
theorem sampleSets_card {t : ℕ} (ht : 2 ≤ t) (slot : E → σ)
    (A : ∀ r : σ, Finset ({e : E // slot e = r} → Pref)) (r : σ) :
    (sampleSets ht slot A r).card ≤
      2 * t * (Nat.ceil (Real.log ((A r).card : ℝ)) + 1) :=
  (Classical.choose_spec (claim312 (A r) t _ ht rfl)).1

/-- The sample separates: two candidates of `A r` agreeing on it differ on at most `|fibre r|/t`
coordinates of the round. -/
theorem sampleSets_sep {t : ℕ} (ht : 2 ≤ t) (slot : E → σ)
    (A : ∀ r : σ, Finset ({e : E // slot e = r} → Pref)) (r : σ) :
    ∀ a ∈ A r, ∀ b ∈ A r, (∀ x ∈ sampleSets ht slot A r, a x = b x) →
      (Finset.univ.filter fun x : {e : E // slot e = r} => a x ≠ b x).card ≤
        Fintype.card {e : E // slot e = r} / t :=
  (Classical.choose_spec (claim312 (A r) t _ ht rfl)).2

/-! ## §3.5's per-round count, for an arbitrary consistent candidate -/

/-- **A round's mis-estimates.**  Agreement on the sample plus Claim 3.12's separation (read on the
fibre `{e // slot e = r}`) bounds the mis-estimated edges of round `r` by `|fibre r|/t`.  The sample
`sampleSets` was fixed before `est` was chosen, and the estimate is used only through "it is a
candidate" and "it answers the queries" — so this holds for every consistent candidate. -/
theorem per_round_mis {t : ℕ} (ht : 2 ≤ t) (slot : E → σ)
    (A : ∀ r : σ, Finset ({e : E // slot e = r} → Pref)) (truth est : E → Pref)
    (htruth : ∀ r, (fun x : {e : E // slot e = r} => truth x.1) ∈ A r)
    (hest : ∀ r, (fun x : {e : E // slot e = r} => est x.1) ∈ A r)
    (hagree : ∀ (r : σ) (x : {e : E // slot e = r}), x ∈ sampleSets ht slot A r →
      est x.1 = truth x.1)
    (r : σ) :
    ((Finset.univ.filter fun e => est e ≠ truth e ∧ slot e = r).card : ℝ) ≤
      ((Finset.univ.filter fun e => slot e = r).card : ℝ) / (t : ℝ) := by
  classical
  have hsep := sampleSets_sep ht slot A r
    (fun x : {e : E // slot e = r} => truth x.1) (htruth r)
    (fun x : {e : E // slot e = r} => est x.1) (hest r)
    (fun x hx => (hagree r x hx).symm)
  have hfilter : (Finset.univ.filter fun x : {e : E // slot e = r} => est x.1 ≠ truth x.1) =
      (Finset.univ.filter fun x : {e : E // slot e = r} => truth x.1 ≠ est x.1) := by
    refine Finset.filter_congr fun x _ => ?_
    exact ne_comm
  have h' : ((Finset.univ.filter fun x : {e : E // slot e = r} => est x.1 ≠ truth x.1).card : ℝ) ≤
      (Fintype.card {e : E // slot e = r} : ℝ) / (t : ℝ) := by
    have h1 : ((Finset.univ.filter fun x : {e : E // slot e = r} => est x.1 ≠ truth x.1).card : ℝ) ≤
        ((Fintype.card {e : E // slot e = r} / t : ℕ) : ℝ) := by
      rw [hfilter]
      exact_mod_cast hsep
    exact le_trans h1 Nat.cast_div_le
  have hbij : (Finset.univ.filter fun x : {e : E // slot e = r} => est x.1 ≠ truth x.1).card =
      (Finset.univ.filter fun e : E => est e ≠ truth e ∧ slot e = r).card := by
    refine Finset.card_bij (fun (x : {e : E // slot e = r}) _ => x.1) ?_ ?_ ?_
    · intro x hx
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2, x.2⟩
    · intro x₁ _ x₂ _ h
      exact Subtype.ext h
    · intro e he
      obtain ⟨-, hne, hslot⟩ := Finset.mem_filter.mp he
      exact ⟨⟨e, hslot⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩, rfl⟩
  have hcard : (Fintype.card {e : E // slot e = r} : ℝ) =
      ((Finset.univ.filter fun e => slot e = r).card : ℝ) := by
    rw [Fintype.card_subtype (p := fun e : E => slot e = r)]
  rw [hbij, hcard] at h'
  exact h'

/-- **§3.5's total, for any consistent candidate.**  Every edge is scheduled into one round, so a
candidate of the family that answers the queries mis-estimates at most `|E|/t` edges: "the total
number of edges with incorrect estimates is at most `Σ mᵢ/t = m/t`".  The algorithm's "selects any
vector in `A` consistent with the queried answers" therefore costs nothing. -/
theorem mis_count_of_sample {t : ℕ} (ht : 2 ≤ t) (slot : E → σ)
    (A : ∀ r : σ, Finset ({e : E // slot e = r} → Pref)) (truth est : E → Pref)
    (htruth : ∀ r, (fun x : {e : E // slot e = r} => truth x.1) ∈ A r)
    (hest : ∀ r, (fun x : {e : E // slot e = r} => est x.1) ∈ A r)
    (hagree : ∀ (r : σ) (x : {e : E // slot e = r}), x ∈ sampleSets ht slot A r →
      est x.1 = truth x.1) :
    ((Finset.univ.filter fun e => est e ≠ truth e).card : ℝ) ≤
      (Fintype.card E : ℝ) / (t : ℝ) := by
  classical
  refine card_mis_le slot (fun e => est e ≠ truth e)
    (fun r => (Finset.univ.filter fun e => slot e = r).card) ?_ ?_
  · intro r
    exact per_round_mis ht slot A truth est htruth hest hagree r
  · rw [← Finset.card_univ,
      Finset.card_eq_sum_card_fiberwise (f := slot) (s := (Finset.univ : Finset E))
        (t := (Finset.univ : Finset σ)) (fun e _ => Finset.mem_univ _)]

/-! ## §3.3's error premise with the sample computed -/

namespace CallOut

namespace RoundData

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder E] {t : ℕ} {P : Finset V}
  {E₀ : Finset E} (D : RoundData G P E₀ ι t)

/-- **§3.3's instance error premise, with Claim 3.12's sample computed from the candidate family.**
Compared with `card_U_le_number_bound_of_sampling`, the sample is no longer data: it is `sampleSets`,
a function of `A` and the round index alone, which is what makes the algorithm executable.  The
estimate `est` is still arbitrary — the count holds for every consistent candidate
(`mis_count_of_sample`).  What remains is Lemma 3.7's per-edge conclusion for `est` (a process fact),
the family's coverage `htruth`, and Lemma 3.11's `lost` bound. -/
theorem card_U_le_number_bound_of_queries {s t : ℕ} (H : History V E s)
    (est : E → Pref) (slot : E → Fin s × Fin s) {m n : ℝ} (ht : 2 ≤ t) (hm : 0 ≤ m) (hn : 0 ≤ n)
    (hmE : (Fintype.card E : ℝ) ≤ m)
    (A : ∀ r : Fin s × Fin s, Finset ({e : E // slot e = r} → Pref))
    (htruth : ∀ r : Fin s × Fin s,
      (fun x : {e : E // slot e = r} => H.pref x.1 (slot x.1).1 (slot x.1).2) ∈ A r)
    (hest : ∀ r : Fin s × Fin s, (fun x : {e : E // slot e = r} => est x.1) ∈ A r)
    (hagree : ∀ (r : Fin s × Fin s) (x : {e : E // slot e = r}), x ∈ sampleSets ht slot A r →
      est x.1 = H.pref x.1 (slot x.1).1 (slot x.1).2)
    (h : ∀ e ∈ E₀, ¬ supported G D.F e → H.errOf est e (slot e))
    (hlost : (H.lost slot : ℝ) * Real.log 2 ≤
      (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 * Real.sqrt (m * n) + 2 * m / (t : ℝ)) :
    (D.U.card : ℝ) ≤ 10 * (t : ℝ) ^ 2 * Real.sqrt (m * n) + 4 * m / (t : ℝ) := by
  have hmis : ((Finset.univ.filter fun e =>
      est e ≠ H.pref e (slot e).1 (slot e).2).card : ℝ) ≤ (Fintype.card E : ℝ) / (t : ℝ) :=
    mis_count_of_sample ht slot A (fun e => H.pref e (slot e).1 (slot e).2) est htruth hest
      (fun r x hx => hagree r x hx)
  exact D.card_U_le_number_bound_of_all_mis H est slot (by omega) hm hn hmE h hlost hmis

/-- **The same count in the display's shape** (`toCall`'s retained set), for `Strategy.Counts`. -/
theorem card_U_le_display_form_of_queries {s t : ℕ} (H : History V E s)
    (est : E → Pref) (slot : E → Fin s × Fin s) {m n : ℝ} (ht : 2 ≤ t) (hm : 0 ≤ m) (hn : 0 ≤ n)
    (hmE : (Fintype.card E : ℝ) ≤ m)
    (A : ∀ r : Fin s × Fin s, Finset ({e : E // slot e = r} → Pref))
    (htruth : ∀ r : Fin s × Fin s,
      (fun x : {e : E // slot e = r} => H.pref x.1 (slot x.1).1 (slot x.1).2) ∈ A r)
    (hest : ∀ r : Fin s × Fin s, (fun x : {e : E // slot e = r} => est x.1) ∈ A r)
    (hagree : ∀ (r : Fin s × Fin s) (x : {e : E // slot e = r}), x ∈ sampleSets ht slot A r →
      est x.1 = H.pref x.1 (slot x.1).1 (slot x.1).2)
    (h : ∀ e ∈ E₀, ¬ supported G D.F e → H.errOf est e (slot e))
    (hlost : (H.lost slot : ℝ) * Real.log 2 ≤
      (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 * Real.sqrt (m * n) + 2 * m / (t : ℝ)) :
    ((D.toCall.U).card : ℝ) ≤ 10 * (t : ℝ) ^ 2 * Real.sqrt (m * n) + 4 * m / (t : ℝ) :=
  card_U_le_number_bound_of_queries (D := D) H est slot ht hm hn hmE A htruth hest hagree
    h hlost

end RoundData

end CallOut

end DLMST