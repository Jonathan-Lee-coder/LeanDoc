import DLMST.Dispatch
import DLMST.Sampling

/-!
# §3.5's `m/t`: the total number of mis-estimated edges

Claim 3.12 (`Sampling.claim312`) gives, in each round, a sample `S*` such that any two preference
vectors consistent on `S*` disagree on at most `|α|/t` coordinates.  The algorithm's estimate is
chosen from the vectors consistent with the queried true values, so *the number of edges whose
estimate is wrong in that round is at most `mᵢ/t`*, where `mᵢ` is the number of edges scheduled in
round `i`.  Summing that over the `t²` rounds and using the fiber identity
`Σ mᵢ = |E|` (`Dispatch.sum_rEdges_card`) gives the paper's "the total number of edges with incorrect
estimates is at most `Σ mᵢ/t = m/t`" — `misestimate_total_le` below.

Only the arithmetic is formalised here: which edges are mis-estimated is the algorithm's business,
and that is exactly the part the paper leaves to the (unformalised) driver.
-/

namespace DLMST

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- **`Σ mᵢ/t = m/t`, machine-checked.**  If round `i` mis-estimates at most `mᵢ/t` edges, then the
whole run mis-estimates at most `|E|/t` — the `m/t` term of §3.5.  The two inputs are the per-round
bound and `Dispatch.sum_rEdges_card`. -/
theorem misestimate_total_le {t : ℕ} (sched : E → ℕ) (hbound : ∀ e, sched e < t ^ 2)
    (mis : ℕ → ℕ) (hper : ∀ r : ℕ, (mis r : ℝ) ≤ (rEdges sched r).card / (t : ℝ)) :
    ((Finset.sum (Finset.range (t ^ 2)) mis : ℕ) : ℝ) ≤ (Fintype.card E : ℝ) / (t : ℝ) := by
  calc ((Finset.sum (Finset.range (t ^ 2)) mis : ℕ) : ℝ)
      = Finset.sum (Finset.range (t ^ 2)) (fun r => (mis r : ℝ)) := by push_cast; rfl
    _ ≤ Finset.sum (Finset.range (t ^ 2))
          (fun r => ((rEdges sched r).card : ℝ) / (t : ℝ)) :=
        Finset.sum_le_sum (fun r _ => hper r)
    _ = ((Finset.sum (Finset.range (t ^ 2)) (fun r => (rEdges sched r).card) : ℕ) : ℝ) /
          (t : ℝ) := by
        rw [← Finset.sum_div]
        push_cast
        rfl
    _ = (Fintype.card E : ℝ) / (t : ℝ) := by rw [sum_rEdges_card sched hbound]

/-- **The mis-estimate half of §3.3, as the display consumes it.**  Every edge is scheduled into one of
the `t²` rounds; if round `r` mis-estimates at most `mᵣ/t` of *its own* edges (`hper`) and the per-round
allowances total at most `|E|` (`hsum`), then the set of mis-estimated edges has at most `|E|/t`
elements — the `err2 ≤ m/t` premise of `error_count_le`.  The count is made exact by the fiberwise
identity `∑_r #(wrong ∩ slot⁻¹r) = #wrong`. -/
theorem card_mis_le {σ : Type*} [Fintype σ] [DecidableEq σ] {t : ℕ} (slot : E → σ) (wrong : E → Prop)
    [DecidablePred wrong] (m : σ → ℕ)
    (hper : ∀ r, ((Finset.univ.filter fun e => wrong e ∧ slot e = r).card : ℝ) ≤
      (m r : ℝ) / (t : ℝ))
    (hsum : (∑ r, m r) ≤ Fintype.card E) :
    ((Finset.univ.filter wrong).card : ℝ) ≤ (Fintype.card E : ℝ) / (t : ℝ) := by
  classical
  have hsplit : (Finset.univ.filter wrong).card =
      ∑ r : σ, (Finset.univ.filter fun e => wrong e ∧ slot e = r).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := slot) (t := Finset.univ)
      (s := Finset.univ.filter wrong) (fun e _ => Finset.mem_univ _)]
    exact Finset.sum_congr rfl fun r _ => by
      rw [Finset.filter_filter]
  have h1 : ((Finset.univ.filter wrong).card : ℝ) =
      ∑ r : σ, ((Finset.univ.filter fun e => wrong e ∧ slot e = r).card : ℝ) := by
    rw [hsplit]
    push_cast
    rfl
  rw [h1]
  calc ∑ r : σ, ((Finset.univ.filter fun e => wrong e ∧ slot e = r).card : ℝ)
      ≤ ∑ r : σ, (m r : ℝ) / (t : ℝ) := Finset.sum_le_sum fun r _ => hper r
    _ = ((∑ r : σ, m r : ℕ) : ℝ) / (t : ℝ) := by
        rw [← Finset.sum_div]
        push_cast
        rfl
    _ ≤ (Fintype.card E : ℝ) / (t : ℝ) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hsum) (by positivity)

/-- **Claim 3.12 as a mis-estimate count.**  The sample's only role is as a certificate: two
candidates of the family `A` that agree on it differ on at most `|α|/t` coordinates.  The estimate is
drawn from `A` and queries the truth on the sample — both are the driver's facts, kept as
hypotheses — so it mis-estimates at most `|α|/t` coordinates. -/
theorem claim312_mis {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (A : Finset (α → β)) {t : ℕ} (ht : 2 ≤ t) {truth est : α → β}
    (htruth : truth ∈ A) (hest : est ∈ A) :
    ∃ S : Finset α,
      S.card ≤ 2 * t * (Nat.ceil (Real.log ((A.card : ℝ))) + 1) ∧
      ((∀ x ∈ S, est x = truth x) →
        (Finset.univ.filter fun x => est x ≠ truth x).card ≤ Fintype.card α / t) := by
  obtain ⟨S, hS, hsep⟩ := claim312 A t (Fintype.card α / t) ht rfl
  refine ⟨S, hS, fun hagree => ?_⟩
  simpa [ne_comm] using hsep truth htruth est hest (fun x hx => (hagree x hx).symm)

/-- **The per-round `mᵢ/t` count.**  A round's edges are the fiber `{e // slot e = r}`; Claim 3.12
on that coordinate type with the round's candidate vectors yields a sample `S r`, and once the
estimate agrees with the truth there, at most `|fiber|/t` of the round's edges are mis-estimated.
This is `card_mis_le`'s `hper` — the driver's sampling, not an assumption. -/
theorem mis_fiber_hper {σ : Type*} [Fintype σ] [DecidableEq σ] {t : ℕ} (ht : 2 ≤ t)
    (slot : E → σ) (truth est : E → Pref)
    (A : ∀ r : σ, Finset ({e : E // slot e = r} → Pref))
    (htruth : ∀ r, (fun x : {e : E // slot e = r} => truth x.1) ∈ A r)
    (hest : ∀ r, (fun x : {e : E // slot e = r} => est x.1) ∈ A r) :
    ∃ S : ∀ r : σ, Finset {e : E // slot e = r},
      (∀ r, (S r).card ≤ 2 * t * (Nat.ceil (Real.log ((A r).card : ℝ)) + 1)) ∧
      (∀ (hagree : ∀ r (x : {e : E // slot e = r}), x ∈ S r → est x.1 = truth x.1) (r : σ),
        ((Finset.univ.filter fun e => est e ≠ truth e ∧ slot e = r).card : ℝ) ≤
          ((Finset.univ.filter fun e => slot e = r).card : ℝ) / (t : ℝ)) := by
  classical
  let S : ∀ r : σ, Finset {e : E // slot e = r} :=
    fun r => Classical.choose (claim312_mis (A r) ht (htruth r) (hest r))
  have hS : ∀ r, (S r).card ≤ 2 * t * (Nat.ceil (Real.log ((A r).card : ℝ)) + 1) ∧
      ((∀ x ∈ S r, est x.1 = truth x.1) →
        (Finset.univ.filter fun (x : {e : E // slot e = r}) => est x.1 ≠ truth x.1).card ≤
          Fintype.card {e : E // slot e = r} / t) :=
    fun r => Classical.choose_spec (claim312_mis (A r) ht (htruth r) (hest r))
  refine ⟨S, fun r => (hS r).1, fun hagree r => ?_⟩
  have h := (hS r).2 (fun x hx => hagree r x hx)
  have h' : ((Finset.univ.filter fun x : {e : E // slot e = r} => est x.1 ≠ truth x.1).card : ℝ) ≤
      (Fintype.card {e : E // slot e = r} : ℝ) / (t : ℝ) :=
    le_trans (by exact_mod_cast h) Nat.cast_div_le
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
  rw [hbij] at h'
  have hcard : (Fintype.card {e : E // slot e = r} : ℝ) =
      ((Finset.univ.filter fun e => slot e = r).card : ℝ) := by
    rw [Fintype.card_subtype (p := fun e : E => slot e = r)]
  rw [hcard] at h'
  exact h'

/-- **`card_mis_le`'s `hper` and `hsum`, both from the sampling.**  With the per-round samples of
`mis_fiber_hper` and the fiberwise identity `Σ_r |fiber r| = |E|`, the number of mis-estimated edges
is at most `|E|/t` — the `err2 ≤ m/t` half of §3.5's error budget.  The only process inputs are the
driver's facts: the truth and the estimate are candidates (`htruth`, `hest`) and they agree on the
queried samples (`hagree`). -/
theorem card_mis_le_of_claim312 {σ : Type*} [Fintype σ] [DecidableEq σ] {t : ℕ} (ht : 2 ≤ t)
    (slot : E → σ) (truth est : E → Pref)
    (A : ∀ r : σ, Finset ({e : E // slot e = r} → Pref))
    (htruth : ∀ r, (fun x : {e : E // slot e = r} => truth x.1) ∈ A r)
    (hest : ∀ r, (fun x : {e : E // slot e = r} => est x.1) ∈ A r) :
    ∃ S : ∀ r : σ, Finset {e : E // slot e = r},
      (∀ r, (S r).card ≤ 2 * t * (Nat.ceil (Real.log ((A r).card : ℝ)) + 1)) ∧
      (∀ (hagree : ∀ r (x : {e : E // slot e = r}), x ∈ S r → est x.1 = truth x.1),
        ((Finset.univ.filter fun e => est e ≠ truth e).card : ℝ) ≤
          (Fintype.card E : ℝ) / (t : ℝ)) := by
  classical
  obtain ⟨S, hScard, hcount⟩ := mis_fiber_hper ht slot truth est A htruth hest
  refine ⟨S, hScard, fun hagree => ?_⟩
  refine card_mis_le slot (fun e => est e ≠ truth e)
    (fun r => (Finset.univ.filter fun e => slot e = r).card) ?_ ?_
  · intro r
    exact hcount hagree r
  · rw [← Finset.card_univ,
      Finset.card_eq_sum_card_fiberwise (f := slot) (s := (Finset.univ : Finset E))
        (t := (Finset.univ : Finset σ)) (fun e _ => Finset.mem_univ _)]

end DLMST