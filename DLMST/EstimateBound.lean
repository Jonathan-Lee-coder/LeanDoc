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

end DLMST