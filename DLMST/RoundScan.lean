import DLMST.CallFromRounds
import DLMST.Greedy

/-!
# Rounds that accept by connectivity: the scan, and the round data it produces

`CallFromRounds.RoundData` asks for a per-round family of forest pieces whose union is a forest,
together with a classification of the instance's edges and the portal budget.  The paper's §3.1
acceptance rule is *local*: round `r` scans its batch and keeps an edge exactly when its two ends are
not yet joined by the edges kept so far.  This file shows that the three structural fields of that
rule — the pieces are inside `E₀`, their union is a forest, and the union is exactly the accumulator —
are consequences of the rule, so `RoundData.hforest`/`hsubF`/`hdisj`/`hcover` need not be taken as
data.

Two layers:

* `isForest_K` — Kruskal's scan is forestness-preserving for **any** edge list, sorted or not
  (`Greedy.kruskal_correct` needs the order only for *minimality*).  The scan's forest is therefore
  the acceptance rule's own product;
* `preF sc k` — the accumulator after the first `k` rounds, each round scanning `sc k`.  It grows
  (`preF_mono`), stays inside `E₀` (`preF_subset_of_scan`), is a forest at every stage
  (`isForest_preF`), and the family of round pieces `r ↦ preF sc (r+1)` has union `preF sc t²`
  (`biUnion_preF`) because the pieces are nested.

`RoundData.ofScan` then packages a scan plus a *classification* `cls : E → Option (round × child)` of
the edges the forest does not account for.  Children's inputs are the fibres of `cls` inside `E₀`, so
they are pairwise disjoint by construction (`Finset.disjoint_left` on `Option.some.inj`) and every
unclassified edge is kept or retained.  What is left as hypotheses is exactly the numeric content:
the portal count `|F| ≤ |P|`, the portal budget, and totality of `cls` on the edges that are neither
kept nor retained.
-/

namespace DLMST
open Classical
set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] {G : WGraph V E}
  [LinearOrder E]

/-! ## Kruskal's scan preserves forestness -/

/-- **A Kruskal scan of any edge list keeps the accumulator a forest.**  Each step either leaves the
accumulator alone or inserts an edge whose ends are not joined, and `IsForest.insert` handles the
latter.  No ordering hypothesis appears, unlike in `kruskal_correct`: sortedness is what makes the
output *minimum*, not what makes it a forest. -/
theorem isForest_K : ∀ (es : List E) {F : Finset E}, IsForest G F → IsForest G (K G es F) := by
  intro es
  induction es with
  | nil => intro F hF; rw [K_nil]; exact hF
  | cons a as ih =>
    intro F hF
    rw [K_cons]
    refine ih ?_
    rcases step_eq_or_conn G F a with ⟨hr, _⟩ | ⟨ha, hc⟩
    · rw [hr]; exact hF
    · rw [ha]; exact kruskal_step_isForest hF hc

/-- Every edge of a scan's output was either already in the accumulator or lies in the scanned
list — the scan never invents edges.  This is what keeps the accumulator inside `E₀`. -/
theorem mem_K_or : ∀ (es : List E) (F : Finset E) {e : E}, e ∈ K G es F → e ∈ F ∨ e ∈ es := by
  intro es
  induction es with
  | nil => intro F e h; exact Or.inl (by rwa [K_nil] at h)
  | cons a as ih =>
    intro F e h
    rw [K_cons] at h
    rcases ih (step G F a) h with hstep | hin
    · rcases step_eq_or_conn G F a with ⟨hr, _⟩ | ⟨ha, _⟩
      · exact Or.inl (by rwa [hr] at hstep)
      · rw [ha] at hstep
        rcases Finset.mem_insert.mp hstep with rfl | hF
        · exact Or.inr List.mem_cons_self
        · exact Or.inl hF
    · exact Or.inr (List.mem_cons_of_mem a hin)

/-! ## The rounds' accumulator -/

/-- `preF sc k`: the forest the procedure holds at the **start of round `k`** — the paper's `Fᵢ`
(Definition 1.5).  Round `0` starts empty and round `k+1` is round `k`'s scan applied to the
accumulator of round `k`. -/
noncomputable def preF (sc : ℕ → List E) : ℕ → Finset E
  | 0 => ∅
  | k + 1 => K G (sc k) (preF sc k)

theorem preF_zero (sc : ℕ → List E) : preF (G := G) sc 0 = ∅ := rfl

theorem preF_succ (sc : ℕ → List E) (k : ℕ) :
    preF (G := G) sc (k + 1) = K G (sc k) (preF (G := G) sc k) := rfl

/-- A round never loses an edge. -/
theorem preF_subset_succ (sc : ℕ → List E) (k : ℕ) :
    preF (G := G) sc k ⊆ preF (G := G) sc (k + 1) :=
  K_mono (sc k) (preF (G := G) sc k)

/-- ... so the accumulator grows with the round index. -/
theorem preF_mono (sc : ℕ → List E) {k l : ℕ} (h : k ≤ l) :
    preF (G := G) sc k ⊆ preF (G := G) sc l := by
  induction l, h using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ l _ ih => exact Finset.Subset.trans ih (preF_subset_succ sc l)

/-- Every round's accumulator is a forest. -/
theorem isForest_preF (sc : ℕ → List E) (k : ℕ) : IsForest G (preF (G := G) sc k) := by
  induction k with
  | zero => rw [preF_zero]; exact IsForest.empty
  | succ k ih => rw [preF_succ]; exact isForest_K (sc k) ih

/-- The accumulator stays inside the instance's edge set, as long as every round scans only edges of
`E₀`. -/
theorem preF_subset_of_scan {E₀ : Finset E} {sc : ℕ → List E}
    (hsub : ∀ k e, e ∈ sc k → e ∈ E₀) (k : ℕ) : preF (G := G) sc k ⊆ E₀ := by
  induction k with
  | zero => rw [preF_zero]; exact Finset.empty_subset _
  | succ k ih =>
    rw [preF_succ]
    intro e he
    rcases mem_K_or (sc k) (preF (G := G) sc k) he with hin | hes
    · exact ih hin
    · exact hsub k e hes

/-- **The round pieces are nested and their union is the final accumulator.**  Taking round `r`'s
contribution to be `preF sc (r+1)` (the forest at the *end* of round `r`), the `t²` pieces cover
`preF sc t²` — which is what lets `RoundData` read the union as one forest. -/
theorem biUnion_preF (sc : ℕ → List E) (t : ℕ) :
    (Finset.univ.biUnion (fun r : Fin (t ^ 2) => preF (G := G) sc ((r : ℕ) + 1)))
      = preF (G := G) sc (t ^ 2) := by
  rcases Nat.eq_zero_or_pos (t ^ 2) with h0 | hpos
  · rw [h0, preF_zero]
    simp
  · refine Finset.Subset.antisymm ?_ ?_
    · intro e he
      obtain ⟨r, -, hr⟩ := Finset.mem_biUnion.mp he
      exact preF_mono (sc := sc) (k := (r : ℕ) + 1) (l := t ^ 2)
        (by have := r.2; omega) hr
    · intro e he
      refine Finset.mem_biUnion.mpr ⟨⟨t ^ 2 - 1, by omega⟩, Finset.mem_univ _, ?_⟩
      rwa [Nat.sub_add_cancel (by omega : 1 ≤ t ^ 2)]

/-! ## The round data, from a scan and a classification -/

namespace CallOut

namespace RoundData

/-- **A scan plus a classification is round data.**  The round pieces are the accumulators
`preF sc (r+1)`; the child `(r, i)` receives the edges of `E₀` that `cls` assigns to it.  Then

* the pieces are inside `E₀` and their union is a forest (`preF_subset_of_scan`, `biUnion_preF`,
  `isForest_preF`) — §3.1's acceptance rule, not an extra assumption;
* the children's inputs are pairwise disjoint by construction, and every edge the scan does not keep
  is classified (`hcls`), so `hcover` holds.

What remains as hypotheses is the numeric content: the forest's portal count, the portal budget, and
that `cls` is total on the edges the scan does not keep.

**Modelling caveat.**  `hcls` says *nothing is dropped*: an edge the scan rejects is dispatched to a
child.  The paper's §3.1 procedure also discards supported edges (`F` supports them, so they are
safe), and `CallOut.hcover` has no bucket for them — the formal model reads every input edge as
kept, retained or dispatched.  A faithful instance of the paper's algorithm therefore needs either a
fourth "dropped" bucket in `CallOut` or a `cls` that sends supported edges to a child; the §3.6
display is unaffected (it bounds `|F|`, `|U|` and `Σ|Eᵢ|` separately, never via `hcover`). -/
noncomputable def ofScan {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ}
    {P : Finset V} {E₀ : Finset E} (sc : ℕ → List E)
    (hsub : ∀ k e, e ∈ sc k → e ∈ E₀) (P' : Finset V)
    (cls : E → Option (Fin (t ^ 2) × ι)) (hP' : P' ⊆ P)
    (hbudget : 4 * (Fintype.card (Fin (t ^ 2) × ι) * P'.card) ≤ P.card)
    (hFcard : (preF (G := G) sc (t ^ 2)).card ≤ P.card)
    (hcls : ∀ e ∈ E₀, e ∉ preF (G := G) sc (t ^ 2) → ∃ p : Fin (t ^ 2) × ι, cls e = some p) :
    RoundData G P E₀ ι t where
  Fr r := preF (G := G) sc ((r : ℕ) + 1)
  inp r i := E₀.filter (fun e => cls e = some (r, i))
  P' := P'
  hsubF := by
    rw [biUnion_preF]
    exact preF_subset_of_scan hsub (t ^ 2)
  hforest := by
    rw [biUnion_preF]
    exact isForest_preF sc (t ^ 2)
  hFcard := by rw [biUnion_preF]; exact hFcard
  hP' := hP'
  hbudget := hbudget
  hcover := by
    intro e he
    rw [biUnion_preF]
    by_cases hF : e ∈ preF (G := G) sc (t ^ 2)
    · exact Or.inl hF
    · obtain ⟨p, hp⟩ := hcls e he hF
      obtain ⟨a, b⟩ := p
      refine Or.inr (Or.inr ⟨(a, b), ?_⟩)
      simp only [Finset.mem_filter]
      exact ⟨he, hp⟩
  hdisj := by
    intro p _ q _ hpq
    refine Finset.disjoint_left.mpr fun e hep heq => ?_
    simp only [Finset.mem_filter] at hep heq
    have h : ((p.1, p.2) : Fin (t ^ 2) × ι) = (q.1, q.2) :=
      Option.some.inj (hep.2.symm.trans heq.2)
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
    exact hpq (Prod.ext h1 h2)

end RoundData

end CallOut

end DLMST