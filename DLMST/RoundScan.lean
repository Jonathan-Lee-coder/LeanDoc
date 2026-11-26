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
set_option linter.unusedVariables false

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

/-! ## The scan keeps something -/

/-- A relation only joins distinct vertices by way of at least one edge. -/
theorem conn_nonempty {F : Finset E} {u v : V} (h : Conn G F u v) (hne : u ≠ v) :
    F.Nonempty := by
  obtain ⟨es, p, hmem⟩ := path_of_conn h
  cases p with
  | nil x => exact absurd rfl hne
  | fwd e _ _ _ => exact ⟨e, hmem e (List.mem_cons_self ..)⟩
  | bwd e _ _ _ => exact ⟨e, hmem e (List.mem_cons_self ..)⟩

/-- **A reachable non-loop edge forces a nonempty accumulator.**  An edge some batch reaches is
either kept or rejected; rejection means its ends were already joined, and joining two distinct
vertices takes at least one accepted edge.  Taking the last batch of the schedule, the scan's final
forest is nonempty. -/
theorem preF_nonempty_of_mem {t : ℕ} {sc : ℕ → List E} {k : ℕ} {e : E} (hk : k < t ^ 2)
    (he : e ∈ sc k) (hne : G.src e ≠ G.dst e) : (preF (G := G) sc (t ^ 2)).Nonempty := by
  by_cases hkeep : e ∈ preF (G := G) sc (k + 1)
  · exact ⟨e, preF_mono sc (by omega) hkeep⟩
  · have hkeep' : e ∉ K G (sc k) (preF (G := G) sc k) := by rwa [preF_succ] at hkeep
    have hc := mem_or_conn_of_mem (G := G) (sc k) (preF (G := G) sc k) e he
    rcases hc with hin | hconn
    · exact absurd hin hkeep'
    · have hn : (preF (G := G) sc (k + 1)).Nonempty := conn_nonempty hconn hne
      obtain ⟨f, hf⟩ := hn
      exact ⟨f, preF_mono sc (by omega) hf⟩

/-! ## The round data, from a scan and a classification -/

namespace CallOut

namespace RoundData

/-- **A scan plus a classification is round data.**  The round pieces are the accumulators
`preF sc (r+1)`; the child `(r, i)` receives the edges of `E₀` that `cls` assigns to it.  Then

* the pieces are inside `E₀` and their union is a forest (`preF_subset_of_scan`, `biUnion_preF`,
  `isForest_preF`) — §3.1's acceptance rule, not an extra assumption;
* the children's inputs are pairwise disjoint by construction, and every edge the scan does not keep
  is either supported by the returned forest (so it may be discarded) or classified (`hcls`), so the
  four-way `hcover` holds.

What remains as hypotheses is the numeric content: the forest's portal count, the portal budget, and
that `cls` is total on the rejected edges the forest does not support.

**The fourth bucket.**  A rejected edge that the scan forest *supports* need not be dispatched: it
becomes part of the call's `drop` bucket (`CallOut.ofClass` derives `drop` from `cls = none`), which is
the paper's "we may therefore filter out (discard) every supported edge outside `F`".  Edges that are
rejected and unsupported still must be classified (`hcls`), since they are safe nowhere else. -/
noncomputable def ofScan {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ}
    {P : Finset V} {E₀ : Finset E} (sc : ℕ → List E)
    (hsub : ∀ k e, e ∈ sc k → e ∈ E₀) (P' : Finset V)
    (cls : E → Option (Fin (t ^ 2) × ι)) (hP' : P' ⊆ P)
    (hbudget : 4 * (Fintype.card (Fin (t ^ 2) × ι) * P'.card) ≤ P.card)
    (hends : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hcls : ∀ e ∈ E₀, e ∉ preF (G := G) sc (t ^ 2) →
      ¬ supported G (preF (G := G) sc (t ^ 2)) e → ∃ p : Fin (t ^ 2) × ι, cls e = some p) :
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
  hFcard := by
    rw [biUnion_preF]
    exact card_le_card_of_isForest_of_ends (isForest_preF sc (t ^ 2))
      (fun e he => hends e (preF_subset_of_scan hsub (t ^ 2) he))
  hP' := hP'
  hbudget := hbudget
  hcover := by
    intro e he
    rw [biUnion_preF]
    by_cases hF : e ∈ preF (G := G) sc (t ^ 2)
    · exact Or.inl hF
    · by_cases hS : supported G (preF (G := G) sc (t ^ 2)) e
      · exact Or.inr (Or.inr (Or.inl hS))
      · obtain ⟨p, hp⟩ := hcls e he hF hS
        obtain ⟨a, b⟩ := p
        refine Or.inr (Or.inr (Or.inr ⟨(a, b), ?_⟩))
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

/-! ## A procedure's data, as a strategy -/

namespace Strategy

/-- The round data of one instance, built from the procedure's three data (batches, classification,
shared portal set).  Isolated as a def so that its fields can be named in proofs. -/
noncomputable def roundData {t : ℕ}
    (sc : Finset V → Finset E → ℕ → List E)
    (hsub : ∀ (P : Finset V) (E₀ : Finset E) (k : ℕ) (e : E), e ∈ sc P E₀ k → e ∈ E₀)
    (Pp : Finset V → Finset E → Finset V)
    (cls : Finset V → Finset E → E → Option (Fin (t ^ 2)))
    (hP' : ∀ (P : Finset V) (E₀ : Finset E), Pp P E₀ ⊆ P)
    (hbudget : ∀ (P : Finset V) (E₀ : Finset E),
      4 * (Fintype.card (Fin (t ^ 2)) * (Pp P E₀).card) ≤ P.card)
    (hends : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hcls : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ →
      e ∉ preF (G := G) (sc P E₀) (t ^ 2) →
      ¬ supported G (preF (G := G) (sc P E₀) (t ^ 2)) e → ∃ p : Fin (t ^ 2), cls P E₀ e = some p)
    (P : Finset V) (E₀ : Finset E) : CallOut.RoundData G P E₀ Unit t :=
  CallOut.RoundData.ofScan (G := G) (sc P E₀) (hsub P E₀) (Pp P E₀)
    (fun e => (cls P E₀ e).map (fun r => (r, ())))
    (hP' P E₀) (by simpa using hbudget P E₀) (hends P E₀) (by
      intro e he hne hns
      obtain ⟨p, hp⟩ := hcls P E₀ e he hne hns
      exact ⟨(p, ()), by simp [hp]⟩)

theorem roundData_F {t : ℕ}
    (sc : Finset V → Finset E → ℕ → List E)
    (hsub : ∀ (P : Finset V) (E₀ : Finset E) (k : ℕ) (e : E), e ∈ sc P E₀ k → e ∈ E₀)
    (Pp : Finset V → Finset E → Finset V)
    (cls : Finset V → Finset E → E → Option (Fin (t ^ 2)))
    (hP' : ∀ (P : Finset V) (E₀ : Finset E), Pp P E₀ ⊆ P)
    (hbudget : ∀ (P : Finset V) (E₀ : Finset E),
      4 * (Fintype.card (Fin (t ^ 2)) * (Pp P E₀).card) ≤ P.card)
    (hends : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hcls : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ →
      e ∉ preF (G := G) (sc P E₀) (t ^ 2) →
      ¬ supported G (preF (G := G) (sc P E₀) (t ^ 2)) e → ∃ p : Fin (t ^ 2), cls P E₀ e = some p)
    (P : Finset V) (E₀ : Finset E) :
    (roundData sc hsub Pp cls hP' hbudget hends hcls P E₀).F
      = preF (G := G) (sc P E₀) (t ^ 2) := by
  show Finset.univ.biUnion
      (fun r : Fin (t ^ 2) => preF (G := G) (sc P E₀) ((r : ℕ) + 1))
      = preF (G := G) (sc P E₀) (t ^ 2)
  exact biUnion_preF (sc P E₀) t

/-- **Every child input lies in its round's batch.**  A classification that only ever sends an edge to a
round that scanned it (`hcls_mem`, which the batch-induced `clsOf` satisfies by `clsOf_eq_some`) has
`inp r i ⊆ (sc r).toFinset`.  This is the §3.6 containment `inp' ⊆ Rej ∪ ⋃roundIn ∪ ⋃blkIn` with the
rejection and block terms *empty*: the batches alone already cover every dispatched edge. -/
theorem roundData_inp_subset {t : ℕ}
    (sc : Finset V → Finset E → ℕ → List E)
    (hsub : ∀ (P : Finset V) (E₀ : Finset E) (k : ℕ) (e : E), e ∈ sc P E₀ k → e ∈ E₀)
    (Pp : Finset V → Finset E → Finset V)
    (cls : Finset V → Finset E → E → Option (Fin (t ^ 2)))
    (hP' : ∀ (P : Finset V) (E₀ : Finset E), Pp P E₀ ⊆ P)
    (hbudget : ∀ (P : Finset V) (E₀ : Finset E),
      4 * (Fintype.card (Fin (t ^ 2)) * (Pp P E₀).card) ≤ P.card)
    (hends : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hcls : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ →
      e ∉ preF (G := G) (sc P E₀) (t ^ 2) →
      ¬ supported G (preF (G := G) (sc P E₀) (t ^ 2)) e → ∃ p : Fin (t ^ 2), cls P E₀ e = some p)
    (hcls_mem : ∀ (P : Finset V) (E₀ : Finset E) (e : E) (r : Fin (t ^ 2)),
      cls P E₀ e = some r → e ∈ sc P E₀ (r : ℕ))
    (P : Finset V) (E₀ : Finset E) (p : Fin (t ^ 2) × Unit) :
    (roundData sc hsub Pp cls hP' hbudget hends hcls P E₀).inp p.1 p.2 ⊆
      (sc P E₀ (p.1 : ℕ)).toFinset := by
  intro e he
  have he' : e ∈ E₀.filter (fun e => (cls P E₀ e).map (fun r => (r, ())) = some (p.1, p.2)) := he
  obtain ⟨-, hmap⟩ := Finset.mem_filter.mp he'
  cases hr : cls P E₀ e with
  | none => simp [hr] at hmap
  | some r =>
    have hp : ((r, ()) : Fin (t ^ 2) × Unit) = (p.1, p.2) := by simpa [hr] using hmap
    have hr' : r = p.1 := (Prod.ext_iff.mp hp).1
    rw [hr'] at hr
    exact List.mem_toFinset.mpr (hcls_mem P E₀ e p.1 hr)

/-- **The second count, from the batches.**  The call's total child input is at most the total size of
the round batches: each child input is a fibre of the classification, each fibre lies in its round's
batch (`roundData_inp_subset`), and the fibre cards over one round sum to at most the batch card.  So
§3.6's `Σᵢ|Eᵢ| ≤ |Rej| + 2t²(n−1) + t(n−1+r²n)` follows from the batches alone, with the per-round
`2(n−1)` / per-block terms available for whatever batch bound the caller has. -/
theorem sum_kidE_le_batches {t : ℕ}
    (sc : Finset V → Finset E → ℕ → List E)
    (hsub : ∀ (P : Finset V) (E₀ : Finset E) (k : ℕ) (e : E), e ∈ sc P E₀ k → e ∈ E₀)
    (Pp : Finset V → Finset E → Finset V)
    (cls : Finset V → Finset E → E → Option (Fin (t ^ 2)))
    (hP' : ∀ (P : Finset V) (E₀ : Finset E), Pp P E₀ ⊆ P)
    (hbudget : ∀ (P : Finset V) (E₀ : Finset E),
      4 * (Fintype.card (Fin (t ^ 2)) * (Pp P E₀).card) ≤ P.card)
    (hends : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hcls : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ →
      e ∉ preF (G := G) (sc P E₀) (t ^ 2) →
      ¬ supported G (preF (G := G) (sc P E₀) (t ^ 2)) e → ∃ p : Fin (t ^ 2), cls P E₀ e = some p)
    (hcls_mem : ∀ (P : Finset V) (E₀ : Finset E) (e : E) (r : Fin (t ^ 2)),
      cls P E₀ e = some r → e ∈ sc P E₀ (r : ℕ))
    (P : Finset V) (E₀ : Finset E) :
    (∑ p : Fin (t ^ 2) × Unit,
        ((roundData sc hsub Pp cls hP' hbudget hends hcls P E₀).toCall.kidE p).card) ≤
      ∑ r : Fin (t ^ 2), (sc P E₀ (r : ℕ)).toFinset.card := by
  classical
  let D := roundData sc hsub Pp cls hP' hbudget hends hcls P E₀
  refine le_trans (Finset.sum_le_sum fun p _ =>
    Finset.card_le_card (D.kidE_subset_input p)) ?_
  have h1 : (∑ p : Fin (t ^ 2) × Unit, (D.inp' p).card) =
      ∑ r, ∑ i : Unit, (D.inp r i).card :=
    Fintype.sum_prod_type (f := fun p : Fin (t ^ 2) × Unit => (D.inp' p).card)
  rw [h1]
  refine Finset.sum_le_sum fun r _ => ?_
  have h : ∀ i : Unit, (D.inp r i).card ≤ (sc P E₀ (r : ℕ)).toFinset.card :=
    fun _ => Finset.card_le_card (roundData_inp_subset sc hsub Pp cls hP' hbudget hends hcls
      hcls_mem P E₀ (r, ()))
  simpa using h ()

/-- **The classification the batches induce.**  An edge kept by the scan is `none`; any other edge
is sent to one round that scanned it (`Classical.choose` of the covering round).  This is the
paper's dispatch rule read at the level of the batch lists alone — no classification has to be
supplied. -/
noncomputable def clsOf (sc : ℕ → List E) (t : ℕ) : E → Option (Fin (t ^ 2)) :=
  fun e => if h : ∃ k, k < t ^ 2 ∧ e ∈ sc k then some ⟨h.choose, h.choose_spec.1⟩ else none

/-- **`clsOf` dispatches into the batches**: an edge sent to round `k` was scanned in round `k`.  This
is what turns the §3.6 containment `inp' ⊆ Rej ∪ ⋃roundIn ∪ ⋃blkIn` into a theorem for the
batch-induced classification (`roundData_inp_subset`). -/
theorem clsOf_eq_some {sc : ℕ → List E} {t : ℕ} {e : E} {k : Fin (t ^ 2)}
    (h : clsOf sc t e = some k) : e ∈ sc (k : ℕ) := by
  unfold clsOf at h
  by_cases hex : ∃ k, k < t ^ 2 ∧ e ∈ sc k
  · rw [dite_eq_left hex] at h
    have hk : (⟨hex.choose, hex.choose_spec.1⟩ : Fin (t ^ 2)) = k := Option.some.inj h
    rw [← hk]
    exact hex.choose_spec.2
  · rw [dite_eq_right hex] at h
    exact absurd h (by simp)

/-- **A procedure's three data are a well-formed strategy.**  Per instance `(P, E₀)` a procedure
supplies only: a sequence of batches `sc` inside `E₀` (the rounds' scan lists), a classification
`cls` of the edges the scan does not keep into the round-child that receives them, and a shared
portal set `Pp`.  Everything else `RoundData` needs is derived: forestness and the accumulator by
`RoundScan.ofScan`, the forest bound `|F| ≤ |P|` by `ForestCard.card_le_card_of_isForest_of_ends`
from `hends` (the instance's edges live on its portal set), and the portal budget from `hbudget`
(which `portals_shrink` supplies from the per-round counts).  This is the last object §3.6 asks a
recursive procedure to produce. -/
noncomputable def ofScan {t : ℕ}
    (sc : Finset V → Finset E → ℕ → List E)
    (hsub : ∀ (P : Finset V) (E₀ : Finset E) (k : ℕ) (e : E), e ∈ sc P E₀ k → e ∈ E₀)
    (Pp : Finset V → Finset E → Finset V)
    (cls : Finset V → Finset E → E → Option (Fin (t ^ 2)))
    (hP' : ∀ (P : Finset V) (E₀ : Finset E), Pp P E₀ ⊆ P)
    (hbudget : ∀ (P : Finset V) (E₀ : Finset E),
      4 * (Fintype.card (Fin (t ^ 2)) * (Pp P E₀).card) ≤ P.card)
    (hends : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hcls : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ →
      e ∉ preF (G := G) (sc P E₀) (t ^ 2) →
      ¬ supported G (preF (G := G) (sc P E₀) (t ^ 2)) e → ∃ p : Fin (t ^ 2), cls P E₀ e = some p) :
    Strategy G :=
  fun (P : Finset V) (E₀ : Finset E) =>
    ⟨Fintype.card (Fin (t ^ 2) × Unit),
      CallOut.reindex (Fintype.equivFin (Fin (t ^ 2) × Unit))
        (roundData sc hsub Pp cls hP' hbudget hends hcls P E₀).toCall⟩

/-- **The strategy answers about the instance it was asked about**: its instance fields are
`RoundData`'s parameters, so `P` and `E₀` are the ones supplied. -/
theorem ofScan_wf {t : ℕ}
    (sc : Finset V → Finset E → ℕ → List E)
    (hsub : ∀ (P : Finset V) (E₀ : Finset E) (k : ℕ) (e : E), e ∈ sc P E₀ k → e ∈ E₀)
    (Pp : Finset V → Finset E → Finset V)
    (cls : Finset V → Finset E → E → Option (Fin (t ^ 2)))
    (hP' : ∀ (P : Finset V) (E₀ : Finset E), Pp P E₀ ⊆ P)
    (hbudget : ∀ (P : Finset V) (E₀ : Finset E),
      4 * (Fintype.card (Fin (t ^ 2)) * (Pp P E₀).card) ≤ P.card)
    (hends : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hcls : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ →
      e ∉ preF (G := G) (sc P E₀) (t ^ 2) →
      ¬ supported G (preF (G := G) (sc P E₀) (t ^ 2)) e → ∃ p : Fin (t ^ 2), cls P E₀ e = some p) :
    Wf (ofScan sc hsub Pp cls hP' hbudget hends hcls) :=
  fun _ _ => ⟨rfl, rfl⟩

/-- **The strategy's vertex-to-edge ratio.**  If every portal of every instance is an end of one of
the instance's edges (no isolated vertices — the paper's standing assumption, cf.
`Section36.card_le_two_mul_of_no_isolated`), then `|P| ≤ 2|E₀|` for every instance of the scan's
strategy, which is the `hnm` premise of the display. -/
theorem ofScan_hnm {t : ℕ}
    (sc : Finset V → Finset E → ℕ → List E)
    (hsub : ∀ (P : Finset V) (E₀ : Finset E) (k : ℕ) (e : E), e ∈ sc P E₀ k → e ∈ E₀)
    (Pp : Finset V → Finset E → Finset V)
    (cls : Finset V → Finset E → E → Option (Fin (t ^ 2)))
    (hP' : ∀ (P : Finset V) (E₀ : Finset E), Pp P E₀ ⊆ P)
    (hbudget : ∀ (P : Finset V) (E₀ : Finset E),
      4 * (Fintype.card (Fin (t ^ 2)) * (Pp P E₀).card) ≤ P.card)
    (hends : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hcls : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ →
      e ∉ preF (G := G) (sc P E₀) (t ^ 2) →
      ¬ supported G (preF (G := G) (sc P E₀) (t ^ 2)) e → ∃ p : Fin (t ^ 2), cls P E₀ e = some p)
    (huse : ∀ (P : Finset V) (E₀ : Finset E) (v : V), v ∈ P →
      ∃ e ∈ E₀, G.src e = v ∨ G.dst e = v) :
    ∀ (P : Finset V) (E₀ : Finset E),
      (((ofScan sc hsub Pp cls hP' hbudget hends hcls P E₀).2.P.card : ℕ) : ℝ) ≤
        2 * (((ofScan sc hsub Pp cls hP' hbudget hends hcls P E₀).2.E₀.card : ℕ) : ℝ) := by
  intro P E₀
  exact_mod_cast card_le_two_mul_card_of_subset_ends (G := G) (huse P E₀)

/-- **The scan's procedure terminates.**  If every edge of the instance appears in some batch and no
edge is a loop, the scan keeps at least one edge (`preF_nonempty_of_mem`: a non-loop edge is either
kept, or rejected because its ends are already joined by a nonempty forest).  A kept edge is in `F`,
which no child receives — so every child's input is strictly smaller.  (For instances with loops the
scan alone does not terminate; §3.6 treats loops by a separate class call.) -/
theorem ofScan_strict {t : ℕ}
    (sc : Finset V → Finset E → ℕ → List E)
    (hsub : ∀ (P : Finset V) (E₀ : Finset E) (k : ℕ) (e : E), e ∈ sc P E₀ k → e ∈ E₀)
    (Pp : Finset V → Finset E → Finset V)
    (cls : Finset V → Finset E → E → Option (Fin (t ^ 2)))
    (hP' : ∀ (P : Finset V) (E₀ : Finset E), Pp P E₀ ⊆ P)
    (hbudget : ∀ (P : Finset V) (E₀ : Finset E),
      4 * (Fintype.card (Fin (t ^ 2)) * (Pp P E₀).card) ≤ P.card)
    (hends : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hcls : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ →
      e ∉ preF (G := G) (sc P E₀) (t ^ 2) →
      ¬ supported G (preF (G := G) (sc P E₀) (t ^ 2)) e → ∃ p : Fin (t ^ 2), cls P E₀ e = some p)
    (hcover : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ →
      ∃ k, k < t ^ 2 ∧ e ∈ sc P E₀ k)
    (hnoloop : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ≠ G.dst e) :
    Strict (ofScan sc hsub Pp cls hP' hbudget hends hcls) := by
  intro P E₀ hne i
  obtain ⟨e₀, he₀⟩ := hne
  obtain ⟨k, hk, hmem⟩ := hcover P E₀ e₀ he₀
  obtain ⟨f, hf⟩ := preF_nonempty_of_mem (G := G) (sc := sc P E₀) hk hmem
    (hnoloop P E₀ e₀ he₀)
  have hfF : f ∈ (roundData sc hsub Pp cls hP' hbudget hends hcls P E₀).F := by
    rw [roundData_F]; simpa using hf
  exact (roundData sc hsub Pp cls hP' hbudget hends hcls P E₀).toCall_kidE_card_lt hfF
    ((Fintype.equivFin (Fin (t ^ 2) × Unit)).symm i)

/-- **The procedure from its batches alone.**  If every edge of the instance appears in some batch,
the classification is *constructed* (`clsOf`), so a procedure needs only batches, portal sets and the
endpoint geometry — `hcls` is a theorem, not a hypothesis.  (The batch classifier still sends every
rejected edge to its batch's child, so this particular strategy has an empty `drop` bucket; the model
itself has the bucket — `CallOut.drop`, exercised by `CallOut.ofClass` and counted in
`CallFromRounds.partition` — so a strategy that filters supported edges is expressible.) -/
noncomputable def ofBatches {t : ℕ}
    (sc : Finset V → Finset E → ℕ → List E)
    (hsub : ∀ (P : Finset V) (E₀ : Finset E) (k : ℕ) (e : E), e ∈ sc P E₀ k → e ∈ E₀)
    (Pp : Finset V → Finset E → Finset V)
    (hP' : ∀ (P : Finset V) (E₀ : Finset E), Pp P E₀ ⊆ P)
    (hbudget : ∀ (P : Finset V) (E₀ : Finset E),
      4 * (Fintype.card (Fin (t ^ 2)) * (Pp P E₀).card) ≤ P.card)
    (hends : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hcover : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ →
      ∃ k, k < t ^ 2 ∧ e ∈ sc P E₀ k) :
    Strategy G :=
  ofScan sc hsub Pp (fun P E₀ e => clsOf (sc P E₀) t e) hP' hbudget hends (by
    intro P E₀ e he _ _
    obtain ⟨k, hk, hmem⟩ := hcover P E₀ e he
    have hex : ∃ k, k < t ^ 2 ∧ e ∈ sc P E₀ k := ⟨k, hk, hmem⟩
    exact ⟨⟨hex.choose, hex.choose_spec.1⟩, dite_eq_left hex⟩)

/-- The batches-only strategy is well-formed. -/
theorem ofBatches_wf {t : ℕ}
    (sc : Finset V → Finset E → ℕ → List E)
    (hsub : ∀ (P : Finset V) (E₀ : Finset E) (k : ℕ) (e : E), e ∈ sc P E₀ k → e ∈ E₀)
    (Pp : Finset V → Finset E → Finset V)
    (hP' : ∀ (P : Finset V) (E₀ : Finset E), Pp P E₀ ⊆ P)
    (hbudget : ∀ (P : Finset V) (E₀ : Finset E),
      4 * (Fintype.card (Fin (t ^ 2)) * (Pp P E₀).card) ≤ P.card)
    (hends : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hcover : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ →
      ∃ k, k < t ^ 2 ∧ e ∈ sc P E₀ k) :
    Wf (ofBatches sc hsub Pp hP' hbudget hends hcover) :=
  ofScan_wf sc hsub Pp _ hP' hbudget hends _

/-- The batches-only strategy shrinks strictly (batches cover, no loops). -/
theorem ofBatches_strict {t : ℕ}
    (sc : Finset V → Finset E → ℕ → List E)
    (hsub : ∀ (P : Finset V) (E₀ : Finset E) (k : ℕ) (e : E), e ∈ sc P E₀ k → e ∈ E₀)
    (Pp : Finset V → Finset E → Finset V)
    (hP' : ∀ (P : Finset V) (E₀ : Finset E), Pp P E₀ ⊆ P)
    (hbudget : ∀ (P : Finset V) (E₀ : Finset E),
      4 * (Fintype.card (Fin (t ^ 2)) * (Pp P E₀).card) ≤ P.card)
    (hends : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hcover : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ →
      ∃ k, k < t ^ 2 ∧ e ∈ sc P E₀ k)
    (hnoloop : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ≠ G.dst e) :
    Strict (ofBatches sc hsub Pp hP' hbudget hends hcover) :=
  ofScan_strict sc hsub Pp _ hP' hbudget hends _ hcover hnoloop

/-- The batches-only strategy satisfies the display's vertex-to-edge premise. -/
theorem ofBatches_hnm {t : ℕ}
    (sc : Finset V → Finset E → ℕ → List E)
    (hsub : ∀ (P : Finset V) (E₀ : Finset E) (k : ℕ) (e : E), e ∈ sc P E₀ k → e ∈ E₀)
    (Pp : Finset V → Finset E → Finset V)
    (hP' : ∀ (P : Finset V) (E₀ : Finset E), Pp P E₀ ⊆ P)
    (hbudget : ∀ (P : Finset V) (E₀ : Finset E),
      4 * (Fintype.card (Fin (t ^ 2)) * (Pp P E₀).card) ≤ P.card)
    (hends : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hcover : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ →
      ∃ k, k < t ^ 2 ∧ e ∈ sc P E₀ k)
    (huse : ∀ (P : Finset V) (E₀ : Finset E) (v : V), v ∈ P →
      ∃ e ∈ E₀, G.src e = v ∨ G.dst e = v) :
    ∀ (P : Finset V) (E₀ : Finset E),
      (((ofBatches sc hsub Pp hP' hbudget hends hcover P E₀).2.P.card : ℕ) : ℝ) ≤
        2 * (((ofBatches sc hsub Pp hP' hbudget hends hcover P E₀).2.E₀.card : ℕ) : ℝ) :=
  ofScan_hnm sc hsub Pp _ hP' hbudget hends _ huse

end Strategy

end DLMST
