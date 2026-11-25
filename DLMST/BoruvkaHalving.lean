import DLMST.Boruvka
import DLMST.ForestCard
import DLMST.Section36

/-!
# §4: Borůvka phases halve the number of components

The paper's §4 spends `k` Borůvka phases before recursing, so that the recursive instances have
`n' ≤ n/2^k` vertices — this is the `hn` slot of `CertificateBuild.certificate_of_display`.  The
present file checks the purely combinatorial half: **one phase halves the component count**, hence
`k` phases divide it by `2^k`.

The argument uses nothing that `Boruvka.lean` has not already established.

* `F.card + compCount G F = |V|` (`ForestCard.card_add_compCount`) turns "components halve" into the
  edge count of the phase: since a phase edge is never in `F` (`BorPhase.not_mem`), the new forest
  `F ∪ A` has `compCount G (F ∪ A) = compCount G F - |A|`, so `c' ≤ c/2` is exactly `|A| ≥ c/2`.
* `|A| ≥ c/2` is the classical Borůvka count: each component *picks* an outgoing edge, and each
  picked edge is picked by at most two components (the two sides of the edge).  Counted as a union
  of two-element sets of components: `univ.image (comp G F) ⊆ A.biUnion (·.src/dst components)`,
  whose size is at most `2|A|`.

Note what is *not* used: the multi-cut blue rule.  The halving bound is a statement about the
component count and needs only `BorPhase`'s two fields (openness and the choice rule), so the §4
vertex halving is independent of extendability — which `Boruvka.boruvka_round` proves separately.
Activity at every phase is likewise discharged from connectivity of `G` in `BoruvkaPhase.lean`.
The cost of running the phases is `Halving.lean`'s object; the executable run itself (with the
`Fin (k+1)`-indexed data and the well-founded child recursion) is still where the driver's
remaining work sits.
-/

open Classical

namespace DLMST

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

/-- **One Borůvka phase halves the component count**, provided every component of the current forest
actually picks an outgoing edge (`hcover` — true for the phase that aggregates all components'
`wOrd`-lightest out-edges).  Only `BorPhase`'s forestness and the bookkeeping identity are used. -/
theorem compCount_halves {F A : Finset E} (hF : IsForest G F) (hph : BorPhase G F A)
    (hcover : ∀ C ∈ Finset.univ.image (comp G F),
      ∃ e ∈ A, comp G F (G.src e) = C ∨ comp G F (G.dst e) = C) :
    2 * compCount G (F ∪ A) ≤ compCount G F := by
  classical
  have hFA : IsForest G (F ∪ A) := boruvka_forest hF hph
  have hdisj : Disjoint F A :=
    Finset.disjoint_left.mpr (fun e heF heA => hph.not_mem heA heF)
  -- `|A| ≥ c/2`: each component is one of the two sides of a phase edge.
  have hc : compCount G F ≤ 2 * A.card := by
    set S : Finset (Finset V) := Finset.univ.image (comp G F) with hS
    set T : Finset (Finset V) :=
      A.biUnion (fun e => ({comp G F (G.src e), comp G F (G.dst e)} : Finset (Finset V)))
      with hT
    have hsub : S ⊆ T := by
      intro C hC
      obtain ⟨e, he, hCe⟩ := hcover C hC
      refine Finset.mem_biUnion.mpr ⟨e, he, ?_⟩
      rcases hCe with h | h <;> rw [← h]
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hTle : T.card ≤
        Finset.sum A (fun e =>
          ({comp G F (G.src e), comp G F (G.dst e)} : Finset (Finset V)).card) :=
      Finset.card_biUnion_le
    have htwo : ∀ e ∈ A,
        ({comp G F (G.src e), comp G F (G.dst e)} : Finset (Finset V)).card ≤ 2 :=
      fun e _ => Finset.card_le_two
    calc compCount G F = S.card := by simp [compCount, hS]
      _ ≤ T.card := Finset.card_le_card hsub
      _ ≤ Finset.sum A (fun _ => 2) := le_trans hTle (Finset.sum_le_sum htwo)
      _ = 2 * A.card := by
          rw [Finset.sum_const_nat (fun _ _ => rfl), Nat.mul_comm]
  have h1 := card_add_compCount (G := G) hF
  have h2 := card_add_compCount (G := G) hFA
  have h3 : (F ∪ A).card = F.card + A.card := Finset.card_union_of_disjoint hdisj
  omega

/-- Abstract doubling: a sequence that at least halves (`2·c(i+1) ≤ c(i)`) is at most `2^{-k}`
of its start.  Kept separate so that no induction ever runs over the graph-theoretic context. -/
theorem pow_two_mul_le_of_le (c : ℕ → ℕ) (K : ℕ) (h : ∀ i, i < K → 2 * c (i + 1) ≤ c i)
    {k : ℕ} (hk : k ≤ K) : 2 ^ k * c k ≤ c 0 := by
  induction k with
  | zero => simp
  | succ n ih =>
      have hn : n < K := Nat.lt_of_succ_le hk
      calc 2 ^ (n + 1) * c (n + 1) = 2 ^ n * (2 * c (n + 1)) := by rw [Nat.pow_succ]; ring
        _ ≤ 2 ^ n * c n := Nat.mul_le_mul_left _ (h n hn)
        _ ≤ c 0 := ih (Nat.le_of_succ_le hk)

/-- **`k` phases divide the component count by `2^k`.**  `F 0` is the starting forest,
`F (i+1) = F i ∪ A i` is the forest after phase `i`, and each `A i` (`i < K`) is a covering phase
of `F i`; at any `k ≤ K` phases the component count is `2^k`-times smaller. -/
theorem compCount_pow_halves (K : ℕ) (F A : ℕ → Finset E) (hF0 : IsForest G (F 0))
    (hstep : ∀ i, F (i + 1) = F i ∪ A i)
    (hph : ∀ i, i < K → BorPhase G (F i) (A i))
    (hcover : ∀ i, i < K → ∀ C ∈ Finset.univ.image (comp G (F i)),
      ∃ e ∈ A i, comp G (F i) (G.src e) = C ∨ comp G (F i) (G.dst e) = C)
    {k : ℕ} (hk : k ≤ K) :
    2 ^ k * compCount G (F k) ≤ compCount G (F 0) := by
  classical
  have hforest : ∀ i, i ≤ K → IsForest G (F i) := by
    intro i hi
    induction i with
    | zero => exact hF0
    | succ n ih =>
        exact (hstep n).symm ▸
          boruvka_forest (ih (Nat.le_of_succ_le hi)) (hph n (Nat.lt_of_succ_le hi))
  have chain : ∀ i, i < K → 2 * compCount G (F (i + 1)) ≤ compCount G (F i) := by
    intro i hi
    rw [hstep i]
    exact compCount_halves (hforest i (Nat.le_of_lt hi)) (hph i hi) (hcover i hi)
  exact pow_two_mul_le_of_le (fun i => compCount G (F i)) K chain hk

/-- Natural-number form of the halving: from `c_k · 2^k ≤ c_0 ≤ 2m`, the `k`-th component count is
at most `2m / 2^k`. -/
theorem compCount_le_div_pow (K : ℕ) (F A : ℕ → Finset E) (m k : ℕ) (hF0 : IsForest G (F 0))
    (hstep : ∀ i, F (i + 1) = F i ∪ A i)
    (hph : ∀ i, i < K → BorPhase G (F i) (A i))
    (hcover : ∀ i, i < K → ∀ C ∈ Finset.univ.image (comp G (F i)),
      ∃ e ∈ A i, comp G (F i) (G.src e) = C ∨ comp G (F i) (G.dst e) = C)
    (hk : k ≤ K) (h0 : compCount G (F 0) ≤ 2 * m) :
    compCount G (F k) ≤ 2 * m / 2 ^ k := by
  have h1 : compCount G (F k) * 2 ^ k ≤ 2 * m := by
    rw [Nat.mul_comm]
    exact le_trans (compCount_pow_halves K F A hF0 hstep hph hcover hk) h0
  exact (Nat.le_div_iff_mul_le (pow_pos (by norm_num) k)).mpr h1

/-- Real form, in exactly the shape `CertificateBuild.certificate_of_display` consumes:
after `k ≤ K` phases, `n' ≤ 2m / 2^k`. -/
theorem compCount_le_real (K : ℕ) (F A : ℕ → Finset E) (m k : ℕ) (hF0 : IsForest G (F 0))
    (hstep : ∀ i, F (i + 1) = F i ∪ A i)
    (hph : ∀ i, i < K → BorPhase G (F i) (A i))
    (hcover : ∀ i, i < K → ∀ C ∈ Finset.univ.image (comp G (F i)),
      ∃ e ∈ A i, comp G (F i) (G.src e) = C ∨ comp G (F i) (G.dst e) = C)
    (hk : k ≤ K) (h0 : compCount G (F 0) ≤ 2 * m) :
    (compCount G (F k) : ℝ) ≤ 2 * (m : ℝ) / (2 : ℝ) ^ k := by
  have hnat := compCount_le_div_pow K F A m k hF0 hstep hph hcover hk h0
  have h1 : compCount G (F k) * 2 ^ k ≤ 2 * m :=
    (Nat.le_div_iff_mul_le (pow_pos (by norm_num) k)).mp hnat
  have hcast : (compCount G (F k) : ℝ) * (2 : ℝ) ^ k ≤ 2 * (m : ℝ) := by
    have h2 : ((compCount G (F k) * 2 ^ k : ℕ) : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h2
    linarith
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- The paper's hypothesis read off the graph: with no isolated vertex, `n ≤ 2m`
(`Section36.card_le_two_mul_of_no_isolated`), so starting from the empty forest — `|V|` components —
`k` phases leave at most `2m / 2^k` components.  This is exactly the `hn` field of
`CertificateBuild.certificate_of_display` at `k = 2j`, with `m = |E|` and the phase count discharged
by the Borůvka run rather than assumed. -/
theorem compCount_le_real_of_empty (K : ℕ) (F A : ℕ → Finset E) (k : ℕ) (hF0 : F 0 = ∅)
    (hstep : ∀ i, F (i + 1) = F i ∪ A i)
    (hph : ∀ i, i < K → BorPhase G (F i) (A i))
    (hcover : ∀ i, i < K → ∀ C ∈ Finset.univ.image (comp G (F i)),
      ∃ e ∈ A i, comp G (F i) (G.src e) = C ∨ comp G (F i) (G.dst e) = C)
    (hk : k ≤ K) (hno : ∀ v : V, 1 ≤ degV G v) :
    (compCount G (F k) : ℝ) ≤ 2 * (Fintype.card E : ℝ) / (2 : ℝ) ^ k := by
  have hforest0 : IsForest G (F 0) := by rw [hF0]; exact IsForest.empty
  have h0 : compCount G (F 0) ≤ 2 * Fintype.card E := by
    rw [hF0, compCount_empty]
    have h := card_le_two_mul_of_no_isolated (G := G) hno
    exact_mod_cast h
  exact compCount_le_real K F A (Fintype.card E) k hforest0 hstep hph hcover hk h0

end DLMST