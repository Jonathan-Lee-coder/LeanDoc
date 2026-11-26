import DLMST.CostLinear
import DLMST.LevelWork

/-!
# B2: the branching recursion of Algorithm 2, closed at the counting level

`CostLinear.lean` proves that a strategy's *own* recursion tree is linear once (i) every node's
children satisfy the display `Σ|Eᵢ| ≤ εm + C√(mn)` and (ii) the contracted vertex count obeys
`n ≤ 2m/2^{2j}`; `LevelWork.lean` proves that the paper's two per-call numeric outputs (the §3.5
estimate `|U| ≤ 10t_d²√(mn) + 4m/t_d` and the p. 24 input count) imply that display at the *root*.
The two halves had never been joined: the display-consuming theorem asked for the display at every
instance, the display-producing theorem only delivered it at one root.

This file joins them.  It is the paper's Theorem 4.1 recursion read as a *branching* recursion:
a node runs its rounds (the per-call counts), hands its children `Eᵢ` (the next nodes), and the
argument is a strong induction on `|E₀|`, not an `m`-indexed worst case.

* `kidE_le_of_display` — the three-bucket display `|F|+|U|+Σ|Eᵢ| ≤ …` implies the children-only
  display `Σ|Eᵢ| ≤ …` (drop two nonnegative terms);
* `kidE_display_of_counts` — the children-only display at **every root**, from
  `display_of_strategy_of_nat_counts` instantiated at that root (§3.5 + §3.6 counts, at the root's
  own depth, down to depth `|E₀|`);
* `child_shrink_of_counts` — the `m/2` shrink `Σ|Eᵢ| ≤ m/2` at every node, from the display and
  the post-phase vertex bound (`children_shrink`);
* **`cost_linear_of_counts`** — the branching recursion: any counting cost `T` obeying
  `T(P,E₀) ≤ Σᵢ T(Eᵢ) + c·|E₀|` is `≤ 2c·|E₀|` on **every** instance, from the per-call §3.5/§3.6
  counts at every node and the two constant conditions `ε ≤ 1/8`, `C_ε·2/2^j ≤ 3/8`;
* `exists_displayC_phase` — the second constant condition can always be met by choosing enough
  Borůvka phases (`2^j` unbounded).

What remains outside is unchanged from boundary **B2**: `T` is a *counting* measure supplied by the
caller (comparisons, queries, path-maxima), and the paper provides no RAM cost model, so
"linear time" itself is still not machine-checked.  Boundary **B4** enters only through `hU`: the
`|U|` count at each node is the output of §3.5's estimates, whose existence is the deterministic
§3.4/§3.5 layer (`History.lemma311`, `Sampling.claim312`); the *probability* reading of those
lemmas is `Prob.lean`.
-/

namespace DLMST

open Classical

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

/-- **§3.6's display constant**, the same one `display_of_strategy_of_nat_counts` produces:
`C_ε = √2 + γ²·800000 + √2·((2γ²+γ+64γ⁷)·202²¹·2)`. -/
noncomputable def displayC (γ : ℝ) : ℝ :=
  Real.sqrt 2 + γ ^ 2 * 800000 +
    Real.sqrt 2 * ((2 * γ ^ 2 + γ + 64 * γ ^ 7) * ((202 : ℝ) ^ 21 * 2))

theorem displayC_nonneg {γ : ℝ} (hγ : 0 ≤ γ) : 0 ≤ displayC γ := by
  unfold displayC
  positivity

namespace Strategy

/-- **Children-only display from the three-bucket display.**  `|F|` and `|U|` are nonnegative, so
`Σ|Eᵢ| ≤ |F| + |U| + Σ|Eᵢ| ≤ RHS`. -/
theorem kidE_le_of_display (S : Strategy G) {ε C : ℝ}
    (hdis : ∀ (P : Finset V) (E₀ : Finset E),
      ((S P E₀).2.F.card : ℝ) + (((S P E₀).2.U).card : ℝ) +
          ((∑ i, ((S P E₀).2.kidE i).card : ℕ) : ℝ) ≤
        ε * (E₀.card : ℝ) + C * Real.sqrt ((E₀.card : ℝ) * ((S P E₀).2.P.card : ℝ))) :
    ∀ (P : Finset V) (E₀ : Finset E),
      ((∑ i, ((S P E₀).2.kidE i).card : ℕ) : ℝ) ≤
        ε * (E₀.card : ℝ) + C * Real.sqrt ((E₀.card : ℝ) * ((S P E₀).2.P.card : ℝ)) := by
  intro P E₀
  have h := hdis P E₀
  have h1 : (0 : ℝ) ≤ ((S P E₀).2.F.card : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (((S P E₀).2.U).card : ℝ) := Nat.cast_nonneg _
  linarith

/-- **The children-only display at every root, from the per-call counts.**  For *each* instance
`(P, E₀)` used as a root, the §3.5 estimate and the p. 24 input count hold along that instance's own
chain down to depth `|E₀|`; `display_of_strategy_of_nat_counts` then gives the three-bucket display
at that root, and `kidE_le_of_display` drops `|F|`, `|U|`.  This is the "the same procedure runs on
each child" step: the counts are a universally quantified premise, not a property of one root. -/
theorem kidE_display_of_counts (S : Strategy G) (hS : Wf S) {γ ε : ℝ}
    (hγ1 : 1 ≤ γ) (hε : 0 < ε) (hγε : 16 ≤ ε * γ)
    (hnm : ∀ (P : Finset V) (E₀ : Finset E),
      ((S P E₀).2.P.card : ℝ) ≤ 2 * ((S P E₀).2.E₀.card : ℝ))
    (herrU : ∀ (P : Finset V) (E₀ : Finset E) (d : ℕ), d ≤ E₀.card →
      ∀ a ∈ (Level.chain P E₀ S hS d).insts,
        (((S a.1 a.2).2.U).card : ℝ) ≤
          10 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 *
              Real.sqrt ((a.2.card : ℝ) * (a.1.card : ℝ))) +
            4 * (a.2.card : ℝ) / (γ * ((d : ℝ) + 1) ^ 3))
    (hrounds : ∀ (P : Finset V) (E₀ : Finset E) (d : ℕ), d ≤ E₀.card →
      ∀ a ∈ (Level.chain P E₀ S hS d).insts,
        ((∑ i, ((S a.1 a.2).2.kidE i).card : ℕ) : ℝ) ≤
          (((S a.1 a.2).2.U).card : ℝ) +
            2 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 * (((a.1.card - 1 : ℕ) : ℝ))) +
              (γ * ((d : ℝ) + 1) ^ 3) *
                ((((a.1.card - 1 : ℕ) : ℝ)) +
                  (8 * (γ * ((d : ℝ) + 1) ^ 3) ^ 3) ^ 2 * (a.1.card : ℝ))) :
    ∀ (P : Finset V) (E₀ : Finset E),
      ((∑ i, ((S P E₀).2.kidE i).card : ℕ) : ℝ) ≤
        ε * (E₀.card : ℝ) + displayC γ *
          Real.sqrt ((E₀.card : ℝ) * ((S P E₀).2.P.card : ℝ)) := by
  intro P E₀
  have h := display_of_strategy_of_nat_counts P E₀ S hS hγ1 hε hγε (hnm P E₀)
    (herrU P E₀) (hrounds P E₀)
  rw [(hS P E₀).2] at h
  have h1 : (0 : ℝ) ≤ ((S P E₀).2.F.card : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (((S P E₀).2.U).card : ℝ) := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ ((∑ i, ((S P E₀).2.kidE i).card : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold displayC
  linarith

/-- **The `m/2` shrink at every node, from the per-call counts.**  Combines the children-only
display with the post-phase vertex bound `n ≤ 2m/2^{2j}` (`children_shrink`), so the strong
induction of `cost_linear` applies along the whole branch tree. -/
theorem child_shrink_of_counts (S : Strategy G) (hS : Wf S) {γ ε : ℝ}
    (hγ1 : 1 ≤ γ) (hε : 0 < ε) (hε8 : ε ≤ 1 / 8) (hγε : 16 ≤ ε * γ) {j : ℕ}
    (hj : displayC γ * 2 / (2 : ℝ) ^ j ≤ 3 / 8)
    (hnm : ∀ (P : Finset V) (E₀ : Finset E),
      ((S P E₀).2.P.card : ℝ) ≤ 2 * ((S P E₀).2.E₀.card : ℝ))
    (hnphase : ∀ (P : Finset V) (E₀ : Finset E),
      ((S P E₀).2.P.card : ℝ) ≤ 2 * (E₀.card : ℝ) / (2 : ℝ) ^ (2 * j))
    (herrU : ∀ (P : Finset V) (E₀ : Finset E) (d : ℕ), d ≤ E₀.card →
      ∀ a ∈ (Level.chain P E₀ S hS d).insts,
        (((S a.1 a.2).2.U).card : ℝ) ≤
          10 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 *
              Real.sqrt ((a.2.card : ℝ) * (a.1.card : ℝ))) +
            4 * (a.2.card : ℝ) / (γ * ((d : ℝ) + 1) ^ 3))
    (hrounds : ∀ (P : Finset V) (E₀ : Finset E) (d : ℕ), d ≤ E₀.card →
      ∀ a ∈ (Level.chain P E₀ S hS d).insts,
        ((∑ i, ((S a.1 a.2).2.kidE i).card : ℕ) : ℝ) ≤
          (((S a.1 a.2).2.U).card : ℝ) +
            2 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 * (((a.1.card - 1 : ℕ) : ℝ))) +
              (γ * ((d : ℝ) + 1) ^ 3) *
                ((((a.1.card - 1 : ℕ) : ℝ)) +
                  (8 * (γ * ((d : ℝ) + 1) ^ 3) ^ 3) ^ 2 * (a.1.card : ℝ))) :
    ∀ (P : Finset V) (E₀ : Finset E),
      ((∑ i, ((S P E₀).2.kidE i).card : ℕ) : ℝ) ≤ (E₀.card : ℝ) / 2 := by
  have hγ0 : (0 : ℝ) ≤ γ := le_trans zero_le_one hγ1
  intro P E₀
  exact children_shrink S P E₀ (C := displayC γ) (ε := ε) (j := j)
    (displayC_nonneg hγ0) hε8 hj
    (kidE_display_of_counts S hS hγ1 hε hγε hnm herrU hrounds P E₀) (hnphase P E₀)

/-- **B2: the branch recursion is linear in counting work.**  Let `S` be a terminating strategy
(`Strict` + `Leaf`) whose every node carries the paper's two per-call numeric outputs (§3.5 estimate
`|U| ≤ 10t²√(mn) + 4m/t`, p. 24 input count) at its own depth `d ≤ |E₀|`, whose vertex count obeys
the post-Borůvka bound `n ≤ 2m/2^{2j}`, and whose constants satisfy `ε ≤ 1/8` and
`C_ε·2/2^j ≤ 3/8`.  Then every counting cost obeying the per-node recursion
`T(P,E₀) ≤ Σᵢ T(kidᵢ) + c·|E₀|` is at most `2c·|E₀|` on **every** instance.

This is the paper's Theorem 4.1 recurrence `T(m) ≤ Σᵢ T(mᵢ) + O(m)` with `Σmᵢ ≤ m/2`, proved
instance-by-instance along the branching tree — the `m`-indexed worst case and any depth–size
identity are both absent. -/
theorem cost_linear_of_counts (S : Strategy G) (hS : Wf S) (hstr : Strict S) (hleaf : Leaf S)
    {γ ε : ℝ} (hγ1 : 1 ≤ γ) (hε : 0 < ε) (hε8 : ε ≤ 1 / 8) (hγε : 16 ≤ ε * γ) {j : ℕ}
    (hj : displayC γ * 2 / (2 : ℝ) ^ j ≤ 3 / 8)
    (hnm : ∀ (P : Finset V) (E₀ : Finset E),
      ((S P E₀).2.P.card : ℝ) ≤ 2 * ((S P E₀).2.E₀.card : ℝ))
    (hnphase : ∀ (P : Finset V) (E₀ : Finset E),
      ((S P E₀).2.P.card : ℝ) ≤ 2 * (E₀.card : ℝ) / (2 : ℝ) ^ (2 * j))
    (herrU : ∀ (P : Finset V) (E₀ : Finset E) (d : ℕ), d ≤ E₀.card →
      ∀ a ∈ (Level.chain P E₀ S hS d).insts,
        (((S a.1 a.2).2.U).card : ℝ) ≤
          10 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 *
              Real.sqrt ((a.2.card : ℝ) * (a.1.card : ℝ))) +
            4 * (a.2.card : ℝ) / (γ * ((d : ℝ) + 1) ^ 3))
    (hrounds : ∀ (P : Finset V) (E₀ : Finset E) (d : ℕ), d ≤ E₀.card →
      ∀ a ∈ (Level.chain P E₀ S hS d).insts,
        ((∑ i, ((S a.1 a.2).2.kidE i).card : ℕ) : ℝ) ≤
          (((S a.1 a.2).2.U).card : ℝ) +
            2 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 * (((a.1.card - 1 : ℕ) : ℝ))) +
              (γ * ((d : ℝ) + 1) ^ 3) *
                ((((a.1.card - 1 : ℕ) : ℝ)) +
                  (8 * (γ * ((d : ℝ) + 1) ^ 3) ^ 3) ^ 2 * (a.1.card : ℝ)))
    (T : Finset V → Finset E → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hrec : ∀ (P : Finset V) (E₀ : Finset E),
      T P E₀ ≤ (∑ i : Fin ((S P E₀).1), T ((S P E₀).2.kidV i) ((S P E₀).2.kidE i)) +
        c * (E₀.card : ℝ)) :
    ∀ (P : Finset V) (E₀ : Finset E), T P E₀ ≤ 2 * c * (E₀.card : ℝ) :=
  cost_linear_of_display S hstr hleaf (displayC_nonneg (le_trans zero_le_one hγ1)) hε8 hj
    (kidE_display_of_counts S hS hγ1 hε hγε hnm herrU hrounds) hnphase T c hc hrec

end Strategy

/-- **The phase constant is attainable.**  For any `γ`, some number `j` of contracted halvings
makes `C_ε·2/2^j ≤ 3/8`: `2^j` is unbounded, so the paper's "choose `k` large enough" is a
theorem about `C_ε`, not an extra assumption on the algorithm.  (The instance-level premise
`n ≤ 2m/2^{2j}` is separate and is what Borůvka's `k` phases supply.) -/
theorem exists_displayC_phase (γ : ℝ) : ∃ j : ℕ, displayC γ * 2 / (2 : ℝ) ^ j ≤ 3 / 8 := by
  by_cases hsmall : displayC γ * 2 ≤ 3 / 8
  · exact ⟨0, by simpa using hsmall⟩
  · simp only [not_le] at hsmall
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (displayC γ * 2 * (8 / 3))
      (show (1 : ℝ) < 2 by norm_num)
    refine ⟨n, ?_⟩
    have hpos : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) n
    rw [div_le_iff₀ hpos]
    nlinarith

end DLMST