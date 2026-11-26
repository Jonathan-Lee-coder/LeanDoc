import DLMST.Assembly
import DLMST.Bookkeeping

/-!
# Linear cost on every instance: the recursion without the `m`-indexed worst case

`Certificate.lean`/`CertificateBuild.lean` phrase §4 as an inequality about the *worst case over
instances with `m` edges*: `Σ|Eᵢ| ≤ ρm + C√(m·n_sub(m))`, and `certificate_implies_linear` closes the
recursion for a sequence `T : ℕ → ℝ`.  That leaves two pieces of bookkeeping outside the machine: the
`m`-indexed instance family (`subSizes m`, `nsub m` must be read off *the* algorithm's recursion tree)
and the depth–size identity `t_a = γ(d+1)³` that makes one `t` serve a whole level.

Neither is needed if the recursion is stated where it actually lives — on the strategy's own
instances.  A `Strategy G` is a function `(P, E₀) ↦ CallOut`, children are instances of the *same*
graph, and `Strategy.Strict` decreases the edge count, so the recursion tree is a well-founded tree
in `E₀.card` and a strong induction replaces the worst-case function.  This file proves that:

* `Strategy.cost_linear` — any cost measure satisfying the per-instance recursion
  `T(P,E₀) ≤ Σᵢ T(kidᵢ) + c·|E₀|`, whose children's total edge count is at most `|E₀|/2`, is
  `≤ 2c|E₀|` on **every** instance (conclusion for all `(P, E₀)` at once, not just the worst case);

* `Strategy.children_shrink` — the children-only display `Σ|Eᵢ| ≤ εm + C√(mn)` (which
  `Assembly.sum_kidE_le_paper_bound` delivers), together with the post-phase vertex bound
  `n ≤ 2m/2^{2j}`, gives the `m/2` shrink `Σ|Eᵢ| ≤ εm + C√(m·2m/2^{2j}) ≤ m/8 + 3m/8`
  (`Bookkeeping.closure`);

* `Strategy.cost_linear_of_display` — the two combined: per-instance display + vertex halving +
  constants `0 ≤ C`, `ε ≤ 1/8`, `C·2/2^j ≤ 3/8` ⟹ every instance's cost is `≤ 2c|E₀|`.

The display is taken as *data at each instance* — which is exactly what the paper asserts about its
procedure ("run the same procedure on each child"), and is what `display_of_roundData_sampling`
delivers for the root of any chain.  The caveat is worth stating plainly: in the paper the parameter
`t_c = γ(d−c+1)³` depends on the *level*, and a Lean `Strategy` is a function of the instance alone,
so a single strategy cannot use a level-dependent `t` while also being its own recursive callee.
The depth-indexed reading is covered by the level-chain theorems (`Procedure.lean`'s
`errors_levels_poly` etc.); this file covers the size-indexed reading, where each call re-derives
its parameter from its instance.
-/

namespace DLMST

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

namespace Strategy

/-- **The children's half-bound implies strict decrease.**  If a strategy hands its children at most
half its edges in total (`hshrink`), then each child's edge set is strictly smaller than the
instance's — the `Strategy.Strict` premise of `cost_linear` is implied by `hshrink`, as its
docstring claims.  (For a nonempty instance `|E₀| ≥ 1`, so a child with `|kidE i| ≤ |E₀|/2` has
`|kidE i| < |E₀|`.) -/
theorem strict_of_shrink (S : Strategy G)
    (hshrink : ∀ (P : Finset V) (E₀ : Finset E),
      ((∑ i, ((S P E₀).2.kidE i).card : ℕ) : ℝ) ≤ (E₀.card : ℝ) / 2) :
    Strategy.Strict S := by
  intro P E₀ hne i
  have hpos : 0 < E₀.card := Finset.card_pos.mpr hne
  have hsingle : (((S P E₀).2.kidE i).card : ℝ) ≤ (E₀.card : ℝ) / 2 :=
    le_trans (by
      exact_mod_cast Finset.single_le_sum
        (f := fun i => ((S P E₀).2.kidE i).card) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)) (hshrink P E₀)
  have h2 : ((S P E₀).2.kidE i).card * 2 ≤ E₀.card := by
    have hreal : (((S P E₀).2.kidE i).card * 2 : ℝ) ≤ (E₀.card : ℝ) := by
      linarith
    exact_mod_cast hreal
  have hle : ((S P E₀).2.kidE i).card ≤ E₀.card / 2 :=
    (Nat.le_div_iff_mul_le (by norm_num)).mpr h2
  exact lt_of_le_of_lt hle (Nat.div_lt_self hpos (by norm_num))

/-- **The display's `m/2` shrink, per instance.**  If the children's total obeys the paper's
children-only display bound `Σ|Eᵢ| ≤ εm + C√(mn)` (this is `sum_kidE_le_paper_bound`'s conclusion),
and the instance's vertex count obeys the post-phase bound `n ≤ 2m/2^{2j}`, then
`Σ|Eᵢ| ≤ εm + C√(m·2m/2^{2j}) ≤ m/8 + 3m/8 = m/2` (`Bookkeeping.closure`). -/
theorem children_shrink (S : Strategy G) (P : Finset V) (E₀ : Finset E)
    {C ε : ℝ} {j : ℕ} (hC : 0 ≤ C) (hε : ε ≤ 1 / 8)
    (hj : C * 2 / (2 : ℝ) ^ j ≤ 3 / 8)
    (hdisp : ((∑ i, ((S P E₀).2.kidE i).card : ℕ) : ℝ) ≤
      ε * (E₀.card : ℝ) + C * Real.sqrt ((E₀.card : ℝ) * ((S P E₀).2.P.card : ℝ)))
    (hn : ((S P E₀).2.P.card : ℝ) ≤ 2 * (E₀.card : ℝ) / (2 : ℝ) ^ (2 * j)) :
    ((∑ i, ((S P E₀).2.kidE i).card : ℕ) : ℝ) ≤ (E₀.card : ℝ) / 2 := by
  have hm0 : (0 : ℝ) ≤ (E₀.card : ℝ) := Nat.cast_nonneg _
  have hprod : (E₀.card : ℝ) * ((S P E₀).2.P.card : ℝ) ≤
      (E₀.card : ℝ) * (2 * (E₀.card : ℝ) / (2 : ℝ) ^ (2 * j)) :=
    mul_le_mul_of_nonneg_left hn hm0
  have hsqrt := Real.sqrt_le_sqrt hprod
  have hCsqrt : C * Real.sqrt ((E₀.card : ℝ) * ((S P E₀).2.P.card : ℝ)) ≤
      C * Real.sqrt ((E₀.card : ℝ) * (2 * (E₀.card : ℝ) / (2 : ℝ) ^ (2 * j))) :=
    mul_le_mul_of_nonneg_left hsqrt hC
  have hεm : ε * (E₀.card : ℝ) ≤ (1 / 8 : ℝ) * (E₀.card : ℝ) :=
    mul_le_mul_of_nonneg_right hε hm0
  have hε8 : (1 / 8 : ℝ) * (E₀.card : ℝ) = (E₀.card : ℝ) / 8 := by ring
  have hcl := closure E₀.card C j hC hj
  linarith

/-- **The strategy's own recursion is linear, instance by instance.**  The measure `T` satisfies the
recursion along the strategy's children (`hrec`), the children's edge total is at most half the
instance (`hshrink`), and the empty instance costs nothing (`Leaf` + `hrec`).  Then every instance's
cost is `≤ 2c|E₀|` — strong induction in `E₀.card` along the well-founded recursion tree, with no
worst case over `m` anywhere.

The strict decrease is taken from `Strategy.Strict` (the paper's "a child only receives edges outside
`F`", machine-checked by `CallOut.kidE_card_lt`); it is also implied by `hshrink`, which is what the
application `cost_linear_of_display` uses. -/
theorem cost_linear (S : Strategy G) (hstr : Strategy.Strict S) (hleaf : Strategy.Leaf S)
    (hshrink : ∀ (P : Finset V) (E₀ : Finset E),
      ((∑ i, ((S P E₀).2.kidE i).card : ℕ) : ℝ) ≤ (E₀.card : ℝ) / 2)
    (T : Finset V → Finset E → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hrec : ∀ (P : Finset V) (E₀ : Finset E),
      T P E₀ ≤ (∑ i : Fin ((S P E₀).1), T ((S P E₀).2.kidV i) ((S P E₀).2.kidE i)) +
        c * (E₀.card : ℝ)) :
    ∀ (P : Finset V) (E₀ : Finset E), T P E₀ ≤ 2 * c * (E₀.card : ℝ) := by
  suffices H : ∀ m : ℕ, ∀ (P : Finset V) (E₀ : Finset E), E₀.card = m →
      T P E₀ ≤ 2 * c * (E₀.card : ℝ) from fun P E₀ => H E₀.card P E₀ rfl
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro P E₀ hm
    by_cases hE : E₀ = ∅
    · subst hE
      have hsum : (∑ i : Fin ((S P ∅).1),
          T ((S P ∅).2.kidV i) ((S P ∅).2.kidE i)) = 0 := by
        refine Finset.sum_eq_zero (fun i _ => ?_)
        have h0 : (S P ∅).1 = 0 := hleaf P
        exact absurd i.isLt (by omega)
      calc T P ∅ ≤ (∑ i : Fin ((S P ∅).1),
            T ((S P ∅).2.kidV i) ((S P ∅).2.kidE i)) + c * ((∅ : Finset E).card : ℝ) :=
            hrec P ∅
        _ = 0 := by rw [hsum]; simp
        _ = 2 * c * ((∅ : Finset E).card : ℝ) := by simp
    · have hne : (E₀.Nonempty) := Finset.ne_empty_iff_nonempty.mp hE
      have hmE : (E₀.card : ℝ) = (m : ℝ) := by rw [hm]
      have hkid : ∀ i : Fin ((S P E₀).1), ((S P E₀).2.kidE i).card < m := by
        intro i
        have h1 := hstr P E₀ hne i
        rwa [hm] at h1
      have hle : ∀ i : Fin ((S P E₀).1),
          T ((S P E₀).2.kidV i) ((S P E₀).2.kidE i) ≤
            2 * c * (((S P E₀).2.kidE i).card : ℝ) := by
        intro i
        exact ih _ (hkid i) ((S P E₀).2.kidV i) ((S P E₀).2.kidE i) rfl
      have hcast_sum : (∑ i : Fin ((S P E₀).1), (((S P E₀).2.kidE i).card : ℝ)) =
          ((∑ i : Fin ((S P E₀).1), ((S P E₀).2.kidE i).card : ℕ) : ℝ) :=
        (Nat.cast_sum Finset.univ (fun i => ((S P E₀).2.kidE i).card)).symm
      have hsum_eq : (∑ i : Fin ((S P E₀).1), 2 * c * (((S P E₀).2.kidE i).card : ℝ)) =
          2 * c * (∑ i : Fin ((S P E₀).1), (((S P E₀).2.kidE i).card : ℝ)) := by
        rw [Finset.mul_sum]
      have hshrinkE := hshrink P E₀
      rw [hmE] at hshrinkE
      have hfin : 2 * c * (∑ i : Fin ((S P E₀).1), (((S P E₀).2.kidE i).card : ℝ)) ≤
          2 * c * ((m : ℝ) / 2) := by
        rw [hcast_sum]
        exact mul_le_mul_of_nonneg_left hshrinkE (by linarith)
      have hrecE := hrec P E₀
      rw [hmE] at hrecE
      calc T P E₀ ≤ (∑ i : Fin ((S P E₀).1),
            T ((S P E₀).2.kidV i) ((S P E₀).2.kidE i)) + c * (m : ℝ) := hrecE
        _ ≤ (∑ i : Fin ((S P E₀).1), 2 * c * (((S P E₀).2.kidE i).card : ℝ)) +
              c * (m : ℝ) := by
          have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hle i)
          linarith
        _ = 2 * c * (∑ i : Fin ((S P E₀).1), (((S P E₀).2.kidE i).card : ℝ)) +
              c * (m : ℝ) := by rw [hsum_eq]
        _ ≤ 2 * c * ((m : ℝ) / 2) + c * (m : ℝ) := by linarith [hfin]
        _ = 2 * c * (m : ℝ) := by ring
        _ = 2 * c * (E₀.card : ℝ) := by rw [hmE]

/-- **Linear cost without a separate strictness hypothesis.**  `cost_linear` with its
`Strategy.Strict` premise discharged by the children's half-bound (`strict_of_shrink`). -/
theorem cost_linear_of_shrink (S : Strategy G) (hleaf : Strategy.Leaf S)
    (hshrink : ∀ (P : Finset V) (E₀ : Finset E),
      ((∑ i, ((S P E₀).2.kidE i).card : ℕ) : ℝ) ≤ (E₀.card : ℝ) / 2)
    (T : Finset V → Finset E → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hrec : ∀ (P : Finset V) (E₀ : Finset E),
      T P E₀ ≤ (∑ i : Fin ((S P E₀).1), T ((S P E₀).2.kidV i) ((S P E₀).2.kidE i)) +
        c * (E₀.card : ℝ)) :
    ∀ (P : Finset V) (E₀ : Finset E), T P E₀ ≤ 2 * c * (E₀.card : ℝ) :=
  cost_linear S (strict_of_shrink S hshrink) hleaf hshrink T c hc hrec

/-- **Linear cost from the per-instance display.**  The children-only display
`Σ|Eᵢ| ≤ εm + C√(mn)` and the post-phase vertex bound `n ≤ 2m/2^{2j}` are assumed at *every*
instance (this is the paper's "the same procedure runs on each child"), the constants satisfy
`0 ≤ C`, `ε ≤ 1/8`, `C·2/2^j ≤ 3/8`.  Then any cost measure obeying the strategy's recursion is
`≤ 2c|E₀|` on every instance.  Neither a sequence `subSizes : ℕ → List ℕ` nor a depth–size
identity appears. -/
theorem cost_linear_of_display (S : Strategy G) (hstr : Strategy.Strict S)
    (hleaf : Strategy.Leaf S) {C ε : ℝ} {j : ℕ} (hC : 0 ≤ C) (hε : ε ≤ 1 / 8)
    (hj : C * 2 / (2 : ℝ) ^ j ≤ 3 / 8)
    (hdisp : ∀ (P : Finset V) (E₀ : Finset E),
      ((∑ i, ((S P E₀).2.kidE i).card : ℕ) : ℝ) ≤
        ε * (E₀.card : ℝ) + C * Real.sqrt ((E₀.card : ℝ) * ((S P E₀).2.P.card : ℝ)))
    (hn : ∀ (P : Finset V) (E₀ : Finset E),
      ((S P E₀).2.P.card : ℝ) ≤ 2 * (E₀.card : ℝ) / (2 : ℝ) ^ (2 * j))
    (T : Finset V → Finset E → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hrec : ∀ (P : Finset V) (E₀ : Finset E),
      T P E₀ ≤ (∑ i : Fin ((S P E₀).1), T ((S P E₀).2.kidV i) ((S P E₀).2.kidE i)) +
        c * (E₀.card : ℝ)) :
    ∀ (P : Finset V) (E₀ : Finset E), T P E₀ ≤ 2 * c * (E₀.card : ℝ) :=
  cost_linear S hstr hleaf
    (fun P E₀ => children_shrink S P E₀ hC hε hj (hdisp P E₀) (hn P E₀))
    T c hc hrec

end Strategy

end DLMST