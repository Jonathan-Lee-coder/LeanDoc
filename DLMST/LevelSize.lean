import DLMST.CostLinear
import DLMST.BoruvkaHalving

/-!
# The depth–size identity: a level's size is halved, so depth is logarithmic

`CostLinear.lean` replaced the `m`-indexed worst case by a per-instance recursion; what it took as
data was the shrink `Σᵢ|Eᵢ| ≤ |E₀|/2`.  This file closes the remaining gap between the *level*
index and the *instance's size*:

* `LevelChain.edges_halve` — a per-node halving `2·Σᵢ|Eᵢ| ≤ |E₀|` makes one whole level's edge
  total at most half the previous level's (`chain_edges_succ` + `Finset.sum_le_sum`);
* `LevelChain.edges_pow_two_le` — iterating: **the level `d` edge total times `2^d` is at most the
  root's edge count**; and per instance (`instance_card_mul_pow_le`), a node at depth `d` satisfies
  `|E₀| · 2^d ≤ m`;
* `LevelChain.pow_two_le_of_mem` / `level_le_card` / `level_le_log2` — a *nonempty* instance at depth
  `d` forces `2^d ≤ m`, hence `d ≤ ⌊log₂ m⌋`: in particular the recursion's depth is logarithmic in
  the root's edge count;
* `LevelChain.t_level_le` — hence the paper's per-level parameter is bounded by its value at the
  root: `γ(d+1)³ ≤ γ(m+1)³` for `0 ≤ γ`.  (The sharper `γ(log₂m+1)³` follows from `level_le_log2`
  the same way; it is stated at `m` to keep the arithmetic free of `Nat.log2` casts.)

The second half of the file records *which reading of the paper's `t_c` is machine-realizable*:

* `Strategy.Cpaper` — the display constant of `Assembly.sum_kidE_le_paper_bound`, named;
* `Strategy.display_of_roundData_nodes` — that theorem re-exported with `Cpaper` (per call);
* `Strategy.hn_root_of_phases` / `Strategy.cost_linear_of_contraction` — the aspect-ratio hypothesis
  `hn` is *produced* at the root by `BoruvkaHalving.compCount_le_real_of_empty` (at `k = 2j`) and
  propagated to the children by the per-call contraction `|kidV i| ≤ 2|kidE i|/2^{2j}`, so it is
  asked only of the instance the caller actually queries — never of every instance at once;
* `Strategy.htd_all_roots_impossible` — **no instance-indexed `tOf` can satisfy `htd` for every root
  at once**: a nonempty instance `E₀` with any child `X` puts `X` at depth 1 of `E₀`'s level chain
  and at depth 0 of `X`'s own, where `tOf X` would have to be simultaneously `8γ` and `γ`.  So the
  paper's `t_c = γ(d−c+1)³` is necessarily **per-call (level-stamped) bookkeeping**, not a function
  of the instance alone — which is why the round-data interface keeps `tOf`/`htd` as data, and why
  the display is consumed per call (`display_of_roundData_nodes`) while the cost recursion
  (`cost_linear_of_nodes`) takes the per-node display as its input.
-/

namespace DLMST

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

namespace LevelChain

variable (P : Finset V) (E₀ : Finset E) (S : Strategy G) (hS : Strategy.Wf S)

/-- **One level halves.**  If every call passes at most half its edges to its children
(`2·Σᵢ|Eᵢ| ≤ |E₀|`), the next level's edge total is at most half of this level's
(`chain_edges_succ` turns the level total into the sum of the calls' child inputs). -/
theorem edges_halve
    (hshrink : ∀ (P' : Finset V) (E₀' : Finset E),
      2 * (∑ i, ((S P' E₀').2.kidE i).card) ≤ E₀'.card)
    (d : ℕ) :
    (Level.chain P E₀ S hS (d + 1)).edges * 2 ≤ (Level.chain P E₀ S hS d).edges := by
  rw [chain_edges_succ P E₀ S hS d, Finset.sum_mul]
  show (∑ a ∈ (Level.chain P E₀ S hS d).insts,
      (∑ i, ((S a.1 a.2).2.kidE i).card) * 2) ≤
    ∑ a ∈ (Level.chain P E₀ S hS d).insts, a.2.card
  refine Finset.sum_le_sum (fun a (_ : a ∈ _) => ?_)
  have h := hshrink a.1 a.2
  omega

/-- **The level's edge total decays by `2^d`.**  `d` halvings stack: level `d` carries at most
`m / 2^d` edges in total. -/
theorem edges_pow_two_le
    (hshrink : ∀ (P' : Finset V) (E₀' : Finset E),
      2 * (∑ i, ((S P' E₀').2.kidE i).card) ≤ E₀'.card)
    (d : ℕ) :
    (Level.chain P E₀ S hS d).edges * 2 ^ d ≤ E₀.card := by
  induction d with
  | zero =>
      rw [chain_edges P E₀ S hS]
      simp
  | succ k ih =>
      have hs := edges_halve P E₀ S hS hshrink k
      calc (Level.chain P E₀ S hS (k + 1)).edges * 2 ^ (k + 1)
          = ((Level.chain P E₀ S hS (k + 1)).edges * 2) * 2 ^ k := by
            rw [Nat.pow_succ]
            ring
        _ ≤ (Level.chain P E₀ S hS k).edges * 2 ^ k := Nat.mul_le_mul_right _ hs
        _ ≤ E₀.card := ih

/-- **Every instance at depth `d` is small**: `|E₀| · 2^d ≤ m`.  This is the instance-level form of
the depth–size identity — the level index is recovered from the size up to a factor of `2`. -/
theorem instance_card_mul_pow_le
    (hshrink : ∀ (P' : Finset V) (E₀' : Finset E),
      2 * (∑ i, ((S P' E₀').2.kidE i).card) ≤ E₀'.card)
    (d : ℕ) {b : Inst V E} (hb : b ∈ (Level.chain P E₀ S hS d).insts) :
    b.2.card * 2 ^ d ≤ E₀.card := by
  have h1 : b.2.card ≤ (Level.chain P E₀ S hS d).edges :=
    Finset.single_le_sum (f := fun a : Inst V E => a.2.card) (fun _ _ => Nat.zero_le _) hb
  exact le_trans (Nat.mul_le_mul_right _ h1) (edges_pow_two_le P E₀ S hS hshrink d)

/-- **A nonempty instance at depth `d` forces `2^d ≤ m`.** -/
theorem pow_two_le_of_mem
    (hshrink : ∀ (P' : Finset V) (E₀' : Finset E),
      2 * (∑ i, ((S P' E₀').2.kidE i).card) ≤ E₀'.card)
    (d : ℕ) {b : Inst V E} (hb : b ∈ (Level.chain P E₀ S hS d).insts)
    (hne : b.2.Nonempty) :
    2 ^ d ≤ E₀.card := by
  have h1 : 1 ≤ b.2.card := Finset.card_pos.mpr hne
  calc 2 ^ d = 1 * 2 ^ d := (Nat.one_mul _).symm
    _ ≤ b.2.card * 2 ^ d := Nat.mul_le_mul_right _ h1
    _ ≤ E₀.card := instance_card_mul_pow_le P E₀ S hS hshrink d hb

/-- **Depth is at most the root's edge count.**  Since `d < 2^d`, a nonempty instance at depth `d`
already forces `d < m`. -/
theorem level_lt_card
    (hshrink : ∀ (P' : Finset V) (E₀' : Finset E),
      2 * (∑ i, ((S P' E₀').2.kidE i).card) ≤ E₀'.card)
    (d : ℕ) {b : Inst V E} (hb : b ∈ (Level.chain P E₀ S hS d).insts)
    (hne : b.2.Nonempty) :
    d < E₀.card :=
  lt_of_lt_of_le Nat.lt_two_pow_self (pow_two_le_of_mem P E₀ S hS hshrink d hb hne)

/-- **Depth is logarithmic**: a nonempty instance at depth `d` satisfies `d ≤ ⌊log₂ m⌋`. -/
theorem level_le_log2
    (hshrink : ∀ (P' : Finset V) (E₀' : Finset E),
      2 * (∑ i, ((S P' E₀').2.kidE i).card) ≤ E₀'.card)
    (d : ℕ) {b : Inst V E} (hb : b ∈ (Level.chain P E₀ S hS d).insts)
    (hne : b.2.Nonempty) (hm : E₀.card ≠ 0) :
    d ≤ Nat.log2 E₀.card :=
  (Nat.le_log2 hm).mpr (pow_two_le_of_mem P E₀ S hS hshrink d hb hne)

/-- **The paper's parameter at depth `d` is at most its value at the root**:
`γ(d+1)³ ≤ γ(m+1)³` for `0 ≤ γ`, because a nonempty depth-`d` instance forces `d < m`. -/
theorem t_level_le
    (hshrink : ∀ (P' : Finset V) (E₀' : Finset E),
      2 * (∑ i, ((S P' E₀').2.kidE i).card) ≤ E₀'.card)
    {γ : ℝ} (hγ : 0 ≤ γ) (d : ℕ) {b : Inst V E}
    (hb : b ∈ (Level.chain P E₀ S hS d).insts) (hne : b.2.Nonempty) :
    γ * ((d : ℝ) + 1) ^ 3 ≤ γ * ((E₀.card : ℝ) + 1) ^ 3 := by
  have hd : d ≤ E₀.card := le_of_lt (level_lt_card P E₀ S hS hshrink d hb hne)
  have hcast : (d : ℝ) + 1 ≤ (E₀.card : ℝ) + 1 := by
    have h1 : ((d + 1 : ℕ) : ℝ) ≤ ((E₀.card + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_right hd 1
    push_cast at h1 ⊢
    linarith
  have hcube : ((d : ℝ) + 1) ^ 3 ≤ ((E₀.card : ℝ) + 1) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hcast 3
  exact mul_le_mul_of_nonneg_left hcube hγ

end LevelChain

namespace Strategy

/-- The display constant of `Assembly.sum_kidE_le_paper_bound`, named: §3.6's root constant
`√2 + γ²·800000 + √2·((2γ²+γ+64γ⁷)·202²¹·2)`. -/
noncomputable def Cpaper (γ : ℝ) : ℝ :=
  Real.sqrt 2 + γ ^ 2 * 800000 +
    Real.sqrt 2 * ((2 * γ ^ 2 + γ + 64 * γ ^ 7) * ((202 : ℝ) ^ 21 * 2))

theorem Cpaper_nonneg {γ : ℝ} (hγ : 1 ≤ γ) : 0 ≤ Cpaper γ := by
  have h0 : (0 : ℝ) ≤ γ := by linarith
  unfold Cpaper
  positivity

/-- **One call's display, in the named constant.**  `sum_kidE_le_paper_bound` restated with
`Cpaper γ`; this is the per-call object that `cost_linear_of_nodes` consumes at every node. -/
theorem display_of_roundData_nodes {k : ℕ} (tOf : Finset V → Finset E → ℕ)
    (RD : ∀ (P : Finset V) (E₀ : Finset E), CallOut.RoundData G P E₀ (Fin k) (tOf P E₀))
    (P : Finset V) (E₀ : Finset E)
    {γ ε : ℝ} (hγ1 : 1 ≤ γ) (hε : 0 < ε) (hγε : 16 ≤ ε * γ)
    (hnm : (P.card : ℝ) ≤ 2 * (E₀.card : ℝ))
    (hnpos : ∀ (P' : Finset V), 1 ≤ P'.card)
    (herrU : ∀ (P' : Finset V) (E₀' : Finset E), (((RD P' E₀').toCall.U).card : ℝ) ≤
      10 * ((tOf P' E₀' : ℝ) ^ 2 * Real.sqrt ((E₀'.card : ℝ) * (P'.card : ℝ))) +
        4 * (E₀'.card : ℝ) / (tOf P' E₀' : ℝ))
    (hrnd : ∀ (P' : Finset V) (E₀' : Finset E), (∑ i, ((RD P' E₀').toCall.kidE i).card) ≤
      ((RD P' E₀').toCall.U).card + 2 * (tOf P' E₀') ^ 2 * (P'.card - 1) +
        (tOf P' E₀') * ((P'.card - 1) + (8 * (tOf P' E₀') ^ 3) ^ 2 * P'.card))
    (htd : ∀ (d : ℕ), d ≤ E₀.card → ∀ a ∈ (Level.chain P E₀ (ofRoundDataT tOf RD)
        (ofRoundDataT_wf tOf RD) d).insts,
      (tOf a.1 a.2 : ℝ) = γ * ((d : ℝ) + 1) ^ 3) :
    ((∑ i, (((ofRoundDataT tOf RD) P E₀).2.kidE i).card : ℕ) : ℝ) ≤
      ε * (E₀.card : ℝ) + Cpaper γ * Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) := by
  have h := sum_kidE_le_paper_bound tOf RD P E₀ hγ1 hε hγε hnm hnpos herrU hrnd htd
  simpa [Cpaper] using h

/-- **§4's linear cost, node by node, in the paper's constants.**  The per-node display is the paper's
per-call statement (`display_of_roundData_nodes` supplies it once the call's own §3.5/§3.6 data are
in place), the post-phase vertex bound `n ≤ 2m/2^{2j}` is `BoruvkaHalving`'s, and `Strict`/`Leaf`
are termination.  Then **every** instance's cost is `≤ 2c|E₀|` — no `m`-indexed worst case anywhere.

`hdisp` has no `tOf` in it: the paper's `t_c` never becomes a function of the instance (see
`htd_all_roots_impossible`); it enters only inside each call's own display. -/
theorem cost_linear_of_nodes (S : Strategy G) (hstr : Strategy.Strict S) (hleaf : Strategy.Leaf S)
    {γ ε : ℝ} (hγ1 : 1 ≤ γ) (hε : ε ≤ 1 / 8)
    (hdisp : ∀ (P : Finset V) (E₀ : Finset E),
      ((∑ i, ((S P E₀).2.kidE i).card : ℕ) : ℝ) ≤
        ε * (E₀.card : ℝ) +
          Cpaper γ * Real.sqrt ((E₀.card : ℝ) * ((S P E₀).2.P.card : ℝ)))
    {j : ℕ} (hj : Cpaper γ * 2 / (2 : ℝ) ^ j ≤ 3 / 8)
    (hn : ∀ (P : Finset V) (E₀ : Finset E),
      ((S P E₀).2.P.card : ℝ) ≤ 2 * (E₀.card : ℝ) / (2 : ℝ) ^ (2 * j))
    (T : Finset V → Finset E → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hrec : ∀ (P : Finset V) (E₀ : Finset E),
      T P E₀ ≤ (∑ i : Fin ((S P E₀).1), T ((S P E₀).2.kidV i) ((S P E₀).2.kidE i)) +
        c * (E₀.card : ℝ)) :
    ∀ (P : Finset V) (E₀ : Finset E), T P E₀ ≤ 2 * c * (E₀.card : ℝ) :=
  cost_linear_of_display S hstr hleaf (Cpaper_nonneg hγ1) hε hj hdisp hn T c hc hrec

/-- **The same, with the phase count chosen by the constants.**  `Bookkeeping.exists_phase` supplies
a `j` with `Cpaper γ · 2/2^j ≤ 3/8`, so the vertex bound only has to be available at some such
`j` — the paper's "run enough Borůvka phases". -/
theorem cost_linear_of_nodes_exists (S : Strategy G) (hstr : Strategy.Strict S)
    (hleaf : Strategy.Leaf S) {γ ε : ℝ} (hγ1 : 1 ≤ γ) (hε : ε ≤ 1 / 8)
    (hdisp : ∀ (P : Finset V) (E₀ : Finset E),
      ((∑ i, ((S P E₀).2.kidE i).card : ℕ) : ℝ) ≤
        ε * (E₀.card : ℝ) +
          Cpaper γ * Real.sqrt ((E₀.card : ℝ) * ((S P E₀).2.P.card : ℝ)))
    (hn : ∀ (j : ℕ), Cpaper γ * 2 / (2 : ℝ) ^ j ≤ 3 / 8 →
      ∀ (P : Finset V) (E₀ : Finset E),
        ((S P E₀).2.P.card : ℝ) ≤ 2 * (E₀.card : ℝ) / (2 : ℝ) ^ (2 * j))
    (T : Finset V → Finset E → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hrec : ∀ (P : Finset V) (E₀ : Finset E),
      T P E₀ ≤ (∑ i : Fin ((S P E₀).1), T ((S P E₀).2.kidV i) ((S P E₀).2.kidE i)) +
        c * (E₀.card : ℝ)) :
    ∀ (P : Finset V) (E₀ : Finset E), T P E₀ ≤ 2 * c * (E₀.card : ℝ) := by
  obtain ⟨j, hj⟩ := exists_phase (Cpaper γ)
  exact cost_linear_of_nodes S hstr hleaf hγ1 hε hdisp hj (hn j hj) T c hc hrec

/-- **The root's `hn`, produced by the phases.**  `BoruvkaHalving.compCount_le_real_of_empty` at
`k = 2j`: after `2j` phases from the empty forest, with no isolated vertices, the component count is
at most `2|E|/2^{2j}`.  This is the one place the recursion's aspect-ratio hypothesis is *derived*
rather than assumed — and it is exactly what the paper's "run `j` double-phases, then recurse" gives
the root instance when `E₀` is all of `E`. -/
theorem hn_root_of_phases {K : ℕ} (F A : ℕ → Finset E) {j : ℕ} (hF0 : F 0 = ∅)
    (hstep : ∀ i, F (i + 1) = F i ∪ A i)
    (hph : ∀ i, i < K → BorPhase G (F i) (A i))
    (hcover : ∀ i, i < K → ∀ C ∈ Finset.univ.image (comp G (F i)),
      ∃ e ∈ A i, comp G (F i) (G.src e) = C ∨ comp G (F i) (G.dst e) = C)
    (hK : 2 * j ≤ K) (hno : ∀ v : V, 1 ≤ degV G v) :
    (compCount G (F (2 * j)) : ℝ) ≤ 2 * (Fintype.card E : ℝ) / (2 : ℝ) ^ (2 * j) :=
  compCount_le_real_of_empty K F A (2 * j) hF0 hstep hph hcover hK hno

/-- **The same, in the instance's own edge count.**  `hn` is stated against `|E₀|`, not `|E|`:
with the global invariant `|V| ≤ 2|E₀|` (the no-isolated-vertices bound at the root instance, which
is `Strategy.hnm_at` at `E₀ = univ`), `compCount_le_real` at `m := |E₀|` gives exactly the shape
`|P_root| ≤ 2|E₀|/2^{2j}` that `cost_linear_of_contraction` asks of the instance it is queried at. -/
theorem hn_root_of_phases_le {K : ℕ} (F A : ℕ → Finset E) {j : ℕ} (hF0 : F 0 = ∅)
    (hstep : ∀ i, F (i + 1) = F i ∪ A i)
    (hph : ∀ i, i < K → BorPhase G (F i) (A i))
    (hcover : ∀ i, i < K → ∀ C ∈ Finset.univ.image (comp G (F i)),
      ∃ e ∈ A i, comp G (F i) (G.src e) = C ∨ comp G (F i) (G.dst e) = C)
    (hK : 2 * j ≤ K) {E₀ : Finset E} (h0 : Fintype.card V ≤ 2 * E₀.card) :
    (compCount G (F (2 * j)) : ℝ) ≤ 2 * (E₀.card : ℝ) / (2 : ℝ) ^ (2 * j) := by
  have hforest0 : IsForest G (F 0) := by rw [hF0]; exact IsForest.empty
  have hcomp0 : compCount G (F 0) ≤ 2 * E₀.card := by
    rw [hF0, compCount_empty]; exact h0
  exact compCount_le_real K F A E₀.card (2 * j) hforest0 hstep hph hcover hK hcomp0

/-- **The cost recursion with `hn` instantiated per call.**  `cost_linear_of_nodes` assumed the
post-phase vertex bound `|P| ≤ 2|E₀|/2^{2j}` at *every* instance.  Here it is asked only at the
instance the caller actually queries, and each call hands its children contracted instances —
`|kidV i| ≤ 2|kidE i|/2^{2j}`, the paper's "the child is what `j` double-phases leave behind", which
`CallOut.kidV_card` supplies for the vertex quartering.  Then the cost recursion is linear on every
instance that satisfies the bound — the descendants never need it re-assumed.  (At a root that is
all of `E`, the instance's own bound is `hn_root_of_phases`.) -/
theorem cost_linear_of_contraction (S : Strategy G) (hS : Strategy.Wf S) (hstr : Strategy.Strict S)
    (hleaf : Strategy.Leaf S) {C ε : ℝ} {j : ℕ} (hC : 0 ≤ C) (hε : ε ≤ 1 / 8)
    (hj : C * 2 / (2 : ℝ) ^ j ≤ 3 / 8)
    (hdisp : ∀ (P : Finset V) (E₀ : Finset E),
      ((∑ i, ((S P E₀).2.kidE i).card : ℕ) : ℝ) ≤
        ε * (E₀.card : ℝ) + C * Real.sqrt ((E₀.card : ℝ) * ((S P E₀).2.P.card : ℝ)))
    (hcontract : ∀ (P : Finset V) (E₀ : Finset E) (i : Fin ((S P E₀).1)),
      (((S P E₀).2.kidV i).card : ℝ) ≤
        2 * (((S P E₀).2.kidE i).card : ℝ) / (2 : ℝ) ^ (2 * j))
    (T : Finset V → Finset E → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hrec : ∀ (P : Finset V) (E₀ : Finset E),
      T P E₀ ≤ (∑ i : Fin ((S P E₀).1), T ((S P E₀).2.kidV i) ((S P E₀).2.kidE i)) +
        c * (E₀.card : ℝ)) :
    ∀ (P : Finset V) (E₀ : Finset E),
      ((S P E₀).2.P.card : ℝ) ≤ 2 * (E₀.card : ℝ) / (2 : ℝ) ^ (2 * j) →
      T P E₀ ≤ 2 * c * (E₀.card : ℝ) := by
  suffices H : ∀ m : ℕ, ∀ (P : Finset V) (E₀ : Finset E), E₀.card = m →
      ((S P E₀).2.P.card : ℝ) ≤ 2 * (E₀.card : ℝ) / (2 : ℝ) ^ (2 * j) →
      T P E₀ ≤ 2 * c * (E₀.card : ℝ) from fun P E₀ h => H E₀.card P E₀ rfl h
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro P E₀ hm hn
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
        have hchild : (S ((S P E₀).2.kidV i) ((S P E₀).2.kidE i)).2.P =
            (S P E₀).2.kidV i := (hS ((S P E₀).2.kidV i) ((S P E₀).2.kidE i)).1
        have hni : ((S ((S P E₀).2.kidV i) ((S P E₀).2.kidE i)).2.P.card : ℝ) ≤
            2 * (((S P E₀).2.kidE i).card : ℝ) / (2 : ℝ) ^ (2 * j) := by
          rw [hchild]
          exact hcontract P E₀ i
        exact ih _ (hkid i) _ _ rfl hni
      have hcast_sum : (∑ i : Fin ((S P E₀).1), (((S P E₀).2.kidE i).card : ℝ)) =
          ((∑ i : Fin ((S P E₀).1), ((S P E₀).2.kidE i).card : ℕ) : ℝ) :=
        (Nat.cast_sum Finset.univ (fun i => ((S P E₀).2.kidE i).card)).symm
      have hsum_eq : (∑ i : Fin ((S P E₀).1), 2 * c * (((S P E₀).2.kidE i).card : ℝ)) =
          2 * c * (∑ i : Fin ((S P E₀).1), (((S P E₀).2.kidE i).card : ℝ)) := by
        rw [Finset.mul_sum]
      have hshrinkE := children_shrink S P E₀ hC hε hj (hdisp P E₀) hn
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

/-- **The same, with the phase count chosen by the constants.**  `Bookkeeping.exists_phase` supplies
a `j` with `Cpaper γ · 2/2^j ≤ 3/8`; the children's contraction and the queried instance's aspect
ratio are asked at that `j` only, so both are quantified over the choices `j` the constants admit. -/
theorem cost_linear_of_contraction_exists (S : Strategy G) (hS : Strategy.Wf S)
    (hstr : Strategy.Strict S) (hleaf : Strategy.Leaf S) {γ ε : ℝ} (hγ1 : 1 ≤ γ)
    (hε : ε ≤ 1 / 8)
    (hdisp : ∀ (P : Finset V) (E₀ : Finset E),
      ((∑ i, ((S P E₀).2.kidE i).card : ℕ) : ℝ) ≤
        ε * (E₀.card : ℝ) + Cpaper γ * Real.sqrt ((E₀.card : ℝ) * ((S P E₀).2.P.card : ℝ)))
    (hcontract : ∀ (j : ℕ), Cpaper γ * 2 / (2 : ℝ) ^ j ≤ 3 / 8 →
      ∀ (P : Finset V) (E₀ : Finset E) (i : Fin ((S P E₀).1)),
        (((S P E₀).2.kidV i).card : ℝ) ≤
          2 * (((S P E₀).2.kidE i).card : ℝ) / (2 : ℝ) ^ (2 * j))
    (T : Finset V → Finset E → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hrec : ∀ (P : Finset V) (E₀ : Finset E),
      T P E₀ ≤ (∑ i : Fin ((S P E₀).1), T ((S P E₀).2.kidV i) ((S P E₀).2.kidE i)) +
        c * (E₀.card : ℝ)) :
    ∃ j : ℕ, Cpaper γ * 2 / (2 : ℝ) ^ j ≤ 3 / 8 ∧
      ∀ (P : Finset V) (E₀ : Finset E),
        ((S P E₀).2.P.card : ℝ) ≤ 2 * (E₀.card : ℝ) / (2 : ℝ) ^ (2 * j) →
        T P E₀ ≤ 2 * c * (E₀.card : ℝ) := by
  obtain ⟨j, hj⟩ := exists_phase (Cpaper γ)
  exact ⟨j, hj, cost_linear_of_contraction S hS hstr hleaf (Cpaper_nonneg hγ1) hε hj hdisp
    (hcontract j hj) T c hc hrec⟩

/-- **`tOf`/`htd` cannot be indexed by the instance alone.**  If one global parameter map satisfied
`htd` for *every* root's level chain, then a nonempty instance `E₀` with any child `X` would force
`tOf X = γ·8` (as `X` sits at depth `1` of `E₀`'s chain) and `tOf X = γ·1` (as `X` is the depth-`0`
instance of its own chain), so `γ = 0`.  Hence the paper's `t_c = γ(d−c+1)³` is per-call
(level-stamped) bookkeeping: the round-data interface keeps it as data, and the display enters per
call (`display_of_roundData_nodes`), not as a property of a strategy-wide function. -/
theorem htd_all_roots_impossible (tOf : Finset V → Finset E → ℕ) (S : Strategy G)
    (hS : Strategy.Wf S) {γ : ℝ} (hγ : γ ≠ 0)
    {P : Finset V} {E₀ : Finset E} (hne : E₀.Nonempty) (i : Fin ((S P E₀).1))
    (htd : ∀ (Q : Finset V) (F₀ : Finset E) (d : ℕ), d ≤ F₀.card →
      ∀ a ∈ (Level.chain Q F₀ S hS d).insts,
        (tOf a.1 a.2 : ℝ) = γ * ((d : ℝ) + 1) ^ 3) :
    False := by
  set X : Inst V E := ((S P E₀).2.kidV i, (S P E₀).2.kidE i) with hX
  have h1 : X ∈ (Level.chain P E₀ S hS 1).insts := by
    show X ∈ (Level.allChildren (Level.root P E₀)
      (fun a => S a.val.1 a.val.2) (fun a => (hS a.val.1 a.val.2).2)).insts
    exact Finset.mem_biUnion.mpr
      ⟨⟨(P, E₀), Finset.mem_singleton_self _⟩, Finset.mem_attach _ _,
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hcard : 1 ≤ E₀.card := Finset.card_pos.mpr hne
  have hA : (tOf X.1 X.2 : ℝ) = γ * ((1 : ℝ) + 1) ^ 3 := htd P E₀ 1 hcard X h1
  have h2 : X ∈ (Level.chain X.1 X.2 S hS 0).insts := by
    show X ∈ (Level.root X.1 X.2).insts
    exact Finset.mem_singleton_self _
  have hB : (tOf X.1 X.2 : ℝ) = γ * ((0 : ℝ) + 1) ^ 3 := htd X.1 X.2 0 (Nat.zero_le _) X h2
  have heq : γ * ((1 : ℝ) + 1) ^ 3 = γ * ((0 : ℝ) + 1) ^ 3 := hA.symm.trans hB
  norm_num at heq
  exact hγ (by linarith)

end Strategy

namespace Strategy

/-- **The `n ≤ 2m` invariant at an instance.**  If every vertex of an instance is an end of one of
its edges — "no isolated vertices", the invariant the phase contraction maintains — then the
instance's vertex count is at most twice its edge count (`card_le_two_mul_card_of_subset_ends`).
`ofScan_hnm`/`ofBatches_hnm` discharge the hypothesis for the strategies the procedure constructs;
this theorem states the invariant's conclusion at every instance the strategy is asked about. -/
theorem hnm_at (S : Strategy G)
    (huse : ∀ (P' : Finset V) (E₀' : Finset E) (v : V), v ∈ (S P' E₀').2.P →
      ∃ e ∈ (S P' E₀').2.E₀, G.src e = v ∨ G.dst e = v)
    (P' : Finset V) (E₀' : Finset E) :
    ((S P' E₀').2.P.card : ℝ) ≤ 2 * ((S P' E₀').2.E₀.card : ℝ) := by
  have h := card_le_two_mul_card_of_subset_ends (G := G) (P := (S P' E₀').2.P)
    (E₀ := (S P' E₀').2.E₀) (fun v hv => huse P' E₀' v hv)
  exact_mod_cast h

end Strategy

namespace LevelChain

variable (P : Finset V) (E₀ : Finset E) (S : Strategy G) (hS : Strategy.Wf S)

/-- **The paper's vertex bound at every level: `n_d ≤ 2m/2^d`.**  The edge count of a depth-`d`
instance is `2^d` times smaller (`instance_card_mul_pow_le`, from the per-node halving
`2·Σ|Eᵢ| ≤ |E₀|`), and `n ≤ 2m` at every instance (`Strategy.hnm_at`) supplies the factor `2`.  This
is the per-call vertex budget that §4's recursion consumes (`certificate_of_display`'s `hn`), with
both of its halves — the phase halving and the no-isolated-vertices invariant — used. -/
theorem card_le_two_mul_div_pow
    (hshrink : ∀ (P' : Finset V) (E₀' : Finset E),
      2 * (∑ i, ((S P' E₀').2.kidE i).card) ≤ E₀'.card)
    (huse : ∀ (P' : Finset V) (E₀' : Finset E) (v : V), v ∈ (S P' E₀').2.P →
      ∃ e ∈ (S P' E₀').2.E₀, G.src e = v ∨ G.dst e = v)
    (d : ℕ) {b : Inst V E} (hb : b ∈ (Level.chain P E₀ S hS d).insts) :
    (b.1.card : ℝ) ≤ 2 * (E₀.card : ℝ) / (2 : ℝ) ^ d := by
  obtain ⟨hP, hE⟩ := hS b.1 b.2
  have h1 : (b.1.card : ℝ) ≤ 2 * (b.2.card : ℝ) := by
    have h := Strategy.hnm_at (G := G) S huse b.1 b.2
    rw [hP, hE] at h
    exact h
  have h2 : ((b.2.card : ℝ)) * (2 : ℝ) ^ d ≤ (E₀.card : ℝ) := by
    have h := instance_card_mul_pow_le P E₀ S hS hshrink d hb
    exact_mod_cast h
  have hpow : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  have h3 : (b.2.card : ℝ) ≤ (E₀.card : ℝ) / (2 : ℝ) ^ d := (le_div_iff₀ hpow).mpr h2
  calc (b.1.card : ℝ) ≤ 2 * (b.2.card : ℝ) := h1
    _ ≤ 2 * ((E₀.card : ℝ) / (2 : ℝ) ^ d) := by linarith
    _ = 2 * (E₀.card : ℝ) / (2 : ℝ) ^ d := by ring

end LevelChain

end DLMST
