import DLMST.History
import DLMST.Selection
import DLMST.VectorMaxima

/-!
# §3.4, Lemma 3.10: how many histories does a call have?

Lemma 3.11 (`History.lean`) needs one number: `log |Hs|`, the log of the number of histories the
schedule must be good for.  Lemma 3.10 of the paper supplies it, and this file machine-checks the
count.

A history (Definition 3.8) is a triple of sequences indexed by the `t²` rounds: spokes `σ_i`
(functions `V → E`), forests `F_i` (edge sets) and true preference vectors `a_i`.  The paper counts
each sequence separately and multiplies:

* **spokes**: in round `i` and at vertex `v`, the spoke `σ_i(v)` is one of `deg(v) + 1` values (an
  incident edge, or "no spoke").  `card_spokeSeqs_le` proves the `(∏_v (deg v + 1))^{t²}` bound.
  Our model represents "no spoke" as `¬ incident G v (σ v)` rather than a bottom element, so we
  count the legal spoke functions as "incident, or a fixed default edge `e₀`" (`SpokeOK`); this is
  the paper's `{⊥} ∪ δ(v)` with `⊥` renamed.
* **forests**: a forest in an `m`-edge graph has at most `n - 1` edges, so the number of possible
  `F_i` is at most the number of edge sets of size `≤ n - 1`, which is `∑_{k ≤ n-1} C(m,k) ≤
  C(m+n-1, n-1)` (`card_forestSeqs_le`, via the hockey-stick inequality `sum_range_choose_le`).
* **preferences**: the paper counts `C(m+2n-1, m)^{t²}` preference vectors, via Fredman's bound on
  the `m` sets `S_e` in the `2n`-element ground set of spokes and forest edges.  In our model a
  preference vector is *determined* by the spokes and the forest (Definition 3.8's `Consistent` is
  an equation, and `actOf` is a function), so no third factor is needed for a fixed graph `G`:
  `card_histories_le` multiplies only the first two factors.  The third factor is still available
  for audits of the paper's uniform-over-inputs claim; it is `maxima_vectors_card` from
  `VectorMaxima.lean`, restated as `pref_vectors_le` below.

The analytic part is the paper's Fact 2.1, `log C(m+n,n) ≤ 2√(mn)`.  We prove the same statement
with constant `4` (`log_choose_le`), because the paper's sharper constant uses `log(1+x) ≤ √x`,
whose formal proof needs an integral comparison; we use the elementary `log(1+x) ≤ 2√x`
(`Selection.log_one_add_le_two_sqrt`, already in the project), which loses a factor `2` but keeps
the `√(mn)`.  The assembly `log_card_histories_le` therefore reads
`log |H| ≤ t²(2√(2mn) + 4√(m(n-1)))`, the paper's `O(t²√(mn))` with a slightly larger constant.
The spoke factor's summation is §3.2's `test_budget` applied to `deg G`, and the handshake inequality
`∑_v deg_G(v) ≤ 2m` comes from `Selection.sum_degree` (loops are counted twice there, once here).

The paper's third factor is justified by reading the preference as a maximum over `S_e` (spokes plus
the `u`–`v` path in the round's forest); that reduction is `PrefTrail.prefFind_iff_trail_weight`
(`prefFind` ⟺ every edge of the unique reduced `F`-trail is at most `p(e)`), which gives
`pref_vectors_le` its intended content.  The count itself does not need it: for a fixed `G` the
preference is an equation in (spokes, forest), and that is the injection used here.
-/

namespace DLMST

open Classical

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] {G : WGraph V E}
  {t : ℕ}

/-! ## Analytic input: the binomial-coefficient bound -/

/-- `1/√j ≤ 2(√j - √(j-1))` for `j ≥ 1`: the telescoping step for the harmonic-type bound below.
Both sides are nonnegative; squaring reduces the claim to `4j(j-1) ≤ (2j-1)²`. -/
lemma one_div_sqrt_le_two_mul_sub {j : ℕ} (hj : 1 ≤ j) :
    1 / Real.sqrt (j : ℝ) ≤ 2 * (Real.sqrt (j : ℝ) - Real.sqrt ((j - 1 : ℕ) : ℝ)) := by
  have hj1 : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
    rw [Nat.cast_sub hj]
    norm_num
  set s := Real.sqrt (j : ℝ) with hs
  set u := Real.sqrt ((j - 1 : ℕ) : ℝ) with hu
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = (j : ℝ) := Real.sq_sqrt (by positivity)
  have hu2 : u ^ 2 = ((j - 1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  have hsne : (0 : ℝ) < s := Real.sqrt_pos.mpr (by exact_mod_cast hj)
  have hprod : 2 * s * u ≤ 2 * (j : ℝ) - 1 := by
    have hsq : (2 * s * u) ^ 2 ≤ (2 * (j : ℝ) - 1) ^ 2 := by nlinarith
    have hpos : 0 ≤ 2 * s * u := by positivity
    have hrhs : 0 ≤ 2 * (j : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
      linarith
    calc 2 * s * u = Real.sqrt ((2 * s * u) ^ 2) := (Real.sqrt_sq hpos).symm
      _ ≤ Real.sqrt ((2 * (j : ℝ) - 1) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 2 * (j : ℝ) - 1 := Real.sqrt_sq hrhs
  rw [div_le_iff₀ hsne]
  nlinarith

/-- `∑_{i<n} 1/√(i+1) ≤ 2√n`, by telescoping with `one_div_sqrt_le_two_mul_sub`. -/
lemma sum_range_one_div_sqrt_succ_le (n : ℕ) :
    ∑ i ∈ Finset.range n, 1 / Real.sqrt ((i + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
  have htel : ∑ i ∈ Finset.range n,
      2 * (Real.sqrt ((i + 1 : ℕ) : ℝ) - Real.sqrt ((i : ℕ) : ℝ)) = 2 * Real.sqrt (n : ℝ) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have hterm : ∀ i ∈ Finset.range n,
      1 / Real.sqrt ((i + 1 : ℕ) : ℝ) ≤
        2 * (Real.sqrt ((i + 1 : ℕ) : ℝ) - Real.sqrt ((i : ℕ) : ℝ)) := by
    intro i _
    exact one_div_sqrt_le_two_mul_sub (Nat.succ_le_succ (Nat.zero_le i))
  exact le_trans (Finset.sum_le_sum hterm) (le_of_eq htel)

/-- **The product formula for a binomial coefficient**: `C(a+b, b) = ∏_{i<b} (a+i+1)/(i+1)`, the
values of `(1 + a/i)` for `i = 1..b`. -/
lemma choose_eq_prod_range (a b : ℕ) :
    ((a + b).choose b : ℝ) = ∏ i ∈ Finset.range b, ((a + i + 1 : ℕ) : ℝ) / ((i + 1 : ℕ) : ℝ) := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hidx : a + (b + 1) = a + b + 1 := rfl
    rw [hidx]
    rw [Finset.prod_range_succ, ← ih]
    -- `(b+1) C(a+b+1, b+1) = (a+b+1) C(a+b, b)`
    have h := Nat.add_one_mul_choose_eq (a + b) b
    have h' : (((a + b + 1) * (a + b).choose b : ℕ) : ℝ) =
        ((((a + b + 1).choose (b + 1)) * (b + 1) : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h' ⊢
    field_simp
    linarith

/-- **Fact 2.1 of the paper, with constant `4`**: `log C(a+b, b) ≤ 4√(ab)`.  The paper's `≤ 2√(mn)`
follows from `log(1+x) ≤ √x`; with `log(1+x) ≤ 2√x` the sum of the `b` terms `2√(a/i)` gains a
factor `2`. -/
lemma log_choose_le (a b : ℕ) :
    Real.log ((a + b).choose b : ℝ) ≤ 4 * Real.sqrt ((a : ℝ) * (b : ℝ)) := by
  rw [choose_eq_prod_range]
  have hne : ∀ i ∈ Finset.range b, ((a + i + 1 : ℕ) : ℝ) / ((i + 1 : ℕ) : ℝ) ≠ 0 := by
    intro i _
    positivity
  rw [Real.log_prod hne]
  have hterm : ∀ i ∈ Finset.range b,
      Real.log (((a + i + 1 : ℕ) : ℝ) / ((i + 1 : ℕ) : ℝ)) ≤
        2 * (Real.sqrt (a : ℝ) * (1 / Real.sqrt ((i + 1 : ℕ) : ℝ))) := by
    intro i _
    have hpos : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
    have h1 : ((a + i + 1 : ℕ) : ℝ) / ((i + 1 : ℕ) : ℝ) =
        1 + (a : ℝ) / ((i + 1 : ℕ) : ℝ) := by
      push_cast
      field_simp
      ring
    have h2 : Real.sqrt ((a : ℝ) / ((i + 1 : ℕ) : ℝ)) =
        Real.sqrt (a : ℝ) * (1 / Real.sqrt ((i + 1 : ℕ) : ℝ)) := by
      rw [Real.sqrt_div (by positivity), mul_one_div]
    rw [h1, ← h2]
    exact log_one_add_le_two_sqrt (x := (a : ℝ) / ((i + 1 : ℕ) : ℝ)) (by positivity)
  calc ∑ i ∈ Finset.range b, Real.log (((a + i + 1 : ℕ) : ℝ) / ((i + 1 : ℕ) : ℝ))
      ≤ ∑ i ∈ Finset.range b, 2 * (Real.sqrt (a : ℝ) * (1 / Real.sqrt ((i + 1 : ℕ) : ℝ))) :=
        Finset.sum_le_sum hterm
    _ = 2 * Real.sqrt (a : ℝ) * ∑ i ∈ Finset.range b, 1 / Real.sqrt ((i + 1 : ℕ) : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ 2 * Real.sqrt (a : ℝ) * (2 * Real.sqrt (b : ℝ)) := by
        have h := sum_range_one_div_sqrt_succ_le b
        exact mul_le_mul_of_nonneg_left h (by positivity)
    _ = 4 * Real.sqrt ((a : ℝ) * (b : ℝ)) := by
        rw [Real.sqrt_mul (by positivity)]
        ring

/-! ## The degree of a vertex, and the handshake inequality -/

/-- `deg G v`: the number of edges incident to `v`. -/
noncomputable def degV (G : WGraph V E) (v : V) : ℕ :=
  (Finset.univ.filter (incident G v)).card

/-- **`∑_v deg_G(v) ≤ 2m`**: an edge is incident to at most its two endpoints.  (For a loop the two
copies coincide, so this is an inequality, not the paper's exact `2m`; `Selection.sum_degree` is the
exact count with multiplicity.) -/
lemma sum_degV_le_two_mul : ∑ v : V, degV G v ≤ 2 * Fintype.card E := by
  have hle : ∑ v : V, degV G v ≤
      ∑ v : V, ((Finset.univ.filter fun e => G.src e = v).card +
        (Finset.univ.filter fun e => G.dst e = v).card) := by
    refine Finset.sum_le_sum fun v _ => ?_
    simp only [degV]
    calc (Finset.univ.filter (incident G v)).card
        ≤ ((Finset.univ.filter fun e => G.src e = v) ∪
            (Finset.univ.filter fun e => G.dst e = v)).card :=
          Finset.card_le_card (fun e he => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at he ⊢
            exact he)
      _ ≤ _ + _ := Finset.card_union_le _ _
  calc ∑ v : V, degV G v
      ≤ ∑ v : V, ((Finset.univ.filter fun e => G.src e = v).card +
          (Finset.univ.filter fun e => G.dst e = v).card) := hle
    _ = 2 * (Finset.univ : Finset E).card := sum_degree G.src G.dst Finset.univ
    _ = 2 * Fintype.card E := by rw [Finset.card_univ]

/-- **`∑_v log(deg v + 1) ≤ 2√(2mn)`**: §3.2's summed test budget (`Selection.test_budget`) applied
to the degree function, with the handshake inequality.  This is the paper's
`t² ∑_v log(deg v + 1) ≤ t²√(2mn)`, with the constant `2` of `log(1+x) ≤ 2√x`. -/
lemma sum_log_degV_le :
    ∑ v : V, Real.log ((degV G v : ℝ) + 1) ≤
      2 * Real.sqrt (2 * (Fintype.card E : ℝ) * (Fintype.card V : ℝ)) := by
  have htest := test_budget (fun v => degV G v) 1
  simp only [Nat.cast_one, one_mul, mul_one] at htest
  have hdeg : ∑ v : V, (degV G v : ℝ) ≤ 2 * (Fintype.card E : ℝ) := by
    have := sum_degV_le_two_mul (G := G)
    exact_mod_cast this
  have hcs : Real.sqrt ((Fintype.card V : ℝ) * ∑ v : V, (degV G v : ℝ)) ≤
      Real.sqrt (2 * (Fintype.card E : ℝ) * (Fintype.card V : ℝ)) := by
    refine Real.sqrt_le_sqrt ?_
    nlinarith [hdeg, Nat.cast_nonneg (α := ℝ) (Fintype.card V)]
  calc ∑ v : V, Real.log ((degV G v : ℝ) + 1)
      ≤ 2 * Real.sqrt ((Fintype.card V : ℝ) * ∑ v : V, (degV G v : ℝ)) := htest
    _ ≤ 2 * Real.sqrt (2 * (Fintype.card E : ℝ) * (Fintype.card V : ℝ)) := by linarith

/-! ## Counting the spoke and forest sequences -/

/-- A **legal spoke vector** in the sense of Lemma 3.10: at each vertex, an incident edge or the
fixed default edge `e₀` (the paper's `⊥`, "no spoke"). -/
def SpokeOK (e₀ : E) (σ : V → E) : Prop := ∀ v, σ v = e₀ ∨ incident G v (σ v)

/-- **Spoke count**: at most `∏_v (deg v + 1)` legal spoke vectors. -/
lemma card_spokeOK_le (e₀ : E) :
    Fintype.card {σ : V → E // SpokeOK (G := G) e₀ σ} ≤ ∏ v : V, (degV G v + 1) := by
  classical
  have hmem : ∀ (σ : V → E), SpokeOK (G := G) e₀ σ →
      ∀ v : V, σ v ∈ insert e₀ (Finset.univ.filter (incident G v)) := by
    intro σ hσ v
    rcases hσ v with h | h
    · rw [h]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  let f : {σ : V → E // SpokeOK (G := G) e₀ σ} →
      (∀ v : V, ↥(insert e₀ (Finset.univ.filter (incident G v)))) :=
    fun σ v => ⟨σ.1 v, hmem σ.1 σ.2 v⟩
  have hinj : Function.Injective f := by
    intro σ₁ σ₂ h
    exact Subtype.ext (funext fun v => congrArg (fun g => (g v).1) h)
  calc Fintype.card {σ : V → E // SpokeOK (G := G) e₀ σ}
      ≤ Fintype.card (∀ v : V, ↥(insert e₀ (Finset.univ.filter (incident G v)))) :=
        Fintype.card_le_of_injective f hinj
    _ = ∏ v : V, (insert e₀ (Finset.univ.filter (incident G v))).card := by
        rw [Fintype.card_pi]
        exact Finset.prod_congr rfl fun v _ => Fintype.card_coe _
    _ ≤ ∏ v : V, (degV G v + 1) :=
        Finset.prod_le_prod fun v _ => by
          calc (insert e₀ (Finset.univ.filter (incident G v))).card
              ≤ (Finset.univ.filter (incident G v)).card + 1 := Finset.card_insert_le _ _
            _ = degV G v + 1 := rfl

/-- Round sequences behave multiplicatively: the functions `ι → α` all of whose values satisfy `P`
are exactly the `ι`-indexed families of elements satisfying `P`. -/
lemma card_filter_forall {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι] (P : α → Prop) :
    (Finset.univ.filter (fun f : ι → α => ∀ i, P (f i))).card =
      (Fintype.card {a : α // P a}) ^ Fintype.card ι := by
  classical
  rw [← Fintype.card_coe]
  have e : ↥(Finset.univ.filter (fun f : ι → α => ∀ i, P (f i))) ≃ (∀ i : ι, {a : α // P a}) :=
  { toFun := fun f i => ⟨f.1 i, (Finset.mem_filter.mp f.2).2 i⟩
    invFun := fun g =>
      ⟨fun i => (g i).1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => (g i).2⟩⟩
    left_inv := fun f => Subtype.ext rfl
    right_inv := fun g => funext fun i => Subtype.ext rfl }
  rw [Fintype.card_congr e, Fintype.card_pi, Finset.prod_const, Finset.card_univ]

/-- **The spoke sequences of a call**: at most `(∏_v (deg v + 1))^{t²}`. -/
lemma card_spokeSeqs_le (e₀ : E) :
    (Finset.univ.filter (fun σ : Fin t × Fin t → V → E =>
      ∀ p, SpokeOK (G := G) e₀ (σ p))).card ≤
      (∏ v : V, (degV G v + 1)) ^ (t * t) := by
  rw [card_filter_forall (P := fun σ : V → E => SpokeOK (G := G) e₀ σ),
    show Fintype.card (Fin t × Fin t) = t * t from by simp [Fintype.card_prod]]
  exact Nat.pow_le_pow_left (card_spokeOK_le e₀) _

/-- Hockey stick: `∑_{k ≤ r} C(N,k) ≤ C(N+r, r)`. -/
lemma sum_range_choose_le (N r : ℕ) :
    ∑ k ∈ Finset.range (r + 1), Nat.choose N k ≤ Nat.choose (N + r) r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ,
      show N + (r + 1) = (N + r) + 1 from by omega]
    calc (∑ k ∈ Finset.range (r + 1), Nat.choose N k) + Nat.choose N (r + 1)
        ≤ Nat.choose (N + r) r + Nat.choose (N + r) (r + 1) :=
          Nat.add_le_add ih (Nat.choose_le_choose (r + 1) (Nat.le_add_right N r))
      _ = Nat.choose (N + r + 1) (r + 1) := by
          rw [Nat.choose_succ_succ]

/-- **Forest count**: an `m`-edge graph has at most `C(m+n-1, n-1)` edge sets of size `≤ n-1`. -/
lemma card_finsets_le_choose (r : ℕ) :
    (Finset.univ.filter (fun F : Finset E => F.card ≤ r)).card ≤
      Nat.choose (Fintype.card E + r) r := by
  classical
  have hset : (Finset.univ.filter (fun F : Finset E => F.card ≤ r)) =
      (Finset.range (r + 1)).biUnion (fun k => (Finset.univ : Finset E).powersetCard k) := by
    ext F
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_powersetCard]
    constructor
    · intro h
      exact ⟨F.card, by omega, Finset.subset_univ _, rfl⟩
    · rintro ⟨k, hk, -, hcard⟩
      omega
  rw [hset]
  have hdisj : (↑(Finset.range (r + 1)) : Set ℕ).PairwiseDisjoint
      (fun k => (Finset.univ : Finset E).powersetCard k) := by
    intro k _ l _ hkl
    rw [Function.onFun, Finset.disjoint_left]
    intro F hF1 hF2
    rw [Finset.mem_powersetCard] at hF1 hF2
    exact hkl (hF1.2.symm.trans hF2.2)
  rw [Finset.card_biUnion hdisj]
  calc ∑ k ∈ Finset.range (r + 1), ((Finset.univ : Finset E).powersetCard k).card
      = ∑ k ∈ Finset.range (r + 1), Nat.choose (Fintype.card E) k := by
        exact Finset.sum_congr rfl fun k _ => by
          rw [Finset.card_powersetCard, Finset.card_univ]
    _ ≤ Nat.choose (Fintype.card E + r) r := sum_range_choose_le _ _

/-- **The forest sequences of a call**: at most `C(m+n-1, n-1)^{t²}`. -/
lemma card_forestSeqs_le (n : ℕ) :
    (Finset.univ.filter (fun F : Fin t × Fin t → Finset E => ∀ p, (F p).card ≤ n - 1)).card ≤
      (Nat.choose (Fintype.card E + (n - 1)) (n - 1)) ^ (t * t) := by
  classical
  -- each round independently picks an edge set of size `≤ n-1`
  have hinj : Function.Injective
      (fun F : {F : Fin t × Fin t → Finset E // ∀ p, (F p).card ≤ n - 1} =>
        fun p => (⟨F.1 p, F.2 p⟩ : {G : Finset E // G.card ≤ n - 1})) := by
    intro a b h
    apply Subtype.ext
    funext p
    exact congrArg (fun g => (g p).1) h
  have h1 : Fintype.card {F : Fin t × Fin t → Finset E // ∀ p, (F p).card ≤ n - 1} ≤
      (Fintype.card {G : Finset E // G.card ≤ n - 1}) ^ (t * t) := by
    refine (Fintype.card_le_of_injective _ hinj).trans (le_of_eq ?_)
    rw [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin]
  have h2 : Fintype.card {G : Finset E // G.card ≤ n - 1} ≤
      Nat.choose (Fintype.card E + (n - 1)) (n - 1) := by
    rw [Fintype.card_subtype]
    exact card_finsets_le_choose (n - 1)
  rw [← Fintype.card_subtype (fun F : Fin t × Fin t → Finset E => ∀ p, (F p).card ≤ n - 1)]
  exact h1.trans (Nat.pow_le_pow_left h2 _)

/-! ## The paper's third factor, for audits of the uniform-in-`G` count -/

/-- **Lemma 3.10's preference factor**: on a ground set of size `2n` (the `n` spokes and at most
`n - 1` forest edges, padded to `2n`), any family of maximiser vectors of `m` sets has at most
`C(2n+m-1, m)` members — `maxima_vector_determined` plus `Sym.card_sym_eq_choose`.  Reading a
preference vector off such a maximiser vector is the paper's `S_e` argument, not formalised (see the
file header). -/
theorem pref_vectors_le (m n : ℕ) (Se : Fin m → Finset (Fin (2 * n)))
    (r : Fin (2 * n) ≃ Fin (2 * n)) (C : Finset (Fin m → Fin (2 * n)))
    (hC : ∀ a ∈ C, ∀ i, a i ∈ Se i ∧ ∀ x ∈ Se i, r x ≤ r (a i)) :
    C.card ≤ Nat.choose (2 * n + m - 1) m := by
  classical
  have hinj : Function.Injective
      (fun a : {a : Fin m → Fin (2 * n) // a ∈ C} =>
        (⟨Multiset.map a.1 Finset.univ.val, by simp⟩ : Sym (Fin (2 * n)) m)) := by
    intro a b hab
    have hm : Multiset.map a.1 Finset.univ.val = Multiset.map b.1 Finset.univ.val :=
      congrArg Subtype.val hab
    apply Subtype.ext
    funext i
    exact maxima_vector_determined Se r a.1 b.1 (fun i => (hC b.1 b.2 i).1)
      (fun i x hx => (hC a.1 a.2 i).2 x hx) hm i
  have h : Fintype.card {a : Fin m → Fin (2 * n) // a ∈ C} ≤
      Fintype.card (Sym (Fin (2 * n)) m) :=
    Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_coe] at h
  calc C.card ≤ Fintype.card (Sym (Fin (2 * n)) m) := h
    _ = Nat.choose (2 * n + m - 1) m := by
        rw [Sym.card_sym_eq_choose, Fintype.card_fin]

/-! ## Lemma 3.10: the count of histories -/

/-- The **legal histories** of Lemma 3.10: consistent (Definition 3.8), with legal spokes
(`SpokeOK`, the paper's `σ(v) ∈ {⊥} ∪ δ(v)`) and forests of at most `n - 1` edges. -/
def Legal (e₀ : E) (n : ℕ) (H : History V E t) : Prop :=
  H.Consistent (G := G) ∧ (∀ b i, SpokeOK (G := G) e₀ (H.spoke b i)) ∧
    ∀ b i, (H.forest b i).card ≤ n - 1

/-- **Lemma 3.10, the count.**  A consistent history is determined by its spoke and forest sequences
(the preference vector is an equation, not free data), so a family of legal histories injects into
"spoke sequences × forest sequences", and the two factors are bounded separately. -/
theorem card_histories_le (e₀ : E) (n : ℕ) (Hs : Finset (History V E t))
    (hleg : ∀ H ∈ Hs, Legal (G := G) e₀ n H) :
    Hs.card ≤ (∏ v : V, (degV G v + 1)) ^ (t * t) *
      (Nat.choose (Fintype.card E + (n - 1)) (n - 1)) ^ (t * t) := by
  classical
  set SP := Finset.univ.filter (fun σ : Fin t × Fin t → V → E =>
    ∀ p, SpokeOK (G := G) e₀ (σ p)) with hSP
  set FO := Finset.univ.filter (fun F : Fin t × Fin t → Finset E =>
    ∀ p, (F p).card ≤ n - 1) with hFO
  let g : History V E t → (Fin t × Fin t → V → E) × (Fin t × Fin t → Finset E) :=
    fun H => (fun p => H.spoke p.1 p.2, fun p => H.forest p.1 p.2)
  have hmaps : Set.MapsTo g ↑Hs ↑(SP.product FO) := by
    intro H hH
    obtain ⟨hcons, hsp, hfo⟩ := hleg H hH
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · rw [hSP, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, fun p => hsp p.1 p.2⟩
    · rw [hFO, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, fun p => hfo p.1 p.2⟩
  have hinj : Set.InjOn g ↑Hs := by
    intro H₁ h₁ H₂ h₂ heq
    obtain ⟨s1, f1, p1⟩ := H₁
    obtain ⟨s2, f2, p2⟩ := H₂
    have hsp : s1 = s2 := by
      have h := congrArg Prod.fst heq
      funext b i
      exact congrFun h (b, i)
    have hfo : f1 = f2 := by
      have h := congrArg Prod.snd heq
      funext b i
      exact congrFun h (b, i)
    have hpref : p1 = p2 := by
      funext e b i
      have h1 := (hleg ⟨s1, f1, p1⟩ h₁).1 e b i
      have h2 := (hleg ⟨s2, f2, p2⟩ h₂).1 e b i
      rw [hsp] at h1
      rw [hfo] at h1
      exact h1.trans h2.symm
    rw [hsp, hfo, hpref]
  have h1 := Finset.card_le_card_of_injOn g hmaps hinj
  have h2 : (SP.product FO).card = SP.card * FO.card := Finset.card_product SP FO
  rw [h2] at h1
  exact h1.trans (Nat.mul_le_mul (card_spokeSeqs_le e₀) (card_forestSeqs_le n))

/-- **Lemma 3.10, in logarithmic form.**  For a family of legal histories of a graph with `m` edges
and `n` vertices, `log |H| ≤ t²(2√(2mn) + 4√(m(n-1)))` — the paper's `O(t²√(mn))`, with the
constant of `log_choose_le` and of `log_one_add_le_two_sqrt`. -/
theorem log_card_histories_le (e₀ : E) (Hs : Finset (History V E t))
    (hleg : ∀ H ∈ Hs, Legal (G := G) e₀ (Fintype.card V) H) (hpos : 0 < Hs.card) :
    Real.log (Hs.card : ℝ) ≤ (t : ℝ) ^ 2 *
      (2 * Real.sqrt (2 * (Fintype.card E : ℝ) * (Fintype.card V : ℝ)) +
        4 * Real.sqrt ((Fintype.card E : ℝ) * (((Fintype.card V - 1 : ℕ)) : ℝ))) := by
  classical
  have hpt : (0 : ℝ) < ((∏ v : V, (degV G v + 1) : ℕ) : ℝ) := by
    rw [Nat.cast_prod]
    exact Finset.prod_pos fun v _ => by positivity
  have hct : (0 : ℝ) <
      (Nat.choose (Fintype.card E + (Fintype.card V - 1)) (Fintype.card V - 1) : ℝ) := by
    have := Nat.choose_pos (show Fintype.card V - 1 ≤ Fintype.card E + (Fintype.card V - 1)
      from Nat.le_add_left _ _)
    exact_mod_cast this
  have hlogP : Real.log (((∏ v : V, (degV G v + 1) : ℕ) : ℝ)) =
      ∑ v : V, Real.log ((degV G v : ℝ) + 1) := by
    rw [Nat.cast_prod, Real.log_prod (fun v _ => by positivity)]
    exact Finset.sum_congr rfl fun v _ => by push_cast; ring
  have hcard := card_histories_le (t := t) (G := G) e₀ (Fintype.card V) Hs hleg
  have hcardR : (Hs.card : ℝ) ≤
      ((∏ v : V, (degV G v + 1) : ℕ) : ℝ) ^ (t * t) *
        ((Nat.choose (Fintype.card E + (Fintype.card V - 1))
          (Fintype.card V - 1) : ℕ) : ℝ) ^ (t * t) := by
    exact_mod_cast hcard
  have hlog := Real.log_le_log (by exact_mod_cast hpos) hcardR
  have hp1 : (0 : ℝ) < ((∏ v : V, (degV G v + 1) : ℕ) : ℝ) ^ (t * t) := pow_pos hpt _
  have hc1 : (0 : ℝ) < ((Nat.choose (Fintype.card E + (Fintype.card V - 1))
      (Fintype.card V - 1) : ℕ) : ℝ) ^ (t * t) := pow_pos hct _
  rw [Real.log_mul (ne_of_gt hp1) (ne_of_gt hc1), Real.log_pow, Real.log_pow] at hlog
  have hPle : Real.log (((∏ v : V, (degV G v + 1) : ℕ) : ℝ)) ≤
      2 * Real.sqrt (2 * (Fintype.card E : ℝ) * (Fintype.card V : ℝ)) := by
    rw [hlogP]
    exact sum_log_degV_le
  have hCle : Real.log ((Nat.choose (Fintype.card E + (Fintype.card V - 1))
        (Fintype.card V - 1) : ℕ) : ℝ) ≤
      4 * Real.sqrt ((Fintype.card E : ℝ) * (((Fintype.card V - 1 : ℕ)) : ℝ)) :=
    log_choose_le _ _
  have ht2 : ((t * t : ℕ) : ℝ) = (t : ℝ) ^ 2 := by push_cast; ring
  calc Real.log (Hs.card : ℝ)
      ≤ ((t * t : ℕ) : ℝ) * Real.log (((∏ v : V, (degV G v + 1) : ℕ) : ℝ)) +
          ((t * t : ℕ) : ℝ) * Real.log ((Nat.choose (Fintype.card E + (Fintype.card V - 1))
            (Fintype.card V - 1) : ℕ) : ℝ) := hlog
    _ ≤ ((t * t : ℕ) : ℝ) *
            (2 * Real.sqrt (2 * (Fintype.card E : ℝ) * (Fintype.card V : ℝ))) +
          ((t * t : ℕ) : ℝ) *
            (4 * Real.sqrt ((Fintype.card E : ℝ) * (((Fintype.card V - 1 : ℕ)) : ℝ))) :=
        add_le_add (mul_le_mul_of_nonneg_left hPle (by positivity))
          (mul_le_mul_of_nonneg_left hCle (by positivity))
    _ = (t : ℝ) ^ 2 *
          (2 * Real.sqrt (2 * (Fintype.card E : ℝ) * (Fintype.card V : ℝ)) +
            4 * Real.sqrt ((Fintype.card E : ℝ) * (((Fintype.card V - 1 : ℕ)) : ℝ))) := by
        rw [← ht2]; ring

end DLMST