import DLMST.Section36
import DLMST.Driver
import DLMST.ScheduleBound

/-!
# §3.6: assembling Lemma 1.2 from one call and its recursion levels

The paper's §3.6 is the last step before §4: it takes the *per-call* statements of §3.2–§3.5 —
a call at depth `d` with parameters `t = γd³`, `r = 8t³` returns a forest `F`, has at most
`O(t²√(m_c n_c)) + 4m_c/t` errors, passes at most `4m_c/t` edges to children, and spends
`O(t²(n_c + √(m_c n_c)))` comparisons — and sums them over the recursion tree.  Two facts make the
sum collapse:

* **the vertex totals shrink by `4` each level**: the `t²` children of a call have
  `2nt/r = n/4` vertices in total, so after `d` levels the total is `n/4^d` (this is the only place
  §3.6's geometry is used);
* **an edge is passed to at most one child**, so the level edge totals never exceed `m`.

With these, `Σ_d poly(d)·√(m_d n_d) = O(√(mn))` because `poly(d)/2^d` is summable — the numerical
fact already isolated as `Section36.claim_3_13` and its `40000` bound.  This file supplies the two
interfaces the sum needs and performs it:

* `CallOut` — one call's output, with its classification of the instance's edges into `F`,
  `U(F) = unsupp ∩ E` (each edge exactly once, `CallOut.partition_eq`) and the children's inputs;
* `Level` / `Step` — the level totals and the two geometric facts, proved as
  `LevelChain.verts` (`nL d · 4^d ≤ n`) and `LevelChain.edges` (`mL d ≤ m`) from the *per-call*
  subset/disjointness/shrink data, so `hn`/`hm` of `errors_levels` are no longer hypotheses;
* `errors_gather` / `comparisons_gather` — the per-level Cauchy–Schwarz that turns per-call bounds
  into level totals;
* `lemma12_of_levels` — the composition: the display of Lemma 1.2 at the root;
* `comparisons_of_levels` — the paper's comparison sentence
  `Σ_calls O(t²(n_c + √(m_c n_c))) = Oγ(n + √(mn))`.

What is *not* here is the procedure producing a call's `(F, P', cls)`.  The packaging is
`CallOut.ofClass` (§6): once the classifying function exists, every field of `CallOut` follows, and
its only numerical obligation is the portal budget `4·t²·|P'| ≤ |P|`, which `portals_shrink`
derives from the per-round bounds `Portals.portal_bound` supplies.  The leaf case is complete
(`CallOut.ofForest`, `CallOut.nonempty_of_isForest`), and `Step.ofCallOut` turns one call into one
recursion step, so a `Level` chain can be built as soon as the children are themselves calls.
This file is the accounting that binds the pieces, with every hypothesis named.
-/

open Classical
open scoped BigOperators

namespace DLMST

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [LinearOrder E] {G : WGraph V E}

/-! ## 1. One call: the classification of its instance's edges -/

/-- The output of one certificate call on the instance `(P, E₀)`: the forest `F` it returns, and
its children, each a recursive call on its own portal set `kidV i` and input `kidE i`.

The fields are exactly the facts §3.6's bookkeeping uses.  `hcover` is the "an edge is passed to at
most one child" (here: *exactly one* of `F`, `U(F)`, or one child) and `hshrink` is "the `t²`
children have in total a quarter of the vertices" (`2nt/r = n/4`).  Children *share* portals (the
paper's `t²` calls all draw from the same `2nt/r` portal set), so `kidV` is not required to be
pairwise disjoint — only the edge sets are. -/
structure CallOut (G : WGraph V E) (ι : Type*) [Fintype ι] where
  P : Finset V
  E₀ : Finset E
  F : Finset E
  kidE : ι → Finset E
  kidV : ι → Finset V
  hFsub : F ⊆ E₀
  hforest : IsForest G F
  hFcard : F.card ≤ P.card
  hkidE : ∀ i, kidE i ⊆ E₀
  hkidV : ∀ i, kidV i ⊆ P
  hkidEdisj : ∀ i j, i ≠ j → Disjoint (kidE i) (kidE j)
  hFkid : ∀ i, Disjoint F (kidE i)
  hUkid : ∀ i, Disjoint (unsupp G F ∩ E₀) (kidE i)
  hcover : ∀ e ∈ E₀, e ∈ F ∨ e ∈ unsupp G F ∨ ∃ i, e ∈ kidE i
  hshrink : 4 * (∑ i, (kidV i).card) ≤ P.card

namespace CallOut

variable {ι : Type*} [Fintype ι] {O : CallOut G ι}

/-- The instance's unsupported edges — the paper's `U(F)` restricted to this instance. -/
noncomputable def U (O : CallOut G ι) : Finset E := unsupp G O.F ∩ O.E₀

theorem U_sub (O : CallOut G ι) : O.U ⊆ O.E₀ := Finset.inter_subset_right

theorem FU_disjoint (O : CallOut G ι) : Disjoint O.F O.U :=
  (disjoint_unsupp (G := G) (F := O.F)).mono_right Finset.inter_subset_left

theorem kids_disjoint (O : CallOut G ι) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset ι)) O.kidE :=
  fun i _ j _ hij => O.hkidEdisj i j hij

/-- **The partition identity**: `|F| + |U(F)| + Σᵢ|Eᵢ| = |E₀|`.  Every edge of the instance is in
exactly one of the forest, the unsupported set, or one child's input — the paper's "an edge is
projected and passed to exactly one child recursion instance". -/
theorem partition_eq (O : CallOut G ι) :
    O.F.card + O.U.card + ∑ i, (O.kidE i).card = O.E₀.card := by
  have hii := O.kids_disjoint
  have hcover : O.F ∪ O.U ∪ Finset.univ.biUnion O.kidE = O.E₀ := by
    apply Finset.Subset.antisymm
    · intro e he
      rcases Finset.mem_union.mp he with heFU | heK
      · rcases Finset.mem_union.mp heFU with heF | heU
        · exact O.hFsub heF
        · exact O.U_sub heU
      · obtain ⟨i, -, hei⟩ := Finset.mem_biUnion.mp heK
        exact O.hkidE i hei
    · intro e he
      rcases O.hcover e he with heF | heU | ⟨i, hei⟩
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl heF)))
      · exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨heU, he⟩))))
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hei⟩))
  have hUnion : Disjoint (O.F ∪ O.U) (Finset.univ.biUnion O.kidE) := by
    rw [Finset.disjoint_biUnion_right]
    intro i _
    rw [Finset.disjoint_union_left]
    exact ⟨O.hFkid i, O.hUkid i⟩
  have h1 : (O.F ∪ O.U ∪ Finset.univ.biUnion O.kidE).card
      = O.F.card + O.U.card + (Finset.univ.biUnion O.kidE).card := by
    rw [Finset.card_union_of_disjoint hUnion, Finset.card_union_of_disjoint O.FU_disjoint]
  have h2 : (Finset.univ.biUnion O.kidE).card = ∑ i, (O.kidE i).card :=
    Finset.card_biUnion hii
  rw [hcover] at h1
  omega

/-- The children's inputs are at most as large as the instance's edge set. -/
theorem sum_kidE_le (O : CallOut G ι) : ∑ i, (O.kidE i).card ≤ O.E₀.card := by
  calc ∑ i, (O.kidE i).card = (Finset.univ.biUnion O.kidE).card :=
        (Finset.card_biUnion O.kids_disjoint).symm
    _ ≤ O.E₀.card := Finset.card_le_card (by
        intro e he
        obtain ⟨i, -, hei⟩ := Finset.mem_biUnion.mp he
        exact O.hkidE i hei)

/-- Each child's portal set is small: the total shrink gives `4·|kidV i| ≤ |P|`. -/
theorem kidV_card (O : CallOut G ι) (i : ι) : 4 * (O.kidV i).card ≤ O.P.card := by
  have hle : (O.kidV i).card ≤ ∑ j, (O.kidV j).card :=
    Finset.single_le_sum (f := fun j => (O.kidV j).card) (fun j _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have h := O.hshrink
  omega

/-- **Strict decrease at one call.**  A child's input is a subset of the instance's edge set; if even
one edge of the instance is kept away from that child, the child is strictly smaller.  This is the
one place the recursion's termination condition is produced. -/
theorem kidE_card_lt (O : CallOut G ι) (i : ι) {e : E} (he : e ∈ O.E₀) (hne : e ∉ O.kidE i) :
    (O.kidE i).card < O.E₀.card :=
  Finset.card_lt_card (Finset.ssubset_iff_of_subset (O.hkidE i) |>.mpr ⟨e, he, hne⟩)

end CallOut

/-! ## 2. The recursion's levels and their geometry -/

/-- One instance of the recursion: its portal set and its edge set. -/
abbrev Inst (V E : Type*) := Finset V × Finset E

/-- All calls at one recursion depth.  Only the *edge* sets are disjoint (an edge is passed to one
child); the vertex sets may share portals, so `verts` is a cost total, not a union size. -/
structure Level (V E : Type*) [DecidableEq V] [DecidableEq E] where
  insts : Finset (Inst V E)
  edisj : ∀ a ∈ insts, ∀ b ∈ insts, a ≠ b → Disjoint a.2 b.2

namespace Level

variable (L : Level V E)

/-- The number of vertices across all calls at this depth. -/
noncomputable def verts : ℕ := ∑ a ∈ L.insts, a.1.card

/-- The number of edges across all calls at this depth. -/
noncomputable def edges : ℕ := ∑ a ∈ L.insts, a.2.card

end Level

/-- One recursion step: every call at the next depth is a child of one at this depth, with its
portal set and edges contained in the parent's, and the vertex totals shrink by `4` — the paper's
`t² · 2nt/r = n/4`. -/
structure Step (A B : Level V E) : Prop where
  sub : ∀ b ∈ B.insts, ∃ a ∈ A.insts, b.1 ⊆ a.1 ∧ b.2 ⊆ a.2
  shrink : 4 * B.verts ≤ A.verts

namespace Step

variable {A B : Level V E}

/-- Children's edge totals never exceed the parent's: an edge is passed to at most one child. -/
theorem edges_le (h : Step A B) : B.edges ≤ A.edges := by
  have hB : B.edges = (B.insts.biUnion (·.2)).card :=
    (Finset.card_biUnion (fun a ha b hb hab => B.edisj a ha b hb hab)).symm
  have hsub : B.insts.biUnion (·.2) ⊆ A.insts.biUnion (·.2) := by
    intro e he
    obtain ⟨b, hb, heb⟩ := Finset.mem_biUnion.mp he
    obtain ⟨a, ha, -, hea⟩ := h.sub b hb
    exact Finset.mem_biUnion.mpr ⟨a, ha, hea heb⟩
  calc B.edges = (B.insts.biUnion (·.2)).card := hB
    _ ≤ (A.insts.biUnion (·.2)).card := Finset.card_le_card hsub
    _ ≤ ∑ a ∈ A.insts, a.2.card := Finset.card_biUnion_le
    _ = A.edges := rfl

end Step

namespace LevelChain

variable {n m : ℕ}

/-- **The vertex totals shrink by `4` per level** — the paper's `n_d ≤ 4^{-(d-1)} n`, which is the
`hn` hypothesis of `errors_levels`, now a theorem about the recursion's levels. -/
theorem verts {L : ℕ → Level V E} (hstep : ∀ d, Step (L d) (L (d + 1)))
    (h0 : (L 0).verts = n) (d : ℕ) : (L d).verts * 4 ^ d ≤ n := by
  induction d with
  | zero => simp [h0]
  | succ k ih =>
      have hs : (L (k + 1)).verts * 4 ≤ (L k).verts := by
        rw [Nat.mul_comm]
        exact (hstep k).shrink
      calc (L (k + 1)).verts * 4 ^ (k + 1) = ((L (k + 1)).verts * 4) * 4 ^ k := by
            rw [Nat.pow_succ]; ring
        _ ≤ (L k).verts * 4 ^ k := Nat.mul_le_mul_right _ hs
        _ ≤ n := ih

/-- **The edge totals never exceed `m`** — the `hm` hypothesis of `errors_levels`. -/
theorem edges {L : ℕ → Level V E} (hstep : ∀ d, Step (L d) (L (d + 1)))
    (h0 : (L 0).edges = m) (d : ℕ) : (L d).edges ≤ m := by
  induction d with
  | zero => simp [h0]
  | succ k ih => exact le_trans (hstep k).edges_le ih

end LevelChain

/-! ## 3. Per-level Cauchy–Schwarz: from calls to level totals -/

/-- **The paper's per-level Cauchy–Schwarz for errors.**  If each call at one recursion depth has at
most `t²√(m_c n_c) + 4m_c/t` errors with the *same* `t`, the level's total error count is at most
`t²√(m_d n_d) + 4m_d/t` where `m_d`, `n_d` are the level totals. -/
theorem errors_gather {ι : Type*} [Fintype ι] {mC nC errC : ι → ℕ} {t : ℝ} (ht : 0 < t)
    (herr : ∀ i, (errC i : ℝ) ≤
      t ^ 2 * Real.sqrt ((mC i : ℝ) * (nC i : ℝ)) + 4 * (mC i : ℝ) / t) :
    (∑ i, (errC i : ℝ)) ≤
      t ^ 2 * Real.sqrt ((∑ i, (mC i : ℝ)) * (∑ i, (nC i : ℝ))) +
        4 * (∑ i, (mC i : ℝ)) / t := by
  have hcs : (∑ i, Real.sqrt ((mC i : ℝ) * (nC i : ℝ)))
      ≤ Real.sqrt ((∑ i, (mC i : ℝ)) * (∑ i, (nC i : ℝ))) := by
    have h1 := Real.sum_sqrt_mul_sqrt_le (Finset.univ)
      (f := fun i => (mC i : ℝ)) (g := fun i => (nC i : ℝ))
      (fun i => Nat.cast_nonneg _) (fun i => Nat.cast_nonneg _)
    calc ∑ i, Real.sqrt ((mC i : ℝ) * (nC i : ℝ))
        = ∑ i, Real.sqrt (mC i : ℝ) * Real.sqrt (nC i : ℝ) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          exact Real.sqrt_mul (Nat.cast_nonneg (mC i)) _
      _ ≤ Real.sqrt (∑ i, (mC i : ℝ)) * Real.sqrt (∑ i, (nC i : ℝ)) := h1
      _ = Real.sqrt ((∑ i, (mC i : ℝ)) * (∑ i, (nC i : ℝ))) := by
          rw [Real.sqrt_mul (by positivity)]
  have hstep : (∑ i, (errC i : ℝ))
      ≤ ∑ i, (t ^ 2 * Real.sqrt ((mC i : ℝ) * (nC i : ℝ)) + 4 * (mC i : ℝ) / t) :=
    Finset.sum_le_sum (fun i _ => herr i)
  have hsplit : (∑ i, (t ^ 2 * Real.sqrt ((mC i : ℝ) * (nC i : ℝ)) + 4 * (mC i : ℝ) / t))
      = t ^ 2 * (∑ i, Real.sqrt ((mC i : ℝ) * (nC i : ℝ))) +
        4 * (∑ i, (mC i : ℝ)) / t := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_div]
  have hmono : t ^ 2 * (∑ i, Real.sqrt ((mC i : ℝ) * (nC i : ℝ))) ≤
      t ^ 2 * Real.sqrt ((∑ i, (mC i : ℝ)) * (∑ i, (nC i : ℝ))) :=
    mul_le_mul_of_nonneg_left hcs (by positivity)
  rw [hsplit] at hstep
  linarith

/-- **The same for the edges handed to children**: per call at most `4m_c/t`, so the level total is
at most `4m_d/t`. -/
theorem inputs_gather {ι : Type*} [Fintype ι] {mC inC : ι → ℕ} {t : ℝ}
    (hin : ∀ i, (inC i : ℝ) ≤ 4 * (mC i : ℝ) / t) :
    (∑ i, (inC i : ℝ)) ≤ 4 * (∑ i, (mC i : ℝ)) / t := by
  calc (∑ i, (inC i : ℝ)) ≤ ∑ i, 4 * (mC i : ℝ) / t := Finset.sum_le_sum (fun i _ => hin i)
    _ = 4 * (∑ i, (mC i : ℝ)) / t := by
        rw [Finset.mul_sum, ← Finset.sum_div]

/-! ### The uniform form: one procedure, applied to every instance of a level

`errors_gather`/`inputs_gather` are stated per level, against the level's totals.  The paper's
procedure is uniform: the same call is made on every subproblem.  The two lemmas below rewrite the
per-level hypotheses as per-instance ones with the same `t`, which is where the uniformity matters
— the `t` depends on the depth, not on the instance. -/

/-- **A level's error total from uniform per-call bounds.**  If every instance `a` of the level obeys
`err a ≤ t²√(m_a n_a) + 4m_a/t` with the level's own `t`, then the level total obeys the level
bound.  `L.edges` and `L.verts` are exactly the sums `errors_gather` needs. -/
theorem Level.errors_le {t : ℝ} (ht : 0 < t) (L : Level V E) (errF : Inst V E → ℕ)
    (h : ∀ a ∈ L.insts, (errF a : ℝ) ≤
      t ^ 2 * Real.sqrt ((a.2.card : ℝ) * (a.1.card : ℝ)) + 4 * (a.2.card : ℝ) / t) :
    (∑ a ∈ L.insts, (errF a : ℝ)) ≤
      t ^ 2 * Real.sqrt ((L.edges : ℝ) * (L.verts : ℝ)) + 4 * (L.edges : ℝ) / t := by
  have hg := errors_gather (ι := ↥L.insts) (mC := fun a => a.1.2.card)
    (nC := fun a => a.1.1.card) (errC := fun a => errF a.1) ht (fun a => h a.1 a.2)
  have hm : (∑ i : ↥L.insts, (i.1.2.card : ℝ)) = (L.edges : ℝ) := by
    have h1 : (∑ i : ↥L.insts, (i.1.2.card : ℝ)) = ∑ a ∈ L.insts, (a.2.card : ℝ) := by
      rw [Finset.univ_eq_attach]
      exact Finset.sum_attach (s := L.insts) (f := fun a : Inst V E => (a.2.card : ℝ))
    rw [h1, Level.edges, Nat.cast_sum]
  have hn : (∑ i : ↥L.insts, (i.1.1.card : ℝ)) = (L.verts : ℝ) := by
    have h1 : (∑ i : ↥L.insts, (i.1.1.card : ℝ)) = ∑ a ∈ L.insts, (a.1.card : ℝ) := by
      rw [Finset.univ_eq_attach]
      exact Finset.sum_attach (s := L.insts) (f := fun a : Inst V E => (a.1.card : ℝ))
    rw [h1, Level.verts, Nat.cast_sum]
  have h2 : (∑ i : ↥L.insts, (errF i.1 : ℝ)) = ∑ a ∈ L.insts, (errF a : ℝ) := by
    rw [Finset.univ_eq_attach]
    exact Finset.sum_attach (s := L.insts) (f := fun a : Inst V E => (errF a : ℝ))
  rw [hm, hn, h2] at hg
  exact hg

/-- **The same for the edges handed to children.** -/
theorem Level.inputs_le {t : ℝ} (L : Level V E) (inF : Inst V E → ℕ)
    (h : ∀ a ∈ L.insts, (inF a : ℝ) ≤ 4 * (a.2.card : ℝ) / t) :
    (∑ a ∈ L.insts, (inF a : ℝ)) ≤ 4 * (L.edges : ℝ) / t := by
  have hg := inputs_gather (ι := ↥L.insts) (mC := fun a => a.1.2.card)
    (inC := fun a => inF a.1) (fun a => h a.1 a.2)
  have hm : (∑ i : ↥L.insts, (i.1.2.card : ℝ)) = (L.edges : ℝ) := by
    have h1 : (∑ i : ↥L.insts, (i.1.2.card : ℝ)) = ∑ a ∈ L.insts, (a.2.card : ℝ) := by
      rw [Finset.univ_eq_attach]
      exact Finset.sum_attach (s := L.insts) (f := fun a : Inst V E => (a.2.card : ℝ))
    rw [h1, Level.edges, Nat.cast_sum]
  have h2 : (∑ i : ↥L.insts, (inF i.1 : ℝ)) = ∑ a ∈ L.insts, (inF a : ℝ) := by
    rw [Finset.univ_eq_attach]
    exact Finset.sum_attach (s := L.insts) (f := fun a : Inst V E => (inF a : ℝ))
  rw [hm, h2] at hg
  exact hg

/-- **The honest per-instance input bound, gathered.**  An instance hands its children at most
`errF a + C·t²·n_a` edges: the rejected edges (already counted in `errF`) *plus* the per-round MSF
calls on `n_a` vertices — `2t²(n_a − 1)` for the old and the child forest, `t(n_a − 1 + r_a²n_a)`
per block.  With `t` uniform on the level, the level total is `ΣerrF + C·t²·n_L`.

`Level.inputs_le` is the `errF`-free, `C = 0` special case (the paper's display of `Σ|Eᵢ|`); this is
the version the procedure's actual calls satisfy. -/
theorem Level.inputs_le_err {t C : ℝ} (L : Level V E) (errF inF : Inst V E → ℕ)
    (h : ∀ a ∈ L.insts, (inF a : ℝ) ≤ (errF a : ℝ) + C * (t ^ 2 * (a.1.card : ℝ))) :
    (∑ a ∈ L.insts, (inF a : ℝ)) ≤ (∑ a ∈ L.insts, (errF a : ℝ)) +
      C * (t ^ 2 * (L.verts : ℝ)) := by
  refine le_trans (Finset.sum_le_sum h) (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Level.verts, Nat.cast_sum]

/-! ## 4. The `hrest` account of §3.6, and the display at the root -/

/-- **§3.6's error account from a recursion.**  `L 0` is the root call (`verts = n`, `edges = m`),
`L (d+1)` the calls at depth `d+1`; each level's errors and child inputs obey the per-call bounds
`O(t²√(mn)) + 4m/t` and `4m/t` with `t = γ(d+1)³`; every unsupported edge is charged to some
level's error (Lemma 3.7) and the root's children are the next level's inputs.  Then

`|U(F)| + Σ|Eᵢ| ≤ γ²·40000·√(mn) + 16m/γ` —

exactly the `hrest` hypothesis of `lemma12_bound`. -/
theorem hrest_of_levels {n m : ℕ} {γ : ℝ} (hγ : 0 < γ) {D : ℕ} {L : ℕ → Level V E}
    (hstep : ∀ d, Step (L d) (L (d + 1))) (hn0 : (L 0).verts = n) (hm0 : (L 0).edges = m)
    {errL inL : ℕ → ℕ}
    (herr : ∀ d ∈ Finset.range D, (errL d : ℝ) ≤
      (γ * ((d : ℝ) + 1) ^ 3) ^ 2 * Real.sqrt (((L d).edges : ℝ) * ((L d).verts : ℝ)) +
        4 * ((L d).edges : ℝ) / (γ * ((d : ℝ) + 1) ^ 3))
    (hin : ∀ d ∈ Finset.range D, (inL d : ℝ) ≤
        4 * ((L d).edges : ℝ) / (γ * ((d : ℝ) + 1) ^ 3))
    {U SE : ℕ} (hU : U ≤ ∑ d ∈ Finset.range D, errL d)
    (hSE : SE ≤ ∑ d ∈ Finset.range D, inL d) :
    (U : ℝ) + (SE : ℝ) ≤
      γ ^ 2 * 40000 * Real.sqrt ((m : ℝ) * (n : ℝ)) + 16 * (m : ℝ) / γ := by
  have hbase := errors_levels (n := n) (m := m) hγ (D := D)
    (nL := fun d => (L d).verts) (mL := fun d => (L d).edges) (errL := errL) (inL := inL)
    (fun d _ => by exact_mod_cast LevelChain.verts hstep hn0 d)
    (fun d _ => by exact_mod_cast LevelChain.edges hstep hm0 d)
    herr hin
  have h1 : (U : ℝ) ≤ (∑ d ∈ Finset.range D, (errL d : ℝ)) := by exact_mod_cast hU
  have h2 : (SE : ℝ) ≤ (∑ d ∈ Finset.range D, (inL d : ℝ)) := by exact_mod_cast hSE
  linarith

/-- **Lemma 1.2 at a call, with every §3.6 input named.**  The instance has `P` vertices and `E₀`
edges with `|P| ≤ 2|E₀|`, `F` is its returned forest with `|F| ≤ |P|`, and `hrest` is the error
account (`hrest_of_levels` at the root). -/
theorem display_of_callout {ι : Type*} [Fintype ι] (O : CallOut G ι) {γ ε : ℝ}
    (hγ : 0 < γ) (hε : 0 < ε) (hγε : 16 ≤ ε * γ)
    (hnm : (O.P.card : ℝ) ≤ 2 * (O.E₀.card : ℝ))
    (hrest : ((O.U).card : ℝ) + ((∑ i, (O.kidE i).card : ℕ) : ℝ) ≤
      γ ^ 2 * 40000 * Real.sqrt ((O.E₀.card : ℝ) * (O.P.card : ℝ)) +
        16 * (O.E₀.card : ℝ) / γ) :
    (O.F.card : ℝ) + ((O.U).card : ℝ) + ((∑ i, (O.kidE i).card : ℕ) : ℝ) ≤
      ε * (O.E₀.card : ℝ) +
        (Real.sqrt 2 + γ ^ 2 * 40000) *
          Real.sqrt ((O.E₀.card : ℝ) * (O.P.card : ℝ)) :=
  lemma12_bound (n := O.P.card) (m := O.E₀.card) (Fc := O.F.card)
    (U := (O.U).card) (SE := ∑ i, (O.kidE i).card) hγ hε hγε hnm
    (by exact_mod_cast O.hFcard) hrest

/-- **The root's display, end to end**: one call `O` whose unsupported edges and child inputs pay
the §3.6 account.  This is the `hdisplay` of `CertificateBuild.certificate_of_display` at the
instance `O`, with `C = √2 + γ²·40000` and `ρ = ε`. -/
theorem display_of_callout_full {ι : Type*} [Fintype ι] (O : CallOut G ι) {γ ε : ℝ}
    (hγ : 0 < γ) (hε : 0 < ε) (hγε : 16 ≤ ε * γ)
    (hnm : (O.P.card : ℝ) ≤ 2 * (O.E₀.card : ℝ))
    {D : ℕ} {L : ℕ → Level V E} (hstep : ∀ d, Step (L d) (L (d + 1)))
    (hn0 : (L 0).verts = O.P.card) (hm0 : (L 0).edges = O.E₀.card)
    {errL inL : ℕ → ℕ}
    (herr : ∀ d ∈ Finset.range D, (errL d : ℝ) ≤
      (γ * ((d : ℝ) + 1) ^ 3) ^ 2 * Real.sqrt (((L d).edges : ℝ) * ((L d).verts : ℝ)) +
        4 * ((L d).edges : ℝ) / (γ * ((d : ℝ) + 1) ^ 3))
    (hin : ∀ d ∈ Finset.range D, (inL d : ℝ) ≤
        4 * ((L d).edges : ℝ) / (γ * ((d : ℝ) + 1) ^ 3))
    (hU : (O.U).card ≤ ∑ d ∈ Finset.range D, errL d)
    (hSE : ∑ i, (O.kidE i).card ≤ ∑ d ∈ Finset.range D, inL d) :
    (O.F.card : ℝ) + ((O.U).card : ℝ) + ((∑ i, (O.kidE i).card : ℕ) : ℝ) ≤
      ε * (O.E₀.card : ℝ) +
        (Real.sqrt 2 + γ ^ 2 * 40000) *
          Real.sqrt ((O.E₀.card : ℝ) * (O.P.card : ℝ)) :=
  display_of_callout O hγ hε hγε hnm
    (hrest_of_levels hγ hstep hn0 hm0 herr hin hU hSE)

/-- **§3.6's error account with the procedure's honest per-call input.**  The child calls of one
instance are not just the rejected edges (`≤ 4m_c/t`): they also replay the rounds and the blocks,
`2t²(n_c − 1)` and `t(n_c − 1 + r_c²n_c)` edges, so per instance the true total is
`errF + C·t²·n_c`.  Level `d` has `n_d ≤ n/4^d`, so this piece decays by `4^{-d}`
(`errors_levels_rest`) and the level sum still closes with `16m/γ` for both `4m_d/t_d` accounts. -/
theorem hrest_of_levels_rest {n m : ℕ} {γ C : ℝ} (hγ : 0 < γ) (hC : 0 ≤ C) {D : ℕ}
    {L : ℕ → Level V E}
    (hstep : ∀ d, Step (L d) (L (d + 1))) (hn0 : (L 0).verts = n) (hm0 : (L 0).edges = m)
    {errL inL : ℕ → ℕ}
    (herr : ∀ d ∈ Finset.range D, (errL d : ℝ) ≤
      (γ * ((d : ℝ) + 1) ^ 3) ^ 2 * Real.sqrt (((L d).edges : ℝ) * ((L d).verts : ℝ)) +
        4 * ((L d).edges : ℝ) / (γ * ((d : ℝ) + 1) ^ 3))
    (hin : ∀ d ∈ Finset.range D, (inL d : ℝ) ≤ (errL d : ℝ) +
      C * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 * ((L d).verts : ℝ)))
    (hnm : (n : ℝ) ≤ 2 * (m : ℝ))
    {U SE : ℕ} (hU : U ≤ ∑ d ∈ Finset.range D, errL d)
    (hSE : SE ≤ ∑ d ∈ Finset.range D, inL d) :
    (U : ℝ) + (SE : ℝ) ≤
      γ ^ 2 * (40000 * (2 + Real.sqrt 2 * C)) * Real.sqrt ((m : ℝ) * (n : ℝ)) +
        16 * (m : ℝ) / γ := by
  have hbase := errors_levels_rest (n := n) (m := m) (γ := γ) (C := C) hγ hC (D := D)
    (nL := fun d => (L d).verts) (mL := fun d => (L d).edges) (errL := errL) (inL := inL)
    (fun d _ => by exact_mod_cast LevelChain.verts hstep hn0 d)
    (fun d _ => by exact_mod_cast LevelChain.edges hstep hm0 d) hnm herr hin
  have hbase' : ((∑ d ∈ Finset.range D, (errL d : ℝ)) + ∑ d ∈ Finset.range D, (inL d : ℝ)) ≤
      γ ^ 2 * (40000 * (2 + Real.sqrt 2 * C)) * Real.sqrt ((m : ℝ) * (n : ℝ)) +
        16 * (m : ℝ) / γ := by
    have h := hbase
    rw [show γ ^ 2 * 40000 * (2 + Real.sqrt 2 * C) * Real.sqrt ((m : ℝ) * (n : ℝ))
        = γ ^ 2 * (40000 * (2 + Real.sqrt 2 * C)) *
            Real.sqrt ((m : ℝ) * (n : ℝ)) by ring] at h
    exact h
  have h1 : (U : ℝ) ≤ (∑ d ∈ Finset.range D, (errL d : ℝ)) := by exact_mod_cast hU
  have h2 : (SE : ℝ) ≤ (∑ d ∈ Finset.range D, (inL d : ℝ)) := by exact_mod_cast hSE
  linarith

/-- **§3.6 from per-instance data alone.**  The two per-call hypotheses are stated for every instance
of every level: `errF a ≤ t_d²√(m_a n_a) + 4m_a/t_d` and `inF a ≤ errF a + C·t_d²·n_a`.  Gathering them
level by level (`Level.errors_le`, `Level.inputs_le_err`) and summing over the levels
(`hrest_of_levels_rest`) gives the root account — no per-level hypothesis is left to the caller. -/
theorem hrest_of_instances_rest {n m : ℕ} {γ C : ℝ} (hγ : 0 < γ) (hC : 0 ≤ C) {D : ℕ}
    {L : ℕ → Level V E}
    (hstep : ∀ d, Step (L d) (L (d + 1))) (hn0 : (L 0).verts = n) (hm0 : (L 0).edges = m)
    {errF inF : Inst V E → ℕ}
    (herr : ∀ d ∈ Finset.range D, ∀ a ∈ (L d).insts, (errF a : ℝ) ≤
      (γ * ((d : ℝ) + 1) ^ 3) ^ 2 * Real.sqrt ((a.2.card : ℝ) * (a.1.card : ℝ)) +
        4 * (a.2.card : ℝ) / (γ * ((d : ℝ) + 1) ^ 3))
    (hin : ∀ d ∈ Finset.range D, ∀ a ∈ (L d).insts, (inF a : ℝ) ≤ (errF a : ℝ) +
      C * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 * (a.1.card : ℝ)))
    (hnm : (n : ℝ) ≤ 2 * (m : ℝ))
    {U SE : ℕ} (hU : U ≤ ∑ d ∈ Finset.range D, ∑ a ∈ (L d).insts, errF a)
    (hSE : SE ≤ ∑ d ∈ Finset.range D, ∑ a ∈ (L d).insts, inF a) :
    (U : ℝ) + (SE : ℝ) ≤
      γ ^ 2 * (40000 * (2 + Real.sqrt 2 * C)) * Real.sqrt ((m : ℝ) * (n : ℝ)) +
        16 * (m : ℝ) / γ := by
  have hn' : ∀ d ∈ Finset.range D,
      ((∑ a ∈ (L d).insts, errF a : ℕ) : ℝ) ≤
        (γ * ((d : ℝ) + 1) ^ 3) ^ 2 *
            Real.sqrt (((L d).edges : ℝ) * ((L d).verts : ℝ)) +
          4 * ((L d).edges : ℝ) / (γ * ((d : ℝ) + 1) ^ 3) := by
    intro d hd
    rw [Nat.cast_sum]
    exact Level.errors_le (t := γ * ((d : ℝ) + 1) ^ 3) (by positivity) (L d) errF
      (fun a ha => herr d hd a ha)
  have hi' : ∀ d ∈ Finset.range D,
      ((∑ a ∈ (L d).insts, inF a : ℕ) : ℝ) ≤
        ((∑ a ∈ (L d).insts, errF a : ℕ) : ℝ) +
          C * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 * ((L d).verts : ℝ)) := by
    intro d hd
    rw [Nat.cast_sum, Nat.cast_sum]
    exact Level.inputs_le_err (t := γ * ((d : ℝ) + 1) ^ 3) (L d) errF inF
      (fun a ha => hin d hd a ha)
  exact hrest_of_levels_rest (n := n) (m := m) hγ hC hstep hn0 hm0 hn' hi' hnm hU hSE

/-- **The root's display with the procedure's honest per-call input**, `C` open: the constant is
`C_ε = √2 + γ²·40000·(2 + √2·C)`. -/
theorem display_of_callout_rest {ι : Type*} [Fintype ι] (O : CallOut G ι) {γ ε C : ℝ}
    (hγ : 0 < γ) (hε : 0 < ε) (hγε : 16 ≤ ε * γ) (hC : 0 ≤ C)
    (hnm : (O.P.card : ℝ) ≤ 2 * (O.E₀.card : ℝ))
    {D : ℕ} {L : ℕ → Level V E} (hstep : ∀ d, Step (L d) (L (d + 1)))
    (hn0 : (L 0).verts = O.P.card) (hm0 : (L 0).edges = O.E₀.card)
    {errL inL : ℕ → ℕ}
    (herr : ∀ d ∈ Finset.range D, (errL d : ℝ) ≤
      (γ * ((d : ℝ) + 1) ^ 3) ^ 2 * Real.sqrt (((L d).edges : ℝ) * ((L d).verts : ℝ)) +
        4 * ((L d).edges : ℝ) / (γ * ((d : ℝ) + 1) ^ 3))
    (hin : ∀ d ∈ Finset.range D, (inL d : ℝ) ≤ (errL d : ℝ) +
      C * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 * ((L d).verts : ℝ)))
    (hU : (O.U).card ≤ ∑ d ∈ Finset.range D, errL d)
    (hSE : ∑ i, (O.kidE i).card ≤ ∑ d ∈ Finset.range D, inL d) :
    (O.F.card : ℝ) + ((O.U).card : ℝ) + ((∑ i, (O.kidE i).card : ℕ) : ℝ) ≤
      ε * (O.E₀.card : ℝ) +
        (Real.sqrt 2 + γ ^ 2 * (40000 * (2 + Real.sqrt 2 * C))) *
          Real.sqrt ((O.E₀.card : ℝ) * (O.P.card : ℝ)) :=
  lemma12_bound_gen (n := O.P.card) (m := O.E₀.card) (Fc := O.F.card)
    (U := (O.U).card) (SE := ∑ i, (O.kidE i).card) (K := 40000 * (2 + Real.sqrt 2 * C))
    hγ hε hγε (by positivity) hnm (by exact_mod_cast O.hFcard)
    (hrest_of_levels_rest (n := O.P.card) (m := O.E₀.card) hγ hC hstep hn0 hm0 herr hin hnm
      hU hSE)

/-! ## 5. The comparisons account of §3.6 -/

/-- **§3.6's comparison sentence.**  Per level `d` the calls spend at most `C` times
`t_d²(|P| + √(m_d n_d))`; with the geometric shrink of the level vertex totals this sums to
`Oγ(n + √(mn))`.  The `√` part is `claim_3_13`; the `|P|` part is the same geometric series with
`n_d ≤ n/4^d ≤ n/2^d`. -/
theorem comparisons_of_levels {n m : ℕ} {γ : ℝ} (hγ : 0 < γ) {D : ℕ} {L : ℕ → Level V E}
    (hstep : ∀ d, Step (L d) (L (d + 1))) (hn0 : (L 0).verts = n) (hm0 : (L 0).edges = m) :
    (∑ d ∈ Finset.range D, (γ * ((d : ℝ) + 1) ^ 3) ^ 2 *
        (((L d).verts : ℝ) + Real.sqrt (((L d).edges : ℝ) * ((L d).verts : ℝ))))
      ≤ γ ^ 2 * 40000 * ((n : ℝ) + Real.sqrt ((m : ℝ) * (n : ℝ))) := by
  have hcoef : ∀ d : ℕ, (γ * ((d : ℝ) + 1) ^ 3) ^ 2 = γ ^ 2 * ((d : ℝ) + 1) ^ 6 := by
    intro d
    rw [mul_pow]
    congr 1
    ring
  have hvterm : ∀ d ∈ Finset.range D,
      (γ * ((d : ℝ) + 1) ^ 3) ^ 2 * ((L d).verts : ℝ) ≤
        (γ ^ 2 * (((d : ℝ) + 1) ^ 6 / 2 ^ d)) * (n : ℝ) := by
    intro d _
    have h4 : (0 : ℝ) < 4 ^ d := by positivity
    have hnd : ((L d).verts : ℝ) ≤ (n : ℝ) / 4 ^ d := by
      rw [le_div_iff₀ h4]
      exact_mod_cast LevelChain.verts hstep hn0 d
    have h24 : (2 : ℝ) ^ d ≤ 4 ^ d := by
      apply pow_le_pow_left₀ (by norm_num) (by norm_num)
    have hnd' : ((L d).verts : ℝ) ≤ (n : ℝ) / 2 ^ d :=
      le_trans hnd (div_le_div_of_nonneg_left (Nat.cast_nonneg n) (by positivity) h24)
    calc (γ * ((d : ℝ) + 1) ^ 3) ^ 2 * ((L d).verts : ℝ)
        ≤ (γ * ((d : ℝ) + 1) ^ 3) ^ 2 * ((n : ℝ) / 2 ^ d) :=
          mul_le_mul_of_nonneg_left hnd' (by positivity)
      _ = (γ ^ 2 * (((d : ℝ) + 1) ^ 6 / 2 ^ d)) * (n : ℝ) := by
          rw [hcoef d]
          field_simp
  have hvsum : (∑ d ∈ Finset.range D, (γ * ((d : ℝ) + 1) ^ 3) ^ 2 * ((L d).verts : ℝ))
      ≤ γ ^ 2 * (n : ℝ) * 40000 := by
    calc (∑ d ∈ Finset.range D, (γ * ((d : ℝ) + 1) ^ 3) ^ 2 * ((L d).verts : ℝ))
        ≤ ∑ d ∈ Finset.range D, (γ ^ 2 * (((d : ℝ) + 1) ^ 6 / 2 ^ d)) * (n : ℝ) :=
          Finset.sum_le_sum hvterm
      _ = (γ ^ 2 * (n : ℝ)) * ∑ d ∈ Finset.range D, (((d : ℝ) + 1) ^ 6 / 2 ^ d) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun d _ => ?_)
          ring
      _ ≤ (γ ^ 2 * (n : ℝ)) * 40000 :=
          mul_le_mul_of_nonneg_left (sum_pow6_div_two_pow_le D) (by positivity)
      _ = γ ^ 2 * (n : ℝ) * 40000 := by ring
  have hesum := claim_3_13 (n := n) (m := m) hγ.le (D := D)
    (nL := fun d => (L d).verts) (mL := fun d => (L d).edges)
    (fun d _ => by exact_mod_cast LevelChain.verts hstep hn0 d)
    (fun d _ => by exact_mod_cast LevelChain.edges hstep hm0 d)
  calc (∑ d ∈ Finset.range D, (γ * ((d : ℝ) + 1) ^ 3) ^ 2 *
        (((L d).verts : ℝ) + Real.sqrt (((L d).edges : ℝ) * ((L d).verts : ℝ))))
      = (∑ d ∈ Finset.range D, (γ * ((d : ℝ) + 1) ^ 3) ^ 2 * ((L d).verts : ℝ)) +
          ∑ d ∈ Finset.range D, (γ * ((d : ℝ) + 1) ^ 3) ^ 2 *
            Real.sqrt (((L d).edges : ℝ) * ((L d).verts : ℝ)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun d _ => ?_)
        ring
    _ ≤ γ ^ 2 * (n : ℝ) * 40000 +
          γ ^ 2 * 40000 * Real.sqrt ((m : ℝ) * (n : ℝ)) := add_le_add hvsum hesum
    _ = γ ^ 2 * 40000 * ((n : ℝ) + Real.sqrt ((m : ℝ) * (n : ℝ))) := by ring

/-! ## 6. Concrete calls: from classification data to a `CallOut`, and the first step

`CallOut`'s fields are the *conclusions* §3.6 uses, so a call can be packaged as soon as its
classifying function is in hand.  `CallOut.ofClass` does exactly that: given the returned forest
`F`, the portal set `P'` shared by the child instances, the number `N` of children, and a total
classification `cls : E → Option ι` of the instance's edges (`none` = kept in `F`/`U(F)`,
`some i` = handed to child `i`), all eleven fields are the definition's own bookkeeping.
`CallOut.ofForest` is the childless case: whenever `F` covers the supported part of `E₀` no child is
created, so every forest input (in particular `E₀ = ∅`) is a leaf call.

What a procedure must still produce is `(F, P', cls)`.  Its only numerical obligation is the portal
budget `4·t²·|P'| ≤ |P|` — the paper's `t²·2nt/r = n/4` — and `portals_shrink` performs that
arithmetic from the per-round portal bounds `r·|Q b| ≤ 2n` that `Portals.portal_bound` supplies.
`Step.ofCallOut` turns one call into one recursion step, the shape `LevelChain` consumes. -/

/-- **Summing over an image costs no more than summing over the domain** (all terms are natural
numbers, hence nonnegative). -/
theorem sum_image_le_sum {α β : Type*} [Fintype α] [DecidableEq β] (f : α → β) (g : β → ℕ) :
    ((Finset.univ : Finset α).image f).sum g ≤ ∑ i, g (f i) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset α))
    (t := (Finset.univ : Finset α).image f) (g := f)
    (fun x _ => Finset.mem_image_of_mem f (Finset.mem_univ x)) (fun x => g (f x))]
  refine Finset.sum_le_sum (fun y hy => ?_)
  have hne : ((Finset.univ : Finset α).filter (fun x => f x = y)).Nonempty := by
    obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hy
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
  have hinner : ((Finset.univ : Finset α).filter (fun x => f x = y)).sum (fun x => g (f x))
      = ((Finset.univ : Finset α).filter (fun x => f x = y)).card * g y := by
    rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2]),
      Finset.sum_const, smul_eq_mul]
  rw [hinner]
  calc g y = 1 * g y := (Nat.one_mul _).symm
    _ ≤ _ * g y := Nat.mul_le_mul_right _ (Finset.card_pos.mpr hne)

/-- A union's sum is at most the sum of the two sums (natural numbers are nonnegative). -/
theorem sum_union_le {β : Type*} [DecidableEq β] (s t : Finset β) (f : β → ℕ) :
    (s ∪ t).sum f ≤ s.sum f + t.sum f := by
  have hunion : s ∪ t = s ∪ (t \ s) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  rw [hunion, Finset.sum_union Finset.disjoint_sdiff]
  have hle : (t \ s).sum f ≤ t.sum f :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun x _ _ => Nat.zero_le _)
  exact Nat.add_le_add_left hle _

/-- **Summing over a `biUnion` costs no more than summing over the pieces.** -/
theorem sum_biUnion_le {α β : Type*} [DecidableEq β] (s : Finset α) (t : α → Finset β)
    (f : β → ℕ) : (s.biUnion t).sum f ≤ ∑ a ∈ s, (t a).sum f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      exact le_trans (sum_union_le (t a) (s.biUnion t) f) (by omega)

namespace Level

/-- The level consisting of a single call. -/
def root (P : Finset V) (E₀ : Finset E) : Level V E where
  insts := {(P, E₀)}
  edisj := by
    intro a ha b hb hab
    rw [Finset.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab

/-- **The children of one call, as the next level.**  Children sharing a portal set but receiving
different inputs are distinct instances; genuinely identical children are identified (`Level` is a
set of instances), which can only lower the level's vertex total. -/
def ofCallOut {ι : Type*} [Fintype ι] (O : CallOut G ι) : Level V E where
  insts := Finset.univ.image (fun i => (O.kidV i, O.kidE i))
  edisj := by
    intro a ha b hb hab
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hb
    by_cases hij : i = j
    · rw [hij] at hab
      exact absurd rfl hab
    · exact O.hkidEdisj i j hij

/-- **The children of all calls at one level**, each call with its own number of children (the
paper's `t²` depends on the depth, so the child index is `Fin N` with `N` supplied per call).  If
every instance `a` of `A` carries a call whose input is exactly `a`'s, the union of all those calls'
children is the next level.  Their edge sets are pairwise disjoint for two reasons: siblings' inputs
are disjoint by `CallOut`, and different parents' inputs are disjoint by `Level`'s own edge field. -/
def allChildren (A : Level V E) (c : A.insts → Sigma fun N : ℕ => CallOut G (Fin N))
    (hE : ∀ a, (c a).2.E₀ = a.val.2) : Level V E where
  insts := A.insts.attach.biUnion
    (fun a => Finset.univ.image (fun i => ((c a).2.kidV i, (c a).2.kidE i)))
  edisj := by
    intro b₁ hb₁ b₂ hb₂ hne
    obtain ⟨a₁, -, hb₁'⟩ := Finset.mem_biUnion.mp hb₁
    obtain ⟨a₂, -, hb₂'⟩ := Finset.mem_biUnion.mp hb₂
    obtain ⟨i₁, -, rfl⟩ := Finset.mem_image.mp hb₁'
    obtain ⟨i₂, -, rfl⟩ := Finset.mem_image.mp hb₂'
    by_cases ha : a₁ = a₂
    · subst ha
      by_cases hi : i₁ = i₂
      · subst hi
        exact absurd rfl hne
      · exact (c a₁).2.hkidEdisj i₁ i₂ hi
    · have hdisj : Disjoint a₁.val.2 a₂.val.2 :=
        A.edisj a₁.val a₁.property a₂.val a₂.property (fun h => ha (Subtype.ext h))
      have h1 : (c a₁).2.kidE i₁ ⊆ a₁.val.2 := by
        rw [← hE a₁]; exact (c a₁).2.hkidE i₁
      have h2 : (c a₂).2.kidE i₂ ⊆ a₂.val.2 := by
        rw [← hE a₂]; exact (c a₂).2.hkidE i₂
      exact hdisj.mono h1 h2

end Level

namespace Step

/-- **One call is one recursion step**: its children are the next level, each contained in the
call's instance, and the vertex totals shrink by `4` — `CallOut.hshrink` is exactly `Step.shrink`. -/
theorem ofCallOut {ι : Type*} [Fintype ι] (O : CallOut G ι) :
    Step (Level.root O.P O.E₀) (Level.ofCallOut O) where
  sub := by
    intro b hb
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨(O.P, O.E₀), Finset.mem_singleton_self _, O.hkidV i, O.hkidE i⟩
  shrink := by
    have hle : (Level.ofCallOut O).verts ≤ ∑ i, (O.kidV i).card :=
      sum_image_le_sum (fun i => (O.kidV i, O.kidE i)) (fun a => a.1.card)
    have hroot : (Level.root O.P O.E₀).verts = O.P.card := by
      simp [Level.verts, Level.root]
    show 4 * (Level.ofCallOut O).verts ≤ (Level.root O.P O.E₀).verts
    rw [hroot]
    exact le_trans (Nat.mul_le_mul_left 4 hle) O.hshrink

/-- **One recursion step, for a whole level.**  If every instance of `A` carries a call on that
instance, then the level of all their children is the next level, and the vertex totals shrink by
`4`.  This is the induction step of §3.6's geometry: the only remaining input is the per-instance
call itself. -/
theorem ofCalls (A : Level V E) (c : A.insts → Sigma fun N : ℕ => CallOut G (Fin N))
    (hP : ∀ a, (c a).2.P = a.val.1) (hE : ∀ a, (c a).2.E₀ = a.val.2) :
    Step A (Level.allChildren A c hE) where
  sub := by
    intro b hb
    simp only [Level.allChildren] at hb
    obtain ⟨a, -, hb'⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hb'
    exact ⟨a.val, a.property, by rw [← hP a]; exact (c a).2.hkidV i, by
      rw [← hE a]; exact (c a).2.hkidE i⟩
  shrink := by
    have h1 : (Level.allChildren A c hE).verts ≤
        ∑ a : A.insts, ∑ i, ((c a).2.kidV i).card := by
      calc (Level.allChildren A c hE).verts
          = (A.insts.attach.biUnion
              (fun a => Finset.univ.image (fun i => ((c a).2.kidV i, (c a).2.kidE i)))).sum
                (fun b => b.1.card) := rfl
        _ ≤ ∑ a : A.insts,
              (Finset.univ.image (fun i => ((c a).2.kidV i, (c a).2.kidE i))).sum
                (fun b => b.1.card) := sum_biUnion_le _ _ _
        _ ≤ ∑ a : A.insts, ∑ i, ((c a).2.kidV i).card :=
            Finset.sum_le_sum (fun a _ => sum_image_le_sum _ _)
    have h2 : 4 * (∑ a : A.insts, ∑ i, ((c a).2.kidV i).card) ≤
        ∑ a : A.insts, a.val.1.card := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun a _ => by
        have := (c a).2.hshrink
        rwa [hP a] at this)
    calc 4 * (Level.allChildren A c hE).verts
        ≤ 4 * (∑ a : A.insts, ∑ i, ((c a).2.kidV i).card) := Nat.mul_le_mul_left 4 h1
      _ ≤ ∑ a : A.insts, a.val.1.card := h2
      _ = A.verts := Finset.sum_attach A.insts (fun a => a.1.card)

end Step

namespace CallOut

/-- **A call, from its classification.**  `F` is the forest the call returns, `P'` the portal set
shared by the `#ι` children, and `cls` sends each input edge to `none` (kept in `F` or `U(F)`) or to
the child that receives it.  The portal budget `4·#ι·|P'| ≤ |P|` is the paper's `t²·2nt/r = n/4`.
Every field is then the definition's own bookkeeping, so a procedure need only produce
`(F, P', cls)`. -/
def ofClass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finset V) (E₀ : Finset E) (F : Finset E) (P' : Finset V) (cls : E → Option ι)
    (hFsub : F ⊆ E₀) (hforest : IsForest G F) (hFcard : F.card ≤ P.card)
    (hP' : P' ⊆ P) (hbudget : 4 * (Fintype.card ι * P'.card) ≤ P.card)
    (hkeep : ∀ e ∈ E₀, cls e = none → e ∈ F ∨ e ∈ unsupp G F)
    (hmove : ∀ e ∈ E₀, ∀ i, cls e = some i → e ∉ F ∧ e ∉ unsupp G F) :
    CallOut G ι where
  P := P
  E₀ := E₀
  F := F
  kidE := fun i => E₀.filter (fun e => cls e = some i)
  kidV := fun _ => P'
  hFsub := hFsub
  hforest := hforest
  hFcard := hFcard
  hkidE := fun _ e he => (Finset.mem_filter.mp he).1
  hkidV := fun _ => hP'
  hkidEdisj := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro e hei hej
    rw [Finset.mem_filter] at hei hej
    exact hij (Option.some.inj (hei.2.symm.trans hej.2))
  hFkid := by
    intro i
    rw [Finset.disjoint_left]
    intro e heF hkid
    exact (hmove e (hFsub heF) i (Finset.mem_filter.mp hkid).2).1 heF
  hUkid := by
    intro i
    rw [Finset.disjoint_left]
    intro e heU hkid
    have he : e ∈ E₀ := (Finset.mem_inter.mp heU).2
    exact (hmove e he i (Finset.mem_filter.mp hkid).2).2 (Finset.mem_inter.mp heU).1
  hcover := by
    intro e he
    cases hcl : cls e with
    | none =>
        rcases hkeep e he hcl with hF | hU
        · exact Or.inl hF
        · exact Or.inr (Or.inl hU)
    | some i => exact Or.inr (Or.inr ⟨i, Finset.mem_filter.mpr ⟨he, hcl⟩⟩)
  hshrink := by
    have hsum : (∑ _i : ι, P'.card) = Fintype.card ι * P'.card := by
      simp [Finset.sum_const, smul_eq_mul]
    rw [hsum]
    exact hbudget

/-- **The childless call.**  If `F` covers the supported part of `E₀`, no child is created and the
portal budget is vacuous.  This is the recursion's base case: `E₀ = ∅` qualifies, and so does any
forest input with `F = E₀` (a forest edge is always supported by its own forest). -/
def ofForest (P : Finset V) (E₀ : Finset E) {F : Finset E}
    (hFsub : F ⊆ E₀) (hforest : IsForest G F) (hFcard : F.card ≤ P.card)
    (hcover : ∀ e ∈ E₀, e ∈ F ∨ e ∈ unsupp G F) : CallOut G Empty where
  P := P
  E₀ := E₀
  F := F
  kidE := fun i => Empty.elim i
  kidV := fun i => Empty.elim i
  hFsub := hFsub
  hforest := hforest
  hFcard := hFcard
  hkidE := fun i => Empty.elim i
  hkidV := fun i => Empty.elim i
  hkidEdisj := fun i => Empty.elim i
  hFkid := fun i => Empty.elim i
  hUkid := fun i => Empty.elim i
  hcover := fun e he => by
    rcases hcover e he with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  hshrink := by simp

/-- **Every forest instance is a leaf call**: take `F = E₀`, which covers itself. -/
theorem nonempty_of_isForest (P : Finset V) (E₀ : Finset E) (h : IsForest G E₀)
    (hcard : E₀.card ≤ P.card) : Nonempty (CallOut G Empty) :=
  ⟨ofForest P E₀ (Finset.Subset.refl E₀) h hcard (fun _e he => Or.inl he)⟩

/-- **A call exists for any interior forest.**  Given any subforest `F ⊆ E₀` with `|F| ≤ |P|`, any
portal set `P' ⊆ P` and any inhabited child type satisfying the budget `4·#ι·|P'| ≤ |P|`, a call
exists: put every edge of `E₀` that is neither in `F` nor unsupported into the distinguished child
`default`, so all other children receive nothing.  The packaging itself never obstructs — the only
content of a call is the choice of `F` (the rounds) and of the numbers. -/
theorem nonempty_of_subforest {ι : Type*} [Fintype ι] [DecidableEq ι] [Inhabited ι]
    (P : Finset V) (E₀ : Finset E) {F : Finset E} {P' : Finset V}
    (hFsub : F ⊆ E₀) (hforest : IsForest G F) (hFcard : F.card ≤ P.card)
    (hP' : P' ⊆ P) (hbudget : 4 * (Fintype.card ι * P'.card) ≤ P.card) :
    Nonempty (CallOut G ι) := by
  classical
  refine ⟨ofClass P E₀ F P' (fun e => if e ∈ F ∨ e ∈ unsupp G F then none else some default)
    hFsub hforest hFcard hP' hbudget ?_ ?_⟩
  · intro e _ hcl
    by_contra h
    rw [ite_eq_right h] at hcl
    exact absurd hcl (by simp)
  · intro e _ i hcl
    by_cases h : e ∈ F ∨ e ∈ unsupp G F
    · rw [ite_eq_left h] at hcl
      exact absurd hcl (by simp)
    · exact not_or.mp h

/-- **`ofClass` keeps `F` away from every child.**  `hmove` says a classified edge lies in neither
`F` nor `U(F)`, so every edge of `F` stays out of all children: the edge the recursion leaves
behind is any edge of the forest the call returns. -/
theorem ofClass_kidE_not_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : Finset V} {E₀ : Finset E} {F : Finset E} {P' : Finset V} {cls : E → Option ι}
    {hFsub : F ⊆ E₀} {hforest : IsForest G F} {hFcard : F.card ≤ P.card} {hP' : P' ⊆ P}
    {hbudget : 4 * (Fintype.card ι * P'.card) ≤ P.card}
    {hkeep : ∀ e ∈ E₀, cls e = none → e ∈ F ∨ e ∈ unsupp G F}
    {hmove : ∀ e ∈ E₀, ∀ i, cls e = some i → e ∉ F ∧ e ∉ unsupp G F}
    {e : E} (heF : e ∈ F) (i : ι) :
    e ∉ (ofClass P E₀ F P' cls hFsub hforest hFcard hP' hbudget hkeep hmove).kidE i := by
  intro hmem
  exact (hmove e (hFsub heF) i (Finset.mem_filter.mp hmem).2).1 heF

end CallOut

/-- **The portal budget of the `t` batch rounds.**  If round `b` contributes a portal set of size
`Q b` with `r·|Q b| ≤ 2n` (`r = 8t³`, i.e. "at most `2n/r` new portals", `Portals.portal_bound`),
then the accumulated portal set `P' ⊆ ⋃_b Q_b` satisfies the call's budget `4·t²·|P'| ≤ n`.  This is
the paper's `t²·2nt/r = n/4` (here `Section36.children_vertices_le` is the equality form). -/
theorem portals_shrink {t n P' : ℕ} (ht : 0 < t) {Q : ℕ → ℕ}
    (hQ : ∀ b ∈ Finset.range t, 8 * t ^ 3 * Q b ≤ 2 * n)
    (hP' : P' ≤ ∑ b ∈ Finset.range t, Q b) : 4 * t ^ 2 * P' ≤ n := by
  set S := ∑ b ∈ Finset.range t, Q b with hS
  have hsum : 8 * t ^ 3 * S ≤ 2 * n * t := by
    have h1 : (∑ b ∈ Finset.range t, 8 * t ^ 3 * Q b) ≤ ∑ _b ∈ Finset.range t, (2 * n) :=
      Finset.sum_le_sum hQ
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at h1
    rw [← Finset.mul_sum, ← hS] at h1
    calc 8 * t ^ 3 * S ≤ t * (2 * n) := h1
      _ = 2 * n * t := by ring
  have h2 : 4 * t ^ 2 * S ≤ n := by
    have hmul : 2 * t * (4 * t ^ 2 * S) ≤ 2 * t * n := by
      calc 2 * t * (4 * t ^ 2 * S) = 8 * t ^ 3 * S := by ring
        _ ≤ 2 * n * t := hsum
        _ = 2 * t * n := by ring
    exact Nat.le_of_mul_le_mul_left hmul (by positivity)
  exact le_trans (Nat.mul_le_mul_left _ hP') h2

/-! ## 7. The recursion: a strategy generates the level chain

A *strategy* answers, for every instance `(P, E₀)`, with a call whose `N` children are indexed by
`Fin N` (the paper's `t²` depends on the depth, so `N` is chosen per call).  The only requirement is
that the call is a call *on the instance it was asked about* (`Strategy.Wf`): a strategy cannot cheat
by returning an answer to a different problem.  Under that requirement

* `Level.next` is the level of all children, `Step.next` its recursion-step geometry (both are
  `Level.allChildren`/`Step.ofCalls` with the strategy substituted);
* `Level.chain` iterates from the root instance, and `LevelChain.chain_step` says every consecutive
  pair is a recursion step, so `LevelChain.verts`/`edges` — hence all of §3.6 — apply to it;
* `display_of_strategy` is `display_of_callout_full` at the root call of the strategy, with `hn`/`hm`
  discharged by `chain_verts`/`chain_edges` instead of assumed.

The hypotheses left in `display_of_strategy` are exactly the *numbers* §3.1–§3.5 produce: per-level
error and child-input bounds, and the root's unsupported-edge and child-input accounts.  Nothing
about the recursion's shape is assumed any more.

*Termination* is the other half of "a strategy really is a procedure": `Strategy.Strict` says a
nonempty instance's children have strictly fewer edges (true of any call, since `F` is nonempty when
`E₀` is and a child only receives edges outside `F`), and `Strategy.Leaf` says an edge-less instance
has no children (`CallOut.ofForest`).  Then `chain_edges_le_card` gives `≤ |E₀| - d` edges at depth
`d`, and `chain_insts_empty_of_le` says every level from `|E₀| + 1` on is empty — the sums of §3.6
cover every level, not just those below a chosen depth. -/

/-- **A recursive strategy**: for each instance, a call with `N` children indexed by `Fin N`. -/
abbrev Strategy (G : WGraph V E) : Type _ :=
  (P : Finset V) → (E₀ : Finset E) → Sigma fun N : ℕ => CallOut G (Fin N)

namespace Strategy

/-- The strategy answers about the instance it was asked about. -/
def Wf (S : Strategy G) : Prop :=
  ∀ (P : Finset V) (E₀ : Finset E), (S P E₀).2.P = P ∧ (S P E₀).2.E₀ = E₀

/-- **Strict decrease**: a nonempty instance's children have strictly fewer edges.  This is what
makes the recursion terminate — `F` is nonempty whenever `E₀` is (it is the rounds' forest), and a
child only receives edges outside `F` (`CallOut.hFkid`). -/
def Strict (S : Strategy G) : Prop :=
  ∀ (P : Finset V) (E₀ : Finset E), E₀.Nonempty → ∀ i, ((S P E₀).2.kidE i).card < E₀.card

/-- **Emptiness is a leaf**: an instance with no edges has no children, so the recursion stops there
(the paper's base case, `CallOut.ofForest`). -/
def Leaf (S : Strategy G) : Prop :=
  ∀ P : Finset V, (S P ∅).1 = 0

/-- **A dropped edge at every instance**: one edge of `E₀` that no child receives.  This is the
data-level form of strict decrease — in the paper it is any edge of the rounds' forest, which
`CallOut.hFkid` keeps away from all children.  Stated over the union of the children's inputs so that
no child index has to be named. -/
def Drops (S : Strategy G) : Prop :=
  ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ →
    e ∉ Finset.univ.biUnion (S P E₀).2.kidE

/-- **A dropped edge forces strict decrease.**  `CallOut.kidE_card_lt` is the whole proof: the child's
input is a subset of `E₀` and misses a known edge of `E₀`. -/
theorem strict_of_drops (S : Strategy G) (hS : Wf S) (h : Drops S) : Strict S := by
  intro P E₀ hne i
  obtain ⟨e, he⟩ := hne
  have hdrop : e ∉ (S P E₀).2.kidE i := fun hmem =>
    h P E₀ e he (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hmem⟩)
  have he' : e ∈ (S P E₀).2.E₀ := (hS P E₀).2.symm ▸ he
  have hlt : ((S P E₀).2.kidE i).card < (S P E₀).2.E₀.card :=
    CallOut.kidE_card_lt (S P E₀).2 i he' hdrop
  rwa [(hS P E₀).2] at hlt

/-- The call on the empty instance: no forest, no unsupported edges, no children. -/
noncomputable def leafOut (P : Finset V) : CallOut G (Fin 0) where
  P := P
  E₀ := ∅
  F := ∅
  kidE := fun i => i.elim0
  kidV := fun i => i.elim0
  hFsub := Finset.empty_subset _
  hforest := IsForest.empty
  hFcard := by simp
  hkidE := fun i => i.elim0
  hkidV := fun i => i.elim0
  hkidEdisj := fun i => i.elim0
  hFkid := fun i => i.elim0
  hUkid := fun i => i.elim0
  hcover := fun e he => by simp at he
  hshrink := by simp

/-- **The recursion's three shape hypotheses, named.**  A strategy that answers about its instance,
drops an edge at every nonempty instance, and is childless at `∅` satisfies all of `Wf`, `Strict`,
`Leaf` — i.e. everything `LevelChain.chain_step` and `chain_insts_empty_of_le` need.  What a
procedure still owes is exactly the call at each instance and the dropped edge. -/
theorem wf_strict_leaf (S : Strategy G) (hS : Wf S) (hd : Drops S) (hl : Leaf S) :
    Wf S ∧ Strict S ∧ Leaf S :=
  ⟨hS, strict_of_drops S hS hd, hl⟩

/-- **A strategy from its interior calls.**  The base case `E₀ = ∅` is decided automatically
(`leafOut`), so a procedure only has to answer on nonempty instances — the shape the paper's procedure
is written in: run the rounds and classify at a nonempty instance, accept immediately at an empty
one. -/
noncomputable def ofInterior
    (c : (P : Finset V) → (E₀ : Finset E) → E₀.Nonempty → Sigma fun N : ℕ => CallOut G (Fin N)) :
    Strategy G :=
  fun P E₀ => if h : E₀.Nonempty then c P E₀ h else ⟨0, leafOut P⟩

/-- The assembled strategy answers about the instance it was asked about, provided the interior calls
do. -/
theorem ofInterior_wf (c : (P : Finset V) → (E₀ : Finset E) → E₀.Nonempty →
      Sigma fun N : ℕ => CallOut G (Fin N))
    (hP : ∀ (P : Finset V) (E₀ : Finset E) (h : E₀.Nonempty), (c P E₀ h).2.P = P)
    (hE : ∀ (P : Finset V) (E₀ : Finset E) (h : E₀.Nonempty), (c P E₀ h).2.E₀ = E₀) :
    Wf (ofInterior c) := by
  intro P E₀
  by_cases h : E₀.Nonempty
  · have hval : ofInterior c P E₀ = c P E₀ h := dite_eq_left h
    rw [hval, hP P E₀ h, hE P E₀ h]
    exact ⟨rfl, rfl⟩
  · have hval : ofInterior c P E₀ = ⟨0, leafOut P⟩ := dite_eq_right h
    rw [hval]
    exact ⟨rfl, (Finset.not_nonempty_iff_eq_empty.mp h).symm⟩

/-- The assembled strategy is childless at the empty instance. -/
theorem ofInterior_leaf (c : (P : Finset V) → (E₀ : Finset E) → E₀.Nonempty →
      Sigma fun N : ℕ => CallOut G (Fin N)) : Leaf (ofInterior c) := by
  intro P
  have hval : ofInterior c P ∅ = ⟨0, leafOut P⟩ := dite_eq_right Finset.not_nonempty_empty
  rw [hval]

/-- **Strict decrease from the interior calls' dropped edges.**  At a nonempty instance the interior
call must keep one edge of `E₀` away from every child; the empty instance has none. -/
theorem ofInterior_strict (c : (P : Finset V) → (E₀ : Finset E) → E₀.Nonempty →
      Sigma fun N : ℕ => CallOut G (Fin N)) (hS : Wf (ofInterior c))
    (hdrops : ∀ (P : Finset V) (E₀ : Finset E) (h : E₀.Nonempty) (e : E), e ∈ E₀ →
      e ∉ Finset.univ.biUnion (c P E₀ h).2.kidE) : Strict (ofInterior c) :=
  strict_of_drops _ hS (by
    intro P E₀ e he
    by_cases h : E₀.Nonempty
    · have hval : ofInterior c P E₀ = c P E₀ h := dite_eq_left h
      rw [hval]
      exact hdrops P E₀ h e he
    · exact absurd ⟨e, he⟩ h)

/-- **What the recursion's shape reduces to.**  A well-formed, strictly decreasing, childless-at-`∅`
strategy exists as soon as every nonempty instance has a call on that instance which keeps one of its
edges away from all children.  Nothing else about the procedure enters the recursion account. -/
theorem exists_strategy_of_interior
    (c : (P : Finset V) → (E₀ : Finset E) → E₀.Nonempty → Sigma fun N : ℕ => CallOut G (Fin N))
    (hP : ∀ (P : Finset V) (E₀ : Finset E) (h : E₀.Nonempty), (c P E₀ h).2.P = P)
    (hE : ∀ (P : Finset V) (E₀ : Finset E) (h : E₀.Nonempty), (c P E₀ h).2.E₀ = E₀)
    (hdrops : ∀ (P : Finset V) (E₀ : Finset E) (h : E₀.Nonempty) (e : E), e ∈ E₀ →
      e ∉ Finset.univ.biUnion (c P E₀ h).2.kidE) :
    ∃ S : Strategy G, Wf S ∧ Strict S ∧ Leaf S :=
  ⟨ofInterior c, ofInterior_wf c hP hE, ofInterior_strict c (ofInterior_wf c hP hE) hdrops,
    ofInterior_leaf c⟩

end Strategy

namespace Level

/-- The next level generated by a strategy. -/
noncomputable def next (A : Level V E) (S : Strategy G) (hS : Strategy.Wf S) : Level V E :=
  allChildren A (fun a => S a.val.1 a.val.2) (fun a => (hS a.val.1 a.val.2).2)

/-- **The levels generated by a strategy**: `L 0` is the root instance and `L (d+1)` its children.
All of §3.6's inequalities concern finitely many levels, so plain iteration suffices — no
well-foundedness is needed to state the account. -/
noncomputable def chain (P : Finset V) (E₀ : Finset E) (S : Strategy G) (hS : Strategy.Wf S) :
    ℕ → Level V E
  | 0 => root P E₀
  | d + 1 => (chain P E₀ S hS d).next S hS

end Level

namespace Step

/-- **A well-formed strategy is one recursion step everywhere.** -/
theorem next (A : Level V E) (S : Strategy G) (hS : Strategy.Wf S) : Step A (A.next S hS) :=
  ofCalls A (fun a => S a.val.1 a.val.2) (fun a => (hS a.val.1 a.val.2).1)
    (fun a => (hS a.val.1 a.val.2).2)

end Step

namespace LevelChain

/-- **The strategy's levels are a recursion chain.** -/
theorem chain_step (P : Finset V) (E₀ : Finset E) (S : Strategy G) (hS : Strategy.Wf S) :
    ∀ d, Step (Level.chain P E₀ S hS d) (Level.chain P E₀ S hS (d + 1)) :=
  fun d => Step.next (Level.chain P E₀ S hS d) S hS

/-- The root level has the root instance's vertex total. -/
theorem chain_verts (P : Finset V) (E₀ : Finset E) (S : Strategy G) (hS : Strategy.Wf S) :
    (Level.chain P E₀ S hS 0).verts = P.card :=
  rfl

/-- The root level has the root instance's edge total. -/
theorem chain_edges (P : Finset V) (E₀ : Finset E) (S : Strategy G) (hS : Strategy.Wf S) :
    (Level.chain P E₀ S hS 0).edges = E₀.card :=
  rfl

/-- **The level edge totals shrink by one per level** under a strictly decreasing strategy: every
instance at depth `d` has at most `|E₀| - d` edges.  This is the well-foundedness of the recursion,
read on the levels. -/
theorem chain_edges_le_card (P : Finset V) (E₀ : Finset E) (S : Strategy G) (hS : Strategy.Wf S)
    (hstr : Strategy.Strict S) (d : ℕ) :
    ∀ b ∈ (Level.chain P E₀ S hS d).insts, b.2.card ≤ E₀.card - d := by
  induction d with
  | zero =>
      intro b hb
      simp only [Level.chain, Level.root, Finset.mem_singleton] at hb
      rw [hb]
      simp
  | succ d ih =>
      intro b hb
      show b.2.card ≤ E₀.card - (d + 1)
      simp only [Level.chain, Level.next, Level.allChildren] at hb
      obtain ⟨a, -, hb'⟩ := Finset.mem_biUnion.mp hb
      obtain ⟨i, -, hbval⟩ := Finset.mem_image.mp hb'
      have ha := ih a.val a.property
      have hsub : (S a.val.1 a.val.2).2.kidE i ⊆ a.val.2 :=
        Finset.Subset.trans ((S a.val.1 a.val.2).2.hkidE i) (hS a.val.1 a.val.2).2.le
      have hgoal : ((S a.val.1 a.val.2).2.kidE i).card ≤ E₀.card - (d + 1) := by
        by_cases hne : a.val.2.Nonempty
        · have hlt : ((S a.val.1 a.val.2).2.kidE i).card < a.val.2.card :=
            hstr a.val.1 a.val.2 hne i
          omega
        · have hnk : ¬ ((S a.val.1 a.val.2).2.kidE i).Nonempty :=
            fun ⟨e, he⟩ => hne ⟨e, hsub he⟩
          rw [Finset.not_nonempty_iff_eq_empty.mp hnk]
          exact Nat.zero_le _
      rw [← hbval]
      exact hgoal

/-- At depth `|E₀|` every instance has an empty edge set. -/
theorem chain_edges_empty (P : Finset V) (E₀ : Finset E) (S : Strategy G) (hS : Strategy.Wf S)
    (hstr : Strategy.Strict S) {b : Inst V E}
    (hb : b ∈ (Level.chain P E₀ S hS E₀.card).insts) : b.2 = ∅ := by
  have h0 : b.2.card = 0 :=
    Nat.le_zero.mp (by simpa using chain_edges_le_card P E₀ S hS hstr E₀.card b hb)
  exact Finset.card_eq_zero.mp h0

/-- Once a level is empty, every later level is empty. -/
theorem chain_insts_succ_empty (P : Finset V) (E₀ : Finset E) (S : Strategy G)
    (hS : Strategy.Wf S) (d : ℕ) (h : (Level.chain P E₀ S hS d).insts = ∅) :
    (Level.chain P E₀ S hS (d + 1)).insts = ∅ := by
  have hunfold : (Level.chain P E₀ S hS (d + 1)).insts =
      (Level.chain P E₀ S hS d).insts.attach.biUnion
        (fun a => Finset.univ.image (fun i => ((S a.val.1 a.val.2).2.kidV i,
          (S a.val.1 a.val.2).2.kidE i))) := rfl
  rw [hunfold, h]
  simp

/-- **The recursion stops**: with strict decrease and a childless leaf at `E₀ = ∅`, the level at
depth `|E₀| + 1` is empty, hence every deeper level is empty too.  This is what lets §3.6's sums
over the levels account for *all* edges, not only those down to a chosen depth. -/
theorem chain_insts_empty_at (P : Finset V) (E₀ : Finset E) (S : Strategy G) (hS : Strategy.Wf S)
    (hstr : Strategy.Strict S) (hleaf : Strategy.Leaf S) :
    (Level.chain P E₀ S hS (E₀.card + 1)).insts = ∅ := by
  rw [← Finset.subset_empty]
  have hunfold : (Level.chain P E₀ S hS (E₀.card + 1)).insts =
      (Level.chain P E₀ S hS E₀.card).insts.attach.biUnion
        (fun a => Finset.univ.image (fun i => ((S a.val.1 a.val.2).2.kidV i,
          (S a.val.1 a.val.2).2.kidE i))) := rfl
  rw [hunfold, Finset.biUnion_subset]
  intro a _
  have hE : a.val.2 = ∅ := chain_edges_empty P E₀ S hS hstr a.property
  rw [hE]
  simp [hleaf a.val.1]

/-- Every level deeper than `|E₀|` is empty. -/
theorem chain_insts_empty_of_le (P : Finset V) (E₀ : Finset E) (S : Strategy G)
    (hS : Strategy.Wf S) (hstr : Strategy.Strict S) (hleaf : Strategy.Leaf S) (d : ℕ)
    (hd : E₀.card + 1 ≤ d) : (Level.chain P E₀ S hS d).insts = ∅ :=
  Nat.le_induction (chain_insts_empty_at P E₀ S hS hstr hleaf)
    (fun n _ ih => chain_insts_succ_empty P E₀ S hS n ih) d hd

/-- **The next level's edges are exactly the calls' child inputs.**  The instances of level `d + 1`
are the children of level `d`'s calls, and equal children can only have empty edge sets (their inputs
are pairwise disjoint), so no edge is lost or counted twice when the children are collected into a
level: the next level's edge total is the sum of all `|Eᵢ|` over the calls at depth `d`. -/
theorem chain_edges_succ (P : Finset V) (E₀ : Finset E) (S : Strategy G) (hS : Strategy.Wf S)
    (d : ℕ) :
    (Level.chain P E₀ S hS (d + 1)).edges =
      ∑ a ∈ (Level.chain P E₀ S hS d).insts, ∑ i, ((S a.1 a.2).2.kidE i).card := by
  classical
  set A := Level.chain P E₀ S hS d
  have hunion : (Level.chain P E₀ S hS (d + 1)).insts.biUnion (·.2) =
      A.insts.attach.biUnion
        (fun a => Finset.univ.biUnion (fun i => ((S a.val.1 a.val.2).2.kidE i))) := by
    simp only [Level.chain, Level.next, Level.allChildren, Finset.biUnion_biUnion,
      Finset.image_biUnion]
    rfl
  have hstep : (Level.chain P E₀ S hS (d + 1)).edges =
      ((Level.chain P E₀ S hS (d + 1)).insts.biUnion (·.2)).card := by
    rw [Level.edges]
    exact (Finset.card_biUnion (fun a ha b hb hab =>
      (Level.chain P E₀ S hS (d + 1)).edisj a ha b hb hab)).symm
  have houter : ∀ a ∈ A.insts.attach, ∀ b ∈ A.insts.attach, a ≠ b →
      Disjoint (Finset.univ.biUnion (fun i => ((S a.val.1 a.val.2).2.kidE i)))
        (Finset.univ.biUnion (fun i => ((S b.val.1 b.val.2).2.kidE i))) := by
    intro a _ b _ hab
    refine Finset.disjoint_left.mpr (fun e hea heb => ?_)
    obtain ⟨i, -, hei⟩ := Finset.mem_biUnion.mp hea
    obtain ⟨j, -, hej⟩ := Finset.mem_biUnion.mp heb
    have h1 : e ∈ a.val.2 := (hS a.val.1 a.val.2).2 ▸ ((S a.val.1 a.val.2).2.hkidE i hei)
    have h2 : e ∈ b.val.2 := (hS b.val.1 b.val.2).2 ▸ ((S b.val.1 b.val.2).2.hkidE j hej)
    exact (Finset.disjoint_left.mp (A.edisj a.val a.property b.val b.property
      (fun h => hab (Subtype.ext h)))) h1 h2
  rw [hstep, hunion, Finset.card_biUnion houter]
  have hconv : (∑ u ∈ A.insts.attach,
        (Finset.univ.biUnion (fun i => ((S u.val.1 u.val.2).2.kidE i))).card)
      = ∑ a ∈ A.insts,
        (Finset.univ.biUnion (fun i => ((S a.1 a.2).2.kidE i))).card :=
    Finset.sum_attach (s := A.insts)
      (f := fun a : Inst V E => (Finset.univ.biUnion (fun i => ((S a.1 a.2).2.kidE i))).card)
  rw [hconv]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  exact Finset.card_biUnion (fun i _ j _ hij => (S a.1 a.2).2.hkidEdisj i j hij)

/-- **Every edge is accounted exactly once** (the telescoping identity): at every level an edge is
either kept in a call's forest, or becomes unsupported at that level; the levels partition `E₀` down
to whatever edge set survives to depth `D`.  So the sum of `|F| + |U(F)|` over the first `D` levels
plus the edges still alive at depth `D` is `|E₀|` — with a terminating strategy (`D = |E₀| + 1`,
`chain_insts_empty_at`) nothing survives. -/
theorem kept_telescope (P : Finset V) (E₀ : Finset E) (S : Strategy G) (hS : Strategy.Wf S) :
    ∀ D : ℕ, (∑ d ∈ Finset.range D, ∑ a ∈ (Level.chain P E₀ S hS d).insts,
        ((S a.1 a.2).2.F.card + (S a.1 a.2).2.U.card)) +
      (Level.chain P E₀ S hS D).edges = E₀.card := by
  intro D
  induction D with
  | zero => simp [Level.chain, Level.root, Level.edges]
  | succ D ih =>
      have hstep := chain_edges_succ P E₀ S hS D
      have hpart : ∀ a ∈ (Level.chain P E₀ S hS D).insts,
          (S a.1 a.2).2.F.card + (S a.1 a.2).2.U.card +
            ∑ i, ((S a.1 a.2).2.kidE i).card = a.2.card := by
        intro a _
        have h := CallOut.partition_eq (S a.1 a.2).2
        rw [(hS a.1 a.2).2] at h
        exact h
      have hsum : (∑ a ∈ (Level.chain P E₀ S hS D).insts,
            ((S a.1 a.2).2.F.card + (S a.1 a.2).2.U.card))
          + ∑ a ∈ (Level.chain P E₀ S hS D).insts, ∑ i, ((S a.1 a.2).2.kidE i).card
          = (Level.chain P E₀ S hS D).edges := by
        rw [← Finset.sum_add_distrib, Level.edges]
        exact Finset.sum_congr rfl hpart
      rw [Finset.sum_range_succ, hstep]
      omega

/-- **Every edge is accounted exactly once in a terminating run.**  At depth `|E₀| + 1` nothing
survives (`chain_insts_empty_at`), so the forest edges kept and the edges rejected to `U(F)` across
*all* levels add up to exactly `|E₀|`: the paper's "each edge is either taken into some forest or
declared unsupported, exactly once", read on the strategy that actually runs. -/
theorem kept_telescope_full (P : Finset V) (E₀ : Finset E) (S : Strategy G)
    (hS : Strategy.Wf S) (hstr : Strategy.Strict S) (hleaf : Strategy.Leaf S) :
    (∑ d ∈ Finset.range (E₀.card + 1), ∑ a ∈ (Level.chain P E₀ S hS d).insts,
        ((S a.1 a.2).2.F.card + (S a.1 a.2).2.U.card)) = E₀.card := by
  have h := kept_telescope P E₀ S hS (E₀.card + 1)
  have h0 : (Level.chain P E₀ S hS (E₀.card + 1)).edges = 0 := by
    rw [Level.edges, chain_insts_empty_at P E₀ S hS hstr hleaf]
    simp
  rw [h0] at h
  simpa using h

end LevelChain

/-- **§3.6's display, from a strategy.**  The root call is `(S P E₀).2` on the instance `(P, E₀)`,
the levels are the ones `S` generates, and `hn`/`hm` of `display_of_callout_full` are
`LevelChain.chain_verts`/`chain_edges`.  What remains assumed is exactly §3.1–§3.5's numerical
output: `herr`/`hin` the per-level error and child-input bounds, `hU`/`hSE` the root's
unsupported-edge and child-input accounts. -/
theorem display_of_strategy (P : Finset V) (E₀ : Finset E) (S : Strategy G) (hS : Strategy.Wf S)
    {γ ε : ℝ} (hγ : 0 < γ) (hε : 0 < ε) (hγε : 16 ≤ ε * γ)
    (hnm : ((S P E₀).2.P.card : ℝ) ≤ 2 * ((S P E₀).2.E₀.card : ℝ))
    {D : ℕ} {errL inL : ℕ → ℕ}
    (herr : ∀ d ∈ Finset.range D, (errL d : ℝ) ≤
      (γ * ((d : ℝ) + 1) ^ 3) ^ 2 *
          Real.sqrt (((Level.chain P E₀ S hS d).edges : ℝ) *
            ((Level.chain P E₀ S hS d).verts : ℝ)) +
        4 * ((Level.chain P E₀ S hS d).edges : ℝ) / (γ * ((d : ℝ) + 1) ^ 3))
    (hin : ∀ d ∈ Finset.range D, (inL d : ℝ) ≤
        4 * ((Level.chain P E₀ S hS d).edges : ℝ) / (γ * ((d : ℝ) + 1) ^ 3))
    (hU : ((S P E₀).2.U).card ≤ ∑ d ∈ Finset.range D, errL d)
    (hSE : ∑ i, ((S P E₀).2.kidE i).card ≤ ∑ d ∈ Finset.range D, inL d) :
    ((S P E₀).2.F.card : ℝ) + (((S P E₀).2.U).card : ℝ) +
        ((∑ i, ((S P E₀).2.kidE i).card : ℕ) : ℝ) ≤
      ε * ((S P E₀).2.E₀.card : ℝ) +
        (Real.sqrt 2 + γ ^ 2 * 40000) *
          Real.sqrt (((S P E₀).2.E₀.card : ℝ) * ((S P E₀).2.P.card : ℝ)) :=
  display_of_callout_full (S P E₀).2 hγ hε hγε hnm
    (L := Level.chain P E₀ S hS) (LevelChain.chain_step P E₀ S hS)
    (by simp [LevelChain.chain_verts, (hS P E₀).1])
    (by simp [LevelChain.chain_edges, (hS P E₀).2])
    herr hin hU hSE

/-- **§3.6 from one procedure.**  The paper's procedure is uniform: the same call is made on every
subproblem, so the per-level sums of `display_of_strategy` follow from per-*instance* bounds with the
depth's own `t = γ(d+1)³`.  `errF a`/`inF a` are the error count and the child-input count of the
call at instance `a`; the level sums are built by `Level.errors_le`/`Level.inputs_le`.  What is still
assumed is exactly the two per-call numeric outputs of §3.1–§3.5 and the root's charging of `U(F)`
and the children to the levels. -/
theorem display_of_strategy_of_uniform (P : Finset V) (E₀ : Finset E) (S : Strategy G)
    (hS : Strategy.Wf S)
    {γ ε : ℝ} (hγ : 0 < γ) (hε : 0 < ε) (hγε : 16 ≤ ε * γ)
    (hnm : ((S P E₀).2.P.card : ℝ) ≤ 2 * ((S P E₀).2.E₀.card : ℝ))
    {D : ℕ} (errF inF : Inst V E → ℕ)
    (herr : ∀ d ∈ Finset.range D, ∀ a ∈ (Level.chain P E₀ S hS d).insts,
      (errF a : ℝ) ≤ (γ * ((d : ℝ) + 1) ^ 3) ^ 2 *
          Real.sqrt ((a.2.card : ℝ) * (a.1.card : ℝ)) +
        4 * (a.2.card : ℝ) / (γ * ((d : ℝ) + 1) ^ 3))
    (hin : ∀ d ∈ Finset.range D, ∀ a ∈ (Level.chain P E₀ S hS d).insts,
      (inF a : ℝ) ≤ 4 * (a.2.card : ℝ) / (γ * ((d : ℝ) + 1) ^ 3))
    (hU : ((S P E₀).2.U).card ≤
      ∑ d ∈ Finset.range D, ∑ a ∈ (Level.chain P E₀ S hS d).insts, errF a)
    (hSE : ∑ i, ((S P E₀).2.kidE i).card ≤
      ∑ d ∈ Finset.range D, ∑ a ∈ (Level.chain P E₀ S hS d).insts, inF a) :
    ((S P E₀).2.F.card : ℝ) + (((S P E₀).2.U).card : ℝ) +
        ((∑ i, ((S P E₀).2.kidE i).card : ℕ) : ℝ) ≤
      ε * ((S P E₀).2.E₀.card : ℝ) +
        (Real.sqrt 2 + γ ^ 2 * 40000) *
          Real.sqrt (((S P E₀).2.E₀.card : ℝ) * ((S P E₀).2.P.card : ℝ)) :=
  display_of_strategy P E₀ S hS hγ hε hγε hnm
    (errL := fun d => ∑ a ∈ (Level.chain P E₀ S hS d).insts, errF a)
    (inL := fun d => ∑ a ∈ (Level.chain P E₀ S hS d).insts, inF a)
    (fun d hd => by
      rw [Nat.cast_sum]
      exact Level.errors_le (by positivity) _ errF (fun a ha => herr d hd a ha))
    (fun d hd => by
      rw [Nat.cast_sum]
      exact Level.inputs_le _ inF (fun a ha => hin d hd a ha))
    hU hSE

/-- **The display with no root-level accounting left.**  `hU`/`hSE` of
`display_of_strategy_of_uniform` concern the root call alone, and the root sits alone at level `0`
(`Level.chain … 0 = Level.root P E₀`), so they follow from the *per-instance* accounts
`|U_a| ≤ errF a` and `Σᵢ|kidE_a i| ≤ inF a` taken at the root.  What remains assumed is exactly
§3.1–§3.5's per-call numeric output, now at every instance of every level down to depth `|E₀|`. -/
theorem display_of_strategy_of_calls (P : Finset V) (E₀ : Finset E) (S : Strategy G)
    (hS : Strategy.Wf S)
    {γ ε : ℝ} (hγ : 0 < γ) (hε : 0 < ε) (hγε : 16 ≤ ε * γ)
    (hnm : ((S P E₀).2.P.card : ℝ) ≤ 2 * ((S P E₀).2.E₀.card : ℝ))
    (errF inF : Inst V E → ℕ)
    (herror : ∀ d, d ≤ E₀.card → ∀ a ∈ (Level.chain P E₀ S hS d).insts,
      (errF a : ℝ) ≤ (γ * ((d : ℝ) + 1) ^ 3) ^ 2 *
          Real.sqrt ((a.2.card : ℝ) * (a.1.card : ℝ)) +
        4 * (a.2.card : ℝ) / (γ * ((d : ℝ) + 1) ^ 3))
    (hinF : ∀ d, d ≤ E₀.card → ∀ a ∈ (Level.chain P E₀ S hS d).insts,
      (inF a : ℝ) ≤ 4 * (a.2.card : ℝ) / (γ * ((d : ℝ) + 1) ^ 3))
    (hUinst : ∀ d, d ≤ E₀.card → ∀ a ∈ (Level.chain P E₀ S hS d).insts,
      ((S a.1 a.2).2.U).card ≤ errF a)
    (hSEinst : ∀ d, d ≤ E₀.card → ∀ a ∈ (Level.chain P E₀ S hS d).insts,
      (∑ i, ((S a.1 a.2).2.kidE i).card) ≤ inF a) :
    ((S P E₀).2.F.card : ℝ) + (((S P E₀).2.U).card : ℝ) +
        ((∑ i, ((S P E₀).2.kidE i).card : ℕ) : ℝ) ≤
      ε * ((S P E₀).2.E₀.card : ℝ) +
        (Real.sqrt 2 + γ ^ 2 * 40000) *
          Real.sqrt (((S P E₀).2.E₀.card : ℝ) * ((S P E₀).2.P.card : ℝ)) := by
  have hroot : (P, E₀) ∈ (Level.chain P E₀ S hS 0).insts := by
    simp [Level.chain, Level.root]
  refine display_of_strategy_of_uniform P E₀ S hS hγ hε hγε hnm errF inF
    (fun d hd a ha => herror d (Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)) a ha)
    (fun d hd a ha => hinF d (Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)) a ha)
    ?_ ?_
  · have hU0 : ((S P E₀).2.U).card ≤ errF (P, E₀) :=
      hUinst 0 (Nat.zero_le _) (P, E₀) hroot
    have h0 : (∑ a ∈ (Level.chain P E₀ S hS 0).insts, errF a) = errF (P, E₀) := by
      simp [Level.chain, Level.root]
    have hle := Finset.single_le_sum
      (f := fun d => ∑ a ∈ (Level.chain P E₀ S hS d).insts, errF a)
      (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.succ_pos E₀.card))
    calc ((S P E₀).2.U).card ≤ errF (P, E₀) := hU0
      _ = ∑ a ∈ (Level.chain P E₀ S hS 0).insts, errF a := h0.symm
      _ ≤ ∑ d ∈ Finset.range (E₀.card + 1),
            ∑ a ∈ (Level.chain P E₀ S hS d).insts, errF a := hle
  · have hSE0 : (∑ i, ((S P E₀).2.kidE i).card) ≤ inF (P, E₀) :=
      hSEinst 0 (Nat.zero_le _) (P, E₀) hroot
    have h0 : (∑ a ∈ (Level.chain P E₀ S hS 0).insts, inF a) = inF (P, E₀) := by
      simp [Level.chain, Level.root]
    have hle := Finset.single_le_sum
      (f := fun d => ∑ a ∈ (Level.chain P E₀ S hS d).insts, inF a)
      (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.succ_pos E₀.card))
    calc (∑ i, ((S P E₀).2.kidE i).card) ≤ inF (P, E₀) := hSE0
      _ = ∑ a ∈ (Level.chain P E₀ S hS 0).insts, inF a := h0.symm
      _ ≤ ∑ d ∈ Finset.range (E₀.card + 1),
            ∑ a ∈ (Level.chain P E₀ S hS d).insts, inF a := hle

/-- **The same, with the procedure's honest per-call input.**  `hinF` now says `inF a ≤ errF a +
C·t²·n_a` — the rejected edges already counted by `errF`, plus the per-round MSF calls on the
instance's `n_a` vertices — instead of the rejected-edge-only `4m_a/t`.  The root display then holds
with `C_ε = √2 + γ²·40000·(2 + √2·C)`. -/
theorem display_of_strategy_of_calls_rest (P : Finset V) (E₀ : Finset E) (S : Strategy G)
    (hS : Strategy.Wf S)
    {γ ε C : ℝ} (hγ : 0 < γ) (hε : 0 < ε) (hγε : 16 ≤ ε * γ) (hC : 0 ≤ C)
    (hnm : ((S P E₀).2.P.card : ℝ) ≤ 2 * ((S P E₀).2.E₀.card : ℝ))
    (errF inF : Inst V E → ℕ)
    (herror : ∀ d, d ≤ E₀.card → ∀ a ∈ (Level.chain P E₀ S hS d).insts,
      (errF a : ℝ) ≤ (γ * ((d : ℝ) + 1) ^ 3) ^ 2 *
          Real.sqrt ((a.2.card : ℝ) * (a.1.card : ℝ)) +
        4 * (a.2.card : ℝ) / (γ * ((d : ℝ) + 1) ^ 3))
    (hinF : ∀ d, d ≤ E₀.card → ∀ a ∈ (Level.chain P E₀ S hS d).insts,
      (inF a : ℝ) ≤ (errF a : ℝ) +
        C * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 * (a.1.card : ℝ)))
    (hUinst : ∀ d, d ≤ E₀.card → ∀ a ∈ (Level.chain P E₀ S hS d).insts,
      ((S a.1 a.2).2.U).card ≤ errF a)
    (hSEinst : ∀ d, d ≤ E₀.card → ∀ a ∈ (Level.chain P E₀ S hS d).insts,
      (∑ i, ((S a.1 a.2).2.kidE i).card) ≤ inF a) :
    ((S P E₀).2.F.card : ℝ) + (((S P E₀).2.U).card : ℝ) +
        ((∑ i, ((S P E₀).2.kidE i).card : ℕ) : ℝ) ≤
      ε * ((S P E₀).2.E₀.card : ℝ) +
        (Real.sqrt 2 + γ ^ 2 * (40000 * (2 + Real.sqrt 2 * C))) *
          Real.sqrt (((S P E₀).2.E₀.card : ℝ) * ((S P E₀).2.P.card : ℝ)) := by
  have hroot : (P, E₀) ∈ (Level.chain P E₀ S hS 0).insts := by
    simp [Level.chain, Level.root]
  refine display_of_callout_rest (S P E₀).2 hγ hε hγε hC hnm
    (L := Level.chain P E₀ S hS) (LevelChain.chain_step P E₀ S hS)
    (by simp [LevelChain.chain_verts, (hS P E₀).1])
    (by simp [LevelChain.chain_edges, (hS P E₀).2])
    (errL := fun d => ∑ a ∈ (Level.chain P E₀ S hS d).insts, errF a)
    (inL := fun d => ∑ a ∈ (Level.chain P E₀ S hS d).insts, inF a)
    (fun d hd => by
      rw [Nat.cast_sum]
      exact Level.errors_le (by positivity) _
        errF (fun a ha => herror d (Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)) a ha))
    (fun d hd => by
      rw [Nat.cast_sum, Nat.cast_sum]
      exact Level.inputs_le_err _ errF inF
        (fun a ha => hinF d (Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)) a ha))
    ?_ ?_
  · have hU0 : ((S P E₀).2.U).card ≤ errF (P, E₀) :=
      hUinst 0 (Nat.zero_le _) (P, E₀) hroot
    have h0 : (∑ a ∈ (Level.chain P E₀ S hS 0).insts, errF a) = errF (P, E₀) := by
      simp [Level.chain, Level.root]
    have hle := Finset.single_le_sum
      (f := fun d => ∑ a ∈ (Level.chain P E₀ S hS d).insts, errF a)
      (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.succ_pos E₀.card))
    calc ((S P E₀).2.U).card ≤ errF (P, E₀) := hU0
      _ = ∑ a ∈ (Level.chain P E₀ S hS 0).insts, errF a := h0.symm
      _ ≤ ∑ d ∈ Finset.range (E₀.card + 1),
            ∑ a ∈ (Level.chain P E₀ S hS d).insts, errF a := hle
  · have hSE0 : (∑ i, ((S P E₀).2.kidE i).card) ≤ inF (P, E₀) :=
      hSEinst 0 (Nat.zero_le _) (P, E₀) hroot
    have h0 : (∑ a ∈ (Level.chain P E₀ S hS 0).insts, inF a) = inF (P, E₀) := by
      simp [Level.chain, Level.root]
    have hle := Finset.single_le_sum
      (f := fun d => ∑ a ∈ (Level.chain P E₀ S hS d).insts, inF a)
      (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.succ_pos E₀.card))
    calc (∑ i, ((S P E₀).2.kidE i).card) ≤ inF (P, E₀) := hSE0
      _ = ∑ a ∈ (Level.chain P E₀ S hS 0).insts, inF a := h0.symm
      _ ≤ ∑ d ∈ Finset.range (E₀.card + 1),
            ∑ a ∈ (Level.chain P E₀ S hS d).insts, inF a := hle

/-! ## 8. Loops: what the recursion's termination really assumes -/

/-- A loop is supported by *every* edge set: its two endpoints are the same vertex, joined by the
empty walk. -/
theorem supported_of_loop {F : Finset E} {e : E} (h : G.src e = G.dst e) :
    supported G F e := by
  unfold supported
  rw [h]
  exact Conn.refl _

/-- A forest contains no loops (`IsForest.add` demands `src ≠ dst`). -/
theorem IsForest.src_ne_dst {F : Finset E} (h : IsForest G F) :
    ∀ e ∈ F, G.src e ≠ G.dst e := by
  induction h with
  | empty => intro e he; simp at he
  | add hF hloop hn ih =>
      intro e he
      rw [Finset.mem_insert] at he
      rcases he with rfl | he
      · exact hloop
      · exact ih e he

/-- **Without loops nothing is supported by the empty forest**, so the whole edge set is `U(∅)`. -/
theorem unsupp_empty_of_loopfree (hloop : ∀ e : E, G.src e ≠ G.dst e) :
    unsupp G ∅ = Finset.univ := by
  ext e
  rw [mem_unsupp]
  constructor
  · intro _; exact Finset.mem_univ e
  · intro _ hs
    have hs' : Conn G (∅ : Finset E) (G.src e) (G.dst e) := by
      unfold supported at hs
      simpa using hs
    exact hloop e (conn_empty_eq hs')

namespace Strategy

/-- **A loop makes strict decrease impossible.**  On the instance `{e}` a loop can be in no forest
(`IsForest.src_ne_dst`), is in no `U(F)` (`supported_of_loop`), so `hcover` forces it into some child;
that child's input is then the whole instance and `CallOut.kidE_card_lt` cannot apply.  The paper's
MST setting has no loops; this theorem says the hypothesis is not a convenience but a necessity for
the recursion account as stated. -/
theorem not_strict_of_loop (e₀ : E) (hloop : G.src e₀ = G.dst e₀) (S : Strategy G) (hS : Wf S) :
    ¬ Strategy.Strict S := by
  classical
  intro hstr
  have hne : ({e₀} : Finset E).Nonempty := ⟨e₀, Finset.mem_singleton_self e₀⟩
  obtain ⟨i, hi⟩ : ∃ i, e₀ ∈ (S (∅ : Finset V) {e₀}).2.kidE i := by
    rcases (S (∅ : Finset V) {e₀}).2.hcover e₀ ((hS ∅ {e₀}).2.symm ▸ Finset.mem_singleton_self e₀) with
      heF | heU | ⟨i, hi⟩
    · exact absurd hloop ((S (∅ : Finset V) {e₀}).2.hforest.src_ne_dst e₀ heF)
    · exact absurd (supported_of_loop (F := (S (∅ : Finset V) {e₀}).2.F) hloop)
        (mem_unsupp.mp heU)
    · exact ⟨i, hi⟩
  have hcard : ((S (∅ : Finset V) {e₀}).2.kidE i).card = 1 := by
    have hsub : (S (∅ : Finset V) {e₀}).2.kidE i ⊆ ({e₀} : Finset E) :=
      fun x hx => (hS ∅ {e₀}).2 ▸ ((S (∅ : Finset V) {e₀}).2.hkidE i hx)
    have hge : ({e₀} : Finset E) ⊆ (S (∅ : Finset V) {e₀}).2.kidE i := by
      intro x hx
      rw [Finset.mem_singleton] at hx
      subst hx
      exact hi
    rw [Finset.Subset.antisymm hsub hge, Finset.card_singleton]
  have hlt : ((S (∅ : Finset V) {e₀}).2.kidE i).card < 1 := by
    simpa using hstr (∅ : Finset V) {e₀} hne i
  omega

/-- **The recursion interface is inhabited when the graph has no loops.**  Classify every edge as
kept (`cls = none`): with no loops every edge lies in `U(∅)`, so the single child receives nothing,
the dropped edge is any edge of a nonempty instance, and the empty instance has no children at all.
This is the degenerate strategy — it recurses in name only — but it shows that `Wf`/`Strict`/`Leaf`
are consistent, and `not_strict_of_loop` shows that loop-freeness is exactly what makes them so. -/
noncomputable def emptyClassCall (hloop : ∀ e : E, G.src e ≠ G.dst e)
    (P : Finset V) (E₀ : Finset E) (_h : E₀.Nonempty) :
    Sigma fun N : ℕ => CallOut G (Fin N) :=
  ⟨1, CallOut.ofClass P E₀ ∅ ∅ (fun _ => none)
      (Finset.empty_subset E₀) IsForest.empty (Nat.zero_le _)
      (Finset.empty_subset P) (by simp)
      (fun _e _ hcl => Or.inr (by simp [unsupp_empty_of_loopfree hloop]))
      (fun _e _ i hcl => absurd hcl (by simp))⟩

theorem exists_strict_of_loopfree (hloop : ∀ e : E, G.src e ≠ G.dst e) :
    ∃ S : Strategy G, Wf S ∧ Strict S ∧ Leaf S := by
  classical
  refine exists_strategy_of_interior (emptyClassCall hloop) (fun P E₀ _ => rfl) (fun P E₀ _ => rfl)
    ?_
  intro P E₀ h e he hmem
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hmem
  exact absurd (Finset.mem_filter.mp hi).2 (by simp)

end Strategy

end DLMST