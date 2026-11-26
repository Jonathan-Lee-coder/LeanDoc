import DLMST.BoruvkaHalving
import DLMST.BoruvkaPhase

/-!
# Instance-relative components: the counting base of the phase contraction

`BoruvkaHalving` measures components on the whole graph (`compCount G F` counts every vertex of `V`,
isolated ones included), which is the right notion for a run rooted at all of `V`.  The recursion's
calls, however, are made on *instances* `(P, E₀)` — a subset of vertices, a subset of edges — and
the `hn` slot of the cost recursion (`Strategy.cost_linear_of_contraction`) asks for the instance's
own vertex count after `2j` phases.  `compCount G F` cannot express that: a vertex outside `P` is a
singleton component of `compCount` but belongs to no instance component.

This file supplies the counting half of the instance-level theory:

* `compOn G P F v` — the part of `F`'s component of `v` inside `P`; `compCountOn G P F` — the number
  of instance components.  When every edge of `F` has both ends in `P`, a vertex outside `P` is
  isolated (`comp_eq_singleton_of_notMem`) and inside-P components are exactly the global ones
  (`compOn_eq_comp`), so `compCount G F = |V \ P| + compCountOn G P F`
  (`compCount_eq_sdiff_add_compCountOn`);
* `card_add_compCountOn` — the instance identity `|F| + #components = |P|`, the analogue of
  `ForestCard.card_add_compCount` that the phase halving consumes;
* `compCountOn_insert` — a joining edge drops the instance component count by exactly one.

* `compCountOn_halves` — one phase halves the instance component count, ported verbatim from
  `BoruvkaHalving.compCount_halves` with `P.image (compOn G P F)` in place of
  `univ.image (comp G F)`; `compCountOn_pow_halves` / `compCountOn_le_real` divide by `2^k`.
  Starting from the empty forest, `compCountOn G P (F k) ≤ |P| / 2^k` is the instance-level `hn`
  slot — the vertex count *of the instance*, which the global `compCount` could not state.

* `four_mul_compCountOn_le` / `four_mul_card_le_of_phases` — the `hshrink` shape
  `4·|kidV| ≤ |P|` *derived* from `2j ≥ 2` phases (a child vertex set with one vertex per
  component injects into the component image, `card_le_compCountOn_of_pairwise_not_conn`);
* `hcontract_of_phases` — the real-valued contraction hypothesis of
  `Strategy.cost_linear_of_contraction`, derived from the phase chain plus the child's edge budget
  `|P| ≤ 2|E_child|`.

What is not here yet: the driver data that produces, for a call `(P, E₀)`, such a phase chain
(`hstep`/`hph`/`hcover` on `compOn`) and identifies `kidV`/`kidE` with the component image and the
child's edge set — the `.P = P`口径 gap recorded in `CostLinear.lean`.
-/

namespace DLMST

open Classical

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

/-- `compOn G P F v`: the vertices of `P` reachable from `v` using only edges of `F`. -/
noncomputable def compOn (G : WGraph V E) (P : Finset V) (F : Finset E) (v : V) : Finset V :=
  P.filter (fun x => Conn G F v x)

theorem mem_compOn {P : Finset V} {F : Finset E} {v x : V} :
    x ∈ compOn G P F v ↔ x ∈ P ∧ Conn G F v x := by
  simp [compOn]

theorem compOn_subset (P : Finset V) (F : Finset E) (v : V) :
    compOn G P F v ⊆ P := Finset.filter_subset _ _

/-- Vertices in the same `F`-component have the same instance component. -/
theorem compOn_congr {P : Finset V} {F : Finset E} {v w : V} (h : Conn G F v w) :
    compOn G P F v = compOn G P F w := by
  ext x
  rw [mem_compOn, mem_compOn]
  exact ⟨fun hx => ⟨hx.1, h.symm.trans hx.2⟩, fun hx => ⟨hx.1, h.trans hx.2⟩⟩

/-- The number of components of the instance `(P, F)`: the components meeting `P`, counted once. -/
noncomputable def compCountOn (G : WGraph V E) (P : Finset V) (F : Finset E) : ℕ :=
  (P.image (compOn G P F)).card

/-- **Connectivity preserves membership when `P` is closed under `F`'s edges.** -/
theorem mem_conn_iff {P : Finset V} {F : Finset E}
    (hP : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P) {u v : V} (h : Conn G F u v) :
    (u ∈ P ↔ v ∈ P) := by
  induction h with
  | refl w => exact Iff.rfl
  | step e he => exact ⟨fun _ => (hP e he).2, fun _ => (hP e he).1⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- **A trail starting outside `P` never moves**, when every edge of `F` has both ends in `P`. -/
theorem eq_of_conn_of_notMem {P : Finset V} {F : Finset E}
    (hP : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P) {u v : V} (h : Conn G F u v) (hu : u ∉ P) :
    v = u := by
  revert hu
  induction h with
  | refl w => exact fun _ => rfl
  | step e he => exact fun h => absurd (hP e he).1 h
  | symm hab ih => exact fun hv => (ih ((mem_conn_iff hP hab).not.mpr hv)).symm
  | trans hab hbc ihab ihbc =>
      exact fun hu => (ihbc (ihab hu ▸ hu)).trans (ihab hu)

/-- **Inside the instance, the instance component is the global one.**  Every edge of `F` has its
ends in `P`, so a trail from `v ∈ P` never leaves `P`. -/
theorem compOn_eq_comp {P : Finset V} {F : Finset E}
    (hP : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P) {v : V} (hv : v ∈ P) :
    compOn G P F v = comp G F v := by
  ext x
  rw [mem_compOn, mem_comp]
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨(mem_conn_iff hP h).mp hv, h⟩

/-- **Outside the instance, a vertex is isolated.**  If every edge of `F` has both ends in `P`, a
trail starting outside `P` never moves. -/
theorem comp_eq_singleton_of_notMem {P : Finset V} {F : Finset E}
    (hP : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P) {v : V} (hv : v ∉ P) :
    comp G F v = ({v} : Finset V) := by
  ext x
  rw [mem_comp, Finset.mem_singleton]
  exact ⟨fun h => eq_of_conn_of_notMem hP h hv, fun hx => by rw [hx]; exact Conn.refl v⟩

/-- **The global component count splits into the outside vertices and the instance's components.** -/
theorem compCount_eq_sdiff_add_compCountOn {P : Finset V} {F : Finset E}
    (hP : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P) :
    compCount G F = (Finset.univ \ P).card + compCountOn G P F := by
  classical
  have hsplit : (Finset.univ : Finset V).image (comp G F) =
      P.image (compOn G P F) ∪ (Finset.univ \ P).image (fun v => ({v} : Finset V)) := by
    ext s
    constructor
    · intro hs
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hs
      by_cases hv : v ∈ P
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨v, hv, compOn_eq_comp hP hv⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
          ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv⟩,
            (comp_eq_singleton_of_notMem hP hv).symm⟩))
    · intro hs
      rcases Finset.mem_union.mp hs with hs | hs
      · obtain ⟨v, hv, hvs⟩ := Finset.mem_image.mp hs
        exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, (compOn_eq_comp hP hv).symm.trans hvs⟩
      · obtain ⟨v, hv, hvs⟩ := Finset.mem_image.mp hs
        exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v,
          (comp_eq_singleton_of_notMem hP (Finset.mem_sdiff.mp hv).2).trans hvs⟩
  have hdisj : Disjoint (P.image (compOn G P F))
      ((Finset.univ \ P).image (fun v => ({v} : Finset V))) := by
    rw [Finset.disjoint_left]
    intro s hs hs'
    obtain ⟨u, _, hsu⟩ := Finset.mem_image.mp hs
    obtain ⟨v, hv, hvs⟩ := Finset.mem_image.mp hs'
    have hvP : v ∈ P := compOn_subset P F u (hsu.symm ▸ (hvs ▸ Finset.mem_singleton_self v))
    exact (Finset.mem_sdiff.mp hv).2 hvP
  have hcard_out : ((Finset.univ \ P).image (fun v => ({v} : Finset V))).card =
      (Finset.univ \ P).card :=
    Finset.card_image_of_injective _ (fun a b h => by
      simpa using congrArg (fun s : Finset V => a ∈ s) h)
  rw [compCount, compCountOn, hsplit, Finset.card_union_of_disjoint hdisj, hcard_out]
  exact Nat.add_comm _ _

/-- **The instance component identity**: `|F| + #components = |P|` for a forest whose edges all
have their ends in `P`.  This is `ForestCard.card_add_compCount` at an instance, and it is what the
phase halving spends (`|F ∪ A| + c' = |P|` against `|F| + c = |P|`). -/
theorem card_add_compCountOn {P : Finset V} {F : Finset E} (hF : IsForest G F)
    (hP : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P) :
    F.card + compCountOn G P F = P.card := by
  have hg := card_add_compCount (G := G) hF
  have hb := compCount_eq_sdiff_add_compCountOn (G := G) hP
  have hs : (Finset.univ \ P).card + P.card = Fintype.card V := by
    have h := Finset.card_sdiff_add_card_inter (s := (Finset.univ : Finset V)) (t := P)
    rwa [Finset.univ_inter, Finset.card_univ] at h
  omega

/-- **A joining edge drops the instance's component count by exactly one.** -/
theorem compCountOn_insert {P : Finset V} {F : Finset E} {e : E} (hF : IsForest G F)
    (hP : ∀ e' ∈ F, G.src e' ∈ P ∧ G.dst e' ∈ P)
    (hsP : G.src e ∈ P) (hdP : G.dst e ∈ P) (hloop : G.src e ≠ G.dst e)
    (hsep : ¬ Conn G F (G.src e) (G.dst e)) :
    compCountOn G P (insert e F) = compCountOn G P F - 1 := by
  have hP' : ∀ e' ∈ insert e F, G.src e' ∈ P ∧ G.dst e' ∈ P := by
    intro e' he'
    rcases Finset.mem_insert.mp he' with rfl | he'
    · exact ⟨hsP, hdP⟩
    · exact hP e' he'
  have hF' : IsForest G (insert e F) := IsForest.add hF hloop hsep
  have h1 := card_add_compCountOn (G := G) hF hP
  have h2 := card_add_compCountOn (G := G) hF' hP'
  have hne : e ∉ F := not_mem_of_not_conn hsep
  have hc : (insert e F).card = F.card + 1 := Finset.card_insert_of_notMem hne
  omega

/-! ### The instance-level phase halving -/

theorem compOn_empty_eq (P : Finset V) {v : V} (hv : v ∈ P) :
    compOn G P (∅ : Finset E) v = {v} := by
  ext x
  rw [mem_compOn, Finset.mem_singleton]
  constructor
  · rintro ⟨_, hconn⟩
    exact conn_empty hconn
  · intro hx
    rw [hx]
    exact ⟨hv, Conn.refl _⟩

theorem compOn_empty_of_notMem {P : Finset V} {v : V} (hv : v ∉ P) :
    compOn G P (∅ : Finset E) v = ∅ := by
  rw [compOn]
  refine Finset.filter_false_of_mem ?_
  intro x hx hconn
  exact hv (conn_empty hconn ▸ hx)

theorem compCountOn_empty (P : Finset V) : compCountOn G P (∅ : Finset E) = P.card := by
  have hfun : compOn G P (∅ : Finset E) = fun v => if v ∈ P then ({v} : Finset V) else ∅ := by
    funext v
    by_cases hv : v ∈ P
    · rw [ite_eq_left hv, compOn_empty_eq P hv]
    · rw [ite_eq_right hv, compOn_empty_of_notMem hv]
  rw [compCountOn, hfun]
  have himg : Finset.image (fun v => if v ∈ P then ({v} : Finset V) else ∅) P
      = Finset.image (fun v => ({v} : Finset V)) P := by
    refine Finset.image_congr ?_
    intro v hv
    exact ite_eq_left hv
  rw [himg, Finset.card_image_of_injOn]
  intro v _ w _ hvw
  exact Finset.singleton_inj.mp hvw

/-- **The counting core of the halving.**  Everything `compCountOn_halves` uses about a phase is:
`F ∪ A` is a forest, `A` misses `F`, all ends lie in `P`, and `A` covers the instance components.
Any phase predicate (tail form, witness form, ambient set) can feed this. -/
theorem compCountOn_halves_of {P : Finset V} {F A : Finset E} (hF : IsForest G F)
    (hFA : IsForest G (F ∪ A)) (hdisj : Disjoint F A)
    (hP : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P)
    (hPU : ∀ e ∈ F ∪ A, G.src e ∈ P ∧ G.dst e ∈ P)
    (hcover : ∀ C ∈ P.image (compOn G P F),
      ∃ e ∈ A, compOn G P F (G.src e) = C ∨ compOn G P F (G.dst e) = C) :
    2 * compCountOn G P (F ∪ A) ≤ compCountOn G P F := by
  have hc : compCountOn G P F ≤ 2 * A.card := by
    set S : Finset (Finset V) := P.image (compOn G P F) with hS
    set T : Finset (Finset V) :=
      A.biUnion (fun e => ({compOn G P F (G.src e), compOn G P F (G.dst e)} : Finset (Finset V)))
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
          ({compOn G P F (G.src e), compOn G P F (G.dst e)} : Finset (Finset V)).card) :=
      Finset.card_biUnion_le
    have htwo : ∀ e ∈ A,
        ({compOn G P F (G.src e), compOn G P F (G.dst e)} : Finset (Finset V)).card ≤ 2 :=
      fun e _ => Finset.card_le_two
    calc compCountOn G P F = S.card := by rw [compCountOn, hS]
      _ ≤ T.card := Finset.card_le_card hsub
      _ ≤ Finset.sum A (fun _ => 2) := le_trans hTle (Finset.sum_le_sum htwo)
      _ = 2 * A.card := by
          rw [Finset.sum_const_nat (fun _ _ => rfl), Nat.mul_comm]
  have h1 := card_add_compCountOn (G := G) hF hP
  have h2 := card_add_compCountOn (G := G) hFA hPU
  have h3 : (F ∪ A).card = F.card + A.card := Finset.card_union_of_disjoint hdisj
  omega

/-- **One phase halves the instance component count.**  Same count as `compCount_halves`, with
components taken inside `P`: every instance component (`P.image (compOn G P F)`) is one of the two
sides of a phase edge, so `c ≤ 2|A|`, and the instance identity `|F| + c = |P|` converts that into
`2c' ≤ c`. -/
theorem compCountOn_halves {P : Finset V} {F A : Finset E} (hF : IsForest G F)
    (hP : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P) (hph : BorPhase G F A)
    (hPA : ∀ e ∈ A, G.src e ∈ P ∧ G.dst e ∈ P)
    (hcover : ∀ C ∈ P.image (compOn G P F),
      ∃ e ∈ A, compOn G P F (G.src e) = C ∨ compOn G P F (G.dst e) = C) :
    2 * compCountOn G P (F ∪ A) ≤ compCountOn G P F :=
  compCountOn_halves_of hF (boruvka_forest hF hph)
    (Finset.disjoint_left.mpr (fun e heF heA => hph.not_mem heA heF))
    hP (fun e he => by
      rcases Finset.mem_union.mp he with h | h
      · exact hP e h
      · exact hPA e h) hcover

/-- **`k` phases divide the instance component count by `2^k`.** -/
theorem compCountOn_pow_halves (K : ℕ) (P : Finset V) (F A : ℕ → Finset E)
    (hF0 : IsForest G (F 0)) (hP0 : ∀ e ∈ F 0, G.src e ∈ P ∧ G.dst e ∈ P)
    (hstep : ∀ i, F (i + 1) = F i ∪ A i)
    (hph : ∀ i, i < K → BorPhase G (F i) (A i))
    (hPA : ∀ i, i < K → ∀ e ∈ A i, G.src e ∈ P ∧ G.dst e ∈ P)
    (hcover : ∀ i, i < K → ∀ C ∈ P.image (compOn G P (F i)),
      ∃ e ∈ A i, compOn G P (F i) (G.src e) = C ∨ compOn G P (F i) (G.dst e) = C)
    {k : ℕ} (hk : k ≤ K) :
    2 ^ k * compCountOn G P (F k) ≤ compCountOn G P (F 0) := by
  have hforest : ∀ i, i ≤ K → IsForest G (F i) := by
    intro i hi
    induction i with
    | zero => exact hF0
    | succ n ih =>
        exact (hstep n).symm ▸
          boruvka_forest (ih (Nat.le_of_succ_le hi)) (hph n (Nat.lt_of_succ_le hi))
  have hPall : ∀ i, i ≤ K → ∀ e ∈ F i, G.src e ∈ P ∧ G.dst e ∈ P := by
    intro i hi
    induction i with
    | zero => exact hP0
    | succ n ih =>
        have hn : n ≤ K := Nat.le_of_succ_le hi
        intro e he
        rcases Finset.mem_union.mp ((hstep n).symm ▸ he : e ∈ F n ∪ A n) with h | h
        · exact ih hn e h
        · exact hPA n (Nat.lt_of_succ_le hi) e h
  have chain : ∀ i, i < K → 2 * compCountOn G P (F (i + 1)) ≤ compCountOn G P (F i) := by
    intro i hi
    rw [hstep i]
    exact compCountOn_halves (hforest i (Nat.le_of_lt hi)) (hPall i (Nat.le_of_lt hi))
      (hph i hi) (hPA i hi) (hcover i hi)
  exact pow_two_mul_le_of_le (fun i => compCountOn G P (F i)) K chain hk

/-- Instance-level `hn` slot at `k` phases: from the empty forest, an instance on `P` has at most
`|P| / 2^k` components (hence that many vertices after contraction). -/
theorem compCountOn_le_div_pow (K : ℕ) (P : Finset V) (F A : ℕ → Finset E) (k : ℕ)
    (hF0 : F 0 = ∅)
    (hstep : ∀ i, F (i + 1) = F i ∪ A i)
    (hph : ∀ i, i < K → BorPhase G (F i) (A i))
    (hPA : ∀ i, i < K → ∀ e ∈ A i, G.src e ∈ P ∧ G.dst e ∈ P)
    (hcover : ∀ i, i < K → ∀ C ∈ P.image (compOn G P (F i)),
      ∃ e ∈ A i, compOn G P (F i) (G.src e) = C ∨ compOn G P (F i) (G.dst e) = C)
    (hk : k ≤ K) :
    compCountOn G P (F k) ≤ P.card / 2 ^ k := by
  have hpow := compCountOn_pow_halves K P F A (by rw [hF0]; exact IsForest.empty)
    (by rw [hF0]; simp) hstep hph hPA hcover hk
  have h1 : compCountOn G P (F k) * 2 ^ k ≤ P.card := by
    rw [Nat.mul_comm]
    exact le_trans hpow (by rw [hF0, compCountOn_empty])
  exact (Nat.le_div_iff_mul_le (pow_pos (by norm_num) k)).mpr h1

/-- Real form, the shape the contraction hypothesis consumes. -/
theorem compCountOn_le_real (K : ℕ) (P : Finset V) (F A : ℕ → Finset E) (k : ℕ)
    (hF0 : F 0 = ∅)
    (hstep : ∀ i, F (i + 1) = F i ∪ A i)
    (hph : ∀ i, i < K → BorPhase G (F i) (A i))
    (hPA : ∀ i, i < K → ∀ e ∈ A i, G.src e ∈ P ∧ G.dst e ∈ P)
    (hcover : ∀ i, i < K → ∀ C ∈ P.image (compOn G P (F i)),
      ∃ e ∈ A i, compOn G P (F i) (G.src e) = C ∨ compOn G P (F i) (G.dst e) = C)
    (hk : k ≤ K) :
    (compCountOn G P (F k) : ℝ) ≤ (P.card : ℝ) / (2 : ℝ) ^ k := by
  have hnat := compCountOn_le_div_pow K P F A k hF0 hstep hph hPA hcover hk
  have h1 : compCountOn G P (F k) * 2 ^ k ≤ P.card :=
    (Nat.le_div_iff_mul_le (pow_pos (by norm_num) k)).mp hnat
  have hcast : (compCountOn G P (F k) : ℝ) * (2 : ℝ) ^ k ≤ (P.card : ℝ) := by
    have h2 : ((compCountOn G P (F k) * 2 ^ k : ℕ) : ℝ) ≤ ((P.card : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h2
    linarith
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- The paper's `hcontract` shape: if the parent instance satisfies `|P| ≤ 2|E₀|`, then `k` phases
leave at most `2|E₀| / 2^k` instance components. -/
theorem compCountOn_le_real_of_card_le (K : ℕ) (P : Finset V) (F A : ℕ → Finset E)
    (k : ℕ) {E₀ : Finset E}
    (hF0 : F 0 = ∅)
    (hstep : ∀ i, F (i + 1) = F i ∪ A i)
    (hph : ∀ i, i < K → BorPhase G (F i) (A i))
    (hPA : ∀ i, i < K → ∀ e ∈ A i, G.src e ∈ P ∧ G.dst e ∈ P)
    (hcover : ∀ i, i < K → ∀ C ∈ P.image (compOn G P (F i)),
      ∃ e ∈ A i, compOn G P (F i) (G.src e) = C ∨ compOn G P (F i) (G.dst e) = C)
    (hk : k ≤ K) (h0 : P.card ≤ 2 * E₀.card) :
    (compCountOn G P (F k) : ℝ) ≤ 2 * (E₀.card : ℝ) / (2 : ℝ) ^ k := by
  have h := compCountOn_le_real K P F A k hF0 hstep hph hPA hcover hk
  have h0' : (P.card : ℝ) ≤ 2 * (E₀.card : ℝ) := by exact_mod_cast h0
  rw [le_div_iff₀ (by positivity)] at h ⊢
  nlinarith

/-! ### From the phase chain to the child instance's data -/

theorem four_le_pow_two_two_mul {j : ℕ} (hj : 1 ≤ j) : 4 ≤ 2 ^ (2 * j) := by
  have h : 2 ^ 2 ≤ 2 ^ (2 * j) := Nat.pow_le_pow_right (by norm_num) (by omega)
  simpa using h

/-- **Vertex quartering from phases**: after `2j ≥ 2` phases the instance has at most `|P|/4`
components — the `hshrink` shape `4·|kidV| ≤ |P|`, here derived rather than assumed. -/
theorem four_mul_compCountOn_le (K : ℕ) (P : Finset V) (F A : ℕ → Finset E) {j : ℕ}
    (hF0 : F 0 = ∅)
    (hstep : ∀ i, F (i + 1) = F i ∪ A i)
    (hph : ∀ i, i < K → BorPhase G (F i) (A i))
    (hPA : ∀ i, i < K → ∀ e ∈ A i, G.src e ∈ P ∧ G.dst e ∈ P)
    (hcover : ∀ i, i < K → ∀ C ∈ P.image (compOn G P (F i)),
      ∃ e ∈ A i, compOn G P (F i) (G.src e) = C ∨ compOn G P (F i) (G.dst e) = C)
    (hjK : 2 * j ≤ K) (hj : 1 ≤ j) :
    4 * compCountOn G P (F (2 * j)) ≤ P.card := by
  have hpow := compCountOn_pow_halves K P F A (by rw [hF0]; exact IsForest.empty)
    (by rw [hF0]; simp) hstep hph hPA hcover hjK
  calc 4 * compCountOn G P (F (2 * j))
      ≤ 2 ^ (2 * j) * compCountOn G P (F (2 * j)) :=
        Nat.mul_le_mul_right _ (four_le_pow_two_two_mul hj)
    _ ≤ compCountOn G P (F 0) := hpow
    _ = P.card := by rw [hF0, compCountOn_empty]

/-- A vertex set with at most one vertex per instance component injects into the component image,
so it has at most `compCountOn` elements — the contracted instance's vertex set. -/
theorem card_le_compCountOn_of_pairwise_not_conn {P Q : Finset V} {F : Finset E}
    (hQ : Q ⊆ P) (hsep : ∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → ¬ Conn G F u v) :
    Q.card ≤ compCountOn G P F := by
  have hinj : ∀ u ∈ Q, ∀ v ∈ Q, compOn G P F u = compOn G P F v → u = v := by
    intro u hu v hv h
    by_contra huv
    refine hsep u hu v hv huv ?_
    have hmem : u ∈ compOn G P F v := h ▸ mem_compOn.mpr ⟨hQ hu, Conn.refl u⟩
    exact (mem_compOn.mp hmem).2.symm
  calc Q.card = (Q.image (compOn G P F)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (P.image (compOn G P F)).card := by
        refine Finset.card_le_card ?_
        intro x hx
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_image.mpr ⟨v, hQ hv, rfl⟩
    _ = compCountOn G P F := rfl

/-- `hshrink` from the phase chain: a child vertex set with one vertex per component has
`4·|kidV| ≤ |P|` once `2j ≥ 2` phases have run. -/
theorem four_mul_card_le_of_phases (K : ℕ) (P : Finset V) (F A : ℕ → Finset E) {j : ℕ}
    {Q : Finset V} (hQ : Q ⊆ P)
    (hsep : ∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → ¬ Conn G (F (2 * j)) u v)
    (hF0 : F 0 = ∅)
    (hstep : ∀ i, F (i + 1) = F i ∪ A i)
    (hph : ∀ i, i < K → BorPhase G (F i) (A i))
    (hPA : ∀ i, i < K → ∀ e ∈ A i, G.src e ∈ P ∧ G.dst e ∈ P)
    (hcover : ∀ i, i < K → ∀ C ∈ P.image (compOn G P (F i)),
      ∃ e ∈ A i, compOn G P (F i) (G.src e) = C ∨ compOn G P (F i) (G.dst e) = C)
    (hjK : 2 * j ≤ K) (hj : 1 ≤ j) :
    4 * Q.card ≤ P.card := by
  have h1 : Q.card ≤ compCountOn G P (F (2 * j)) :=
    card_le_compCountOn_of_pairwise_not_conn hQ hsep
  have h2 := four_mul_compCountOn_le K P F A hF0 hstep hph hPA hcover hjK hj
  omega

/-- **`hcontract` from the phase chain**: a child vertex set with one vertex per component, whose
edge budget carries the parent's vertex count (`|P| ≤ 2|E_child|`), satisfies
`|kidV| ≤ 2|E_child|/2^{2j}` — exactly the hypothesis `Strategy.cost_linear_of_contraction`
consumes. -/
theorem hcontract_of_phases (K : ℕ) (P : Finset V) (F A : ℕ → Finset E) {j : ℕ}
    {Q : Finset V} {Echild : Finset E} (hQ : Q ⊆ P)
    (hsep : ∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → ¬ Conn G (F (2 * j)) u v)
    (hF0 : F 0 = ∅)
    (hstep : ∀ i, F (i + 1) = F i ∪ A i)
    (hph : ∀ i, i < K → BorPhase G (F i) (A i))
    (hPA : ∀ i, i < K → ∀ e ∈ A i, G.src e ∈ P ∧ G.dst e ∈ P)
    (hcover : ∀ i, i < K → ∀ C ∈ P.image (compOn G P (F i)),
      ∃ e ∈ A i, compOn G P (F i) (G.src e) = C ∨ compOn G P (F i) (G.dst e) = C)
    (hjK : 2 * j ≤ K) (h0 : P.card ≤ 2 * Echild.card) :
    (Q.card : ℝ) ≤ 2 * (Echild.card : ℝ) / (2 : ℝ) ^ (2 * j) := by
  have h1 : (Q.card : ℝ) ≤ (compCountOn G P (F (2 * j)) : ℝ) := by
    exact_mod_cast card_le_compCountOn_of_pairwise_not_conn hQ hsep
  have h2 : (compCountOn G P (F (2 * j)) : ℝ) ≤ (P.card : ℝ) / (2 : ℝ) ^ (2 * j) :=
    compCountOn_le_real K P F A (2 * j) hF0 hstep hph hPA hcover hjK
  have h0' : (P.card : ℝ) ≤ 2 * (Echild.card : ℝ) := by exact_mod_cast h0
  have hc : (Q.card : ℝ) * (2 : ℝ) ^ (2 * j)
      ≤ (compCountOn G P (F (2 * j)) : ℝ) * (2 : ℝ) ^ (2 * j) :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  rw [le_div_iff₀ (by positivity)] at h2 ⊢
  linarith

/-! ### Bridging the global Borůvka cover to the instance cover -/

/-- The cover produced by `BoruvkaPhase` is stated on whole-graph components; inside an instance the
same phase edges cover the instance components, provided both their ends are in `P`. -/
theorem cover_on_of_cover {P : Finset V} {F A : Finset E}
    (hP : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P)
    (hPA : ∀ e ∈ A, G.src e ∈ P ∧ G.dst e ∈ P)
    (hcover : ∀ C ∈ Finset.univ.image (comp G F),
      ∃ e ∈ A, comp G F (G.src e) = C ∨ comp G F (G.dst e) = C) :
    ∀ C ∈ P.image (compOn G P F),
      ∃ e ∈ A, compOn G P F (G.src e) = C ∨ compOn G P F (G.dst e) = C := by
  intro C hC
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hC
  have hCimg : compOn G P F v ∈ Finset.univ.image (comp G F) := by
    refine Finset.mem_image.mpr ⟨v, Finset.mem_univ v, ?_⟩
    exact (compOn_eq_comp hP hv).symm
  obtain ⟨e, he, hCe⟩ := hcover _ hCimg
  refine ⟨e, he, ?_⟩
  rcases hCe with h | h
  · left
    rw [compOn_eq_comp hP (hPA e he).1, h]
  · right
    rw [compOn_eq_comp hP (hPA e he).2, h]

/-- The halving lemma in the form a driver consumes: only the Borůvka phase's own cover is needed. -/
theorem compCountOn_halves_of_cover {P : Finset V} {F A : Finset E} (hF : IsForest G F)
    (hP : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P) (hph : BorPhase G F A)
    (hPA : ∀ e ∈ A, G.src e ∈ P ∧ G.dst e ∈ P)
    (hcover : ∀ C ∈ Finset.univ.image (comp G F),
      ∃ e ∈ A, comp G F (G.src e) = C ∨ comp G F (G.dst e) = C) :
    2 * compCountOn G P (F ∪ A) ≤ compCountOn G P F :=
  compCountOn_halves hF hP hph hPA (cover_on_of_cover hP hPA hcover)

/-- **One representative per instance component.**  Choosing an element of every component of
`P.image (compOn G P F)` gives a vertex set `Q ⊆ P` of size `compCountOn G P F` whose distinct
elements are pairwise not `F`-connected — the `kidV` shape `hcontract_of_phases` and
`four_mul_card_le_of_phases` consume, now produced rather than assumed. -/
theorem exists_reps (P : Finset V) (F : Finset E) :
    ∃ Q : Finset V, Q ⊆ P ∧ Q.card = compCountOn G P F ∧
      ∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → ¬ Conn G F u v := by
  classical
  have hne : ∀ C ∈ P.image (compOn G P F), C.Nonempty := by
    intro C hC
    obtain ⟨v, hv, hCv⟩ := Finset.mem_image.mp hC
    rw [← hCv]
    exact ⟨v, mem_compOn.mpr ⟨hv, Conn.refl v⟩⟩
  set S : Finset (Finset V) := P.image (compOn G P F)
  let g : {C // C ∈ S} → V := fun C => (hne C.1 C.2).choose
  set Q : Finset V := S.attach.image g with hQ
  -- the chosen vertex lies in its component
  have hcomp : ∀ C : {C // C ∈ S}, compOn G P F (g C) = C.1 := by
    intro C
    obtain ⟨v, -, hCv⟩ := Finset.mem_image.mp C.2
    have hxg : g C ∈ compOn G P F v := by
      rw [hCv]
      exact (hne C.1 C.2).choose_spec
    exact ((compOn_congr (mem_compOn.mp hxg).2).symm).trans hCv
  have hinj : Set.InjOn g ↑S.attach := by
    intro C1 _ C2 _ h
    exact Subtype.ext (by rw [← hcomp C1, ← hcomp C2, h])
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨C, -, rfl⟩ := Finset.mem_image.mp hu
    refine compOn_subset (G := G) P F (g C) ?_
    rw [hcomp C]
    exact (hne C.1 C.2).choose_spec
  · rw [hQ, Finset.card_image_of_injOn hinj, Finset.card_attach]
    rfl
  · intro u hu v hv huv hconn
    obtain ⟨C1, -, hC1⟩ := Finset.mem_image.mp hu
    obtain ⟨C2, -, hC2⟩ := Finset.mem_image.mp hv
    have hC : C1.1 = C2.1 := by
      rw [← hcomp C1, ← hcomp C2, hC1, hC2]
      exact compOn_congr hconn
    exact huv (by rw [← hC1, ← hC2]; exact congrArg g (Subtype.ext hC))

/-! ### The component map is a partition of `P` -/

/-- Two components sharing a vertex are the same component. -/
theorem compOn_eq_of_mem_inter {P : Finset V} {F : Finset E} {v w x : V}
    (hv : x ∈ compOn G P F v) (hw : x ∈ compOn G P F w) :
    compOn G P F v = compOn G P F w :=
  compOn_congr ((mem_compOn.mp hv).2.trans (mem_compOn.mp hw).2.symm)

/-- Distinct instance components are disjoint. -/
theorem disjoint_compOn {P : Finset V} {F : Finset E} {v w : V}
    (h : compOn G P F v ≠ compOn G P F w) : Disjoint (compOn G P F v) (compOn G P F w) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  exact h (compOn_eq_of_mem_inter hx hx')

/-- The instance components are pairwise disjoint — the map `compOn G P F` is a partition. -/
theorem pairwise_disjoint_compOn (P : Finset V) (F : Finset E) :
    ∀ C ∈ P.image (compOn G P F), ∀ D ∈ P.image (compOn G P F), C ≠ D → Disjoint C D := by
  intro C hC D hD hCD
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hD
  exact disjoint_compOn hCD

/-- The instance components cover `P`. -/
theorem biUnion_compOn (P : Finset V) (F : Finset E) :
    (P.image (compOn G P F)).biUnion (fun C => C) = P := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨v, -, hCv⟩ := Finset.mem_image.mp hC
    rw [← hCv] at hxC
    exact compOn_subset (G := G) P F v hxC
  · intro hx
    exact Finset.mem_biUnion.mpr
      ⟨compOn G P F x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, mem_compOn.mpr ⟨hx, Conn.refl x⟩⟩

/-- **A transversal that reaches every vertex.**  Besides one representative per component, every
vertex of `P` is `F`-connected to some representative.  This is the data a contraction needs: the
representatives are the new vertices, and the phase forest connects each old vertex to its own. -/
theorem exists_reps_conn (P : Finset V) (F : Finset E) :
    ∃ Q : Finset V, Q ⊆ P ∧ Q.card = compCountOn G P F ∧
      (∀ v ∈ P, ∃ q ∈ Q, Conn G F v q) ∧
      (∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → ¬ Conn G F u v) := by
  classical
  obtain ⟨Q, hQ, hcard, hsep⟩ := exists_reps (G := G) P F
  refine ⟨Q, hQ, hcard, fun v hv => ?_, hsep⟩
  set S : Finset (Finset V) := P.image (compOn G P F)
  have hSsub : Q.image (fun q => compOn G P F q) ⊆ S := by
    intro C hC
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hC
    exact Finset.mem_image.mpr ⟨q, hQ hq, rfl⟩
  have hinj : Set.InjOn (compOn G P F) ↑Q := by
    intro u hu w hw huw
    by_contra hne
    have hw' : w ∈ compOn G P F u := by
      rw [huw]
      exact mem_compOn.mpr ⟨hQ hw, Conn.refl w⟩
    exact hsep u hu w hw hne (mem_compOn.mp hw').2
  have himg : Q.image (fun q => compOn G P F q) = S := by
    refine Finset.eq_of_subset_of_card_le hSsub ?_
    rw [Finset.card_image_of_injOn hinj]
    have hS : S.card = compCountOn G P F := rfl
    rw [hS, hcard]
  have hC : compOn G P F v ∈ S := Finset.mem_image.mpr ⟨v, hv, rfl⟩
  rw [← himg] at hC
  obtain ⟨q, hq, hqv⟩ := Finset.mem_image.mp hC
  refine ⟨q, hq, ?_⟩
  have hv' : v ∈ compOn G P F q := by
    rw [hqv]
    exact mem_compOn.mpr ⟨hv, Conn.refl v⟩
  exact (mem_compOn.mp hv').2.symm

/-- **Activation from connectivity inside the instance.**  If `E₀` joins every pair of `P` and the
instance still has at least two components, every `v ∈ P` has an `E₀`-edge leaving its `F`-component.
The global form `hact_of_conn_E₀` asks connectivity of *all* of `V`, which the tower's level graphs do
not satisfy once vertices stop being representatives; restricting to `P` fixes that. -/
theorem hact_of_connOn_E₀ (K : ℕ) {P : Finset V} {E₀ : Finset E} (F : ℕ → Finset E)
    (hconn : ∀ u ∈ P, ∀ w ∈ P, Conn G E₀ u w)
    (hc : ∀ i, i < K → 2 ≤ compCountOn G P (F i)) :
    ∀ i, i < K → ∀ v ∈ P, ∃ e ∈ E₀, leaves G (F i) v e := by
  intro i hi v hv
  have hcard : 1 < (P.image (compOn G P (F i))).card := hc i hi
  have hex : ∃ s ∈ P.image (compOn G P (F i)), s ≠ compOn G P (F i) v := by
    by_contra h
    have h' : ∀ s ∈ P.image (compOn G P (F i)), s = compOn G P (F i) v := by
      intro s hs
      by_contra hne
      exact h ⟨s, hs, hne⟩
    have hsub : P.image (compOn G P (F i)) ⊆ {compOn G P (F i) v} := by
      intro s hs
      exact Finset.mem_singleton.mpr (h' s hs)
    have hle := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hle
    omega
  obtain ⟨s, hs, hsv⟩ := hex
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hs
  have hnc : ¬ Conn G (F i) v w := fun hc' => hsv (compOn_congr hc').symm
  exact leaves_of_conn_E₀ (G := G) (E₀ := E₀) (F := F i) ⟨w, hconn v hv w hw, hnc⟩

end DLMST