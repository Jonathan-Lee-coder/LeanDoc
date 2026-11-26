import DLMST.Tower

/-!
# §4 needs no activation

`Tower`'s soundness theorem `tower_sound` (and its bounded form `tower_sound_bd`) carries a
per-level activation hypothesis: every vertex of every level must have an outgoing instance edge
in each of the two phases.  That hypothesis is what makes the *measure* half work
(`four_pow_mul_lvlVerts_le` needs it through `four_mul_repSet_card_le`), and it is genuinely
unsatisfiable at a collapsed level: a one-vertex instance has no leaving edge at all
(`activated_iff_two_le_compCountOn` below makes this precise).

The *correctness* half, however, never needed it.  The two-phase forest of a level is contained
in *some* minimum spanning forest of the level's instance — this is `phaseChain_safe`, which is
proved by the relative blue rule and mentions no activation — and `isMSFOf_union_cGraph_child`
splices a child's MSF along such a containment.  So the splice at every level is available
unconditionally:

* `contract_step_sound_nohact`: two phases plus the child's MSF give an MSF of the level;
* `tower_sound_nohact`: splicing all the way down gives an MSF of the root instance, with no
  hypothesis besides the instance shape `hPE`;
* `tower_msf_at_stop_nohact` / `..._card`: at *any* depth whose vertex set has at most one
  vertex, the bottom call is unnecessary and the answer is an MSF with at most `|P| - 1` edges.

What remains is to find a stopping depth.  No activation is needed for that either: while a level
has at least two vertices, one phase is nonempty (its existence is *derived* from level
connectivity and the level having `≥ 2` components by `hact_of_connOn_E₀`), so the two-phase
chain carries a nonempty forest and the next vertex set is strictly smaller.  Hence
`|V_d| ≤ 1` or `|V_d| + d ≤ |P|` at every depth, and depth `|P|` always stops.  Composing:

* `mst_main_connected`: if `G[E₀]` is connected on `P`, then
  `answer G P E₀ P.card ∅` is an MSF of `G[E₀]` and has at most `|P| - 1` edges;
* `mst_main_connected_three_fourths`: `3 · |F| ≤ 4 · |P|`;
* `mst_main_connected_package`: also the weight telescope and the measure at the stop depth.

This closes boundary B3 of the audit in the only way available: the tower's correctness and the
`4/3` size bound are *unconditional* (given connectivity), while the measure-based `|P|/4^d`
account stays activation-bound.  All sizes are edge counts; there is still no RAM model (B2).
-/
open Classical

namespace DLMST

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]

/-! ## The splice without activation -/

/-- **§4's step, without activation.**  The phase chain is contained in some MSF of the instance
(`phaseChain_safe`), and along that containment the child's MSF splices back
(`isMSFOf_union_cGraph_child`).  No vertex of the instance is ever asked for a leaving edge. -/
theorem contract_step_sound_nohact {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    {B' : Finset {e // e ∈ crossE G (phaseChain G E₀ 2) E₀}}
    (hB' : IsMSFOf (cGraph G P (phaseChain G E₀ 2) E₀)
      (Finset.univ : Finset {e // e ∈ crossE G (phaseChain G E₀ 2) E₀}) B') :
    IsMSFOf G E₀ (phaseChain G E₀ 2 ∪ B'.image Subtype.val) := by
  obtain ⟨M, hM, hFM⟩ :=
    phaseChain_safe (G := G) (S := E₀) (phaseChain G E₀) rfl (fun _ => rfl) 2
  exact isMSFOf_union_cGraph_child (G := G) (P := P) (E₀ := E₀) hPE
    (isForest_phaseChain E₀ (phaseChain G E₀) 2 rfl (fun _ => rfl)) hM hFM hB'

/-! ## The tower without activation -/

/-- **§4 terminates at every depth, and the answer is an MSF — unconditionally.**  If the
level-`d` instance has an MSF `B`, splicing the level forests on the way down gives an MSF of the
root instance.  Unlike `tower_sound`, no phase is ever required to activate. -/
theorem tower_sound_nohact {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (d : ℕ) (B : Finset E)
    (hB : IsMSFOf (lvlGraph G P E₀ d) (lvlE G P E₀ d) B) :
    IsMSFOf G E₀ (answer G P E₀ d B) := by
  revert B
  induction d with
  | zero =>
      intro B hB
      exact hB
  | succ n ih =>
      intro B hB
      have hFS : lvlForest G P E₀ n = phaseChain (lvlGraph G P E₀ n) (lvlE G P E₀ n) 2 :=
        lvlForest_eq_chain G P E₀ n
      have hBsub : ∀ e ∈ B,
          e ∈ crossE (lvlGraph G P E₀ n) (phaseChain (lvlGraph G P E₀ n) (lvlE G P E₀ n) 2)
            (lvlE G P E₀ n) := by
        intro e he
        have h1 : e ∈ lvlE G P E₀ (n + 1) := hB.1.2.1 he
        rw [lvlE_succ, hFS] at h1
        exact h1
      set B' : Finset {e // e ∈ crossE (lvlGraph G P E₀ n)
          (phaseChain (lvlGraph G P E₀ n) (lvlE G P E₀ n) 2) (lvlE G P E₀ n)} :=
        B.subtype (fun e => e ∈ crossE (lvlGraph G P E₀ n)
          (phaseChain (lvlGraph G P E₀ n) (lvlE G P E₀ n) 2) (lvlE G P E₀ n))
        with hB'def
      have himg : B'.image Subtype.val = B := by
        rw [hB'def]
        exact image_subtype_crossE (phaseChain (lvlGraph G P E₀ n) (lvlE G P E₀ n) 2)
          (lvlE G P E₀ n) hBsub
      have hflat : IsMSFOf
          (cGraphFlat (lvlGraph G P E₀ n) (lvlVerts G P E₀ n)
            (phaseChain (lvlGraph G P E₀ n) (lvlE G P E₀ n) 2))
          (crossE (lvlGraph G P E₀ n) (phaseChain (lvlGraph G P E₀ n) (lvlE G P E₀ n) 2)
            (lvlE G P E₀ n))
          (B'.image Subtype.val) := by
        rw [himg]
        rw [lvlGraph_succ, lvlE_succ, hFS] at hB
        exact hB
      have hchild : IsMSFOf
          (cGraph (lvlGraph G P E₀ n) (lvlVerts G P E₀ n)
            (phaseChain (lvlGraph G P E₀ n) (lvlE G P E₀ n) 2) (lvlE G P E₀ n))
          (Finset.univ : Finset
            {e // e ∈ crossE (lvlGraph G P E₀ n)
              (phaseChain (lvlGraph G P E₀ n) (lvlE G P E₀ n) 2) (lvlE G P E₀ n)}) B' :=
        isMSFOf_cGraph_of_flat hflat
      have hMSF : IsMSFOf (lvlGraph G P E₀ n) (lvlE G P E₀ n)
          (phaseChain (lvlGraph G P E₀ n) (lvlE G P E₀ n) 2 ∪ B'.image Subtype.val) :=
        contract_step_sound_nohact (G := lvlGraph G P E₀ n) (P := lvlVerts G P E₀ n)
          (E₀ := lvlE G P E₀ n) (lvl_hPE hPE n) hchild
      have hMSF' : IsMSFOf (lvlGraph G P E₀ n) (lvlE G P E₀ n) (lvlForest G P E₀ n ∪ B) := by
        rw [hFS, ← himg]
        exact hMSF
      exact ih (lvlForest G P E₀ n ∪ B) hMSF'

/-- **The bottom call is unnecessary whenever the vertex set has collapsed.**  At any depth with
`|verts| ≤ 1` the level is all loops, the empty forest is its MSF, and the spliced answer is an MSF
of the root instance — with no activation hypothesis on any level. -/
theorem tower_msf_at_stop_nohact {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (D : ℕ) (hstop : (lvlVerts G P E₀ D).card ≤ 1) :
    IsMSFOf G E₀ (answer G P E₀ D ∅) :=
  tower_sound_nohact hPE D ∅ (isMSFOf_empty_of_card_le_one (lvl_hPE hPE D) hstop)

/-- The stopping answer is a forest on the instance, so it has at most `|P| - 1` edges. -/
theorem tower_msf_at_stop_nohact_card {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (D : ℕ) (hstop : (lvlVerts G P E₀ D).card ≤ 1) :
    (answer G P E₀ D ∅).card ≤ P.card - 1 := by
  have h := tower_msf_at_stop_nohact hPE D hstop
  exact card_le_card_sub_one_of_isForest_of_ends (G := G) (F := answer G P E₀ D ∅) h.1.1
    (fun e he => hPE e (h.1.2.1 he)) hP

/-! ## Finding a stopping depth without activation

The only hypothesis is that the instance is connected on `P` (`hroot`).  Every level's vertex set
is then connected inside itself (`lvl_connOn_of_root_conn`), so activation at the first phase is
derived from the count `|P| ≥ 2` — and one nonempty phase forest shrinks the vertex set. -/

/-- Every level's vertex set is at most as large as its parent's. -/
theorem lvlVerts_step_le {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (d : ℕ) :
    (lvlVerts G P E₀ (d + 1)).card ≤ (lvlVerts G P E₀ d).card := by
  have hF2 : IsForest (lvlGraph G P E₀ d)
      (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) 2) :=
    isForest_phaseChain _ _ 2 rfl (fun _ => rfl)
  have hP2 : ∀ e ∈ phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) 2,
      (lvlGraph G P E₀ d).src e ∈ lvlVerts G P E₀ d ∧
        (lvlGraph G P E₀ d).dst e ∈ lvlVerts G P E₀ d :=
    fun e he => lvl_hPE hPE d e
      (phaseChain_subset (lvlGraph G P E₀ d) (lvlE G P E₀ d) 2 he)
  have hnext : (lvlVerts G P E₀ (d + 1)).card = (lvlVerts G P E₀ d).card -
      (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) 2).card := by
    have h := card_add_compCountOn (G := lvlGraph G P E₀ d) (P := lvlVerts G P E₀ d)
      (F := phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) 2) hF2 hP2
    have hrep : (lvlVerts G P E₀ (d + 1)).card =
        compCountOn (lvlGraph G P E₀ d) (lvlVerts G P E₀ d)
          (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) 2) := by
      rw [lvlVerts_succ_chain, repSet_card]
    omega
  rw [hnext]
  exact Nat.sub_le _ _

/-- **A level with at least two vertices strictly shrinks.**  Connectivity supplies the phase-0
activation, one nonempty non-loop edge enters the phase chain, and the component identity turns
that into a strict decrease of the vertex count.  No activation is assumed; it is derived from
`hconn` and `2 ≤ |verts|` by `hact_of_connOn_E₀`. -/
theorem lvlVerts_succ_lt {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (d : ℕ)
    (hconn : ∀ u ∈ lvlVerts G P E₀ d, ∀ w ∈ lvlVerts G P E₀ d,
      Conn (lvlGraph G P E₀ d) (lvlE G P E₀ d) u w)
    (h2 : 2 ≤ (lvlVerts G P E₀ d).card) :
    (lvlVerts G P E₀ (d + 1)).card < (lvlVerts G P E₀ d).card := by
  classical
  have hact0 : ∀ v ∈ lvlVerts G P E₀ d, ∃ e ∈ lvlE G P E₀ d,
      leaves (lvlGraph G P E₀ d)
        (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) 0) v e := by
    refine hact_of_connOn_E₀ 1 (G := lvlGraph G P E₀ d) (P := lvlVerts G P E₀ d)
      (E₀ := lvlE G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d)) hconn
      (fun i hi => ?_) 0 (by norm_num)
    have hi0 : i = 0 := Nat.lt_one_iff.mp hi
    have h0 : phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) 0 = (∅ : Finset E) := rfl
    rw [hi0, h0, compCountOn_empty]
    exact h2
  obtain ⟨v0, hv0⟩ := Finset.card_pos.mp (by omega : 0 < (lvlVerts G P E₀ d).card)
  obtain ⟨e0, he0, hlv0⟩ := hact0 v0 hv0
  have hne : ((lvlE G P E₀ d).filter
      (fun e => leaves (lvlGraph G P E₀ d)
        (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) 0) v0 e)).Nonempty :=
    ⟨e0, Finset.mem_filter.mpr ⟨he0, hlv0⟩⟩
  obtain ⟨m, hm, hmin⟩ := exists_wOrd_min (G := lvlGraph G P E₀ d) _ hne
  have hm1 : m ∈ phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) 1 :=
    Finset.mem_union_right _ (mem_phaseIn.mpr ⟨(Finset.mem_filter.mp hm).1, v0,
      (Finset.mem_filter.mp hm).2, fun f hf hlf => hmin f (Finset.mem_filter.mpr ⟨hf, hlf⟩)⟩)
  have hpos1 : 0 < (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) 1).card :=
    Finset.card_pos.mpr ⟨m, hm1⟩
  have hmono : (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) 1).card ≤
      (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) 2).card :=
    Finset.card_le_card Finset.subset_union_left
  have hpos2 : 0 < (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) 2).card :=
    lt_of_lt_of_le hpos1 hmono
  have hF2 : IsForest (lvlGraph G P E₀ d)
      (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) 2) :=
    isForest_phaseChain _ _ 2 rfl (fun _ => rfl)
  have hP2 : ∀ e ∈ phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) 2,
      (lvlGraph G P E₀ d).src e ∈ lvlVerts G P E₀ d ∧
        (lvlGraph G P E₀ d).dst e ∈ lvlVerts G P E₀ d :=
    fun e he => lvl_hPE hPE d e
      (phaseChain_subset (lvlGraph G P E₀ d) (lvlE G P E₀ d) 2 he)
  have hnext : (lvlVerts G P E₀ (d + 1)).card = (lvlVerts G P E₀ d).card -
      (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) 2).card := by
    have h := card_add_compCountOn (G := lvlGraph G P E₀ d) (P := lvlVerts G P E₀ d)
      (F := phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) 2) hF2 hP2
    have hrep : (lvlVerts G P E₀ (d + 1)).card =
        compCountOn (lvlGraph G P E₀ d) (lvlVerts G P E₀ d)
          (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) 2) := by
      rw [lvlVerts_succ_chain, repSet_card]
    omega
  rw [hnext]
  exact Nat.sub_lt (by omega : 0 < (lvlVerts G P E₀ d).card) hpos2

/-- **The stopping dichotomy**: at every depth either the level has collapsed to at most one
vertex, or the vertex count plus the depth fits in `|P|`.  The depth term pays for the strict
decrease of `lvlVerts_succ_lt`; a collapsed level stops counting because it can only stay
collapsed (`lvlVerts_step_le`). -/
theorem lvlVerts_le_one_or_card_add_le {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hroot : ∀ u ∈ P, ∀ w ∈ P, Conn G E₀ u w) (d : ℕ) :
    (lvlVerts G P E₀ d).card ≤ 1 ∨ (lvlVerts G P E₀ d).card + d ≤ P.card := by
  induction d with
  | zero =>
      refine Or.inr ?_
      simp [lvlVerts, lvlData]
  | succ n ih =>
      have hconn := lvl_connOn_of_root_conn (G := G) (P := P) (E₀ := E₀) hPE hroot n
      rcases ih with hsmall | hbig
      · exact Or.inl ((lvlVerts_step_le hPE n).trans hsmall)
      · by_cases h1 : (lvlVerts G P E₀ n).card ≤ 1
        · exact Or.inl ((lvlVerts_step_le hPE n).trans h1)
        · refine Or.inr ?_
          have h2 : 2 ≤ (lvlVerts G P E₀ n).card := by omega
          have hlt := lvlVerts_succ_lt hPE n hconn h2
          omega

/-- **A stopping depth exists**: depth `|P|` always has at most one vertex.  The alternative
`|V_{|P|}| + |P| ≤ |P|` would force the level to be empty. -/
theorem lvlVerts_card_le_one_at_card {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hroot : ∀ u ∈ P, ∀ w ∈ P, Conn G E₀ u w) :
    (lvlVerts G P E₀ P.card).card ≤ 1 := by
  rcases lvlVerts_le_one_or_card_add_le hPE hroot P.card with h | h
  · exact h
  · omega

/-- The stopping depth, as an existential. -/
theorem exists_lvlVerts_card_le_one {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hroot : ∀ u ∈ P, ∀ w ∈ P, Conn G E₀ u w) :
    ∃ D, (lvlVerts G P E₀ D).card ≤ 1 :=
  ⟨P.card, lvlVerts_card_le_one_at_card hPE hroot⟩

/-! ## §4, unconditionally -/

/-- **§4 on a connected instance**: the spliced answer at depth `|P|` is a minimum spanning forest
of `G[E₀]` and has at most `|P| - 1` edges.  No activation hypothesis anywhere. -/
theorem mst_main_connected {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hroot : ∀ u ∈ P, ∀ w ∈ P, Conn G E₀ u w) :
    IsMSFOf G E₀ (answer G P E₀ P.card ∅) ∧
      (answer G P E₀ P.card ∅).card ≤ P.card - 1 := by
  have hstop := lvlVerts_card_le_one_at_card hPE hroot
  exact ⟨tower_msf_at_stop_nohact hPE P.card hstop,
    tower_msf_at_stop_nohact_card hPE hP P.card hstop⟩

/-- The unconditional `4/3` bound: a forest on `|P|` vertices has `|F| ≤ |P| - 1`, so
`3|F| ≤ 3(|P| - 1) < 4|P|`. -/
theorem mst_main_connected_three_fourths {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hroot : ∀ u ∈ P, ∀ w ∈ P, Conn G E₀ u w) :
    3 * (answer G P E₀ P.card ∅).card ≤ 4 * P.card := by
  obtain ⟨-, hcard⟩ := mst_main_connected hPE hP hroot
  omega

/-- **The weight telescope, unconditionally**: the answer's weight is the sum of the level
forests' weights, with no bottom term.  (The instance shape plays no role: the telescope is about
the level data alone.) -/
theorem mst_main_connected_weight {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (_hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (_hP : 0 < P.card)
    (_hroot : ∀ u ∈ P, ∀ w ∈ P, Conn G E₀ u w) :
    wsum G (answer G P E₀ P.card ∅) =
      Finset.sum (Finset.range P.card) (fun j => wsum G (lvlForest G P E₀ j)) := by
  have h := tower_wsum (G := G) (P := P) (E₀ := E₀) P.card ∅ (Finset.empty_subset _)
  simpa [wsum] using h

/-- **The whole unconditional account at depth `|P|`**: correctness, the edge bound, the `4/3`
bound, the weight telescope, and a stopping level whose vertex set has at most one element. -/
theorem mst_main_connected_package {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hroot : ∀ u ∈ P, ∀ w ∈ P, Conn G E₀ u w) :
    IsMSFOf G E₀ (answer G P E₀ P.card ∅) ∧
      (answer G P E₀ P.card ∅).card ≤ P.card - 1 ∧
      3 * (answer G P E₀ P.card ∅).card ≤ 4 * P.card ∧
      (lvlVerts G P E₀ P.card).card ≤ 1 ∧
      wsum G (answer G P E₀ P.card ∅) =
        Finset.sum (Finset.range P.card) (fun j => wsum G (lvlForest G P E₀ j)) := by
  obtain ⟨hmsf, hcard⟩ := mst_main_connected hPE hP hroot
  exact ⟨hmsf, hcard, by omega, lvlVerts_card_le_one_at_card hPE hroot,
    mst_main_connected_weight hPE hP hroot⟩

/-! ## Activation is exactly non-collapse

This records *why* `tower_sound` cannot be used unconditionally: its activation hypothesis is
equivalent, on a connected instance, to the level not having collapsed.  A one-vertex level has no
leaving edge to offer, so the two-phase stop interface `tower_msf_of_stop` is satisfiable only when
the collapse happens at a level boundary (a path on four vertices is the smallest witness; an
odd star collapses inside a level and leaves the second phase unactivated). -/

/-- **Activation ⇔ at least two components.**  On a connected instance, every vertex has a leaving
instance edge if and only if the forest has not yet spanned.  (`→`: a leaving edge puts the far
endpoint outside the component.  `←`: `hact_of_connOn_E₀` with a constant forest.) -/
theorem activated_iff_two_le_compCountOn {G : WGraph V E} {P : Finset V} {E₀ F : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hconn : ∀ u ∈ P, ∀ w ∈ P, Conn G E₀ u w) (hPne : P.Nonempty) :
    (∀ v ∈ P, ∃ e ∈ E₀, leaves G F v e) ↔ 2 ≤ compCountOn G P F := by
  constructor
  · intro hact
    obtain ⟨v0, hv0⟩ := hPne
    obtain ⟨e, he, hlv⟩ := hact v0 hv0
    obtain ⟨w, hwP, hw⟩ : ∃ w ∈ P, ¬ Conn G F v0 w := by
      rcases hlv with ⟨-, hd⟩ | ⟨hs, -⟩
      · exact ⟨G.dst e, (hPE e he).2, hd⟩
      · exact ⟨G.src e, (hPE e he).1, hs⟩
    have hne : compOn G P F v0 ≠ compOn G P F w := by
      intro heq
      have hmem : w ∈ compOn G P F v0 := by
        rw [heq]
        exact mem_compOn.mpr ⟨hwP, Conn.refl w⟩
      exact hw (mem_compOn.mp hmem).2
    have hlt : 1 < (P.image (compOn G P F)).card :=
      Finset.one_lt_card.mpr
        ⟨_, Finset.mem_image.mpr ⟨v0, hv0, rfl⟩,
          _, Finset.mem_image.mpr ⟨w, hwP, rfl⟩, hne⟩
    show 2 ≤ (P.image (compOn G P F)).card
    omega
  · intro hc
    have h := hact_of_connOn_E₀ 1 (G := G) (P := P) (E₀ := E₀) (fun _ => F) hconn
      (fun i _ => hc) 0 (by norm_num)
    simpa using h

end DLMST