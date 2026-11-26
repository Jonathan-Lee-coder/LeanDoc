/-
# §4 at arbitrary depth: the contraction tower, flattened

§4 recurses on the contracted instance.  The child instance's edge type is a subtype of the
parent's, so the *nested* tower has no single edge type to state a theorem in.  This file
keeps every level on the **ambient** edge type `E`: level `d`'s graph has the same vertex type
and the same edges, but its endpoints are the `d`-fold images under `repOf`, and its weights are
inherited.  Level `d + 1`'s graph is exactly level `d`'s contraction read back on `E`
(`cGraphFlat`), which is `cGraph` with the subtype forgotten.

This removes all instance friction: `IsMSFOf` and `IsForest` capture a `DecidableEq` argument
for the edge type, and with one edge type for all levels the argument never changes.  The
connection to the real, nested recursion is `conn_cGraphFlat_iff` / `isForest_*_of_image` /
`isMSFOf_cGraph_of_flat`, which lets the one-step §4 theorem (`contract_step_sound_and_small''`)
be applied level by level.

Main results: `four_pow_mul_lvlVerts_le` (`4^d · |verts| ≤ |P|` at every depth),
`tower_sound` (an MSF at depth `d` splices to an MSF of the original instance) and
`tower_small` (`4^(d+1) · |B| ≤ |P|` for an MSF at depth `d + 1`).
-/
import DLMST.ContractSize

open Classical

namespace DLMST

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]

/-! ## Levels -/

/-- The two-phase forest built from the empty forest (the `F` of `isForest_phaseChain`). -/
noncomputable def phaseChain (G : WGraph V E) (B : Finset E) : ℕ → Finset E
  | 0 => ∅
  | n + 1 => phaseChain G B n ∪ phaseIn G B (phaseChain G B n)

/-- The contracted graph read back on the ambient edge type.  Its endpoints are the
representatives of the ends of the *ambient* edge, so `cGraph` is this graph with the edge type
restricted to the cross edges. -/
noncomputable def cGraphFlat (G : WGraph V E) (P : Finset V) (F : Finset E) : WGraph V E where
  endpoints e := (repOf G P F (G.src e), repOf G P F (G.dst e))
  weight e := G.weight e

/-- One §4 level: graph, vertex set, admissible edges, and the level's two-phase forest.  The
recursion is a single structural descent because the forest is stored alongside the data that
produces it. -/
noncomputable def lvlData (G : WGraph V E) (P : Finset V) (E₀ : Finset E) :
    ℕ → WGraph V E × Finset V × Finset E × Finset E
  | 0 => (G, P, E₀, phaseChain G E₀ 2)
  | d + 1 =>
      let g := lvlData G P E₀ d
      let G' : WGraph V E := g.1
      let P' : Finset V := g.2.1
      let E' : Finset E := g.2.2.1
      let F' : Finset E := g.2.2.2
      (cGraphFlat G' P' F', repSet G' P' F', crossE G' F' E',
        phaseChain (cGraphFlat G' P' F') (crossE G' F' E') 2)

noncomputable def lvlGraph (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (d : ℕ) :
    WGraph V E :=
  (lvlData G P E₀ d).1

noncomputable def lvlVerts (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (d : ℕ) :
    Finset V :=
  (lvlData G P E₀ d).2.1

noncomputable def lvlE (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (d : ℕ) : Finset E :=
  (lvlData G P E₀ d).2.2.1

noncomputable def lvlForest (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (d : ℕ) :
    Finset E :=
  (lvlData G P E₀ d).2.2.2

theorem lvlGraph_succ (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (d : ℕ) :
    lvlGraph G P E₀ (d + 1) =
      cGraphFlat (lvlGraph G P E₀ d) (lvlVerts G P E₀ d) (lvlForest G P E₀ d) := rfl

theorem lvlVerts_succ (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (d : ℕ) :
    lvlVerts G P E₀ (d + 1) =
      repSet (lvlGraph G P E₀ d) (lvlVerts G P E₀ d) (lvlForest G P E₀ d) := rfl

theorem lvlE_succ (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (d : ℕ) :
    lvlE G P E₀ (d + 1) =
      crossE (lvlGraph G P E₀ d) (lvlForest G P E₀ d) (lvlE G P E₀ d) := rfl

theorem lvlGraph_src_succ (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (d : ℕ) (e : E) :
    (lvlGraph G P E₀ (d + 1)).src e =
      repOf (lvlGraph G P E₀ d) (lvlVerts G P E₀ d) (lvlForest G P E₀ d)
        ((lvlGraph G P E₀ d).src e) := rfl

theorem lvlGraph_dst_succ (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (d : ℕ) (e : E) :
    (lvlGraph G P E₀ (d + 1)).dst e =
      repOf (lvlGraph G P E₀ d) (lvlVerts G P E₀ d) (lvlForest G P E₀ d)
        ((lvlGraph G P E₀ d).dst e) := rfl

/-- Each level's forest is its instance's two-phase chain. -/
theorem lvlForest_eq_chain (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (d : ℕ) :
    lvlForest G P E₀ d = phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) 2 := by
  cases d with
  | zero => rfl
  | succ n => rfl

/-- The vertex-set form of the level's forest, matching `four_mul_repSet_card_le`'s shape. -/
theorem lvlVerts_succ_chain (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (d : ℕ) :
    lvlVerts G P E₀ (d + 1) =
      repSet (lvlGraph G P E₀ d) (lvlVerts G P E₀ d)
        (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) 2) := by
  rw [lvlVerts_succ, lvlForest_eq_chain]

/-! ## The level chain -/

/-- Every level's edges end in that level's vertex set. -/
theorem lvl_hPE {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (d : ℕ) :
    ∀ e ∈ lvlE G P E₀ d,
      (lvlGraph G P E₀ d).src e ∈ lvlVerts G P E₀ d ∧
        (lvlGraph G P E₀ d).dst e ∈ lvlVerts G P E₀ d := by
  induction d with
  | zero => exact hPE
  | succ n ih =>
      intro e he
      have he' : e ∈ lvlE G P E₀ n := by
        rw [lvlE_succ] at he
        exact crossE_subset (G := lvlGraph G P E₀ n) (lvlForest G P E₀ n) (lvlE G P E₀ n) he
      obtain ⟨hs, hd⟩ := ih e he'
      constructor
      · rw [lvlGraph_src_succ, lvlVerts_succ]
        exact repOf_mem_repSet (G := lvlGraph G P E₀ n) (lvlVerts G P E₀ n) (lvlForest G P E₀ n) hs
      · rw [lvlGraph_dst_succ, lvlVerts_succ]
        exact repOf_mem_repSet (G := lvlGraph G P E₀ n) (lvlVerts G P E₀ n) (lvlForest G P E₀ n) hd

/-- Every level's vertex set is nonempty. -/
theorem lvlVerts_pos {G : WGraph V E} {P : Finset V} {E₀ : Finset E} (hP : 0 < P.card) (d : ℕ) :
    0 < (lvlVerts G P E₀ d).card := by
  induction d with
  | zero => exact hP
  | succ n ih =>
      rw [lvlVerts_succ]
      exact repSet_card_pos (G := lvlGraph G P E₀ n) (P := lvlVerts G P E₀ n)
        (F := lvlForest G P E₀ n) ih

/-- Every level's vertex set sits inside the instance's. -/
theorem lvlVerts_subset {G : WGraph V E} {P : Finset V} {E₀ : Finset E} (d : ℕ) :
    lvlVerts G P E₀ d ⊆ P := by
  induction d with
  | zero => intro x hx; exact hx
  | succ n ih =>
      rw [lvlVerts_succ]
      exact (repSet_subset (G := lvlGraph G P E₀ n) (P := lvlVerts G P E₀ n)
        (F := lvlForest G P E₀ n)).trans ih

/-- Every level has at most `|P|` vertices (no activation needed). -/
theorem lvlVerts_card_le {G : WGraph V E} {P : Finset V} {E₀ : Finset E} (d : ℕ) :
    (lvlVerts G P E₀ d).card ≤ P.card :=
  Finset.card_le_card (lvlVerts_subset d)

/-- **The measure quarters at every depth.**  Two phases shrink the vertex set by a factor of
four, level after level, so `4^d · |verts at depth d| ≤ |P|`. -/
theorem four_pow_mul_lvlVerts_le {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (_hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) : 4 ^ d * (lvlVerts G P E₀ d).card ≤ P.card := by
  induction d with
  | zero => simp [lvlVerts, lvlData]
  | succ n ih =>
      have h4 : 4 * (lvlVerts G P E₀ (n + 1)).card ≤ (lvlVerts G P E₀ n).card := by
        rw [lvlVerts_succ_chain]
        exact four_mul_repSet_card_le (G := lvlGraph G P E₀ n) (P := lvlVerts G P E₀ n) 2
          (by norm_num) (lvlE G P E₀ n) (phaseChain (lvlGraph G P E₀ n) (lvlE G P E₀ n))
          rfl (fun i => rfl) (lvl_hPE hPE n) (hact n)
      calc 4 ^ (n + 1) * (lvlVerts G P E₀ (n + 1)).card
          = 4 ^ n * (4 * (lvlVerts G P E₀ (n + 1)).card) := by
            rw [pow_succ]; ring
        _ ≤ 4 ^ n * (lvlVerts G P E₀ n).card := Nat.mul_le_mul_left _ h4
        _ ≤ P.card := ih

/-! ## Reading the contracted graph back on the ambient edge type -/

/-- Connectivity agrees between the contracted graph and its ambient reading. -/
theorem conn_cGraphFlat_iff {G : WGraph V E} {P : Finset V} {F : Finset E} {E₀ : Finset E}
    {A : Finset {e // e ∈ crossE G F E₀}} {u v : V} :
    Conn (cGraph G P F E₀) A u v ↔ Conn (cGraphFlat G P F) (A.image Subtype.val) u v := by
  constructor
  · intro h
    induction h with
    | refl w => exact Conn.refl w
    | step e he => exact Conn.step e.1 (Finset.mem_image.mpr ⟨e, he, rfl⟩)
    | symm _ ih => exact ih.symm
    | trans _ _ ih1 ih2 => exact ih1.trans ih2
  · intro h
    induction h with
    | refl w => exact Conn.refl w
    | step e he =>
        obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
        exact Conn.step e' he'
    | symm _ ih => exact ih.symm
    | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- A child forest reads upstairs as a forest. -/
theorem isForest_image_of_cGraph {G : WGraph V E} {P : Finset V} {F : Finset E}
    {E₀ : Finset E} {A : Finset {e // e ∈ crossE G F E₀}}
    (h : IsForest (cGraph G P F E₀) A) :
    IsForest (cGraphFlat G P F) (A.image Subtype.val) := by
  induction h with
  | empty => exact IsForest.empty
  | @add A₀ e _ he hc ih =>
      rw [Finset.image_insert]
      refine IsForest.add ih ?_ ?_
      · exact he
      · intro hconn
        exact hc ((conn_cGraphFlat_iff (A := A₀)).2 hconn)

/-- A forest on the ambient reading whose edges are cross edges comes from a child forest. -/
theorem isForest_cGraph_of_image {G : WGraph V E} {P : Finset V} {F : Finset E}
    {E₀ : Finset E} {A : Finset {e // e ∈ crossE G F E₀}}
    (h : IsForest (cGraphFlat G P F) (A.image Subtype.val)) :
    IsForest (cGraph G P F E₀) A := by
  induction A using Finset.induction with
  | empty => exact IsForest.empty
  | insert a A₀ ha ih =>
      have himg : (insert a A₀).image Subtype.val = insert a.1 (A₀.image Subtype.val) := by
        simp
      rw [himg] at h
      have hA₀ : IsForest (cGraphFlat G P F) (A₀.image Subtype.val) :=
        h.subset (Finset.subset_insert _ _)
      have hins : IsForest (cGraph G P F E₀) A₀ := ih hA₀
      have hne : (cGraph G P F E₀).src a ≠ (cGraph G P F E₀).dst a :=
        h.nloop (Finset.mem_insert_self a.1 (A₀.image Subtype.val))
      refine IsForest.add hins hne ?_
      intro hconn
      have hbridge := h.bridge (Finset.mem_insert_self a.1 (A₀.image Subtype.val))
      have hnotin : a.1 ∉ A₀.image Subtype.val := by
        intro hmem
        obtain ⟨b, hb, hbeq⟩ := Finset.mem_image.mp hmem
        exact ha (by rw [← Subtype.val_injective hbeq]; exact hb)
      rw [Finset.erase_insert hnotin] at hbridge
      exact hbridge ((conn_cGraphFlat_iff (A := A₀)).1 hconn)

/-- Weights agree between a child set and its ambient reading. -/
theorem wsum_cGraphFlat_image {G : WGraph V E} {P : Finset V} {F : Finset E} {E₀ : Finset E}
    {A : Finset {e // e ∈ crossE G F E₀}} :
    wsum (cGraphFlat G P F) (A.image Subtype.val) = wsum (cGraph G P F E₀) A := by
  rw [wsum, wsum, Finset.sum_image (fun a _ b _ h => Subtype.val_injective h)]
  rfl

/-- **The one-step theorem, read on the ambient edge type.**  If `B` is an MSF of the flattened
child (edge set `crossE`, graph `cGraphFlat`), then its subtype form is an MSF of the real child
on `univ`.  This is the bridge that lets `contract_step_sound_and_small''` run level by level. -/
theorem isMSFOf_cGraph_of_flat {G : WGraph V E} {P : Finset V} {F : Finset E} {E₀ : Finset E}
    {B : Finset {e // e ∈ crossE G F E₀}}
    (h : IsMSFOf (cGraphFlat G P F) (crossE G F E₀) (B.image Subtype.val)) :
    IsMSFOf (cGraph G P F E₀) (Finset.univ : Finset {e // e ∈ crossE G F E₀}) B := by
  obtain ⟨⟨hf, hsub, hsp⟩, hmin⟩ := h
  refine ⟨⟨?_, fun _ _ => Finset.mem_univ _, ?_⟩, ?_⟩
  · exact isForest_cGraph_of_image hf
  · intro e' _ hne
    have hne' : (cGraphFlat G P F).src e'.1 ≠ (cGraphFlat G P F).dst e'.1 := hne
    exact (conn_cGraphFlat_iff (A := B)).2 (hsp e'.1 e'.2 hne')
  · intro T' hT'
    have hT'' : IsSpanningForestOf (cGraphFlat G P F) (crossE G F E₀) (T'.image Subtype.val) := by
      refine ⟨isForest_image_of_cGraph hT'.1, ?_, ?_⟩
      · intro e he
        obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp he
        exact y.2
      · intro e he hne
        have hchild : Conn (cGraph G P F E₀) T' ((cGraph G P F E₀).src ⟨e, he⟩)
            ((cGraph G P F E₀).dst ⟨e, he⟩) :=
          hT'.2.2 ⟨e, he⟩ (Finset.mem_univ _) hne
        exact (conn_cGraphFlat_iff (A := T')).1 hchild
    have hw := hmin (T'.image Subtype.val) hT''
    rwa [wsum_cGraphFlat_image (A := B), wsum_cGraphFlat_image (A := T')] at hw

/-! ## The tower -/

/-- The answer at depth `d`, read upstairs: the level forests `0, …, d-1` spliced with the answer
`B` returned at depth `d`. -/
noncomputable def answer (G : WGraph V E) (P : Finset V) (E₀ : Finset E) :
    ℕ → Finset E → Finset E
  | 0, B => B
  | d + 1, B => answer G P E₀ d (lvlForest G P E₀ d ∪ B)

/-- **§4 terminates at every depth, and the answer is an MSF of the original instance.**  If the
level-`d` instance has an MSF `B` (on the ambient edge type), then splicing the level forests on
the way down gives an MSF of `G[E₀]`. -/
theorem tower_sound {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (B : Finset E) (hB : IsMSFOf (lvlGraph G P E₀ d) (lvlE G P E₀ d) B) :
    IsMSFOf G E₀ (answer G P E₀ d B) ∧ 4 ^ d * (lvlVerts G P E₀ d).card ≤ P.card := by
  induction d generalizing B with
  | zero =>
      refine ⟨hB, ?_⟩
      simp [lvlVerts, lvlData]
  | succ n ih =>
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
      obtain ⟨hMSF, -, -⟩ :=
        contract_step_sound_and_small'' (G := lvlGraph G P E₀ n) (P := lvlVerts G P E₀ n)
          (E₀ := lvlE G P E₀ n) 2 (by norm_num)
          (phaseChain (lvlGraph G P E₀ n) (lvlE G P E₀ n)) rfl (fun i => rfl)
          (hact n) (lvl_hPE hPE n) hchild (lvlVerts_pos hP n)
      have hMSF' : IsMSFOf (lvlGraph G P E₀ n) (lvlE G P E₀ n) (lvlForest G P E₀ n ∪ B) := by
        rw [hFS, ← himg]
        exact hMSF
      exact ⟨(ih (lvlForest G P E₀ n ∪ B) hMSF').1,
        four_pow_mul_lvlVerts_le hPE hP hact (n + 1)⟩

/-- **The MSF half of the tower, activating only strictly above a stopping depth.**

Once a level's instance has collapsed to at most one vertex there is no phase left to run, so an
honest interface only needs the phase data *above* the level where the recursion stops.  This is
the MSF half of `tower_sound` with that weaker hypothesis (the measure half genuinely needs the
phases at the bottom level and is not claimed here). -/
theorem tower_sound_bd {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (D : ℕ)
    (hact : ∀ (d i : ℕ), d < D → i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (hd : d ≤ D) (B : Finset E)
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
      have hnD : n < D := Nat.lt_of_succ_le hd
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
      obtain ⟨hMSF, -, -⟩ :=
        contract_step_sound_and_small'' (G := lvlGraph G P E₀ n) (P := lvlVerts G P E₀ n)
          (E₀ := lvlE G P E₀ n) 2 (by norm_num)
          (phaseChain (lvlGraph G P E₀ n) (lvlE G P E₀ n)) rfl (fun i => rfl)
          (fun i hi => hact n i hnD hi) (lvl_hPE hPE n) hchild (lvlVerts_pos hP n)
      have hMSF' : IsMSFOf (lvlGraph G P E₀ n) (lvlE G P E₀ n) (lvlForest G P E₀ n ∪ B) := by
        rw [hFS, ← himg]
        exact hMSF
      exact ih (Nat.le_of_succ_le hd) (lvlForest G P E₀ n ∪ B) hMSF'

/-- **The edge count at depth `d + 1`.**  An MSF of the depth-`(d+1)` instance is a forest on the
depth-`(d+1)` vertex set, so it has at most that many edges, and the measure quarters. -/
theorem tower_small {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (B : Finset E)
    (hB : IsMSFOf (lvlGraph G P E₀ (d + 1)) (lvlE G P E₀ (d + 1)) B) :
    4 ^ (d + 1) * B.card ≤ P.card := by
  have hBcard : B.card ≤ (lvlVerts G P E₀ (d + 1)).card :=
    card_le_card_of_isForest_of_ends hB.1.1 fun e he =>
      lvl_hPE hPE (d + 1) e (hB.1.2.1 he)
  calc 4 ^ (d + 1) * B.card
      ≤ 4 ^ (d + 1) * (lvlVerts G P E₀ (d + 1)).card := Nat.mul_le_mul_left _ hBcard
    _ ≤ P.card := four_pow_mul_lvlVerts_le hPE hP hact (d + 1)

/-! ## The telescopes

The answer at depth `d` is the disjoint union of the level forests and the returned `B`.  Hence
both the total weight and the total size are the sums of the per-level accounts.  The
disjointness is nesting: `lvlE (j + 1) ⊆ lvlE j`, and level `j + 1`'s edges are cross edges of
level `j`'s forest (so disjoint from it). -/

section Telescopes

variable (G : WGraph V E) (P : Finset V) (E₀ : Finset E)

/-- Weights are inherited level by level: every level weighs with `G.weight`. -/
theorem lvlGraph_weight (d : ℕ) (e : E) :
    (lvlGraph G P E₀ d).weight e = G.weight e := by
  induction d with
  | zero => rfl
  | succ n ih =>
      rw [lvlGraph_succ]
      exact ih

/-- The weight sum of a level is the ambient one. -/
theorem wsum_lvlGraph (d : ℕ) (A : Finset E) :
    wsum (lvlGraph G P E₀ d) A = wsum G A := by
  rw [wsum, wsum]
  exact Finset.sum_congr rfl fun e _ => lvlGraph_weight G P E₀ d e

/-- A two-phase chain only ever adds edges of its instance. -/
theorem phaseChain_subset (B : Finset E) (n : ℕ) : phaseChain G B n ⊆ B := by
  induction n with
  | zero => exact Finset.empty_subset B
  | succ n ih => exact Finset.union_subset ih (phaseIn_subset B (phaseChain G B n))

theorem lvlForest_succ (d : ℕ) :
    lvlForest G P E₀ (d + 1) =
      phaseChain (cGraphFlat (lvlGraph G P E₀ d) (lvlVerts G P E₀ d) (lvlForest G P E₀ d))
        (crossE (lvlGraph G P E₀ d) (lvlForest G P E₀ d) (lvlE G P E₀ d)) 2 := rfl

/-- Each level's forest lies in the level's instance edges. -/
theorem lvlForest_subset_lvlE (d : ℕ) :
    lvlForest G P E₀ d ⊆ lvlE G P E₀ d := by
  cases d with
  | zero => exact phaseChain_subset G E₀ 2
  | succ n =>
      rw [lvlForest_succ, lvlE_succ]
      exact phaseChain_subset _ _ 2

/-- Instance edges nest: the child instance's edges are cross edges of the parent instance. -/
theorem lvlE_succ_subset (d : ℕ) : lvlE G P E₀ (d + 1) ⊆ lvlE G P E₀ d := by
  rw [lvlE_succ]
  exact crossE_subset (G := lvlGraph G P E₀ d) (F := lvlForest G P E₀ d) (E₀ := lvlE G P E₀ d)

/-- A level's forest is disjoint from the next level's edges. -/
theorem disjoint_lvlForest_lvlE_succ (d : ℕ) :
    Disjoint (lvlForest G P E₀ d) (lvlE G P E₀ (d + 1)) := by
  rw [lvlE_succ]
  exact disjoint_crossE_F (G := lvlGraph G P E₀ d) (F := lvlForest G P E₀ d)
    (E₀ := lvlE G P E₀ d)

/-- Anything inside the next level's edges misses this level's forest. -/
theorem disjoint_lvlForest_of_subset {d : ℕ} {X : Finset E}
    (hX : X ⊆ lvlE G P E₀ (d + 1)) : Disjoint (lvlForest G P E₀ d) X := by
  rw [Finset.disjoint_left]
  intro e heF heX
  exact (Finset.disjoint_left.1 (disjoint_lvlForest_lvlE_succ G P E₀ d) heF) (hX heX)

/-- **The weight telescope.**  The answer's weight is the sum of the level-forest weights plus the
weight of the deepest answer `B` (all read on the ambient graph). -/
theorem tower_wsum (d : ℕ) (B : Finset E) (hB : B ⊆ lvlE G P E₀ d) :
    wsum G (answer G P E₀ d B) =
      Finset.sum (Finset.range d) (fun j => wsum G (lvlForest G P E₀ j)) + wsum G B := by
  induction d generalizing B with
  | zero => simp [answer]
  | succ n ih =>
      rw [answer]
      have hsub : lvlForest G P E₀ n ∪ B ⊆ lvlE G P E₀ n := by
        refine Finset.union_subset (lvlForest_subset_lvlE G P E₀ n) ?_
        exact fun e he => lvlE_succ_subset G P E₀ n (hB he)
      rw [ih (lvlForest G P E₀ n ∪ B) hsub, Finset.sum_range_succ]
      have hdisj : Disjoint (lvlForest G P E₀ n) B := disjoint_lvlForest_of_subset G P E₀ hB
      have hsplit : wsum G (lvlForest G P E₀ n ∪ B) =
          wsum G (lvlForest G P E₀ n) + wsum G B := by
        rw [wsum]
        exact Finset.sum_union hdisj
      rw [hsplit]
      ring

/-- The weight telescope in the physically meaningful form: each level's forest is weighed by its
own level graph. -/
theorem tower_wsum_lvl (d : ℕ) (B : Finset E) (hB : B ⊆ lvlE G P E₀ d) :
    wsum G (answer G P E₀ d B) =
      Finset.sum (Finset.range d)
        (fun j => wsum (lvlGraph G P E₀ j) (lvlForest G P E₀ j)) +
      wsum (lvlGraph G P E₀ d) B := by
  rw [tower_wsum G P E₀ d B hB]
  simp only [wsum_lvlGraph]

/-- **The size telescope**: the answer's cardinality is the sum of the per-level sizes. -/
theorem tower_card (d : ℕ) (B : Finset E) (hB : B ⊆ lvlE G P E₀ d) :
    (answer G P E₀ d B).card =
      Finset.sum (Finset.range d) (fun j => (lvlForest G P E₀ j).card) + B.card := by
  induction d generalizing B with
  | zero => simp [answer]
  | succ n ih =>
      rw [answer]
      have hsub : lvlForest G P E₀ n ∪ B ⊆ lvlE G P E₀ n := by
        refine Finset.union_subset (lvlForest_subset_lvlE G P E₀ n) ?_
        exact fun e he => lvlE_succ_subset G P E₀ n (hB he)
      rw [ih (lvlForest G P E₀ n ∪ B) hsub, Finset.sum_range_succ]
      have hdisj : Disjoint (lvlForest G P E₀ n) B := disjoint_lvlForest_of_subset G P E₀ hB
      rw [Finset.card_union_of_disjoint hdisj]
      ring

end Telescopes

/-! ## Activation at every level

The tower's `hact` says every vertex of a level has an outgoing instance edge in each phase.  By
`hact_of_conn_E₀` this follows level by level from structural input: each level's instance is
connected (on the ambient vertex type), and each phase forest has at least two components. -/

section Activation

variable (G : WGraph V E) (P : Finset V) (E₀ : Finset E)

/-- **Activation from per-level connectivity.** -/
theorem tower_hact_of_lvl_conn
    (hconn : ∀ d : ℕ, ∀ u w : V, Conn (lvlGraph G P E₀ d) (lvlE G P E₀ d) u w)
    (hc : ∀ (d i : ℕ), i < 2 →
      2 ≤ compCount (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i)) :
    ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e :=
  fun d i hi =>
    hact_of_conn_E₀ 2 (G := lvlGraph G P E₀ d) (P := lvlVerts G P E₀ d) (E₀ := lvlE G P E₀ d)
      (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d)) (hconn d) (fun i hi => hc d i hi) i hi

/-- **Activation from per-level connectivity *inside* each level.**  The level graphs need not
connect vertices that stopped being representatives; connectivity restricted to `lvlVerts` and the
instance count `compCountOn` suffice (`hact_of_connOn_E₀`). -/
theorem tower_hact_of_lvl_connOn
    (hconn : ∀ d : ℕ, ∀ u ∈ lvlVerts G P E₀ d, ∀ w ∈ lvlVerts G P E₀ d,
      Conn (lvlGraph G P E₀ d) (lvlE G P E₀ d) u w)
    (hc : ∀ (d i : ℕ), i < 2 →
      2 ≤ compCountOn (lvlGraph G P E₀ d) (lvlVerts G P E₀ d)
        (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i)) :
    ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e :=
  fun d i hi =>
    hact_of_connOn_E₀ 2 (G := lvlGraph G P E₀ d) (P := lvlVerts G P E₀ d) (E₀ := lvlE G P E₀ d)
      (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d)) (hconn d) (fun i hi => hc d i hi) i hi

/-! ### Level connectivity from the root's connectivity

The tower's activation `hact` only needs each level's instance to connect its *own* vertices, and
that connectivity is preserved downward: contracting a connected instance along a forest leaves the
representatives connected, and the cross edges are exactly the level's edge set. -/

/-- Within `F ∪ crossE`, the whole instance edge set is connected: a supported edge is replaced by
the `F`-path that supports it. -/
theorem conn_union_crossE_of_conn {G : WGraph V E} {F E₀ : Finset E} {u v : V}
    (h : Conn G E₀ u v) : Conn G (F ∪ crossE G F E₀) u v := by
  induction h with
  | refl w => exact Conn.refl w
  | step e he =>
      by_cases heF : e ∈ F
      · exact Conn.step e (Finset.mem_union_left _ heF)
      · by_cases hc : Conn G F (G.src e) (G.dst e)
        · exact Conn.mono (Finset.subset_union_left) hc
        · exact Conn.step e (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨he, hc⟩))
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- **Contraction keeps representatives connected**: a connected instance, read on the ambient edge
type through `cGraphFlat`, connects its representatives along the cross edges. -/
theorem conn_cGraphFlat_of_conn {G : WGraph V E} {P : Finset V} {F E₀ : Finset E}
    (hF : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P)
    {u v : V} (hu : u ∈ repSet G P F) (hv : v ∈ repSet G P F)
    (h : Conn G (F ∪ crossE G F E₀) u v) :
    Conn (cGraphFlat G P F) (crossE G F E₀) u v := by
  have h1 : Conn (cGraph G P F E₀)
      ((crossE G F E₀).subtype (fun e => e ∈ crossE G F E₀))
      (repOf G P F u) (repOf G P F v) :=
    conn_cGraph_of_conn (G := G) (P := P) (F := F) (E₀ := E₀) hF
      (B := crossE G F E₀) (fun e he => he) h
  rw [repOf_repSet (G := G) (P := P) (F := F) hu,
    repOf_repSet (G := G) (P := P) (F := F) hv] at h1
  have h2 := (conn_cGraphFlat_iff (G := G) (P := P) (F := F) (E₀ := E₀)
    (A := (crossE G F E₀).subtype (fun e => e ∈ crossE G F E₀))).1 h1
  rwa [image_subtype_crossE (G := G) (F := F) (E₀ := E₀) (B := crossE G F E₀)
    (fun e he => he)] at h2

/-- **One level down**: connectivity inside level `d` gives connectivity inside level `d+1`. -/
theorem lvl_conn_succ {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (d : ℕ)
    (hconn : ∀ u ∈ lvlVerts G P E₀ d, ∀ w ∈ lvlVerts G P E₀ d,
      Conn (lvlGraph G P E₀ d) (lvlE G P E₀ d) u w) :
    ∀ u ∈ lvlVerts G P E₀ (d + 1), ∀ w ∈ lvlVerts G P E₀ (d + 1),
      Conn (lvlGraph G P E₀ (d + 1)) (lvlE G P E₀ (d + 1)) u w := by
  intro u hu w hw
  have hF : ∀ e ∈ lvlForest G P E₀ d,
      (lvlGraph G P E₀ d).src e ∈ lvlVerts G P E₀ d ∧
      (lvlGraph G P E₀ d).dst e ∈ lvlVerts G P E₀ d :=
    fun e he => lvl_hPE hPE d e (lvlForest_subset_lvlE G P E₀ d he)
  have hu0 : u ∈ lvlVerts G P E₀ d :=
    repSet_subset (G := lvlGraph G P E₀ d) (P := lvlVerts G P E₀ d)
      (F := lvlForest G P E₀ d) hu
  have hw0 : w ∈ lvlVerts G P E₀ d :=
    repSet_subset (G := lvlGraph G P E₀ d) (P := lvlVerts G P E₀ d)
      (F := lvlForest G P E₀ d) hw
  have h1 := conn_cGraphFlat_of_conn (G := lvlGraph G P E₀ d) (P := lvlVerts G P E₀ d)
    (F := lvlForest G P E₀ d) (E₀ := lvlE G P E₀ d) hF hu hw
    (conn_union_crossE_of_conn (hconn u hu0 w hw0))
  simpa only [lvlGraph_succ, lvlE_succ] using h1

/-- **Every level connects its own vertices**, from root connectivity alone. -/
theorem lvl_connOn_of_root_conn {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hconn : ∀ u ∈ P, ∀ w ∈ P, Conn G E₀ u w) :
    ∀ d : ℕ, ∀ u ∈ lvlVerts G P E₀ d, ∀ w ∈ lvlVerts G P E₀ d,
      Conn (lvlGraph G P E₀ d) (lvlE G P E₀ d) u w := by
  intro d
  induction d with
  | zero => intro u hu w hw; exact hconn u hu w hw
  | succ n ih => exact lvl_conn_succ hPE n ih

/-- **§4 termination, with activation from instance-internal connectivity.** -/
theorem tower_sound_connOn {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hconn : ∀ d : ℕ, ∀ u ∈ lvlVerts G P E₀ d, ∀ w ∈ lvlVerts G P E₀ d,
      Conn (lvlGraph G P E₀ d) (lvlE G P E₀ d) u w)
    (hc : ∀ (d i : ℕ), i < 2 →
      2 ≤ compCountOn (lvlGraph G P E₀ d) (lvlVerts G P E₀ d)
        (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i))
    (d : ℕ) (B : Finset E) (hB : IsMSFOf (lvlGraph G P E₀ d) (lvlE G P E₀ d) B) :
    IsMSFOf G E₀ (answer G P E₀ d B) ∧ 4 ^ d * (lvlVerts G P E₀ d).card ≤ P.card :=
  tower_sound hPE hP (tower_hact_of_lvl_connOn G P E₀ hconn hc) d B hB

/-- **Activation from root connectivity alone** (per-level component counts stay as data). -/
theorem tower_hact_of_root_conn {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hconn : ∀ u ∈ P, ∀ w ∈ P, Conn G E₀ u w)
    (hc : ∀ (d i : ℕ), i < 2 →
      2 ≤ compCountOn (lvlGraph G P E₀ d) (lvlVerts G P E₀ d)
        (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i)) :
    ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e :=
  tower_hact_of_lvl_connOn G P E₀ (lvl_connOn_of_root_conn hPE hconn) hc

/-- **§4 termination, with activation derived.**  `tower_sound` with `hact` replaced by per-level
connectivity and non-generation. -/
theorem tower_sound_conn {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hconn : ∀ d : ℕ, ∀ u w : V, Conn (lvlGraph G P E₀ d) (lvlE G P E₀ d) u w)
    (hc : ∀ (d i : ℕ), i < 2 →
      2 ≤ compCount (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i))
    (d : ℕ) (B : Finset E) (hB : IsMSFOf (lvlGraph G P E₀ d) (lvlE G P E₀ d) B) :
    IsMSFOf G E₀ (answer G P E₀ d B) ∧ 4 ^ d * (lvlVerts G P E₀ d).card ≤ P.card :=
  tower_sound hPE hP (tower_hact_of_lvl_conn G P E₀ hconn hc) d B hB

/-- **The edge count at depth `d + 1`, with activation derived.** -/
theorem tower_small_conn {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hconn : ∀ d : ℕ, ∀ u w : V, Conn (lvlGraph G P E₀ d) (lvlE G P E₀ d) u w)
    (hc : ∀ (d i : ℕ), i < 2 →
      2 ≤ compCount (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i))
    (d : ℕ) (B : Finset E)
    (hB : IsMSFOf (lvlGraph G P E₀ (d + 1)) (lvlE G P E₀ (d + 1)) B) :
    4 ^ (d + 1) * B.card ≤ P.card :=
  tower_small hPE hP (tower_hact_of_lvl_conn G P E₀ hconn hc) d B hB

end Activation

/-! ## The bottom of the tower

`tower_sound` takes the deepest level's MSF as input.  At a depth where the level's vertex set has
shrunk to a single vertex there is nothing left to choose: every level edge is a loop, so the empty
forest is the level's MSF.  With `|P| ≤ 4^d` the measure forces exactly that, so §4 needs no bottom
call at all — it terminates. -/

section Termination

/-- Every level's edge set sits inside the instance. -/
theorem lvlE_subset (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (d : ℕ) :
    lvlE G P E₀ d ⊆ E₀ := by
  induction d with
  | zero => exact Finset.Subset.refl E₀
  | succ n ih => exact (lvlE_succ_subset G P E₀ n).trans ih

/-- **A one-vertex instance has only loops**, so its only forest is the empty one and that is its
MSF — with no sign assumption on weights, since every spanning forest is empty. -/
theorem isMSFOf_empty_of_card_le_one {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : P.card ≤ 1) :
    IsMSFOf G E₀ (∅ : Finset E) := by
  have hloop : ∀ e ∈ E₀, G.src e = G.dst e := by
    intro e he
    obtain ⟨h1, h2⟩ := hPE e he
    exact Finset.card_le_one.mp hP (G.src e) h1 (G.dst e) h2
  refine ⟨⟨IsForest.empty, Finset.empty_subset E₀, ?_⟩, ?_⟩
  · intro e he hne
    exact absurd (hloop e he) hne
  · intro T' hT'
    have hempty : T' = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun e he => ?_
      exact hT'.1.nloop he (hloop e (hT'.2.1 he))
    rw [hempty]

/-- **§4 stops and is correct**: if the depth-`D` instance has collapsed to at most one vertex and
the phases are activated at every level above `D`, then the spliced answer at depth `D` (with no
bottom call) is an MSF of the original instance.  Unlike `tower_terminates`, the activation
assumption here is consistent: it never asks a collapsed level to produce an outgoing edge. -/
theorem tower_msf_of_stop {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (D : ℕ)
    (hact : ∀ (d i : ℕ), d < D → i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (hstop : (lvlVerts G P E₀ D).card ≤ 1) :
    IsMSFOf G E₀ (answer G P E₀ D ∅) :=
  tower_sound_bd hPE hP D hact D le_rfl ∅
    (isMSFOf_empty_of_card_le_one (lvl_hPE hPE D) hstop)

/-- The stopping answer is a forest on the instance, so it has at most `|P| - 1` edges. -/
theorem tower_msf_of_stop_card {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (D : ℕ)
    (hact : ∀ (d i : ℕ), d < D → i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (hstop : (lvlVerts G P E₀ D).card ≤ 1) :
    (answer G P E₀ D ∅).card ≤ P.card - 1 := by
  have h := tower_msf_of_stop hPE hP D hact hstop
  exact card_le_card_sub_one_of_isForest_of_ends (G := G) (F := answer G P E₀ D ∅) h.1.1
    (fun e he => hPE e (h.1.2.1 he)) hP

/-- **The measure forces the bottom**: at any depth with `|P| ≤ 4^d`, the level's vertex set has at
most one vertex. -/
theorem lvlVerts_card_le_one {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (hd : P.card ≤ 4 ^ d) : (lvlVerts G P E₀ d).card ≤ 1 := by
  have h4 := four_pow_mul_lvlVerts_le hPE hP hact d
  have hpow : 0 < 4 ^ d := Nat.pow_pos (by norm_num)
  have hle : 4 ^ d * (lvlVerts G P E₀ d).card ≤ 4 ^ d * 1 := by
    calc 4 ^ d * (lvlVerts G P E₀ d).card ≤ P.card := h4
      _ ≤ 4 ^ d := hd
      _ = 4 ^ d * 1 := (Nat.mul_one _).symm
  exact Nat.le_of_mul_le_mul_left hle hpow

/-- **§4 terminates**: at any depth with `|P| ≤ 4^d` the recursion has no bottom call to make, and
splicing the level forests up gives an MSF of the original instance. -/
theorem tower_terminates {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (hd : P.card ≤ 4 ^ d) : IsMSFOf G E₀ (answer G P E₀ d ∅) :=
  (tower_sound hPE hP hact d ∅
    (isMSFOf_empty_of_card_le_one (lvl_hPE hPE d) (lvlVerts_card_le_one hPE hP hact d hd))).1

/-- The terminating answer is a forest on the instance, so it has at most `|P|` edges. -/
theorem tower_terminates_card {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (hd : P.card ≤ 4 ^ d) : (answer G P E₀ d ∅).card ≤ P.card :=
  have h := tower_terminates hPE hP hact d hd
  card_le_card_of_isForest_of_ends h.1.1 fun e he => hPE e (h.1.2.1 he)

end Termination

/-! ## Descent

The child of an instance is the level-`1` instance, and descending one level is the same as
shifting the tower: `lvlData G P E₀ (d+1)` is `lvlData` at the level-`1` instance, depth `d`.  So
the §4 recursion's child literally re-enters the tower, and an MSF at depth `d+1` yields the child's
own answer at depth `d`. -/

section Descent

/-- **The tower shifts by one**: the level-`(d+1)` data is the level-`1` child's level-`d` data. -/
theorem lvlData_shift (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (d : ℕ) :
    lvlData G P E₀ (d + 1) =
      lvlData (lvlGraph G P E₀ 1) (lvlVerts G P E₀ 1) (lvlE G P E₀ 1) d := by
  induction d with
  | zero => rfl
  | succ n ih =>
      conv_lhs => unfold lvlData
      conv_rhs => unfold lvlData
      rw [ih]

theorem lvlGraph_shift (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (d : ℕ) :
    lvlGraph G P E₀ (d + 1) =
      lvlGraph (lvlGraph G P E₀ 1) (lvlVerts G P E₀ 1) (lvlE G P E₀ 1) d :=
  congrArg (fun t => t.1) (lvlData_shift G P E₀ d)

theorem lvlVerts_shift (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (d : ℕ) :
    lvlVerts G P E₀ (d + 1) =
      lvlVerts (lvlGraph G P E₀ 1) (lvlVerts G P E₀ 1) (lvlE G P E₀ 1) d :=
  congrArg (fun t => t.2.1) (lvlData_shift G P E₀ d)

theorem lvlE_shift (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (d : ℕ) :
    lvlE G P E₀ (d + 1) =
      lvlE (lvlGraph G P E₀ 1) (lvlVerts G P E₀ 1) (lvlE G P E₀ 1) d :=
  congrArg (fun t => t.2.2.1) (lvlData_shift G P E₀ d)

theorem lvlForest_shift (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (d : ℕ) :
    lvlForest G P E₀ (d + 1) =
      lvlForest (lvlGraph G P E₀ 1) (lvlVerts G P E₀ 1) (lvlE G P E₀ 1) d :=
  congrArg (fun t => t.2.2.2) (lvlData_shift G P E₀ d)

/-- **Activation descends**: the child's `hact` is the parent's, shifted by one level. -/
theorem hact_shift {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e) :
    ∀ (k i : ℕ), i < 2 →
      ∀ v ∈ lvlVerts (lvlGraph G P E₀ 1) (lvlVerts G P E₀ 1) (lvlE G P E₀ 1) k,
      ∃ e ∈ lvlE (lvlGraph G P E₀ 1) (lvlVerts G P E₀ 1) (lvlE G P E₀ 1) k,
        leaves (lvlGraph (lvlGraph G P E₀ 1) (lvlVerts G P E₀ 1) (lvlE G P E₀ 1) k)
          (phaseChain (lvlGraph (lvlGraph G P E₀ 1) (lvlVerts G P E₀ 1) (lvlE G P E₀ 1) k)
            (lvlE (lvlGraph G P E₀ 1) (lvlVerts G P E₀ 1) (lvlE G P E₀ 1) k) i) v e := by
  intro k i hi v hv
  simp only [← lvlGraph_shift, ← lvlVerts_shift, ← lvlE_shift] at hv ⊢
  exact hact (k + 1) i hi v hv

/-- **The answer splices**: one more level of the parent is the level-`0` forest on top of the
child's own answer. -/
theorem answer_splice (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (d : ℕ) (B : Finset E) :
    answer G P E₀ (d + 1) B =
      lvlForest G P E₀ 0 ∪
        answer (lvlGraph G P E₀ 1) (lvlVerts G P E₀ 1) (lvlE G P E₀ 1) d B := by
  induction d generalizing B with
  | zero => rfl
  | succ n ih =>
      rw [answer]
      rw [ih (lvlForest G P E₀ (n + 1) ∪ B)]
      rw [answer, lvlForest_shift]

/-- **The recursion step, read on the child**: an MSF at the parent's depth `d+1` is the child's
own answer at depth `d` — and the child's measure is the parent's measure at that depth. -/
theorem tower_sound_child {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (B : Finset E)
    (hB : IsMSFOf (lvlGraph G P E₀ (d + 1)) (lvlE G P E₀ (d + 1)) B) :
    IsMSFOf (lvlGraph G P E₀ 1) (lvlE G P E₀ 1)
        (answer (lvlGraph G P E₀ 1) (lvlVerts G P E₀ 1) (lvlE G P E₀ 1) d B) ∧
      4 ^ d * (lvlVerts G P E₀ (d + 1)).card ≤ (lvlVerts G P E₀ 1).card := by
  obtain ⟨hMSF, hbud⟩ :=
    tower_sound (G := lvlGraph G P E₀ 1) (P := lvlVerts G P E₀ 1) (E₀ := lvlE G P E₀ 1)
      (lvl_hPE hPE 1) (lvlVerts_pos hP 1) (hact_shift hact) d B
      (by simpa only [← lvlGraph_shift, ← lvlE_shift] using hB)
  refine ⟨hMSF, ?_⟩
  rwa [← lvlVerts_shift] at hbud

/-- **The child terminates on its own**: at depth `d` inside the child (`|child| ≤ 4^d`), the empty
answer is the child's MSF — no bottom call. -/
theorem tower_terminates_child {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (hd : (lvlVerts G P E₀ 1).card ≤ 4 ^ d) :
    IsMSFOf (lvlGraph G P E₀ 1) (lvlE G P E₀ 1)
      (answer (lvlGraph G P E₀ 1) (lvlVerts G P E₀ 1) (lvlE G P E₀ 1) d ∅) :=
  tower_terminates (lvl_hPE hPE 1) (lvlVerts_pos hP 1) (hact_shift hact) d hd

end Descent

end DLMST