import DLMST.Filtering
import DLMST.Tree

/-!
# Fact 2.5: an MSF preserves connectivity at every weight threshold

§2 states, as a "standard property" and without proof:

> **Fact 2.5.** Let `G` be a graph, `S ⊆ E(G)` and `F = MSF(G[S])`. For any vertices `u, v` and
> threshold `k`, if `G[S]` contains a path from `u` to `v` using only edges of weight at most `k`,
> then `F≤k` connects `u` and `v`.

This is the load-bearing property behind two of the paper's moves.  In §3.2 the batch procedure
declares edges `D`, replaces `F` by `MSF(G[F ∪ D])`, and then claims that a declared representative
of weight `≤ w(e)` joining the ends of `e` makes `e` *supported* by the new forest — that claim is
Fact 2.5 and nothing else.  In §3.3 the same fact is what lets the forest `F` be used as a certificate
for edges it does not contain.  It is also the reason an MSF is a *sparse* representative of its graph:
the light-edge components of `G[S]` and of its MSF coincide, threshold by threshold.

Because the paper applies the fact to `MSF(G[F ∪ D])` rather than to `MSF(G)`, the statement is
formalised relative to an edge set: `IsMSFOf G S T` says `T` is a minimum spanning forest of the
edge-induced subgraph `G[S]`, written inside the ambient graph so that every lemma of
`Exchange.lean`/`Tree.lean` applies unchanged.  The two structural facts needed for that
(`isSpanningForestOf_exchange`, `IsMSFOf.lightest_bridge`) are the relative versions of lemmas already
proved absolutely; their proofs are the ambient ones with the quantifier `∀ e ∈ S` in place of
`∀ e : E`.

The proof of `below_span` is the cut argument, and it is the first place in this development where
both halves of the trail machinery are needed at once: `crossing` on the light `S`-trail finds the edge
`g` leaving the `T≤k`-component, the `T`-trail of `g` (made backtrack-free by
`IsForest.exists_consecFree_trail`) then supplies an edge `f` that both leaves that component and is
separated by its own deletion (`IsForest.sep_of_mem_trail`), so `IsMSFOf.lightest_bridge` gives
`w(f) ≤ w(g) ≤ k` — making `f` a member of `T≤k`, which is exactly the contradiction.
-/

namespace DLMST

set_option linter.unusedSectionVars false

open Classical

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] {G : WGraph V E}

/-- **`F≤θ`** (paper, §2): the edges of `F` no heavier than `θ`.  `below` in `MsfKernel.lean` is the
strict version; the paper's `F≤k` is this one. -/
noncomputable def belowLe (G : WGraph V E) (F : Finset E) (θ : ℝ) : Finset E :=
  F.filter fun e => G.weight e ≤ θ

theorem belowLe_mem {F : Finset E} {θ : ℝ} {e : E} :
    e ∈ belowLe G F θ ↔ e ∈ F ∧ G.weight e ≤ θ := Finset.mem_filter

/-- **`T` is a spanning forest of `G[S]`** (paper, §2: `G[S] = (V, S)` is the edge-induced subgraph).
Written inside the ambient graph `G`: a forest, contained in `S`, that already joins the ends of every
non-loop edge of `S`. -/
def IsSpanningForestOf (G : WGraph V E) (S T : Finset E) : Prop :=
  IsForest G T ∧ T ⊆ S ∧ ∀ e ∈ S, G.src e ≠ G.dst e → Conn G T (G.src e) (G.dst e)

/-- **`T` is a minimum spanning forest of `G[S]`** — the paper's `F = MSF(G[S])`, which §2 uses in
Fact 2.5, in Algorithm 1's `F ← MSF(G[F ∪ D])`, and in §3.4's recursive calls. -/
def IsMSFOf (G : WGraph V E) (S T : Finset E) : Prop :=
  IsSpanningForestOf G S T ∧ ∀ T', IsSpanningForestOf G S T' → wsum G T ≤ wsum G T'

/-- **Spanning forests of `S` exist**: a `⊆`-maximal forest inside `S` spans `S`.  An edge of `S`
whose ends the forest does not join could be added, and adding it keeps both the forestness and the
containment in `S`. -/
theorem exists_spanningForestOf (S : Finset E) : ∃ T, IsSpanningForestOf G S T := by
  classical
  obtain ⟨T, hTmem, hTmax⟩ :=
    Finset.exists_max_image (Finset.univ.filter fun T : Finset E => T ⊆ S ∧ IsForest G T)
      (fun T : Finset E => T.card)
      ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.empty_subset S, IsForest.empty⟩⟩
  obtain ⟨hTS, hTf⟩ := (Finset.mem_filter.mp hTmem).2
  refine ⟨T, hTf, hTS, ?_⟩
  intro e he hne
  by_contra hconn
  have hmem : (insert e T) ∈ Finset.univ.filter
      fun T : Finset E => T ⊆ S ∧ IsForest G T :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Finset.insert_subset_iff.mpr ⟨he, hTS⟩, IsForest.add hTf hne hconn⟩
  have hle := hTmax (insert e T) hmem
  rw [Finset.card_insert_of_notMem (not_mem_of_not_conn hconn)] at hle
  omega

/-- **Minimum spanning forests of `S` exist** — so the paper's `MSF(G[S])` refers to something. -/
theorem exists_msfof (S : Finset E) : ∃ T, IsMSFOf G S T := by
  classical
  obtain ⟨T₀, hT₀⟩ := exists_spanningForestOf (G := G) S
  obtain ⟨T, hTmem, hTmax⟩ :=
    Finset.exists_max_image (Finset.univ.filter fun T : Finset E => IsSpanningForestOf G S T)
      (fun T : Finset E => -wsum G T) ⟨T₀, Finset.mem_filter.mpr ⟨Finset.mem_univ T₀, hT₀⟩⟩
  refine ⟨T, (Finset.mem_filter.mp hTmem).2, fun T' hT' => ?_⟩
  have := hTmax T' (Finset.mem_filter.mpr ⟨Finset.mem_univ T', hT'⟩)
  linarith

/-- The ambient `IsMSF` is the relative one at `S = univ`. -/
theorem IsMSF.msfof_univ {T : Finset E} (hT : IsMSF G T) : IsMSFOf G (Finset.univ : Finset E) T := by
  obtain ⟨⟨hTf, hTsp⟩, hTmin⟩ := hT
  exact ⟨⟨hTf, Finset.subset_univ _, fun e _ => hTsp e⟩, fun T' hT' =>
    hTmin T' ⟨hT'.1, fun e => hT'.2.2 e (Finset.mem_univ e)⟩⟩

/-- **The exchange, relative to `S`.**  Same statement as `isSpanningForest_exchange`, with the
quantifier over `S` instead of over all edges. -/
theorem isSpanningForestOf_exchange {S T : Finset E} (hT : IsSpanningForestOf G S T) {f e : E}
    (hf : f ∈ T) (he : e ∈ S) (hsep : ¬ Conn G (T.erase f) (G.src e) (G.dst e)) :
    IsSpanningForestOf G S (insert e (T.erase f)) := by
  obtain ⟨hTf, hTS, hTsp⟩ := hT
  have hne : G.src e ≠ G.dst e := fun h => hsep (by rw [h]; exact Conn.refl _)
  refine ⟨IsForest.add (hTf.hereditary _ (Finset.erase_subset f T)) hne hsep,
    Finset.insert_subset_iff.mpr ⟨he, Finset.subset_iff.mpr
      fun x hx => hTS (Finset.mem_erase.mp hx).2⟩, ?_⟩
  intro h hh hne2
  exact conn_erase_insert hTf hf (hTsp e he hne) hsep (hTsp h hh hne2)

/-- **Cut property, relative to `S`.**  A tree edge `f` of `MSF(G[S])` is no heavier than any edge of
`S` whose ends `T − f` separates. -/
theorem IsMSFOf.lightest_bridge {S T : Finset E} (hT : IsMSFOf G S T) {f e : E} (hf : f ∈ T)
    (he : e ∈ S) (hsep : ¬ Conn G (T.erase f) (G.src e) (G.dst e)) : G.weight f ≤ G.weight e := by
  classical
  obtain ⟨⟨hTf, hTS, hTsp⟩, hTmin⟩ := hT
  have hge : wsum G T ≤ wsum G (insert e (T.erase f)) :=
    hTmin _ (isSpanningForestOf_exchange ⟨hTf, hTS, hTsp⟩ hf he hsep)
  rw [wsum_exchange hf (not_mem_of_not_conn hsep)] at hge
  linarith

/-- **The exchange, relative to `S`, preserves optimality.**  Replacing the tree edge `f` by an
edge `e ∈ S` that is no heavier and that `T - f` does not reconnect keeps the minimum spanning
forest property of `G[S]`.  This is PR02's exchange at the level of an instance. -/
theorem IsMSFOf.exchange {S T : Finset E} (hT : IsMSFOf G S T) {f e : E} (hf : f ∈ T)
    (he : e ∈ S) (hsep : ¬ Conn G (T.erase f) (G.src e) (G.dst e)) (hw : G.weight e ≤ G.weight f) :
    IsMSFOf G S (insert e (T.erase f)) := by
  refine ⟨isSpanningForestOf_exchange hT.1 hf he hsep, fun T' hT' => ?_⟩
  have h1 : wsum G T ≤ wsum G T' := hT.2 T' hT'
  have h2 : wsum G (insert e (T.erase f)) ≤ wsum G T := by
    rw [wsum_exchange hf (not_mem_of_not_conn hsep)]
    linarith
  exact le_trans h2 h1

/-- A trail whose ends lie on opposite sides of a cut has an edge crossing it, in either direction. -/
private theorem crossing_compl {u v : V} {es : List E} (p : Path G u es v) (S : Set V)
    (hu : u ∉ S) (hv : v ∈ S) :
    ∃ e ∈ es, (G.src e ∈ S ∧ G.dst e ∉ S) ∨ (G.src e ∉ S ∧ G.dst e ∈ S) := by
  obtain ⟨e, he, hcr⟩ := crossing p Sᶜ hu (fun h => h hv)
  simp only [Set.mem_compl_iff, not_not] at hcr
  exact ⟨e, he, hcr.elim (fun ⟨h1, h2⟩ => Or.inr ⟨h1, h2⟩) fun ⟨h1, h2⟩ => Or.inl ⟨h1, h2⟩⟩

private theorem crossing_pair {u v : V} {es : List E} (p : Path G u es v) (S : Set V)
    (h : (u ∈ S ∧ v ∉ S) ∨ (u ∉ S ∧ v ∈ S)) :
    ∃ e ∈ es, (G.src e ∈ S ∧ G.dst e ∉ S) ∨ (G.src e ∉ S ∧ G.dst e ∈ S) := by
  rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · exact crossing p S hu hv
  · exact crossing_compl p S hu hv

/-- **Fact 2.5 (machine-checked).**  Let `T` be an MSF of `G[S]`.  If `u` and `v` are joined inside
`G[S]` by edges of weight at most `θ`, they are joined in `T≤θ`.  The light-edge components of `S` and
of its minimum spanning forest are the same. -/
theorem IsMSFOf.below_span {S T : Finset E} (hT : IsMSFOf G S T) {θ : ℝ} {u v : V}
    (huv : Conn G (belowLe G S θ) u v) : Conn G (belowLe G T θ) u v := by
  classical
  have hTf : IsForest G T := hT.1.1
  have hTsp : ∀ e ∈ S, G.src e ≠ G.dst e → Conn G T (G.src e) (G.dst e) := hT.1.2.2
  by_contra hno
  -- the `T≤θ`-component of `u`
  let C : Set V := { x | Conn G (belowLe G T θ) u x }
  have huC : u ∈ C := Conn.refl u
  have hvC : v ∉ C := hno
  obtain ⟨g, hg, hcr⟩ := crossing_of_conn huv C huC hvC
  obtain ⟨hgS, hwg⟩ := belowLe_mem.mp hg
  have hne : G.src g ≠ G.dst g := by
    rcases hcr with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · intro he; exact h2 (he ▸ h1)
    · intro he; exact h1 (he ▸ h2)
  -- `g` is not a tree edge: as a light one it would lie in `T≤θ`, whose components are `C`
  have hgT : g ∉ T := by
    intro hgt
    rcases hcr with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2 (Conn.trans h1 (Conn.step g (belowLe_mem.mpr ⟨hgt, hwg⟩)))
    · exact h1 (Conn.trans h2 (Conn.step g (belowLe_mem.mpr ⟨hgt, hwg⟩)).symm)
  -- the `T`-trail of `g`, made backtrack-free, has an edge leaving `C`
  obtain ⟨es0, p0, hmem0⟩ := path_of_conn (hTsp g hgS hne)
  obtain ⟨es, p, hmem, hf⟩ := hTf.exists_consecFree_trail es0 p0 hmem0
  obtain ⟨f, hfes, hcrf⟩ := crossing_pair p C hcr
  have hfT : f ∈ T := hmem f hfes
  have hfw : G.weight f ≤ θ := by
    have hsep : ¬ Conn G (T.erase f) (G.src g) (G.dst g) :=
      hTf.sep_of_mem_trail p hmem hf hfes
    exact le_trans (IsMSFOf.lightest_bridge hT hfT hgS hsep) hwg
  have hfC : f ∈ belowLe G T θ := belowLe_mem.mpr ⟨hfT, hfw⟩
  rcases hcrf with ⟨hs, hd⟩ | ⟨hs, hd⟩
  · exact hd (hs.trans (Conn.step f hfC))
  · exact hs (hd.trans (Conn.step f hfC).symm)

/-- **The §3.2 corollary.**  Anything supported by `S` is supported by `MSF(G[S])`: the filter a
batch produces is a certificate for the whole edge set it was built from. -/
theorem IsMSFOf.supported_of {S T : Finset E} (hT : IsMSFOf G S T) {e : E}
    (he : supported G S e) : supported G T e :=
  show Conn G (belowLe G T (G.weight e)) (G.src e) (G.dst e) from IsMSFOf.below_span hT he

end DLMST
