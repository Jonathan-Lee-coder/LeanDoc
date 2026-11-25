import DLMST.MsfKernel

/-!
# Explicit trails, cut-crossing, and existence of a minimum spanning forest

`Conn G F u v` is an inductive relation, so its proofs are derivations rather than walks whose edges
you can point at.  `Path G u es v` is the same reachability with the edge list `es` made explicit.
That extra datum is what three silent steps in the paper actually use:

* a `T`-path is a *sequence of edges*, which is why `P(T)`, the vertices incident to it, has at most
  `2m` members (§3), and why "every vertex of `U(T)` is an endpoint of an edge of `T`" holds;
* a trail that starts inside a vertex set and ends outside it uses an edge crossing that cut
  (`crossing`, `crossing_of_conn`) — the fact behind "a Borůvka component is closed under `T`-
  connections" and behind `U(F)` being precisely the edges that connectivity inside `F` forbids;
* reachability is unchanged by adding an edge whose endpoints are already joined.

Also proved here because the paper writes "the MSF" without existence: every weighted multigraph on
a finite edge set has a minimum spanning forest (`msf_exists`).  The argument is a finite maximum:
a forest of largest cardinality cannot leave two endpoints unjoined (`extend_to_spanning`), and a
spanning forest of least weight exists because there are only finitely many spanning forests.
`IsForest.hereditary` (subsets of forests are forests) is proved in the same style and is the lemma
the deletion arguments elsewhere would need.

What is *not* here: that adding a lightest edge across a Borůvka cut keeps the partial solution
extendable to an MSF.  Forestness is preserved (`boruvka_step` in `MsfKernel.lean`), but the
optimisation half needs `e ∈ F → ¬ Conn G (F.erase e) (src e) (dst e)` for the inductive `IsForest`
— "every edge of a forest is a bridge" — whose proof runs through decomposing trails at a repeated
edge.  That lemma is now machine-checked, as `IsForest.bridge` in `Exchange.lean`, together with the
single-edge cut/cycle exchange it powers.  What remains unproved there is only the multi-edge (whole
Borůvka phase / Kruskal prefix) version.
-/

namespace DLMST

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] {G : WGraph V E}

/-- `Path G u es v`: reading `es` from the front, the edges form a walk from `u` to `v`, each edge
traversed in either direction. -/
inductive Path (G : WGraph V E) : V → List E → V → Prop where
  | nil (u : V) : Path G u [] u
  | fwd {u v w : V} {es : List E} (e : E) (hs : G.src e = u) (hd : G.dst e = v)
      (p : Path G v es w) : Path G u (e :: es) w
  | bwd {u v w : V} {es : List E} (e : E) (hd : G.dst e = u) (hs : G.src e = v)
      (p : Path G v es w) : Path G u (e :: es) w

/-- Traverse `e` from its source to its target. -/
theorem Path.edge (e : E) : Path G (G.src e) [e] (G.dst e) :=
  Path.fwd e rfl rfl (Path.nil (G.dst e))

/-- Traverse `e` the other way. -/
theorem Path.edge_rev (e : E) : Path G (G.dst e) [e] (G.src e) :=
  Path.bwd e rfl rfl (Path.nil (G.src e))

/-- Concatenate trails. -/
theorem Path.append {u v : V} {es : List E} (p : Path G u es v) :
    ∀ (fs : List E) (w : V), Path G v fs w → Path G u (es ++ fs) w := by
  induction p with
  | nil x =>
      intro fs w pfs
      exact pfs
  | fwd e hs hd _ ih =>
      intro fs w pfs
      exact Path.fwd e hs hd (ih fs w pfs)
  | bwd e hd hs _ ih =>
      intro fs w pfs
      exact Path.bwd e hd hs (ih fs w pfs)

/-- Read a trail backwards. -/
theorem Path.reverse {u v : V} {es : List E} (p : Path G u es v) : Path G v es.reverse u := by
  induction p with
  | nil x => exact Path.nil x
  | fwd e hs hd _ ih =>
      have h1 : Path G (G.dst e) [e] (G.src e) := Path.edge_rev e
      rw [hd, hs] at h1
      rw [List.reverse_cons]
      exact ih.append [e] _ h1
  | bwd e hd hs _ ih =>
      have h1 : Path G (G.src e) [e] (G.dst e) := Path.edge e
      rw [hs, hd] at h1
      rw [List.reverse_cons]
      exact ih.append [e] _ h1

/-- An explicit trail inside `F` is an `F`-connection. -/
theorem conn_of_path {u v : V} {F : Finset E} {es : List E} (p : Path G u es v)
    (h : ∀ e ∈ es, e ∈ F) : Conn G F u v := by
  induction p with
  | nil x => exact Conn.refl x
  | fwd e hs hd _ ih =>
      refine Conn.trans ?_ (ih fun x hx => h x (by simp [hx]))
      rw [← hs, ← hd]
      exact Conn.step e (h e (by simp))
  | bwd e hd hs _ ih =>
      refine Conn.trans ?_ (ih fun x hx => h x (by simp [hx]))
      rw [← hd, ← hs]
      exact (Conn.step e (h e (by simp))).symm

/-- Every `Conn` proof is witnessed by a trail. -/
theorem path_of_conn {u v : V} {F : Finset E} (h : Conn G F u v) :
    ∃ es : List E, Path G u es v ∧ ∀ e ∈ es, e ∈ F := by
  induction h with
  | refl x => exact ⟨[], Path.nil x, by simp⟩
  | step e he => exact ⟨[e], Path.edge e, by simpa using he⟩
  | symm _ ih =>
      obtain ⟨es, pes, hmem⟩ := ih
      exact ⟨es.reverse, pes.reverse, fun x hx => hmem x (List.mem_reverse.mp hx)⟩
  | trans _ _ ih1 ih2 =>
      obtain ⟨es, pes, h1⟩ := ih1
      obtain ⟨fs, pfs, h2⟩ := ih2
      refine ⟨es ++ fs, pes.append fs _ pfs, ?_⟩
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact h1 x hx
      · exact h2 x hx

/-- **Cut-crossing.**  A trail from a vertex of `S` to a vertex outside `S` uses an edge with one
end in `S` and the other outside. -/
theorem crossing {u v : V} {es : List E} (p : Path G u es v) :
    ∀ (S : Set V), u ∈ S → v ∉ S →
      ∃ e ∈ es, (G.src e ∈ S ∧ G.dst e ∉ S) ∨ (G.src e ∉ S ∧ G.dst e ∈ S) := by
  classical
  induction p with
  | nil x =>
      intro S hx hnx
      exact absurd hx hnx
  | fwd e hs hd _ ih =>
      intro S hx hnw
      by_cases hy : G.dst e ∈ S
      · rw [hd] at hy
        obtain ⟨f, hf, hcr⟩ := ih S hy hnw
        exact ⟨f, by simp [hf], hcr⟩
      · refine ⟨e, by simp, ?_⟩
        rw [← hs] at hx
        exact Or.inl ⟨hx, hy⟩
  | bwd e hd hs _ ih =>
      intro S hx hnw
      by_cases hy : G.src e ∈ S
      · rw [hs] at hy
        obtain ⟨f, hf, hcr⟩ := ih S hy hnw
        exact ⟨f, by simp [hf], hcr⟩
      · refine ⟨e, by simp, ?_⟩
        rw [← hd] at hx
        exact Or.inr ⟨hy, hx⟩

/-- The cut-crossing property for `Conn`. -/
theorem crossing_of_conn {u v : V} {F : Finset E} (h : Conn G F u v) (S : Set V)
    (hu : u ∈ S) (hv : v ∉ S) :
    ∃ e ∈ F, (G.src e ∈ S ∧ G.dst e ∉ S) ∨ (G.src e ∉ S ∧ G.dst e ∈ S) := by
  obtain ⟨es, pes, hmem⟩ := path_of_conn h
  obtain ⟨e, he, hcr⟩ := crossing pes S hu hv
  exact ⟨e, hmem e he, hcr⟩

/-- Adding an edge never separates vertices that were already joined. -/
theorem conn_insert_of_conn {F : Finset E} {e : E} {u v : V} (h : Conn G F u v) :
    Conn G (insert e F) u v :=
  h.mono (Finset.subset_insert e F)

/-- Subsets of a forest are forests: a subset that had to be built by joining previously
disconnected vertices cannot fail to be buildable that way. -/
theorem IsForest.hereditary {F : Finset E} (hF : IsForest G F) :
    ∀ (F' : Finset E), F' ⊆ F → IsForest G F' := by
  classical
  induction hF with
  | empty =>
      intro F' hsub
      have h1 : F' = ∅ := by
        apply Finset.ext
        intro a
        exact ⟨fun ha => absurd (hsub ha) (by simp), fun ha => absurd ha (by simp)⟩
      rw [h1]
      exact IsForest.empty
  | @add Fsub esub hF hne hc ih =>
      intro F' hs
      by_cases he : esub ∈ F'
      · have hsub : F'.erase esub ⊆ Fsub := by
          intro x hx
          have hx' := hs (Finset.mem_erase.mp hx).2
          rcases Finset.mem_insert.mp hx' with rfl | hxF
          · exact absurd hx (by simp)
          · exact hxF
        rw [← Finset.insert_erase he]
        refine IsForest.add (ih _ hsub) hne ?_
        exact fun hconn => hc (hconn.mono hsub)
      · refine ih F' ?_
        intro x hx
        rcases Finset.mem_insert.mp (hs hx) with rfl | hxF
        · exact absurd hx he
        · exact hxF

/-- A forest that is maximal by inclusion among forests is spanning: an unjoined pair of endpoints
could always be added. -/
theorem extend_to_spanning {F : Finset E} (hF : IsForest G F)
    (maximal : ∀ F' : Finset E, IsForest G F' → F ⊆ F' → F' = F) :
    ∀ e : E, G.src e ≠ G.dst e → Conn G F (G.src e) (G.dst e) := by
  classical
  intro e hne
  by_contra hconn
  have h2 : insert e F = F := maximal _ (hF.insert hne hconn) (Finset.subset_insert e F)
  have h3 : e ∈ F := by rw [← h2]; exact Finset.mem_insert_self e F
  exact absurd h3 (not_mem_of_not_conn hconn)

/-- **Existence of a minimum spanning forest.**  The paper speaks of "the" MSF; this is the lemma
that makes that legitimate.  The proof is finite maximisation, not the algorithm. -/
theorem msf_exists : ∃ F : Finset E, IsMSF G F := by
  classical
  -- a forest of maximum size
  obtain ⟨T, hTmem, hTmax⟩ :=
    Finset.exists_max_image (Finset.univ.filter fun F : Finset E => IsForest G F)
      (fun F : Finset E => F.card)
      ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, IsForest.empty⟩⟩
  have hTf : IsForest G T := (Finset.mem_filter.mp hTmem).2
  -- it is spanning, so it is a spanning forest
  have hTspan : IsSpanningForest G T :=
    ⟨hTf, extend_to_spanning hTf fun F' hF' hsub =>
      (Finset.eq_of_subset_of_card_le hsub
        (hTmax F' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hF'⟩))).symm⟩
  -- among spanning forests, one of least total weight: the family is finite
  obtain ⟨F, hFmem, hFmin⟩ :=
    Set.exists_min_image {F' | IsSpanningForest G F'} (wsum G)
      (Set.Finite.subset Set.finite_univ (Set.subset_univ _)) ⟨T, hTspan⟩
  exact ⟨F, hFmem, fun F' hF' => hFmin F' hF'⟩

end DLMST
