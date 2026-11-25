import Mathlib

/-!
# The MST kernel the paper's algorithm lives in

This mathlib has no spanning-tree API at all (`Mathlib/GraphTheory` is absent, and the only mention
of `spanningTree` in the whole library is in `GroupTheory/FreeGroup/NielsenSchreier.lean`), so
everything below is self-contained: weighted multigraphs with parallel edges and loops, a
reachability relation `Conn`, forests built up edge by edge (`IsForest`), and the threshold edge
sets `below G θ` that the paper's Fact 2.5 is about.

Machine-checked here:

* `IsForest.insert` / `boruvka_step` — the invariant a Borůvka phase maintains: an edge leaving a
  union of current components cannot close a cycle, so component merging keeps a forest;
* `conn_of_mem` / `not_mem_of_not_conn` — the same invariant read the other way;
* `below_mono` / `conn_below_mono` — threshold connectivity is monotone in the threshold;
* `below_relabel` / `conn_relabel` — Fact 2.5 in the form "which edges lie below a threshold, and
  what they connect, depends only on the *order* of the weights, not on their numerical values".
  That is the model-level half of the claim that the computation can be phrased purely in
  comparisons, which is what lets the paper quote the Pettie–Ramachandran reduction.

Deliberately **not** proved here, because it is the paper's own content rather than background:
that the certificate procedure of §2–§3 returns a forest `F` with
`|F| + |U(F)| + Σ|E_i| ≤ εm + C_ε√(mn)` (Lemma 1.2), the matrix-scheduling lemma (Lemma 3.11), the
sampling claim (Claim 3.12), and the exchange argument that a Borůvka step preserves extendability
to a minimum spanning forest.  Those need several hundred more lines of matroid-style machinery.
What *follows* from them is checked in `Bookkeeping.lean` (the slack arithmetic), `Recurrence.lean`
(the recursion) and `VectorMaxima.lean` (Lemma 3.9).
-/

namespace DLMST

-- `below` and `wsum` need `[Fintype E]`, the relations and the Borůvka step do not.
set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- A weighted undirected multigraph.  Parallel edges and loops are allowed: contraction creates
parallel edges, and the paper's rejection set `U(F)` is exactly about loops and heavy parallels. -/
structure WGraph (V E : Type*) where
  endpoints : E → V × V
  weight : E → ℝ

variable {G : WGraph V E}

def WGraph.src (G : WGraph V E) (e : E) : V := (G.endpoints e).1
def WGraph.dst (G : WGraph V E) (e : E) : V := (G.endpoints e).2

/-- `Conn G F u v`: `v` is reachable from `u` using edges of the edge set `F`. -/
inductive Conn (G : WGraph V E) (F : Finset E) : V → V → Prop where
  | refl (v : V) : Conn G F v v
  | step (e : E) (he : e ∈ F) : Conn G F (G.src e) (G.dst e)
  | symm {u v : V} (h : Conn G F u v) : Conn G F v u
  | trans {u v w : V} (h1 : Conn G F u v) (h2 : Conn G F v w) : Conn G F u w

/-- The edges of weight below `θ`. -/
noncomputable def below (G : WGraph V E) (θ : ℝ) : Finset E :=
  Finset.filter (fun e => G.weight e < θ) Finset.univ

/-- A forest, by construction: nothing but the empty set and edges joining two previously
disconnected vertices.  This is how an MST routine's own invariant is stated, which makes the
invariant checkable by construction instead of by counting edges. -/
inductive IsForest (G : WGraph V E) : Finset E → Prop where
  | empty : IsForest G ∅
  | add {F : Finset E} {e : E} (hF : IsForest G F) (he : G.src e ≠ G.dst e)
      (h : ¬ Conn G F (G.src e) (G.dst e)) : IsForest G (insert e F)

/-- Total weight of an edge set. -/
def wsum (G : WGraph V E) (F : Finset E) : ℝ := F.sum G.weight

/-- A spanning forest: a forest in which every non-loop edge already has its endpoints joined. -/
def IsSpanningForest (G : WGraph V E) (F : Finset E) : Prop :=
  IsForest G F ∧ ∀ e : E, G.src e ≠ G.dst e → Conn G F (G.src e) (G.dst e)

/-- A minimum spanning forest: a spanning forest of least total weight. -/
def IsMSF (G : WGraph V E) (F : Finset E) : Prop :=
  IsSpanningForest G F ∧ ∀ F', IsSpanningForest G F' → wsum G F ≤ wsum G F'

/-- Growing the edge set cannot destroy reachability. -/
theorem Conn.mono {F F' : Finset E} (h : F ⊆ F') {u v : V} (huuv : Conn G F u v) :
    Conn G F' u v := by
  induction huuv
  · exact Conn.refl _
  · exact Conn.step _ (h ‹_›)
  · exact Conn.symm ‹_›
  · exact Conn.trans ‹_› ‹_›

/-- An edge of the set joins two vertices the set already connects. -/
theorem conn_of_mem {F : Finset E} {e : E} (he : e ∈ F) : Conn G F (G.src e) (G.dst e) :=
  Conn.step e he

/-- So an edge whose endpoints are not joined is absent — which is what makes adding it legal. -/
theorem not_mem_of_not_conn {F : Finset E} {e : E}
    (h : ¬ Conn G F (G.src e) (G.dst e)) : e ∉ F := fun he => h (conn_of_mem he)

/-- Adding an edge that joins two components keeps a forest. -/
theorem IsForest.insert {F : Finset E} (hF : IsForest G F) {e : E} (he : G.src e ≠ G.dst e)
    (h : ¬ Conn G F (G.src e) (G.dst e)) : IsForest G (insert e F) :=
  IsForest.add hF he h

/-- **Borůvka step.**  Let `S` be a union of connected components of the forest `F` (`closed`
below) and let `e` leave `S`.  Then `e` cannot close a cycle, so it is addable; a Borůvka phase
picks for each component a lightest such edge.  Lightness is not used for forestness — the
(unformalised) exchange argument is what uses it to keep the choice extendable to an MSF. -/
theorem boruvka_step {F : Finset E} (hF : IsForest G F) (S : Set V)
    (closed : ∀ u ∈ S, ∀ v : V, Conn G F u v → v ∈ S) (e : E) (he1 : G.src e ∈ S)
    (he2 : G.dst e ∉ S) (hne : G.src e ≠ G.dst e) : IsForest G (insert e F) :=
  hF.insert hne (fun hc => he2 (closed _ he1 _ hc))

/-- Raising a threshold never destroys a connection. -/
theorem below_mono {θ θ' : ℝ} (h : θ ≤ θ') : below G θ ⊆ below G θ' := by
  intro e he
  simp only [below, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  exact lt_of_lt_of_le he h

theorem conn_below_mono {u v : V} (θ θ' : ℝ) (h : θ ≤ θ') (huuv : Conn G (below G θ) u v) :
    Conn G (below G θ') u v :=
  Conn.mono (below_mono h) huuv

/-- Relabelling the weights. -/
def relabel (φ : ℝ → ℝ) (G : WGraph V E) : WGraph V E :=
  { endpoints := G.endpoints, weight := fun e => φ (G.weight e) }

/-- Membership in a threshold set is exactly the weight comparison. -/
theorem mem_below {G : WGraph V E} {θ : ℝ} {e : E} : e ∈ below G θ ↔ G.weight e < θ := by
  classical
  simp [below]

theorem mem_below_relabel (φ : ℝ → ℝ) (θ : ℝ) (h : ∀ x, x < θ ↔ φ x < φ θ) (e : E) :
    e ∈ below (relabel φ G) (φ θ) ↔ e ∈ below G θ := by
  classical
  rw [mem_below (G := relabel φ G), mem_below]
  exact (h (G.weight e)).symm

/-- **Fact 2.5.**  For a relabelling that reflects the comparison against `θ`, the threshold edge
set is unchanged: it is a function of the comparison outcomes, not of the numerical weights. -/
theorem below_relabel (φ : ℝ → ℝ) (θ : ℝ) (h : ∀ x, x < θ ↔ φ x < φ θ) :
    below (relabel φ G) (φ θ) = below G θ := by
  classical
  ext e
  exact mem_below_relabel φ θ h e

/-- And so is reachability inside that threshold set. -/
theorem conn_relabel {u v : V} (φ : ℝ → ℝ) (θ : ℝ) (h : ∀ x, x < θ ↔ φ x < φ θ)
    (huuv : Conn G (below G θ) u v) : Conn G (below (relabel φ G) (φ θ)) u v := by
  rw [below_relabel φ θ h]
  exact huuv

end DLMST
