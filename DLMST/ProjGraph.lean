import DLMST.Rounds

/-!
# The projection graph `G′`

§3.2 contracts every vertex to its portal: the child instance runs on the graph whose *vertices are
the portals* and whose edges are the projected batch edges, drawn between the portals of their ends.
This file defines that graph (`projGraph`), records that its weights are the parent's weights (so
`F≤θ` means the same thing on both sides, `belowLe_projGraph`), and proves the one thing every
lifting argument uses: **connectivity in `G′` at a threshold lifts to connectivity in `G` at the same
threshold, through spokes** — `conn_of_projGraph` for a bare `Conn`, and `conn_lift` in the shape
Claim 3.6 consumes (a `θ`-walk in `G′` between the portals of `e` becomes a `θ`-walk in `G` between
the ends of `e`).

The hypotheses are exactly the paper's: the spokes are genuine (`incident`, so `joins_portal`
applies), the child's edges lie in the level's forest `S`, and both the spokes and `e` are no heavier
than `θ` (with `θ = max{w(e), p(e)}` those last bounds are `le_pE_left/right`).
-/

namespace DLMST

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] {G : WGraph V E}
  [LinearOrder E]

/-- **`G′`, the projection graph.**  Same vertices, same weights; each edge `e` is drawn between the
portals of its endpoints. -/
def projGraph (G : WGraph V E) (σ : V → E) : WGraph V E where
  endpoints e := (portal G σ (G.src e), portal G σ (G.dst e))
  weight := G.weight

@[simp] theorem projGraph_src (σ : V → E) (e : E) :
    (projGraph G σ).src e = portal G σ (G.src e) := rfl

@[simp] theorem projGraph_dst (σ : V → E) (e : E) :
    (projGraph G σ).dst e = portal G σ (G.dst e) := rfl

@[simp] theorem projGraph_weight (σ : V → E) (e : E) :
    (projGraph G σ).weight e = G.weight e := rfl

/-- Threshold sets are literally the same edge sets in `G′` and in `G`: only the endpoints moved. -/
theorem belowLe_projGraph (σ : V → E) (B : Finset E) (θ : ℝ) :
    belowLe (projGraph G σ) B θ = belowLe G B θ := rfl

/-- **One projected edge lifts.**  A projected edge `e` joins the portals of its ends by the three-edge
walk `σ(src e), e, σ(dst e)`, so it gives a `Conn` at any threshold above `w(e)` and the spokes. -/
theorem conn_projEdge {S : Finset E} {σ : V → E} {θ : ℝ} {e : E}
    (hsp : ∀ x, incident G x (σ x)) (he : e ∈ belowLe G S θ)
    (hσ : ∀ x, σ x ∈ belowLe G S θ) :
    Conn G (belowLe G S θ) (portal G σ (G.src e)) (portal G σ (G.dst e)) := by
  have h1 : Path G (portal G σ (G.src e)) [σ (G.src e)] (G.src e) :=
    Path.of_joins (joins_swap (joins_portal (hsp (G.src e))))
  have h2 : Path G (G.src e) [e] (G.dst e) := Path.edge e
  have h3 : Path G (G.dst e) [σ (G.dst e)] (portal G σ (G.dst e)) :=
    Path.of_joins (joins_portal (hsp (G.dst e)))
  have hcat : (([σ (G.src e)] ++ [e]) ++ [σ (G.dst e)]) =
      σ (G.src e) :: e :: [σ (G.dst e)] := by simp
  have hwalk : Path G (portal G σ (G.src e)) (σ (G.src e) :: e :: [σ (G.dst e)])
      (portal G σ (G.dst e)) :=
    hcat ▸ ((h1.append [e] _ h2).append _ _ h3)
  exact conn_of_path hwalk (by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact hσ _
    · exact he
    · exact hσ _)

/-- **Connectivity lifts out of `G′`.**  If `G′≤θ` joins two vertices, then `G≤θ` joins them too,
provided every projected edge is in `F≤θ` and every spoke is in `F≤θ`.  Proof by induction on the
`Conn` derivation: the only work is the single-step case (`conn_projEdge`). -/
theorem conn_of_projGraph {S B : Finset E} {σ : V → E} {θ : ℝ} {u v : V}
    (hsp : ∀ x, incident G x (σ x)) (hB : B ⊆ belowLe G S θ)
    (hσ : ∀ x, σ x ∈ belowLe G S θ)
    (h : Conn (projGraph G σ) B u v) : Conn G (belowLe G S θ) u v := by
  induction h with
  | refl x => exact Conn.refl x
  | step e he => exact conn_projEdge hsp (hB he) hσ
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- **Claim 3.6's lifting step at the graph level.**  A `θ`-connection in `G′` between the *portals*
of `e`, with the child's edges lying in the level's forest `S` and `w(e), σ ≤ θ`, becomes a
`θ`-connection in `G` between the *ends* of `e` (the edge `e` itself is never traversed — the walk
goes `σ(src e)` into `G′` and `σ(dst e)` back out).  This is the shape the paper uses with
`θ = max{w(e), p(e)}`. -/
theorem conn_lift {S B : Finset E} {σ : V → E} {θ : ℝ} {e : E}
    (hsp : ∀ x, incident G x (σ x)) (hB : B ⊆ S)
    (hσ : ∀ x, σ x ∈ belowLe G S θ)
    (h : Conn (projGraph G σ) (belowLe (projGraph G σ) B θ)
      (portal G σ (G.src e)) (portal G σ (G.dst e))) :
    Conn G (belowLe G S θ) (G.src e) (G.dst e) := by
  have h1 : Conn G (belowLe G S θ) (G.src e) (portal G σ (G.src e)) :=
    conn_of_joins (joins_portal (hsp (G.src e))) (hσ _)
  have h3 : Conn G (belowLe G S θ) (portal G σ (G.dst e)) (G.dst e) :=
    (conn_of_joins (joins_portal (hsp (G.dst e))) (hσ _)).symm
  have h2 : Conn G (belowLe G S θ) (portal G σ (G.src e)) (portal G σ (G.dst e)) :=
    conn_of_projGraph hsp (belowLe_subset hB θ) hσ h
  exact h1.trans (h2.trans h3)

end DLMST