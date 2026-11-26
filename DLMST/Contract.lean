import DLMST.Exchange
import DLMST.HistoryOfRounds
import DLMST.InstancePhase
import DLMST.Filtering
import DLMST.LightSpan

/-!
# Contracting an instance's components

The recursion of §4 replaces an instance by *contracted* ones: the components of the returned
forest become single vertices, and the edges that cross components become the new edges.  This file
builds the two ingredients that identification needs, without committing to a vertex type for the
contracted graph:

* `repOf` — a representative of each vertex's instance component (`compOn G P F v`), with
  `conn_repOf` (the phase forest connects every vertex to its representative) and
  `repOf_eq_of_compOn_eq` (the representative only depends on the component, so the map is well
  defined on components);
* `crossE` / `cGraph` — the instance edges leaving their component, and the graph whose endpoints
  are representatives.  `conn_contract` lifts any path in that graph back to a path of the original
  graph once the forest `F` is added, which is the soundness half of the contraction.

`disjoint_crossE_F` says cross edges are never forest edges, so contraction and the forest do not
overlap — the counting of §4 splits edges into kept (in `F`) and contracted (in `crossE`).
-/

open Classical

namespace DLMST

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

/-! ## Representatives of components -/

theorem compOn_nonempty {P : Finset V} {F : Finset E} {v : V} (hv : v ∈ P) :
    (compOn G P F v).Nonempty :=
  ⟨v, mem_compOn.mpr ⟨hv, Conn.refl v⟩⟩

/-- A representative of `v`'s instance component: a chosen element of `compOn G P F v`, and `v`
itself outside `P`. -/
noncomputable def repOf (G : WGraph V E) (P : Finset V) (F : Finset E) (v : V) : V :=
  if hv : v ∈ P then (compOn_nonempty (G := G) (F := F) hv).choose else v

theorem repOf_of_mem {P : Finset V} {F : Finset E} {v : V} (hv : v ∈ P) :
    repOf G P F v = (compOn_nonempty (G := G) (F := F) hv).choose := by
  rw [repOf, dite_eq_left hv]

theorem repOf_mem {P : Finset V} {F : Finset E} {v : V} (hv : v ∈ P) : repOf G P F v ∈ P := by
  rw [repOf_of_mem hv]
  exact compOn_subset (G := G) P F v (compOn_nonempty hv).choose_spec

theorem conn_repOf {P : Finset V} {F : Finset E} {v : V} (hv : v ∈ P) :
    Conn G F v (repOf G P F v) := by
  rw [repOf_of_mem hv]
  exact (mem_compOn.mp (compOn_nonempty hv).choose_spec).2

theorem compOn_repOf {P : Finset V} {F : Finset E} {v : V} (hv : v ∈ P) :
    compOn G P F (repOf G P F v) = compOn G P F v :=
  (compOn_congr (conn_repOf hv)).symm

/-- The representative only depends on the component: equal components give equal representatives.
This is what makes the contraction map well defined on the quotient. -/
theorem repOf_eq_of_compOn_eq {P : Finset V} {F : Finset E} {v w : V} (hv : v ∈ P) (hw : w ∈ P)
    (h : compOn G P F v = compOn G P F w) : repOf G P F v = repOf G P F w := by
  rw [repOf_of_mem hv, repOf_of_mem hw]
  simp only [h]

theorem repOf_idem {P : Finset V} {F : Finset E} {v : V} (hv : v ∈ P) :
    repOf G P F (repOf G P F v) = repOf G P F v :=
  repOf_eq_of_compOn_eq (repOf_mem hv) hv (compOn_repOf hv)

/-! ## Crossing edges and the contracted graph -/

/-- The instance edges whose ends fall in different components of `F`. -/
noncomputable def crossE (G : WGraph V E) (F E₀ : Finset E) : Finset E :=
  E₀.filter (fun e => ¬ Conn G F (G.src e) (G.dst e))

/-- The contracted graph: its vertices are the representatives of the ends, its edges are the cross
edges, and weights are inherited.  It is a `WGraph` on the original vertex type, so the instance
machinery applies to it unchanged; the *instance* it belongs to is `(P, crossE)`. -/
noncomputable def cGraph (G : WGraph V E) (P : Finset V) (F E₀ : Finset E) :
    WGraph V {e // e ∈ crossE G F E₀} where
  endpoints e := (repOf G P F (G.src e.1), repOf G P F (G.dst e.1))
  weight e := G.weight e.1

section Instance

variable (P : Finset V) (F E₀ : Finset E)

theorem mem_crossE {e : E} :
    e ∈ crossE G F E₀ ↔ e ∈ E₀ ∧ ¬ Conn G F (G.src e) (G.dst e) := by
  classical
  unfold crossE
  rw [Finset.mem_filter]

theorem crossE_subset : crossE G F E₀ ⊆ E₀ := Finset.filter_subset _ _

/-- A cross edge is never a forest edge: an `F` edge connects its own two ends. -/
theorem disjoint_crossE_F : Disjoint F (crossE G F E₀) := by
  rw [Finset.disjoint_left]
  intro e heF he
  exact (mem_crossE (G := G) F E₀ (e := e)).1 he |>.2 (Conn.step e heF)

/-- **Soundness of the contraction.**  A path in the contracted graph lifts to a path of the
original graph on the forest together with the crossed edges: each contracted step takes the two
ends' representatives, and `F` carries a representative to its own end (`conn_repOf`). -/
theorem conn_contract (hP : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    {F'' : Finset {e // e ∈ crossE G F E₀}} {u v : V}
    (h : Conn (cGraph G P F E₀) F'' u v) :
    Conn G (F ∪ F''.image (fun e => e.1)) u v := by
  induction h with
  | refl w => exact Conn.refl w
  | step e he =>
      have hE0 : e.1 ∈ E₀ := crossE_subset (G := G) F E₀ e.2
      have hmem : e.1 ∈ F ∪ F''.image (fun e => e.1) :=
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)
      have hFsub : F ⊆ F ∪ F''.image (fun e => e.1) := Finset.subset_union_left
      have h1 : Conn G (F ∪ F''.image (fun e => e.1))
          ((cGraph G P F E₀).src e) (G.src e.1) :=
        (Conn.mono hFsub (conn_repOf (hP e.1 hE0).1)).symm
      have h2 : Conn G (F ∪ F''.image (fun e => e.1)) (G.src e.1) (G.dst e.1) :=
        Conn.step e.1 hmem
      have h3 : Conn G (F ∪ F''.image (fun e => e.1))
          (G.dst e.1) ((cGraph G P F E₀).dst e) :=
        Conn.mono hFsub (conn_repOf (hP e.1 hE0).2)
      exact h1.trans (h2.trans h3)
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- **Completeness of the contraction.**  A path of the instance that spends only the forest and
cross edges contracts to a path of the contracted graph between the representatives: forest steps
vanish (both ends lie in one component), cross steps become contracted edges.  With `conn_contract`
this says contraction preserves connectivity both ways. -/
theorem conn_cGraph_of_conn (hF : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P) {B : Finset E}
    (hB : ∀ e ∈ B, e ∈ crossE G F E₀) :
    ∀ {u v : V}, Conn G (F ∪ B) u v →
      Conn (cGraph G P F E₀)
        (B.subtype (fun e => e ∈ crossE G F E₀))
        (repOf G P F u) (repOf G P F v) := by
  intro u v h
  induction h with
  | refl w => exact Conn.refl _
  | step e he =>
      by_cases heB : e ∈ B
      · have himg : (⟨e, hB e heB⟩ : {e // e ∈ crossE G F E₀}) ∈
            B.subtype (fun e => e ∈ crossE G F E₀) :=
          Finset.mem_subtype.mpr heB
        exact Conn.step (G := cGraph G P F E₀) ⟨e, hB e heB⟩ himg
      · have heF : e ∈ F := by
          rcases Finset.mem_union.mp he with h | h
          · exact h
          · exact absurd h heB
        have hsrc : repOf G P F (G.src e) = repOf G P F (G.dst e) :=
          repOf_eq_of_compOn_eq (hF e heF).1 (hF e heF).2 (compOn_congr (Conn.step e heF))
        rw [hsrc]
        exact Conn.refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- Ends of a cross edge lie in different components, so their representatives differ. -/
theorem repOf_ne_of_crossE (hP : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    {e : {e // e ∈ crossE G F E₀}} :
    repOf G P F (G.src e.1) ≠ repOf G P F (G.dst e.1) := by
  intro h
  have hE0 : e.1 ∈ E₀ := crossE_subset (G := G) F E₀ e.2
  have h1 : Conn G F (G.src e.1) (repOf G P F (G.src e.1)) := conn_repOf (hP e.1 hE0).1
  have h2 : Conn G F (G.dst e.1) (repOf G P F (G.dst e.1)) := conn_repOf (hP e.1 hE0).2
  rw [← h] at h2
  exact (mem_crossE (G := G) F E₀ (e := e.1)).1 e.2 |>.2 (h1.trans h2.symm)

/-- The contracted instance's vertex set: the representatives of `P`'s `F`-components. -/
noncomputable def repSet (G : WGraph V E) (P : Finset V) (F : Finset E) : Finset V :=
  P.image (repOf G P F)

theorem mem_repSet {v : V} :
    v ∈ repSet G P F ↔ ∃ u ∈ P, repOf G P F u = v := by
  classical
  unfold repSet
  rw [Finset.mem_image]

theorem repOf_mem_repSet {v : V} (hv : v ∈ P) : repOf G P F v ∈ repSet G P F :=
  Finset.mem_image.mpr ⟨v, hv, rfl⟩

theorem repSet_subset : repSet G P F ⊆ P := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := (mem_repSet (G := G) (P := P) (F := F) (v := v)).1 hv
  exact repOf_mem hu

/-- The subtype finset of the cross edges maps back to the cross-edge family itself. -/
theorem image_subtype_crossE {B : Finset E} (hB : ∀ e ∈ B, e ∈ crossE G F E₀) :
    (B.subtype (fun e => e ∈ crossE G F E₀)).image (fun e => e.1) = B := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_subtype (p := fun e => e ∈ crossE G F E₀)).1 hy
  · intro hx
    exact Finset.mem_image.mpr ⟨⟨x, hB x hx⟩,
      (Finset.mem_subtype (p := fun e => e ∈ crossE G F E₀)).2 hx, rfl⟩

/-- The reverse round trip: a family of cross edges, read upstairs and then restricted again, is the
family itself. -/
theorem subtype_image_subtype {B : Finset {e // e ∈ crossE G F E₀}} :
    (B.image Subtype.val).subtype (fun e => e ∈ crossE G F E₀) = B := by
  ext x
  rw [Finset.mem_subtype, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have h : y = x := Subtype.ext hxy
    exact h ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- **Contraction preserves connectivity**: two instance vertices are connected through the forest
and the cross edges exactly when their representatives are connected by the contracted cross
edges.  The two halves are `conn_cGraph_of_conn` (down) and `conn_contract` (up). -/
theorem conn_iff_conn_cGraph (hP : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hF : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P) {B : Finset E}
    (hB : ∀ e ∈ B, e ∈ crossE G F E₀) {u v : V} (hu : u ∈ P) (hv : v ∈ P) :
    Conn G (F ∪ B) u v ↔
      Conn (cGraph G P F E₀) (B.subtype (fun e => e ∈ crossE G F E₀))
        (repOf G P F u) (repOf G P F v) := by
  constructor
  · intro h
    exact conn_cGraph_of_conn (G := G) (P := P) (F := F) (E₀ := E₀) hF (B := B) hB h
  · intro h
    have hcont := conn_contract (G := G) (P := P) (F := F) (E₀ := E₀) hP
      (F'' := B.subtype (fun e => e ∈ crossE G F E₀)) h
    rw [image_subtype_crossE (G := G) (F := F) (E₀ := E₀) hB] at hcont
    have h1 : Conn G (F ∪ B) u (repOf G P F u) :=
      Conn.mono Finset.subset_union_left (conn_repOf hu)
    have h2 : Conn G (F ∪ B) (repOf G P F v) v :=
      (Conn.mono Finset.subset_union_left (conn_repOf hv)).symm
    exact h1.trans (hcont.trans h2)

/-- A representative is its own representative. -/
theorem repOf_repSet {v : V} (hv : v ∈ repSet G P F) : repOf G P F v = v := by
  obtain ⟨u, hu, rfl⟩ := (mem_repSet (G := G) (P := P) (F := F) (v := v)).1 hv
  exact repOf_idem hu

/-- The instance's component image is already carried by the representatives: contracting first
changes nothing, because `compOn` is constant along `repOf`. -/
theorem image_compOn_eq_repSet_image :
    P.image (compOn G P F) = (repSet G P F).image (compOn G P F) := by
  apply Finset.Subset.antisymm
  · intro C hC
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hC
    exact Finset.mem_image.mpr ⟨repOf G P F v, repOf_mem_repSet P F hv, compOn_repOf hv⟩
  · apply Finset.image_subset_iff.mpr
    intro v hv
    exact Finset.mem_image.mpr ⟨v, repSet_subset P F hv, rfl⟩

/-- On the representatives, `compOn` is injective: distinct representatives lie in distinct
components (otherwise `repOf_eq_of_compOn_eq` would identify them). -/
theorem card_image_compOn_repSet :
    ((repSet G P F).image (compOn G P F)).card = (repSet G P F).card := by
  refine Finset.card_image_of_injOn ?_
  intro u hu v hv huv
  rw [← repOf_repSet P F hu, ← repOf_repSet P F hv]
  exact repOf_eq_of_compOn_eq (repSet_subset P F hu) (repSet_subset P F hv) huv

/-- **The contracted instance has exactly the instance's components as vertices**: the
representative set of `(P, F)` has one element per `F`-component of `P`. -/
theorem repSet_card : (repSet G P F).card = compCountOn G P F := by
  have h : (P.image (compOn G P F)).card = (repSet G P F).card := by
    rw [image_compOn_eq_repSet_image, card_image_compOn_repSet]
  exact h.symm

/-- **Component images contract to contracted components.**  The representatives of a
`F ∪ B`-component of the instance are exactly a `B`-component of the contracted graph. -/
theorem compOn_image_repOf (hP : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hF : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P) {B : Finset E}
    (hB : ∀ e ∈ B, e ∈ crossE G F E₀) {v : V} (hv : v ∈ P) :
    (compOn G P (F ∪ B) v).image (repOf G P F) =
      compOn (cGraph G P F E₀) (repSet G P F)
        (B.subtype (fun e => e ∈ crossE G F E₀)) (repOf G P F v) := by
  classical
  ext b
  constructor
  · intro hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨huP, hcu⟩ :=
      (mem_compOn (G := G) (P := P) (F := F ∪ B) (v := v) (x := u)).1 hu
    exact (mem_compOn (G := cGraph G P F E₀) (P := repSet G P F)
      (F := B.subtype (fun e => e ∈ crossE G F E₀)) (v := repOf G P F v)).2
      ⟨repOf_mem_repSet P F huP,
        (conn_iff_conn_cGraph (G := G) (P := P) (F := F) (E₀ := E₀) hP hF hB hv huP).1 hcu⟩
  · intro hb
    obtain ⟨hbR, hcb⟩ := (mem_compOn (G := cGraph G P F E₀) (P := repSet G P F)
      (F := B.subtype (fun e => e ∈ crossE G F E₀)) (v := repOf G P F v)).1 hb
    obtain ⟨u, huP, rfl⟩ := (mem_repSet (G := G) (P := P) (F := F) (v := b)).1 hbR
    exact Finset.mem_image.mpr ⟨u,
      (mem_compOn (G := G) (P := P) (F := F ∪ B) (v := v) (x := u)).2
        ⟨huP,
          (conn_iff_conn_cGraph (G := G) (P := P) (F := F) (E₀ := E₀) hP hF hB hv huP).2
            hcb⟩,
      rfl⟩

/-- The contracted component images of all instance components. -/
theorem image_image_repOf (hP : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hF : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P) {B : Finset E}
    (hB : ∀ e ∈ B, e ∈ crossE G F E₀) :
    (P.image (compOn G P (F ∪ B))).image (fun C => C.image (repOf G P F)) =
      (repSet G P F).image
        (compOn (cGraph G P F E₀) (repSet G P F)
          (B.subtype (fun e => e ∈ crossE G F E₀))) := by
  classical
  apply Finset.Subset.antisymm
  · intro D hD
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hC
    exact Finset.mem_image.mpr ⟨repOf G P F v, repOf_mem_repSet P F hv,
      (compOn_image_repOf (G := G) (P := P) (F := F) (E₀ := E₀) hP hF hB hv).symm⟩
  · intro D hD
    obtain ⟨b, hbR, rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨v, hv, rfl⟩ := (mem_repSet (G := G) (P := P) (F := F) (v := b)).1 hbR
    exact Finset.mem_image.mpr ⟨compOn G P (F ∪ B) v,
      Finset.mem_image.mpr ⟨v, hv, rfl⟩,
      compOn_image_repOf (G := G) (P := P) (F := F) (E₀ := E₀) hP hF hB hv⟩

/-- Component images remember the component: on the instance's component images, taking
representatives is injective. -/
theorem image_repOf_injOn (hP : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hF : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P) {B : Finset E}
    (hB : ∀ e ∈ B, e ∈ crossE G F E₀) :
    Set.InjOn (fun C : Finset V => C.image (repOf G P F))
      ↑(P.image (compOn G P (F ∪ B))) := by
  classical
  intro C hC D hD hCD
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hD
  have h : compOn (cGraph G P F E₀) (repSet G P F)
        (B.subtype (fun e => e ∈ crossE G F E₀)) (repOf G P F v) =
      compOn (cGraph G P F E₀) (repSet G P F)
        (B.subtype (fun e => e ∈ crossE G F E₀)) (repOf G P F w) := by
    rw [← compOn_image_repOf (G := G) (P := P) (F := F) (E₀ := E₀) hP hF hB hv,
      ← compOn_image_repOf (G := G) (P := P) (F := F) (E₀ := E₀) hP hF hB hw]
    exact hCD
  have hconn : Conn (cGraph G P F E₀) (B.subtype (fun e => e ∈ crossE G F E₀))
      (repOf G P F v) (repOf G P F w) := by
    have hmem : repOf G P F w ∈ compOn (cGraph G P F E₀) (repSet G P F)
        (B.subtype (fun e => e ∈ crossE G F E₀)) (repOf G P F w) :=
      (mem_compOn (G := cGraph G P F E₀) (P := repSet G P F)
        (F := B.subtype (fun e => e ∈ crossE G F E₀)) (v := repOf G P F w)).2
        ⟨repOf_mem_repSet P F hw, Conn.refl _⟩
    rw [← h] at hmem
    exact ((mem_compOn (G := cGraph G P F E₀) (P := repSet G P F)
      (F := B.subtype (fun e => e ∈ crossE G F E₀)) (v := repOf G P F v)).1 hmem).2
  exact compOn_congr
    ((conn_iff_conn_cGraph (G := G) (P := P) (F := F) (E₀ := E₀) hP hF hB hv hw).2 hconn)

/-- **The component count is a contraction invariant.**  Contracting the instance's `F`-components
and keeping the cross edges `B` neither merges nor splits components. -/
theorem compCountOn_eq_cGraph (hP : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hF : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P) {B : Finset E}
    (hB : ∀ e ∈ B, e ∈ crossE G F E₀) :
    compCountOn G P (F ∪ B) =
      compCountOn (cGraph G P F E₀) (repSet G P F)
        (B.subtype (fun e => e ∈ crossE G F E₀)) := by
  classical
  have h1 : (P.image (compOn G P (F ∪ B))).card =
      ((P.image (compOn G P (F ∪ B))).image (fun C => C.image (repOf G P F))).card := by
    rw [Finset.card_image_of_injOn (image_repOf_injOn (G := G) (P := P) (F := F) (E₀ := E₀) hP hF hB)]
  rw [image_image_repOf (G := G) (P := P) (F := F) (E₀ := E₀) hP hF hB] at h1
  exact h1

/-- A cross edge is never a self-loop upstairs: a loop is connected by the empty forest. -/
theorem crossE_nloop {e : E} (he : e ∈ crossE G F E₀) : G.src e ≠ G.dst e := by
  intro h
  exact ((mem_crossE (G := G) F E₀ (e := e)).1 he).2 (by rw [h]; exact Conn.refl _)

theorem cGraph_src (e : {e // e ∈ crossE G F E₀}) :
    (cGraph G P F E₀).src e = repOf G P F (G.src e.1) := rfl

theorem cGraph_dst (e : {e // e ∈ crossE G F E₀}) :
    (cGraph G P F E₀).dst e = repOf G P F (G.dst e.1) := rfl

theorem cGraph_weight (e : {e // e ∈ crossE G F E₀}) :
    (cGraph G P F E₀).weight e = G.weight e.1 := rfl

/-- **The child's spanning property lifts.**  If the contracted forest connects all contracted
vertices, then the forest together with the crossed edges connects all instance vertices. -/
theorem conn_union_span_cGraph (hP : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hF : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P) {B : Finset E}
    (hB : ∀ e ∈ B, e ∈ crossE G F E₀)
    (hspan : ∀ u ∈ repSet G P F, ∀ v ∈ repSet G P F,
      Conn (cGraph G P F E₀) (B.subtype (fun e => e ∈ crossE G F E₀)) u v) :
    ∀ v ∈ P, ∀ w ∈ P, Conn G (F ∪ B) v w := by
  intro v hv w hw
  have hvP : repOf G P F v ∈ P := repSet_subset P F (repOf_mem_repSet P F hv)
  have hwP : repOf G P F w ∈ P := repSet_subset P F (repOf_mem_repSet P F hw)
  have h1 : Conn G (F ∪ B) v (repOf G P F v) :=
    Conn.mono Finset.subset_union_left (conn_repOf hv)
  have hmid : Conn G (F ∪ B) (repOf G P F v) (repOf G P F w) :=
    (conn_iff_conn_cGraph (G := G) (P := P) (F := F) (E₀ := E₀) hP hF hB hvP hwP).2
      (hspan _ (repOf_mem_repSet P F hvP) _ (repOf_mem_repSet P F hwP))
  have h2 : Conn G (F ∪ B) (repOf G P F w) w :=
    (Conn.mono Finset.subset_union_left (conn_repOf hw)).symm
  exact h1.trans (hmid.trans h2)

/-- **The child's spanning property covers the instance's edges**: every instance edge has its
ends joined by the forest plus the crossed edges. -/
theorem conn_edge_span_cGraph (hP : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hF : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P) {B : Finset E}
    (hB : ∀ e ∈ B, e ∈ crossE G F E₀)
    (hspan : ∀ u ∈ repSet G P F, ∀ v ∈ repSet G P F,
      Conn (cGraph G P F E₀) (B.subtype (fun e => e ∈ crossE G F E₀)) u v)
    {e : E} (he : e ∈ E₀) : Conn G (F ∪ B) (G.src e) (G.dst e) := by
  by_cases hc : Conn G F (G.src e) (G.dst e)
  · exact Conn.mono Finset.subset_union_left hc
  · have hec : e ∈ crossE G F E₀ := (mem_crossE (G := G) F E₀ (e := e)).2 ⟨he, hc⟩
    have hspan' := hspan _ (repOf_mem_repSet P F (hP e he).1)
      _ (repOf_mem_repSet P F (hP e he).2)
    exact (conn_iff_conn_cGraph (G := G) (P := P) (F := F) (E₀ := E₀) hP hF hB
      (hP e he).1 (hP e he).2).2 hspan'

/-- **Contraction preserves total weight**: a family of cross edges weighs the same upstairs and in
the contracted graph. -/
theorem wsum_cGraph {B : Finset E} (hB : ∀ e ∈ B, e ∈ crossE G F E₀) :
    wsum (cGraph G P F E₀) (B.subtype (fun e => e ∈ crossE G F E₀)) = wsum G B := by
  show (B.subtype (fun e => e ∈ crossE G F E₀)).sum (fun e => G.weight e.1) = B.sum G.weight
  rw [Finset.sum_subtype_eq_sum_filter (f := G.weight),
    Finset.filter_true_of_mem (s := B) hB]

/-- **The child's forest lifts.**  A forest of the contracted graph, read upstairs through the
cross edges, is a forest of the original graph once the parent's forest is added: the two pieces
are edge-disjoint, and every contracted add is legal upstairs because a path through `F ∪ B₀`
would contract to the very connection the child's forest lacks. -/
theorem isForest_union_cGraph {F : Finset E} (hFf : IsForest G F)
    (hPF : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P) {B : Finset E}
    (hB : ∀ e ∈ B, e ∈ crossE G F E₀)
    (hB' : IsForest (cGraph G P F E₀) (B.subtype (fun e => e ∈ crossE G F E₀))) :
    IsForest G (F ∪ B) := by
  classical
  refine IsForest.rec (motive := fun F' _ => ∀ (B : Finset E),
      (∀ x ∈ B, x ∈ crossE G F E₀) →
        B.subtype (fun x => x ∈ crossE G F E₀) = F' → IsForest G (F ∪ B))
    ?_ ?_ hB' B hB rfl
  · intro B hB hEq
    have hBempty : B = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨x, hx⟩
      have hmem : (⟨x, hB x hx⟩ : {e // e ∈ crossE G F E₀}) ∈
          (∅ : Finset {e // e ∈ crossE G F E₀}) := by
        rw [← hEq]
        exact Finset.mem_subtype.mpr hx
      exact absurd hmem (Finset.notMem_empty _)
    rw [hBempty, Finset.union_empty]
    exact hFf
  · intro F'₀ e hF'₀ hne hnc ih B hB hEq
    have heB' : e ∈ B.subtype (fun e => e ∈ crossE G F E₀) := by
      rw [hEq]
      exact Finset.mem_insert_self _ _
    have heB : e.1 ∈ B := (Finset.mem_subtype (p := fun x => x ∈ crossE G F E₀)).1 heB'
    have hB₀ : ∀ x ∈ B.erase e.1, x ∈ crossE G F E₀ :=
      fun x hx => hB x (Finset.mem_of_mem_erase hx)
    have hB₀sub : (B.erase e.1).subtype (fun x => x ∈ crossE G F E₀) = F'₀ := by
      ext x
      constructor
      · intro hx
        have hx' := (Finset.mem_subtype (p := fun x => x ∈ crossE G F E₀)).1 hx
        have hxB : x.1 ∈ B := Finset.mem_of_mem_erase hx'
        have hxe : x.1 ≠ e.1 := Finset.ne_of_mem_erase hx'
        have hmem : x ∈ B.subtype (fun x => x ∈ crossE G F E₀) :=
          Finset.mem_subtype.mpr hxB
        rw [hEq] at hmem
        rcases Finset.mem_insert.1 hmem with hxE | hxF
        · exact absurd (congrArg Subtype.val hxE) hxe
        · exact hxF
      · intro hx
        have hmem : x ∈ B.subtype (fun x => x ∈ crossE G F E₀) := by
          rw [hEq]
          exact Finset.mem_insert_of_mem hx
        have hxB : x.1 ∈ B :=
          (Finset.mem_subtype (p := fun x => x ∈ crossE G F E₀)).1 hmem
        refine Finset.mem_subtype.mpr (Finset.mem_erase.mpr ⟨?_, hxB⟩)
        intro hxe
        have hxe' : x = e := Subtype.ext hxe
        exact hnc (Conn.step e (hxe' ▸ hx))
    have hnc' : ¬ Conn G (F ∪ B.erase e.1) (G.src e.1) (G.dst e.1) := by
      intro hconn
      have hcol := conn_cGraph_of_conn (G := G) (P := P) (F := F) (E₀ := E₀) hPF
        (B := B.erase e.1) hB₀ hconn
      rw [hB₀sub] at hcol
      exact hnc hcol
    rw [← Finset.insert_erase heB, Finset.union_insert]
    exact IsForest.insert (ih (B.erase e.1) hB₀ hB₀sub) (crossE_nloop (G := G) (F := F) (E₀ := E₀) (e := e.1) e.2) hnc'

/-- A family of cross edges is disjoint from the forest, so the two add up. -/
theorem disjoint_F_of_subset_crossE {B : Finset E} (hB : ∀ e ∈ B, e ∈ crossE G F E₀) :
    Disjoint F B :=
  (disjoint_crossE_F (G := G) F E₀).mono_right (Finset.subset_iff.mpr hB)

/-- The §4 edge split is a sum: kept edges plus contracted edges. -/
theorem card_union_of_subset_crossE {B : Finset E} (hB : ∀ e ∈ B, e ∈ crossE G F E₀) :
    (F ∪ B).card = F.card + B.card :=
  Finset.card_union_of_disjoint (disjoint_F_of_subset_crossE (G := G) (F := F) (E₀ := E₀) hB)

/-- A supported edge is connected by the whole forest: `F≤w(e) ⊆ F`. -/
theorem conn_of_supported {F : Finset E} {e : E} (h : supported G F e) :
    Conn G F (G.src e) (G.dst e) :=
  h.mono (Finset.filter_subset _ _)

/-- **Cross edges are unsupported.**  This is what makes contraction the recursion on §1.2's
retained set `U(F)`: an edge the forest fails to connect is *a fortiori* unsupported. -/
theorem crossE_subset_unsupp : crossE G F E₀ ⊆ unsupp G F := by
  intro e he
  rw [mem_unsupp]
  intro hsup
  exact ((mem_crossE (G := G) F E₀ (e := e)).1 he).2 (conn_of_supported (G := G) hsup)

theorem crossE_card_le : (crossE G F E₀).card ≤ E₀.card :=
  Finset.card_le_card (crossE_subset (G := G) F E₀)

theorem repSet_card_le_card : (repSet G P F).card ≤ P.card :=
  Finset.card_le_card (repSet_subset P F)

/-- **One recursion level is sound.**  If the child's forest is a forest of the contracted graph and
spans every contracted edge, then the parent's forest together with it is a forest covering the whole
instance: §4's "contract, recurse, splice the child's forest back" preserves both forestness and
spanning. -/
theorem isForest_span_of_child (hP : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) {F : Finset E}
    (hFf : IsForest G F) (hPF : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P) {B : Finset E}
    (hB : ∀ e ∈ B, e ∈ crossE G F E₀)
    (hB' : IsForest (cGraph G P F E₀) (B.subtype (fun e => e ∈ crossE G F E₀)))
    (hspan : ∀ e : {e // e ∈ crossE G F E₀},
      Conn (cGraph G P F E₀) (B.subtype (fun e => e ∈ crossE G F E₀))
        ((cGraph G P F E₀).src e) ((cGraph G P F E₀).dst e)) :
    IsForest G (F ∪ B) ∧ ∀ e ∈ E₀, Conn G (F ∪ B) (G.src e) (G.dst e) := by
  refine ⟨isForest_union_cGraph P E₀ hFf hPF hB hB', fun e he => ?_⟩
  by_cases hc : Conn G F (G.src e) (G.dst e)
  · exact Conn.mono Finset.subset_union_left hc
  · have hec : e ∈ crossE G F E₀ := (mem_crossE (G := G) F E₀ (e := e)).2 ⟨he, hc⟩
    exact (conn_iff_conn_cGraph (G := G) (P := P) (F := F) (E₀ := E₀) hP hPF hB
      (hP e he).1 (hP e he).2).2 (hspan ⟨e, hec⟩)


/-- The child instance has the same shape: every end of a contracted edge is a representative of
the parent instance, so it lies in the child's vertex set.  This is what lets the §4 recursion be
applied one level down without re-deriving `hP`. -/
theorem cGraph_src_mem_repSet (hP : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (q : {e // e ∈ crossE G F E₀}) :
    (cGraph G P F E₀).src q ∈ repSet G P F :=
  repOf_mem_repSet P F (hP q.1 (crossE_subset (G := G) F E₀ q.2)).1

theorem cGraph_dst_mem_repSet (hP : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (q : {e // e ∈ crossE G F E₀}) :
    (cGraph G P F E₀).dst q ∈ repSet G P F :=
  repOf_mem_repSet P F (hP q.1 (crossE_subset (G := G) F E₀ q.2)).2

/-- The contracted instance satisfies the same end-condition as its parent. -/
theorem cGraph_hP (hP : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) :
    ∀ q : {e // e ∈ crossE G F E₀},
      (cGraph G P F E₀).src q ∈ repSet G P F ∧ (cGraph G P F E₀).dst q ∈ repSet G P F :=
  fun q => ⟨cGraph_src_mem_repSet P F E₀ hP q, cGraph_dst_mem_repSet P F E₀ hP q⟩

/-- Weight is additive across the §4 split. -/
theorem wsum_union_of_subset_crossE {B : Finset E} (hB : ∀ e ∈ B, e ∈ crossE G F E₀) :
    wsum G (F ∪ B) = wsum G F + wsum G B :=
  Finset.sum_union (disjoint_F_of_subset_crossE (G := G) (F := F) (E₀ := E₀) hB)

/-- **The spliced forest costs the parent plus the child.**  §4 compares weights upstairs, but the
recursion computes them one level down; this says the two accounts agree. -/
theorem wsum_union_eq_child_wsum {B : Finset E} (hB : ∀ e ∈ B, e ∈ crossE G F E₀) :
    wsum G (F ∪ B) =
      wsum G F + wsum (cGraph G P F E₀) (B.subtype (fun e => e ∈ crossE G F E₀)) := by
  rw [wsum_union_of_subset_crossE (G := G) (F := F) (E₀ := E₀) hB,
    ← wsum_cGraph (G := G) (P := P) (F := F) (E₀ := E₀) hB]


/-- **The child's optimisation is the parent's.**  Two candidate splices compare upstairs exactly
as their child parts compare downstairs: the two weights differ by the constant `wsum G F`.  This is
the formal content of "recurse on the contracted instance": the minimum is preserved by the
translation, so it is enough to solve the problem one level down. -/
theorem wsum_splice_le_iff {B₁ B₂ : Finset E}
    (hB₁ : ∀ e ∈ B₁, e ∈ crossE G F E₀) (hB₂ : ∀ e ∈ B₂, e ∈ crossE G F E₀) :
    wsum G (F ∪ B₁) ≤ wsum G (F ∪ B₂) ↔
      wsum (cGraph G P F E₀) (B₁.subtype (fun e => e ∈ crossE G F E₀)) ≤
        wsum (cGraph G P F E₀) (B₂.subtype (fun e => e ∈ crossE G F E₀)) := by
  rw [wsum_union_eq_child_wsum (G := G) (P := P) (F := F) (E₀ := E₀) hB₁,
    wsum_union_eq_child_wsum (G := G) (P := P) (F := F) (E₀ := E₀) hB₂]
  constructor <;> intro h <;> linarith


/-- **Contraction reflects forestness.**  A forest upstairs whose extra edges are all contracted has
a forest downstairs.  Together with `isForest_union_cGraph` this makes forestness a two-way notion
across the §4 split, which is what a minimality comparison one level down needs. -/
theorem isForest_cGraph_of_union (hP : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) :
    ∀ (B : Finset E), (∀ e ∈ B, e ∈ crossE G F E₀) → IsForest G (F ∪ B) →
      IsForest (cGraph G P F E₀) (B.subtype (fun e => e ∈ crossE G F E₀)) := by
  classical
  intro B
  refine Finset.induction_on (motive := fun B => (∀ e ∈ B, e ∈ crossE G F E₀) →
      IsForest G (F ∪ B) →
      IsForest (cGraph G P F E₀) (B.subtype (fun e => e ∈ crossE G F E₀))) B ?_ ?_
  · intro _ _
    rw [show (∅ : Finset E).subtype (fun e => e ∈ crossE G F E₀) = ∅ by
      ext x
      simp]
    exact IsForest.empty
  · intro a s ha ih hB hBu
    have hBa : a ∈ crossE G F E₀ := hB a (Finset.mem_insert_self a s)
    have hBs : ∀ e ∈ s, e ∈ crossE G F E₀ :=
      fun e he => hB e (Finset.mem_insert_of_mem he)
    have hBsu : IsForest G (F ∪ s) :=
      hBu.subset (Finset.union_subset_union_right (Finset.subset_insert a s))
    have hEq : (insert a s).subtype (fun e => e ∈ crossE G F E₀) =
        insert ⟨a, hBa⟩ (s.subtype (fun e => e ∈ crossE G F E₀)) := by
      ext x
      simp only [Finset.mem_subtype, Finset.mem_insert]
      constructor
      · rintro (hx | hx)
        · exact Or.inl (Subtype.ext hx)
        · exact Or.inr hx
      · rintro (hx | hx)
        · exact Or.inl (by rw [hx])
        · exact Or.inr hx
    rw [hEq]
    refine IsForest.insert (ih hBs hBsu)
      (repOf_ne_of_crossE (G := G) (P := P) (F := F) (E₀ := E₀) hP (e := ⟨a, hBa⟩)) ?_
    intro hconn
    have hcont := conn_contract (G := G) (P := P) (F := F) (E₀ := E₀) hP
      (F'' := s.subtype (fun e => e ∈ crossE G F E₀)) hconn
    rw [image_subtype_crossE (G := G) (F := F) (E₀ := E₀) hBs] at hcont
    dsimp only [cGraph, WGraph.src, WGraph.dst] at hcont
    have hsa : G.src a ∈ P := (hP a (crossE_subset (G := G) F E₀ hBa)).1
    have hda : G.dst a ∈ P := (hP a (crossE_subset (G := G) F E₀ hBa)).2
    have hs := Conn.mono (Finset.subset_union_left (s₂ := s))
      (conn_repOf (G := G) (P := P) (F := F) hsa)
    have hd := Conn.mono (Finset.subset_union_left (s₂ := s))
      (conn_repOf (G := G) (P := P) (F := F) hda)
    have hall : Conn G (F ∪ s) (G.src a) (G.dst a) :=
      (hs.trans (show Conn G (F ∪ s) (repOf G P F (G.src a)) (repOf G P F (G.dst a))
        from hcont)).trans hd.symm
    have hsub : F ∪ s ⊆ (F ∪ insert a s).erase a := by
      intro x hx
      rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · intro hxa
        rcases Finset.mem_union.mp hx with hxF | hxs
        · exact Finset.disjoint_left.mp (disjoint_crossE_F (G := G) F E₀) hxF (hxa ▸ hBa)
        · exact ha (hxa ▸ hxs)
      · rcases Finset.mem_union.mp hx with hxF | hxs
        · exact Finset.mem_union.mpr (Or.inl hxF)
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert_of_mem hxs))
    exact (hBu.bridge (Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self a s))))
      (Conn.mono hsub hall)


/-- Upstairs spanning gives downstairs spanning: read every contracted edge through the child's own
connectivity.  Converse of the second half of `isForest_span_of_child`. -/
theorem span_cGraph_of_span (hPF : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P) {B : Finset E}
    (hB : ∀ e ∈ B, e ∈ crossE G F E₀)
    (hspan : ∀ e ∈ E₀, Conn G (F ∪ B) (G.src e) (G.dst e)) :
    ∀ q : {e // e ∈ crossE G F E₀},
      Conn (cGraph G P F E₀) (B.subtype (fun e => e ∈ crossE G F E₀))
        ((cGraph G P F E₀).src q) ((cGraph G P F E₀).dst q) := by
  intro q
  exact conn_cGraph_of_conn (G := G) (P := P) (F := F) (E₀ := E₀) hPF (B := B) hB
    (hspan q.1 (crossE_subset (G := G) F E₀ q.2))

/-- **Spanning is preserved both ways by contraction.**  The parent instance is spanned by `F ∪ B`
exactly when the contracted instance is spanned by the child forest. -/
theorem span_iff_span_cGraph (hP : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hPF : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P) {B : Finset E}
    (hB : ∀ e ∈ B, e ∈ crossE G F E₀) :
    (∀ e ∈ E₀, Conn G (F ∪ B) (G.src e) (G.dst e)) ↔
      ∀ q : {e // e ∈ crossE G F E₀},
        Conn (cGraph G P F E₀) (B.subtype (fun e => e ∈ crossE G F E₀))
          ((cGraph G P F E₀).src q) ((cGraph G P F E₀).dst q) := by
  constructor
  · intro hspan
    exact span_cGraph_of_span P F E₀ hPF hB hspan
  · intro hspan e he
    by_cases hc : Conn G F (G.src e) (G.dst e)
    · exact Conn.mono Finset.subset_union_left hc
    · have hec : e ∈ crossE G F E₀ := (mem_crossE (G := G) F E₀ (e := e)).2 ⟨he, hc⟩
      exact (conn_iff_conn_cGraph (G := G) (P := P) (F := F) (E₀ := E₀) hP hPF hB
        (hP e he).1 (hP e he).2).2 (hspan ⟨e, hec⟩)

/-- **The §4 step is optimal if the child is.**  If the child forest is a minimum among spanning
forests of the contracted instance, then the spliced forest `F ∪ B` is a minimum among all splices
`F ∪ B₂` with `B₂ ⊆ crossE` that span the parent instance.  (Comparing against *arbitrary* spanning
forests of `G`, not just splices, is the exchange argument the paper quotes from PR02.) -/
theorem splice_minimal (hP : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hPF : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P) {B : Finset E}
    (hB : ∀ e ∈ B, e ∈ crossE G F E₀)
    (hmin : ∀ B' : Finset {e // e ∈ crossE G F E₀}, IsForest (cGraph G P F E₀) B' →
      (∀ q : {e // e ∈ crossE G F E₀},
        Conn (cGraph G P F E₀) B' ((cGraph G P F E₀).src q) ((cGraph G P F E₀).dst q)) →
      wsum (cGraph G P F E₀) (B.subtype (fun e => e ∈ crossE G F E₀)) ≤
        wsum (cGraph G P F E₀) B') :
    ∀ B₂ : Finset E, (∀ e ∈ B₂, e ∈ crossE G F E₀) → IsForest G (F ∪ B₂) →
      (∀ e ∈ E₀, Conn G (F ∪ B₂) (G.src e) (G.dst e)) →
      wsum G (F ∪ B) ≤ wsum G (F ∪ B₂) := by
  intro B₂ hB₂ hB₂f hspan₂
  have hB₂' : IsForest (cGraph G P F E₀) (B₂.subtype (fun e => e ∈ crossE G F E₀)) :=
    isForest_cGraph_of_union P F E₀ hP B₂ hB₂ hB₂f
  have hsp₂ := span_cGraph_of_span (G := G) (P := P) (F := F) (E₀ := E₀) (B := B₂) hPF hB₂ hspan₂
  exact (wsum_splice_le_iff (G := G) (P := P) (F := F) (E₀ := E₀) hB hB₂).2
    (hmin _ hB₂' hsp₂)


/-- **One level of §4's contraction recursion**, as a record: the instance `(P, E₀)`, the forest `F`
found at this level, and the child's forest `B` (a set of contracted edges) together with its
forestness and spanning properties downstairs.  The projections below are precisely what the next
level and the splicing step consume, so a step can be iterated. -/
structure ContractStep (G : WGraph V E) (P : Finset V) (E₀ : Finset E) where
  hP : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P
  F : Finset E
  hFsub : F ⊆ E₀
  hFf : IsForest G F
  hPF : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P
  B : Finset E
  hB : ∀ e ∈ B, e ∈ crossE G F E₀
  hBf : IsForest (cGraph G P F E₀) (B.subtype (fun e => e ∈ crossE G F E₀))
  hBspan : ∀ q : {e // e ∈ crossE G F E₀},
    Conn (cGraph G P F E₀) (B.subtype (fun e => e ∈ crossE G F E₀))
      ((cGraph G P F E₀).src q) ((cGraph G P F E₀).dst q)

/-- Splicing a step: the parent forest together with the child's forest is a forest spanning the
whole instance. -/
theorem ContractStep.forest_span {P : Finset V} {E₀ : Finset E} (S : ContractStep G P E₀) :
    IsForest G (S.F ∪ S.B) ∧ ∀ e ∈ E₀, Conn G (S.F ∪ S.B) (G.src e) (G.dst e) :=
  isForest_span_of_child P E₀ S.hP S.hFf S.hPF S.hB S.hBf S.hBspan

/-- The child instance is again of the right shape, so the recursion can go one level down. -/
theorem ContractStep.child_shape {P : Finset V} {E₀ : Finset E} (S : ContractStep G P E₀) :
    ∀ q : {e // e ∈ crossE G S.F E₀},
      (cGraph G P S.F E₀).src q ∈ repSet G P S.F ∧
        (cGraph G P S.F E₀).dst q ∈ repSet G P S.F :=
  cGraph_hP P S.F E₀ S.hP

/-- The spliced forest's weight is the parent's plus the child's. -/
theorem ContractStep.wsum_splice {P : Finset V} {E₀ : Finset E} (S : ContractStep G P E₀) :
    wsum G (S.F ∪ S.B) =
      wsum G S.F + wsum (cGraph G P S.F E₀) (S.B.subtype (fun e => e ∈ crossE G S.F E₀)) :=
  wsum_union_eq_child_wsum (G := G) (P := P) (F := S.F) (E₀ := E₀) S.hB


/-- **A step is optimal if its child is.**  Given that the child's forest is a minimum among
spanning forests of the contracted instance, the splice `F ∪ B` is a minimum among all splices
`F ∪ B₂` that span the parent instance. -/
theorem ContractStep.optimal {P : Finset V} {E₀ : Finset E} (S : ContractStep G P E₀)
    (hmin : ∀ B' : Finset {e // e ∈ crossE G S.F E₀},
      IsForest (cGraph G P S.F E₀) B' →
      (∀ q : {e // e ∈ crossE G S.F E₀},
        Conn (cGraph G P S.F E₀) B' ((cGraph G P S.F E₀).src q) ((cGraph G P S.F E₀).dst q)) →
      wsum (cGraph G P S.F E₀) (S.B.subtype (fun e => e ∈ crossE G S.F E₀)) ≤
        wsum (cGraph G P S.F E₀) B') :
    ∀ B₂ : Finset E, (∀ e ∈ B₂, e ∈ crossE G S.F E₀) → IsForest G (S.F ∪ B₂) →
      (∀ e ∈ E₀, Conn G (S.F ∪ B₂) (G.src e) (G.dst e)) →
      wsum G (S.F ∪ S.B) ≤ wsum G (S.F ∪ B₂) :=
  splice_minimal (G := G) (P := P) (F := S.F) (E₀ := E₀) S.hP S.hPF S.hB hmin


/-- An edge of a forest `M` outside `F ⊆ M` is not joined by `F`: otherwise the forest would have
a cycle through it (`IsForest.bridge`).  Hence it is a contracted edge. -/
theorem mem_crossE_of_mem_of_not_mem {F M : Finset E} (hM : IsForest G M) (hFM : F ⊆ M)
    (hME : M ⊆ E₀) {e : E} (heM : e ∈ M) (heF : e ∉ F) : e ∈ crossE G F E₀ := by
  rw [mem_crossE]
  refine ⟨hME heM, fun hc => ?_⟩
  have hsub : F ⊆ M.erase e := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨fun hxe => heF (hxe ▸ hx), hFM hx⟩
  exact (hM.bridge heM) (Conn.mono hsub hc)

/-- **A forest is its kept part plus its contracted part.**  For `F ⊆ M` the edges of the forest `M`
outside `F` are exactly its contracted edges: `M = F ∪ (M ∩ crossE)`.  This is how an MSF is
projected onto the contracted instance. -/
theorem eq_union_inter_crossE {F M : Finset E} (hM : IsForest G M) (hFM : F ⊆ M)
    (hME : M ⊆ E₀) : M = F ∪ (M ∩ crossE G F E₀) := by
  ext e
  constructor
  · intro heM
    by_cases heF : e ∈ F
    · exact Finset.mem_union.mpr (Or.inl heF)
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr
        ⟨heM, mem_crossE_of_mem_of_not_mem (G := G) (E₀ := E₀) hM hFM hME heM heF⟩))
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · exact hFM h
    · exact (Finset.mem_inter.mp h).1

/-- Weight of a forest splits into its kept part and its contracted part. -/
theorem wsum_eq_add_inter_crossE {F M : Finset E} (hM : IsForest G M) (hFM : F ⊆ M)
    (hME : M ⊆ E₀) :
    wsum G M = wsum G F + wsum G (M ∩ crossE G F E₀) := by
  have hEq := eq_union_inter_crossE (G := G) (E₀ := E₀) hM hFM hME
  have hdisj : Disjoint F (M ∩ crossE G F E₀) :=
    (disjoint_crossE_F (G := G) F E₀).mono_right Finset.inter_subset_right
  show M.sum G.weight = F.sum G.weight + (M ∩ crossE G F E₀).sum G.weight
  conv_lhs => rw [hEq]
  rw [Finset.sum_union hdisj]


/-- **A spanning forest containing `F` projects to a spanning forest of the contracted instance.**
Given `F ⊆ M ⊆ E₀` and that `M` already joins the ends of every non-loop edge of the instance,
the contracted part `M ∩ crossE` is a spanning forest of `cGraph`.  This is the projection step of
the exchange argument: an MSF upstairs becomes a candidate downstairs. -/
theorem isSpanningForest_cGraph_of_union {F M : Finset E}
    (hP : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hPF : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P)
    (hMf : IsForest G M) (hFM : F ⊆ M) (hME : M ⊆ E₀)
    (hspan : ∀ e ∈ E₀, G.src e ≠ G.dst e → Conn G M (G.src e) (G.dst e)) :
    IsSpanningForest (cGraph G P F E₀)
      ((M ∩ crossE G F E₀).subtype (fun e => e ∈ crossE G F E₀)) := by
  have hEq := eq_union_inter_crossE (G := G) (E₀ := E₀) hMf hFM hME
  have hB : ∀ e ∈ M ∩ crossE G F E₀, e ∈ crossE G F E₀ :=
    fun _ he => (Finset.mem_inter.mp he).2
  refine ⟨isForest_cGraph_of_union P F E₀ hP (M ∩ crossE G F E₀) hB (hEq ▸ hMf), ?_⟩
  intro q hne
  have hE0 : q.1 ∈ E₀ := crossE_subset (G := G) F E₀ q.2
  have hneG : G.src q.1 ≠ G.dst q.1 :=
    crossE_nloop (G := G) (F := F) (E₀ := E₀) (e := q.1) q.2
  have hc := hspan q.1 hE0 hneG
  rw [hEq] at hc
  exact conn_cGraph_of_conn (G := G) (P := P) (F := F) (E₀ := E₀) hPF hB hc


/-- **Contraction preserves optimality** (the exchange argument of §4): if `M` is a minimum
spanning forest of `G` containing `F`, and `B` is a minimum spanning forest of the contracted
instance, then `F ∪ B` is a minimum spanning forest of `G`.  The projection of `M` is a candidate
downstairs, so the child's minimum wins; adding back `wsum G F` on both sides finishes. -/
theorem isMSF_union_cGraph {P : Finset V} {F : Finset E}
    (hP : ∀ e ∈ (Finset.univ : Finset E), G.src e ∈ P ∧ G.dst e ∈ P)
    (hFf : IsForest G F) {M : Finset E} (hM : IsMSF G M) (hFM : F ⊆ M)
    {B : Finset E} (hB : ∀ e ∈ B, e ∈ crossE G F Finset.univ)
    (hB' : IsSpanningForest (cGraph G P F Finset.univ)
      (B.subtype (fun e => e ∈ crossE G F Finset.univ)))
    (hmin : ∀ B' : Finset {e // e ∈ crossE G F Finset.univ},
      IsSpanningForest (cGraph G P F Finset.univ) B' →
      wsum (cGraph G P F Finset.univ)
          (B.subtype (fun e => e ∈ crossE G F Finset.univ)) ≤
        wsum (cGraph G P F Finset.univ) B') :
    IsMSF G (F ∪ B) := by
  have hPF : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P :=
    fun e _ => hP e (Finset.mem_univ e)
  have hspanB : ∀ e ∈ (Finset.univ : Finset E),
      Conn G (F ∪ B) (G.src e) (G.dst e) := by
    refine (span_iff_span_cGraph (G := G) (P := P) (F := F) (E₀ := Finset.univ)
      hP hPF hB).2 ?_
    intro q
    exact hB'.2 q (repOf_ne_of_crossE (G := G) (P := P) (F := F) (E₀ := Finset.univ) hP)
  have hFS : IsForest G (F ∪ B) :=
    isForest_union_cGraph P Finset.univ hFf hPF hB hB'.1
  refine ⟨⟨hFS, fun e _ => hspanB e (Finset.mem_univ e)⟩, ?_⟩
  intro T₂ hT₂
  have hMproj : IsSpanningForest (cGraph G P F Finset.univ)
      ((M ∩ crossE G F Finset.univ).subtype (fun e => e ∈ crossE G F Finset.univ)) :=
    isSpanningForest_cGraph_of_union (G := G) (P := P) (E₀ := Finset.univ)
      hP hPF hM.1.1 hFM (Finset.subset_univ M) (fun e _ => hM.1.2 e)
  have hmins := hmin _ hMproj
  have hw1 : wsum G (F ∪ B) =
      wsum G F + wsum (cGraph G P F Finset.univ)
        (B.subtype (fun e => e ∈ crossE G F Finset.univ)) :=
    wsum_union_eq_child_wsum (G := G) (P := P) (F := F) (E₀ := Finset.univ) hB
  have hw2 : wsum G M = wsum G F + wsum G (M ∩ crossE G F Finset.univ) :=
    wsum_eq_add_inter_crossE (G := G) (E₀ := Finset.univ) hM.1.1 hFM (Finset.subset_univ M)
  have hw3 : wsum (cGraph G P F Finset.univ)
      ((M ∩ crossE G F Finset.univ).subtype (fun e => e ∈ crossE G F Finset.univ)) =
      wsum G (M ∩ crossE G F Finset.univ) :=
    wsum_cGraph (G := G) (P := P) (F := F) (E₀ := Finset.univ)
      (B := M ∩ crossE G F Finset.univ) (fun _ he => (Finset.mem_inter.mp he).2)
  have hminM := hM.2 T₂ hT₂
  have hstep : wsum (cGraph G P F Finset.univ)
      (B.subtype (fun e => e ∈ crossE G F Finset.univ)) ≤
      wsum G (M ∩ crossE G F Finset.univ) := by
    rw [← hw3]
    exact hmins
  rw [hw1]
  linarith

/-- **Contraction preserves optimality, relative to the instance `E₀`.**  The exchange argument of
`isMSF_union_cGraph` with the comparison class restricted to `G[E₀]`: if `M` is a minimum spanning
forest of `G[E₀]` containing `F`, and `B` is a minimum spanning forest of the contracted instance,
then `F ∪ B` is a minimum spanning forest of `G[E₀]`.  This is the form §4's recursion consumes. -/
theorem isMSFOf_union_cGraph {P : Finset V} {E₀ F : Finset E}
    (hP : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hFf : IsForest G F)
    {M : Finset E} (hM : IsMSFOf G E₀ M) (hFM : F ⊆ M)
    {B : Finset E} (hB : ∀ e ∈ B, e ∈ crossE G F E₀)
    (hB' : IsSpanningForest (cGraph G P F E₀) (B.subtype (fun e => e ∈ crossE G F E₀)))
    (hmin : ∀ B' : Finset {e // e ∈ crossE G F E₀},
      IsSpanningForest (cGraph G P F E₀) B' →
      wsum (cGraph G P F E₀) (B.subtype (fun e => e ∈ crossE G F E₀)) ≤
        wsum (cGraph G P F E₀) B') :
    IsMSFOf G E₀ (F ∪ B) := by
  have hPF : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P :=
    fun e he => hP e (hM.1.2.1 (hFM he))
  have hFS : IsForest G (F ∪ B) := isForest_union_cGraph P E₀ hFf hPF hB hB'.1
  have hsub : F ∪ B ⊆ E₀ := by
    intro e he
    rcases Finset.mem_union.mp he with h | h
    · exact hM.1.2.1 (hFM h)
    · exact crossE_subset (G := G) F E₀ (hB e h)
  have hspan : ∀ e ∈ E₀, G.src e ≠ G.dst e → Conn G (F ∪ B) (G.src e) (G.dst e) := by
    have h := (span_iff_span_cGraph (G := G) (P := P) (F := F) (E₀ := E₀) hP hPF hB).2
      (fun q => hB'.2 q (repOf_ne_of_crossE (G := G) (P := P) (F := F) (E₀ := E₀) hP))
    exact fun e he _ => h e he
  refine ⟨⟨hFS, hsub, hspan⟩, ?_⟩
  intro T₂ hT₂
  have hMle := hM.2 T₂ hT₂
  have hMproj : IsSpanningForest (cGraph G P F E₀)
      ((M ∩ crossE G F E₀).subtype (fun e => e ∈ crossE G F E₀)) :=
    isSpanningForest_cGraph_of_union (G := G) (P := P) (E₀ := E₀)
      hP hPF hM.1.1 hFM hM.1.2.1 hM.1.2.2
  have hmins := hmin _ hMproj
  have hw1 : wsum G (F ∪ B) =
      wsum G F + wsum (cGraph G P F E₀)
        (B.subtype (fun e => e ∈ crossE G F E₀)) :=
    wsum_union_eq_child_wsum (G := G) (P := P) (F := F) (E₀ := E₀) hB
  have hw2 : wsum G M = wsum G F + wsum G (M ∩ crossE G F E₀) :=
    wsum_eq_add_inter_crossE (G := G) (E₀ := E₀) hM.1.1 hFM hM.1.2.1
  have hw3 : wsum (cGraph G P F E₀)
      ((M ∩ crossE G F E₀).subtype (fun e => e ∈ crossE G F E₀)) =
      wsum G (M ∩ crossE G F E₀) :=
    wsum_cGraph (G := G) (P := P) (F := F) (E₀ := E₀)
      (B := M ∩ crossE G F E₀) (fun _ he => (Finset.mem_inter.mp he).2)
  have hstep : wsum (cGraph G P F E₀)
      (B.subtype (fun e => e ∈ crossE G F E₀)) ≤
      wsum G (M ∩ crossE G F E₀) := by
    rw [← hw3]
    exact hmins
  rw [hw1]
  linarith

/-- The instance exchange argument applied to a recorded §4 step. -/
theorem ContractStep.isMSFOf_union {P : Finset V} {E₀ : Finset E}
    (S : ContractStep G P E₀) {M : Finset E} (hM : IsMSFOf G E₀ M) (hFM : S.F ⊆ M)
    (hmin : ∀ B' : Finset {e // e ∈ crossE G S.F E₀},
      IsSpanningForest (cGraph G P S.F E₀) B' →
      wsum (cGraph G P S.F E₀) (S.B.subtype (fun e => e ∈ crossE G S.F E₀)) ≤
        wsum (cGraph G P S.F E₀) B') :
    IsMSFOf G E₀ (S.F ∪ S.B) :=
  isMSFOf_union_cGraph (G := G) (P := P) (E₀ := E₀) S.hP S.hFf hM hFM S.hB
    ⟨S.hBf, fun q _ => S.hBspan q⟩ hmin

/-- **The child's MSF splices back.**  `isMSFOf_union_cGraph` with `hmin` supplied by the child's
own optimality: if the recursion's child returns a minimum spanning forest `B'` of the *whole*
contracted instance, then `F ∪ B'` is a minimum spanning forest of `G[E₀]`.  This is the form in
which §4 consumes the child's answer — the caller never has to prove a bare minimality. -/
theorem isMSFOf_union_cGraph_child {P : Finset V} {E₀ F : Finset E}
    (hP : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hFf : IsForest G F)
    {M : Finset E} (hM : IsMSFOf G E₀ M) (hFM : F ⊆ M)
    {B' : Finset {e // e ∈ crossE G F E₀}}
    (hB' : IsMSFOf (cGraph G P F E₀) (Finset.univ : Finset {e // e ∈ crossE G F E₀}) B') :
    IsMSFOf G E₀ (F ∪ B'.image Subtype.val) := by
  have hB : ∀ e ∈ B'.image Subtype.val, e ∈ crossE G F E₀ := by
    intro e he
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp he
    exact y.2
  have hBeq : (B'.image Subtype.val).subtype (fun e => e ∈ crossE G F E₀) = B' := by
    ext x
    rw [Finset.mem_subtype, Finset.mem_image]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have h : y = x := Subtype.ext hxy
      exact h ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  refine isMSFOf_union_cGraph (G := G) (P := P) (E₀ := E₀) hP hFf hM hFM hB ?_ ?_
  · rw [hBeq]
    exact ⟨hB'.1.1, fun q hne => hB'.1.2.2 q (Finset.mem_univ q) hne⟩
  · intro B₂ hB₂
    rw [hBeq]
    exact hB'.2 B₂ ⟨hB₂.1, Finset.subset_univ _,
      fun x _ hne => hB₂.2 x hne⟩

end Instance
