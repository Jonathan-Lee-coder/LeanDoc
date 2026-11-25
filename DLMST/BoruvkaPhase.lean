import DLMST.BoruvkaHalving

/-!
# Definition 2.8 made concrete: the phase's own edge set

`BoruvkaHalving.lean` proves that a phase halves the component count, but it takes the phase `A`
as an assumption (`hcover`).  This file builds the phase itself:

* `leaveSet G F v` — the edges with **exactly one** endpoint in the `F`-component of `v`; on the
  contracted graph these are the incident edges of the component, and `leaveSet_congr` says the set
  depends only on the component, not on the representative.
* `exists_wOrd_min` — the dual of `Boruvka.exists_wOrd_max`, so every nonempty set of leaving
  edges has a `wOrd`-least one.  `Finset.min'` is not used: it minimises the tie-break order alone,
  and its `≤` does not imply `wOrd`.
* `boruvkaPhase G F` — the edges that are some component's `wOrd`-least leaving edge, i.e.
  Definition 2.8's `S = {e_v : v ∈ V}`.  Since `wOrd` is total and antisymmetric the minimum is
  unique, so the filter formulation is the image of the selection function without needing a
  default element of `E`.

The one place where the modelling needs care is the *choice rule*.  `Boruvka.BorPhase` states it at
`comp (src e)`, which is only one of the two components that picked `e`; the paper's rule is at the
component that *picked* it.  `BorPhaseAt` below is that faithful version: `e` is `wOrd`-least among
the edges leaving the component of a witness `v`, and the witness is the vertex whose pick `e` was.
`BorPhase.toAt` shows the source-restricted rule implies the witness rule, so nothing in
`Boruvka.lean` is lost; `boruvka_forest_at` is the same heaviest-edge argument, with the cut taken
at the witness component instead of at the source component (a case split decides which end of the
phase edge lies in that component).

With the phase in hand `boruvkaPhase_halves` discharges `compCount_halves_of_forest`'s three
hypotheses — forestness, disjointness from `F`, and coverage of every component — and
`boruvkaRun_le_real` iterates the phase into the `n' ≤ 2m / 2^k` shape of
`CertificateBuild.certificate_of_display`.

Extendability is here too, in witness form: `boruvka_round_at` runs `Boruvka.boruvka_round`'s
two-level exchange with the cut at the component that picked the missing edge, so the concrete
phase is not merely acyclic but extendable to a minimum spanning forest (`boruvkaPhase_round`,
`boruvkaRun_extendable`).

The one hypothesis the halving still takes is activity (`hact`: no component is closed, i.e. every
component has a leaving edge).  At the first phase this is "no isolated vertices and no
loops-only vertices"; at later phases it says the run has not yet spanned the graph.  It is *not* an
assumption about the algorithm: the final section derives it from connectivity of `G`
(`hact_of_conn`: a connected graph with at least two components leaves every vertex an edge to
pick), so `boruvkaPhase_halves_of_conn` and `boruvkaRun_halves_of_conn` carry no activation
hypothesis.  The `− 1` in the run form is the "already spanned" case: once `F` spans there is no
leaving edge anywhere, and the count is already `1`.
-/

open Classical

namespace DLMST

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

/-! ## The leaving edges of a component -/

/-- `leaveSet G F v`: the edges with exactly one endpoint in the `F`-component of `v`. -/
noncomputable def leaveSet (G : WGraph V E) (F : Finset E) (v : V) : Finset E :=
  Finset.univ.filter (fun e => leaves G F v e)

theorem mem_leaveSet {F : Finset E} {v : V} {e : E} :
    e ∈ leaveSet G F v ↔ leaves G F v e := by
  classical
  simp [leaveSet]

/-- A leaving edge is never already inside the component: it is open in `F`. -/
theorem not_conn_of_leaves {F : Finset E} {v : V} {e : E} (hlv : leaves G F v e) :
    ¬ Conn G F (G.src e) (G.dst e) := by
  intro h
  rcases hlv with ⟨hs, hd⟩ | ⟨hs, hd⟩
  · exact hd (hs.trans h)
  · exact hs (hd.trans h.symm)

/-- Moving the base point inside a component does not change which edges leave it. -/
theorem leaves_of_conn {F : Finset E} {v w : V} (h : Conn G F v w) {e : E}
    (hlv : leaves G F v e) : leaves G F w e := by
  rcases hlv with ⟨hs, hd⟩ | ⟨hs, hd⟩
  · exact Or.inl ⟨h.symm.trans hs, fun hc => hd (h.trans hc)⟩
  · exact Or.inr ⟨fun hc => hs (h.trans hc), h.symm.trans hd⟩

/-- Leaving a component is a property of the component, not of the chosen vertex. -/
theorem leaveSet_congr {F : Finset E} {v w : V} (h : Conn G F v w) :
    leaveSet G F v = leaveSet G F w := by
  ext e
  rw [mem_leaveSet, mem_leaveSet]
  exact ⟨leaves_of_conn h, leaves_of_conn h.symm⟩

/-! ## The lightest leaving edge -/

/-- Every nonempty finset of edges has a `wOrd`-least element — the dual of `exists_wOrd_max`. -/
theorem exists_wOrd_min (A : Finset E) (hne : A.Nonempty) :
    ∃ m ∈ A, ∀ a ∈ A, wOrd G m a := by
  classical
  induction A using Finset.induction_on with
  | empty => exact absurd hne (by simp)
  | @insert b s hb ih =>
    rcases Finset.eq_empty_or_nonempty s with hs | hs
    · refine ⟨b, Finset.mem_insert_self b s, fun a ha => ?_⟩
      rcases Finset.mem_insert.mp ha with heq | ha2
      · rw [heq]
        exact wOrd_refl b
      · rw [hs] at ha2
        exact absurd ha2 (by simp)
    · obtain ⟨m, hm, hmin⟩ := ih hs
      rcases wOrd_total (G := G) b m with hbm | hmb
      · refine ⟨b, Finset.mem_insert_self b s, fun a ha => ?_⟩
        rcases Finset.mem_insert.mp ha with heq | ha2
        · rw [heq]
          exact wOrd_refl b
        · exact wOrd_trans (G := G) hbm (hmin a ha2)
      · refine ⟨m, Finset.mem_insert_of_mem hm, fun a ha => ?_⟩
        rcases Finset.mem_insert.mp ha with heq | ha2
        · rw [heq]
          exact hmb
        · exact hmin a ha2

/-- The `wOrd`-lightest edge leaving the component of `v`, tied down to an actual element of the
set (`exists_wOrd_min`), so that later definitions need no default element of `E`. -/
theorem exists_min_leaving {F : Finset E} {v : V} (h : (leaveSet G F v).Nonempty) :
    ∃ m, m ∈ leaveSet G F v ∧ ∀ f, leaves G F v f → wOrd G m f := by
  obtain ⟨m, hm, hmin⟩ := exists_wOrd_min (G := G) (leaveSet G F v) h
  exact ⟨m, hm, fun f hf => hmin f (mem_leaveSet.mpr hf)⟩

/-! ## The witness form of the choice rule -/

/-- **The choice rule of Definition 2.8.**  Every edge of the phase is `wOrd`-least among the
edges leaving the component that picked it.  Unlike `BorPhase`, the witness `v` is not forced to be
`G.src e`: a component can pick an edge from either side. -/
def BorPhaseAt (G : WGraph V E) (F A : Finset E) : Prop :=
  ∀ e ∈ A, ∃ v, leaves G F v e ∧ ∀ f, leaves G F v f → wOrd G e f

/-- The source-restricted rule of `Boruvka.lean` is a special case: the source of `e` is always a
legal witness for its own component. -/
theorem BorPhase.toAt {F A : Finset E} (hph : BorPhase G F A) : BorPhaseAt G F A := by
  intro e he
  exact ⟨G.src e, Or.inl ⟨Conn.refl _, hph.1 e he⟩, fun f hlf => hph.2 e he f hlf⟩

/-- A witness-form phase edge is open in `F`, hence absent from it. -/
theorem BorPhaseAt.not_mem {F A : Finset E} (hph : BorPhaseAt G F A) {e : E} (he : e ∈ A) :
    e ∉ F := by
  obtain ⟨v, hlv, -⟩ := hph e he
  exact not_mem_of_not_conn (not_conn_of_leaves hlv)

theorem BorPhaseAt.erase {F A : Finset E} (hph : BorPhaseAt G F A) (a : E) :
    BorPhaseAt G F (A.erase a) :=
  fun e he => hph e (Finset.mem_of_mem_erase he)

/-! ## Definition 2.8's selected set -/

/-- `boruvkaPhase G F`: the edges that are their component's `wOrd`-lightest leaving edge —
Definition 2.8's `S = {e_v : v ∈ V}` in the contracted view, where the components of `F` are the
vertices.  Stated as a filter rather than as the image of a choice function: `wOrd` is total and
antisymmetric, so a component's minimum is unique and nothing is lost, and the definition needs no
default element of `E`. -/
noncomputable def boruvkaPhase (G : WGraph V E) (F : Finset E) : Finset E :=
  Finset.univ.filter (fun e => ∃ v, leaves G F v e ∧ ∀ f, leaves G F v f → wOrd G e f)

theorem mem_boruvkaPhase {F : Finset E} {e : E} :
    e ∈ boruvkaPhase G F ↔ ∃ v, leaves G F v e ∧ ∀ f, leaves G F v f → wOrd G e f := by
  classical
  unfold boruvkaPhase
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ e, h⟩⟩

/-- The selected set satisfies the witness choice rule, by construction. -/
theorem boruvkaPhase_borPhaseAt {F : Finset E} :
    BorPhaseAt G F (boruvkaPhase G F) :=
  fun _ he => mem_boruvkaPhase.mp he

/-- Every component picks, so every component is one of the two sides of a phase edge: the
`hcover` hypothesis of `compCount_halves`. -/
theorem boruvkaPhase_cover {F : Finset E} (hact : ∀ v : V, (leaveSet G F v).Nonempty) :
    ∀ C ∈ Finset.univ.image (comp G F),
      ∃ e ∈ boruvkaPhase G F,
        comp G F (G.src e) = C ∨ comp G F (G.dst e) = C := by
  intro C hC
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨e, he, hmin⟩ := exists_min_leaving (G := G) (hact v)
  refine ⟨e, mem_boruvkaPhase.mpr ⟨v, mem_leaveSet.mp he, hmin⟩, ?_⟩
  rcases mem_leaveSet.mp he with ⟨hs, -⟩ | ⟨-, hd⟩
  · exact Or.inl (comp_eq_of_conn hs).symm
  · exact Or.inr (comp_eq_of_conn hd).symm

/-! ## Forestness of the selected set -/

/-- **Cut crossing for a phase edge.**  If the rest of the phase, together with `F`, already joins
the ends of `m`, then some *other* phase edge leaves `m`'s witness component, and it is not in
`F`.  This is the geometric core shared by forestness and the exchange argument; the caller
compares it with `m` through the choice rule and maximality. -/
theorem crossing_phase_edge {F A : Finset E} {m : E} {v : V} (hlv : leaves G F v m)
    (hc : Conn G (F ∪ A.erase m) (G.src m) (G.dst m)) :
    ∃ g, g ∈ A.erase m ∧ g ∉ F ∧ leaves G F v g := by
  classical
  rcases hlv with ⟨hs, hd⟩ | ⟨hs, hd⟩
  · obtain ⟨es, pes, hes⟩ := path_of_conn hc
    obtain ⟨g, hg, hcr⟩ := crossing pes {x : V | Conn G F v x} hs hd
    have hgF : g ∉ F := by
      intro hgf
      rcases hcr with ⟨hsin, hdout⟩ | ⟨hsin, hdout⟩
      · exact absurd (hsin.trans (Conn.step g hgf)) hdout
      · exact absurd (hdout.trans (Conn.step g hgf).symm) hsin
    have hgA : g ∈ A.erase m := (Finset.mem_union.mp (hes g hg)).resolve_left hgF
    exact ⟨g, hgA, hgF, hcr⟩
  · obtain ⟨es, pes, hes⟩ := path_of_conn (Conn.symm hc)
    obtain ⟨g, hg, hcr⟩ := crossing pes {x : V | Conn G F v x} hd hs
    have hgF : g ∉ F := by
      intro hgf
      rcases hcr with ⟨hsin, hdout⟩ | ⟨hsin, hdout⟩
      · exact absurd (hsin.trans (Conn.step g hgf)) hdout
      · exact absurd (hdout.trans (Conn.step g hgf).symm) hsin
    have hgA : g ∈ A.erase m := (Finset.mem_union.mp (hes g hg)).resolve_left hgF
    exact ⟨g, hgA, hgF, hcr⟩

/-- **A witness-form phase keeps a forest.**  Same argument as `boruvka_forest`: the heaviest
phase edge `m` cannot be closed by the rest, because the cut at its witness component would then
be crossed by a phase edge that is both lighter (choice rule) and heavier (maximality). -/
theorem boruvka_forest_at {F A : Finset E} (hF : IsForest G F) (hph : BorPhaseAt G F A) :
    IsForest G (F ∪ A) := by
  classical
  have key : ∀ (n : ℕ) (A : Finset E), A.card = n → BorPhaseAt G F A → IsForest G (F ∪ A) := by
    intro n
    induction n with
    | zero =>
      intro A hcard hph
      rw [Finset.card_eq_zero.mp hcard, Finset.union_empty]
      exact hF
    | succ n ih =>
      intro A hcard hph
      have hne : A.Nonempty := by
        refine Finset.ne_empty_iff_nonempty.mp ?_
        intro h
        rw [h, Finset.card_empty] at hcard
        omega
      obtain ⟨m, hm, hgt⟩ := exists_wOrd_max (G := G) A hne
      obtain ⟨v, hlv, hmin⟩ := hph m hm
      have hopen : ¬ Conn G F (G.src m) (G.dst m) := not_conn_of_leaves hlv
      have hconn : ¬ Conn G (F ∪ A.erase m) (G.src m) (G.dst m) := by
        intro hc
        obtain ⟨g, hgA, -, hlvg⟩ := crossing_phase_edge (A := A) hlv hc
        exact (Finset.mem_erase.mp hgA).1
          (wOrd_antisymm (hmin g hlvg) (hgt g (Finset.mem_of_mem_erase hgA))).symm
      have hEq : (F ∪ A : Finset E) = insert m (F ∪ A.erase m) := by
        ext x
        rw [Finset.mem_union, Finset.mem_insert, Finset.mem_union, Finset.mem_erase]
        by_cases hx : x = m
        · subst hx
          simp [hm]
        · simp [hx]
      rw [hEq]
      refine IsForest.insert (ih (A.erase m)
        (by rw [Finset.card_erase_of_mem hm, hcard]; omega) (hph.erase m)) ?_ hconn
      intro he
      exact hopen (he ▸ Conn.refl (G.src m))
  exact key A.card A rfl hph

/-! ## Halving for the concrete phase -/

/-- **One phase halves the component count**, in the generality the concrete phase needs: the
grown set only has to be a forest disjoint from `F` and to cover every component.  This is
`compCount_halves` with the phase hypothesis split into its two consequences. -/
theorem compCount_halves_of_forest {F A : Finset E} (hFA : IsForest G (F ∪ A))
    (hnot : ∀ e ∈ A, e ∉ F)
    (hcover : ∀ C ∈ Finset.univ.image (comp G F),
      ∃ e ∈ A, comp G F (G.src e) = C ∨ comp G F (G.dst e) = C) :
    2 * compCount G (F ∪ A) ≤ compCount G F := by
  classical
  have hF : IsForest G F := hFA.hereditary F Finset.subset_union_left
  have hdisj : Disjoint F A :=
    Finset.disjoint_left.mpr (fun e heF heA => hnot e heA heF)
  have hc : compCount G F ≤ 2 * A.card := by
    set S : Finset (Finset V) := Finset.univ.image (comp G F) with hS
    set T : Finset (Finset V) :=
      A.biUnion (fun e => ({comp G F (G.src e), comp G F (G.dst e)} : Finset (Finset V)))
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
          ({comp G F (G.src e), comp G F (G.dst e)} : Finset (Finset V)).card) :=
      Finset.card_biUnion_le
    have htwo : ∀ e ∈ A,
        ({comp G F (G.src e), comp G F (G.dst e)} : Finset (Finset V)).card ≤ 2 :=
      fun e _ => Finset.card_le_two
    calc compCount G F = S.card := by simp [compCount, hS]
      _ ≤ T.card := Finset.card_le_card hsub
      _ ≤ Finset.sum A (fun _ => 2) := le_trans hTle (Finset.sum_le_sum htwo)
      _ = 2 * A.card := by
          rw [Finset.sum_const_nat (fun _ _ => rfl), Nat.mul_comm]
  have h1 := card_add_compCount (G := G) hF
  have h2 := card_add_compCount (G := G) hFA
  have h3 : (F ∪ A).card = F.card + A.card := Finset.card_union_of_disjoint hdisj
  omega

/-- **Definition 2.8's selection halves the components**, with no phase hypothesis left: only the
`F`-forestness and "no component is closed" (`hact`) remain. -/
theorem boruvkaPhase_halves {F : Finset E} (hF : IsForest G F)
    (hact : ∀ v : V, (leaveSet G F v).Nonempty) :
    2 * compCount G (F ∪ boruvkaPhase G F) ≤ compCount G F :=
  compCount_halves_of_forest
    (boruvka_forest_at hF boruvkaPhase_borPhaseAt)
    (fun _ he => boruvkaPhase_borPhaseAt.not_mem he)
    (boruvkaPhase_cover hact)

/-! ## The iterated run -/

/-- `k` phases of Definition 2.8, starting from the empty forest. -/
noncomputable def boruvkaRun (G : WGraph V E) : ℕ → Finset E
  | 0 => ∅
  | n + 1 => boruvkaRun G n ∪ boruvkaPhase G (boruvkaRun G n)

theorem boruvkaRun_zero : boruvkaRun G 0 = (∅ : Finset E) := rfl

theorem boruvkaRun_succ (n : ℕ) :
    boruvkaRun G (n + 1) = boruvkaRun G n ∪ boruvkaPhase G (boruvkaRun G n) := rfl

theorem boruvkaRun_forest : ∀ i : ℕ, IsForest G (boruvkaRun G i) := by
  intro i
  induction i with
  | zero =>
      rw [boruvkaRun_zero]
      exact IsForest.empty
  | succ n ih =>
      rw [boruvkaRun_succ]
      exact boruvka_forest_at ih boruvkaPhase_borPhaseAt

/-- **`k` phases divide the component count by `2^k`**, for the concrete selection. -/
theorem boruvkaRun_pow_halves
    (hact : ∀ i : ℕ, ∀ v : V, (leaveSet G (boruvkaRun G i) v).Nonempty) (k : ℕ) :
    2 ^ k * compCount G (boruvkaRun G k) ≤ compCount G (boruvkaRun G 0) := by
  induction k with
  | zero => simp
  | succ n ih =>
      have hstep : 2 * compCount G (boruvkaRun G (n + 1)) ≤ compCount G (boruvkaRun G n) := by
        rw [boruvkaRun_succ]
        exact boruvkaPhase_halves (boruvkaRun_forest n) (hact n)
      calc 2 ^ (n + 1) * compCount G (boruvkaRun G (n + 1))
          = 2 ^ n * (2 * compCount G (boruvkaRun G (n + 1))) := by
              rw [Nat.pow_succ]
              ring
        _ ≤ 2 ^ n * compCount G (boruvkaRun G n) := Nat.mul_le_mul_left _ hstep
        _ ≤ compCount G (boruvkaRun G 0) := ih

/-- **The §4 vertex bound for the concrete run**: after `k` phases the component count is at most
`2m / 2^k`, with the start `c₀ = |V| ≤ 2m` discharged from "no isolated vertices".  This is the
`hn` slot of `CertificateBuild.certificate_of_display` for the run itself, not for an assumed
phase sequence. -/
theorem boruvkaRun_le_real
    (hact : ∀ i : ℕ, ∀ v : V, (leaveSet G (boruvkaRun G i) v).Nonempty) (k : ℕ)
    (hno : ∀ v : V, 1 ≤ degV G v) :
    (compCount G (boruvkaRun G k) : ℝ) ≤ 2 * (Fintype.card E : ℝ) / (2 : ℝ) ^ k := by
  have hnat := boruvkaRun_pow_halves (G := G) hact k
  have h0 : compCount G (boruvkaRun G 0) ≤ 2 * Fintype.card E := by
    rw [boruvkaRun_zero, compCount_empty]
    have h := card_le_two_mul_of_no_isolated (G := G) hno
    exact_mod_cast h
  have h1 : compCount G (boruvkaRun G k) * 2 ^ k ≤ 2 * Fintype.card E := by
    rw [Nat.mul_comm]
    exact le_trans hnat h0
  have hcast : (compCount G (boruvkaRun G k) : ℝ) * (2 : ℝ) ^ k ≤
      2 * (Fintype.card E : ℝ) := by
    have h2 : ((compCount G (boruvkaRun G k) * 2 ^ k : ℕ) : ℝ) ≤
        ((2 * Fintype.card E : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h2
    linarith
  rw [le_div_iff₀ (by positivity)]
  linarith

/-! ## Extendability of the concrete phase -/

/-- **A phase edge's own cut is crossed by a `T`-edge outside `F`.**  The reduced `T`-trail between
the ends of `e` crosses the witness component, and reducedness then says deleting the crossing edge
separates `e`'s ends — the two facts the exchange needs. -/
theorem exists_trail_crossing {F T : Finset E} {e : E} {v : V} (hTf : IsForest G T)
    (hTsp : ∀ e' : E, G.src e' ≠ G.dst e' → Conn G T (G.src e') (G.dst e'))
    (hne : G.src e ≠ G.dst e) (hlv : leaves G F v e) :
    ∃ g, g ∈ T ∧ g ∉ F ∧ leaves G F v g ∧ ¬ Conn G (T.erase g) (G.src e) (G.dst e) := by
  classical
  rcases hlv with ⟨hs, hd⟩ | ⟨hs, hd⟩
  · obtain ⟨es0, p0, hmem0⟩ := path_of_conn (hTsp e hne)
    obtain ⟨es, p, hmem, hf⟩ := hTf.exists_consecFree_trail es0 p0 hmem0
    obtain ⟨g, hg, hcr⟩ := crossing p {x : V | Conn G F v x} hs hd
    have hgF : g ∉ F := by
      intro hgf
      rcases hcr with ⟨hsin, hdout⟩ | ⟨hsin, hdout⟩
      · exact absurd (hsin.trans (Conn.step g hgf)) hdout
      · exact absurd (hdout.trans (Conn.step g hgf).symm) hsin
    exact ⟨g, hmem g hg, hgF, hcr, hTf.sep_of_mem_trail p hmem hf hg⟩
  · obtain ⟨es0, p0, hmem0⟩ := path_of_conn (Conn.symm (hTsp e hne))
    obtain ⟨es, p, hmem, hf⟩ := hTf.exists_consecFree_trail es0 p0 hmem0
    obtain ⟨g, hg, hcr⟩ := crossing p {x : V | Conn G F v x} hd hs
    have hgF : g ∉ F := by
      intro hgf
      rcases hcr with ⟨hsin, hdout⟩ | ⟨hsin, hdout⟩
      · exact absurd (hsin.trans (Conn.step g hgf)) hdout
      · exact absurd (hdout.trans (Conn.step g hgf).symm) hsin
    exact ⟨g, hmem g hg, hgF, hcr, fun hc => hTf.sep_of_mem_trail p hmem hf hg (Conn.symm hc)⟩

/-- **The multi-cut blue rule, witness form.**  If every edge of `A` is the `wOrd`-least leaving
edge of the component that picked it and some minimum spanning forest contains `F`, then some
minimum spanning forest contains all of `F ∪ A`.  The proof is `Boruvka.boruvka_round`'s two-level
exchange; only the cut moves from `comp (src e)` to the witness component. -/
theorem boruvka_round_at {F A T₀ : Finset E} (hT₀ : IsMSF G T₀) (hsub : F ⊆ T₀)
    (hph : BorPhaseAt G F A) : ∃ T, IsMSF G T ∧ F ∪ A ⊆ T := by
  classical
  -- level one: a minimum spanning forest containing `F` with the most phase edges
  obtain ⟨T₁, hT₁mem, hT₁max⟩ :=
    Finset.exists_max_image (Finset.univ.filter fun T : Finset E => IsMSF G T ∧ F ⊆ T)
      (fun T : Finset E => (T ∩ A).card)
      ⟨T₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT₀, hsub⟩⟩
  -- level two: among those, least total rank
  obtain ⟨T, hTco, hTmin⟩ :=
    Set.exists_min_image
      {T : Finset E | T ∈ Finset.univ.filter fun T : Finset E =>
        IsMSF G T ∧ F ⊆ T ∧ (T ∩ A).card = (T₁ ∩ A).card}
      (fun T : Finset E => (T ∩ A).sum (wRank G A))
      (Set.Finite.subset Set.finite_univ (Set.subset_univ _))
      ⟨T₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hT₁mem).2.1,
        (Finset.mem_filter.mp hT₁mem).2.2, rfl⟩⟩
  obtain ⟨hTmsf, hFT, hTeq⟩ := (Finset.mem_filter.mp hTco).2
  refine ⟨T, hTmsf, Finset.union_subset_iff.mpr ⟨hFT, ?_⟩⟩
  by_contra hnot
  rw [Finset.not_subset] at hnot
  obtain ⟨e, heA, heT⟩ := hnot
  -- the exchange: the reduced `T`-trail between the ends of `e` crosses `e`'s own component
  obtain ⟨v, hlv, hmin⟩ := hph e heA
  obtain ⟨hTf, hTsp⟩ := hTmsf.1
  have hopen : ¬ Conn G F (G.src e) (G.dst e) := not_conn_of_leaves hlv
  have hne : G.src e ≠ G.dst e := fun h => hopen (h ▸ Conn.refl (G.src e))
  obtain ⟨g, hgT, hgF, hlvg, hsep⟩ := exists_trail_crossing hTf hTsp hne hlv
  have hwo : wOrd G e g := hmin g hlvg
  have hgne : g ≠ e := fun h => heT (h ▸ hgT)
  -- the swapped forest: still minimum, still contains `F`
  have hT' : IsMSF G (insert e (T.erase g)) :=
    isMSF_exchange hTmsf hgT hsep (weight_le_of_wOrd hwo)
  have hF' : F ⊆ insert e (T.erase g) := fun x hx =>
    Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun hxg => hgF (hxg ▸ hx), hFT hx⟩)
  have hT'Fam : insert e (T.erase g) ∈
      Finset.univ.filter fun T : Finset E => IsMSF G T ∧ F ⊆ T :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT', hF'⟩
  -- its phase edges: the old ones minus `g`, plus `e`
  have hinter : (insert e (T.erase g)) ∩ A = insert e ((T ∩ A).erase g) := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · intro h
      obtain ⟨hx, hA⟩ := h
      rcases hx with rfl | hxT
      · exact Or.inl rfl
      · exact Or.inr ⟨hxT.1, hxT.2, hA⟩
    · rintro (rfl | ⟨hxg, hxT, hA⟩)
      · exact ⟨Or.inl rfl, heA⟩
      · exact ⟨Or.inr ⟨hxg, hxT⟩, hA⟩
  have heinter : e ∉ (T ∩ A).erase g := fun h =>
    heT (Finset.mem_inter.mp (Finset.mem_erase.mp h).2).1
  by_cases hgA : g ∈ A
  · -- same number of phase edges, strictly smaller rank sum
    have hmemg : g ∈ T ∩ A := Finset.mem_inter.mpr ⟨hgT, hgA⟩
    have hcard' : ((insert e (T.erase g)) ∩ A).card = (T ∩ A).card := by
      rw [hinter, Finset.card_insert_of_notMem heinter, Finset.card_erase_of_mem hmemg]
      have hpos : 0 < (T ∩ A).card := Finset.card_pos.mpr ⟨g, hmemg⟩
      omega
    have hT'co : insert e (T.erase g) ∈
        {T : Finset E | T ∈ Finset.univ.filter fun T : Finset E =>
          IsMSF G T ∧ F ⊆ T ∧ (T ∩ A).card = (T₁ ∩ A).card} :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ⟨hT', hF', by rw [hcard']; exact hTeq⟩⟩
    have hle : (T ∩ A).sum (wRank G A) ≤
        wRank G A e + ((T ∩ A).erase g).sum (wRank G A) := by
      have h := hTmin _ hT'co
      rw [hinter, Finset.sum_insert heinter] at h
      exact h
    have hsum : ((T ∩ A).erase g).sum (wRank G A) + wRank G A g =
        (T ∩ A).sum (wRank G A) := Finset.sum_erase_add _ _ hmemg
    have hrank : wRank G A e < wRank G A g := wRank_lt heA (wOrdLt_of_wOrd hwo (Ne.symm hgne))
    have hpos : wRank G A g ≤ (T ∩ A).sum (wRank G A) :=
      Finset.single_le_sum (f := wRank G A) (fun _ _ => Nat.zero_le _) hmemg
    omega
  · -- one more phase edge
    have hgTA : g ∉ T ∩ A := fun h => hgA (Finset.mem_inter.mp h).2
    have her : (T ∩ A).erase g = T ∩ A := by
      ext x
      by_cases hx : x = g
      · subst hx
        simp [hgTA]
      · simp [hx]
    have hcard' : ((insert e (T.erase g)) ∩ A).card = (T ∩ A).card + 1 := by
      rw [hinter, Finset.card_insert_of_notMem heinter, her]
    have hle : ((insert e (T.erase g)) ∩ A).card ≤ (T₁ ∩ A).card := hT₁max _ hT'Fam
    rw [hcard'] at hle
    omega

/-- **Definition 2.8's selection is extendable after one phase.** -/
theorem boruvkaPhase_round {F T₀ : Finset E} (hT₀ : IsMSF G T₀) (hsub : F ⊆ T₀) :
    ∃ T, IsMSF G T ∧ F ∪ boruvkaPhase G F ⊆ T :=
  boruvka_round_at hT₀ hsub boruvkaPhase_borPhaseAt

/-- **Every prefix of the run is extendable to a minimum spanning forest** — the concrete phases
are blue-safe, not merely acyclic. -/
theorem boruvkaRun_extendable (k : ℕ) : ∃ T, IsMSF G T ∧ boruvkaRun G k ⊆ T := by
  induction k with
  | zero =>
      obtain ⟨l, -, hl⟩ := kruskal_exists (G := G)
      exact ⟨K G l ∅, hl, by rw [boruvkaRun_zero]; exact Finset.empty_subset _⟩
  | succ n ih =>
      obtain ⟨T, hT, hsub⟩ := ih
      rw [boruvkaRun_succ]
      exact boruvkaPhase_round hT hsub

/-! ## Activation from connectivity

`boruvkaPhase_halves` carries `hact : ∀ v, (leaveSet G F v).Nonempty` — "no component is closed".
That is not an assumption about the algorithm: if the *graph* is connected and `F` has more than one
component, every proper component has an edge leaving it, and every vertex of that component sees
that edge (`leaves_of_conn`).  Only when `F` already spans is some component closed — and then the
halving has nothing left to do (the count is already `1`, and a phase adds no edge).

`comp_ne_univ_of_two_le` records the partition fact; `hact_of_conn` turns connectivity into
activation; `boruvkaPhase_halves_of_conn` and `boruvkaRun_halves_of_conn` are the bound with `hact`
discharged.  The `− 1` in the run version handles the case where the forest spans before the `k`-th
phase: `c − 1 = 0` then, and `2·0 ≤ 0` is the trivial step. -/

/-- If `F` has at least two components, no vertex's component is all of `V` (components are
disjoint, so if one is everything so is every other). -/
theorem comp_ne_univ_of_two_le {F : Finset E} (hc : 2 ≤ compCount G F) (v : V) :
    comp G F v ≠ Finset.univ := by
  intro h
  have himg : compCount G F = 1 := by
    rw [compCount]
    have : Finset.univ.image (comp G F) = {Finset.univ} := by
      apply Finset.Subset.antisymm
      · intro C hC
        obtain ⟨w, -, hw⟩ := Finset.mem_image.mp hC
        have hwv : w ∈ comp G F v := by rw [h]; exact Finset.mem_univ w
        have hweq : comp G F w = comp G F v := comp_eq_of_conn (mem_comp.mp hwv).symm
        rw [← hw, hweq, h]
        exact Finset.mem_singleton_self _
      · intro C hC
        rw [Finset.mem_singleton.mp hC]
        exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, h⟩
    rw [this]
    simp
  omega

/-- **A connected graph activates every vertex whose component is proper**: the component has an
outgoing edge, and the vertex is `F`-connected to that edge's inside end. -/
theorem leaveSet_nonempty_of_conn {F : Finset E}
    (hconn : ∀ u v : V, Conn G Finset.univ u v) {v : V}
    (hv : comp G F v ≠ Finset.univ) : (leaveSet G F v).Nonempty := by
  have hex : ∃ x, x ∉ comp G F v := by
    by_contra h
    push Not at h
    exact hv (Finset.eq_univ_of_forall h)
  obtain ⟨x, hx⟩ := hex
  obtain ⟨e, -, hcr⟩ :=
    crossing_of_conn (hconn v x) (comp G F v) comp_self_mem hx
  refine ⟨e, mem_leaveSet.mpr ?_⟩
  rcases hcr with ⟨hs, hd⟩ | ⟨hs, hd⟩
  · exact Or.inl ⟨mem_comp.mp hs, fun hc => hd (mem_comp.mpr hc)⟩
  · exact Or.inr ⟨fun hc => hs (mem_comp.mpr hc), mem_comp.mp hd⟩

/-- **Activation from connectivity**: a connected graph with at least two components leaves every
vertex an edge to pick. -/
theorem hact_of_conn {F : Finset E} (hconn : ∀ u v : V, Conn G Finset.univ u v)
    (hc : 2 ≤ compCount G F) : ∀ v : V, (leaveSet G F v).Nonempty :=
  fun v => leaveSet_nonempty_of_conn hconn (comp_ne_univ_of_two_le hc v)

/-- **One phase halves the components of a connected graph** — `hact` no longer a hypothesis. -/
theorem boruvkaPhase_halves_of_conn {F : Finset E} (hF : IsForest G F)
    (hconn : ∀ u v : V, Conn G Finset.univ u v) (hc : 2 ≤ compCount G F) :
    2 * compCount G (F ∪ boruvkaPhase G F) ≤ compCount G F :=
  boruvkaPhase_halves hF (hact_of_conn hconn hc)

/-- One step of the run: `2·(c_{i+1} − 1) ≤ c_i − 1`.  When `c_i ≥ 2` this is the halving; when
`c_i ≤ 1` the forest already spans (a phase edge would need a component with an outside), and both
sides are `0`. -/
theorem boruvkaRun_step {i : ℕ} (hconn : ∀ u v : V, Conn G Finset.univ u v) :
    2 * (compCount G (boruvkaRun G (i + 1)) - 1) ≤ compCount G (boruvkaRun G i) - 1 := by
  rw [boruvkaRun_succ]
  have hFA : IsForest G (boruvkaRun G i ∪ boruvkaPhase G (boruvkaRun G i)) :=
    boruvka_forest_at (boruvkaRun_forest i) boruvkaPhase_borPhaseAt
  have hmono : compCount G (boruvkaRun G i ∪ boruvkaPhase G (boruvkaRun G i))
      ≤ compCount G (boruvkaRun G i) := by
    have h1 := card_add_compCount (G := G) (boruvkaRun_forest i)
    have h2 := card_add_compCount (G := G) hFA
    have h3 : (boruvkaRun G i).card ≤
        (boruvkaRun G i ∪ boruvkaPhase G (boruvkaRun G i)).card :=
      Finset.card_le_card (Finset.subset_union_left)
    omega
  rcases Nat.lt_or_ge (compCount G (boruvkaRun G i)) 2 with hc | hc
  · have h0 : compCount G (boruvkaRun G i) ≤ 1 := by omega
    omega
  · have hhalf := boruvkaPhase_halves_of_conn (boruvkaRun_forest i) hconn hc
    have hpos : 1 ≤ compCount G (boruvkaRun G i) := by omega
    omega

/-- **`k` phases divide the *excess* component count by `2^k`** — connectivity alone, with no
activation hypothesis.  `c_k ≤ 1 + (n − 1)/2^k`: the run spans after `⌈log₂ n⌉` phases and the `−1`
is exactly the paper's "already connected" case. -/
theorem boruvkaRun_halves_of_conn (hconn : ∀ u v : V, Conn G Finset.univ u v) (k : ℕ) :
    2 ^ k * (compCount G (boruvkaRun G k) - 1) ≤ compCount G (boruvkaRun G 0) - 1 := by
  induction k with
  | zero => simp
  | succ n ih =>
      have hstep := boruvkaRun_step (G := G) (i := n) hconn
      calc 2 ^ (n + 1) * (compCount G (boruvkaRun G (n + 1)) - 1)
          = 2 ^ n * (2 * (compCount G (boruvkaRun G (n + 1)) - 1)) := by
              rw [Nat.pow_succ]
              ring
        _ ≤ 2 ^ n * (compCount G (boruvkaRun G n) - 1) := Nat.mul_le_mul_left _ hstep
        _ ≤ compCount G (boruvkaRun G 0) - 1 := ih

/-- Real form of `boruvkaRun_halves_of_conn`, in the shape of `CertificateBuild`'s vertex bound:
`c_k ≤ 1 + c_0/2^k`. -/
theorem boruvkaRun_le_one_add (hconn : ∀ u v : V, Conn G Finset.univ u v) (k : ℕ) :
    (compCount G (boruvkaRun G k) : ℝ) ≤
      1 + (compCount G (boruvkaRun G 0) : ℝ) / (2 : ℝ) ^ k := by
  have hnat := boruvkaRun_halves_of_conn (G := G) hconn k
  have hsub : compCount G (boruvkaRun G k) - 1 ≤
      (compCount G (boruvkaRun G 0) - 1) / 2 ^ k :=
    (Nat.le_div_iff_mul_le (pow_pos (by norm_num) k)).mpr (by
      rw [Nat.mul_comm]
      exact hnat)
  have hcast : ((compCount G (boruvkaRun G k) : ℕ) : ℝ) ≤
      ((compCount G (boruvkaRun G k) - 1 : ℕ) : ℝ) + 1 := by
    have h : compCount G (boruvkaRun G k) ≤ (compCount G (boruvkaRun G k) - 1) + 1 := by omega
    exact_mod_cast h
  have hdiv : (((compCount G (boruvkaRun G 0) - 1 : ℕ)) : ℝ) / (2 : ℝ) ^ k ≤
      (compCount G (boruvkaRun G 0) : ℝ) / (2 : ℝ) ^ k := by
    apply div_le_div_of_nonneg_right
    · exact_mod_cast Nat.sub_le _ _
    · positivity
  have h2 : (((compCount G (boruvkaRun G 0) - 1) / 2 ^ k : ℕ) : ℝ) ≤
      (((compCount G (boruvkaRun G 0) - 1 : ℕ)) : ℝ) / (2 : ℝ) ^ k := by
    have h := Nat.cast_div_le (α := ℝ)
      (m := compCount G (boruvkaRun G 0) - 1) (n := 2 ^ k)
    push_cast at h
    exact h
  have hsub' : ((compCount G (boruvkaRun G k) - 1 : ℕ) : ℝ) ≤
      (((compCount G (boruvkaRun G 0) - 1) / 2 ^ k : ℕ) : ℝ) := by exact_mod_cast hsub
  linarith

end DLMST