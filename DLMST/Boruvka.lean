import DLMST.Greedy

/-!
# A Borůvka phase: the edges it accepts still form a forest

`Greedy.lean` ends with a *scan*: one edge at a time, each accepted because it is the lightest edge
whose ends are still open.  The paper's phases are the other shape — every component of the current
forest simultaneously accepts its own lightest out-edge, and the graph is then contracted.  This file
starts that layer by proving the half that is specific to the simultaneous version: **the edges
accepted in one phase never close a cycle.**

Two things are needed that a single-edge step does not need.

* A *tie-broken* order `wOrd`, not the weight order alone.  With ties allowed, two components joined
  by two parallel edges of equal weight each pick their own copy, and the two copies form a cycle of
  length two — which is exactly the configuration that makes Borůvka's rule need a rule for breaking
  ties.  `wOrd G a b` compares weights first and an arbitrary linear order on `E` second, and
  `wOrd_antisymm` is the property the proof actually consumes.
* An orientation-free reading of "leaves the component".  `crossing` returns an edge with one end
  inside the set and one outside, without saying which end is the tail; since a cut cannot tell the
  two orientations apart, `leaves` is stated as "exactly one endpoint lies in the component", and the
  choice hypothesis of `BorPhase` then applies to whatever edge the cut produces.

With those in place the proof is short: take the phase's `wOrd`-greatest edge `m`
(`exists_wOrd_max`, so no sorting routine is needed), and suppose the other phase edges together with
`F` already join its ends.  `path_of_conn` turns that into a trail, `crossing` finds an edge of the
phase leaving the component that `m` was chosen from — that edge is `wOrd`-below `m` by the choice
rule and `wOrd`-above `m` by maximality, so it equals `m`, contradiction.  Induct on the number of
phase edges.

Extendability is here in its one-edge form (`boruvka_blue_rule`, `boruvka_round_one`): a lightest
out-edge of a single component is blue, by the same reduced-trail exchange `kruskal_step` uses, with
the component cut in place of the scan.  What was *not* here is the simultaneous round.  Forestness is
a statement about one cut at a time; extendability of the whole phase needs the lightness of `m`
against every edge leaving the *grown* component, and by then that set is a union of several
components, so `m` is no longer covered by its own choice rule.  That is the multi-cut blue rule
(Kerminen's, or Klein–Tarjan's blue rule for multiple cuts), and it is now written: `boruvka_round`
below performs the two-level exchange for the simultaneous phase (`wRank` maximality, then minimum
total rank), and `BoruvkaPhase.boruvka_round_at` carries it to Definition 2.8's phase, with
`boruvkaRun_extendable` the iterated form.-/

open Classical

namespace DLMST

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

/-- Weight, with an arbitrary linear order on the edge type breaking ties: `wOrd G a b` means `a` is
strictly lighter than `b`, or equally light and earlier in that order.  Finiteness is all that is
needed to have such an order (`edge_order_exists`).  Plain `≤` on weights would let two components
pick the two copies of a parallel pair and close a 2-cycle. -/
def wOrd (G : WGraph V E) (a b : E) : Prop :=
  G.weight a < G.weight b ∨ (G.weight a = G.weight b ∧ a ≤ b)

/-- The tie-break hypothesis is satisfiable: transport the order of `Fin n` along any enumeration. -/
theorem edge_order_exists (α : Type*) [Fintype α] [DecidableEq α] : Nonempty (LinearOrder α) :=
  ⟨Equiv.linearOrder (Fintype.equivFin α)⟩

theorem wOrd_refl (a : E) : wOrd G a a := Or.inr ⟨rfl, le_refl a⟩

theorem wOrd_total (a b : E) : wOrd G a b ∨ wOrd G b a := by
  cases lt_trichotomy (G.weight a) (G.weight b) with
  | inl h => exact Or.inl (Or.inl h)
  | inr h =>
    cases h with
    | inl he =>
      cases le_total a b with
      | inl hab => exact Or.inl (Or.inr ⟨he, hab⟩)
      | inr hba => exact Or.inr (Or.inr ⟨he.symm, hba⟩)
    | inr hb => exact Or.inr (Or.inl hb)

theorem wOrd_antisymm {a b : E} (h1 : wOrd G a b) (h2 : wOrd G b a) : a = b := by
  rcases h1 with hlt | ⟨heq, hle⟩
  · rcases h2 with hlt' | ⟨heq', _⟩
    · exact absurd (lt_trans hlt hlt') (lt_irrefl _)
    · rw [heq'] at hlt
      exact absurd hlt (lt_irrefl _)
  · rcases h2 with hlt' | ⟨heq', hle'⟩
    · rw [heq] at hlt'
      exact absurd hlt' (lt_irrefl _)
    · exact le_antisymm hle hle'

theorem wOrd_trans {a b c : E} (h1 : wOrd G a b) (h2 : wOrd G b c) : wOrd G a c := by
  rcases h1 with hlt | ⟨heq, hle⟩
  · rcases h2 with hlt' | ⟨heq', _⟩
    · exact Or.inl (lt_trans hlt hlt')
    · exact Or.inl (lt_of_lt_of_le hlt heq'.le)
  · rcases h2 with hlt' | ⟨heq', hle'⟩
    · exact Or.inl (lt_of_le_of_lt heq.le hlt')
    · exact Or.inr ⟨heq.trans heq', hle.trans hle'⟩

/-- The tie-broken order still refines weight, which is what lets it stand in for weight in a
lightness hypothesis. -/
theorem weight_le_of_wOrd {a b : E} (h : wOrd G a b) : G.weight a ≤ G.weight b :=
  h.elim (fun hlt => hlt.le) (fun ⟨heq, _⟩ => heq.le)

/-- Every nonempty finset of edges has a `wOrd`-greatest element, by induction on the set. -/
theorem exists_wOrd_max (A : Finset E) (hne : A.Nonempty) :
    ∃ m ∈ A, ∀ a ∈ A, wOrd G a m := by
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
    · obtain ⟨m, hm, hmax⟩ := ih hs
      rcases wOrd_total (G := G) b m with hbm | hmb
      · refine ⟨m, Finset.mem_insert_of_mem hm, fun a ha => ?_⟩
        rcases Finset.mem_insert.mp ha with heq | ha2
        · rw [heq]
          exact hbm
        · exact hmax a ha2
      · refine ⟨b, Finset.mem_insert_self b s, fun a ha => ?_⟩
        rcases Finset.mem_insert.mp ha with heq | ha2
        · rw [heq]
          exact wOrd_refl b
        · exact wOrd_trans (G := G) (hmax a ha2) hmb

/-- `leaves G F v e`: the edge `e` has exactly one endpoint in the `F`-component of `v`.  Stated
without reference to which endpoint, because a cut does not distinguish the two orientations. -/
def leaves (G : WGraph V E) (F : Finset E) (v : V) (e : E) : Prop :=
  (Conn G F v (G.src e) ∧ ¬ Conn G F v (G.dst e)) ∨
    (¬ Conn G F v (G.src e) ∧ Conn G F v (G.dst e))

/-- **A Borůvka phase.**  `A` is a set of edges open in `F` such that each is `wOrd`-least among the
edges leaving its own tail-component. -/
def BorPhase (G : WGraph V E) (F A : Finset E) : Prop :=
  (∀ e ∈ A, ¬ Conn G F (G.src e) (G.dst e)) ∧
    (∀ e ∈ A, ∀ f, leaves G F (G.src e) f → wOrd G e f)

/-- Subsetting a phase keeps a phase. -/
protected theorem BorPhase.erase {F A : Finset E} (hph : BorPhase G F A) (a : E) :
    BorPhase G F (A.erase a) :=
  ⟨fun e he => hph.1 e (Finset.mem_of_mem_erase he),
    fun e he f hl => hph.2 e (Finset.mem_of_mem_erase he) f hl⟩

/-- A phase edge is never already in the forest, so the phase genuinely grows it. -/
theorem BorPhase.not_mem {F A : Finset E} (hph : BorPhase G F A) {e : E} (he : e ∈ A) : e ∉ F :=
  not_mem_of_not_conn (hph.1 e he)

/-- **A Borůvka phase keeps a forest.**  No matter how many components accept an edge at once, the
accepted edges together with `F` stay acyclic.  The heaviest phase edge cannot be closed by the rest:
the cut it was chosen against would then already be crossed by a phase edge that is both lighter (by
the choice rule) and heavier (by maximality). -/
theorem boruvka_forest {F A : Finset E} (hF : IsForest G F) (hph : BorPhase G F A) :
    IsForest G (F ∪ A) := by
  classical
  have key : ∀ (n : ℕ) (A : Finset E), A.card = n → BorPhase G F A → IsForest G (F ∪ A) := by
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
      have hopen : ¬ Conn G F (G.src m) (G.dst m) := hph.1 m hm
      have hconn : ¬ Conn G (F ∪ A.erase m) (G.src m) (G.dst m) := by
        intro hc
        obtain ⟨es, pes, hmem⟩ := path_of_conn hc
        obtain ⟨g, hg, hcr⟩ := crossing pes {x | Conn G F (G.src m) x} (Conn.refl (G.src m)) hopen
        have hgF : g ∉ F := by
          intro hf
          rcases hcr with ⟨hs, hd⟩ | ⟨hs, hd⟩
          · exact absurd (Conn.trans hs (Conn.step g hf)) hd
          · exact absurd (Conn.trans hd ((Conn.step g hf).symm)) hs
        have hmemg : g ∈ F ∪ A.erase m := hmem g hg
        rw [Finset.mem_union] at hmemg
        have hgA : g ∈ A.erase m := hmemg.resolve_left hgF
        have hlv : leaves G F (G.src m) g := by
          rcases hcr with ⟨hs, hd⟩ | ⟨hs, hd⟩
          · exact Or.inl ⟨hs, hd⟩
          · exact Or.inr ⟨hs, hd⟩
        exact (Finset.mem_erase.mp hgA).1
          (wOrd_antisymm (hph.2 m hm g hlv) (hgt g (Finset.mem_of_mem_erase hgA))).symm
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

/-- No phase edge is a loop: an edge whose ends coincide is already joined by every edge set. -/
theorem BorPhase.nloop {F A : Finset E} (hph : BorPhase G F A) {e : E} (he : e ∈ A) :
    G.src e ≠ G.dst e :=
  fun h => hph.1 e he (by rw [h]; exact Conn.refl (G.dst e))

/-- **The Borůvka blue rule, for one component.**  If `e` is `wOrd`-lightest among the edges
leaving its own `F`-component and some minimum spanning forest contains `F`, then some minimum
spanning forest contains `insert e F`.

This is the component-local twin of `kruskal_step` in `Tree.lean`, and the two hypotheses are not
interchangeable: there the exchanged edge's weight is bounded because the *scan* has already seen
every open edge, here only because the *component* chose `e`.  So the cut that must be used is the
`F`-component of `G.src e` — the exchanged edge `g` is then an edge of a reduced `T`-trail crossing
that component, which is exactly what makes `leaves G F (G.src e) g` hold and hence makes `g`
comparable with `e` under the choice rule. -/
theorem boruvka_blue_rule {F T : Finset E} (hT : IsMSF G T) (hsub : F ⊆ T) (e : E)
    (hph : BorPhase G F ({e} : Finset E)) : ∃ T', IsMSF G T' ∧ insert e F ⊆ T' := by
  classical
  have hme : e ∈ ({e} : Finset E) := Finset.mem_singleton_self e
  obtain ⟨hTf, hTsp⟩ := hT.1
  have hopen : ¬ Conn G F (G.src e) (G.dst e) := hph.1 e hme
  have hlight : ∀ g, leaves G F (G.src e) g → G.weight e ≤ G.weight g := fun g hlv =>
    weight_le_of_wOrd (hph.2 e hme g hlv)
  have hne : G.src e ≠ G.dst e := fun he => hopen (he ▸ Conn.refl (G.src e))
  obtain ⟨es0, p0, hmem0⟩ := path_of_conn (hTsp e hne)
  obtain ⟨es, p, hmem, hf⟩ := hTf.exists_consecFree_trail es0 p0 hmem0
  let S : Set V := { x | Conn G F (G.src e) x }
  obtain ⟨g, hg, hcr⟩ := crossing p S (Conn.refl (G.src e)) (fun hh => hopen hh)
  have hlv : leaves G F (G.src e) g := by
    rcases hcr with ⟨hs, hd⟩ | ⟨hs, hd⟩
    · exact Or.inl ⟨hs, hd⟩
    · exact Or.inr ⟨hs, hd⟩
  have hgF : g ∉ F := by
    intro hgf
    rcases hcr with ⟨hs, hd⟩ | ⟨hs, hd⟩
    · exact absurd (hs.trans (Conn.step g hgf)) hd
    · exact absurd (hd.trans (Conn.step g hgf).symm) hs
  have hgT : g ∈ T := hmem g hg
  have hsep : ¬ Conn G (T.erase g) (G.src e) (G.dst e) := hTf.sep_of_mem_trail p hmem hf hg
  refine ⟨insert e (T.erase g), isMSF_exchange hT hgT hsep (hlight g hlv), ?_⟩
  intro x hx
  rcases Finset.mem_insert.mp hx with hx_eq | hxF
  · rw [hx_eq]
    exact Finset.mem_insert_self _ _
  · refine Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun hxg => absurd (hxg ▸ hxF) hgF, ?_⟩)
    exact hsub hxF

/-- A phase that accepts at most one edge keeps the accumulator extendable.  This is the `|A| = 1`
case of the obligation stated in the header; the induction that would give it for several edges is
exactly where a component-local choice rule stops covering the grown cut. -/
theorem boruvka_round_one {F A T : Finset E} (hT : IsMSF G T) (hsub : F ⊆ T) (e : E)
    (hA : A ⊆ ({e} : Finset E)) (hph : BorPhase G F A) :
    ∃ T', IsMSF G T' ∧ F ∪ A ⊆ T' := by
  classical
  by_cases hsome : ∃ m, m ∈ A
  · obtain ⟨m, hm⟩ := hsome
    have hm2 : m = e := Finset.mem_singleton.mp (hA hm)
    have hAm : A = ({m} : Finset E) := by
      apply Finset.ext
      intro x
      simp only [Finset.mem_singleton]
      constructor
      · intro hx
        exact (Finset.mem_singleton.mp (hA hx)).trans hm2.symm
      · intro hx
        rw [hx]
        exact hm
    have hph' : BorPhase G F ({m} : Finset E) := by rw [← hAm]; exact hph
    obtain ⟨T', hT', hsub'⟩ := boruvka_blue_rule (G := G) hT hsub m hph'
    refine ⟨T', hT', ?_⟩
    rw [hAm, Finset.union_singleton]
    exact hsub'
  · refine ⟨T, hT, ?_⟩
    have hA0 : A = ∅ := by
      by_contra h
      exact hsome ((Finset.ne_empty_iff_nonempty (s := A)).mp h)
    rw [hA0, Finset.union_empty]
    exact hsub

/-- `wOrd` made strict: lighter, or equally light and earlier in the tie-break. -/
def wOrdLt (G : WGraph V E) (a b : E) : Prop := wOrd G a b ∧ ¬ wOrd G b a

theorem wOrdLt.irrefl (G : WGraph V E) (a : E) : ¬ wOrdLt G a a := fun ⟨h, hn⟩ => hn h

theorem wOrdLt.trans {a b c : E} (h1 : wOrdLt G a b) (h2 : wOrdLt G b c) : wOrdLt G a c := by
  refine ⟨wOrd_trans (G := G) h1.1 h2.1, ?_⟩
  intro h
  exact h1.2 (wOrd_trans (G := G) h2.1 h)

theorem wOrdLt.ne {a b : E} (h : wOrdLt G a b) : a ≠ b := by
  intro heq
  rw [heq] at h
  exact h.2 (wOrd_refl b)

/-- Anything a strict order is not undecided by: `a ≤ b` plus `a ≠ b` is `a < b`. -/
theorem wOrdLt_of_wOrd {a b : E} (hab : wOrd G a b) (hne : a ≠ b) : wOrdLt G a b :=
  ⟨hab, fun hba => absurd (wOrd_antisymm hab hba) hne⟩

theorem wOrdLt_total (a b : E) (hne : a ≠ b) : wOrdLt G a b ∨ wOrdLt G b a :=
  (wOrd_total (G := G) a b).elim (fun h => Or.inl (wOrdLt_of_wOrd h hne))
    (fun h => Or.inr (wOrdLt_of_wOrd h (Ne.symm hne)))

/-- **The bookkeeping that turns the single-edge blue rule into a whole-round one.**  `wRank G A e`
counts the phase edges strictly `wOrd`-below `e`, so it is a rank function on `A`: strictly lighter
phase edges have strictly smaller rank.  Defining it as a cardinality rather than as an index in a
sorted list is deliberate — no sorting routine is needed, and `wRank_lt` is then just
`Finset.card_mono`. -/
noncomputable def wRank (G : WGraph V E) (A : Finset E) (e : E) : ℕ :=
  (A.filter fun a => wOrdLt G a e).card

theorem wRank_lt (hA : e ∈ A) (hlt : wOrdLt G e f) : wRank G A e < wRank G A f := by
  classical
  have hsub : insert e (A.filter fun a => wOrdLt G a e) ⊆
      A.filter fun a => wOrdLt G a f := by
    rw [Finset.insert_subset_iff]
    refine ⟨Finset.mem_filter.mpr ⟨hA, hlt⟩, fun a ha => ?_⟩
    obtain ⟨haA, hlt'⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨haA, wOrdLt.trans hlt' hlt⟩
  have hne : e ∉ A.filter fun a => wOrdLt G a e := fun h =>
    wOrdLt.irrefl G e ((Finset.mem_filter.mp h).2)
  have hcard : (A.filter fun a => wOrdLt G a e).card <
      (A.filter fun a => wOrdLt G a f).card := by
    have h1 : (insert e (A.filter fun a => wOrdLt G a e)).card ≤
        (A.filter fun a => wOrdLt G a f).card := Finset.card_mono hsub
    rw [Finset.card_insert_of_notMem hne] at h1
    omega
  exact hcard

/-- **A whole Borůvka phase is safe.**  If every edge of `A` is the `wOrd`-lightest edge leaving
its own `F`-component and some minimum spanning forest contains `F`, then some minimum spanning
forest contains all of `F ∪ A`.  This is the multi-cut blue rule (Kerminen; Klein–Tarjan) in the
form the paper's phases use.

The one-edge rule cannot simply be iterated: once earlier phase edges have merged components, the
next edge is no longer covered by its own component's choice rule.  Instead pick a minimum spanning
forest `T ⊇ F` by a two-level measure — first with the most phase edges in it, and among those with
the least total `wRank`.  If a phase edge `e` is missing from `T`, the reduced `T`-trail between the
ends of `e` crosses `e`'s own component in some edge `g`; `g ∉ F`, so the exchange keeps `F`, and
the choice rule puts `e` `wOrd`-below `g`.  Swapping `g` for `e` gives another minimum spanning
forest: if `g` was not a phase edge it holds more phase edges, and if it was it holds the same
number but a strictly smaller rank sum.  Either way `T` was not optimal. -/
theorem boruvka_round {F A T₀ : Finset E} (hT₀ : IsMSF G T₀) (hsub : F ⊆ T₀)
    (hph : BorPhase G F A) : ∃ T, IsMSF G T ∧ F ∪ A ⊆ T := by
  classical
  -- level one: a minimum spanning forest containing `F` with the most phase edges
  obtain ⟨T₁, hT₁mem, hT₁max⟩ :=
    Finset.exists_max_image (Finset.univ.filter fun T : Finset E => IsMSF G T ∧ F ⊆ T)
      (fun T : Finset E => (T ∩ A).card) ⟨T₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT₀, hsub⟩⟩
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
  -- the exchange: the reduced `T`-trail between the ends of `e` crosses `e`'s component
  obtain ⟨hTf, hTsp⟩ := hTmsf.1
  have hopen : ¬ Conn G F (G.src e) (G.dst e) := hph.1 e heA
  have hne : G.src e ≠ G.dst e := fun h => hopen (h ▸ Conn.refl (G.src e))
  obtain ⟨es0, p0, hmem0⟩ := path_of_conn (hTsp e hne)
  obtain ⟨es, p, hmem, hf⟩ := hTf.exists_consecFree_trail es0 p0 hmem0
  let S : Set V := { x | Conn G F (G.src e) x }
  obtain ⟨g, hg, hcr⟩ := crossing p S (Conn.refl (G.src e)) (fun hh => hopen hh)
  have hlv : leaves G F (G.src e) g := by
    rcases hcr with ⟨hs, hd⟩ | ⟨hs, hd⟩
    · exact Or.inl ⟨hs, hd⟩
    · exact Or.inr ⟨hs, hd⟩
  have hgF : g ∉ F := by
    intro hgf
    rcases hcr with ⟨hs, hd⟩ | ⟨hs, hd⟩
    · exact absurd (hs.trans (Conn.step g hgf)) hd
    · exact absurd (hd.trans (Conn.step g hgf).symm) hs
  have hgT : g ∈ T := hmem g hg
  have hwo : wOrd G e g := hph.2 e heA g hlv
  have hgne : g ≠ e := fun h => heT (h ▸ hgT)
  have hsep : ¬ Conn G (T.erase g) (G.src e) (G.dst e) := hTf.sep_of_mem_trail p hmem hf hg
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

end DLMST
