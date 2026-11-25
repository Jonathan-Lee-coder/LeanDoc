import DLMST.Boruvka
import DLMST.LightSpan
import DLMST.Selection

/-!
# §3.2, Lemma 3.2: every surviving batch edge is supported or projects

`Portals.lean` checks the *counting* half of Lemma 3.2 (`|D| ≤ kn`, `|P′| ≤ 2n/r`).  This file checks
its *guarantee*, which is the reason the batch is run at all:

> After replacing `F` by `MSF(G[F ∪ D])`, every edge `e = (u, v) ∈ B \ R′` satisfies at least one of
> • `e` is supported by `F` — `F≤w(e)` connects `u` and `v`;
> • both endpoints have spokes and `p(e) = max{w(σ(u)), w(σ(v))} ≤ w(e)`, so `e` admits a valid
>   projection.

The proof is a two-case split at each endpoint, and each case leans on one thing already proved
elsewhere: the first bullet is Fact 2.5 applied to a declared representative (`IsMSFOf.supported_of`,
`LightSpan.lean`), the second is the quota clause of Lemma 3.3 together with "the spoke update can only
improve the bound".  What this file adds is the interface the paper never writes down — the
`BatchSpec`/`SpokeSpec` records saying what the selection procedure and the spoke update actually
return — and the two lemmas that make the split legitimate:

* `exists_rep` — a group containing an admissible edge has a representative (take the smallest one in
  the tie-broken order; §3.2's "minimum weight" is then automatic since that order refines weight).
* `card_Sv` — `|Sv|` is the *number of groups won* at `v`, not merely the number of edges selected,
  because `IsRep.unique` makes the other-endpoint map injective on `sel v`.  §3.2 writes `|Sv| = k`
  and `k = r²` interchangeably; this is the justification.
* `exists_cnd` — the covering of `Portals.lean` really does produce a candidate spoke at every full
  vertex, which is the datum `SpokeSpec` asks for.

Three modelling choices, stated so they can be audited.  (1) Spokes are a *total* map `σ : V → E`
whereas the paper writes `σ(v) = ⊥` for a vertex without one; the second bullet therefore has to ask
for `incident G v (σ v)` explicitly, which is precisely the paper's "both endpoints have spokes".  (2) The
edges that fail a test (`R′`) are not passed around as a set: `adm e` says "`e` passes", and untested
edges are treated as admissible — the paper's "any untested edge can be made admissible without
changing the execution or output".  (3) "Lightest" is read in a tie-broken linear order on `E`
(`OrderedByWeight`, the property `wOrd` of `Boruvka.lean` has and `wOrd_weight` records), which is how
§3.3 says the median split is done.

Not formalised here: the recursive procedure that produces a `BatchSpec` (that is Lemma 3.3's own
argument, partly in `Selection.lean`), the projection graph `G′` and the lifting of `F′`/`R′` back to
`G`, and §3.4's bookkeeping of which round updates which spoke.
-/

namespace DLMST

set_option linter.unusedSectionVars false

open Classical

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {G : WGraph V E} [LinearOrder E]

/-! ## Viewing a batch from one vertex -/

/-- **`e` is incident at `v`** — an edge of the batch as seen from `v`. -/
def incident (G : WGraph V E) (v : V) (e : E) : Prop := G.src e = v ∨ G.dst e = v

/-- **The group key** (§3.2: "group the incident edges of `B` by their other endpoint").  Away from
`incident G v e` this is *not* an other endpoint, which is why every statement below restricts to
`Bv G v B`. -/
def other (G : WGraph V E) (v : V) (e : E) : V :=
  if G.src e = v then G.dst e else G.src e

/-- **The batch seen from `v`**: the input of the grouping. -/
noncomputable def Bv (G : WGraph V E) (v : V) (B : Finset E) : Finset E := B.filter fun e => incident G v e

theorem mem_Bv {v : V} {e : E} {B : Finset E} :
    e ∈ Bv G v B ↔ e ∈ B ∧ incident G v e := Finset.mem_filter

theorem other_src {v : V} {e : E} (h : G.src e = v) : other G v e = G.dst e := by
  simp [other, h]

theorem other_dst {v : V} {e : E} (h : G.dst e = v) : other G v e = G.src e := by
  by_cases h' : G.src e = v
  · simp [other, h, h']
  · simp [other, h']

/-- `e` **joins** `v` and `x`, in either direction — the graph-theoretic content of `other G v e = x`. -/
def joins (G : WGraph V E) (v x : V) (e : E) : Prop :=
  (G.src e = v ∧ G.dst e = x) ∨ (G.src e = x ∧ G.dst e = v)

theorem joins_swap {v x : V} {e : E} (h : joins G v x e) : joins G x v e :=
  h.elim Or.inr Or.inl

theorem joins_of_other {v x : V} {e : E} (hat : incident G v e) (hox : other G v e = x) :
    joins G v x e := by
  rcases hat with hsv | hdv
  · exact Or.inl ⟨hsv, (other_src hsv).symm.trans hox⟩
  · exact Or.inr ⟨(other_dst hdv).symm.trans hox, hdv⟩

theorem conn_of_joins {v x : V} {e : E} {F : Finset E} (h : joins G v x e) (he : e ∈ F) :
    Conn G F v x := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1; subst h2; exact Conn.step e he
  · subst h2; subst h1; exact (Conn.step e he).symm

/-- **A weight-respecting tie-broken order** (§3.3: "using the fixed edge order to break weight
ties").  `IsRep` of `Selection.lean` reads "lightest" in that order and this is the only property of it
§3.2 uses; `wOrd G` below is the same construction, and `edge_order_exists` in `Boruvka.lean` shows the
tie-breaker it needs exists for every finite edge type. -/
def OrderedByWeight (G : WGraph V E) : Prop :=
  ∀ a b : E, a ≤ b → G.weight a ≤ G.weight b

/-- `wOrd G` is weight-first: the tie-broken order `Boruvka.lean` uses has exactly this property. -/
theorem wOrd_weight {a b : E} (h : wOrd G a b) : G.weight a ≤ G.weight b := by
  rcases h with hlt | ⟨heq, _⟩
  · exact le_of_lt hlt
  · exact heq.le

/-! ## What the selection procedure returns -/

/-- **Lemma 3.3's guarantee, as §3.2 uses it.**  `sel v` is the set of edges the batch declares *from*
`v`.  The five fields say: they are batch edges seen from `v`; the quota `k` is respected; every
selected edge is its group's representative; an unselected representative forces a full quota (the
procedure returns *all* representatives when there are fewer than `k`); and the selected ones are the
lightest.  The last two together are `reps_below_of_not_lower`. -/
def BatchSpec (G : WGraph V E) (B : Finset E) (adm : E → Prop) (k : ℕ)
    (sel : V → Finset E) : Prop :=
  (∀ v, sel v ⊆ Bv G v B) ∧
    (∀ v, (sel v).card ≤ k) ∧
    (∀ v f, f ∈ sel v → IsRep (other G v) adm (Bv G v B) f) ∧
    (∀ v e, IsRep (other G v) adm (Bv G v B) e → e ∈ sel v ∨ (sel v).card = k) ∧
    (∀ v f, f ∈ sel v → ∀ e, IsRep (other G v) adm (Bv G v B) e → e ∉ sel v → f ≤ e)

theorem BatchSpec.sel_sub (hsel : BatchSpec G B adm k sel) :
    ∀ v, sel v ⊆ Bv G v B := hsel.1

theorem BatchSpec.card_le (hsel : BatchSpec G B adm k sel) :
    ∀ v, (sel v).card ≤ k := hsel.2.1

theorem BatchSpec.rep (hsel : BatchSpec G B adm k sel) :
    ∀ v f, f ∈ sel v → IsRep (other G v) adm (Bv G v B) f := hsel.2.2.1

theorem BatchSpec.quota (hsel : BatchSpec G B adm k sel) :
    ∀ v e, IsRep (other G v) adm (Bv G v B) e → e ∈ sel v ∨ (sel v).card = k := hsel.2.2.2.1

theorem BatchSpec.lightest (hsel : BatchSpec G B adm k sel) :
    ∀ v f, f ∈ sel v → ∀ e, IsRep (other G v) adm (Bv G v B) e → e ∉ sel v → f ≤ e :=
  hsel.2.2.2.2

/-- **A group with an admissible edge has a representative** (§3.2's "if one exists"): take the
smallest edge of the group in the tie-broken order.  Uniqueness is `IsRep.unique`. -/
theorem exists_rep {U : Finset E} {e : E} (he : e ∈ U) (hadm : adm e) :
    ∃ r, IsRep grp adm U r ∧ grp r = grp e := by
  classical
  have hne : (U.filter fun f => grp f = grp e ∧ adm f).Nonempty :=
    ⟨e, Finset.mem_filter.mpr ⟨he, rfl, hadm⟩⟩
  obtain ⟨r, hr, hmin⟩ :=
    Finset.exists_min_image (U.filter fun f => grp f = grp e ∧ adm f) (fun f => f) hne
  obtain ⟨hru, hre, hra⟩ := Finset.mem_filter.mp hr
  refine ⟨r, ⟨hru, hra, fun f hfU hgr hfa =>
    hmin f (Finset.mem_filter.mpr ⟨hfU, hgr.trans hre, hfa⟩)⟩, hre⟩

/-- **`Sv`** (§3.2): the neighbours of `v` reached by the selected edges. -/
def Sv (G : WGraph V E) (v : V) (sel : V → Finset E) : Finset V :=
  Finset.image (other G v) (sel v)

theorem mem_Sv {v x : V} {sel : V → Finset E} :
    x ∈ Sv G v sel ↔ ∃ e ∈ sel v, other G v e = x := Finset.mem_image

/-- **`|Sv|` is the number of groups won at `v`**, not merely the number of edges selected: one
selected edge per group, by `IsRep.unique`.  §3.2 writes `|Sv| = k` for "the quota was used up", and
this is what makes that legal. -/
theorem card_Sv (hsel : BatchSpec G B adm k sel) (v : V) :
    (Sv G v sel).card = (sel v).card := by
  unfold Sv
  refine Finset.card_image_of_injOn (fun a ha b hb hab => ?_)
  exact IsRep.unique (hsel.rep v a ha) (hsel.rep v b hb) hab

/-- **The declared set `D`** (§3.2: "`D` becomes the union of declared edges over all vertices"). -/
def Dcl (sel : V → Finset E) : Finset E := Finset.biUnion Finset.univ sel

theorem mem_Dcl {v : V} {e : E} {sel : V → Finset E} (he : e ∈ sel v) : e ∈ Dcl sel :=
  Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ v, he⟩

/-- **`|D| ≤ kn`** (Lemma 3.2's first sentence).  This is `declared_card` of `Portals.lean` in the
heterogeneous form the batch needs, where declared edges live in `E` and vertices in `V`. -/
theorem card_Dcl_le (hsel : BatchSpec G B adm k sel) :
    (Dcl sel).card ≤ k * Fintype.card V := by
  classical
  have h1 : (Dcl sel).card ≤ (Finset.univ : Finset V).sum (fun v => (sel v).card) :=
    Finset.card_biUnion_le
  have h2 : (Finset.univ : Finset V).sum (fun v => (sel v).card) ≤
      (Finset.univ : Finset V).sum (fun _ => k) :=
    Finset.sum_le_sum (fun v _ => hsel.card_le v)
  have h3 : (Finset.univ : Finset V).sum (fun _ => k) = (Finset.univ : Finset V).card * k :=
    Finset.sum_const_nat (fun _ _ => rfl)
  have h4 : (Finset.univ : Finset V).card * k ≤ Fintype.card V * k := by
    rw [Finset.card_univ]
  have h5 : Fintype.card V * k = k * Fintype.card V := Nat.mul_comm _ _
  omega

/-- **The spoke update** (§3.2, the paragraph before Lemma 3.2).  At a vertex whose quota filled, the
*candidate* spoke is a selected edge whose far end is a portal (`exists_cnd` builds one from the
covering), and the new spoke is the lighter of the candidate and the old one.  `σ` is total: the paper
writes `σ(v) = ⊥` where there is no spoke, and the second bullet of Lemma 3.2 asks for
`incident G v (σ v)`, which is its "both endpoints have spokes". -/
def SpokeSpec (G : WGraph V E) (sel : V → Finset E) (k : ℕ) (P : Finset V)
    (cnd σ : V → E) : Prop :=
  (∀ v, (sel v).card = k → cnd v ∈ sel v) ∧
    (∀ v, (sel v).card = k → other G v (cnd v) ∈ P) ∧
    (∀ v, (sel v).card = k → incident G v (σ v) ∧ G.weight (σ v) ≤ G.weight (cnd v))

theorem SpokeSpec.cnd_in (hsp : SpokeSpec G sel k P cnd σ) :
    ∀ v, (sel v).card = k → cnd v ∈ sel v := hsp.1

theorem SpokeSpec.cnd_portal (hsp : SpokeSpec G sel k P cnd σ) :
    ∀ v, (sel v).card = k → other G v (cnd v) ∈ P := hsp.2.1

theorem SpokeSpec.spoke (hsp : SpokeSpec G sel k P cnd σ) :
    ∀ v, (sel v).card = k → incident G v (σ v) ∧ G.weight (σ v) ≤ G.weight (cnd v) := hsp.2.2

/-- **The covering really does supply a candidate spoke**: "let `x` be the first portal selected that
belongs to `Sv`; the selected edge from `v` to `x` is the new candidate spoke".  The covering of the
full sets `Sv` is what `exists_greedy_maximal` and `portal_bound` of `Portals.lean` provide. -/
theorem exists_cnd (hsel : BatchSpec G B adm k sel) (P : Finset V)
    (hcover : ∀ v, k ≤ (Sv G v sel).card → ∃ x ∈ Sv G v sel, x ∈ P)
    (v : V) (hv : (sel v).card = k) : ∃ f ∈ sel v, other G v f ∈ P := by
  obtain ⟨x, hx, hxP⟩ :=
    hcover v (le_of_eq (hv.symm.trans (card_Sv hsel v).symm))
  obtain ⟨f, hf, hof⟩ := (mem_Sv).mp hx
  rw [← hof] at hxP
  exact ⟨f, hf, hxP⟩

/-! ## The dichotomy -/

/-- **The per-vertex half of Lemma 3.2.**  For an admissible batch edge `e` seen from an endpoint `v`,
either
* `v` selected the representative of `e`'s group — then some declared edge joins `v` to `e`'s other end
  and is no heavier than `e` (equivalently, by `mem_Sv`, that end lies in `Sv`), or
* the quota was full — `|sel v| = k`, and then *every* edge declared at `v` is no heavier than `e`. -/
theorem batch_at_vertex (hw : OrderedByWeight G) (hsel : BatchSpec G B adm k sel)
    (v : V) (e : E) (hat : incident G v e) (heB : e ∈ B) (hadm : adm e) :
    (∃ f ∈ sel v, joins G v (other G v e) f ∧ G.weight f ≤ G.weight e) ∨
      ((sel v).card = k ∧ ∀ f ∈ sel v, G.weight f ≤ G.weight e) := by
  classical
  by_cases h : ∃ f ∈ sel v, other G v f = other G v e
  · obtain ⟨f, hf, hof⟩ := h
    have hfU : f ∈ Bv G v B := hsel.sel_sub v hf
    have hatf : incident G v f := (Finset.mem_filter.mp hfU).2
    refine Or.inl ⟨f, hf, joins_of_other hatf hof,
      hw f e ((hsel.rep v f hf).2.2 e (mem_Bv.mpr ⟨heB, hat⟩) hof.symm hadm)⟩
  · have hex : ∃ r, IsRep (other G v) adm (Bv G v B) r ∧ other G v r = other G v e :=
      exists_rep (grp := other G v) (mem_Bv.mpr ⟨heB, hat⟩) hadm
    obtain ⟨r, hrep, hrg⟩ := hex
    have hrn : r ∉ sel v := fun hmem => h ⟨r, hmem, hrg⟩
    refine Or.inr ⟨(hsel.quota v r hrep).resolve_left hrn, fun f hf => ?_⟩
    exact le_trans (hw f r (hsel.lightest v f hf r hrep hrn))
      (hw r e (hrep.2.2 e (mem_Bv.mpr ⟨heB, hat⟩) hrg.symm hadm))

/-- **Bullet 1, as a one-edge certificate.**  A declared edge joining the ends of `e` and no heavier
than `e` makes `e` supported by *every* MSF of `G[F ∪ D]`: that edge is a one-edge `≤w(e)`-path inside
`F ∪ D`, and Fact 2.5 (`IsMSFOf.supported_of`) moves it into the forest. -/
theorem supported_of_declared {F F₁ D : Finset E} {sel : V → Finset E} {u v : V}
    (hT₁ : IsMSFOf G (F ∪ D) F₁) (hDec : Dcl sel ⊆ D) {e f : E}
    (hf : f ∈ sel u ∨ f ∈ sel v) (huf : joins G u v f) (he : joins G u v e)
    (hwf : G.weight f ≤ G.weight e) : supported G F₁ e := by
  have hfD : f ∈ D :=
    hf.elim (fun h => hDec (mem_Dcl h)) (fun h => hDec (mem_Dcl h))
  have hmem : f ∈ (F ∪ D).filter fun g => G.weight g ≤ G.weight e :=
    Finset.mem_filter.mpr ⟨Finset.mem_union.mpr (Or.inr hfD), hwf⟩
  refine IsMSFOf.supported_of hT₁ (show supported G (F ∪ D) e from conn_of_joins ?_ hmem)
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1; subst h2; exact huf
  · subst h1; subst h2; exact joins_swap huf

/-- **`p(e)`** (§3.2): the heavier of the two spokes; the projection of `e` is **valid** when it does
not exceed `w(e)`.  It depends only on the unordered pair of endpoints. -/
def pmax (G : WGraph V E) (σ : V → E) (u v : V) : ℝ :=
  max (G.weight (σ u)) (G.weight (σ v))

theorem pmax_swap (G : WGraph V E) (σ : V → E) (u v : V) :
    pmax G σ u v = pmax G σ v u := by
  unfold pmax
  rw [max_comm]

/-- **Lemma 3.2, machine-checked.**  Let `B` be a batch whose selection satisfies `BatchSpec`
(Lemma 3.3's guarantee), let `D` contain every declared edge, let `F₁` be an MSF of `G[F ∪ D]`, and let
`σ` be the spokes after the update.  Then every admissible edge of `B` — i.e. every edge of `B \ R′` —
is supported by `F₁`, or has genuine spokes at both ends with `p(e) ≤ w(e)`.

The two halves use different machinery: the first is Fact 2.5 applied to the declared representative,
the second is the quota clause at *both* ends plus `SpokeSpec`, which is the paper's "the spoke update
applied at the end can only improve on this bound". -/
theorem batch_supported_or_project {F F₁ D : Finset E} {B : Finset E} {adm : E → Prop} {k : ℕ}
    {sel : V → Finset E} {P : Finset V} {cnd σ : V → E}
    (hw : OrderedByWeight G) (hsel : BatchSpec G B adm k sel)
    (hsp : SpokeSpec G sel k P cnd σ) (hDec : Dcl sel ⊆ D)
    (hT₁ : IsMSFOf G (F ∪ D) F₁)
    (e : E) (heB : e ∈ B) (hadm : adm e) :
    supported G F₁ e ∨
      (incident G (G.src e) (σ (G.src e)) ∧ incident G (G.dst e) (σ (G.dst e)) ∧
        pmax G σ (G.src e) (G.dst e) ≤ G.weight e) := by
  classical
  obtain h1 | h1 := batch_at_vertex hw hsel (G.src e) e (Or.inl rfl) heB hadm
  · obtain ⟨f, hf, hj, hwf⟩ := h1
    rw [other_src rfl] at hj
    exact Or.inl (supported_of_declared hT₁ hDec (Or.inl hf) hj (Or.inl ⟨rfl, rfl⟩) hwf)
  · obtain h2 | h2 := batch_at_vertex hw hsel (G.dst e) e (Or.inr rfl) heB hadm
    · obtain ⟨f, hf, hj, hwf⟩ := h2
      rw [other_dst rfl] at hj
      exact Or.inl (supported_of_declared hT₁ hDec (Or.inl hf) hj (Or.inr ⟨rfl, rfl⟩) hwf)
    · refine Or.inr ⟨(hsp.spoke (G.src e) h1.1).1, (hsp.spoke (G.dst e) h2.1).1, ?_⟩
      unfold pmax
      refine max_le_iff.mpr ⟨le_trans (hsp.spoke (G.src e) h1.1).2
        (h1.2 _ (hsp.cnd_in (G.src e) h1.1)),
        le_trans (hsp.spoke (G.dst e) h2.1).2 (h2.2 _ (hsp.cnd_in (G.dst e) h2.1))⟩

end DLMST
