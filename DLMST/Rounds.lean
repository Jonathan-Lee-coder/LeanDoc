import DLMST.Batch
import DLMST.Schedule

/-!
# §3.3: the round state, Claims 3.5–3.6 and Lemma 3.7

`Schedule.lean` counts the bad rounds of Definition 3.4 but takes the *table* of preferred actions as
data.  This file supplies what that table is supposed to come from — the round state the paper describes
in §1.2 and §3.3 — and then checks the three statements that rest on it:

* **`MonoRow`** (§3.3: "within each block, the preferred action of `e` is `project` for an initial
  sequence of rounds, followed by `find`"; Definition 1.3's `PPPPFFF`), derived from the two facts the
  paper cites for it: the spokes are frozen inside a block, so `p(e)` is one fixed real number, and
  connectivity in `F≤a` only improves as the rounds run.  `good_project_succ` is the corollary the
  proofs actually quote — a good `project` round is followed by a `project` round.
* **Claim 3.5** ("every edge in the returned forest `F` is admissible"), as an induction over the three
  insertion sources the paper enumerates: a declared edge that passed the admissibility test, the lift
  of an edge a child level returned, and a rejected edge inserted at its *first* invalid level.  What
  Claim 3.6 consumes is `admOut_spokes`: the two spokes used to project an edge are no heavier than it.
* **Claim 3.6** ("if the child recursion supports the projected edge, then on return
  `F≤max{w(e),p(e)}` connects `u` and `v`").  This is the lifting argument, and it is the one place in §3
  where a path in a contracted graph must be read back as a walk in the original one.  `LiftsLe` is that
  read-back: each child edge is replaced by the three-edge walk `σ(x), f, σ(y)`.  `LiftsLe.walk`
  concatenates them and the last step is Fact 2.5 — the paper's "By Fact 2.5, `u` and `v` are connected
  in `F≤max{w(e),p(e)}`".
* **Lemma 3.7**, split the way its proof is: `lemma37_last` (the deepest level: Lemma 3.2's dichotomy,
  plus "the two spokes meet at a common portal", plus "`p(e′)` can only decrease"),
  `lemma37_project_step` (Claim 3.6 plus the good-round contradiction — the only place `MonoRow` is
  needed), `lemma37_rejected_error` (the sentence about rejected edges), and `lemma37`, the backward
  induction over recursion levels.  Levels are indexed by depth because an edge is projected into
  *exactly one* child instance.

Modelling choices, so they can be audited.  (1) `σ : V → E` stays *total* as in `Batch.lean`; "either
endpoint has no spoke" is `¬ incident G v (σ v)`, and the theorems that need spokes take
`hsp : ∀ x, incident G x (σ x)` — which is also how the paper silently drops clause (1) of the preference
rule from its case splits.  (2) The child instance is not rebuilt as a second `WGraph`: its vertices
*are* the parent's portals, so a child path is described from the parent side by `LiftsLe`, which keeps
the parent edge `f` that each child edge projects.  That is the datum behind "lifted back to the
corresponding edge `f = (x, y)` in `G`", and it is what makes `w(f) = w(f′)` and the spoke bound
available.  (3) Round forests are `F : Fin t → Finset E` inside one block and `Fre ⊆ F j` for the later
rounds is the formal reading of "at the end of that round the edge returns from the recursive call and is
incorporated into the forest".  (4) As in `Schedule.lean`, `act` is the *true* preference table; the
estimate is kept separate so that §3.3's notion of an error is a formula (`error`).

Not formalised here: §3.4's construction of the schedule and of the estimate (Definition 3.8, Lemma 3.11,
Claim 3.12), and the projection graph `G′` itself — `LiftsLe` is a per-edge read-back of a child path, not
a proof that the child instance is the portal graph.
-/

namespace DLMST

set_option linter.unusedSectionVars false

open Classical

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] {G : WGraph V E}
  [LinearOrder E]

/-! ## Thresholds and spokes -/

/-- Raising a threshold never destroys a connection inside `F`: the non-strict twin of
`MsfKernel.conn_below_mono`, and the step hidden in every "still connected later" sentence of §3.3. -/
theorem belowLe_mono {F : Finset E} {θ θ' : ℝ} (h : θ ≤ θ') : belowLe G F θ ⊆ belowLe G F θ' := by
  intro e he
  rw [belowLe_mem] at he ⊢
  exact ⟨he.1, le_trans he.2 h⟩

/-- A sub-forest's threshold set is contained in the bigger forest's. -/
theorem belowLe_subset {F₁ F₂ : Finset E} (h : F₁ ⊆ F₂) (θ : ℝ) :
    belowLe G F₁ θ ⊆ belowLe G F₂ θ := by
  intro e he
  rw [belowLe_mem] at he ⊢
  exact ⟨h he.1, he.2⟩

/-- **Threshold monotonicity for `F≤·`.** -/
theorem conn_belowLe_mono (F : Finset E) (θ θ' : ℝ) (h : θ ≤ θ') {u v : V}
    (huuv : Conn G (belowLe G F θ) u v) : Conn G (belowLe G F θ') u v :=
  Conn.mono (belowLe_mono h) huuv

/-- **`π(v)`**, the portal at the other end of `v`'s spoke (§1.2).  Under the total-`σ` convention this
is `other G v (σ v)`; a vertex whose `σ` is not incident has no spoke and `portal` returns a meaningless
endpoint, which is why every portal statement below also asks for `incident`. -/
def portal (G : WGraph V E) (σ : V → E) (v : V) : V := other G v (σ v)

/-- A genuine spoke joins its vertex to its portal. -/
theorem joins_portal {σ : V → E} {v : V} (hsp : incident G v (σ v)) :
    joins G v (portal G σ v) (σ v) :=
  joins_of_other hsp rfl

/-- **`p(e)`** (§1.2): the heavier of `e`'s two spoke weights, as a function of the edge. -/
def pE (G : WGraph V E) (σ : V → E) (e : E) : ℝ := pmax G σ (G.src e) (G.dst e)

theorem le_pE_left {σ : V → E} {e : E} : G.weight (σ (G.src e)) ≤ pE G σ e :=
  le_max_left _ _

theorem le_pE_right {σ : V → E} {e : E} : G.weight (σ (G.dst e)) ≤ pE G σ e :=
  le_max_right _ _

/-- A preference that is not `find` is `project`. -/
private theorem prefProject_of_not_find {p : Pref} (h : p ≠ Pref.find) : p = Pref.project := by
  cases p with
  | find => exact absurd rfl h
  | project => rfl

/-- **A one-edge trail between joined vertices**, in whichever direction the endpoints are stored.  This
is the primitive the lifting argument concatenates. -/
theorem Path.of_joins {x y : V} {e : E} (h : joins G x y e) : Path G x [e] y := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1; subst h2; exact Path.edge e
  · subst h1; subst h2; exact Path.edge_rev e

/-! ## The preferred action read off the round state, and `MonoRow` -/

/-- **§3.1's rule.**  The preferred action of `e` at a round whose forest is `F` and whose spokes are
`σ` is `find` if either endpoint has no spoke, the two spokes lead to the same portal, or `F≤p(e)`
already joins the ends.  The first two disjuncts do not mention `F`, which is why they survive every
threshold argument below. -/
def prefFind (G : WGraph V E) (σ : V → E) (F : Finset E) (e : E) : Prop :=
  ¬ incident G (G.src e) (σ (G.src e)) ∨ ¬ incident G (G.dst e) (σ (G.dst e)) ∨
    portal G σ (G.src e) = portal G σ (G.dst e) ∨
    Conn G (belowLe G F (pE G σ e)) (G.src e) (G.dst e)

/-- **The preferred action as data**: `find` when `prefFind` holds, `project` otherwise. -/
noncomputable def actOf (G : WGraph V E) (σ : V → E) (F : Finset E) (e : E) : Pref :=
  if prefFind G σ F e then Pref.find else Pref.project

theorem actOf_find {σ : V → E} {F : Finset E} {e : E} (h : prefFind G σ F e) :
    actOf G σ F e = Pref.find := by
  simp [actOf, h]

theorem actOf_project {σ : V → E} {F : Finset E} {e : E} (h : ¬ prefFind G σ F e) :
    actOf G σ F e = Pref.project := by
  simp [actOf, h]

/-- Reading the action back: `find` means one of the four clauses held. -/
theorem prefFind_of_actOf_find {σ : V → E} {F : Finset E} {e : E}
    (h : actOf G σ F e = Pref.find) : prefFind G σ F e := by
  by_cases hc : prefFind G σ F e
  · exact hc
  · rw [actOf_project hc] at h
    exact absurd h.symm (by decide)

/-- **§3.3's "the connectivity in `F` only improves as the rounds progress"**, stated for one block of
rounds at one fixed threshold: the `θ`-connection between `u` and `v` is monotone in the round. -/
def ConnImproves (G : WGraph V E) (F : Fin t → Finset E) (θ : ℝ) (u v : V) : Prop :=
  ∀ i j : Fin t, i ≤ j → Conn G (belowLe G (F i) θ) u v → Conn G (belowLe G (F j) θ) u v

/-- Growing forests improve connectivity at every threshold, so `hgrow` is what a real round state
satisfies. -/
theorem connImproves_of_grow {F : Fin t → Finset E}
    (hgrow : ∀ i j : Fin t, i ≤ j → F i ⊆ F j) :
    ConnImproves G F θ u v := by
  intro i j hij hconn
  exact hconn.mono (belowLe_subset (hgrow i j hij) θ)

/-- **§3.3's per-block monotonicity, machine-checked.**  Inside a block the spokes are frozen and the
forest only grows, so the preferred action of a fixed edge is `project` for an initial run of rounds and
`find` for the rest — the `PPPPFFF` shape of Definition 1.3.  This is the `MonoRow` assumption that
`Schedule.lean` recorded without using. -/
theorem monoRow_of_connImproves {σ : V → E} {F : Fin t → Finset E} {e : E}
    (himp : ConnImproves G F (pE G σ e) (G.src e) (G.dst e)) :
    MonoRow (fun _ i => actOf G σ (F i) e) := by
  intro b i j hij hfind
  obtain h1 | h2 | h3 | h4 := prefFind_of_actOf_find hfind
  · exact actOf_find (Or.inl h1)
  · exact actOf_find (Or.inr (Or.inl h2))
  · exact actOf_find (Or.inr (Or.inr (Or.inl h3)))
  · exact actOf_find (Or.inr (Or.inr (Or.inr (himp i j hij h4))))

/-- **The same fact in the form §3.3 quotes.**  If round `i` prefers `project` and is good, then either
`i` is the last round of its block or the *next* round prefers `project` too — because were the next
round `find`, monotonicity would make `i` the last `project` round, i.e. a bad round. -/
theorem good_project_succ {act : Fin t → Fin t → Pref} (hmono : MonoRow act) {b i : Fin t}
    (hi : (i.val + 1 : ℕ) < t) (hp : act b i = Pref.project) (hgood : ¬ bad act (b, i)) :
    act b ⟨i.val + 1, hi⟩ = Pref.project := by
  by_cases h : act b ⟨i.val + 1, hi⟩ = Pref.find
  · exact absurd (Or.inl ⟨hp, fun j hj =>
      hmono b ⟨i.val + 1, hi⟩ j
        (by have hjv : i.val < j.val := hj; show i.val + 1 ≤ j.val; omega) h⟩ : bad act (b, i)) hgood
  · exact prefProject_of_not_find h

/-- What `MonoRow` is really buying, separated out: without monotonicity a good `project` round only has
*some* later `project` round, not necessarily the next one. -/
theorem good_project_exists {act : Fin t → Fin t → Pref} {b i : Fin t}
    (hp : act b i = Pref.project) (hgood : ¬ bad act (b, i)) :
    ∃ j : Fin t, (i : ℕ) < j ∧ act b j = Pref.project := by
  by_cases hlast : ∀ j : Fin t, i < j → act b j = Pref.find
  · exact absurd (Or.inl ⟨hp, hlast⟩ : bad act (b, i)) hgood
  · rw [not_forall] at hlast
    obtain ⟨j, hj⟩ := hlast
    rw [not_imp] at hj
    exact ⟨j, hj.1, prefProject_of_not_find hj.2⟩

/-! ## Claim 3.5: the three insertion sources -/

/-- **Admissibility** (§1.2): every spoke in the projection record `rec` is no heavier than `e` —
equivalently, all projections of `e` at preceding levels were valid. -/
def Admissible (G : WGraph V E) (e : E) (rec : List E) : Prop :=
  ∀ s ∈ rec, G.weight s ≤ G.weight e

/-- A prefix of an admissible record is admissible. -/
theorem Admissible.of_append {e : E} {rec ss : List E} (h : Admissible G e (rec ++ ss)) :
    Admissible G e rec := fun s hs => h s (List.mem_append.mpr (Or.inl hs))

/-- ... and an admissible concatenation bounds the appended part — the half Claim 3.6 reads off. -/
theorem admissible_spokes_of_append {e : E} {rec ss : List E} (h : Admissible G e (rec ++ ss)) :
    ∀ s ∈ ss, G.weight s ≤ G.weight e := fun s hs => h s (List.mem_append.mpr (Or.inr hs))

/-- Admissibility composes. -/
theorem Admissible.append {e : E} {rec ss : List E} (h : Admissible G e rec)
    (hss : ∀ s ∈ ss, G.weight s ≤ G.weight e) : Admissible G e (rec ++ ss) := fun x hx =>
  (List.mem_append.mp hx).elim (h x) (hss x)

/-- **The three ways an edge enters the forest of §3.2/§3.3.**  `AdmOut G rec e` says `e` is in the
forest returned by a level whose incoming projection record is `rec`:

* `declared` — the batch declared `e` and `e` passed the admissibility test at this level;
* `rejected` — `e` is a rejected edge re-inserted at the first level where its projection became
  invalid, so the record it enters `F` with is the record *before* that projection (`hfirst` says the
  extended record really does fail — that is what "first" means);
* `lifted` — the level below returned `e`, having been given `e` with the two spokes used here appended
  to `rec`. -/
inductive AdmOut (G : WGraph V E) : List E → E → Prop where
  | declared {rec : List E} {e : E} (h : Admissible G e rec) : AdmOut G rec e
  | rejected {rec ss : List E} {e : E} (h : Admissible G e rec)
      (hfirst : ¬ Admissible G e (rec ++ ss)) : AdmOut G rec e
  | lifted {rec ss : List E} {e : E} (h : AdmOut G (rec ++ ss) e) : AdmOut G rec e

/-- **Claim 3.5, machine-checked.**  Every edge in the returned forest is admissible.  The `lifted` case
is the paper's "All the returned child forest edges are admissible by induction", and it is the only one
that needs the prefix lemma. -/
theorem admOut_admissible {rec : List E} {e : E} (h : AdmOut G rec e) : Admissible G e rec := by
  induction h with
  | @declared rec e href => exact href
  | @rejected rec ss e href _ => exact href
  | @lifted rec ss e _ ih => exact ih.of_append

/-- **The datum Claim 3.6 consumes.**  An edge admissible at the child level is admissible *including*
the two spokes used to project it here, so those spokes are no heavier than the edge: "By Claim 3.5, `f′`
is admissible, so both spokes `σ(x)` and `σ(y)` used in this lifting have weight at most `w(f)`." -/
theorem admOut_spokes {rec ss : List E} {e : E} (h : AdmOut G (rec ++ ss) e) :
    ∀ s ∈ ss, G.weight s ≤ G.weight e :=
  admissible_spokes_of_append (admOut_admissible h)

/-! ## Claim 3.6: lifting a child path back to a walk -/

/-- **A child path, read from the parent side.**  `LiftsLe G σ S θ q es r` says the list `es` of parent
edges is the lift of a child path from the portal `q` to the portal `r`: each `f` on the path joins
vertices `a`, `b` whose portals are the endpoints of the corresponding child edge, and `f` together with
the spokes `σ a`, `σ b` lies in `S` and is no heavier than `θ`.  `G.weight f ≤ θ` is "the child
recursion supports the projected edge" (with `θ = w(e)`); the spoke bounds are `admOut_spokes`; the
membership in `S` is "spokes can only arise from declared edges `D` during batch processing" and
"child forest edges ... are all incorporated into `F` via exact MSF calls". -/
inductive LiftsLe (G : WGraph V E) (σ : V → E) (S : Finset E) (θ : ℝ) :
    V → List E → V → Prop where
  | nil {q : V} : LiftsLe G σ S θ q [] q
  | step {q p r : V} {a b : V} {f : E} {es : List E}
      (hportal : portal G σ a = q ∧ portal G σ b = p ∧ joins G a b f)
      (hS : f ∈ S ∧ σ a ∈ S ∧ σ b ∈ S)
      (hw : G.weight f ≤ θ ∧ G.weight (σ a) ≤ θ ∧ G.weight (σ b) ≤ θ)
      (rest : LiftsLe G σ S θ p es r) : LiftsLe G σ S θ q (f :: es) r

/-- **The walk Claim 3.6 builds.**  Replacing each lifted child edge `f` by the three-edge walk
`σ(a), f, σ(b)` turns a child path into a walk in `G` from the first portal to the last, inside `S` and
below `θ`. -/
theorem LiftsLe.walk {S : Finset E} {θ : ℝ} {σ : V → E} {es : List E} {q r : V}
    (h : LiftsLe G σ S θ q es r) (hsp : ∀ x, incident G x (σ x)) :
    ∃ gs : List E, Path G q gs r ∧ ∀ g ∈ gs, g ∈ S ∧ G.weight g ≤ θ := by
  induction h with
  | @nil q =>
      refine ⟨[], Path.nil q, ?_⟩
      intro g hg
      simp at hg
  | @step q p r a b f es hportal hS hw _ ih =>
      obtain ⟨ha1, hap, haf⟩ := hportal
      obtain ⟨gs, hpath, hmem⟩ := ih
      have h1 : Path G q [σ a] a := by
        have hj : joins G a (portal G σ a) (σ a) := joins_portal (hsp a)
        rw [ha1] at hj
        exact Path.of_joins hj.symm
      have h2 : Path G a [f] b := Path.of_joins haf
      have h3 : Path G b [σ b] p := by
        have hj : joins G b (portal G σ b) (σ b) := joins_portal (hsp b)
        rw [hap] at hj
        exact Path.of_joins hj
      refine ⟨σ a :: f :: σ b :: gs, ?_, ?_⟩
      · have hcat : (([σ a] ++ [f]) ++ [σ b]) ++ gs = σ a :: f :: σ b :: gs := by simp
        exact hcat ▸ (((h1.append [f] b h2).append [σ b] p h3).append gs r hpath)
      · intro g hg
        simp only [List.mem_cons] at hg
        rcases hg with rfl | rfl | rfl | hg
        · exact ⟨hS.2.1, hw.2.1⟩
        · exact ⟨hS.1, hw.1⟩
        · exact ⟨hS.2.2, hw.2.2⟩
        · exact hmem g hg

/-- **Spokes meeting at a portal.**  If `π(u) = π(v)` then the two spokes alone join `u` to `v` at
threshold `max{w(σ u), w(σ v)}` — §3.3's "the two spokes meet at a common portal, so `F≤p(e′)` connects
`u′` and `v′`". -/
theorem conn_portal_eq {S : Finset E} {σ : V → E} {u v : V}
    (heq : portal G σ u = portal G σ v) (hspu : incident G u (σ u)) (hspv : incident G v (σ v))
    (hus : σ u ∈ S) (hvs : σ v ∈ S) {θ : ℝ} (hθ : pmax G σ u v ≤ θ) :
    Conn G (belowLe G S θ) u v := by
  have h1 : Conn G (belowLe G S θ) u (portal G σ u) :=
    conn_of_joins (joins_portal hspu) (belowLe_mem.mpr ⟨hus, le_trans (le_max_left _ _) hθ⟩)
  have h2 : Conn G (belowLe G S θ) (portal G σ v) v :=
    conn_of_joins (joins_portal hspv).symm (belowLe_mem.mpr ⟨hvs, le_trans (le_max_right _ _) hθ⟩)
  rw [heq.symm] at h2
  exact h1.trans h2

/-- **Claim 3.6, machine-checked.**  Let the child recursion support the projected edge: a path in the
child from `π(u)` to `π(v)` by edges no heavier than `e`, which from the parent side is a `LiftsLe` chain
at threshold `w(e)`.  Then the forest `F₁ = MSF(G[S])` that this level keeps connects `u` and `v` at
threshold `max{w(e), p(e)}`.  The extra `max` is for the two spokes `σ(u)`, `σ(v)`, which are bounded by
`p(e)` and not by `w(e)`; everything on the lifted path is bounded by `w(e)`. -/
theorem claim_3_6 {S F₁ : Finset E} {σ : V → E} {e : E} {es : List E}
    (hT : IsMSFOf G S F₁) (hsp : ∀ x, incident G x (σ x))
    (hchain : LiftsLe G σ S (G.weight e) (portal G σ (G.src e)) es (portal G σ (G.dst e)))
    (hσS : ∀ x, σ x ∈ S) :
    Conn G (belowLe G F₁ (max (G.weight e) (pE G σ e))) (G.src e) (G.dst e) := by
  obtain ⟨gs, hpath, hmem⟩ := hchain.walk hsp
  have hfull : Path G (G.src e) (σ (G.src e) :: gs ++ [σ (G.dst e)]) (G.dst e) := by
    have h1 : Path G (G.src e) [σ (G.src e)] (portal G σ (G.src e)) :=
      Path.of_joins (joins_portal (hsp (G.src e)))
    have h3 : Path G (portal G σ (G.dst e)) [σ (G.dst e)] (G.dst e) :=
      Path.of_joins (joins_portal (hsp (G.dst e))).symm
    have hcat : ([σ (G.src e)] ++ gs) ++ [σ (G.dst e)] = σ (G.src e) :: gs ++ [σ (G.dst e)] := by
      simp
    exact hcat ▸ ((h1.append gs _ hpath).append _ _ h3)
  have hmem2 : ∀ g ∈ σ (G.src e) :: gs ++ [σ (G.dst e)],
      g ∈ S ∧ G.weight g ≤ max (G.weight e) (pE G σ e) := by
    intro g hg
    simp only [List.mem_cons, List.mem_append] at hg
    rcases hg with (rfl | hg) | (rfl | hg)
    · exact ⟨hσS _, le_trans le_pE_left (le_max_right _ _)⟩
    · exact ⟨(hmem g hg).1, (hmem g hg).2.trans (le_max_left _ _)⟩
    · exact ⟨hσS _, le_trans le_pE_right (le_max_right _ _)⟩
    · exact absurd hg (by simp)
  refine IsMSFOf.below_span hT (conn_of_path hfull ?_)
  intro g hg
  exact belowLe_mem.mpr (hmem2 g hg)

/-- **The form Lemma 3.7 uses.**  A *valid* projection — one with `p(e) ≤ w(e)` — turns Claim 3.6 into
plain support. -/
theorem claim_3_6_supported {S F₁ : Finset E} {σ : V → E} {e : E} {es : List E}
    (hT : IsMSFOf G S F₁) (hsp : ∀ x, incident G x (σ x))
    (hchain : LiftsLe G σ S (G.weight e) (portal G σ (G.src e)) es (portal G σ (G.dst e)))
    (hσS : ∀ x, σ x ∈ S) (hp : pE G σ e ≤ G.weight e) : supported G F₁ e := by
  show Conn G (belowLe G F₁ (G.weight e)) (G.src e) (G.dst e)
  refine conn_belowLe_mono F₁ (max (G.weight e) (pE G σ e)) (G.weight e)
    (max_le_iff.mpr ⟨le_refl _, hp⟩) ?_
  exact claim_3_6 hT hsp hchain hσS

/-! ## Lemma 3.7 -/

/-- **§3.3's notion of an error**: either the round assigned to the edge is bad for it, or the estimate
the algorithm used differs from the true preferred action there. -/
def error (act : Fin t → Fin t → Pref) (est : Fin t × Fin t → Pref) (p : Fin t × Fin t) : Prop :=
  bad act p ∨ est p ≠ act p.1 p.2

/-- **Lemma 3.7, the deepest level.**  The projection living at the last level prefers `find`, so the
batch processes it and Lemma 3.2 gives either support already or `p(e) ≤ w(e)`.  In the second case the
assigned round is a *good find* round, so a later block prefers `find` again; there either the portals
coincide — and `conn_portal_eq` turns the two spokes into a `≤p(e)` walk — or `F≤p(e)` connects.  Since
`p` can only decrease, both give the connection at the old threshold, and the final forest supports `e`. -/
theorem lemma37_last {F₁ : Finset E} {σ σ' : V → E} {e : E}
    (hsp : ∀ x, incident G x (σ' x)) (hσsub : ∀ x, σ' x ∈ F₁)
    (hpmono : pE G σ' e ≤ pE G σ e)
    (hbatch : Conn G (belowLe G F₁ (G.weight e)) (G.src e) (G.dst e) ∨
      pE G σ e ≤ G.weight e)
    (hlater : pE G σ e ≤ G.weight e →
      Conn G (belowLe G F₁ (pE G σ' e)) (G.src e) (G.dst e) ∨
        portal G σ' (G.src e) = portal G σ' (G.dst e)) :
    supported G F₁ e := by
  show Conn G (belowLe G F₁ (G.weight e)) (G.src e) (G.dst e)
  rcases hbatch with h | h
  · exact h
  · obtain h1 | h2 := hlater h
    · exact conn_belowLe_mono F₁ (pE G σ' e) (G.weight e) (le_trans hpmono h) h1
    · exact conn_portal_eq h2 (hsp _) (hsp _) (hσsub _) (hσsub _) (le_trans hpmono h)

/-- **Lemma 3.7, the project case.**  At a level where the tracked projection is projected on, Claim 3.6
gives a connection at threshold `max{w(e), p(e)}` inside the forest `Fre` obtained on return.  Rounds
after the assigned one start from a forest that already contains `Fre`, and the spokes are frozen inside
the block, so from the next round on the true preference is `find`.  Were the assigned round good, it
would follow every later round with `find` — a bad round — a contradiction.  Hence `p(e) ≤ w(e)`, i.e.
the projection was valid, and `e` is supported. -/
theorem lemma37_project_step {F₁ Fre : Finset E} {σ : V → E} {F : Fin t → Finset E}
    {e : E} {b r : Fin t} (act : Fin t → Fin t → Pref)
    (hact : ∀ j, act b j = actOf G σ (F j) e)
    (hpref : ¬ prefFind G σ (F r) e)
    (hgood : ¬ bad act (b, r))
    (hret : ∀ j : Fin t, (r.val + 1 : ℕ) ≤ j.val → Fre ⊆ F j)
    (hsub : Fre ⊆ F₁)
    (hconn : Conn G (belowLe G Fre (max (G.weight e) (pE G σ e))) (G.src e) (G.dst e)) :
    supported G F₁ e := by
  by_cases hp : pE G σ e ≤ G.weight e
  · show Conn G (belowLe G F₁ (G.weight e)) (G.src e) (G.dst e)
    refine conn_belowLe_mono F₁ (max (G.weight e) (pE G σ e)) (G.weight e)
      (max_le_iff.mpr ⟨le_refl _, hp⟩) ?_
    exact hconn.mono (belowLe_subset hsub _)
  · have hlt : G.weight e < pE G σ e := lt_of_not_ge hp
    rw [max_eq_right (le_of_lt hlt)] at hconn
    have hfind : ∀ j : Fin t, (r : ℕ) < j → act b j = Pref.find := by
      intro j hj
      rw [hact]
      refine actOf_find (Or.inr (Or.inr (Or.inr ?_)))
      exact hconn.mono (belowLe_subset (hret j (by
        have hjv : r.val < j.val := hj
        show (r.val + 1 : ℕ) ≤ j.val
        omega)) _)
    exact absurd (Or.inl ⟨(hact r).trans (actOf_project hpref), hfind⟩ : bad act (b, r)) hgood

/-- **Lemma 3.7's last sentence.**  A rejected edge is projected at a level where `p(e) > w(e)`; on
return its edges are incorporated and `F≤p(e)` joins the ends, and since the spokes are frozen inside the
block, every later round of that block prefers `find`.  So either the assigned round really was bad or the
estimate was wrong — in both cases an error occurs at this level. -/
theorem lemma37_rejected_error {act : Fin t → Fin t → Pref} {est : Fin t × Fin t → Pref}
    {b r : Fin t} (hproj : est (b, r) = Pref.project)
    (htrue : ∀ j : Fin t, (r.val + 1 : ℕ) ≤ j.val → act b j = Pref.find) :
    error (act := act) est (b, r) := by
  by_cases h : est (b, r) = act b r
  · exact Or.inl (Or.inl ⟨h.symm.trans hproj,
      fun j hj => htrue j (by
        have hjv : r.val < j.val := hj
        show (r.val + 1 : ℕ) ≤ j.val
        omega)⟩)
  · exact Or.inr h

/-- **One level of the recursion as one edge sees it**: `e` is the projection of the tracked edge living
at that level and `F` the forest the level returns. -/
structure Lev (E : Type*) where
  e : E
  F : Finset E

/-- `Lev.supp G ℓ`: the forest returned by this level supports the projection living at it. -/
def Lev.supp (G : WGraph V E) (ℓ : Lev E) : Prop := supported G ℓ.F ℓ.e

/-- **Lemma 3.7, machine-checked (the backward induction).**  `lev j` is the recursion level at depth
`j`, so `lev 0` is the root instance and its edge is the tracked edge itself; past depth `d` the edge is
never passed down again, i.e. its preferred action is `find`.  `hfind` is the deepest-level argument
(`lemma37_last`), `hproject` the per-level step (`lemma37_project_step`).  Then the root forest supports
`e`.  The paper's "we prove by backward induction on the recursion level" is this lemma; the reason a
`ℕ`-indexed chain loses nothing is that an edge is projected into *exactly one* child instance. -/
theorem lemma37 {lev : ℕ → Lev E} {d : ℕ}
    (hfind : ∀ j : ℕ, d ≤ j → Lev.supp G (lev j))
    (hproject : ∀ j : ℕ, j < d → Lev.supp G (lev (j + 1)) → Lev.supp G (lev j)) :
    Lev.supp G (lev 0) := by
  have key : ∀ n : ℕ, ∀ k : ℕ, k + n = d → Lev.supp G (lev k) := by
    intro n
    induction n with
    | zero => intro k hk; exact hfind k (by omega)
    | succ n ih =>
        intro k hk
        exact hproject k (by omega) (ih (k + 1) (by omega))
  exact key d 0 (by omega)

end DLMST