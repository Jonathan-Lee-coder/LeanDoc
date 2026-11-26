import DLMST.Candidates
import DLMST.PrefTrail
import DLMST.ForestCard

/-!
# §3.5's geometric `S_e`, the decoding rule, and `truth ∈ A`

§3.5 attaches to every edge `e` of a round the set `S_e = {σ(u), σ(v)} ∪ (the u–v path in F)` and
declares `e`'s preference to be `find` iff the heaviest element of `S_e` (on the *spoke-first* order
`rOf`) is one of the two spokes.  This file assembles that geometry and machine-checks the rule:

* `spokePair`, `bothSpokes`, `distinctPortals`, `pathSet` (the edges of an `F`-trail from `src e` to
  `dst e`), `sSet = spokePair ∪ pathSet`, and the decoder `geoPref`;
* `actOf_eq_geoPref` — **the rule, in order-generic form**: for any `κ : E → ℕ` that refines the
  weight order and puts a spoke above a non-spoke of equal weight, if `b` is a `κ`-maximum of `S_e`
  then the true action of `e` is `geoPref b e`.  The hypothesis `hFsp` — forest edges are not
  spokes — is what lets the tie-break separate the two cases (it is *not* implied by `IsForest`);
* `actOf_eq_geoPref_keyOf` — the rule instantiated at `κ = keyOf eN (rOf weight spk)`;
* the fibre packaging: `groundSet = image σ ∪ F` (at most `2n` edges), the lifted sets `roundS` /
  `roundSp` on the subtype `Ground`, `roundCand` (the `Pref`-vector family decoded from the argmax
  family over `Ground`), `truth_mem_roundCand` (**the true preference vector is in `A`**), and the
  count `log |A| ≤ 4√(2nm)`.

Not formalised here: the recursion that supplies `σ`, `F` and the `IsForest`/`hFsp` facts at each
level, and the per-call instantiation of `n` and `m` for `cost_linear_of_nodes`.
-/

namespace DLMST

open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

/-! ## The per-edge geometry -/

/-- `x` is a spoke edge: the edge `σ u` of some vertex. -/
def IsSpoke (σ : V → E) (x : E) : Prop := ∃ u : V, σ u = x

/-- **`{σ(u), σ(v)}`**: the two spokes of `e`'s endpoints (§3.5's two always-relevant candidates). -/
noncomputable def spokePair (G : WGraph V E) (σ : V → E) (e : E) : Finset E :=
  {σ (G.src e), σ (G.dst e)}

theorem mem_spokePair_src (G : WGraph V E) (σ : V → E) (e : E) :
    σ (G.src e) ∈ spokePair G σ e :=
  Finset.mem_insert_self _ _

theorem mem_spokePair_dst (G : WGraph V E) (σ : V → E) (e : E) :
    σ (G.dst e) ∈ spokePair G σ e :=
  Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

theorem isSpoke_of_mem_spokePair {σ : V → E} {e : E} {x : E}
    (h : x ∈ spokePair G σ e) : IsSpoke σ x := by
  rcases Finset.mem_insert.mp h with h | h
  · exact ⟨_, h.symm⟩
  · exact ⟨_, (Finset.mem_singleton.mp h).symm⟩

/-- Both ends of `e` have a genuine spoke (the negation of `prefFind`'s first two disjuncts). -/
def bothSpokes (G : WGraph V E) (σ : V → E) (e : E) : Prop :=
  incident G (G.src e) (σ (G.src e)) ∧ incident G (G.dst e) (σ (G.dst e))

/-- The two spokes lead to different portals (the negation of `prefFind`'s third disjunct). -/
def distinctPortals (G : WGraph V E) (σ : V → E) (e : E) : Prop :=
  portal G σ (G.src e) ≠ portal G σ (G.dst e)

/-- **The `src e–dst e` path in `F`**, as a set of edges: the edges of `F` lying on some
backtrack-free `F`-trail between the ends of `e`.  Inside a forest this is (the edge set of) *the*
trail, by `IsForest.trail_eq`; defining it without choice keeps the membership facts syntactic. -/
noncomputable def pathSet (G : WGraph V E) (F : Finset E) (e : E) : Finset E := by
  classical
  exact F.filter fun g => ∃ es : List E, Path G (G.src e) es (G.dst e) ∧
    (∀ g' ∈ es, g' ∈ F) ∧ consecFree es ∧ g ∈ es

theorem mem_pathSet {F : Finset E} {e g : E} :
    g ∈ pathSet G F e ↔ g ∈ F ∧ ∃ es : List E, Path G (G.src e) es (G.dst e) ∧
      (∀ g' ∈ es, g' ∈ F) ∧ consecFree es ∧ g ∈ es :=
  Finset.mem_filter

theorem pathSet_sub (F : Finset E) (e : E) : pathSet G F e ⊆ F :=
  Finset.filter_subset _ _

theorem mem_pathSet_of_trail {F : Finset E} {e : E} {es : List E}
    (hp : Path G (G.src e) es (G.dst e)) (hsub : ∀ g ∈ es, g ∈ F) (hcf : consecFree es)
    {g : E} (hg : g ∈ es) : g ∈ pathSet G F e :=
  mem_pathSet.mpr ⟨hsub g hg, es, hp, hsub, hcf, hg⟩

/-- **`S_e`**: the two spokes together with the connecting `F`-path. -/
noncomputable def sSet (G : WGraph V E) (σ : V → E) (F : Finset E) (e : E) : Finset E :=
  spokePair G σ e ∪ pathSet G F e

theorem spokePair_sub_sSet (σ : V → E) (F : Finset E) (e : E) :
    spokePair G σ e ⊆ sSet G σ F e :=
  Finset.subset_union_left

theorem pathSet_sub_sSet (σ : V → E) (F : Finset E) (e : E) :
    pathSet G F e ⊆ sSet G σ F e :=
  Finset.subset_union_right

theorem sSet_nonempty (σ : V → E) (F : Finset E) (e : E) : (sSet G σ F e).Nonempty :=
  ⟨_, spokePair_sub_sSet σ F e (mem_spokePair_src G σ e)⟩

/-- **§3.5's decoding rule as a function of the candidate `b`.**  When both spokes exist and lead to
different portals, the preference is the connectivity of `F≤p(e)` *and* `b` being a spoke;
otherwise it is `find` unless the pair is connected and `b` is a forest edge. -/
noncomputable def geoPref (G : WGraph V E) (σ : V → E) (F : Finset E) (b e : E) : Pref := by
  classical
  exact
    if bothSpokes G σ e ∧ distinctPortals G σ e then
      (if Conn G (belowLe G F (pE G σ e)) (G.src e) (G.dst e) then
        (if b ∈ spokePair G σ e then Pref.find else Pref.project)
      else Pref.project)
    else Pref.find

/-- Under "both ends have spokes and the portals differ", `prefFind` is exactly the connectivity
clause. -/
theorem prefFind_iff_conn_of_bothSpokes {σ : V → E} {F : Finset E} {e : E}
    (h1 : incident G (G.src e) (σ (G.src e))) (h2 : incident G (G.dst e) (σ (G.dst e)))
    (h3 : portal G σ (G.src e) ≠ portal G σ (G.dst e)) :
    prefFind G σ F e ↔ Conn G (belowLe G F (pE G σ e)) (G.src e) (G.dst e) := by
  constructor
  · intro h
    rcases h with h' | h' | h' | h'
    · exact absurd h1 h'
    · exact absurd h2 h'
    · exact absurd h' h3
    · exact h'
  · intro h
    exact Or.inr (Or.inr (Or.inr h))

/-- If some `F`-free disjunct of `prefFind` holds, the action is `find` whatever the geometry. -/
theorem prefFind_of_not_case {σ : V → E} {F : Finset E} {e : E}
    (h : ¬ (bothSpokes G σ e ∧ distinctPortals G σ e)) : prefFind G σ F e := by
  rcases not_and_or.mp h with h | h
  · rcases not_and_or.mp h with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl (not_not.mp h)))

/-! ## The decoding theorem -/

/-- **§3.5's rule, order-generic.**  Let `κ` refine the weight order (`hP1`) and rank a spoke above
a non-spoke of equal weight (`hP2`).  If `b` is a `κ`-maximum of `S_e` and the forest has no spoke
edges (`hFsp`), then `e`'s true action is `geoPref b e`.

The proof is the paper's case analysis: outside "both spokes, distinct portals" the rule is `find`
by definition; inside it, if `F≤p(e)` connects the ends then every path edge weighs at most `p(e)`
(`PrefTrail.prefFind_iff_trail_weight`), so a `κ`-maximum is a spoke exactly when `find` holds — the
tie-break `hP2` being what rules out a forest edge tying a spoke. -/
theorem actOf_eq_geoPref (hF : IsForest G F) {σ : V → E} {e b : E}
    (hFsp : ∀ g ∈ F, ¬ IsSpoke σ g)
    (κ : E → ℕ)
    (hP1 : ∀ y ∈ sSet G σ F e, ∀ x ∈ sSet G σ F e, G.weight y < G.weight x → κ y < κ x)
    (hP2 : ∀ y ∈ sSet G σ F e, ∀ x ∈ sSet G σ F e, G.weight y = G.weight x →
      ¬ IsSpoke σ y → IsSpoke σ x → κ y < κ x)
    (hbs : b ∈ sSet G σ F e) (hmax : ∀ y ∈ sSet G σ F e, κ y ≤ κ b) :
    actOf G σ F e = geoPref G σ F b e := by
  classical
  have hpem : pE G σ e = max (G.weight (σ (G.src e))) (G.weight (σ (G.dst e))) := rfl
  by_cases hcase : bothSpokes G σ e ∧ distinctPortals G σ e
  · have hsp : bothSpokes G σ e := hcase.1
    have hpne : distinctPortals G σ e := hcase.2
    have hiff := prefFind_iff_conn_of_bothSpokes (F := F) hsp.1 hsp.2 hpne
    by_cases hconn : Conn G (belowLe G F (pE G σ e)) (G.src e) (G.dst e)
    · by_cases hb : b ∈ spokePair G σ e
      · rw [actOf_find (hiff.mpr hconn)]
        unfold geoPref
        rw [if_pos hcase, if_pos hconn, if_pos hb]
      · have hbSmem : b ∈ sSet G σ F e := Finset.mem_union_right _ (by
          rcases Finset.mem_union.mp hbs with h | h
          · exact absurd h hb
          · exact h)
        obtain ⟨hbF, es1, pes1, hes1F, hcf1, hb1⟩ :=
          mem_pathSet.mp (Finset.mem_union.mp hbs |>.resolve_left hb)
        obtain ⟨es0, pes0, hsub0⟩ := path_of_conn hconn
        have hsubF : ∀ g ∈ es0, g ∈ F := fun g hg => Finset.filter_subset _ _ (hsub0 g hg)
        obtain ⟨es, pes, hesF, hcf⟩ := hF.exists_consecFree_trail es0 pes0 hsubF
        have heq : es1 = es := hF.trail_eq es1 es _ _ pes1 pes hes1F hesF hcf1 hcf
        rw [heq] at hb1
        have hnot : ¬ prefFind G σ F e := by
          intro hfind
          have hall : ∀ g ∈ es, G.weight g ≤ pE G σ e :=
            (prefFind_iff_trail_weight hF hsp hpne pes hesF hcf).mp hfind
          have hwb : G.weight b ≤ max (G.weight (σ (G.src e))) (G.weight (σ (G.dst e))) := by
            rw [← hpem]
            exact hall b hb1
          rcases le_max_iff.mp hwb with h1 | h1
          · have hmem : σ (G.src e) ∈ sSet G σ F e :=
              Finset.mem_union_left _ (mem_spokePair_src G σ e)
            have hle : κ (σ (G.src e)) ≤ κ b := hmax _ hmem
            rcases lt_or_eq_of_le h1 with hlt | heqw
            · exact absurd (hP1 b hbSmem _ hmem hlt) (not_lt.mpr hle)
            · exact absurd (hP2 b hbSmem _ hmem heqw (hFsp b hbF) ⟨_, rfl⟩) (not_lt.mpr hle)
          · have hmem : σ (G.dst e) ∈ sSet G σ F e :=
              Finset.mem_union_left _ (mem_spokePair_dst G σ e)
            have hle : κ (σ (G.dst e)) ≤ κ b := hmax _ hmem
            rcases lt_or_eq_of_le h1 with hlt | heqw
            · exact absurd (hP1 b hbSmem _ hmem hlt) (not_lt.mpr hle)
            · exact absurd (hP2 b hbSmem _ hmem heqw (hFsp b hbF) ⟨_, rfl⟩) (not_lt.mpr hle)
        rw [actOf_project hnot]
        unfold geoPref
        rw [if_pos hcase, if_pos hconn, if_neg hb]
    · have hnot : ¬ prefFind G σ F e := fun h => hconn (hiff.mp h)
      rw [actOf_project hnot]
      unfold geoPref
      rw [if_pos hcase, if_neg hconn]
  · rw [actOf_find (prefFind_of_not_case hcase)]
    unfold geoPref
    rw [if_neg hcase]

/-- The spoke edges of the whole instance. -/
noncomputable def spkE (G : WGraph V E) (σ : V → E) : Finset E :=
  Finset.univ.filter (IsSpoke σ)

theorem mem_spkE {σ : V → E} {x : E} : x ∈ spkE G σ ↔ IsSpoke σ x := by
  simp [spkE]

/-- **The decoding rule at the paper's tie-break order** `κ = keyOf eN (rOf weight spk)`: the
`rOf`-maximum of `S_e` determines `e`'s action. -/
theorem actOf_eq_geoPref_keyOf (hF : IsForest G F) {σ : V → E} {e b : E}
    (hFsp : ∀ g ∈ F, ¬ IsSpoke σ g) (eN : E ≃ Fin (Fintype.card E))
    (hbs : b ∈ sSet G σ F e)
    (hmax : ∀ y ∈ sSet G σ F e,
      keyOf eN (rOf G.weight (spkE G σ)) y ≤ keyOf eN (rOf G.weight (spkE G σ)) b) :
    actOf G σ F e = geoPref G σ F b e := by
  refine actOf_eq_geoPref (F := F) hF hFsp (κ := keyOf eN (rOf G.weight (spkE G σ))) ?_ ?_ hbs hmax
  · intro y _ x _ hlt
    exact keyOf_lt_of_lt eN hlt
  · intro y _ x _ heqw hny hxsp
    exact keyOf_lt_of_eq_notMem_mem eN heqw (fun h => hny (mem_spkE.mp h)) (mem_spkE.mpr hxsp)

/-! ## The fibre: the family `A` as argmax vectors over `image σ ∪ F` -/

/-- **The ground set** `image σ ∪ F`: every edge that can appear in some `S_e`, and at most `2n` of
them (Lemma 3.10's `m + 2n` split, with `|image σ| ≤ n` and `|F| ≤ n`). -/
noncomputable def groundSet (G : WGraph V E) (σ : V → E) (F : Finset E) : Finset E :=
  Finset.univ.image σ ∪ F

theorem mem_groundSet_spoke {σ : V → E} {F : Finset E} (u : V) : σ u ∈ groundSet G σ F :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩)

/-- The ground type of the fibre. -/
abbrev Ground (G : WGraph V E) (σ : V → E) (F : Finset E) : Type _ :=
  {x : E // x ∈ groundSet G σ F}

theorem sSet_sub_groundSet (σ : V → E) (F : Finset E) (e : E) :
    sSet G σ F e ⊆ groundSet G σ F := by
  intro g hg
  rcases Finset.mem_union.mp hg with h | h
  · rcases Finset.mem_insert.mp h with h | h
    · rw [h]; exact mem_groundSet_spoke (G := G) (σ := σ) (F := F) _
    · rw [Finset.mem_singleton.mp h]; exact mem_groundSet_spoke (G := G) (σ := σ) (F := F) _
  · exact Finset.mem_union_right _ (pathSet_sub (G := G) F e h)

theorem groundSet_card_le (σ : V → E) (F : Finset E) (hF : IsForest G F) :
    (groundSet G σ F).card ≤ 2 * Fintype.card V := by
  have h1 : (Finset.univ.image σ).card ≤ Fintype.card V := by
    have h := Finset.card_image_le (s := (Finset.univ : Finset V)) (f := σ)
    rwa [Finset.card_univ] at h
  have h2 : F.card ≤ Fintype.card V := card_le_card_of_isForest hF
  calc (groundSet G σ F).card ≤ (Finset.univ.image σ).card + F.card := Finset.card_union_le _ _
    _ ≤ Fintype.card V + Fintype.card V := Nat.add_le_add h1 h2
    _ = 2 * Fintype.card V := by omega

theorem card_Ground_le (σ : V → E) (F : Finset E) (hF : IsForest G F) :
    Fintype.card (Ground G σ F) ≤ 2 * Fintype.card V := by
  calc Fintype.card (Ground G σ F) = (groundSet G σ F).card := by
        rw [← Finset.card_univ, Finset.univ_eq_attach, Finset.card_attach]
    _ ≤ 2 * Fintype.card V := groundSet_card_le σ F hF

/-- The spokes, as a subset of the ground type. -/
noncomputable def spkT (G : WGraph V E) (σ : V → E) (F : Finset E) :
    Finset (Ground G σ F) :=
  (groundSet G σ F).attach.filter (fun z => IsSpoke σ z.1)

theorem mem_spkT {σ : V → E} {F : Finset E} {z : Ground G σ F} :
    z ∈ spkT G σ F ↔ IsSpoke σ z.1 := by
  simp [spkT]

/-- The tie-break key on the ground type. -/
noncomputable def fibreKey (G : WGraph V E) (σ : V → E) (F : Finset E)
    (eN : Ground G σ F ≃ Fin (Fintype.card (Ground G σ F))) : Ground G σ F → ℕ :=
  keyOf eN (rOf (fun z : Ground G σ F => G.weight z.1) (spkT G σ F))

/-- The same key read on `E` (default `0` off the ground set). -/
noncomputable def keyOnE (G : WGraph V E) (σ : V → E) (F : Finset E)
    (eN : Ground G σ F ≃ Fin (Fintype.card (Ground G σ F))) (x : E) : ℕ :=
  if h : x ∈ groundSet G σ F then fibreKey G σ F eN ⟨x, h⟩ else 0

theorem keyOnE_of_mem {σ : V → E} {F : Finset E}
    {eN : Ground G σ F ≃ Fin (Fintype.card (Ground G σ F))} {x : E}
    (hx : x ∈ groundSet G σ F) : keyOnE G σ F eN x = fibreKey G σ F eN ⟨x, hx⟩ := by
  simp only [keyOnE, dif_pos hx]

theorem keyOnE_lt_of_lt {σ : V → E} {F : Finset E} {e : E}
    {eN : Ground G σ F ≃ Fin (Fintype.card (Ground G σ F))} {y x : E}
    (hy : y ∈ sSet G σ F e) (hx : x ∈ sSet G σ F e) (h : G.weight y < G.weight x) :
    keyOnE G σ F eN y < keyOnE G σ F eN x := by
  rw [keyOnE_of_mem (sSet_sub_groundSet σ F e hy), keyOnE_of_mem (sSet_sub_groundSet σ F e hx)]
  exact keyOf_lt_of_lt eN h

theorem keyOnE_lt_of_eq {σ : V → E} {F : Finset E} {e : E}
    {eN : Ground G σ F ≃ Fin (Fintype.card (Ground G σ F))} {y x : E}
    (hy : y ∈ sSet G σ F e) (hx : x ∈ sSet G σ F e) (heq : G.weight y = G.weight x)
    (hny : ¬ IsSpoke σ y) (hxsp : IsSpoke σ x) :
    keyOnE G σ F eN y < keyOnE G σ F eN x := by
  rw [keyOnE_of_mem (sSet_sub_groundSet σ F e hy), keyOnE_of_mem (sSet_sub_groundSet σ F e hx)]
  exact keyOf_lt_of_eq_notMem_mem eN heq (fun h => hny (mem_spkT.mp h)) (mem_spkT.mpr hxsp)

section Fibre

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`S_e` lifted to the ground type**, for each round edge `i`. -/
noncomputable def roundS (σ : V → E) (F : Finset E) (ιE : ι → E) :
    ι → Finset (Ground G σ F) :=
  fun i => (sSet G σ F (ιE i)).attach.image
    (fun g => ⟨g.1, sSet_sub_groundSet σ F (ιE i) g.2⟩)

theorem mem_roundS {σ : V → E} {F : Finset E} {ιE : ι → E} {i : ι} {z : Ground G σ F} :
    z ∈ roundS (G := G) σ F ιE i ↔ z.1 ∈ sSet G σ F (ιE i) := by
  constructor
  · intro hz
    obtain ⟨a, -, hae⟩ := Finset.mem_image.mp hz
    rw [← hae]
    exact a.2
  · intro hz
    exact Finset.mem_image.mpr ⟨⟨z.1, hz⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩

theorem roundS_nonempty (σ : V → E) (F : Finset E) (ιE : ι → E) (i : ι) :
    (roundS (G := G) σ F ιE i).Nonempty := by
  obtain ⟨g, hg⟩ := sSet_nonempty (G := G) σ F (ιE i)
  exact ⟨⟨g, sSet_sub_groundSet σ F (ιE i) hg⟩, mem_roundS.mpr hg⟩

/-- The two spokes of `e`, lifted to the ground type. -/
noncomputable def roundSp (σ : V → E) (F : Finset E) (ιE : ι → E) :
    ι → Finset (Ground G σ F) :=
  fun i => (spokePair G σ (ιE i)).attach.image
    (fun g => ⟨g.1, sSet_sub_groundSet σ F (ιE i) (spokePair_sub_sSet σ F (ιE i) g.2)⟩)

theorem roundSp_sub_roundS (σ : V → E) (F : Finset E) (ιE : ι → E) (i : ι) :
    roundSp (G := G) σ F ιE i ⊆ roundS (G := G) σ F ιE i := by
  intro z hz
  rw [mem_roundS]
  obtain ⟨a, -, hae⟩ := Finset.mem_image.mp hz
  rw [← hae]
  exact spokePair_sub_sSet σ F (ιE i) a.2

theorem roundSp_nonempty (σ : V → E) (F : Finset E) (ιE : ι → E) (i : ι) :
    (roundSp (G := G) σ F ιE i).Nonempty := by
  refine ⟨⟨σ (G.src (ιE i)), sSet_sub_groundSet σ F (ιE i)
    (spokePair_sub_sSet σ F (ιE i) (mem_spokePair_src G σ (ιE i)))⟩, ?_⟩
  exact Finset.mem_image.mpr ⟨⟨_, mem_spokePair_src G σ (ιE i)⟩, Finset.mem_attach _ _,
    Subtype.ext rfl⟩

/-- **`A`**: the `Pref`-vectors decoded from the argmax vectors over the ground type. -/
noncomputable def roundCand (σ : V → E) (F : Finset E) (ιE : ι → E)
    (eN : Ground G σ F ≃ Fin (Fintype.card (Ground G σ F))) : Finset (ι → Pref) :=
  (argmaxFamily (roundS (G := G) σ F ιE) eN).image
    (fun b i => geoPref G σ F (b i).1 (ιE i))

/-- **`truth ∈ A`**: the true preference vector of a round is realised by the `rOf`-argmax vector of
`(S_e)`, hence lies in the decoded family. -/
theorem truth_mem_roundCand (hF : IsForest G F) {σ : V → E}
    (hFsp : ∀ g ∈ F, ¬ IsSpoke σ g) (ιE : ι → E)
    (eN : Ground G σ F ≃ Fin (Fintype.card (Ground G σ F))) :
    (fun i => actOf G σ F (ιE i)) ∈ roundCand (G := G) σ F ιE eN := by
  classical
  have hkey : ∀ i, ∃ x ∈ roundS (G := G) σ F ιE i,
      ∀ y ∈ roundS (G := G) σ F ιE i,
        fibreKey G σ F eN y ≤ fibreKey G σ F eN x :=
    fun i => Finset.exists_max_image _ _ (roundS_nonempty σ F ιE i)
  choose a ha using hkey
  have hfam : a ∈ argmaxFamily (roundS (G := G) σ F ιE) eN :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      rOf (fun z : Ground G σ F => G.weight z.1) (spkT G σ F), fun i => ha i⟩
  refine Finset.mem_image.mpr ⟨a, hfam, ?_⟩
  funext i
  have hbS : (a i).1 ∈ sSet G σ F (ιE i) := mem_roundS.mp (ha i).1
  have hmax : ∀ y ∈ sSet G σ F (ιE i),
      keyOnE G σ F eN y ≤ keyOnE G σ F eN (a i).1 := by
    intro y hy
    have hyR : (⟨y, sSet_sub_groundSet σ F (ιE i) hy⟩ : Ground G σ F) ∈
        roundS (G := G) σ F ιE i := mem_roundS.mpr hy
    have h1 : fibreKey G σ F eN ⟨y, sSet_sub_groundSet σ F (ιE i) hy⟩ ≤ fibreKey G σ F eN (a i) :=
      (ha i).2 _ hyR
    rw [keyOnE_of_mem (sSet_sub_groundSet σ F (ιE i) hy),
      keyOnE_of_mem (sSet_sub_groundSet σ F (ιE i) hbS)]
    exact h1
  exact (actOf_eq_geoPref (F := F) hF hFsp (κ := keyOnE G σ F eN)
    (fun y hy x hx hlt => keyOnE_lt_of_lt hy hx hlt)
    (fun y hy x hx heqw hny hxsp => keyOnE_lt_of_eq hy hx heqw hny hxsp)
    hbS hmax).symm

/-- **`|A| ≤ C(2n + m - 1, m)`.** -/
theorem roundCand_card_le (σ : V → E) (F : Finset E) (ιE : ι → E)
    (eN : Ground G σ F ≃ Fin (Fintype.card (Ground G σ F))) :
    (roundCand (G := G) σ F ιE eN).card ≤
      Nat.choose (Fintype.card (Ground G σ F) + Fintype.card ι - 1) (Fintype.card ι) :=
  Finset.card_image_le.trans (argmaxFamily_card_le (roundS (G := G) σ F ιE) eN)

/-- **Lemma 3.10's third factor**: `log |A| ≤ 4√(2nm)` with `n` bounding `|V|`. -/
theorem log_roundCand_le (σ : V → E) (F : Finset E) (ιE : ι → E)
    (eN : Ground G σ F ≃ Fin (Fintype.card (Ground G σ F))) (hF : IsForest G F) {n : ℕ}
    (hV : Fintype.card V ≤ n) :
    Real.log ((roundCand (G := G) σ F ιE eN).card : ℝ) ≤
      4 * Real.sqrt ((2 * n : ℝ) * (Fintype.card ι : ℝ)) := by
  classical
  rcases Nat.eq_zero_or_pos (roundCand (G := G) σ F ιE eN).card with h0 | hpos
  · rw [h0]
    simp only [Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hcard := roundCand_card_le (G := G) σ F ιE eN
  have hstep : Nat.choose (Fintype.card (Ground G σ F) + Fintype.card ι - 1) (Fintype.card ι) ≤
      Nat.choose (Fintype.card (Ground G σ F) + Fintype.card ι) (Fintype.card ι) :=
    Nat.choose_le_choose _ (by omega)
  have hle : (roundCand (G := G) σ F ιE eN).card ≤
      Nat.choose (Fintype.card (Ground G σ F) + Fintype.card ι) (Fintype.card ι) :=
    hcard.trans hstep
  have hpos' : (0 : ℝ) <
      (Nat.choose (Fintype.card (Ground G σ F) + Fintype.card ι) (Fintype.card ι) : ℝ) := by
    have : 0 < Nat.choose (Fintype.card (Ground G σ F) + Fintype.card ι) (Fintype.card ι) :=
      Nat.choose_pos (by omega)
    exact_mod_cast this
  have hα : Fintype.card (Ground G σ F) ≤ 2 * n := by
    have := card_Ground_le σ F hF
    omega
  calc Real.log ((roundCand (G := G) σ F ιE eN).card : ℝ)
      ≤ Real.log (Nat.choose (Fintype.card (Ground G σ F) + Fintype.card ι)
          (Fintype.card ι) : ℝ) :=
        Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)
    _ ≤ 4 * Real.sqrt ((Fintype.card (Ground G σ F) : ℝ) * (Fintype.card ι : ℝ)) :=
        log_choose_le (Fintype.card (Ground G σ F)) (Fintype.card ι)
    _ ≤ 4 * Real.sqrt ((2 * n : ℝ) * (Fintype.card ι : ℝ)) := by
        have hnm : (Fintype.card (Ground G σ F) : ℝ) ≤ 2 * n := by exact_mod_cast hα
        have := Real.sqrt_le_sqrt
          (mul_le_mul_of_nonneg_right hnm (Nat.cast_nonneg (α := ℝ) (Fintype.card ι)))
        linarith

end Fibre

end DLMST