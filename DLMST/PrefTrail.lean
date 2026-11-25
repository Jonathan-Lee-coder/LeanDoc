import DLMST.Rounds

/-!
# The preference `find` read as a path-maximum test

§3.1 decides `e`'s preferred action by comparing `p(e)` with the path-maximum over the `F`-trail
joining `e`'s ends (Lemma 2.9's path-maximum query).  The definition `prefFind` only asks whether
`F≤p(e)` *connects* the ends, so the passage from one reading to the other is the claim that, inside
a forest, the connecting set `belowLe G F (pE G σ e)` is the whole trail:

* if `F≤p(e)` joins the ends, its witness trail can be reduced to a backtrack-free trail inside
  `F` (`IsForest.exists_consecFree_trail`), and `IsForest.trail_eq` says the reduced trail is *the*
  trail `es` — so every edge of `es` is at most `pE`;
* conversely, if every edge of `es` is at most `pE` then `es` is a trail inside `F≤p(e)`, which is
  exactly a `Conn` witness (`conn_of_path`).

The two spoke-incidence hypotheses and `portal ≠ portal` are what rule out the three `F`-free
disjuncts of `prefFind`, i.e. they say "both ends have spokes and they lead to different portals".
-/

namespace DLMST

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] {G : WGraph V E}

/-- **The `find` preference is a path-maximum test.**  Given that both ends of `e` have spokes
leading to different portals, `prefFind` holds exactly when every edge of the unique reduced
`F`-trail from `G.src e` to `G.dst e` weighs at most `p(e)`. -/
theorem prefFind_iff_trail_weight {F : Finset E} (hF : IsForest G F) {σ : V → E} {e : E}
    (hsp : incident G (G.src e) (σ (G.src e)) ∧ incident G (G.dst e) (σ (G.dst e)))
    (hpne : portal G σ (G.src e) ≠ portal G σ (G.dst e))
    {es : List E} (hp : Path G (G.src e) es (G.dst e)) (hsub : ∀ g ∈ es, g ∈ F)
    (hcf : consecFree es) :
    prefFind G σ F e ↔ ∀ g ∈ es, G.weight g ≤ pE G σ e := by
  classical
  constructor
  · intro hfind
    rcases hfind with h1 | h2 | h3 | h4
    · exact absurd hsp.1 h1
    · exact absurd hsp.2 h2
    · exact absurd h3 hpne
    · obtain ⟨fs, hfs, hfsF⟩ := path_of_conn h4
      have hsuble : belowLe G F (pE G σ e) ⊆ F := Finset.filter_subset _ _
      have hFle : IsForest G (belowLe G F (pE G σ e)) := hF.hereditary _ hsuble
      obtain ⟨fs', hfs', hfs'le, hcf'⟩ := hFle.exists_consecFree_trail fs hfs hfsF
      have hFs' : ∀ g ∈ fs', g ∈ F := fun g hg => hsuble (hfs'le g hg)
      have heq : es = fs' := hF.trail_eq es fs' _ _ hp hfs' hsub hFs' hcf hcf'
      intro g hg
      rw [heq] at hg
      exact (belowLe_mem.mp (hfs'le g hg)).2
  · intro h
    exact Or.inr (Or.inr (Or.inr
      (conn_of_path hp fun g hg => belowLe_mem.mpr ⟨hsub g hg, h g hg⟩)))

end DLMST