import Mathlib

/-!
# §3.3, Definition 3.4: an edge has at most `2t` bad rounds

§3.3 fixes one edge `e` and looks at its *preferred action* in each of the `t²` rounds, laid out as
`t` blocks of `t` rounds (`find` if either endpoint has no spoke, or the two spokes coincide, or
`F≤p(e)` already connects the ends; `project` otherwise).  Definition 3.4 then declares a round
*bad* for `e` if

* it is the last round **in its block** with a `project` preference, or
* its preferred action is `find` and its block is the **last block** containing any `find` preference.

The paper's only claim about this definition is the count: *"By definition, there are at most `2t` bad
rounds.  Indeed, there are at most `t` blocks, each containing at most one bad project round.  In
addition, bad find rounds can occur in at most one block, which contains at most `t` rounds."*  This
file checks that: `badProject_card_le_one` is the per-block uniqueness, and `bad_card_le` is `≤ 2t`;
its proof also exhibits the single block that contains all bad `find` rounds.

Both counts are stated for a `Finset` given by a membership characterisation rather than as
`Finset.univ.filter (· bad)`, because `bad` is a `def` and Lean will not search for its decidability
outside a `classical` block; any two such sets are equal by extensionality, so nothing is lost.

Note what the count does *not* use: the per-block monotonicity the paper derives earlier ("within each
block, the preferred action of `e` is `project` for an initial sequence of rounds, followed by `find`",
from the fact that connectivity in `F≤a` only improves and that spokes are frozen inside a block).
Uniqueness of the last `project` round holds for any preference table, so `MonoRow` is stated below but
only recorded, not used.  That monotonicity is *derived* from the round state, and Claim 3.5, Claim 3.6
and Lemma 3.7 are proved, in `Rounds.lean` (`monoRow_of_connImproves`, `admOut_admissible`,
`LiftsLe.walk`, `claim_3_6`, `lemma37`).  What is not formalised anywhere yet: the schedule and the
estimate of §3.4 (Definition 3.8, Lemma 3.11, Claim 3.12).
-/

namespace DLMST

set_option linter.unusedSectionVars false

/-- **Preferred action** (paper, §3.1/§3.3): `find` when the edge's endpoints are already joined
(spoke missing, equal spokes, or connected in `F≤p(e)`), `project` otherwise. -/
inductive Pref where
  | find
  | project
  deriving DecidableEq

private theorem pref_ne : (Pref.find : Pref) ≠ Pref.project := by decide

/-- **Definition 3.4, first clause**: a round that is the last `project` round of its block. -/
def badProject (act : Fin t → Fin t → Pref) (b i : Fin t) : Prop :=
  act b i = .project ∧ ∀ j : Fin t, i < j → act b j = .find

/-- **Definition 3.4, second clause**: a `find` round whose block is the last block with any `find`
preference. -/
def badFind (act : Fin t → Fin t → Pref) (b i : Fin t) : Prop :=
  act b i = .find ∧ ∀ c : Fin t, b < c → ∀ j : Fin t, act c j = .project

/-- **Definition 3.4**: the bad rounds of `act`, as a predicate on `(block, round)` pairs. -/
def bad (act : Fin t → Fin t → Pref) (p : Fin t × Fin t) : Prop :=
  badProject act p.1 p.2 ∨ badFind act p.1 p.2

/-- **§3.3's monotonicity premise** (recorded, not needed for the count): inside a block, once the
preference is `find` it stays `find`, because connectivity in `F≤a` only improves and the spokes are
frozen until the block ends. -/
def MonoRow (act : Fin t → Fin t → Pref) : Prop :=
  ∀ b i j : Fin t, i ≤ j → act b i = .find → act b j = .find

/-- **"each [block contains] at most one bad project round"** (§3.3, machine-checked). -/
theorem badProject_card_le_one (act : Fin t → Fin t → Pref) (b : Fin t)
    (S : Finset (Fin t)) (hS : ∀ i, i ∈ S ↔ badProject act b i) : S.card ≤ 1 := by
  classical
  refine Finset.card_le_one.mpr (fun i hi j hj => ?_)
  obtain ⟨hpi, hlast⟩ := hS i |>.mp hi
  obtain ⟨hpj, hlaj⟩ := hS j |>.mp hj
  rcases lt_trichotomy i j with hij | heq | hij
  · exact (pref_ne ((hlast j hij).symm.trans hpj)).elim
  · exact heq
  · exact (pref_ne ((hlaj i hij).symm.trans hpi)).elim

/-- **"there are at most `2t` bad rounds"** (Definition 3.4, machine-checked): the `t²` rounds are the
pairs `(block, round)`, and the bad ones number at most `2t`. -/
theorem bad_card_le (act : Fin t → Fin t → Pref) (R : Finset (Fin t × Fin t))
    (hR : ∀ p, p ∈ R ↔ bad act p) : R.card ≤ 2 * t := by
  classical
  let proj : Finset (Fin t × Fin t) := (Finset.univ : Finset (Fin t × Fin t)).filter
    fun p => badProject act p.1 p.2
  let findp : Finset (Fin t × Fin t) := (Finset.univ : Finset (Fin t × Fin t)).filter
    fun p => badFind act p.1 p.2
  have hprojR : R ⊆ proj ∪ findp := by
    intro p hp
    obtain h | h := (hR p).mp hp
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
  -- the bad-project rounds are covered by one row per block, each holding at most one round
  have hrow : ∀ b : Fin t, ((Finset.univ : Finset (Fin t)).filter
      (fun i => badProject act b i)).card ≤ 1 := by
    intro b
    classical
    refine badProject_card_le_one act b _ (fun i => ?_)
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hproj : proj.card ≤ t := by
    classical
    let F : Fin t → Finset (Fin t × Fin t) :=
      fun b => Finset.image (Prod.mk b)
        ((Finset.univ : Finset (Fin t)).filter (fun i => badProject act b i))
    have hsub : proj ⊆ (Finset.univ : Finset (Fin t)).biUnion F := by
      intro p hp
      obtain ⟨_, hpa⟩ := Finset.mem_filter.mp hp
      refine Finset.mem_biUnion.mpr ⟨p.1, Finset.mem_univ _, ?_⟩
      refine Finset.mem_image.mpr ⟨p.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpa⟩, rfl⟩
    have h1 : proj.card ≤ (Finset.univ : Finset (Fin t)).sum (fun b => (F b).card) :=
      Nat.le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
    have h2 : (Finset.univ : Finset (Fin t)).sum (fun b => (F b).card)
        ≤ (Finset.univ : Finset (Fin t)).sum (fun _ => (1 : ℕ)) :=
      Finset.sum_le_sum fun b _ => Nat.le_trans Finset.card_image_le (hrow b)
    have h3 : (Finset.univ : Finset (Fin t)).sum (fun _ => (1 : ℕ)) = t := by
      have hs : (Finset.univ : Finset (Fin t)).sum (fun _ => (1 : ℕ))
          = (Finset.univ : Finset (Fin t)).card := (Finset.card_eq_sum_ones _).symm
      rw [hs, Finset.card_univ, Fintype.card_fin]
    have h4 : (Finset.univ : Finset (Fin t)).sum (fun b => (F b).card) ≤ t :=
      Nat.le_trans h2 (Nat.le_of_eq h3)
    omega
  -- the bad-find rounds all live in the last block that contains a `find` preference
  have hfind : findp.card ≤ t := by
    let B : Finset (Fin t) := (Finset.univ : Finset (Fin t)).filter fun b => ∃ i, act b i = .find
    by_cases hB : B.Nonempty
    · obtain ⟨b, hb, hbmax⟩ := Finset.exists_max_image B (fun c : Fin t => (c : ℕ)) hB
      obtain ⟨_, hexi⟩ := Finset.mem_filter.mp hb
      obtain ⟨i0, hi0⟩ := hexi
      have hsub : findp ⊆ {b} ×ˢ (Finset.univ : Finset (Fin t)) := by
        intro p hp
        obtain ⟨_, hpfind, hlast⟩ := Finset.mem_filter.mp hp
        refine Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr ?_, Finset.mem_univ _⟩
        rcases lt_trichotomy p.1 b with hlt | heq | hgt
        · exact (pref_ne (hi0.symm.trans (hlast b hlt i0))).elim
        · exact heq
        · have hbm := hbmax p.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨p.2, hpfind⟩⟩)
          omega
      refine Nat.le_trans (Finset.card_le_card hsub) ?_
      rw [Finset.card_product, Finset.card_singleton, one_mul, Finset.card_univ, Fintype.card_fin]
    · have hnp : ∀ b i, act b i ≠ .find := by
        intro b i h
        exact hB ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨i, h⟩⟩⟩
      have hz : findp = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro p _ hbad
        obtain ⟨hpfind, _⟩ := hbad
        exact hnp p.1 p.2 hpfind
      rw [hz, Finset.card_empty]
      omega
  have hle := Nat.le_trans (Finset.card_le_card hprojR) (Finset.card_union_le proj findp)
  omega

end DLMST
