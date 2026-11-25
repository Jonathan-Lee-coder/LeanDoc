import DLMST.Greedy
import DLMST.Tree

/-!
# The filtering lemma: what the certificate procedure is *for*

§1.2 and §3.1 define, for a forest `F` and an edge `e`, that `e` is **supported** by `F` when
`F≤w(e)` — the edges of `F` no heavier than `e` — already joins the two ends of `e`.  `U(F)` is the
set of edges that are *not* supported.  The paper then says, in one sentence in §3.1 and without
proof:

> As we will show, `F` together with the unsupported edges contains an MSF of `G`.  We may therefore
> filter out (discard) every supported edge outside `F`.

That sentence is the whole justification of the algorithm's shape: the certificate procedure is
allowed to throw edges away, and the claim is that what it throws away is exactly what is safe to
throw away.  Everything else in §3 is about how *cheaply* such an `F` can be found; this file checks
that the *object* it finds has the claimed property.

`filter_preserves_msf` is the statement, and it is true for **any** edge set `F`, forest or not — the
paper's `F` is a forest, but nothing in the correctness argument uses that.  The proof is a measure
argument: pick an MSF `T` maximising `|T ∩ (F ∪ U(F))|`; if `e ∈ T` is supported and outside `F`, the
supporting `F≤w(e)`-trail must leave the component of `T − e`, which gives an edge `g` of `F` with
`w(g) ≤ w(e)` that `T − e` separates, and `isMSF_exchange` trades `e` for `g` — one more edge inside
`F ∪ U(F)`, contradicting the choice of `T`.

Two side results record what the paper's notation assumes: an edge of `F` is always supported, so
`F` and `U(F)` are disjoint and `|F| + |U(F)|` really is the size of their union; and `U(F)` contains
the plain rejection set `reject G F` of §2, so this is a *weaker* filter than §2's — which is why the
weight threshold has to be paid for by the admissibility bookkeeping of §3.
-/

namespace DLMST

set_option linter.unusedSectionVars false

open Classical

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] {G : WGraph V E}

/-- **`e` is supported by `F`** (paper, §1.2): its ends are joined by the edges of `F` that are no
heavier than `e`.  Adding `e` to `F` then closes a cycle in which `e` is a heaviest edge. -/
def supported (G : WGraph V E) (F : Finset E) (e : E) : Prop :=
  Conn G (F.filter fun g => G.weight g ≤ G.weight e) (G.src e) (G.dst e)

/-- **The retained set `U(F)`** (paper, §1.2): the edges unsupported by `F`.  These are the edges the
certificate procedure cannot account for, and everything recurses on. -/
noncomputable def unsupp (G : WGraph V E) (F : Finset E) : Finset E :=
  Finset.univ.filter fun e => ¬ supported G F e

theorem mem_unsupp {F : Finset E} {e : E} : e ∈ unsupp G F ↔ ¬ supported G F e := by
  simp [unsupp]

/-- An edge already in `F` supports itself, since `F≤w(e)` contains `e`.  This is why the paper can
write `|F| + |U(F)|`: the two sets do not overlap. -/
theorem supported_of_mem {F : Finset E} {e : E} (he : e ∈ F) : supported G F e :=
  Conn.step e (Finset.mem_filter.mpr ⟨he, le_refl _⟩)

/-- `F` and `U(F)` are disjoint. -/
theorem disjoint_unsupp {F : Finset E} : Disjoint F (unsupp G F) :=
  Finset.disjoint_left.mpr fun _e he heu => (mem_unsupp.mp heu) (supported_of_mem he)

/-- **The paper's `|F| + |U(F)|` is the size of `F ∪ U(F)`.**  Justifying the notation costs one line,
but §3.6 counts the two terms as though they were disjoint. -/
theorem card_add_unsupp {F : Finset E} :
    F.card + (unsupp G F).card = (F ∪ unsupp G F).card := by
  have h : (F ∩ unsupp G F).card = 0 := by
    rw [Finset.disjoint_iff_inter_eq_empty.mp disjoint_unsupp]
    exact Finset.card_empty
  have hsum := Finset.card_union_add_card_inter F (unsupp G F)
  omega

/-- `U(F)` retains more edges than §2's rejection set: dropping the weight threshold can only make it
easier to be supported. -/
theorem reject_subset_unsupp {F : Finset E} : reject G F ⊆ unsupp G F := by
  intro e he
  rw [mem_unsupp]
  intro h
  exact (mem_reject.mp he)
    (show Conn G F (G.src e) (G.dst e) from h.mono (Finset.filter_subset _ _))

/-- **The filtering lemma (paper, §3.1: "`F` together with the unsupported edges contains an MSF of
`G`"; machine-checked).**  Discarding every supported edge outside `F` leaves a graph that still has
an MSF of `G`. -/
theorem filter_preserves_msf (F : Finset E) :
    ∃ T, IsMSF G T ∧ T ⊆ F ∪ unsupp G F := by
  classical
  let S := F ∪ unsupp G F
  obtain ⟨l, _hl, hKs⟩ := kruskal_exists (G := G)
  -- an MSF with as many edges inside `S` as possible
  obtain ⟨T, hTmem, hTmax⟩ :=
    Finset.exists_max_image (Finset.univ.filter fun T : Finset E => IsMSF G T)
      (fun T : Finset E => (T ∩ S).card)
      ⟨K G l ∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hKs⟩⟩
  obtain ⟨_, hTmsf⟩ := Finset.mem_filter.mp hTmem
  refine ⟨T, hTmsf, ?_⟩
  by_contra hnot
  rw [Finset.not_subset] at hnot
  obtain ⟨e, heT, heS⟩ := hnot
  have heF : e ∉ F := fun hf => heS (Finset.mem_union.mpr (Or.inl hf))
  have hnsupp : e ∉ unsupp G F := fun hf => heS (Finset.mem_union.mpr (Or.inr hf))
  rw [mem_unsupp] at hnsupp
  have hesupp : supported G F e := not_not.mp hnsupp
  -- the ends of `e` are joined by `F≤w(e)`, but not by `T − e`
  obtain ⟨hTf, _hTsp⟩ := hTmsf.1
  have hsep : ¬ Conn G (T.erase e) (G.src e) (G.dst e) := hTf.bridge heT
  let P : Finset E := F.filter fun g => G.weight g ≤ G.weight e
  have hconn : Conn G P (G.src e) (G.dst e) := hesupp
  have hPS : P ⊆ S :=
    Finset.subset_iff.mpr fun _ hx => Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mp hx).1)
  obtain ⟨g, hgP, hcr⟩ :=
    crossing_of_conn hconn {x | Conn G (T.erase e) (G.src e) x} (Conn.refl (G.src e)) hsep
  obtain ⟨hgF, hwg⟩ := Finset.mem_filter.mp hgP
  have hgne : g ≠ e := fun he => heF (he ▸ hgF)
  have hgs : g ∈ S := hPS hgP
  -- a crossing edge of the component of `T − e` is not joined inside it
  have hgg : ¬ Conn G (T.erase e) (G.src g) (G.dst g) := by
    rcases hcr with ⟨hs, hd⟩ | ⟨hs, hd⟩
    · intro h
      exact absurd (hs.trans h) hd
    · intro h
      exact absurd (hd.trans h.symm) hs
  have hgT : g ∉ T := fun hgt => hgg (Conn.step g (Finset.mem_erase.mpr ⟨hgne, hgt⟩))
  -- trading `e` for the no-heavier `g` stays minimum and moves one more edge inside `S`
  have hT' : IsMSF G (insert g (T.erase e)) := isMSF_exchange hTmsf heT hgg hwg
  have hgt : g ∉ T ∩ S := fun h => hgT (Finset.mem_inter.mp h).1
  have hR : insert g (T ∩ S) ⊆ insert g (T.erase e) ∩ S := by
    refine Finset.insert_subset_iff.mpr ⟨Finset.mem_inter.mpr ⟨by simp, hgs⟩, ?_⟩
    intro x hx
    obtain ⟨hxT, hxS⟩ := Finset.mem_inter.mp hx
    refine Finset.mem_inter.mpr ⟨Finset.mem_insert.mpr (Or.inr ?_), hxS⟩
    exact Finset.mem_erase.mpr ⟨fun he => heS (he ▸ hxS), hxT⟩
  have hle : ((insert g (T.erase e)) ∩ S).card ≤ (T ∩ S).card := by
    simpa using hTmax (insert g (T.erase e)) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT'⟩)
  have hcard : (T ∩ S).card + 1 ≤ ((insert g (T.erase e)) ∩ S).card := by
    have := Finset.card_le_card (s := insert g (T ∩ S)) hR
    rw [Finset.card_insert_of_notMem (s := T ∩ S) hgt] at this
    omega
  omega

end DLMST
