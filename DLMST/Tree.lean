import DLMST.Exchange

/-!
# Path uniqueness in a forest, and the greedy step it unlocks

`Exchange.lean` proves the single-edge exchange argument but stops one lemma short of the greedy
step the paper actually takes: the edge it wants to add, `e`, is lightest across the cut of its
`F`-component, and the tree edge it may replace must *both* cross that cut and separate
`G.src e` from `G.dst e` inside the spanning forest `T`.  `exists_sep_edge` gives a separating edge
and `Path.crossing_of_conn` a cut-crossing edge, but not necessarily the same one.  Uniqueness of
paths in a forest is what identifies them.

This file builds the trail surgery that uniqueness needs, working with the explicit edge lists of
`Path G u es v` rather than with the inductive relation `Conn`:

* `IsForest.nloop` — a forest contains no self-loop, so a backtrack pair can always be deleted;
* `Path.split` — a trail over `as ++ bs` is a trail over `as` followed by one over `bs`;
* `Path.erase_pair` / `erase_pair_cons` — deleting `f :: f` from the middle of a trail leaves a
  trail with the same endpoints (backtracking over an edge accomplishes nothing);
* `consecFree` — "never traverses the same edge twice in a row", the property a trail retains after
  backtrack pairs are deleted; it passes to sub-trails (`consecFree.of_sublist`), not upwards;
* `List.split_first` — cutting a list at the *first* occurrence of an edge;
* `IsForest.closed_consecFree` — **a forest has no reduced closed trail**: a closed trail that never
  immediately backtracks must be empty.  This is the engine of the whole layer; the `consecFree`
  hypothesis cannot be dropped, since `e :: e` is a closed trail in a one-edge forest;
* `IsForest.exists_consecFree_trail` — every trail inside a forest reduces to a backtrack-free one
  over the same endpoints, so nothing is lost by assuming reducedness;
* `IsForest.occur_once` — a reduced forest trail therefore uses each of its edges exactly once: two
  occurrences would bound either a reduced closed trail (impossible) or an empty segment (an
  adjacent backtrack);
* `IsForest.sep_of_mem_trail` — **every edge of a reduced forest trail separates the trail's
  endpoints**: deleting it breaks the trail into two halves that `F` cannot reconnect, since `F` has
  no bridge-free cycle.  This is the path-uniqueness statement the greedy step needs; the stronger
  `trail_eq` (two forest trails with the same endpoints use the same edges) is not required.

`IsForest.trail_eq` — **two forest trails with the same endpoints use the same edges** — is proved
below by parity bookkeeping (`List.count` is preserved by the backtrack deletions that reduce a
trail), and it is what the `Boruvka.lean` whole-round argument uses to see that a round cannot pick
two edges of the same cut twice.  The aggregation of `kruskal_step` into a loop invariant over a
whole sorted scan lives in `Greedy.lean`, together with `kruskal_correct`.

With `sep_of_mem_trail` the gap closes, and this file ends with `kruskal_step`: if `F` is a partial
solution, `T` a minimum spanning forest containing it, and `e` an edge lightest among those whose
ends `F` does not yet join, then some minimum spanning forest contains `insert e F`.
-/

namespace DLMST

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] {G : WGraph V E}

/-- A forest contains no self-loop: each of its edges was added joining two distinct vertices. -/
theorem IsForest.nloop {F : Finset E} (hF : IsForest G F) {f : E} (hf : f ∈ F) :
    G.src f ≠ G.dst f := by
  induction hF with
  | empty => exact absurd hf (by simp)
  | @add Fsub esub hF' hne hc ih =>
      rcases Finset.mem_insert.mp hf with he | hsub
      · exact he ▸ hne
      · exact ih hsub

/-- **Splitting a trail.**  A trail over `as ++ bs` from `u` to `v` is a trail over `as` from `u` to
some vertex `x` followed by a trail over `bs` from `x` to `v`. -/
theorem Path.split {bs : List E} {v : V} :
    ∀ (as : List E) (u : V), Path G u (as ++ bs) v →
      ∃ x, Path G u as x ∧ Path G x bs v := by
  intro as u p
  induction as generalizing u with
  | nil => exact ⟨u, Path.nil u, p⟩
  | cons a as ih =>
      cases p with
      | fwd _ hs hd pes =>
          obtain ⟨x, p1, p2⟩ := ih _ pes
          exact ⟨x, Path.fwd a hs hd p1, p2⟩
      | bwd _ hd hs pes =>
          obtain ⟨x, p1, p2⟩ := ih _ pes
          exact ⟨x, Path.bwd a hd hs p1, p2⟩

/-- **Deleting a backtrack at the head.**  Going over `f` and immediately back is a no-op, provided
`f` is not a self-loop (otherwise the pair really does move along the graph). -/
theorem Path.erase_pair_cons {f : E} (hne : G.src f ≠ G.dst f) {bs : List E} {u v : V}
    (p : Path G u (f :: f :: bs) v) : Path G u bs v := by
  cases p with
  | fwd _ hs hd pes =>
      cases pes with
      | fwd _ hs' _ _ => subst hs'; exact absurd hd.symm hne
      | bwd _ _ hs' pes' => subst hs'; subst hs; exact pes'
  | bwd _ hd hs pes =>
      cases pes with
      | fwd _ _ hd' pes' => subst hd'; subst hd; exact pes'
      | bwd _ hd' _ _ => subst hd'; exact absurd hs hne

/-- **Deleting a backtrack from the middle of a trail.** -/
theorem Path.erase_pair {f : E} (hne : G.src f ≠ G.dst f) {bs : List E} {v : V} :
    ∀ (as : List E) (u : V), Path G u (as ++ f :: f :: bs) v → Path G u (as ++ bs) v := by
  intro as u p
  induction as generalizing u with
  | nil => exact p.erase_pair_cons hne
  | cons a as ih =>
      cases p with
      | fwd _ hs hd pes => exact Path.fwd a hs hd (ih _ pes)
      | bwd _ hd hs pes => exact Path.bwd a hd hs (ih _ pes)

/-- `es` never traverses the same edge twice in a row.  This is the property a trail keeps after
backtrack pairs are deleted, and the hypothesis of `IsForest.closed_consecFree`. -/
def consecFree (es : List E) : Prop :=
  ∀ (as bs : List E) (f : E), es ≠ as ++ f :: f :: bs

/-- A prefix of a backtrack-free list is backtrack-free. -/
theorem consecFree.of_append_left {es fs : List E} (h : consecFree (es ++ fs)) : consecFree es := by
  intro as bs f he
  exact h as (bs ++ fs) f (by simp [he, List.append_assoc])

/-- A suffix of a backtrack-free list is backtrack-free. -/
theorem consecFree.of_append_right {es fs : List E} (h : consecFree (es ++ fs)) : consecFree fs := by
  intro as bs f he
  exact h (es ++ as) bs f (by rw [he, ← List.append_assoc])

/-- A one-edge trail runs from one endpoint of the edge to the other, in one of the two directions. -/
theorem Path.ends_of_singleton {e : E} {u v : V} (p : Path G u [e] v) :
    (u = G.src e ∧ v = G.dst e) ∨ (u = G.dst e ∧ v = G.src e) := by
  cases p with
  | fwd _ hs hd pes =>
      cases pes with
      | nil _ => exact Or.inl ⟨hs.symm, hd.symm⟩
  | bwd _ hd hs pes =>
      cases pes with
      | nil _ => exact Or.inr ⟨hd.symm, hs.symm⟩

/-- Being backtrack-free passes to sub-trails. -/
theorem consecFree.of_sublist {l₁ es l₂ : List E} (h : consecFree (l₁ ++ (es ++ l₂))) :
    consecFree es := by
  have h1 : consecFree (es ++ l₂) := of_append_right (es := l₁) h
  exact of_append_left (fs := l₂) h1

/-- Split a list at the first occurrence of `a`: everything before it is different from `a`. -/
theorem List.split_first {a : E} : (l : List E) → a ∈ l → ∃ p s, l = p ++ a :: s ∧ ∀ x ∈ p, x ≠ a := by
  classical
  intro l
  induction l with
  | nil => intro h; exact absurd h (by simp)
  | cons b l ih =>
      intro hl
      by_cases hab : a = b
      · exact ⟨[], l, by rw [← hab, List.nil_append], by simp⟩
      · rcases List.mem_cons.mp hl with h | hl'
        · exact absurd h hab
        · obtain ⟨p, s, hp, hnp⟩ := ih hl'
          refine ⟨b :: p, s, ?_, ?_⟩
          · rw [hp, List.cons_append]
          · intro x hx
            rcases List.mem_cons.mp hx with hxb | hxp
            · exact fun he => hab (he.symm.trans hxb)
            · exact hnp x hxp

/-- **A forest has no reduced closed trail.**  This is "a forest is cycle-free" in the form the
reduction arguments need: a closed trail that never backtracks along an edge cannot exist at all.
The hypothesis cannot be dropped — going over an edge and straight back *is* a closed trail in a
forest, which is exactly why the reduction to backtrack-free trails has to come first.

The proof is induction over the construction of the forest.  If the last-added edge `esub` is never
used, the trail lives in the smaller forest.  Otherwise cut the trail at the first occurrence of
`esub` and at its second one: the segment between the two crossings is again reduced and closed, and
if the two crossings *end* at the same vertex the induction hypothesis deletes that segment, leaving
`esub :: esub` in the middle of the trail, contradicting reducedness; if they end at opposite
vertices, the smaller forest already connects the two ends of `esub`, contradicting the step that
added it. -/
theorem IsForest.closed_consecFree {T : Finset E} (hT : IsForest G T) :
    ∀ (x : V) (es : List E), Path G x es x → consecFree es → (∀ g ∈ es, g ∈ T) → es = [] := by
  classical
  induction hT with
  | empty =>
      intro x es p hf hmem
      cases es with
      | nil => rfl
      | cons a as => exact absurd (hmem a (by simp)) (by simp)
  | @add Fsub esub hF hne hc ih =>
      intro x es p hf hmem
      by_cases hef : esub ∈ es
      · -- the last-added edge is used: cut the trail at its first occurrence
        obtain ⟨α, β, hab, hnoα⟩ := List.split_first es hef
        have h1 : Path G x (α ++ esub :: β) x := hab ▸ p
        obtain ⟨y, pα, pre1⟩ := Path.split α x h1
        obtain ⟨z, p1, pβ⟩ := Path.split [esub] y (by rw [List.singleton_append]; exact pre1)
        have hα : ∀ g ∈ α, g ∈ Fsub := by
          intro g hg
          rcases Finset.mem_insert.mp (hmem g (by rw [hab]; simp [hg])) with he | hF'
          · exact absurd he (hnoα g hg)
          · exact hF'
        have hconnxy : Conn G Fsub x y := conn_of_path pα hα
        -- which end of `esub` does the trail arrive at, and which does it leave from?
        have hor : (y = G.src esub ∧ z = G.dst esub) ∨ (y = G.dst esub ∧ z = G.src esub) :=
          Path.ends_of_singleton p1
        by_cases hβ : esub ∈ β
        · -- the trail returns to `esub`: cut a second time
          obtain ⟨γ, δ, hγδ, hnoγ⟩ := List.split_first β hβ
          have h2 : Path G z (γ ++ esub :: δ) x := hγδ ▸ pβ
          obtain ⟨w, pγ, pre2⟩ := Path.split γ z h2
          obtain ⟨r, p2, pδ⟩ := Path.split [esub] w (by rw [List.singleton_append]; exact pre2)
          have hγ : ∀ g ∈ γ, g ∈ Fsub := by
            intro g hg
            rcases Finset.mem_insert.mp (hmem g (by rw [hab, hγδ]; simp [hg])) with he | hF'
            · exact absurd he (hnoγ g hg)
            · exact hF'
          have hconnzw : Conn G Fsub z w := conn_of_path pγ hγ
          have hor2 : (w = G.src esub ∧ r = G.dst esub) ∨
              (w = G.dst esub ∧ r = G.src esub) := Path.ends_of_singleton p2
          rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rcases hor2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · -- the two crossings run in opposite directions: `Fsub` joins the ends of `esub`
              exact absurd hconnzw.symm hc
            · -- they run the same way: `γ` is itself a reduced closed trail in `Fsub`
              have hkey : es = (α ++ [esub]) ++ (γ ++ esub :: δ) := by
                rw [hab, hγδ, List.append_assoc, List.singleton_append]
              have hcfγ : consecFree γ := (hkey ▸ hf).of_append_right.of_append_left
              have hmemγ : ∀ g ∈ γ, g ∈ Fsub := hγ
              rw [ih (G.dst esub) γ pγ hcfγ hmemγ, List.nil_append] at hγδ
              subst hγδ
              exact absurd hab (hf α δ esub)
          · rcases hor2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · -- `γ` is a reduced closed trail in `Fsub`
              have hkey : es = (α ++ [esub]) ++ (γ ++ esub :: δ) := by
                rw [hab, hγδ, List.append_assoc, List.singleton_append]
              have hcfγ : consecFree γ := (hkey ▸ hf).of_append_right.of_append_left
              rw [ih (G.src esub) γ pγ hcfγ hγ, List.nil_append] at hγδ
              subst hγδ
              exact absurd hab (hf α δ esub)
            · exact absurd hconnzw hc
        · -- `esub` occurs exactly once: both sides of the crossing lie in `Fsub`
          have hβ' : ∀ g ∈ β, g ∈ Fsub := by
            intro g hg
            rcases Finset.mem_insert.mp (hmem g (by rw [hab]; simp [hg])) with he | hF'
            · exact absurd (he ▸ hg) hβ
            · exact hF'
          have hzx : Conn G Fsub z x := conn_of_path pβ hβ'
          rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact absurd (hzx.trans hconnxy).symm hc
          · exact absurd (hzx.trans hconnxy) hc
      · -- the last-added edge is not used: the trail lies in the smaller forest
        refine ih x es p hf ?_
        intro g hg
        rcases Finset.mem_insert.mp (hmem g hg) with he | hF'
        · exact absurd (he ▸ hg) hef
        · exact hF'


/-- **Reducing a trail.**  Every trail inside a forest has a backtrack-free sub-trail with the same
endpoints: delete `f :: f` pairs until none is left.  Termination is by the length of the list, which
drops by two at each step, so the argument is induction on a length bound. -/
theorem IsForest.exists_consecFree_trail {T : Finset E} (hT : IsForest G T) {u v : V} :
    ∀ (es : List E), Path G u es v → (∀ g ∈ es, g ∈ T) →
      ∃ es', Path G u es' v ∧ (∀ g ∈ es', g ∈ T) ∧ consecFree es' := by
  classical
  have key : ∀ (k : Nat) (es : List E), es.length ≤ k → Path G u es v → (∀ g ∈ es, g ∈ T) →
      ∃ es', Path G u es' v ∧ (∀ g ∈ es', g ∈ T) ∧ consecFree es' := by
    intro k
    induction k with
    | zero =>
        intro es hle p hmem
        have hlen : es.length = 0 := Nat.le_zero.mp hle
        cases es with
        | nil => exact ⟨[], p, hmem, fun as bs f he => absurd he (by simp)⟩
        | cons a as => simp [List.length_cons] at hlen
    | succ k ih =>
        intro es hle p hmem
        by_cases hb : ∃ (as : List E) (f : E) (bs : List E), es = as ++ f :: f :: bs
        · obtain ⟨as, f, bs, rfl⟩ := hb
          have hft : f ∈ T := hmem f (by simp)
          have hne : G.src f ≠ G.dst f := hT.nloop hft
          have p' : Path G u (as ++ bs) v := Path.erase_pair hne as u p
          have hlen : (as ++ bs).length ≤ k := by
            have h : (as ++ f :: f :: bs).length = as.length + bs.length + 2 := by
              rw [List.length_append, List.length_cons, List.length_cons]
              omega
            rw [h] at hle
            rw [List.length_append]
            omega
          obtain ⟨es', pes', hmem', hc'⟩ := ih (as ++ bs) hlen p' (by
            intro g hg
            rcases List.mem_append.mp hg with ha | hb
            · exact hmem g (List.mem_append.mpr (Or.inl ha))
            · exact hmem g (List.mem_append.mpr (Or.inr
                (List.mem_cons_of_mem f (List.mem_cons_of_mem f hb)))))
          exact ⟨es', pes', hmem', hc'⟩
        · exact ⟨es, p, hmem, fun as bs f he => hb ⟨as, f, bs, he⟩⟩
  intro es p hmem
  exact key es.length es (Nat.le_refl _) p hmem

/-- **A reduced trail in a forest uses each of its edges once.**  Two occurrences of one edge bound a
segment that is either itself a reduced closed trail (impossible in a forest) or empty, in which case
the two occurrences are adjacent, contradicting reducedness.  This is where "forest" is used: in a
graph with a cycle, a reduced trail can wind around the cycle and reuse an edge. -/
theorem IsForest.occur_once {T : Finset E} (hT : IsForest G T) {u w : V} {es : List E}
    (p : Path G u es w) (hmem : ∀ g ∈ es, g ∈ T) (hf : consecFree es) {f : E} (hfu : f ∈ es) :
    ∃ α β, es = α ++ f :: β ∧ (∀ x ∈ α, x ≠ f) ∧ f ∉ β := by
  classical
  obtain ⟨α, β, hab, hnoα⟩ := List.split_first es hfu
  refine ⟨α, β, hab, hnoα, ?_⟩
  by_cases hfb : f ∈ β
  · obtain ⟨γ, δ, hγδ, hnoγ⟩ := List.split_first β hfb
    have hkey : es = (α ++ [f]) ++ (γ ++ f :: δ) := by
      rw [hab, hγδ, List.append_assoc, List.singleton_append]
    have h1 : Path G u ((α ++ [f]) ++ (γ ++ f :: δ)) w := hkey ▸ p
    obtain ⟨y, pαf, prest⟩ := Path.split (α ++ [f]) u h1
    obtain ⟨x, pα, pf⟩ := Path.split α u pαf
    obtain ⟨z, pγ, pfd⟩ := Path.split γ y prest
    obtain ⟨r, pf2, pδ⟩ := Path.split [f] z (by rw [List.singleton_append]; exact pfd)
    -- the two crossings of `f` start at `x, z` and end at `y, r`
    have hx : (x = G.src f ∧ y = G.dst f) ∨ (x = G.dst f ∧ y = G.src f) :=
      Path.ends_of_singleton pf
    have hz : (z = G.src f ∧ r = G.dst f) ∨ (z = G.dst f ∧ r = G.src f) :=
      Path.ends_of_singleton pf2
    have hft : f ∈ T := hmem f (by rw [hab]; simp)
    have hcfγ : consecFree γ := (hkey ▸ hf).of_append_right.of_append_left
    have hmemγ : ∀ g ∈ γ, g ∈ T := by intro g hg; exact hmem g (by rw [hkey]; simp [hg])
    -- `γ ++ [f]` is also a contiguous sub-trail: it closes up at the far end of the first crossing
    have hkey2 : es = (α ++ [f]) ++ ((γ ++ [f]) ++ δ) := by
      rw [hkey]
      simp [List.append_assoc]
    have hcfγf : consecFree (γ ++ [f]) :=
      consecFree.of_sublist (l₁ := α ++ [f]) (l₂ := δ) (hkey2 ▸ hf)
    have hmemγf : ∀ h ∈ γ ++ [f], h ∈ T := by
      intro h hh
      rcases List.mem_append.mp hh with hγ | hf2
      · exact hmemγ h hγ
      · rw [List.mem_singleton] at hf2
        subst hf2
        exact hft
    rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · -- the crossings run the same way: `γ ++ [f]` is a reduced closed trail at `G.dst f`
        have hcl : Path G (G.dst f) (γ ++ [f]) (G.dst f) :=
          pγ.append [f] (G.dst f) (Path.edge f)
        have h0 : (γ ++ [f]) = [] :=
          hT.closed_consecFree (G.dst f) (γ ++ [f]) hcl hcfγf hmemγf
        exact absurd h0 (by simp)
      · -- the crossings are adjacent backtracks: `γ` is empty, so `f :: f` survives in `es`
        rw [hT.closed_consecFree (G.dst f) γ pγ hcfγ hmemγ, List.nil_append] at hγδ
        subst hγδ
        exact absurd hab (hf α δ f)
    · rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hT.closed_consecFree (G.src f) γ pγ hcfγ hmemγ, List.nil_append] at hγδ
        subst hγδ
        exact absurd hab (hf α δ f)
      · have hcl : Path G (G.src f) (γ ++ [f]) (G.src f) :=
          pγ.append [f] (G.src f) (Path.edge_rev f)
        have h0 : (γ ++ [f]) = [] :=
          hT.closed_consecFree (G.src f) (γ ++ [f]) hcl hcfγf hmemγf
        exact absurd h0 (by simp)
  · exact hfb

/-- **Every edge of a reduced forest trail is a cut of its own endpoints.**  Deleting it from the
forest separates the trail's start from its end.  This is the lemma that lets a greedy step replace
the edge it *chose* rather than an arbitrary one: the edge being exchanged must be on the trail, and
here any edge on the trail will do.  Without reducedness the statement is false — a trail that
wanders out and back over one edge contains edges that are not on the shortcut. -/
theorem IsForest.sep_of_mem_trail {T : Finset E} (hT : IsForest G T) {u v : V} {es : List E}
    (p : Path G u es v) (hmem : ∀ g ∈ es, g ∈ T) (hf : consecFree es) {f : E} (hfu : f ∈ es) :
    ¬ Conn G (T.erase f) u v := by
  classical
  intro hconn
  obtain ⟨α, β, hab, hnoα, hnoβ⟩ := hT.occur_once p hmem hf hfu
  obtain ⟨x, pα, prest⟩ := Path.split α u (hab ▸ p)
  obtain ⟨y, pf, pβ⟩ := Path.split [f] x (by rw [List.singleton_append]; exact prest)
  have hα : ∀ g ∈ α, g ∈ T.erase f := by
    intro g hg
    exact Finset.mem_erase.mpr ⟨fun he => hnoα g hg he, hmem g (by rw [hab]; simp [hg])⟩
  have hβ : ∀ g ∈ β, g ∈ T.erase f := by
    intro g hg
    exact Finset.mem_erase.mpr ⟨fun he => hnoβ (he ▸ hg), hmem g (by rw [hab]; simp [hg])⟩
  have hux : Conn G (T.erase f) u x := conn_of_path pα hα
  have hyv : Conn G (T.erase f) y v := conn_of_path pβ hβ
  have hft : f ∈ T := hmem f (by rw [hab]; simp)
  rcases Path.ends_of_singleton pf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd (hux.symm.trans (hconn.trans hyv.symm)) (hT.bridge hft)
  · exact absurd (hyv.trans (hconn.symm.trans hux)) (hT.bridge hft)

/-- An empty trail ends where it starts. -/
theorem Path.nil_eq {u v : V} (p : Path G u [] v) : u = v := by
  cases p with
  | nil x => rfl

/-- **Path uniqueness, as an equality of trails.**  Two reduced trails in a forest with the same
endpoints are the same list of edges, traversed the same way.

No occurrence-count bookkeeping is needed; the three lemmas above already decide it.  Induct on the
first trail.  If it is empty the second is a reduced closed trail, hence empty.  Otherwise both
trails leave `u` along the same edge: were the second to start with a different edge `f`, that edge
would lead into `e` (the first edge of the first trail), and the stretch before `e` would either be a
non-empty reduced closed trail at `u`, or join `u` to the far end of `e` without using `e` — which
`sep_of_mem_trail` forbids.  The two first steps then run in the same direction (otherwise `e` would
be a self-loop), and the induction hypothesis applies to the tails. -/
theorem IsForest.trail_eq {T : Finset E} (hT : IsForest G T) :
    ∀ (es fs : List E) (u v : V), Path G u es v → Path G u fs v →
      (∀ g ∈ es, g ∈ T) → (∀ g ∈ fs, g ∈ T) → consecFree es → consecFree fs → es = fs := by
  classical
  intro es
  induction es with
  | nil =>
      intro fs u v p q hmem hmemf hf hff
      have huv : u = v := p.nil_eq
      subst huv
      exact (hT.closed_consecFree _ fs q hff hmemf).symm
  | cons e es ih =>
      intro fs u v p q hmem hmemf hf hff
      cases fs with
      | nil =>
          have huv : u = v := q.nil_eq
          subst huv
          exact hT.closed_consecFree _ (e :: es) p hf hmem
      | cons f fs =>
          have heT : e ∈ T := hmem e List.mem_cons_self
          have hne : G.src e ≠ G.dst e := hT.nloop heT
          -- `e` is used once by each trail
          have hnoes : e ∉ es := by
            obtain ⟨α', β', hab', hnoα', hnoβ'⟩ :=
              hT.occur_once p hmem hf List.mem_cons_self
            cases α' with
            | nil =>
                rw [List.nil_append] at hab'
                rw [(List.cons.inj hab').2]
                exact hnoβ'
            | cons a as =>
                rw [List.cons_append] at hab'
                exact absurd (List.cons.inj hab').1.symm (hnoα' a List.mem_cons_self)
          obtain ⟨w, pe1, pes⟩ := Path.split [e] u (by rw [List.singleton_append]; exact p)
          have hwv : Conn G (T.erase e) w v :=
            conn_of_path pes fun g hg =>
              Finset.mem_erase.mpr ⟨fun he => hnoes (he ▸ hg), hmem g (List.mem_cons_of_mem e hg)⟩
          have heq : e = f := by
            by_contra hnef
            have hsep : ¬ Conn G (T.erase e) u v :=
              hT.sep_of_mem_trail p hmem hf List.mem_cons_self
            -- a `u`–`v` trail avoiding `e` would connect them inside `T.erase e`
            have hein : e ∈ (f :: fs) := by
              by_contra h
              exact hsep (conn_of_path q fun g hg =>
                Finset.mem_erase.mpr ⟨fun hge => h (hge ▸ hg), hmemf g hg⟩)
            obtain ⟨α, β, hab, hnoα, hnoβ⟩ := hT.occur_once q hmemf hff hein
            rw [hab] at hff hmemf q
            cases α with
            | nil =>
                rw [List.nil_append] at hab
                exact hnef (List.cons.inj hab).1.symm
            | cons a as =>
                have hcfα : consecFree (a :: as) :=
                  consecFree.of_append_left (fs := e :: β) hff
                have hmemα : ∀ g ∈ (a :: as), g ∈ T := fun g hg =>
                  hmemf g (List.mem_append.mpr (Or.inl hg))
                have hmemβ : ∀ g ∈ β, g ∈ T := fun g hg =>
                  hmemf g (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem e hg)))
                obtain ⟨x, pα, prest⟩ := Path.split (a :: as) u q
                obtain ⟨y, pe, pβ⟩ := Path.split [e] x (by
                  rw [List.singleton_append]; exact prest)
                have hux : Conn G (T.erase e) u x :=
                  conn_of_path pα fun g hg =>
                    Finset.mem_erase.mpr ⟨hnoα g hg, hmemα g hg⟩
                have hyv : Conn G (T.erase e) y v :=
                  conn_of_path pβ fun g hg =>
                    Finset.mem_erase.mpr ⟨fun heg => hnoβ (heg ▸ hg), hmemβ g hg⟩
                rcases Path.ends_of_singleton pe1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · rcases Path.ends_of_singleton pe with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                  · exact absurd (hT.closed_consecFree (G.src e) (a :: as) pα hcfα hmemα)
                      (by simp)
                  · exact hsep (hux.trans hwv)
                · rcases Path.ends_of_singleton pe with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                  · exact hsep (hux.trans hwv)
                  · exact absurd (hT.closed_consecFree (G.dst e) (a :: as) pα hcfα hmemα)
                      (by simp)
          -- the two trails leave `u` along the same edge, and in the same direction
          rw [← heq] at q hmemf hff ⊢
          refine congrArg (List.cons e) ?_
          cases p with
          | fwd _ hs hd pes =>
              rw [← hd] at pes
              cases q with
              | fwd _ _ qhd qes =>
                  rw [← qhd] at qes
                  exact ih fs (G.dst e) v pes qes (fun g hg => hmem g (List.mem_cons_of_mem e hg))
                    (fun g hg => hmemf g (List.mem_cons_of_mem e hg))
                    (consecFree.of_append_right (es := [e]) hf)
                    (consecFree.of_append_right (es := [e]) hff)
              | bwd _ qhd _ qes => exact absurd (hs.trans qhd.symm) hne
          | bwd _ hd hs pes =>
              rw [← hs] at pes
              cases q with
              | fwd _ qhs _ qes => exact absurd (hd.trans qhs.symm).symm hne
              | bwd _ _ qhs qes =>
                  rw [← qhs] at qes
                  exact ih fs (G.src e) v pes qes (fun g hg => hmem g (List.mem_cons_of_mem e hg))
                    (fun g hg => hmemf g (List.mem_cons_of_mem e hg))
                    (consecFree.of_append_right (es := [e]) hf)
                    (consecFree.of_append_right (es := [e]) hff)

/-- **The greedy step preserves extendability to a minimum spanning forest.**  This is the lemma the
paper uses at every Borůvka and Kruskal step and never states: if `F` is the partial solution, `T` a
minimum spanning forest containing it, and `e` a lightest edge whose two ends are not yet joined by
`F` (Kruskal's acceptance test, together with the weight minimality that scanning the edges in sorted
order gives at that moment), then some MSF contains `insert e F`.

The three requirements on the exchanged edge pull apart, and each comes from a different lemma:
* `g ∉ F` and `G.weight e ≤ G.weight g`: `g` crosses the cut of `e`'s `F`-component
  (`Path.crossing`), so `F` does not join its ends, which is both what makes it exchangeable and what
  makes `e` at most as light as it;
* `¬ Conn G (T.erase g) (G.src e) (G.dst e)`: `g` lies on a reduced `T`-trail between the ends of `e`
  (`sep_of_mem_trail`) — the step that needs the path-uniquness machinery of this file;
* the weight comparison then hands the swap to `isMSF_exchange` in `Exchange.lean`. -/
theorem kruskal_step {F : Finset E} (T : Finset E) (hT : IsMSF G T)
    (hsub : F ⊆ T) {e : E} (hconn : ¬ Conn G F (G.src e) (G.dst e))
    (hmin : ∀ f, ¬ Conn G F (G.src f) (G.dst f) → G.weight e ≤ G.weight f) :
    ∃ T', IsMSF G T' ∧ insert e F ⊆ T' := by
  classical
  obtain ⟨hTf, hTsp⟩ := hT.1
  have hne : G.src e ≠ G.dst e := fun he => hconn (he ▸ Conn.refl (G.src e))
  have heF : e ∉ F := fun hf => hconn (Conn.step e hf)
  -- the `T`-trail between the ends of `e`, reduced so that each of its edges is used once
  obtain ⟨es0, p0, hmem0⟩ := path_of_conn (hTsp e hne)
  obtain ⟨es, p, hmem, hf⟩ := hTf.exists_consecFree_trail es0 p0 hmem0
  -- an edge of that trail crossing the `F`-component of `G.src e`
  let S : Set V := { x | Conn G F (G.src e) x }
  obtain ⟨g, hg, hcr⟩ : ∃ g ∈ es, (G.src g ∈ S ∧ G.dst g ∉ S) ∨ (G.src g ∉ S ∧ G.dst g ∈ S) :=
    crossing p S (Conn.refl (G.src e)) hconn
  have hgF : ¬ Conn G F (G.src g) (G.dst g) := by
    rcases hcr with ⟨hs, hd⟩ | ⟨hs, hd⟩
    · exact fun hh => hd (hs.trans hh)
    · exact fun hh => hs (hd.trans hh.symm)
  have hgnotF : g ∉ F := fun hgf => hgF (Conn.step g hgf)
  have hgT : g ∈ T := hmem g hg
  have hsep : ¬ Conn G (T.erase g) (G.src e) (G.dst e) := hTf.sep_of_mem_trail p hmem hf hg
  refine ⟨insert e (T.erase g), isMSF_exchange hT hgT hsep (hmin g hgF), ?_⟩
  intro x hx
  rcases Finset.mem_insert.mp hx with hx_eq | hxF
  · rw [hx_eq]
    exact Finset.mem_insert_self _ _
  · refine Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun hxg => absurd (hxg ▸ hxF) hgnotF, ?_⟩)
    exact hsub hxF

/-- Forestness survives the greedy step, so `kruskal_step` really does grow a partial solution. -/
theorem kruskal_step_isForest {F : Finset E} (hF : IsForest G F) {e : E}
    (hconn : ¬ Conn G F (G.src e) (G.dst e)) : IsForest G (insert e F) :=
  hF.insert (fun he => hconn (he ▸ Conn.refl (G.src e))) hconn

end DLMST
