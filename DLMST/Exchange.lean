import DLMST.Path

/-!
# The exchange argument the paper relies on and never proves

Everything in `MsfKernel.lean` and `Path.lean` is background.  This file is the real MST theory: the
fact that makes Kruskal/Borůvka-style exchanges work, and which the paper uses in §2 (the
certificate procedure's `U(F)`), §3 (rerouting through `T`-paths) and §4 (the Borůvka phases "do not
create a cycle and do not lose optimality") without ever proving it.

Two structural lemmas open the file:

* `conn_insert_sep` — if `F` does not join the ends of `e`, then any trail inside `insert e F` is an
  `F`-trail, or it goes through `e` exactly once, entering at one end and leaving at the other.
  The hypothesis is what kills the backtracking cases: a trail that crossed `e` twice would join its
  ends inside `F`.
* `IsForest.bridge` — every edge of a forest is a bridge, i.e. deleting it disconnects its own two
  endpoints.  This is the lemma whose absence I flagged earlier; it follows from `conn_insert_sep`
  by induction over the construction of the forest.

From them, in order: `bridge_sides` (the two ends of a bridge are the two sides of its cut),
`reroute` / `conn_erase_insert` (no connection is lost when a bridge is traded for an edge that its
own deletion separates), `exists_sep_edge` (a `T`-path really does contain an edge whose removal
separates its ends — so "remove an edge of the `T`-path" is not vacuous), and
`isSpanningForest_exchange` / `exists_spanning_exchange` (the exchange yields another spanning
forest).

The payoffs are the paper's own claims:

* `msf_lightest_bridge` + `wsum_exchange` — a minimum spanning forest edge `f` is no heavier than
  any edge whose endpoints `T - f` does not join.  That is the §2 certificate's correctness in one
  line, and `msf_reject_min` restates it with the paper's `U(F)` = `reject G F`.
* `not_msf_of_lighter` — the cycle property.
* `isMSF_exchange` / `isMSF_exchange_iff` — §4's "does not lose optimality": trading a tree edge for
  a no-heavier one gives another *minimum* spanning forest, and that happens exactly when the new
  edge is no heavier than the old.
* `exists_msf_with_lighter` — if `e` is lightest among the tree edges whose deletion separates its
  ends, then some exchange produces a minimum spanning forest containing `e`.

What is *not* here: that the edge a greedy step wants to add can be paired with an edge that both
crosses the component cut and separates the ends.  `exists_sep_edge` supplies a separating edge and
`Path.crossing_of_conn` a cut-crossing one, but they need not be the same edge unless trails in a
forest do not repeat an edge.  That identification — the backtrack-free walk surgery and the
`kruskal_step` built on it — is the content of `Tree.lean`; this file stops at the single-edge
exchange, including its optimality.
-/

namespace DLMST

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] {G : WGraph V E}

/-- **Two sides or none.**  Let `F` miss a connection between the ends of `e`.  A trail all of whose
edges are `e` or members of `F` either already is an `F`-trail, or enters `e` at one end and leaves
at the other. -/
theorem conn_insert_sep {F : Finset E} {e : E} {u v : V} {es : List E}
    (hsep : ¬ Conn G F (G.src e) (G.dst e)) (p : Path G u es v)
    (hmem : ∀ g ∈ es, g = e ∨ g ∈ F) :
    Conn G F u v
    ∨ (Conn G F u (G.src e) ∧ Conn G F (G.dst e) v)
    ∨ (Conn G F u (G.dst e) ∧ Conn G F (G.src e) v) := by
  classical
  induction p with
  | nil x => exact Or.inl (Conn.refl x)
  | fwd a has had _ ih =>
      rcases hmem a (by simp) with heq | haF
      · -- the head edge is the one that was inserted: it can be crossed only once, because
        -- crossing it twice would join its ends inside `F`
        subst heq
        rcases ih (fun g hg => hmem g (by simp [hg])) with h1 | ⟨h2a, h2b⟩ | ⟨h3a, h3b⟩
        · rw [← had] at h1
          refine Or.inr (Or.inl ⟨?_, h1⟩)
          rw [← has]
          exact Conn.refl _
        · rw [← had] at h2a
          exact absurd h2a.symm hsep
        · rw [← has]
          exact Or.inl h3b
      · -- the head edge already lies in `F`: glue it onto whatever the tail does
        have haf : Conn G F (G.src a) (G.dst a) := conn_of_mem haF
        rw [← has]
        have hih := ih (fun g hg => hmem g (by simp [hg]))
        rw [← had] at hih
        rcases hih with h1 | ⟨h2a, h2b⟩ | ⟨h3a, h3b⟩
        · exact Or.inl (Conn.trans haf h1)
        · exact Or.inr (Or.inl ⟨Conn.trans haf h2a, h2b⟩)
        · exact Or.inr (Or.inr ⟨Conn.trans haf h3a, h3b⟩)
  | bwd a hd has _ ih =>
      rcases hmem a (by simp) with heq | haF
      · subst heq
        rcases ih (fun g hg => hmem g (by simp [hg])) with h1 | ⟨h2a, h2b⟩ | ⟨h3a, h3b⟩
        · rw [← has] at h1
          refine Or.inr (Or.inr ⟨?_, h1⟩)
          rw [← hd]
          exact Conn.refl _
        · rw [← hd]
          exact Or.inl h2b
        · rw [← has] at h3a
          exact absurd h3a hsep
      · have haf : Conn G F (G.dst a) (G.src a) := (conn_of_mem haF).symm
        rw [← hd]
        have hih := ih (fun g hg => hmem g (by simp [hg]))
        rw [← has] at hih
        rcases hih with h1 | ⟨h2a, h2b⟩ | ⟨h3a, h3b⟩
        · exact Or.inl (Conn.trans haf h1)
        · exact Or.inr (Or.inl ⟨Conn.trans haf h2a, h2b⟩)
        · exact Or.inr (Or.inr ⟨Conn.trans haf h3a, h3b⟩)

/-- The `Conn`-level form: an `insert e F`-connection is an `F`-connection or a single crossing. -/
theorem conn_insert_sep_conn {F : Finset E} {e : E} {u v : V}
    (hsep : ¬ Conn G F (G.src e) (G.dst e)) (h : Conn G (insert e F) u v) :
    Conn G F u v
    ∨ (Conn G F u (G.src e) ∧ Conn G F (G.dst e) v)
    ∨ (Conn G F u (G.dst e) ∧ Conn G F (G.src e) v) := by
  obtain ⟨es, pes, hmem⟩ := path_of_conn h
  refine conn_insert_sep hsep pes ?_
  intro g hg
  exact (Finset.mem_insert.mp (hmem g hg))

/-- Erasing an edge from the set it was just inserted into leaves the original set behind. -/
theorem erase_insert_subset (F : Finset E) (e : E) : (insert e F).erase e ⊆ F := by
  intro x hx
  obtain ⟨hxne, hx1⟩ := Finset.mem_erase.mp hx
  rcases Finset.mem_insert.mp hx1 with hxh | hxF
  · exact absurd hxh hxne
  · exact hxF

/-- **Every edge of a forest is a bridge.**  Deleting an edge of a forest separates its endpoints.
The paper relies on this whenever it removes an edge from a `T`-path, and never states it. -/
theorem IsForest.bridge {F : Finset E} (hF : IsForest G F) {f : E} (hf : f ∈ F) :
    ¬ Conn G (F.erase f) (G.src f) (G.dst f) := by
  classical
  induction hF with
  | empty => exact absurd hf (by simp)
  | @add Fsub esub hF hne hc ih =>
      intro hconn
      rcases Finset.mem_insert.mp hf with hef | haF
      · -- `f` is the edge added last: erasing it leaves a subset of `Fsub`, and nothing connects
        -- the endpoints of the deleted edge inside that subset
        rw [hef] at hconn
        exact absurd hconn (fun hh => hc (hh.mono (erase_insert_subset Fsub esub)))
      · -- `f` is older: `esub` is a bridge over `Fsub - f`, and a crossing of it is impossible
        have hsub : Fsub.erase f ⊆ Fsub := Finset.erase_subset f Fsub
        have hsep : ¬ Conn G (Fsub.erase f) (G.src esub) (G.dst esub) :=
          fun hh => hc (hh.mono hsub)
        obtain ⟨es, pes, hmem⟩ := path_of_conn hconn
        have hmem2 : ∀ g ∈ es, g = esub ∨ g ∈ Fsub.erase f := by
          intro g hg
          obtain ⟨hgnf, hx1⟩ := Finset.mem_erase.mp (hmem g hg)
          rcases Finset.mem_insert.mp hx1 with hge | hgF
          · exact Or.inl hge
          · exact Or.inr (Finset.mem_erase.mpr ⟨hgnf, hgF⟩)
        rcases conn_insert_sep hsep pes hmem2 with h1 | ⟨h2a, h2b⟩ | ⟨h3a, h3b⟩
        · exact absurd h1 (ih haF)
        · exact absurd
            (Conn.trans (Conn.symm (h2a.mono hsub))
              (Conn.trans (conn_of_mem haF) (Conn.symm (h2b.mono hsub)))) hc
        · exact absurd
            (Conn.trans (h3b.mono hsub)
              (Conn.trans (Conn.symm (conn_of_mem haF)) (h3a.mono hsub))) hc

/-- Nothing but reflexivity connects two vertices inside the empty edge set. -/
theorem conn_empty_eq {u v : V} (h : Conn G (∅ : Finset E) u v) : u = v := by
  induction h with
  | refl x => rfl
  | step e he => exact absurd he (by simp)
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- Putting back the edge just erased restores the set. -/
theorem insert_erase_eq {T : Finset E} {f : E} (hf : f ∈ T) : insert f (T.erase f) = T := by
  apply Finset.ext
  intro x
  constructor
  · intro hx
    rcases Finset.mem_insert.mp hx with he | h2
    · exact he ▸ hf
    · exact (Finset.mem_erase.mp h2).2
  · intro hx
    by_cases hxe : x = f
    · exact Finset.mem_insert.mpr (Or.inl hxe)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨hxe, hx⟩))

/-- **The sides of a bridge.**  Deleting the bridge `f` leaves two sides, and the ends of any edge
that `f` separates sit one on each side. -/
theorem bridge_sides {T : Finset E} (hT : IsForest G T) {f : E} (hf : f ∈ T) {u v : V}
    (huv : Conn G T u v) (hsep : ¬ Conn G (T.erase f) u v) :
    (Conn G (T.erase f) u (G.src f) ∧ Conn G (T.erase f) (G.dst f) v)
    ∨ (Conn G (T.erase f) u (G.dst f) ∧ Conn G (T.erase f) (G.src f) v) := by
  classical
  have hbf : ¬ Conn G (T.erase f) (G.src f) (G.dst f) := hT.bridge hf
  have h1 : Conn G (insert f (T.erase f)) u v := by
    rw [insert_erase_eq hf]
    exact huv
  rcases conn_insert_sep_conn hbf h1 with h2 | ⟨h3a, h3b⟩ | ⟨h4a, h4b⟩
  · exact absurd h2 hsep
  · exact Or.inl ⟨h3a, h3b⟩
  · exact Or.inr ⟨h4a, h4b⟩

/-- **Rerouting, first alignment.** -/
theorem reroute {T : Finset E} {f e : E} {u v : V}
    (h1 : Conn G (T.erase f) u (G.src f)) (h2 : Conn G (T.erase f) (G.dst f) v)
    (a : (Conn G (T.erase f) (G.src e) (G.src f)
          ∧ Conn G (T.erase f) (G.dst f) (G.dst e))
      ∨ (Conn G (T.erase f) (G.src e) (G.dst f)
          ∧ Conn G (T.erase f) (G.src f) (G.dst e))) :
    Conn G (insert e (T.erase f)) u v := by
  have sub : T.erase f ⊆ insert e (T.erase f) := Finset.subset_insert e (T.erase f)
  have he : Conn G (insert e (T.erase f)) (G.src e) (G.dst e) :=
    Conn.step e (Finset.mem_insert_self e (T.erase f))
  rcases a with ⟨b1, b2⟩ | ⟨c1, c2⟩
  · exact Conn.trans (h1.mono sub)
      (Conn.trans (Conn.symm (b1.mono sub))
        (Conn.trans he (Conn.trans (Conn.symm (b2.mono sub)) (h2.mono sub))))
  · exact Conn.trans (h1.mono sub)
      (Conn.trans (c2.mono sub)
        (Conn.trans (Conn.symm he) (Conn.trans (c1.mono sub) (h2.mono sub))))

/-- **Rerouting, second alignment.** -/
theorem reroute' {T : Finset E} {f e : E} {u v : V}
    (h1 : Conn G (T.erase f) u (G.dst f)) (h2 : Conn G (T.erase f) (G.src f) v)
    (a : (Conn G (T.erase f) (G.src e) (G.src f)
          ∧ Conn G (T.erase f) (G.dst f) (G.dst e))
      ∨ (Conn G (T.erase f) (G.src e) (G.dst f)
          ∧ Conn G (T.erase f) (G.src f) (G.dst e))) :
    Conn G (insert e (T.erase f)) u v := by
  have sub : T.erase f ⊆ insert e (T.erase f) := Finset.subset_insert e (T.erase f)
  have he : Conn G (insert e (T.erase f)) (G.src e) (G.dst e) :=
    Conn.step e (Finset.mem_insert_self e (T.erase f))
  rcases a with ⟨b1, b2⟩ | ⟨c1, c2⟩
  · exact Conn.trans (h1.mono sub)
      (Conn.trans (b2.mono sub)
        (Conn.trans (Conn.symm he)
          (Conn.trans (b1.mono sub) (h2.mono sub))))
  · exact Conn.trans (h1.mono sub)
      (Conn.trans (Conn.symm (c1.mono sub))
        (Conn.trans he (Conn.trans (Conn.symm (c2.mono sub)) (h2.mono sub))))

/-- **Every connection survives the exchange.**  Replace an edge `f` of the forest `T` by an edge
`e` whose endpoints `T - f` separates: nothing that used to be joined comes apart. -/
theorem conn_erase_insert {T : Finset E} (hT : IsForest G T) {f e : E} (hf : f ∈ T)
    (hef : Conn G T (G.src e) (G.dst e))
    (hsep : ¬ Conn G (T.erase f) (G.src e) (G.dst e))
    {u v : V} (huv : Conn G T u v) : Conn G (insert e (T.erase f)) u v := by
  classical
  have a := bridge_sides hT hf hef hsep
  have hbf : ¬ Conn G (T.erase f) (G.src f) (G.dst f) := hT.bridge hf
  have hsub : T ⊆ insert f (T.erase f) := by
    rw [insert_erase_eq hf]
  rcases conn_insert_sep_conn hbf (huv.mono hsub) with h1 | ⟨h2a, h2b⟩ | ⟨h3a, h3b⟩
  · exact h1.mono (Finset.subset_insert e (T.erase f))
  · exact reroute h2a h2b a
  · exact reroute' h3a h3b a

/-- **A `T`-path contains an edge whose deletion separates its ends.**  This is what lets an
exchange argument speak about *the* edge to remove. -/
theorem exists_sep_edge {T : Finset E} (hT : IsForest G T) {u v : V} (huv : u ≠ v)
    (hconn : Conn G T u v) : ∃ f ∈ T, ¬ Conn G (T.erase f) u v := by
  classical
  refine by_contra fun hna => huv ?_
  push Not at hna
  induction hT with
  | empty => exact conn_empty_eq hconn
  | @add T₀ e₀ hT₀ hne hc ih =>
      have hT₀uv : Conn G T₀ u v :=
        (hna e₀ (Finset.mem_insert_self e₀ T₀)).mono (erase_insert_subset T₀ e₀)
      have hall₀ : ∀ f ∈ T₀, Conn G (T₀.erase f) u v := by
        intro f hf
        have hsub2 : (insert e₀ T₀).erase f ⊆ insert e₀ (T₀.erase f) := by
          intro x hx
          obtain ⟨hxne, hx1⟩ := Finset.mem_erase.mp hx
          rcases Finset.mem_insert.mp hx1 with he | hT
          · exact Finset.mem_insert.mpr (Or.inl he)
          · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨hxne, hT⟩))
        have h1 : Conn G (insert e₀ (T₀.erase f)) u v :=
          (hna f (Finset.mem_insert.mpr (Or.inr hf))).mono hsub2
        have hsep : ¬ Conn G (T₀.erase f) (G.src e₀) (G.dst e₀) :=
          fun hh => hc (hh.mono (Finset.erase_subset f T₀))
        have es : T₀.erase f ⊆ T₀ := Finset.erase_subset f T₀
        rcases conn_insert_sep_conn hsep h1 with h2 | ⟨h3a, h3b⟩ | ⟨h4a, h4b⟩
        · exact h2
        · exact absurd
            (Conn.trans (Conn.symm (h3a.mono es))
              (Conn.trans hT₀uv (Conn.symm (h3b.mono es)))) hc
        · exact absurd
            (Conn.symm (Conn.trans (Conn.symm (h4a.mono es))
              (Conn.trans hT₀uv (Conn.symm (h4b.mono es))))) hc
      exact ih hT₀uv hall₀

/-- **The exchange.**  Replacing an edge of a spanning forest by an edge whose endpoints the forest
minus that edge separates gives another spanning forest.  This is the "remove an edge of the
`T`-path, insert the new edge" step of the paper, §3 and §4. -/
theorem isSpanningForest_exchange {T : Finset E} (hT : IsSpanningForest G T) {f e : E}
    (hf : f ∈ T) (hsep : ¬ Conn G (T.erase f) (G.src e) (G.dst e)) :
    IsSpanningForest G (insert e (T.erase f)) := by
  classical
  obtain ⟨hTf, hTsp⟩ := hT
  have hne : G.src e ≠ G.dst e := fun h => hsep (by rw [h]; exact Conn.refl _)
  refine ⟨IsForest.add (hTf.hereditary _ (Finset.erase_subset f T)) hne hsep, ?_⟩
  intro g hg
  exact conn_erase_insert hTf hf (hTsp e hne) hsep (hTsp g hg)

/-- Weight bookkeeping of the exchange. -/
theorem wsum_exchange {T : Finset E} {f e : E} (hf : f ∈ T) (he : e ∉ T.erase f) :
    wsum G (insert e (T.erase f)) = wsum G T - G.weight f + G.weight e := by
  have h1 : wsum G (insert e (T.erase f)) = G.weight e + wsum G (T.erase f) := by
    show (insert e (T.erase f)).sum G.weight = _
    rw [Finset.sum_insert he]
    rfl
  have h2 : wsum G T = G.weight f + wsum G (T.erase f) := by
    have h : wsum G (insert f (T.erase f)) = G.weight f + wsum G (T.erase f) := by
      show (insert f (T.erase f)).sum G.weight = _
      rw [Finset.sum_insert (fun hx => (Finset.mem_erase.mp hx).1 rfl)]
      rfl
    rw [insert_erase_eq hf] at h
    exact h
  rw [h1, h2]
  ring

/-- **Cut/cycle property, in the paper's `U(F)` form.**  Let `T` be a minimum spanning forest and
`f` one of its edges.  Then `f` is no heavier than any edge whose endpoints `T - f` does not join.
§2 uses exactly this to argue that the rejected set `U(F)` excludes only edges that genuinely
compete with a tree edge, and never proves it. -/
theorem msf_lightest_bridge {T : Finset E} (hT : IsMSF G T) {f e : E} (hf : f ∈ T)
    (hsep : ¬ Conn G (T.erase f) (G.src e) (G.dst e)) : G.weight f ≤ G.weight e := by
  classical
  obtain ⟨hTsp, hTmin⟩ := hT
  have hge : wsum G T ≤ wsum G (insert e (T.erase f)) :=
    hTmin _ (isSpanningForest_exchange hTsp hf hsep)
  rw [wsum_exchange hf (not_mem_of_not_conn hsep)] at hge
  linarith

/-- **Cycle property.**  No edge strictly lighter than a bridge edge of an MSF exists. -/
theorem not_msf_of_lighter {T : Finset E} (hT : IsMSF G T) {f e : E} (hf : f ∈ T)
    (hsep : ¬ Conn G (T.erase f) (G.src e) (G.dst e)) (hw : G.weight e < G.weight f) : False := by
  classical
  have hle := msf_lightest_bridge hT hf hsep
  linarith

/-- **The exchange keeps a *minimum* spanning forest, provided the new edge is no heavier.**
This is §4's "does not lose optimality", for one edge at a time: the forestness half is
`isSpanningForest_exchange`, and the weight bookkeeping is `wsum_exchange`. -/
theorem isMSF_exchange {T : Finset E} (hT : IsMSF G T) {f e : E} (hf : f ∈ T)
    (hsep : ¬ Conn G (T.erase f) (G.src e) (G.dst e)) (hwe : G.weight e ≤ G.weight f) :
    IsMSF G (insert e (T.erase f)) := by
  classical
  obtain ⟨hTsp, hTmin⟩ := hT
  have hT' : IsSpanningForest G (insert e (T.erase f)) := isSpanningForest_exchange hTsp hf hsep
  refine ⟨hT', ?_⟩
  intro F' hF'
  have hge : wsum G T ≤ wsum G F' := hTmin F' hF'
  have hle : wsum G (insert e (T.erase f)) ≤ wsum G T := by
    rw [wsum_exchange hf (not_mem_of_not_conn hsep)]
    linarith
  have he : wsum G T = wsum G (insert e (T.erase f)) :=
    le_antisymm (hTmin _ hT') hle
  exact he ▸ hge

/-- **Characterisation.**  For a minimum spanning forest `T`, an edge `f` of `T` and an edge `e`
that `T - f` separates, the exchange is minimum **exactly when** `e` is no heavier than `f`.
Together with `msf_lightest_bridge` this says the exchange is minimum iff `e` is a lightest member
of the fundamental cut of `f`. -/
theorem isMSF_exchange_iff {T : Finset E} (hT : IsMSF G T) {f e : E} (hf : f ∈ T)
    (hsep : ¬ Conn G (T.erase f) (G.src e) (G.dst e)) :
    IsMSF G (insert e (T.erase f)) ↔ G.weight e ≤ G.weight f := by
  classical
  constructor
  · -- the exchanged forest is minimum, so its weight cannot exceed the original one's
    intro hT'
    obtain ⟨hTspT, _⟩ := hT
    obtain ⟨_, hmin'⟩ := hT'
    have := hmin' T hTspT
    rw [wsum_exchange hf (not_mem_of_not_conn hsep)] at this
    linarith
  · intro hwe
    exact isMSF_exchange hT hf hsep hwe

/-- **No cheaper edge crosses a fundamental cut.**  Restated: if `e` beats `f` then it cannot be
separated by `f`, i.e. the lightest edge across the cut of `T - f` *is* `f` itself. -/
theorem msf_lightest_of_lighter {T : Finset E} (hT : IsMSF G T) {f e : E} (hf : f ∈ T)
    (hsep : ¬ Conn G (T.erase f) (G.src e) (G.dst e)) :
    G.weight e < G.weight f → False := by
  intro hw
  exact not_msf_of_lighter hT hf hsep hw

/-- **The greedy step, as far as it goes without path uniqueness.**  Let `T` be a minimum spanning
forest and `e` an edge outside it.  Among the tree edges whose deletion separates the ends of `e`
(there is at least one, by `exists_sep_edge`), if `e` is lightest then some exchange puts `e` into a
minimum spanning forest.  This is §4's "a Borůvka phase does not lose optimality" one edge at a
time; the paper's version quantifies over a lightest edge *leaving a component*, which needs the
identification of component cuts with fundamental cuts, i.e. the missing uniqueness lemma. -/
theorem exists_msf_with_lighter {T : Finset E} (hT : IsMSF G T) {e : E}
    (hne : G.src e ≠ G.dst e)
    (hmin : ∀ f ∈ T, ¬ Conn G (T.erase f) (G.src e) (G.dst e) → G.weight e ≤ G.weight f) :
    ∃ f ∈ T, IsMSF G (insert e (T.erase f)) := by
  classical
  obtain ⟨⟨hTf, hTsp⟩, hTmin⟩ := hT
  obtain ⟨f, hf, hsep⟩ := exists_sep_edge hTf hne (hTsp e hne)
  exact ⟨f, hf, isMSF_exchange ⟨⟨hTf, hTsp⟩, hTmin⟩ hf hsep (hmin f hf hsep)⟩

/-- **Any edge can be swapped in.**  Given a spanning forest and any non-loop edge, some edge of
the forest can be removed to make room for it: the "still a spanning forest" half of the paper's
rerouting step. -/
theorem exists_spanning_exchange {T : Finset E} (hT : IsSpanningForest G T) {e : E}
    (he : G.src e ≠ G.dst e) : ∃ f ∈ T, IsSpanningForest G (insert e (T.erase f)) := by
  classical
  by_cases heT : e ∈ T
  · refine ⟨e, heT, ?_⟩
    rw [insert_erase_eq heT]
    exact hT
  · obtain ⟨hTf, hTsp⟩ := hT
    have hconn : Conn G T (G.src e) (G.dst e) := hTsp e he
    obtain ⟨f, hf, hsep⟩ := exists_sep_edge hTf he hconn
    exact ⟨f, hf, isSpanningForest_exchange ⟨hTf, hTsp⟩ hf hsep⟩

/-- The paper's rejection set `U(F)`: the edges whose endpoints `F` does not join. -/
noncomputable def reject (G : WGraph V E) (F : Finset E) : Finset E :=
  @Finset.filter E (fun e => ¬ Conn G F (G.src e) (G.dst e))
    (fun _e => Classical.propDecidable _) Finset.univ

theorem mem_reject {F : Finset E} {e : E} : e ∈ reject G F ↔ ¬ Conn G F (G.src e) (G.dst e) := by
  classical
  simp [reject]

/-- **§2's certificate invariant.**  Each MSF edge is a lightest member of the rejection set its
own deletion defines. -/
theorem msf_reject_min {T : Finset E} (hT : IsMSF G T) (f : E) (hf : f ∈ T) :
    ∀ e ∈ reject G (T.erase f), G.weight f ≤ G.weight e := by
  classical
  intro e he
  exact msf_lightest_bridge hT hf (mem_reject.mp he)

end DLMST
