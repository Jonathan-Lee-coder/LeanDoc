import DLMST.Exchange

/-!
# A forest on `n` vertices has at most `n - 1` edges

Lemma 3.1 (and the paragraph after Theorem 4.1) uses "a forest uses at most `n - 1` edges out of the
`m` edges in the graph" — both for `|F|` in the display of Lemma 1.2 and for bounding the number of
possible forests in the history count (Lemma 3.10).  The exact statement is the component identity

  `|F| + (#components of the subgraph with edge set F) = |V|`,

proved here by induction on the `IsForest` derivation.  The step is exactly the acyclicity input: an
inserted edge with unconnected endpoints merges two components into one (`conn_insert_sep_conn`
says a trail inside `insert e F` crosses `e` at most once), so the component count drops by one
while the edge count rises by one.
-/

namespace DLMST
open Classical
set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] {G : WGraph V E}

/-! ## Components of an edge set -/

/-- `comp G F v`: the set of vertices reachable from `v` using only edges of `F`. -/
noncomputable def comp (G : WGraph V E) (F : Finset E) (v : V) : Finset V :=
  Finset.univ.filter (fun x => Conn G F v x)

/-- The number of connected components of the subgraph with edge set `F` (isolated vertices count
as their own component). -/
noncomputable def compCount (G : WGraph V E) (F : Finset E) : ℕ :=
  (Finset.univ.image (comp G F)).card

lemma mem_comp {F : Finset E} {v x : V} : x ∈ comp G F v ↔ Conn G F v x := by
  simp [comp]

lemma comp_self_mem {F : Finset E} {v : V} : v ∈ comp G F v :=
  mem_comp.mpr (Conn.refl v)

lemma comp_eq_of_conn {F : Finset E} {u v : V} (h : Conn G F u v) :
    comp G F u = comp G F v := by
  ext x
  rw [mem_comp, mem_comp]
  exact ⟨fun hx => h.symm.trans hx, fun hx => h.trans hx⟩

lemma conn_of_comp_eq {F : Finset E} {u v : V} (h : comp G F u = comp G F v) :
    Conn G F u v := by
  have h1 : v ∈ comp G F u := by rw [h]; exact comp_self_mem
  exact mem_comp.mp h1

/-! ## The empty edge set -/

lemma conn_empty {v x : V} (h : Conn G (∅ : Finset E) v x) : x = v := by
  induction h with
  | refl => rfl
  | step e he => exact absurd he (by simp)
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih2.trans ih1

lemma comp_empty (v : V) : comp G (∅ : Finset E) v = {v} := by
  ext x
  rw [mem_comp, Finset.mem_singleton]
  exact ⟨fun h => conn_empty h, fun h => by rw [h]; exact Conn.refl v⟩

lemma compCount_empty : compCount G (∅ : Finset E) = Fintype.card V := by
  have himg : Finset.univ.image (comp G (∅ : Finset E))
      = Finset.univ.image (fun v : V => ({v} : Finset V)) := by
    congr 1
    funext v
    exact comp_empty v
  have hinj : Function.Injective (fun v : V => ({v} : Finset V)) := fun a b h =>
    by simpa using congrArg (fun s : Finset V => a ∈ s) h
  rw [compCount, himg, ← Finset.card_univ]
  exact Finset.card_image_of_injective _ hinj

/-! ## Inserting an edge across two components

If `F` does not join the ends of `e`, then `conn_insert_sep_conn` says every trail inside
`insert e F` either avoids `e` or crosses it once, so the only components that change are those of
the two endpoints, which merge. -/

lemma comp_insert_union {F : Finset E} {e : E} {x : V}
    (hsep : ¬ Conn G F (G.src e) (G.dst e))
    (hx : Conn G F x (G.src e) ∨ Conn G F x (G.dst e)) :
    comp G (insert e F) x = comp G F (G.src e) ∪ comp G F (G.dst e) := by
  ext y
  rw [mem_comp, Finset.mem_union, mem_comp, mem_comp]
  constructor
  · intro hy
    rcases conn_insert_sep_conn hsep hy with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases hx with hx | hx
      · exact Or.inl (hx.symm.trans h)
      · exact Or.inr (hx.symm.trans h)
    · exact Or.inr h2
    · exact Or.inl h2
  · intro hy
    have hx' : Conn G (insert e F) x (G.src e) ∨ Conn G (insert e F) x (G.dst e) := by
      rcases hx with hx | hx
      · exact Or.inl (Conn.mono (Finset.subset_insert e F) hx)
      · exact Or.inr (Conn.mono (Finset.subset_insert e F) hx)
    rcases hy with hy | hy
    · rcases hx' with hx' | hx'
      · exact Conn.trans hx' (Conn.mono (Finset.subset_insert e F) hy)
      · exact Conn.trans (Conn.trans hx' (Conn.step e (Finset.mem_insert_self e F)).symm)
          (Conn.mono (Finset.subset_insert e F) hy)
    · rcases hx' with hx' | hx'
      · exact Conn.trans (Conn.trans hx' (Conn.step e (Finset.mem_insert_self e F)))
          (Conn.mono (Finset.subset_insert e F) hy)
      · exact Conn.trans hx' (Conn.mono (Finset.subset_insert e F) hy)

lemma comp_insert_same {F : Finset E} {e : E} {x : V}
    (hsep : ¬ Conn G F (G.src e) (G.dst e))
    (hx : ¬ (Conn G F x (G.src e) ∨ Conn G F x (G.dst e))) :
    comp G (insert e F) x = comp G F x := by
  ext y
  rw [mem_comp, mem_comp]
  constructor
  · intro hy
    rcases conn_insert_sep_conn hsep hy with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h
    · exact absurd (Or.inl h1) hx
    · exact absurd (Or.inr h1) hx
  · intro hy
    exact Conn.mono (Finset.subset_insert e F) hy

lemma comp_ne_of_not_conn {F : Finset E} {e : E}
    (hsep : ¬ Conn G F (G.src e) (G.dst e)) :
    comp G F (G.src e) ≠ comp G F (G.dst e) :=
  fun h => hsep (conn_of_comp_eq h)

lemma union_comp_not_mem_image {F : Finset E} {e : E}
    (hsep : ¬ Conn G F (G.src e) (G.dst e)) :
    comp G F (G.src e) ∪ comp G F (G.dst e) ∉ Finset.univ.image (comp G F) := by
  intro hmem
  obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hmem
  have hxmem : x ∈ comp G F (G.src e) ∪ comp G F (G.dst e) := by
    rw [← hx]
    exact comp_self_mem
  rcases Finset.mem_union.mp hxmem with hxa | hxb
  · have heq : comp G F x = comp G F (G.src e) :=
      comp_eq_of_conn (Conn.symm (mem_comp.mp hxa))
    rw [heq] at hx
    have hb : G.dst e ∈ comp G F (G.src e) := by
      rw [hx]
      exact Finset.mem_union_right _ comp_self_mem
    exact hsep (mem_comp.mp hb)
  · have heq : comp G F x = comp G F (G.dst e) :=
      comp_eq_of_conn (Conn.symm (mem_comp.mp hxb))
    rw [heq] at hx
    have ha : G.src e ∈ comp G F (G.dst e) := by
      rw [hx]
      exact Finset.mem_union_left _ comp_self_mem
    exact hsep (Conn.symm (mem_comp.mp ha))

lemma image_comp_insert {F : Finset E} {e : E}
    (hsep : ¬ Conn G F (G.src e) (G.dst e)) :
    Finset.univ.image (comp G (insert e F))
      = insert (comp G F (G.src e) ∪ comp G F (G.dst e))
          ((Finset.univ.image (comp G F)).erase (comp G F (G.src e))
            |>.erase (comp G F (G.dst e))) := by
  ext C
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, -, rfl⟩
    by_cases hx : Conn G F x (G.src e) ∨ Conn G F x (G.dst e)
    · rw [comp_insert_union hsep hx]
      exact Finset.mem_insert_self _ _
    · rw [comp_insert_same hsep hx]
      refine Finset.mem_insert_of_mem ?_
      rw [Finset.mem_erase, Finset.mem_erase]
      refine ⟨?_, ?_, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩
      · intro hE
        exact hx (Or.inr (conn_of_comp_eq hE))
      · intro hE
        exact hx (Or.inl (conn_of_comp_eq hE))
  · rw [Finset.mem_insert]
    rintro (rfl | hC)
    · exact ⟨G.src e, Finset.mem_univ _, comp_insert_union hsep (Or.inl (Conn.refl _))⟩
    · rw [Finset.mem_erase, Finset.mem_erase] at hC
      obtain ⟨hB, hA, hC⟩ := hC
      obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hC
      have hxn : ¬ (Conn G F x (G.src e) ∨ Conn G F x (G.dst e)) := by
        rintro (h | h)
        · exact hA (hx.symm.trans (comp_eq_of_conn h))
        · exact hB (hx.symm.trans (comp_eq_of_conn h))
      exact ⟨x, Finset.mem_univ x, by rw [comp_insert_same hsep hxn, hx]⟩

lemma compCount_insert {F : Finset E} {e : E}
    (hsep : ¬ Conn G F (G.src e) (G.dst e)) :
    compCount G (insert e F) = compCount G F - 1 := by
  set S := Finset.univ.image (comp G F) with hS
  set A := comp G F (G.src e) with hA
  set B := comp G F (G.dst e) with hB
  have hAim : A ∈ S := Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  have hBim : B ∈ S := Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  have hAB : A ≠ B := comp_ne_of_not_conn hsep
  have hABnot : A ∪ B ∉ S := union_comp_not_mem_image hsep
  have hnotin : A ∪ B ∉ (S.erase A).erase B := by
    rw [Finset.mem_erase, Finset.mem_erase]
    exact fun h => hABnot h.2.2
  have hBA : B ∈ S.erase A := by
    rw [Finset.mem_erase]
    exact ⟨hAB.symm, hBim⟩
  rw [compCount, image_comp_insert hsep, Finset.card_insert_of_notMem hnotin,
    Finset.card_erase_of_mem hBA, Finset.card_erase_of_mem hAim]
  have hSdef : compCount G F = S.card := rfl
  have h2 : 2 ≤ S.card := by
    have hsub : ({A, B} : Finset (Finset V)) ⊆ S := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hAim
      · rw [Finset.mem_singleton] at hx
        exact hx ▸ hBim
    have hc := Finset.card_le_card hsub
    rwa [Finset.card_pair hAB] at hc
  omega

/-! ## The component identity and its two corollaries -/

/-- **`|F| + (#components) = |V|`** for every forest `F`.  Induction on the `IsForest`
derivation: the empty forest has `|V|` components, and adding an edge with unconnected endpoints
merges exactly two of them. -/
theorem card_add_compCount {F : Finset E} (hF : IsForest G F) :
    F.card + compCount G F = Fintype.card V := by
  induction hF with
  | empty =>
      rw [Finset.card_empty, compCount_empty]
      exact Nat.zero_add _
  | @add F e hF he hsep ih =>
      rw [Finset.card_insert_of_notMem (not_mem_of_not_conn hsep), compCount_insert hsep]
      have hpos : 0 < compCount G F :=
        Finset.card_pos.mpr ⟨comp G F (G.src e),
          Finset.mem_image.mpr ⟨G.src e, Finset.mem_univ _, rfl⟩⟩
      omega

/-- **A forest has at most `n` edges** (`n = |V|`): the count `compCount` is at least `0`. -/
theorem card_le_card_of_isForest {F : Finset E} (hF : IsForest G F) :
    F.card ≤ Fintype.card V := by
  have h := card_add_compCount hF
  omega

/-- **A forest has at most `n - 1` edges**: the paper's "each forest uses at most `n - 1` edges
out of the `m` edges", used in Lemma 3.10. -/
theorem card_le_card_sub_one_of_isForest {F : Finset E} (hF : IsForest G F)
    (hV : 0 < Fintype.card V) : F.card ≤ Fintype.card V - 1 := by
  have h := card_add_compCount hF
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp hV
  have hpos : 0 < compCount G F :=
    Finset.card_pos.mpr ⟨_, Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩⟩
  omega

/-- **A Kruskal-order criterion for forestness.**  If every edge of `F` has its ends unjoined by
those edges of `F` that are smaller in a fixed order, then `F` is a forest: inserting the edges in
increasing order, each insertion closes no cycle.  This is the invariant the certificate procedure's
rounds have to establish for the forest they return (they process edges in weight order across the
whole instance); the edge order is otherwise irrelevant. -/
theorem isForest_of_forall_not_conn_below [LinearOrder E] {F : Finset E}
    (h : ∀ e ∈ F, ¬ Conn G (F.filter (fun f => f < e)) (G.src e) (G.dst e)) :
    IsForest G F := by
  classical
  refine Finset.induction_on_max (motive := fun s => (∀ e ∈ s,
    ¬ Conn G (s.filter (fun f => f < e)) (G.src e) (G.dst e)) → IsForest G s) F ?_ ?_ h
  · intro _; exact IsForest.empty
  · intro a s hlt ih hcond
    have hcond_s : ∀ e ∈ s, ¬ Conn G (s.filter (fun f => f < e)) (G.src e) (G.dst e) := by
      intro e he
      have hfilt : (insert a s).filter (fun f => f < e) = s.filter (fun f => f < e) := by
        rw [Finset.filter_insert, ite_eq_right (not_lt.mpr (le_of_lt (hlt e he)))]
      rw [← hfilt]
      exact hcond e (Finset.mem_insert_of_mem he)
    have hfilt_a : (insert a s).filter (fun f => f < a) = s := by
      rw [Finset.filter_insert, ite_eq_right (not_lt.mpr le_rfl)]
      exact Finset.filter_true_of_mem hlt
    have hna : ¬ Conn G s (G.src a) (G.dst a) := by
      rw [← hfilt_a]
      exact hcond a (Finset.mem_insert_self a s)
    exact IsForest.add (ih hcond_s) (fun hh => hna (hh ▸ Conn.refl (G.src a))) hna

end DLMST