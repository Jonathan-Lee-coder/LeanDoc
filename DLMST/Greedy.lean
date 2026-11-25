import DLMST.Tree

/-!
# Kruskal's loop: the invariant, and correctness

`Tree.lean` ends with `kruskal_step`: one accepted edge preserves the existence of a minimum spanning
forest containing the partial solution.  This file runs that step over a whole edge scan and proves
the result is a minimum spanning forest, which is what the paper asserts for its outer loop
("sort the edges, then add each one whose ends are not yet joined") without proving.

The invariant cannot be just "the accumulator extends to an MSF", because the weight comparison needs
to know which edges the scan has already retired.  Two facts travel together:

* `hopen` — every edge whose ends the accumulator does not join is still ahead in the scan.  This is
  what supplies the lightness hypothesis of `kruskal_step`: the edge being tested is the first still
  open one, so every other open edge lies later in the list, and `Sorted` prices it no lower;
* `hsuf` — the unscanned list really is a suffix of the scan, which is what turns "lies later in the
  list" into an equation `Sorted` can be applied to.

`hopen` survives a step in both directions: an edge retired as rejected stays joined, since the
accumulator only grows, and an edge accepted enters the accumulator, so it is joined too.  With the
invariant in hand, the proof is one `kruskal_step` per accepted edge and nothing per rejected one.

The end of the scan is the usual closing argument: the invariant gives an MSF `T` with `K l ∅ ⊆ T`,
and `mem_or_conn_of_mem` says every scanned edge lies in the accumulator or is joined by it — so an
edge of `T` outside the accumulator would be joined by a subset of `T - f`, contradicting
`IsForest.bridge`.  Hence `K l ∅ = T`.

`sortedScan_spec` supplies the sorted scan that `kruskal_correct` asks for, by peeling off a
lightest edge repeatedly (`exists_listing`), so the outer loop is justified as an algorithm rather
than only relative to an oracle listing; `kruskal_exists` packages the two.  No sorting routine is
needed, which keeps the proof away from `List.insertionSort` and its `DecidableRel / Std.Total /
IsTrans` baggage.

Not here: the Borůvka variant that accepts a whole round of lightest out-edges at once.  Also note
the proof never uses distinctness of the scanned list: re-scanning an edge is harmless, and the
listing `exists_listing` builds happens to be duplicate-free anyway.
-/

open Classical

namespace DLMST

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] {G : WGraph V E}

/-- `Sorted G l`: reading `l` left to right, weights never decrease.  Stated as "everything after an
entry is at least as heavy as it", which is exactly the shape the scan argument feeds to it. -/
def Sorted (G : WGraph V E) (l : List E) : Prop :=
  ∀ (as : List E) (a : E) (bs : List E), l = as ++ a :: bs → ∀ b ∈ bs, G.weight a ≤ G.weight b

/-- Kruskal's acceptance test: keep `e` exactly when its ends are not already joined. -/
noncomputable def step (G : WGraph V E) (F : Finset E) (e : E) : Finset E :=
  if ¬ Conn G F (G.src e) (G.dst e) then insert e F else F

/-- The accumulator after scanning the edge list `es` from the starting set `F`: the leftmost edge is
folded first, so `K G (e :: es) F = K G es (step G F e)`. -/
noncomputable def K (G : WGraph V E) (es : List E) (F : Finset E) : Finset E :=
  es.foldl (fun acc e => step G acc e) F

theorem K_nil (G : WGraph V E) (F : Finset E) : K G ([] : List E) F = F := rfl

theorem K_cons (G : WGraph V E) (e : E) (es : List E) (F : Finset E) :
    K G (e :: es) F = K G es (step G F e) := rfl

/-- The test keeps the edge exactly when it is not joined. -/
theorem step_accept (G : WGraph V E) (F : Finset E) (e : E)
    (h : ¬ Conn G F (G.src e) (G.dst e)) : step G F e = insert e F := by
  simp [step, h]

/-- ... and otherwise does nothing at all. -/
theorem step_reject (G : WGraph V E) (F : Finset E) (e : E)
    (h : Conn G F (G.src e) (G.dst e)) : step G F e = F := by
  simp [step, h]

/-- The test has exactly two outcomes, each packaged with the fact that produced it.  Stating the two
together is what keeps the `if`-equations from having to be oriented by hand downstream. -/
theorem step_eq_or_conn (G : WGraph V E) (F : Finset E) (e : E) :
    (step G F e = F ∧ Conn G F (G.src e) (G.dst e)) ∨
      (step G F e = insert e F ∧ ¬ Conn G F (G.src e) (G.dst e)) := by
  by_cases h : ¬ Conn G F (G.src e) (G.dst e)
  · exact Or.inr ⟨step_accept G F e h, h⟩
  · exact Or.inl ⟨step_reject G F e (not_not.mp h), not_not.mp h⟩

/-- Testing an edge never loses an edge. -/
theorem step_subset (G : WGraph V E) (F : Finset E) (e : E) : F ⊆ step G F e := by
  rcases step_eq_or_conn G F e with ⟨hr, _⟩ | ⟨ha, _⟩
  · rw [hr]
  · rw [ha]
    exact Finset.subset_insert e F

/-- Scanning cannot shrink the accumulator. -/
theorem K_mono : ∀ (es : List E) (F : Finset E), F ⊆ K G es F := by
  intro es
  induction es with
  | nil => intro F; exact Finset.Subset.refl F
  | cons a as ih =>
    intro F
    exact Finset.Subset.trans (step_subset G F a) (ih (step G F a))

/-- A scan over a concatenation is a scan over the first half, then over the second. -/
theorem K_append : ∀ (as bs : List E) (F : Finset E),
    K G (as ++ bs) F = K G bs (K G as F) := by
  intro as
  induction as with
  | nil => intro bs F; rfl
  | cons a as ih =>
    intro bs F
    have key : K G ((a :: as) ++ bs) F = K G (as ++ bs) (step G F a) := rfl
    rw [key, ih bs (step G F a), ← K_cons]

/-- An edge the scan reaches is either in the accumulator or joined by it — retired in one of the two
ways Kruskal knows. -/
theorem mem_or_conn_of_mem : ∀ (as : List E) (F : Finset E) (f : E), f ∈ as →
    f ∈ K G as F ∨ Conn G (K G as F) (G.src f) (G.dst f) := by
  intro as
  induction as with
  | nil => intro F f hf; exact absurd hf (by simp)
  | cons a as ih =>
    intro F f hf
    rw [K_cons]
    rcases List.mem_cons.mp hf with heq | hf'
    · rw [heq]
      rcases step_eq_or_conn G F a with ⟨hr, hcon⟩ | ⟨ha, _⟩
      · refine Or.inr ?_
        rw [hr]
        exact Conn.mono (K_mono as F) hcon
      · refine Or.inl (K_mono as (step G F a) ?_)
        rw [ha]
        exact Finset.mem_insert_self a F
    · exact ih (step G F a) f hf'

/-- **Kruskal's loop invariant.**  With `rest` still to be scanned from the accumulator `F`, suppose
some MSF extends `F`, that every edge `F` leaves open is still ahead in the scan, and that `rest` is a
suffix of the sorted scan `l`.  Then some MSF extends the final accumulator `K G rest F`.

The lightness that `kruskal_step` demands comes from `hopen` together with `hsuf`: an edge still open
at `e` lies strictly after `e` in `l`, and `Sorted` then prices `e` no higher. -/
theorem kruskal_inv (l : List E) (hsorted : Sorted G l) :
    ∀ (rest : List E) (F : Finset E), (∃ T, IsMSF G T ∧ F ⊆ T) →
      (∀ f, ¬ Conn G F (G.src f) (G.dst f) → f ∈ rest) →
      (∃ pre, pre ++ rest = l) → ∃ T, IsMSF G T ∧ K G rest F ⊆ T := by
  intro rest
  induction rest with
  | nil => intro F hT _ _; rw [K_nil]; exact hT
  | cons e rest' ih =>
    classical
    intro F hextend hopen hsuf
    obtain ⟨pre, hpre⟩ := hsuf
    obtain ⟨T, hTmsf, hFT⟩ := hextend
    have hsuf' : ∃ p, p ++ rest' = l := ⟨pre ++ [e], by rw [List.append_assoc]; exact hpre⟩
    rcases step_eq_or_conn G F e with ⟨hr, hcon⟩ | ⟨ha, hacc⟩
    · -- rejected: the accumulator does not move, and nothing is retired
      have hopen' : ∀ f, ¬ Conn G F (G.src f) (G.dst f) → f ∈ rest' := by
        intro f hf
        rcases List.mem_cons.mp (hopen f hf) with heq | h
        · subst heq
          exact absurd hcon hf
        · exact h
      obtain ⟨T', hT', hsub⟩ := ih F ⟨T, hTmsf, hFT⟩ hopen' hsuf'
      exact ⟨T', hT', by rw [K_cons, hr]; exact hsub⟩
    · -- accepted: one `kruskal_step`, priced by the edges the scan has already retired
      have hmin : ∀ f, ¬ Conn G F (G.src f) (G.dst f) → G.weight e ≤ G.weight f := by
        intro f hf
        rcases List.mem_cons.mp (hopen f hf) with heq | h
        · rw [heq]
        · exact hsorted pre e rest' hpre.symm f h
      have hopen' : ∀ g, ¬ Conn G (insert e F) (G.src g) (G.dst g) → g ∈ rest' := by
        intro g hg
        rcases List.mem_cons.mp
            (hopen g (fun hc => hg (Conn.mono (Finset.subset_insert e F) hc))) with heq | h
        · rw [heq] at hg
          exfalso
          exact hg (conn_of_mem (Finset.mem_insert_self e F))
        · exact h
      obtain ⟨T₁, hT₁, h₁⟩ := kruskal_step T hTmsf hFT hacc hmin
      obtain ⟨T₂, hT₂, h₂⟩ := ih (insert e F) ⟨T₁, hT₁, h₁⟩ hopen' hsuf'
      exact ⟨T₂, hT₂, by rw [K_cons, ha]; exact h₂⟩

/-- **Kruskal's algorithm is correct.**  Scan a list containing every edge of `G` in nondecreasing
order of weight, starting from the empty set: the result is a minimum spanning forest.  `hfull` is
what makes the output spanning, `Sorted` what makes it minimum.  There is no distinctness hypothesis,
and none is needed: an edge scanned twice is either added the first time or found joined, and the
second visit changes nothing the invariant cares about. -/
theorem kruskal_correct (l : List E) (hsorted : Sorted G l) (hfull : ∀ e : E, e ∈ l) :
    IsMSF G (K G l ∅) := by
  classical
  obtain ⟨T₀, hT₀⟩ := msf_exists (G := G)
  obtain ⟨T, hT, hsub⟩ := kruskal_inv l hsorted l (∅ : Finset E)
    ⟨T₀, hT₀, Finset.empty_subset T₀⟩ (fun f _ => hfull f) ⟨[], rfl⟩
  have hTf : IsForest G T := hT.1.1
  have hTsub : T ⊆ K G l ∅ := by
    intro f hf
    by_contra hnk
    rcases mem_or_conn_of_mem (G := G) l (∅ : Finset E) f (hfull f) with hmem | hconn
    · exact hnk hmem
    · refine absurd (Conn.mono ?_ hconn) (IsForest.bridge hTf hf)
      intro x hx
      exact Finset.mem_erase.mpr ⟨fun hxf => hnk (hxf ▸ hx), hsub hx⟩
  rw [Finset.Subset.antisymm hsub hTsub]
  exact hT

/-- A lightest edge in front of an ordered list keeps the list ordered. -/
theorem Sorted.cons (a : E) (l : List E) (hl : Sorted G l)
    (hmin : ∀ b ∈ l, G.weight a ≤ G.weight b) : Sorted G (a :: l) := by
  intro as x bs hsplit b hb
  cases as with
  | nil =>
    rw [List.nil_append] at hsplit
    obtain ⟨rfl, hl'⟩ := List.cons.inj hsplit
    exact hmin b (hl' ▸ hb)
  | cons c cs =>
    rw [List.cons_append] at hsplit
    obtain ⟨rfl, hsplit'⟩ := List.cons.inj hsplit
    exact hl cs x bs hsplit' b hb

/-- Every finset of edges has a listing that is ordered by weight and contains exactly its elements.
The construction peels off a lightest edge, so no sorting routine has to be formalized: the
correctness of a sort would be this same induction wrapped in `DecidableRel` bookkeeping. -/
theorem exists_listing (G : WGraph V E) : ∀ (s : Finset E),
    ∃ l, Sorted G l ∧ ∀ e, e ∈ l ↔ e ∈ s := by
  classical
  have key : ∀ (n : ℕ) (s : Finset E), s.card = n → ∃ l, Sorted G l ∧ ∀ e, e ∈ l ↔ e ∈ s := by
    intro n
    induction n with
    | zero =>
      intro s hs
      have hs0 : s = ∅ := Finset.card_eq_zero.mp hs
      exact ⟨[], ⟨fun as a bs h _ => absurd h (by simp),
        fun e => ⟨fun h => (List.not_mem_nil h).elim, fun he => absurd he (by rw [hs0]; simp)⟩⟩⟩
    | succ n ih =>
      intro s hs
      have hne : s.Nonempty := by
        refine Finset.ne_empty_iff_nonempty.mp ?_
        intro h
        rw [h, Finset.card_empty] at hs
        omega
      obtain ⟨a, has, hmin⟩ := Finset.exists_min_image s G.weight hne
      obtain ⟨l, hl, hcov⟩ := ih (s.erase a) (by rw [Finset.card_erase_of_mem has]; omega)
      have herase : ∀ {x}, x ∈ s.erase a → x ∈ s := by
        intro x hx
        exact (Finset.mem_erase.1 hx).2
      have hlight : ∀ b ∈ l, G.weight a ≤ G.weight b := by
        intro b hb
        exact hmin b (herase ((hcov b).1 hb))
      use a :: l, Sorted.cons a l hl hlight
      intro e
      constructor
      · intro h
        rcases List.mem_cons.mp h with heq | hl'
        · rw [heq]
          exact has
        · exact herase ((hcov _).1 hl')
      · intro he
        rcases Classical.em (e = a) with heq | hne'
        · rw [heq]
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem a ((hcov _).2 (Finset.mem_erase.mpr ⟨hne', he⟩))
  intro s
  exact key s.card s rfl

/-- **A sorted scan exists.**  `kruskal_correct` is therefore not vacuous: its hypothesis can be
discharged, and `kruskal_exists` below turns the algorithm into a theorem with no assumptions. -/
theorem sortedScan_spec : ∃ l : List E, Sorted G l ∧ ∀ e : E, e ∈ l := by
  obtain ⟨l, hl, hcov⟩ := exists_listing (G := G) (Finset.univ : Finset E)
  exact ⟨l, hl, fun e => (hcov e).2 (Finset.mem_univ e)⟩

/-- **Kruskal, with no oracle.**  Every finite weighted graph has a sorted listing of its edges whose
Kruskal output is a minimum spanning forest.  This is the paper's outer loop, fully justified. -/
theorem kruskal_exists : ∃ l : List E, Sorted G l ∧ IsMSF G (K G l ∅) := by
  obtain ⟨l, hl, hfull⟩ := sortedScan_spec (G := G)
  exact ⟨l, hl, kruskal_correct (G := G) l hl hfull⟩

end DLMST
