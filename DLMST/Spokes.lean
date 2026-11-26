import DLMST.BatchSel

/-!
# The spoke families, computed from `BatchSel.selAt`

`BatchSel.exists_spokeSpec` only says *some* `SpokeSpec` exists, given a total old spoke map.  Here the
spoke map itself is made concrete, in two steps:

* `spokeOf B adm k v` — the lightest admissible representative of the batch `B` at `v`, read off
  `selAt G B adm k v` as its minimum.  This is the initial spoke of a round.
* `spokeTable B adm k : Fin t → Fin t → V → E` — the paper's spoke vector table `(σ_i)_{i ∈ [t²]}`
  (the exact type of `History.spoke`), one entry per `(block, round)`.

Main facts:

* `spokeOf_mem`, `spokeOf_le` — the spoke is *selected*, and it is the minimum of the selection, so it
  is at most every other selected candidate (hence `spokeOf_weight_le` for a weight-ordered edge order);
* `spokeOf_incident` — the spoke is incident at its vertex, so it is a legal spoke;
* `selAt_nonempty_of_adm` — a vertex with an admissible incident edge has a selection, so `spokeOf`
  is really the minimum and not the default;
* `spokeSpec_selAt` / `spokeSpec_table` — the round's `SpokeSpec` with `σ` taken from `selAt` / from
  the table: candidates from `exists_cnd`, spokes from `spokeOf`.

Not formalised here: §3.4's bookkeeping of *which* round updates which spoke (freeze/unfreeze), which
lives in `History`/`ProcChain`; this file only produces the spoke data and its local properties.
-/

namespace DLMST
open Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [LinearOrder E] {G : WGraph V E}

/-- The initial spoke at `v`: the minimum of the batch selection `selAt G B adm k v`.  Falls back to
an arbitrary edge at vertices with no selection (their spoke is `⊥` in the paper). -/
noncomputable def spokeOf (B : Finset E) (adm : E → Prop) (k : ℕ) [Nonempty E] (v : V) : E :=
  if h : (selAt G B adm k v).Nonempty then (selAt G B adm k v).min' h else Classical.arbitrary E

theorem spokeOf_mem {B : Finset E} {adm : E → Prop} {k : ℕ} {v : V} [Nonempty E]
    (h : (selAt G B adm k v).Nonempty) :
    spokeOf (G := G) B adm k v ∈ selAt G B adm k v := by
  unfold spokeOf
  rw [dite_eq_left h]
  exact Finset.min'_mem _ _

theorem spokeOf_le {B : Finset E} {adm : E → Prop} {k : ℕ} {v : V} [Nonempty E]
    (h : (selAt G B adm k v).Nonempty) {e : E} (he : e ∈ selAt G B adm k v) :
    spokeOf (G := G) B adm k v ≤ e := by
  unfold spokeOf
  rw [dite_eq_left h]
  exact Finset.min'_le _ _ he

theorem spokeOf_incident {B : Finset E} {adm : E → Prop} {k : ℕ} {v : V} [Nonempty E]
    (h : (selAt G B adm k v).Nonempty) :
    incident G v (spokeOf (G := G) B adm k v) :=
  ((mem_Bv.mp ((batchSpec_selAt G B adm k).sel_sub v (spokeOf_mem h))).2)

theorem spokeOf_weight_le {B : Finset E} {adm : E → Prop} {k : ℕ} {v : V} [Nonempty E]
    (hw : OrderedByWeight G) (h : (selAt G B adm k v).Nonempty) {e : E}
    (he : e ∈ selAt G B adm k v) :
    G.weight (spokeOf (G := G) B adm k v) ≤ G.weight e :=
  hw _ _ (spokeOf_le h he)

/-- A selection is nonempty as soon as the quota is at least one and the batch has a representative
at `v`. -/
theorem selAt_nonempty {B : Finset E} {adm : E → Prop} {k : ℕ} {v : V}
    (hk : 1 ≤ k) (h : (repsAt G B adm v).Nonempty) :
    (selAt G B adm k v).Nonempty := by
  have hlen : 0 < (sortReps G B adm v).length := by
    unfold sortReps
    rw [Finset.length_sort]
    exact Finset.card_pos.mpr h
  have htake : 0 < ((sortReps G B adm v).take k).length := by
    rw [List.length_take]
    omega
  refine ⟨(sortReps G B adm v).take k |>.get ⟨0, htake⟩, ?_⟩
  rw [mem_selAt]
  exact List.get_mem _ _

/-- A vertex with an admissible incident edge of the batch has a representative, hence a selection. -/
theorem selAt_nonempty_of_adm {B : Finset E} {adm : E → Prop} {k : ℕ} {v : V}
    (hk : 1 ≤ k) (h : ∃ e ∈ Bv G v B, adm e) :
    (selAt G B adm k v).Nonempty := by
  obtain ⟨e, heU, hadm⟩ := h
  obtain ⟨r, hrep, -⟩ := exists_rep (grp := other G v) heU hadm
  exact selAt_nonempty hk ⟨r, mem_repsAt.mpr ⟨hrep.1, hrep⟩⟩

/-- **The round's `SpokeSpec`, with spokes read off `selAt`.**  Candidates come from `exists_cnd`,
spokes are the minimum selected representative; the minimality gives `σ ≤ cnd`. -/
theorem spokeSpec_selAt {P : Finset V} {B : Finset E} {adm : E → Prop} {k : ℕ} [Nonempty E]
    (hk : 1 ≤ k) (hw : OrderedByWeight G)
    (hcover : ∀ v, k ≤ (Sv G v (selAt G B adm k)).card →
      ∃ x ∈ Sv G v (selAt G B adm k), x ∈ P) :
    ∃ cnd σ : V → E, SpokeSpec G (selAt G B adm k) k P cnd σ := by
  classical
  have hsel := batchSpec_selAt G B adm k
  have hwit : ∀ v, (selAt G B adm k v).card = k →
      ∃ f ∈ selAt G B adm k v, other G v f ∈ P :=
    fun v hv => exists_cnd hsel P hcover v hv
  let cnd : V → E := fun v =>
    if hv : (selAt G B adm k v).card = k then (hwit v hv).choose else Classical.arbitrary E
  let σ : V → E := fun v =>
    if hv : (selAt G B adm k v).card = k then spokeOf (G := G) B adm k v
    else Classical.arbitrary E
  refine ⟨cnd, σ, ?_, ?_, ?_⟩
  · intro v hv
    show (if hv' : (selAt G B adm k v).card = k then (hwit v hv').choose
      else Classical.arbitrary E) ∈ selAt G B adm k v
    rw [dite_eq_left hv]
    exact (hwit v hv).choose_spec.1
  · intro v hv
    show other G v (if hv' : (selAt G B adm k v).card = k then (hwit v hv').choose
      else Classical.arbitrary E) ∈ P
    rw [dite_eq_left hv]
    exact (hwit v hv).choose_spec.2
  · intro v hv
    have hne : (selAt G B adm k v).Nonempty :=
      Finset.card_pos.mp (by omega)
    have hσ : σ v = spokeOf (G := G) B adm k v := by
      show (if hv' : (selAt G B adm k v).card = k then _ else Classical.arbitrary E) = _
      rw [dite_eq_left hv]
    have hcm : cnd v ∈ selAt G B adm k v := by
      show (if hv' : (selAt G B adm k v).card = k then (hwit v hv').choose
        else Classical.arbitrary E) ∈ selAt G B adm k v
      rw [dite_eq_left hv]
      exact (hwit v hv).choose_spec.1
    rw [hσ]
    exact ⟨spokeOf_incident hne, hw _ _ (spokeOf_le hne hcm)⟩

/-- **The spoke vector table** `(σ_i)_{i ∈ [t²]}`, one entry per `(block, round)`: the type of
`History.spoke`.  Each entry is the lightest admissible batch representative at the vertex. -/
noncomputable def spokeTable {t : ℕ} (B : Fin t → Fin t → Finset E) (adm : E → Prop) (k : ℕ)
    [Nonempty E] : Fin t → Fin t → V → E :=
  fun i j v => spokeOf (G := G) (B i j) adm k v

/-- Every table entry is the minimum of the round's selection, hence selected. -/
theorem spokeTable_mem {t : ℕ} (B : Fin t → Fin t → Finset E) (adm : E → Prop) (k : ℕ)
    [Nonempty E] (i j : Fin t) (v : V) (h : (selAt G (B i j) adm k v).Nonempty) :
    spokeTable (G := G) B adm k i j v ∈ selAt G (B i j) adm k v :=
  spokeOf_mem h

/-- Every table entry is incident at its vertex, provided the round has an admissible incident edge
there.  This is the legality of the spoke vector, with the hypothesis discharged by
`selAt_nonempty_of_adm`. -/
theorem spokeTable_incident {t : ℕ} (B : Fin t → Fin t → Finset E) (adm : E → Prop) (k : ℕ)
    [Nonempty E] (hk : 1 ≤ k)
    (hadm : ∀ (i j : Fin t) (v : V), ∃ e ∈ Bv G v (B i j), adm e)
    (i j : Fin t) (v : V) : incident G v (spokeTable (G := G) B adm k i j v) :=
  spokeOf_incident (G := G) (B := B i j) (selAt_nonempty_of_adm hk (hadm i j v))

/-- **The round's `SpokeSpec` for the table's own spoke vector.**  Same content as `spokeSpec_selAt`,
with `σ` fixed to `spokeTable`; the spec only constrains full vertices, where the table is the
minimum selection. -/
theorem spokeSpec_table {t : ℕ} {P : Finset V} (B : Fin t → Fin t → Finset E) (adm : E → Prop)
    (k : ℕ) [Nonempty E] (i j : Fin t) (hk : 1 ≤ k) (hw : OrderedByWeight G)
    (hcover : ∀ v, k ≤ (Sv G v (selAt G (B i j) adm k)).card →
      ∃ x ∈ Sv G v (selAt G (B i j) adm k), x ∈ P) :
    ∃ cnd : V → E, SpokeSpec G (selAt G (B i j) adm k) k P cnd (spokeTable (G := G) B adm k i j) := by
  classical
  obtain ⟨cnd, -, h1, h2, h3⟩ := spokeSpec_selAt (G := G) (B := B i j) (adm := adm) (P := P)
    hk hw hcover
  refine ⟨cnd, h1, h2, ?_⟩
  intro v hv
  have hne : (selAt G (B i j) adm k v).Nonempty := Finset.card_pos.mp (by omega)
  have hcm : cnd v ∈ selAt G (B i j) adm k v := h1 v hv
  exact ⟨spokeOf_incident hne, hw _ _ (spokeOf_le hne hcm)⟩

end DLMST