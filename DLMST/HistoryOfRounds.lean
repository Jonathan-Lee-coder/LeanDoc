import DLMST.GeometricHistory
import DLMST.Spokes

/-!
# Building a history from the round data

`GeometricHistory.lean` phrased §3.5's family `A` on an *arbitrary* `History`: consistency, the
per-round forest invariant and `hFsp` were hypotheses.  This file produces the history the driver
actually runs, so two of those three hypotheses become theorems:

* **`History.ofData`** — a history whose `pref` is *defined* as the round's action
  `actOf G (σ b i) (F b i)`: `History.Consistent` holds by `rfl`.  A history is exactly a pair of
  tables (spokes, forests) plus this definition; nothing else in Definition 3.8 is data.
* **`forestUpTo`** — the forest *at the start* of round `r`: the union of the round pieces `D.Fr`
  over the rounds before `r` (rounds flattened by `roundIdx : Fin t × Fin t ≃ Fin (t²)`).  It is
  contained in the call's returned forest `D.F`, so `IsForest` transfers by **`IsForest.subset`**
  (a new downward-closure lemma for the inductive forest predicate — the missing piece that makes
  per-round forests free of charge).
* **`historyOfRoundData`** — `History.ofData σ (forestUpTo D ·)`: consistent by construction,
  per-round `IsForest` by `hforest` + `subset`.  `forestUpTo` also *grows* along the rounds of a
  block (the flat index increases with the round number), so §3.3's `PPPPFFF` row shape
  (`History.monoRow_of_grow`) applies to it without further hypotheses.
* **`historyOfTable`** — the same construction with `σ := Spokes.spokeTable`, whose entries are
  incident at their vertex (`spokeTable_incident`): the spokes are legal.
* **`card_U_le_display_form_of_roundData`** — `card_U_le_display_form_of_geometry` with
  `H := historyOfRoundData D σ`, `H.Consistent` and per-round `IsForest` discharged: only `hFsp`,
  the per-edge error premise, Lemma 3.11's `lost` bound and the numeric parameters remain.
  The companion `_actOf` version writes the two `H`-shaped premises as `bad (prefAct …)`.

Not formalised here: the *recursion* choosing `σ` and `slot` — this file says that once the driver
has produced the spoke table, the round pieces, and the schedule, the driver's obligations are
geometric only.
-/

namespace DLMST
open Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

/-! ## Downward closure of `IsForest` -/

private theorem IsForest.subset_aux {F : Finset E} (hF : IsForest G F) :
    ∀ {S : Finset E}, S ⊆ F → IsForest G S := by
  induction hF with
  | empty =>
      intro S hS
      rw [Finset.subset_empty] at hS
      rw [hS]
      exact IsForest.empty
  | add hF he hconn ih =>
      rename_i F' e'
      intro S hS
      by_cases hmem : e' ∈ S
      · have hErase : S.erase e' ⊆ F' := by
          intro x hx
          have hxS : x ∈ S := Finset.mem_of_mem_erase hx
          rcases Finset.mem_insert.mp (hS hxS) with rfl | h
          · exact absurd rfl (Finset.mem_erase.mp hx).1
          · exact h
        have hnotconn : ¬ Conn G (S.erase e') (G.src e') (G.dst e') :=
          fun hc => hconn (Conn.mono hErase hc)
        have hins := IsForest.add (ih hErase) he hnotconn
        rwa [Finset.insert_erase hmem] at hins
      · have hSF : S ⊆ F' := by
          intro x hx
          rcases Finset.mem_insert.mp (hS hx) with rfl | h
          · exact absurd hx hmem
          · exact h
        exact ih hSF

/-- **`IsForest` is downward closed.**  Deleting edges cannot create a cycle; this is the direction
that `hforest` (a statement about the *union* of the round pieces) is used in. -/
theorem IsForest.subset {F S : Finset E} (hF : IsForest G F) (hS : S ⊆ F) : IsForest G S :=
  IsForest.subset_aux hF hS

/-! ## Rounds as a linear order -/

/-- **Round reindexing**: `Fin t × Fin t ≃ Fin (t²)`, so a round `(b, i)` has a flat number and the
round data's `Fin (t²)`-indexed tables can be read in `(block, round)` form.  `finProdFinEquiv` maps
`(b, i)` to `i + t·b`, so the flat order is block-major and round-minor. -/
noncomputable def roundIdx (t : ℕ) : Fin t × Fin t ≃ Fin (t ^ 2) :=
  (finProdFinEquiv (m := t) (n := t)).trans (finCongr (Nat.pow_two t).symm)

/-- Later rounds of the same block have larger flat number — what makes the forest grow. -/
theorem roundIdx_le_of_le {t : ℕ} {b : Fin t} {i j : Fin t} (hij : i ≤ j) :
    roundIdx t (b, i) ≤ roundIdx t (b, j) := by
  show ((roundIdx t (b, i) : ℕ) ≤ (roundIdx t (b, j) : ℕ))
  have h : (i : ℕ) + t * (b : ℕ) ≤ (j : ℕ) + t * (b : ℕ) :=
    Nat.add_le_add_right (Fin.le_def.mp hij) _
  simpa [roundIdx] using h

/-! ## Histories as tables plus the action rule -/

namespace History

/-- **A history from its two tables.**  The preferred actions are *defined* by §3.1's rule, so the
history is consistent by `rfl`: Definition 3.8 has no further data. -/
noncomputable def ofData {t : ℕ} (σ : Fin t → Fin t → V → E) (Fr : Fin t → Fin t → Finset E) :
    History V E t where
  spoke := σ
  forest := Fr
  pref := fun e b i => actOf G (σ b i) (Fr b i) e

@[simp] theorem ofData_spoke {t : ℕ} (σ : Fin t → Fin t → V → E) (Fr : Fin t → Fin t → Finset E) :
    (ofData (G := G) σ Fr).spoke = σ := rfl

@[simp] theorem ofData_forest {t : ℕ} (σ : Fin t → Fin t → V → E) (Fr : Fin t → Fin t → Finset E)
    (b i : Fin t) : (ofData (G := G) σ Fr).forest b i = Fr b i := rfl

@[simp] theorem ofData_pref {t : ℕ} (σ : Fin t → Fin t → V → E) (Fr : Fin t → Fin t → Finset E)
    (e : E) (b i : Fin t) :
    (ofData (G := G) σ Fr).pref e b i = actOf G (σ b i) (Fr b i) e := rfl

/-- The constructed history is consistent — the only condition Definition 3.8 asks for. -/
theorem ofData_consistent {t : ℕ} (σ : Fin t → Fin t → V → E) (Fr : Fin t → Fin t → Finset E) :
    (ofData (G := G) σ Fr).Consistent (G := G) := fun _ _ _ => rfl

end History

/-! ## The forest at the start of a round -/

/-- **The forest at the start of round `r`**: the union of the round pieces of all earlier rounds. -/
noncomputable def forestUpTo {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ} {P : Finset V}
    {E₀ : Finset E} (D : CallOut.RoundData G P E₀ ι t) (r : Fin t × Fin t) : Finset E :=
  (Finset.univ.filter (fun p : Fin (t ^ 2) => p < roundIdx t r)).biUnion D.Fr

theorem forestUpTo_sub {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ} {P : Finset V}
    {E₀ : Finset E} (D : CallOut.RoundData G P E₀ ι t) (r : Fin t × Fin t) :
    forestUpTo D r ⊆ D.F := by
  intro x hx
  rw [forestUpTo, Finset.mem_biUnion] at hx
  obtain ⟨p, -, hpx⟩ := hx
  rw [CallOut.RoundData.F, Finset.mem_biUnion]
  exact ⟨p, Finset.mem_univ p, hpx⟩

/-- **Per-round forests are free**: the call's returned forest is a forest, so every prefix of the
rounds is one too. -/
theorem isForest_forestUpTo {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ} {P : Finset V}
    {E₀ : Finset E} (D : CallOut.RoundData G P E₀ ι t) (r : Fin t × Fin t) :
    IsForest G (forestUpTo D r) :=
  D.hforest.subset (forestUpTo_sub D r)

/-- The forest grows along the rounds of a block. -/
theorem forestUpTo_grow {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ} {P : Finset V}
    {E₀ : Finset E} (D : CallOut.RoundData G P E₀ ι t) {b : Fin t} {i j : Fin t}
    (hij : i ≤ j) : forestUpTo D (b, i) ⊆ forestUpTo D (b, j) := by
  intro x hx
  rw [forestUpTo, Finset.mem_biUnion] at hx ⊢
  obtain ⟨p, hp, hpx⟩ := hx
  exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p,
    lt_of_lt_of_le (Finset.mem_filter.mp hp).2 (roundIdx_le_of_le hij)⟩, hpx⟩

/-! ## The driver's history -/

/-- **The history of one call**, from the round data and the driver's spoke table: spokes `σ`,
forests the prefixes of the rounds, actions by §3.1's rule. -/
noncomputable def historyOfRoundData {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ}
    {P : Finset V} {E₀ : Finset E} (D : CallOut.RoundData G P E₀ ι t)
    (σ : Fin t → Fin t → V → E) : History V E t :=
  History.ofData (G := G) σ (fun b i => forestUpTo D (b, i))

@[simp] theorem historyOfRoundData_spoke {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ}
    {P : Finset V} {E₀ : Finset E} (D : CallOut.RoundData G P E₀ ι t)
    (σ : Fin t → Fin t → V → E) : (historyOfRoundData D σ).spoke = σ := rfl

@[simp] theorem historyOfRoundData_forest {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ}
    {P : Finset V} {E₀ : Finset E} (D : CallOut.RoundData G P E₀ ι t)
    (σ : Fin t → Fin t → V → E) (b i : Fin t) :
    (historyOfRoundData D σ).forest b i = forestUpTo D (b, i) := rfl

@[simp] theorem historyOfRoundData_pref {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ}
    {P : Finset V} {E₀ : Finset E} (D : CallOut.RoundData G P E₀ ι t)
    (σ : Fin t → Fin t → V → E) (e : E) (b i : Fin t) :
    (historyOfRoundData D σ).pref e b i = actOf G (σ b i) (forestUpTo D (b, i)) e := rfl

/-- The driver's history is consistent. -/
theorem historyOfRoundData_consistent {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ}
    {P : Finset V} {E₀ : Finset E} (D : CallOut.RoundData G P E₀ ι t)
    (σ : Fin t → Fin t → V → E) :
    (historyOfRoundData D σ).Consistent (G := G) := fun _ _ _ => rfl

/-- Every round of the driver's history starts with a forest. -/
theorem isForest_historyOfRoundData {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ}
    {P : Finset V} {E₀ : Finset E} (D : CallOut.RoundData G P E₀ ι t)
    (σ : Fin t → Fin t → V → E) :
    ∀ b i, IsForest G ((historyOfRoundData D σ).forest b i) :=
  fun b i => isForest_forestUpTo D (b, i)

/-- **§3.3's block structure for the driver's history.**  Within a block the spokes must be frozen
(§3.1's `hfreeze` of `History.monoRow_of_grow`), so the table is written `fun b _ => σb b`; the forest
grows by `forestUpTo_grow`, hence each block's action row is `PPPPFFF`. -/
theorem monoRow_historyOfRoundData {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ}
    {P : Finset V} {E₀ : Finset E} (D : CallOut.RoundData G P E₀ ι t)
    (σb : Fin t → V → E) (b : Fin t) (e : E) :
    MonoRow (fun _ i => (historyOfRoundData D (fun b' _ => σb b')).pref e b i) :=
  History.monoRow_of_grow (historyOfRoundData D (fun b' _ => σb b'))
    (historyOfRoundData_consistent D (fun b' _ => σb b'))
    (fun b' => ⟨σb b', fun _ => rfl⟩)
    (fun _ i j hij => forestUpTo_grow D hij) b e

/-- **The driver's history with the spoke table.**  Spokes are read off the batch selections
(`Spokes.spokeTable`), so they are incident at their vertices. -/
noncomputable def historyOfTable {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ}
    {P : Finset V} {E₀ : Finset E} (D : CallOut.RoundData G P E₀ ι t)
    (B : Fin t → Fin t → Finset E) (adm : E → Prop) (k : ℕ) [Nonempty E] : History V E t :=
  historyOfRoundData D (spokeTable (G := G) B adm k)

/-- The spoke table's entries are legal (incident) spokes. -/
theorem historyOfTable_spoke_incident {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ}
    {P : Finset V} {E₀ : Finset E} (D : CallOut.RoundData G P E₀ ι t)
    (B : Fin t → Fin t → Finset E) (adm : E → Prop) (k : ℕ) [Nonempty E] (hk : 1 ≤ k)
    (hadm : ∀ (i j : Fin t) (v : V), ∃ e ∈ Bv G v (B i j), adm e) :
    ∀ (i j : Fin t) (v : V), incident G v ((historyOfTable D B adm k).spoke i j v) :=
  fun i j v => spokeTable_incident (G := G) B adm k hk hadm i j v

/-! ## §3.5's bound for the driver's own history -/

/-- The action the driver's history records for `e` at round `(b, i)`, spelled with `actOf`. -/
noncomputable def prefAct {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ} {P : Finset V}
    {E₀ : Finset E} (D : CallOut.RoundData G P E₀ ι t) (σ : Fin t → Fin t → V → E) (e : E) :
    Fin t → Fin t → Pref :=
  fun b i => actOf G (σ b i) (forestUpTo D (b, i)) e

/-- `bad` for the driver's recorded action — Lemma 3.11's per-edge event, without the `History`
wrapper. -/
noncomputable def badOf {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ} {P : Finset V}
    {E₀ : Finset E} (D : CallOut.RoundData G P E₀ ι t) (σ : Fin t → Fin t → V → E) (e : E)
    (p : Fin t × Fin t) : Prop :=
  bad (prefAct D σ e) p

/-- `X_H(ρ)` for the driver's history, as a plain edge count. -/
noncomputable def lostOf {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ} {P : Finset V}
    {E₀ : Finset E} (D : CallOut.RoundData G P E₀ ι t) (σ : Fin t → Fin t → V → E)
    (slot : E → Fin t × Fin t) : ℕ :=
  ((Finset.univ : Finset E).filter fun e => badOf D σ e (slot e)).card

theorem historyOfRoundData_lost {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ} {P : Finset V}
    {E₀ : Finset E} (D : CallOut.RoundData G P E₀ ι t) (σ : Fin t → Fin t → V → E)
    (slot : E → Fin t × Fin t) :
    (historyOfRoundData D σ).lost slot = lostOf D σ slot := rfl

theorem historyOfRoundData_errOf {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ} {P : Finset V}
    {E₀ : Finset E} (D : CallOut.RoundData G P E₀ ι t) (σ : Fin t → Fin t → V → E)
    (est : E → Pref) (e : E) (p : Fin t × Fin t) :
    (historyOfRoundData D σ).errOf est e p ↔ (badOf D σ e p ∨ est e ≠ prefAct D σ e p.1 p.2) :=
  Iff.rfl

/-- **§3.5's display-form error bound for the driver's history.**  `card_U_le_display_form_of_geometry`
with the history that the driver builds: consistency and the per-round forest invariant are theorems
there, so the remaining premises are `hFsp` (no forest edge is a spoke), the per-edge error premise,
Lemma 3.11's `lost` bound and the numeric parameters. -/
theorem card_U_le_display_form_of_roundData {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ}
    {P : Finset V} {E₀ : Finset E} (D : CallOut.RoundData G P E₀ ι t)
    (σ : Fin t → Fin t → V → E) (slot : E → Fin t × Fin t)
    (eN : ∀ (b i : Fin t), Ground G (σ b i) (forestUpTo D (b, i)) ≃
      Fin (Fintype.card (Ground G (σ b i) (forestUpTo D (b, i)))))
    (c : ∀ r : Fin t × Fin t, {e : E // slot e = r} → Pref)
    (hc : ∀ r, c r ∈ geomFamily (G := G) (historyOfRoundData D σ) slot (fun b i => eN b i) r)
    (hFsp : ∀ (b i : Fin t) (g : E), g ∈ forestUpTo D (b, i) → ¬ IsSpoke (σ b i) g)
    {m n : ℝ} (ht : 2 ≤ t)
    (h : ∀ e ∈ E₀, ¬ supported G D.toCall.F e →
      (historyOfRoundData D σ).errOf (fun e => c (slot e) ⟨e, rfl⟩) e (slot e))
    (hlost : ((historyOfRoundData D σ).lost slot : ℝ) * Real.log 2 ≤
      (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 * Real.sqrt (m * n) + 2 * m / (t : ℝ))
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hmE : (Fintype.card E : ℝ) ≤ m) :
    ∃ S : ∀ r : Fin t × Fin t, Finset {e : E // slot e = r},
      (∀ r, (S r).card ≤ 2 * t *
        (Nat.ceil (Real.log
          ((geomFamily (G := G) (historyOfRoundData D σ) slot (fun b i => eN b i) r).card : ℝ))
          + 1)) ∧
      ((∀ r (x : {e : E // slot e = r}), x ∈ S r →
          c (slot x.1) ⟨x.1, rfl⟩ = (historyOfRoundData D σ).pref x.1 r.1 r.2) →
        ((D.toCall.U).card : ℝ) ≤ 10 * (t : ℝ) ^ 2 * Real.sqrt (m * n) +
          4 * m / (t : ℝ)) := by
  exact card_U_le_display_form_of_geometry (G := G) (D := D) (H := historyOfRoundData D σ) slot
    (fun b i => eN b i) c hc (historyOfRoundData_consistent D σ)
    (isForest_historyOfRoundData D σ) hFsp ht h hlost hm hn hmE

/-- **The same bound, with the two history-shaped premises written through `actOf`.**  This is
`card_U_le_display_form_of_roundData` with `History.errOf`/`History.lost` unfolded: the caller sees
only `badOf`/`lostOf` and §3.1's action rule. -/
theorem card_U_le_display_form_of_roundData_actOf {ι : Type*} [Fintype ι] [DecidableEq ι]
    {t : ℕ} {P : Finset V} {E₀ : Finset E} (D : CallOut.RoundData G P E₀ ι t)
    (σ : Fin t → Fin t → V → E) (slot : E → Fin t × Fin t)
    (eN : ∀ (b i : Fin t), Ground G (σ b i) (forestUpTo D (b, i)) ≃
      Fin (Fintype.card (Ground G (σ b i) (forestUpTo D (b, i)))))
    (c : ∀ r : Fin t × Fin t, {e : E // slot e = r} → Pref)
    (hc : ∀ r, c r ∈ geomFamily (G := G) (historyOfRoundData D σ) slot (fun b i => eN b i) r)
    (hFsp : ∀ (b i : Fin t) (g : E), g ∈ forestUpTo D (b, i) → ¬ IsSpoke (σ b i) g)
    {m n : ℝ} (ht : 2 ≤ t)
    (h : ∀ e ∈ E₀, ¬ supported G D.toCall.F e →
      badOf D σ e (slot e) ∨ c (slot e) ⟨e, rfl⟩ ≠ prefAct D σ e (slot e).1 (slot e).2)
    (hlost : (lostOf D σ slot : ℝ) * Real.log 2 ≤
      (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 * Real.sqrt (m * n) + 2 * m / (t : ℝ))
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hmE : (Fintype.card E : ℝ) ≤ m) :
    ∃ S : ∀ r : Fin t × Fin t, Finset {e : E // slot e = r},
      (∀ r, (S r).card ≤ 2 * t *
        (Nat.ceil (Real.log
          ((geomFamily (G := G) (historyOfRoundData D σ) slot (fun b i => eN b i) r).card : ℝ))
          + 1)) ∧
      ((∀ r (x : {e : E // slot e = r}), x ∈ S r →
          c (slot x.1) ⟨x.1, rfl⟩ = prefAct D σ x.1 r.1 r.2) →
        ((D.toCall.U).card : ℝ) ≤ 10 * (t : ℝ) ^ 2 * Real.sqrt (m * n) +
          4 * m / (t : ℝ)) := by
  have h' : ∀ e ∈ E₀, ¬ supported G D.toCall.F e →
      (historyOfRoundData D σ).errOf (fun e => c (slot e) ⟨e, rfl⟩) e (slot e) := by
    intro e he hne
    exact (historyOfRoundData_errOf D σ _ e (slot e)).mpr (h e he hne)
  have hlost' : ((historyOfRoundData D σ).lost slot : ℝ) * Real.log 2 ≤
      (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 * Real.sqrt (m * n) + 2 * m / (t : ℝ) := by
    rw [historyOfRoundData_lost]
    exact hlost
  rcases card_U_le_display_form_of_roundData D σ slot eN c hc hFsp ht h' hlost' hm hn hmE
    with ⟨S, hScard, hcount⟩
  refine ⟨S, hScard, fun hagree => hcount (fun r x hx => ?_)⟩
  have hx := hagree r x hx
  show c (slot x.1) ⟨x.1, rfl⟩ = (historyOfRoundData D σ).pref x.1 r.1 r.2
  rw [historyOfRoundData_pref]
  exact hx

end DLMST