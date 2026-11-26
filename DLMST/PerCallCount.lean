import DLMST.LevelWork
import DLMST.InputCount
import DLMST.InstanceCount

/-!
# The per-call §3.5/§3.6 numbers, produced from the driver's own data

`LevelWork.chain_work_linear_counts` and `LevelWork.display_of_strategy_of_nat_counts` consume two
numbers per call:

* `|U(F)| ≤ 10 t² √(m n) + 4m/t` — §3.5's sampling estimate;
* `Σᵢ|Eᵢ| ≤ |U(F)| + 2t²(n−1) + t(n−1+r²n)` — p. 24's input count, `r = 8t³`.

This file produces both from the driver's decision data instead of assuming them:

* `KidBoundCall` — the p. 24 input data of one call: the dispatched edges lie in
  `U(F) ∪ ⋃ roundIn ∪ ⋃ blkIn`, each round input has at most `2(n−1)` edges, each block input at most
  `(n−1)+r²n` (`r = 8t³`).  `KidBoundCall.ofForests` replaces the two numeric sizes by the paper's
  decomposition "old forest + new forest" and "old forest + portal edges", using
  `InputCount.card_roundIn_le` / `card_blkIn_le`.
* `KidBoundCall.hrnd` — the input count in ℕ, at the call's own `m = |E₀|`, `n = |P|`.
* `EvidenceOn.herrU` — §3.5's estimate, re-exported per call.
* `KidBoundCall.hrnd_level` / `EvidenceOn.herrU_level` — the same two numbers stamped with the level's
  `t_d = γ(d+1)³`, i.e. exactly the `hU`/`hrnd` shapes of `LevelWork`, for a *single* call.  These are
  the non-vacuous per-call statements: the premise `(t : ℝ) = γ(d+1)³` is satisfiable per node
  (`level_t_of_nat`, e.g. `γ = 16`).
* `driver_herrU_chain` / `driver_hrnd_chain` / `display_of_driver_derived` /
  `work_linear_of_driver_derived` — the same numbers along a root's level chain, for the synthesized
  strategy `driverStrategy`.  Here the bridge "the instance's own `t` is the level's `t_d`" is the
  `htd` hypothesis: it is per-call bookkeeping (the paper's `t_c = γ(d−c+1)³`), and a *global*
  instance-indexed version is impossible (`Strategy.htd_all_roots_impossible`).  So the chain-level
  capstones are conditional on that identification, while the per-call theorems above are not.

Everything is counting; the constants are the paper's (`10`, `2`, `1`, `64`), and no probability
statement is made here (the estimate enters through the already-derived §3.5 count).
-/

open Classical

namespace DLMST

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

/-! ## 1. The p. 24 input data of one call -/

namespace DriverCall

variable {P : Finset V} {E₀ : Finset E} {t : ℕ}

/-- **The input data of one driver call.**  Every dispatched edge is retained or lies in one of the
round inputs / block inputs; a round input has at most `2(n−1)` edges and a block input at most
`(n−1) + r²n` with `r = 8t³` and `n = |P|`.  This is the only procedure-specific input of §3.6's
second count (`sum_kidE_le_inputs`); disjointness and the arithmetic are free. -/
structure KidBoundCall (R : DriverCall G P E₀ t) where
  roundIn : Fin (t ^ 2) → Finset E
  blkIn : Fin t → Finset E
  hsub : ∀ p : Fin (t ^ 2) × Fin 1,
    R.roundData.inp' p ⊆
      R.roundData.toCall.U ∪ (Finset.univ.biUnion roundIn ∪ Finset.univ.biUnion blkIn)
  hround : ∀ i, (roundIn i).card ≤ 2 * (P.card - 1)
  hblk : ∀ b, (blkIn b).card ≤ (P.card - 1) + (8 * t ^ 3) ^ 2 * P.card

/-- **The same data in the paper's decomposition.**  A round's input is the old forest plus the
round's new forest (`|Fold|, |Fnew| ≤ n−1`); a block's input is the old forest plus at most `r²n`
portal edges.  The two numeric sizes of `KidBoundCall` are then *derived*
(`InputCount.card_roundIn_le`, `card_blkIn_le`). -/
noncomputable def KidBoundCall.ofForests (R : DriverCall G P E₀ t)
    {roundIn : Fin (t ^ 2) → Finset E} {blkIn : Fin t → Finset E}
    {Fold : Finset E} {Fnew : Fin (t ^ 2) → Finset E} {Dset : Fin t → Finset E}
    {r : ℕ}
    (hsub : ∀ p : Fin (t ^ 2) × Fin 1,
      R.roundData.inp' p ⊆
        R.roundData.toCall.U ∪ (Finset.univ.biUnion roundIn ∪ Finset.univ.biUnion blkIn))
    (hround : ∀ i, roundIn i ⊆ Fold ∪ Fnew i)
    (hblk : ∀ b, blkIn b ⊆ Fold ∪ Dset b)
    (hFold : Fold.card ≤ P.card - 1) (hFnew : ∀ i, (Fnew i).card ≤ P.card - 1)
    (hD : ∀ b, (Dset b).card ≤ r ^ 2 * P.card)
    (hr : r = 8 * t ^ 3) :
    KidBoundCall R where
  roundIn := roundIn
  blkIn := blkIn
  hsub := hsub
  hround := fun i => card_roundIn_le (hround i) hFold (hFnew i)
  hblk := fun b => by
    rw [← hr]
    exact card_blkIn_le (hblk b) hFold (hD b)

/-- **§3.6's input count for one call, at `m = |E₀|` and `n = |P|`.**  The rounds' dispatch
containment and the per-round / per-block sizes give
`Σ|Eᵢ| ≤ |U(F)| + 2t²(n−1) + t(n−1+r²n)` with `r = 8t³` — the paper's p. 24 count. -/
theorem KidBoundCall.hrnd (R : DriverCall G P E₀ t) (KB : KidBoundCall R) :
    (∑ i, (R.roundData.toCall.kidE i).card) ≤
      (R.roundData.toCall.U).card + 2 * t ^ 2 * (P.card - 1) +
        t * ((P.card - 1) + (8 * t ^ 3) ^ 2 * P.card) :=
  CallOut.RoundData.sum_kidE_le_display_form (D := R.roundData)
    (roundIn := KB.roundIn) (blkIn := KB.blkIn) (r := 8 * t ^ 3) (n := P.card)
    KB.hsub KB.hround KB.hblk

/-- The same count over the reals, with the natural subtraction kept as a cast. -/
theorem KidBoundCall.hrnd_cast (R : DriverCall G P E₀ t) (KB : KidBoundCall R) :
    (((∑ i, (R.roundData.toCall.kidE i).card) : ℕ) : ℝ) ≤
      ((R.roundData.toCall.U).card : ℝ) +
        2 * (t : ℝ) ^ 2 * ((P.card - 1 : ℕ) : ℝ) +
          (t : ℝ) * (((P.card - 1 : ℕ) : ℝ) +
            (8 * (t : ℝ) ^ 3) ^ 2 * (P.card : ℝ)) := by
  exact_mod_cast KB.hrnd R

/-- The level-stamped form: the call's `t` is the level's `t_d = γ(d+1)³`.  This is precisely the
`hrnd` premise of `LevelWork`, for one call. -/
theorem KidBoundCall.hrnd_level (R : DriverCall G P E₀ t) (KB : KidBoundCall R)
    {γ : ℝ} {d : ℕ} (ht : (t : ℝ) = γ * ((d : ℝ) + 1) ^ 3) :
    (((∑ i, (R.roundData.toCall.kidE i).card) : ℕ) : ℝ) ≤
      ((R.roundData.toCall.U).card : ℝ) +
        2 * (γ * ((d : ℝ) + 1) ^ 3) ^ 2 * (((P.card - 1 : ℕ) : ℝ)) +
          (γ * ((d : ℝ) + 1) ^ 3) *
            ((((P.card - 1 : ℕ) : ℝ)) +
              (8 * (γ * ((d : ℝ) + 1) ^ 3) ^ 3) ^ 2 * (P.card : ℝ)) := by
  have h := KB.hrnd_cast R
  simpa only [ht] using h

/-- **The level's `t` is a natural number for `γ = 16`** (and every `d`), so the level-stamped
premise of the per-call theorems is satisfiable, not vacuous. -/
theorem level_t_of_nat (d : ℕ) :
    ((16 * (d + 1) ^ 3 : ℕ) : ℝ) = (16 : ℝ) * ((d : ℝ) + 1) ^ 3 := by
  push_cast
  ring

end DriverCall

/-! ## 2. §3.5's estimate at one call, level-stamped -/

namespace DriverCall

variable {P : Finset V} {E₀ : Finset E} {t : ℕ} [Nonempty E]

/-- **§3.5's bound for one call, instance-local `m = |E₀|`.**  Re-export of
`EvidenceOn.card_U_le_number_bound` under the name the level account consumes. -/
theorem EvidenceOn.herrU (R : DriverCall G P E₀ t) (Ev : EvidenceOn R) (ht : 2 ≤ t)
    (agree : ∀ (r : Fin t × Fin t) (x : {e : E // e ∈ E₀ ∧ R.sched e = r}),
      x ∈ sampleSetsOn E₀ ht R.sched (geomFamilyOn (G := G) R.history R.sched E₀ R.eN) r →
      Ev.c (R.sched x.1) ⟨x.1, x.2.1, rfl⟩ = R.history.pref x.1 r.1 r.2) :
    ((R.roundData.toCall.U).card : ℝ) ≤
      10 * (t : ℝ) ^ 2 * Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) +
        4 * (E₀.card : ℝ) / (t : ℝ) :=
  Ev.card_U_le_number_bound (R := R) ht agree

/-- The level-stamped form of §3.5's bound: exactly the `hU` premise of `LevelWork`, for one call. -/
theorem EvidenceOn.herrU_level (R : DriverCall G P E₀ t) (Ev : EvidenceOn R) (ht : 2 ≤ t)
    (agree : ∀ (r : Fin t × Fin t) (x : {e : E // e ∈ E₀ ∧ R.sched e = r}),
      x ∈ sampleSetsOn E₀ ht R.sched (geomFamilyOn (G := G) R.history R.sched E₀ R.eN) r →
      Ev.c (R.sched x.1) ⟨x.1, x.2.1, rfl⟩ = R.history.pref x.1 r.1 r.2)
    {γ : ℝ} {d : ℕ} (htd : (t : ℝ) = γ * ((d : ℝ) + 1) ^ 3) :
    ((R.roundData.toCall.U).card : ℝ) ≤
      10 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 *
          Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ))) +
        4 * (E₀.card : ℝ) / (γ * ((d : ℝ) + 1) ^ 3) := by
  have h := Ev.herrU R ht agree
  simpa only [htd, mul_assoc] using h

end DriverCall

/-! ## 3. The same two numbers for the synthesized strategy -/

namespace DriverCall

variable [Nonempty E] {tOf : Finset V → Finset E → ℕ}

/-- The per-instance p. 24 input data of the synthesized strategy. -/
abbrev KidBound (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀))
    (P : Finset V) (E₀ : Finset E) : Type _ :=
  KidBoundCall (DR P E₀)

/-- The children's sum of the synthesized strategy, transported across the `Fin (t²)` reindexing
(`CallOut.sum_kidE_reindex`).  Stated as an equality so that the dependent index of the sum never has
to be rewritten in an inequality. -/
theorem sum_kidE_driverStrategy
    (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀))
    (P : Finset V) (E₀ : Finset E) :
    (∑ i, ((driverStrategy DR P E₀).2.kidE i).card) =
      ∑ i : Fin (tOf P E₀ ^ 2) × Fin 1,
        ((driverRoundData DR P E₀).toCall.kidE i).card := by
  show (∑ i : Fin (tOf P E₀ ^ 2 * 1),
      ((CallOut.reindex finProdFinEquiv (driverRoundData DR P E₀).toCall).kidE i).card) = _
  exact CallOut.sum_kidE_reindex finProdFinEquiv _

/-- The strategy's retained set is the round data's (`CallOut.reindex_U`). -/
theorem U_driverStrategy
    (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀))
    (P : Finset V) (E₀ : Finset E) :
    ((driverStrategy DR P E₀).2.U) = ((driverRoundData DR P E₀).toCall.U) := by
  show (CallOut.reindex finProdFinEquiv (driverRoundData DR P E₀).toCall).U = _
  exact CallOut.reindex_U _ _

/-- **The children's total input of the synthesized strategy**, with the `Fin (t²)` reindexing
transported (`CallOut.sum_kidE_reindex`).  This is the `hrnd` premise of `LevelWork` at the
instance's own `t`, in ℕ. -/
theorem hrnd_strategy
    (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀))
    (KB : ∀ (P : Finset V) (E₀ : Finset E), KidBound DR P E₀)
    (P : Finset V) (E₀ : Finset E) :
    (∑ i, ((driverStrategy DR P E₀).2.kidE i).card) ≤
      ((driverStrategy DR P E₀).2.U).card +
        2 * (tOf P E₀) ^ 2 * (P.card - 1) +
          (tOf P E₀) * ((P.card - 1) + (8 * tOf P E₀ ^ 3) ^ 2 * P.card) := by
  have h := (KB P E₀).hrnd (DR P E₀)
  rw [sum_kidE_driverStrategy DR P E₀, U_driverStrategy DR P E₀]
  exact h

/-- The same over the reals. -/
theorem hrnd_strategy_cast
    (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀))
    (KB : ∀ (P : Finset V) (E₀ : Finset E), KidBound DR P E₀)
    (P : Finset V) (E₀ : Finset E) :
    (((∑ i, ((driverStrategy DR P E₀).2.kidE i).card) : ℕ) : ℝ) ≤
      (((driverStrategy DR P E₀).2.U).card : ℝ) +
        2 * (tOf P E₀ : ℝ) ^ 2 * ((P.card - 1 : ℕ) : ℝ) +
          (tOf P E₀ : ℝ) * (((P.card - 1 : ℕ) : ℝ) +
            (8 * (tOf P E₀ : ℝ) ^ 3) ^ 2 * (P.card : ℝ)) := by
  exact_mod_cast hrnd_strategy DR KB P E₀

/-- **The strategy's retained set at the instance's own `t`** — `driverScheme_herrU_on`
transported across the reindexing. -/
theorem herrU_strategy
    (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀))
    (EvOn : ∀ (P : Finset V) (E₀ : Finset E), DriverCall.EvidenceOn (DR P E₀))
    (htOf : ∀ (P : Finset V) (E₀ : Finset E), 2 ≤ tOf P E₀)
    (agree : ∀ (P : Finset V) (E₀ : Finset E) (r : Fin (tOf P E₀) × Fin (tOf P E₀))
      (x : {e : E // e ∈ E₀ ∧ (DR P E₀).sched e = r}),
      x ∈ sampleSetsOn E₀ (htOf P E₀) (DR P E₀).sched
        (geomFamilyOn (G := G) (DR P E₀).history (DR P E₀).sched E₀ (DR P E₀).eN) r →
      (EvOn P E₀).c ((DR P E₀).sched x.1) ⟨x.1, x.2.1, rfl⟩ =
        (DR P E₀).history.pref x.1 r.1 r.2)
    (P : Finset V) (E₀ : Finset E) :
    (((driverStrategy DR P E₀).2.U).card : ℝ) ≤
      10 * ((tOf P E₀ : ℝ) ^ 2 * Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ))) +
        4 * (E₀.card : ℝ) / (tOf P E₀ : ℝ) := by
  have h := driverScheme_herrU_on DR EvOn htOf agree P E₀
  rwa [driverStrategy_U]

/-! ## 4. Along a root's level chain -/

/-- **`hU` along the chain**: the retained-set bound stamped with the level's `t_d = γ(d+1)³`.  The
only extra input is the per-call identification `t = t_d` (`htd`). -/
theorem herrU_chain
    (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀))
    (EvOn : ∀ (P : Finset V) (E₀ : Finset E), DriverCall.EvidenceOn (DR P E₀))
    (htOf : ∀ (P : Finset V) (E₀ : Finset E), 2 ≤ tOf P E₀)
    (agree : ∀ (P : Finset V) (E₀ : Finset E) (r : Fin (tOf P E₀) × Fin (tOf P E₀))
      (x : {e : E // e ∈ E₀ ∧ (DR P E₀).sched e = r}),
      x ∈ sampleSetsOn E₀ (htOf P E₀) (DR P E₀).sched
        (geomFamilyOn (G := G) (DR P E₀).history (DR P E₀).sched E₀ (DR P E₀).eN) r →
      (EvOn P E₀).c ((DR P E₀).sched x.1) ⟨x.1, x.2.1, rfl⟩ =
        (DR P E₀).history.pref x.1 r.1 r.2)
    (P : Finset V) (E₀ : Finset E) {γ : ℝ}
    (htd : ∀ (d : ℕ), ∀ a ∈ (Level.chain P E₀ (driverStrategy DR)
      (driverStrategy_wf DR) d).insts,
      (tOf a.1 a.2 : ℝ) = γ * ((d : ℝ) + 1) ^ 3) :
    ∀ (d : ℕ), ∀ a ∈ (Level.chain P E₀ (driverStrategy DR)
      (driverStrategy_wf DR) d).insts,
      (((driverStrategy DR a.1 a.2).2.U).card : ℝ) ≤
        10 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 *
            Real.sqrt ((a.2.card : ℝ) * (a.1.card : ℝ))) +
          4 * (a.2.card : ℝ) / (γ * ((d : ℝ) + 1) ^ 3) := by
  intro d a ha
  have h := herrU_strategy DR EvOn htOf agree a.1 a.2
  have htd' := htd d a ha
  simpa only [← htd'] using h

/-- **`hrnd` along the chain**: the children's input bound stamped with the level's `t_d`. -/
theorem hrnd_chain
    (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀))
    (KB : ∀ (P : Finset V) (E₀ : Finset E), KidBound DR P E₀)
    (P : Finset V) (E₀ : Finset E) {γ : ℝ}
    (htd : ∀ (d : ℕ), ∀ a ∈ (Level.chain P E₀ (driverStrategy DR)
      (driverStrategy_wf DR) d).insts,
      (tOf a.1 a.2 : ℝ) = γ * ((d : ℝ) + 1) ^ 3) :
    ∀ (d : ℕ), ∀ a ∈ (Level.chain P E₀ (driverStrategy DR)
      (driverStrategy_wf DR) d).insts,
      ((∑ i, ((driverStrategy DR a.1 a.2).2.kidE i).card : ℕ) : ℝ) ≤
        (((driverStrategy DR a.1 a.2).2.U).card : ℝ) +
          2 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 * (((a.1.card - 1 : ℕ) : ℝ))) +
            (γ * ((d : ℝ) + 1) ^ 3) *
              ((((a.1.card - 1 : ℕ) : ℝ)) +
                (8 * (γ * ((d : ℝ) + 1) ^ 3) ^ 3) ^ 2 * (a.1.card : ℝ)) := by
  intro d a ha
  have h := hrnd_strategy_cast DR KB a.1 a.2
  have htd' := htd d a ha
  rw [htd'] at h
  simpa only [mul_assoc] using h

/-! ## 5. §3.6 with both numbers derived -/

/-- **§3.6's display for the synthesized strategy, from the driver's data.**  Same conclusion as
`display_of_driver`, with `herrU` and `hrnd` no longer assumed: the first comes from the sampling
evidence `EvOn` and the algorithm's agreement with its own queries, the second from the p. 24 input
data `KB`.  Only the per-call level identification `htd` remains. -/
theorem display_of_driver_derived
    (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀))
    (EvOn : ∀ (P : Finset V) (E₀ : Finset E), DriverCall.EvidenceOn (DR P E₀))
    (htOf : ∀ (P : Finset V) (E₀ : Finset E), 2 ≤ tOf P E₀)
    (agree : ∀ (P : Finset V) (E₀ : Finset E) (r : Fin (tOf P E₀) × Fin (tOf P E₀))
      (x : {e : E // e ∈ E₀ ∧ (DR P E₀).sched e = r}),
      x ∈ sampleSetsOn E₀ (htOf P E₀) (DR P E₀).sched
        (geomFamilyOn (G := G) (DR P E₀).history (DR P E₀).sched E₀ (DR P E₀).eN) r →
      (EvOn P E₀).c ((DR P E₀).sched x.1) ⟨x.1, x.2.1, rfl⟩ =
        (DR P E₀).history.pref x.1 r.1 r.2)
    (KB : ∀ (P : Finset V) (E₀ : Finset E), KidBound DR P E₀)
    (P : Finset V) (E₀ : Finset E) {γ ε : ℝ}
    (hγ1 : 1 ≤ γ) (hε : 0 < ε) (hγε : 16 ≤ ε * γ)
    (hnm : (P.card : ℝ) ≤ 2 * (E₀.card : ℝ))
    (htd : ∀ (d : ℕ), ∀ a ∈ (Level.chain P E₀ (driverStrategy DR)
      (driverStrategy_wf DR) d).insts,
      (tOf a.1 a.2 : ℝ) = γ * ((d : ℝ) + 1) ^ 3) :
    ((driverStrategy DR P E₀).2.F.card : ℝ) +
        (((driverStrategy DR P E₀).2.U).card : ℝ) +
        (((∑ i, ((driverStrategy DR P E₀).2.kidE i).card) : ℕ) : ℝ) ≤
      ε * (E₀.card : ℝ) +
        (Real.sqrt 2 + γ ^ 2 * 800000 +
            Real.sqrt 2 * ((2 * γ ^ 2 + γ + 64 * γ ^ 7) * ((202 : ℝ) ^ 21 * 2))) *
          Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) := by
  refine display_of_strategy_of_nat_counts P E₀ (driverStrategy DR) (driverStrategy_wf DR)
    hγ1 hε hγε ?_ ?_ ?_
  · show (P.card : ℝ) ≤ 2 * (E₀.card : ℝ)
    exact hnm
  · exact fun d _ => herrU_chain DR EvOn htOf agree P E₀ htd d
  · exact fun d _ => hrnd_chain DR KB P E₀ htd d

/-- **§3.6's total work for the synthesized strategy, from the driver's data.**  Both per-call
numbers are produced (`herrU_chain`, `hrnd_chain`), so the level sum is linear with the paper's
constant — again modulo the per-call level identification `htd`. -/
theorem work_linear_of_driver_derived
    (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀))
    (EvOn : ∀ (P : Finset V) (E₀ : Finset E), DriverCall.EvidenceOn (DR P E₀))
    (htOf : ∀ (P : Finset V) (E₀ : Finset E), 2 ≤ tOf P E₀)
    (agree : ∀ (P : Finset V) (E₀ : Finset E) (r : Fin (tOf P E₀) × Fin (tOf P E₀))
      (x : {e : E // e ∈ E₀ ∧ (DR P E₀).sched e = r}),
      x ∈ sampleSetsOn E₀ (htOf P E₀) (DR P E₀).sched
        (geomFamilyOn (G := G) (DR P E₀).history (DR P E₀).sched E₀ (DR P E₀).eN) r →
      (EvOn P E₀).c ((DR P E₀).sched x.1) ⟨x.1, x.2.1, rfl⟩ =
        (DR P E₀).history.pref x.1 r.1 r.2)
    (KB : ∀ (P : Finset V) (E₀ : Finset E), KidBound DR P E₀)
    (P : Finset V) (E₀ : Finset E) {γ : ℝ} (hγ16 : 16 ≤ γ)
    (htd : ∀ (d : ℕ), ∀ a ∈ (Level.chain P E₀ (driverStrategy DR)
      (driverStrategy_wf DR) d).insts,
      (tOf a.1 a.2 : ℝ) = γ * ((d : ℝ) + 1) ^ 3) :
    ∀ D : ℕ, (∑ d ∈ Finset.range D,
        (((Level.chain P E₀ (driverStrategy DR) (driverStrategy_wf DR) d).verts : ℝ) +
          ((Level.chain P E₀ (driverStrategy DR) (driverStrategy_wf DR) d).edges : ℝ))) ≤
      4 / 3 * (P.card : ℝ) + 4 / 3 * ((E₀.card : ℝ) +
        (10 * (γ ^ 2 * 40000 * Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ))) +
          (64 * γ ^ 7 * ((202 : ℝ) ^ 21 * 2) + 2 * (40000 * γ ^ 2) + 40000 * γ) *
            (P.card : ℝ))) :=
  chain_work_linear_counts P E₀ (driverStrategy DR) (driverStrategy_wf DR) hγ16
    (herrU_chain DR EvOn htOf agree P E₀ htd)
    (hrnd_chain DR KB P E₀ htd)

/-- **Both §3.6 conclusions for the synthesized strategy, with the two per-call numbers derived
from the driver's data.** -/
theorem driver_display_and_work_derived
    (DR : ∀ (P : Finset V) (E₀ : Finset E), DriverCall G P E₀ (tOf P E₀))
    (EvOn : ∀ (P : Finset V) (E₀ : Finset E), DriverCall.EvidenceOn (DR P E₀))
    (htOf : ∀ (P : Finset V) (E₀ : Finset E), 2 ≤ tOf P E₀)
    (agree : ∀ (P : Finset V) (E₀ : Finset E) (r : Fin (tOf P E₀) × Fin (tOf P E₀))
      (x : {e : E // e ∈ E₀ ∧ (DR P E₀).sched e = r}),
      x ∈ sampleSetsOn E₀ (htOf P E₀) (DR P E₀).sched
        (geomFamilyOn (G := G) (DR P E₀).history (DR P E₀).sched E₀ (DR P E₀).eN) r →
      (EvOn P E₀).c ((DR P E₀).sched x.1) ⟨x.1, x.2.1, rfl⟩ =
        (DR P E₀).history.pref x.1 r.1 r.2)
    (KB : ∀ (P : Finset V) (E₀ : Finset E), KidBound DR P E₀)
    (P : Finset V) (E₀ : Finset E) {γ ε : ℝ}
    (hγ1 : 1 ≤ γ) (hγ16 : 16 ≤ γ) (hε : 0 < ε) (hγε : 16 ≤ ε * γ)
    (hnm : (P.card : ℝ) ≤ 2 * (E₀.card : ℝ))
    (htd : ∀ (d : ℕ), ∀ a ∈ (Level.chain P E₀ (driverStrategy DR)
      (driverStrategy_wf DR) d).insts,
      (tOf a.1 a.2 : ℝ) = γ * ((d : ℝ) + 1) ^ 3) :
    (((driverStrategy DR P E₀).2.F.card : ℝ) +
        (((driverStrategy DR P E₀).2.U).card : ℝ) +
        (((∑ i, ((driverStrategy DR P E₀).2.kidE i).card) : ℕ) : ℝ) ≤
      ε * (E₀.card : ℝ) +
        (Real.sqrt 2 + γ ^ 2 * 800000 +
            Real.sqrt 2 * ((2 * γ ^ 2 + γ + 64 * γ ^ 7) * ((202 : ℝ) ^ 21 * 2))) *
          Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ))) ∧
      ∀ D : ℕ, (∑ d ∈ Finset.range D,
        (((Level.chain P E₀ (driverStrategy DR) (driverStrategy_wf DR) d).verts : ℝ) +
          ((Level.chain P E₀ (driverStrategy DR) (driverStrategy_wf DR) d).edges : ℝ))) ≤
        4 / 3 * (P.card : ℝ) + 4 / 3 * ((E₀.card : ℝ) +
          (10 * (γ ^ 2 * 40000 * Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ))) +
            (64 * γ ^ 7 * ((202 : ℝ) ^ 21 * 2) + 2 * (40000 * γ ^ 2) + 40000 * γ) *
              (P.card : ℝ))) :=
  ⟨display_of_driver_derived DR EvOn htOf agree KB P E₀ hγ1 hε hγε hnm htd,
    work_linear_of_driver_derived DR EvOn htOf agree KB P E₀ hγ16 htd⟩

end DriverCall

end DLMST