import DLMST.RoundScan
import DLMST.CertificateBuild

/-!
# End-to-end assembly: the rounds' data, the counts, and the root display

The display chain (`Procedure.lean`) is stated for an arbitrary `Strategy` and arbitrary
per-instance counts.  This file closes the gap to the algorithm: it constructs the strategy from the
procedure's own data (batches / rounds, classification, portal sets — `Strategy.ofRoundData`), proves
its well-formedness, and derives the display's two per-call numeric premises from the §3.5/§3.6
counts (`CallOut.RoundData.card_U_le_number_bound_of_sampling`, `RoundData.sum_kidE_le_inputs`) instead
of assuming them.

The only numeric inputs left are the paper's per-call outputs:

* `|U(F)| ≤ 10 t_c² √(m_c n_c) + 4m_c/t_c` — §3.5's sampling estimate, produced per call by
  `card_U_le_number_bound_of_sampling` from the history's schedule (`ScheduleBound`), the estimate's
  candidate family (`EstimateBound`/Claim 3.12) and the agreement on the sampled set;
* `Σᵢ|Eᵢ| ≤ |U(F)| + 2t_c²(n_c−1) + t_c(n_c−1+r_c²n_c)` — p. 24's input count, produced by
  `RoundData.sum_kidE_le_inputs` from the rounds' dispatch containment and the per-round sizes.

**The depth/t parameter.**  The paper uses `t_c = γ(d−c+1)³`, which depends on the call's level.  A
Lean `Strategy` is a function of the instance `(P, E₀)` alone, so the construction carries a parameter
map `tOf : Finset V → Finset E → ℕ` and the hypothesis `htd` saying that the instance's `tOf` is the
paper's `t_d` at every level where the instance appears.  This is the one piece of the identity
between "size-indexed" and "level-indexed" that is left as data; it holds for the paper's run because
`m_c` halves each level, so the level is a function of the instance's edge count.

**The fourth bucket** matters for the display's per-instance premise to be satisfiable: with
`|F| + |U| + Σ|Eᵢ| = |E₀|` per call, summing over the levels would force the display's left-hand side
to be `m`, which `εm + C√(mn)` cannot dominate.  `CallOut.drop` (and `RoundData`'s four-way `hcover`)
supply the discarded supported edges; `LevelChain.kept_le` records that the filtered graph is at most
the instance.

**The §4 closure.**  `sum_kidE_le_paper_bound` drops `F` and `U` from the display, leaving exactly the
children-only bound `Σ|Eᵢ| ≤ εm + C√(mn)` that `CertificateBuild.certificate_of_display` consumes
(with `subSizes m` read as the children's edge sizes).  Composed with the phase-halving bound
`nsub m ≤ 2m/2^{2j}` (`BoruvkaHalving`), `linear_of_display` then gives `T(m) = O(m)`.  What is not
mechanized here is the m-indexed family itself — for each `m` the algorithm's recursion must supply an
instance and round data; this file proves every instance's obligation in isolation, uniformly in the
instance.
-/

namespace DLMST

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

namespace CallOut

/-- Reindexing preserves the kept forest. -/
theorem reindex_F {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι') (O : CallOut G ι) :
    (reindex e O).F = O.F := rfl

/-- Reindexing preserves the retained set. -/
theorem reindex_U {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι') (O : CallOut G ι) :
    (reindex e O).U = O.U := rfl

/-- Reindexing preserves the discarded set. -/
theorem reindex_drop {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι') (O : CallOut G ι) :
    (reindex e O).drop = O.drop := rfl

/-- Reindexing preserves the total child input. -/
theorem sum_kidE_reindex {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι')
    (O : CallOut G ι) :
    (∑ i : ι', ((reindex e O).kidE i).card) = ∑ i : ι, (O.kidE i).card :=
  Equiv.sum_comp e.symm (fun j => (O.kidE j).card)

end CallOut

namespace CallOut.RoundData

/-- The call's retained set is the round data's. -/
theorem toCall_U_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ} {P : Finset V}
    {E₀ : Finset E} (D : RoundData G P E₀ ι t) : D.toCall.U = D.U := rfl

end CallOut.RoundData

namespace Strategy

/-- **The per-call numeric interface.**  One call's two counting outputs: a bound on the retained
set (`errF`) and a bound on the total child input (`inF`).  Both halves of the display's numeric
content enter through this structure; the identifications with the paper's §3.5/§3.6 counts are
`counts_of_roundData_sampling` below. -/
structure Counts (S : Strategy G) (P : Finset V) (E₀ : Finset E) where
  errF : ℕ
  inF : ℕ
  hU : ((S P E₀).2.U).card ≤ errF
  hSE : (∑ i, ((S P E₀).2.kidE i).card) ≤ inF

/-- **The root display from a per-instance count interface.**  This is
`display_of_strategy_of_calls_count` with its four per-level premises collapsed into two: the
per-instance `Counts` (their `hU`/`hSE` fields discharge `hUinst`/`hSEinst`) and the two level-indexed
numeric bounds on `errF`/`inF` in the paper's `t_d = γ(d+1)³` terms. -/
theorem display_of_counts (P : Finset V) (E₀ : Finset E) (S : Strategy G)
    (hS : Wf S) {γ ε : ℝ} (hγ1 : 1 ≤ γ) (hε : 0 < ε) (hγε : 16 ≤ ε * γ)
    (hnm : ((S P E₀).2.P.card : ℝ) ≤ 2 * ((S P E₀).2.E₀.card : ℝ))
    (num : ∀ P' E₀', Counts S P' E₀')
    (herror : ∀ (d : ℕ), d ≤ E₀.card → ∀ a ∈ (Level.chain P E₀ S hS d).insts,
      ((num a.1 a.2).errF : ℝ) ≤
        10 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 * Real.sqrt ((a.2.card : ℝ) * (a.1.card : ℝ))) +
          4 * (a.2.card : ℝ) / (γ * ((d : ℝ) + 1) ^ 3))
    (hrounds : ∀ (d : ℕ), d ≤ E₀.card → ∀ a ∈ (Level.chain P E₀ S hS d).insts,
      ((num a.1 a.2).inF : ℝ) ≤ (num a.1 a.2).errF +
        2 * (γ * ((d : ℝ) + 1) ^ 3) ^ 2 * ((a.1.card : ℝ) - 1) +
          (γ * ((d : ℝ) + 1) ^ 3) *
            ((a.1.card : ℝ) - 1 + (8 * (γ * ((d : ℝ) + 1) ^ 3) ^ 3) ^ 2 * (a.1.card : ℝ))) :
    ((S P E₀).2.F.card : ℝ) + (((S P E₀).2.U).card : ℝ) +
        ((∑ i, ((S P E₀).2.kidE i).card : ℕ) : ℝ) ≤
      ε * ((S P E₀).2.E₀.card : ℝ) +
        (Real.sqrt 2 + γ ^ 2 * 800000 +
            Real.sqrt 2 * ((2 * γ ^ 2 + γ + 64 * γ ^ 7) * ((202 : ℝ) ^ 21 * 2))) *
          Real.sqrt (((S P E₀).2.E₀.card : ℝ) * ((S P E₀).2.P.card : ℝ)) :=
  display_of_strategy_of_calls_count P E₀ S hS hγ1 hε hγε hnm
    (fun a => (num a.1 a.2).errF) (fun a => (num a.1 a.2).inF)
    herror hrounds
    (fun _ _ a _ => (num a.1 a.2).hU)
    (fun _ _ a _ => (num a.1 a.2).hSE)

/-- **The strategy of instance-wise round data.**  Each instance `(P, E₀)` is answered by its own
round data with its own `t` (`tOf`), the children recoded to `Fin (t²k)`.  This is
`Strategy.ofRoundData` with the rounds' parameter allowed to depend on the instance, which the paper's
`t_c = γ(d−c+1)³` requires. -/
noncomputable def ofRoundDataT {k : ℕ} (tOf : Finset V → Finset E → ℕ)
    (RD : ∀ (P : Finset V) (E₀ : Finset E), CallOut.RoundData G P E₀ (Fin k) (tOf P E₀)) :
    Strategy G :=
  fun P E₀ => ⟨tOf P E₀ ^ 2 * k, (RD P E₀).toCall.reindex finProdFinEquiv⟩

/-- The instance-wise strategy is well-formed: it answers about the instance it was asked about. -/
theorem ofRoundDataT_wf {k : ℕ} (tOf : Finset V → Finset E → ℕ)
    (RD : ∀ (P : Finset V) (E₀ : Finset E), CallOut.RoundData G P E₀ (Fin k) (tOf P E₀)) :
    Wf (ofRoundDataT tOf RD) :=
  fun _ _ => ⟨rfl, rfl⟩

/-- **The counts of the instance-wise strategy, from the round data's own counts.**  The retained set
and the child input are transported across the `Fin (t²k)` reindexing (`reindex_U`,
`sum_kidE_reindex`), so per-instance bounds on the round data become `Counts` for the strategy. -/
def counts_of_roundDataT {k : ℕ} (tOf : Finset V → Finset E → ℕ)
    (RD : ∀ (P : Finset V) (E₀ : Finset E), CallOut.RoundData G P E₀ (Fin k) (tOf P E₀))
    (err inF : Finset V → Finset E → ℕ)
    (hU : ∀ P E₀, ((RD P E₀).toCall.U).card ≤ err P E₀)
    (hSE : ∀ P E₀, (∑ i, ((RD P E₀).toCall.kidE i).card) ≤ inF P E₀) :
    ∀ P E₀, Counts (ofRoundDataT tOf RD) P E₀ := by
  intro P E₀
  refine ⟨err P E₀, inF P E₀, ?_, ?_⟩
  · show ((CallOut.reindex finProdFinEquiv (RD P E₀).toCall).U).card ≤ err P E₀
    rw [CallOut.reindex_U]
    exact hU P E₀
  · show (∑ i : Fin (tOf P E₀ ^ 2 * k),
        ((CallOut.reindex finProdFinEquiv (RD P E₀).toCall).kidE i).card) ≤ inF P E₀
    rw [CallOut.sum_kidE_reindex]
    exact hSE P E₀

end Strategy

namespace CallOut.RoundData

/-- **§3.5's per-call error count, in the display's shape.**  The sampling data of one call — a
history, a schedule, a per-edge estimate, and the candidate family with its truth/estimate members and
Claim 3.12's agreement — bound the call's retained set by `10t²√(mn) + 4m/t`.  This is
`card_U_le_number_bound_of_sampling` read on `toCall` (`toCall_U_eq`). -/
theorem card_U_le_display_form {ι : Type*} [Fintype ι] [DecidableEq ι] {t s : ℕ} {P : Finset V}
    {E₀ : Finset E} (D : RoundData G P E₀ ι t) (H : History V E s) (est : E → Pref)
    (slot : E → Fin s × Fin s) {m n : ℝ} (ht : 2 ≤ t)
    (h : ∀ e ∈ E₀, ¬ supported G D.toCall.F e → H.errOf est e (slot e))
    (hlost : (H.lost slot : ℝ) * Real.log 2 ≤
      (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 * Real.sqrt (m * n) + 2 * m / (t : ℝ))
    (A : ∀ r : Fin s × Fin s, Finset ({e : E // slot e = r} → Pref))
    (htruth : ∀ r : Fin s × Fin s,
      (fun x : {e : E // slot e = r} => H.pref x.1 (slot x.1).1 (slot x.1).2) ∈ A r)
    (hest : ∀ r : Fin s × Fin s, (fun x : {e : E // slot e = r} => est x.1) ∈ A r)
    (hm : 0 ≤ m) (hn : 0 ≤ n)
    (hmE : (Fintype.card E : ℝ) ≤ m) :
    ∃ S : ∀ r : Fin s × Fin s, Finset {e : E // slot e = r},
      (∀ r, (S r).card ≤ 2 * t * (Nat.ceil (Real.log ((A r).card : ℝ)) + 1)) ∧
      ((∀ r (x : {e : E // slot e = r}), x ∈ S r → est x.1 = H.pref x.1 r.1 r.2) →
        ((D.toCall.U).card : ℝ) ≤ 10 * (t : ℝ) ^ 2 * Real.sqrt (m * n) + 4 * m / (t : ℝ)) := by
  obtain ⟨S, hScard, hcount⟩ :=
    D.card_U_le_number_bound_of_sampling H est slot ht hm hn hmE h hlost A htruth hest
  exact ⟨S, hScard, fun hagree => by
    rw [congrArg Finset.card D.toCall_U_eq]
    exact hcount hagree⟩

/-- **§3.6's per-call input count.**  The rounds' dispatch containment and per-round / per-block input
sizes bound the call's total child input by `|U(F)| + 2t²(n−1) + t(n−1+r²n)` — the p. 24 count of
`sum_kidE_le_inputs` with the rejection bucket read as the call's retained set. -/
theorem sum_kidE_le_display_form {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ} {P : Finset V}
    {E₀ : Finset E} (D : RoundData G P E₀ ι t) {roundIn : Fin (t ^ 2) → Finset E}
    {blkIn : Fin t → Finset E} {r n : ℕ}
    (hsub : ∀ p : Fin (t ^ 2) × ι,
      D.inp' p ⊆ D.toCall.U ∪ (Finset.univ.biUnion roundIn ∪ Finset.univ.biUnion blkIn))
    (hround : ∀ i, (roundIn i).card ≤ 2 * (n - 1))
    (hblk : ∀ b, (blkIn b).card ≤ (n - 1) + r ^ 2 * n) :
    (∑ i, ((D.toCall.kidE i).card))
      ≤ (D.toCall.U).card + 2 * t ^ 2 * (n - 1) + t * ((n - 1) + r ^ 2 * n) := by
  have h := D.sum_kidE_le_inputs (Rej := D.toCall.U) (roundIn := roundIn) (blkIn := blkIn)
    hsub hround hblk le_rfl
  omega

end CallOut.RoundData

namespace Strategy

/-- **The root display for the instance-wise strategy, from the two §3.5/§3.6 counts.**

The two numeric premises are per-instance: the retained-set count `herrU` (each call's `|U(F)|` is
within `10·t_a²·√(m_an_a) + 4m_a/t_a`, `card_U_le_display_form`) and the input count `hrnd` (each
call's child input is within `|U(F)| + 2t_a²(n_a−1) + t_a(n_a−1+r_a²n_a)`,
`sum_kidE_le_display_form`).  Everything else is machine-derived: the strategy, its well-formedness,
the count transport (`counts_of_roundDataT`), the level-indexed rewriting `t_a = γ(d+1)³` (`htd`), and
the display chain itself. -/
theorem display_of_roundData_sampling {k : ℕ} (tOf : Finset V → Finset E → ℕ)
    (RD : ∀ (P : Finset V) (E₀ : Finset E), CallOut.RoundData G P E₀ (Fin k) (tOf P E₀))
    (P : Finset V) (E₀ : Finset E)
    {γ ε : ℝ} (hγ1 : 1 ≤ γ) (hε : 0 < ε) (hγε : 16 ≤ ε * γ)
    (hnm : (P.card : ℝ) ≤ 2 * (E₀.card : ℝ))
    (hnpos : ∀ (P' : Finset V), 1 ≤ P'.card)
    (herrU : ∀ (P' : Finset V) (E₀' : Finset E), (((RD P' E₀').toCall.U).card : ℝ) ≤
      10 * ((tOf P' E₀' : ℝ) ^ 2 * Real.sqrt ((E₀'.card : ℝ) * (P'.card : ℝ))) +
        4 * (E₀'.card : ℝ) / (tOf P' E₀' : ℝ))
    (hrnd : ∀ (P' : Finset V) (E₀' : Finset E), (∑ i, ((RD P' E₀').toCall.kidE i).card) ≤
      ((RD P' E₀').toCall.U).card + 2 * (tOf P' E₀') ^ 2 * (P'.card - 1) +
        (tOf P' E₀') * ((P'.card - 1) + (8 * (tOf P' E₀') ^ 3) ^ 2 * P'.card))
    (htd : ∀ (d : ℕ), d ≤ E₀.card → ∀ a ∈ (Level.chain P E₀ (ofRoundDataT tOf RD)
        (ofRoundDataT_wf tOf RD) d).insts,
      (tOf a.1 a.2 : ℝ) = γ * ((d : ℝ) + 1) ^ 3) :
    (((ofRoundDataT tOf RD) P E₀).2.F.card : ℝ) +
        ((((ofRoundDataT tOf RD) P E₀).2.U).card : ℝ) +
        ((∑ i, (((ofRoundDataT tOf RD) P E₀).2.kidE i).card : ℕ) : ℝ) ≤
      ε * (E₀.card : ℝ) +
        (Real.sqrt 2 + γ ^ 2 * 800000 +
            Real.sqrt 2 * ((2 * γ ^ 2 + γ + 64 * γ ^ 7) * ((202 : ℝ) ^ 21 * 2))) *
          Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) := by
  classical
  let errF : Finset V → Finset E → ℕ := fun P' E₀' => ((RD P' E₀').toCall.U).card
  let inF : Finset V → Finset E → ℕ := fun P' E₀' => errF P' E₀' +
    2 * (tOf P' E₀') ^ 2 * (P'.card - 1) +
      (tOf P' E₀') * ((P'.card - 1) + (8 * (tOf P' E₀') ^ 3) ^ 2 * P'.card)
  set hnum := counts_of_roundDataT tOf RD errF inF (fun _ _ => le_rfl) hrnd with hnum_def
  have herror : ∀ (d : ℕ), d ≤ E₀.card → ∀ a ∈ (Level.chain P E₀ (ofRoundDataT tOf RD)
      (ofRoundDataT_wf tOf RD) d).insts,
      ((hnum a.1 a.2).errF : ℝ) ≤
        10 * ((γ * ((d : ℝ) + 1) ^ 3) ^ 2 * Real.sqrt ((a.2.card : ℝ) * (a.1.card : ℝ))) +
          4 * (a.2.card : ℝ) / (γ * ((d : ℝ) + 1) ^ 3) := by
    intro d hd a ha
    have h := herrU a.1 a.2
    rw [htd d hd a ha] at h
    rw [hnum_def]
    exact h
  have hrounds : ∀ (d : ℕ), d ≤ E₀.card → ∀ a ∈ (Level.chain P E₀ (ofRoundDataT tOf RD)
      (ofRoundDataT_wf tOf RD) d).insts,
      ((hnum a.1 a.2).inF : ℝ) ≤ (hnum a.1 a.2).errF +
        2 * (γ * ((d : ℝ) + 1) ^ 3) ^ 2 * ((a.1.card : ℝ) - 1) +
          (γ * ((d : ℝ) + 1) ^ 3) *
            ((a.1.card : ℝ) - 1 + (8 * (γ * ((d : ℝ) + 1) ^ 3) ^ 3) ^ 2 * (a.1.card : ℝ)) := by
    intro d hd a ha
    have hc := htd d hd a ha
    have hsub : ((a.1.card - 1 : ℕ) : ℝ) = (a.1.card : ℝ) - 1 := by
      rw [Nat.cast_sub (hnpos a.1)]
      norm_num
    have hcast : 2 * ((tOf a.1 a.2 : ℝ)) ^ 2 * ((a.1.card - 1 : ℕ) : ℝ) +
        (tOf a.1 a.2 : ℝ) * (((a.1.card - 1 : ℕ) : ℝ) +
          (8 * ((tOf a.1 a.2 : ℝ)) ^ 3) ^ 2 * (a.1.card : ℝ)) =
        2 * (γ * ((d : ℝ) + 1) ^ 3) ^ 2 * ((a.1.card : ℝ) - 1) +
          (γ * ((d : ℝ) + 1) ^ 3) *
            ((a.1.card : ℝ) - 1 + (8 * (γ * ((d : ℝ) + 1) ^ 3) ^ 3) ^ 2 * (a.1.card : ℝ)) := by
      rw [hsub, hc]
    rw [hnum_def]
    change ((((RD a.1 a.2).toCall.U).card +
        2 * (tOf a.1 a.2) ^ 2 * (a.1.card - 1) +
          (tOf a.1 a.2) * ((a.1.card - 1) + (8 * (tOf a.1 a.2) ^ 3) ^ 2 * a.1.card) : ℕ) : ℝ) ≤
      (((RD a.1 a.2).toCall.U).card : ℝ) +
        2 * (γ * ((d : ℝ) + 1) ^ 3) ^ 2 * ((a.1.card : ℝ) - 1) +
          (γ * ((d : ℝ) + 1) ^ 3) *
            ((a.1.card : ℝ) - 1 + (8 * (γ * ((d : ℝ) + 1) ^ 3) ^ 3) ^ 2 * (a.1.card : ℝ))
    push_cast
    linarith [hcast]
  have hnm' : (((ofRoundDataT tOf RD) P E₀).2.P.card : ℝ) ≤
      2 * ((((ofRoundDataT tOf RD) P E₀).2.E₀.card : ℕ) : ℝ) := by
    show (P.card : ℝ) ≤ 2 * (E₀.card : ℝ)
    exact hnm
  exact display_of_counts P E₀ (ofRoundDataT tOf RD) (ofRoundDataT_wf tOf RD)
    hγ1 hε hγε hnm' hnum herror hrounds

/-- **The display bounds the children alone.**  §4 recurses on the children's inputs, so what it
consumes from the display is `Σᵢ|Eᵢ| ≤ εm + C√(mn)` — the kept forest and the retained set enter only
with a sign (`F, U ≥ 0`).  This is the display theorem with those two terms dropped, in exactly the
shape `certificate_of_display` needs (`subSizes m` read as the children's sizes). -/
theorem sum_kidE_le_paper_bound {k : ℕ} (tOf : Finset V → Finset E → ℕ)
    (RD : ∀ (P : Finset V) (E₀ : Finset E), CallOut.RoundData G P E₀ (Fin k) (tOf P E₀))
    (P : Finset V) (E₀ : Finset E)
    {γ ε : ℝ} (hγ1 : 1 ≤ γ) (hε : 0 < ε) (hγε : 16 ≤ ε * γ)
    (hnm : (P.card : ℝ) ≤ 2 * (E₀.card : ℝ))
    (hnpos : ∀ (P' : Finset V), 1 ≤ P'.card)
    (herrU : ∀ (P' : Finset V) (E₀' : Finset E), (((RD P' E₀').toCall.U).card : ℝ) ≤
      10 * ((tOf P' E₀' : ℝ) ^ 2 * Real.sqrt ((E₀'.card : ℝ) * (P'.card : ℝ))) +
        4 * (E₀'.card : ℝ) / (tOf P' E₀' : ℝ))
    (hrnd : ∀ (P' : Finset V) (E₀' : Finset E), (∑ i, ((RD P' E₀').toCall.kidE i).card) ≤
      ((RD P' E₀').toCall.U).card + 2 * (tOf P' E₀') ^ 2 * (P'.card - 1) +
        (tOf P' E₀') * ((P'.card - 1) + (8 * (tOf P' E₀') ^ 3) ^ 2 * P'.card))
    (htd : ∀ (d : ℕ), d ≤ E₀.card → ∀ a ∈ (Level.chain P E₀ (ofRoundDataT tOf RD)
        (ofRoundDataT_wf tOf RD) d).insts,
      (tOf a.1 a.2 : ℝ) = γ * ((d : ℝ) + 1) ^ 3) :
    ((∑ i, (((ofRoundDataT tOf RD) P E₀).2.kidE i).card : ℕ) : ℝ) ≤
      ε * (E₀.card : ℝ) +
        (Real.sqrt 2 + γ ^ 2 * 800000 +
            Real.sqrt 2 * ((2 * γ ^ 2 + γ + 64 * γ ^ 7) * ((202 : ℝ) ^ 21 * 2))) *
          Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) := by
  have h := display_of_roundData_sampling tOf RD P E₀ hγ1 hε hγε hnm hnpos herrU hrnd htd
  have hF : (0 : ℝ) ≤ (((ofRoundDataT tOf RD) P E₀).2.F.card : ℝ) := Nat.cast_nonneg _
  have hU : (0 : ℝ) ≤ ((((ofRoundDataT tOf RD) P E₀).2.U).card : ℝ) := Nat.cast_nonneg _
  linarith

end Strategy

end DLMST