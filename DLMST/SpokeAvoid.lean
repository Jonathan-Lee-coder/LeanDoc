import DLMST.HistoryOfRounds
import DLMST.Queries

/-!
# The spokes avoid the kept forest: where `hFsp` comes from

`GeometricHistory.lean`'s §3.5 theorems take `hFsp` — no forest edge is a spoke — as a side
condition.  This file discharges it from the *selection rule* rather than from the sampling: if the
spoke at every round and vertex is chosen only among edges **outside** the call's kept forest
(`adm := fun e => e ∉ F`), no spoke can be a forest edge (`hFsp_of_spokes_notMem`), and the driver's
actual table `spokeTable B (fun e => e ∉ D.F) k` is of exactly this kind (`spokeTable_notMem`).  The
selections of `BatchSel.selAt` only ever return representatives, and a representative is admissible.

The one input left is `hadm`: each round's batch has, at every vertex, an incident edge outside the
kept forest.  That is a property of the batches — checkable by enumeration before any comparison —
not of the queries, which is the honest place for it: a vertex all of whose incident batch edges are
already in `F` has no legal *non-forest* spoke to offer, and the paper's run does not meet that case
because spokes are read off the contracted graph, whose vertices carry edges outside `F`.

With `hFsp` in hand the geometry layer closes for the driver's own history
`historyOfTable D B (fun e => e ∉ D.F) k`:

* `card_U_le_display_form_of_table` — §3.5's display form with Claim 3.12's sample existential;
* `card_U_le_number_bound_of_table` — the same bound with the sample **computed** (`sampleSets`),
  the truth membership derived (`truth_of_history_slot`), the estimate read off the enumerated family
  (`est_of_choice`) and `hFsp` derived.  What is left is `hc` ("select any vector of `A` consistent
  with the queried answers"), the per-edge premise (Lemma 3.7 read on this history), Lemma 3.11's
  `lost` bound, and the numeric parameters.
-/

namespace DLMST

open Classical

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

/-! ## Selections only return admissible edges -/

/-- A selected edge is admissible: `selAt` cuts a list of representatives, and a representative
carries `adm`. -/
theorem selAt_adm {B : Finset E} {adm : E → Prop} {k : ℕ} {v : V} {e : E}
    (he : e ∈ selAt G B adm k v) : adm e := by
  have hfl : e ∈ sortReps G B adm v := List.mem_of_mem_take (mem_selAt.mp he)
  exact (mem_repsAt.mp (mem_sortReps.mp hfl)).2.2.1

/-- With the admissibility predicate "not in `F`", a selection never picks an edge of `F`. -/
theorem selAt_notMem {B F : Finset E} {k : ℕ} {v : V} {e : E}
    (he : e ∈ selAt G B (fun x => x ∉ F) k v) : e ∉ F :=
  selAt_adm (adm := fun x => x ∉ F) he

/-- **The spoke table avoids the kept forest.**  Every entry of `spokeTable` is the minimum of a
selection, hence a representative, hence admissible — and admissible here means outside `F`. -/
theorem spokeTable_notMem {t : ℕ} (B : Fin t → Fin t → Finset E) (F : Finset E) (k : ℕ)
    [Nonempty E] (hk : 1 ≤ k) (hadm : ∀ (i j : Fin t) (v : V), ∃ e ∈ Bv G v (B i j), e ∉ F)
    (i j : Fin t) (v : V) :
    spokeTable (G := G) B (fun x => x ∉ F) k i j v ∉ F :=
  selAt_adm (adm := fun x => x ∉ F)
    (spokeTable_mem (G := G) B (fun x => x ∉ F) k i j v
      (selAt_nonempty_of_adm hk (hadm i j v)))

/-! ## The table history's accessors -/

section HistoryOfTable

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ} {P : Finset V} {E₀ : Finset E}

@[simp] theorem historyOfTable_spoke (D : CallOut.RoundData G P E₀ ι t)
    (B : Fin t → Fin t → Finset E) (adm : E → Prop) (k : ℕ) [Nonempty E] :
    (historyOfTable D B adm k).spoke = spokeTable (G := G) B adm k := rfl

@[simp] theorem historyOfTable_forest (D : CallOut.RoundData G P E₀ ι t)
    (B : Fin t → Fin t → Finset E) (adm : E → Prop) (k : ℕ) [Nonempty E] (b i : Fin t) :
    (historyOfTable D B adm k).forest b i = forestUpTo D (b, i) := rfl

@[simp] theorem historyOfTable_pref (D : CallOut.RoundData G P E₀ ι t)
    (B : Fin t → Fin t → Finset E) (adm : E → Prop) (k : ℕ) [Nonempty E] (e : E) (b i : Fin t) :
    (historyOfTable D B adm k).pref e b i =
      actOf G (spokeTable (G := G) B adm k b i) (forestUpTo D (b, i)) e := rfl

/-! ## `hFsp` from the spoke rule -/

/-- **No forest edge is a spoke, from two containments.**  If every round's forest lies inside `F`
and every spoke at every round and vertex lies outside `F`, then no edge of a forest is a spoke. -/
theorem hFsp_of_spokes_notMem {t : ℕ} (H : History V E t) (F : Finset E)
    (hforest : ∀ b i, H.forest b i ⊆ F)
    (hspoke : ∀ (b i : Fin t) (v : V), H.spoke b i v ∉ F) :
    ∀ (b i : Fin t) (g : E), g ∈ H.forest b i → ¬ IsSpoke (H.spoke b i) g := by
  intro b i g hg ⟨u, hu⟩
  exact hspoke b i u (by rw [hu]; exact hforest b i hg)

/-- **`hFsp` for the driver's table.**  The round forests are the prefixes `forestUpTo D (b, i)`
(inside `D.F` by construction), and the spokes are read off the batches with "not in `D.F`"
admissibility (`spokeTable_notMem`). -/
theorem hFsp_historyOfTable (D : CallOut.RoundData G P E₀ ι t)
    (B : Fin t → Fin t → Finset E) (k : ℕ) [Nonempty E] (hk : 1 ≤ k)
    (hadm : ∀ (i j : Fin t) (v : V), ∃ e ∈ Bv G v (B i j), e ∉ D.F) :
    ∀ (b i : Fin t) (g : E),
      g ∈ (historyOfTable D B (fun x => x ∉ D.F) k).forest b i →
        ¬ IsSpoke ((historyOfTable D B (fun x => x ∉ D.F) k).spoke b i) g :=
  hFsp_of_spokes_notMem (historyOfTable D B (fun x => x ∉ D.F) k) D.F
    (fun b i => forestUpTo_sub D (b, i))
    (fun b i v => spokeTable_notMem B D.F k hk hadm b i v)

/-! ## §3.5's counts for the table-driven history -/

/-- **§3.5's display form with `hFsp` discharged.**  `card_U_le_display_form_of_roundData` with the
spokes taken from `spokeTable` and the side condition proved
(`hFsp_historyOfTable`).  Claim 3.12's sample is the existential `S`; the bound holds once the
algorithm's chosen candidate answers the queries on `S`. -/
theorem card_U_le_display_form_of_table (D : CallOut.RoundData G P E₀ ι t)
    (B : Fin t → Fin t → Finset E) (k : ℕ) [Nonempty E] (hk : 1 ≤ k)
    (hadm : ∀ (i j : Fin t) (v : V), ∃ e ∈ Bv G v (B i j), e ∉ D.F)
    (slot : E → Fin t × Fin t)
    (eN : ∀ (b i : Fin t), Ground G (spokeTable (G := G) B (fun x => x ∉ D.F) k b i)
      (forestUpTo D (b, i)) ≃
        Fin (Fintype.card (Ground G (spokeTable (G := G) B (fun x => x ∉ D.F) k b i)
          (forestUpTo D (b, i)))))
    (c : ∀ r : Fin t × Fin t, {e : E // slot e = r} → Pref)
    (hc : ∀ r, c r ∈ geomFamily (G := G)
      (historyOfTable D B (fun x => x ∉ D.F) k) slot (fun b i => eN b i) r)
    {m n : ℝ} (ht : 2 ≤ t)
    (h : ∀ e ∈ E₀, ¬ supported G D.toCall.F e →
      (historyOfTable D B (fun x => x ∉ D.F) k).errOf (fun e => c (slot e) ⟨e, rfl⟩) e (slot e))
    (hlost : ((historyOfTable D B (fun x => x ∉ D.F) k).lost slot : ℝ) * Real.log 2 ≤
      (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 * Real.sqrt (m * n) + 2 * m / (t : ℝ))
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hmE : (Fintype.card E : ℝ) ≤ m) :
    ∃ S : ∀ r : Fin t × Fin t, Finset {e : E // slot e = r},
      (∀ r, (S r).card ≤ 2 * t *
        (Nat.ceil (Real.log
          ((geomFamily (G := G) (historyOfTable D B (fun x => x ∉ D.F) k) slot
            (fun b i => eN b i) r).card : ℝ)) + 1)) ∧
      ((∀ r (x : {e : E // slot e = r}), x ∈ S r →
          c (slot x.1) ⟨x.1, rfl⟩ =
            (historyOfTable D B (fun x => x ∉ D.F) k).pref x.1 r.1 r.2) →
        ((D.toCall.U).card : ℝ) ≤ 10 * (t : ℝ) ^ 2 * Real.sqrt (m * n) + 4 * m / (t : ℝ)) :=
  card_U_le_display_form_of_roundData D (spokeTable (G := G) B (fun x => x ∉ D.F) k) slot eN c hc
    (hFsp_historyOfTable D B k hk hadm) ht h hlost hm hn hmE

/-- **§3.5's bound for the table-driven history, with the sample computed.**  Everything the
`geomFamily` layer supplies is derived here: the truth is in `A r` (`truth_of_history_slot`), the
estimate read off one chosen candidate per round is in `A r` (`est_of_choice`), and `hFsp` comes
from the spoke rule (`hFsp_historyOfTable`).  The sample is Claim 3.12's `sampleSets`, fixed before
any query.  The hypotheses left are the algorithm's consistency `hc`, Lemma 3.7's per-edge premise,
Lemma 3.11's `lost` bound, the batches' non-forest supply `hadm`, and the numbers. -/
theorem card_U_le_number_bound_of_table (D : CallOut.RoundData G P E₀ ι t)
    (B : Fin t → Fin t → Finset E) (k : ℕ) [Nonempty E] (hk : 1 ≤ k)
    (hadm : ∀ (i j : Fin t) (v : V), ∃ e ∈ Bv G v (B i j), e ∉ D.F)
    (slot : E → Fin t × Fin t)
    (eN : ∀ (b i : Fin t), Ground G (spokeTable (G := G) B (fun x => x ∉ D.F) k b i)
      (forestUpTo D (b, i)) ≃
        Fin (Fintype.card (Ground G (spokeTable (G := G) B (fun x => x ∉ D.F) k b i)
          (forestUpTo D (b, i)))))
    (c : ∀ r : Fin t × Fin t, {e : E // slot e = r} → Pref)
    (hc : ∀ r, c r ∈ geomFamily (G := G)
      (historyOfTable D B (fun x => x ∉ D.F) k) slot (fun b i => eN b i) r)
    {m n : ℝ} (ht : 2 ≤ t) (hm : 0 ≤ m) (hn : 0 ≤ n) (hmE : (Fintype.card E : ℝ) ≤ m)
    (h : ∀ e ∈ E₀, ¬ supported G D.F e →
      (historyOfTable D B (fun x => x ∉ D.F) k).errOf (fun e => c (slot e) ⟨e, rfl⟩) e (slot e))
    (hlost : ((historyOfTable D B (fun x => x ∉ D.F) k).lost slot : ℝ) * Real.log 2 ≤
      (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 * Real.sqrt (m * n) + 2 * m / (t : ℝ))
    (hagree : ∀ (r : Fin t × Fin t) (x : {e : E // slot e = r}),
      x ∈ sampleSets ht slot
        (geomFamily (G := G) (historyOfTable D B (fun x => x ∉ D.F) k) slot
          (fun b i => eN b i)) r →
      c (slot x.1) ⟨x.1, rfl⟩ =
        (historyOfTable D B (fun x => x ∉ D.F) k).pref x.1 r.1 r.2) :
    ((D.toCall.U).card : ℝ) ≤ 10 * (t : ℝ) ^ 2 * Real.sqrt (m * n) + 4 * m / (t : ℝ) := by
  set H := historyOfTable D B (fun x => x ∉ D.F) k with hH
  set A := geomFamily (G := G) H slot (fun b i => eN b i) with hA
  have htr : ∀ r : Fin t × Fin t,
      (fun x : {e : E // slot e = r} => H.pref x.1 (slot x.1).1 (slot x.1).2) ∈ A r :=
    truth_of_history_slot (G := G) H
      (historyOfRoundData_consistent D (spokeTable (G := G) B (fun x => x ∉ D.F) k))
      (isForest_historyOfRoundData D (spokeTable (G := G) B (fun x => x ∉ D.F) k))
      (hFsp_historyOfTable D B k hk hadm) slot (fun b i => eN b i)
  have hest : ∀ r : Fin t × Fin t,
      (fun x : {e : E // slot e = r} => (fun e => c (slot e) ⟨e, rfl⟩) x.1) ∈ A r :=
    est_of_choice (G := G) H slot (fun b i => eN b i) c hc
  have hagree' : ∀ (r : Fin t × Fin t) (x : {e : E // slot e = r}),
      x ∈ sampleSets ht slot A r →
        (fun e => c (slot e) ⟨e, rfl⟩) x.1 = H.pref x.1 (slot x.1).1 (slot x.1).2 := by
    intro r x hx
    obtain ⟨e', he'⟩ := x
    cases he'
    exact hagree (slot e') ⟨e', rfl⟩ hx
  have hmain := CallOut.RoundData.card_U_le_number_bound_of_queries (D := D) H
    (fun e => c (slot e) ⟨e, rfl⟩) slot ht hm hn hmE A htr hest hagree' h hlost
  rw [congrArg Finset.card (CallOut.RoundData.toCall_U_eq D)]
  exact hmain

end HistoryOfTable

end DLMST