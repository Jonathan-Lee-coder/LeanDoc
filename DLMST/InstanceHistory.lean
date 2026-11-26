import DLMST.InstanceCount
import DLMST.HistoryCount

/-!
# Lemma 3.10 and Lemma 3.11 on the instance `(P, E₀)`

`HistoryCount.lean` counts histories with the *global* graph's `m = |E|`, `n = |V|`;
`InstanceCount.lemma311_on` is already instance-local (`lostOn E₀` averages `2|E₀|/t`).  §3.6 needs
the matching instance-local count of Lemma 3.10: a call's histories have spokes that are *instance*
edges and forests that are *subsets of `E₀`*, so the number of histories should be bounded by
`t²(2√(2|E₀||P|) + 4√(|E₀|(|P|−1)))`, with the instance's `m = |E₀|` and `n = |P|` in both factors.

This file proves that count and composes it with `lemma311_on`:

* `degOn` — the degree of a vertex inside `E₀`; `sum_degOn_le` — `∑_{v∈P} deg_{E₀}(v) ≤ 2|E₀|`;
  `sum_log_degOn_le` — the summed test budget `∑_{v∈P} log(deg_{E₀}(v)+1) ≤ 2√(2|E₀||P|)`.
* `SpokeOKOn` — a spoke vector with entries in `E₀` incident at the vertex (the paper's `δ_{E₀}(v) ∪
  {⊥}`); `card_spokeOKOn_le` counts them by `∏_{v∈P}(deg_{E₀}(v)+1)`.  The `∏` runs over `P`
  only because `hends` puts every edge's endpoints in `P`: at a vertex outside `P` the only legal
  spoke is the default `e₀`.
* `card_subsetsOn_le_choose`, `card_forestSeqsOn_le` — the forest factor `C(|E₀|+n−1, n−1)^{t²}`.
* `LegalOn` — consistent histories with instance-legal spokes and forests contained in `E₀`;
  `card_historiesOn_le`, `log_card_historiesOn_le` — Lemma 3.10 with `m := |E₀|`, `n := |P|`.
* `exists_schedule_lostOn_paper` — Lemma 3.11 + Lemma 3.10: one schedule on which every legal
  history has `lostOn E₀` at most `(2√2+4)t²√(|E₀||P|)/log 2 + 2|E₀|/(t log 2)` — exactly
  `DriverCall.EvidenceOn.hlost`.
* `canonicalHistory`, `legalOn_canonical` — the all-default history, so the family is nonempty.

No probability is used: `lemma311_on` is the exact average over all schedules.
-/

namespace DLMST

open Classical

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E} {t : ℕ}

/-! ## The instance's degrees -/

/-- `deg_{E₀}(v)`: the number of instance edges incident to `v`. -/
noncomputable def degOn (G : WGraph V E) (E₀ : Finset E) (v : V) : ℕ :=
  (E₀.filter (incident G v)).card

/-- **`∑_{v∈P} deg_{E₀}(v) ≤ 2|E₀|`**: handshaking inside the instance (an edge is incident to at
most its two endpoints). -/
theorem sum_degOn_le (P : Finset V) (E₀ : Finset E) :
    ∑ v ∈ P, degOn G E₀ v ≤ 2 * E₀.card := by
  classical
  have hstep : ∀ v : V, degOn G E₀ v ≤
      (E₀.filter fun e => G.src e = v).card + (E₀.filter fun e => G.dst e = v).card := by
    intro v
    unfold degOn
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro e he
    obtain ⟨heE, hinc⟩ := Finset.mem_filter.mp he
    simp only [incident] at hinc
    rcases hinc with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨heE, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨heE, h⟩)
  calc ∑ v ∈ P, degOn G E₀ v
      ≤ ∑ v ∈ P, ((E₀.filter fun e => G.src e = v).card +
          (E₀.filter fun e => G.dst e = v).card) := Finset.sum_le_sum fun v _ => hstep v
    _ ≤ ∑ v : V, ((E₀.filter fun e => G.src e = v).card +
          (E₀.filter fun e => G.dst e = v).card) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ P)
          (fun v _ _ => Nat.zero_le _)
    _ = 2 * E₀.card := sum_degree G.src G.dst E₀

/-- **`∑_{v∈P} log(deg_{E₀}(v)+1) ≤ 2√(2|E₀||P|)`**: §3.2's summed test budget
(`Selection.test_budget`) applied to the instance's degrees, with `sum_degOn_le`. -/
theorem sum_log_degOn_le (P : Finset V) (E₀ : Finset E) :
    ∑ v ∈ P, Real.log ((degOn G E₀ v : ℝ) + 1) ≤
      2 * Real.sqrt (2 * (E₀.card : ℝ) * (P.card : ℝ)) := by
  classical
  have htest := test_budget (fun v : ↥P => degOn G E₀ v.1) 1
  simp only [Nat.cast_one, one_mul, mul_one] at htest
  have hdeg : (∑ v : ↥P, (degOn G E₀ v.1 : ℝ)) ≤ 2 * (E₀.card : ℝ) := by
    have h := sum_degOn_le (G := G) P E₀
    rw [← Finset.sum_coe_sort (s := P) (f := fun v => degOn G E₀ v)] at h
    exact_mod_cast h
  have hcard : ((Fintype.card ↥P : ℕ) : ℝ) = (P.card : ℝ) := by
    rw [Fintype.card_coe]
  have hmono : Real.sqrt ((Fintype.card ↥P : ℝ) * ∑ v : ↥P, (degOn G E₀ v.1 : ℝ)) ≤
      Real.sqrt (2 * (E₀.card : ℝ) * (P.card : ℝ)) := by
    refine Real.sqrt_le_sqrt ?_
    rw [hcard]
    nlinarith [hdeg, Nat.cast_nonneg (α := ℝ) (P.card : ℕ),
      Nat.cast_nonneg (α := ℝ) (E₀.card : ℕ)]
  calc ∑ v ∈ P, Real.log ((degOn G E₀ v : ℝ) + 1)
      = ∑ v : ↥P, Real.log ((degOn G E₀ v.1 : ℝ) + 1) :=
        (Finset.sum_coe_sort (s := P) (f := fun v => Real.log ((degOn G E₀ v : ℝ) + 1))).symm
    _ ≤ 2 * Real.sqrt ((Fintype.card ↥P : ℝ) * ∑ v : ↥P, (degOn G E₀ v.1 : ℝ)) := htest
    _ ≤ 2 * Real.sqrt (2 * (E₀.card : ℝ) * (P.card : ℝ)) := by
        linarith [hmono]

/-! ## Legal spoke vectors inside the instance -/

/-- A **legal instance spoke vector** at one round: every entry is either the default `e₀` or an
instance edge incident at the vertex (the paper's `δ_{E₀}(v) ∪ {⊥}`). -/
def SpokeOKOn (G : WGraph V E) (E₀ : Finset E) (e₀ : E) (σ : V → E) : Prop :=
  ∀ v, σ v = e₀ ∨ (σ v ∈ E₀ ∧ incident G v (σ v))

/-- **`# legal instance spoke vectors ≤ ∏_{v∈P}(deg_{E₀}(v)+1)`.**  A legal vector is determined by
its restriction to `P`: outside `P` the only legal value is `e₀`, because `hends` puts both endpoints
of every instance edge in `P`. -/
lemma card_spokeOKOn_le (P : Finset V) (E₀ : Finset E) (e₀ : E)
    (hends : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) :
    Fintype.card {σ : V → E // SpokeOKOn (G := G) E₀ e₀ σ} ≤
      ∏ v ∈ P, (degOn G E₀ v + 1) := by
  classical
  have hmem : ∀ (σ : V → E), SpokeOKOn (G := G) E₀ e₀ σ → ∀ v ∈ P,
      σ v ∈ insert e₀ (E₀.filter (incident G v)) := by
    intro σ hσ v _
    rcases hσ v with h | ⟨hE, hinc⟩
    · rw [h]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hE, hinc⟩)
  have hout : ∀ (σ : V → E), SpokeOKOn (G := G) E₀ e₀ σ → ∀ v, v ∉ P → σ v = e₀ := by
    intro σ hσ v hv
    rcases hσ v with h | ⟨hE, hinc⟩
    · exact h
    · exfalso
      simp only [incident] at hinc
      rcases hinc with h | h
      · exact hv (h ▸ (hends (σ v) hE).1)
      · exact hv (h ▸ (hends (σ v) hE).2)
  let f : {σ : V → E // SpokeOKOn (G := G) E₀ e₀ σ} →
      (∀ v : ↥P, ↥(insert e₀ (E₀.filter (incident G v.1)))) :=
    fun σ v => ⟨σ.1 v.1, hmem σ.1 σ.2 v.1 v.2⟩
  have hinj : Function.Injective f := by
    intro σ₁ σ₂ h
    refine Subtype.ext (funext fun v => ?_)
    by_cases hv : v ∈ P
    · exact congrArg (fun g => (g ⟨v, hv⟩).1) h
    · rw [hout σ₁.1 σ₁.2 v hv, hout σ₂.1 σ₂.2 v hv]
  calc Fintype.card {σ : V → E // SpokeOKOn (G := G) E₀ e₀ σ}
      ≤ Fintype.card (∀ v : ↥P, ↥(insert e₀ (E₀.filter (incident G v.1)))) :=
        Fintype.card_le_of_injective f hinj
    _ = ∏ v : ↥P, (insert e₀ (E₀.filter (incident G v.1))).card := by
        rw [Fintype.card_pi]
        exact Finset.prod_congr rfl fun v _ => Fintype.card_coe _
    _ ≤ ∏ v : ↥P, (degOn G E₀ v.1 + 1) :=
        Finset.prod_le_prod fun v _ => by
          calc (insert e₀ (E₀.filter (incident G v.1))).card
              ≤ (E₀.filter (incident G v.1)).card + 1 := Finset.card_insert_le _ _
            _ = degOn G E₀ v.1 + 1 := rfl
    _ = ∏ v ∈ P, (degOn G E₀ v + 1) :=
        Finset.prod_coe_sort (s := P) (f := fun v => degOn G E₀ v + 1)

/-- **The instance spoke sequences of a call**: at most `(∏_{v∈P}(deg_{E₀}(v)+1))^{t²}`. -/
lemma card_spokeSeqsOn_le (P : Finset V) (E₀ : Finset E) (e₀ : E)
    (hends : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) :
    (Finset.univ.filter (fun σ : Fin t × Fin t → V → E =>
      ∀ p, SpokeOKOn (G := G) E₀ e₀ (σ p))).card ≤
      (∏ v ∈ P, (degOn G E₀ v + 1)) ^ (t * t) := by
  rw [card_filter_forall (P := fun σ : V → E => SpokeOKOn (G := G) E₀ e₀ σ),
    show Fintype.card (Fin t × Fin t) = t * t from by simp [Fintype.card_prod]]
  exact Nat.pow_le_pow_left (card_spokeOKOn_le P E₀ e₀ hends) _

/-! ## Forest sequences inside the instance -/

/-- **Subsets of `E₀` of size `≤ r`**: at most `C(|E₀|+r, r)` (same hockey-stick argument as
`card_finsets_le_choose`, with the ground set `E₀`). -/
lemma card_subsetsOn_le_choose (E₀ : Finset E) (r : ℕ) :
    (Finset.univ.filter (fun F : Finset E => F ⊆ E₀ ∧ F.card ≤ r)).card ≤
      Nat.choose (E₀.card + r) r := by
  classical
  have hset : (Finset.univ.filter (fun F : Finset E => F ⊆ E₀ ∧ F.card ≤ r)) =
      (Finset.range (r + 1)).biUnion (fun k => E₀.powersetCard k) := by
    ext F
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_powersetCard]
    constructor
    · rintro ⟨hsub, hcard⟩
      exact ⟨F.card, by omega, hsub, rfl⟩
    · rintro ⟨k, hk, hsub, hcard⟩
      exact ⟨hsub, by omega⟩
  rw [hset]
  have hdisj : (↑(Finset.range (r + 1)) : Set ℕ).PairwiseDisjoint
      (fun k => E₀.powersetCard k) := by
    intro k _ l _ hkl
    rw [Function.onFun, Finset.disjoint_left]
    intro F hF1 hF2
    rw [Finset.mem_powersetCard] at hF1 hF2
    exact hkl (hF1.2.symm.trans hF2.2)
  rw [Finset.card_biUnion hdisj]
  calc ∑ k ∈ Finset.range (r + 1), (E₀.powersetCard k).card
      = ∑ k ∈ Finset.range (r + 1), Nat.choose E₀.card k := by
        exact Finset.sum_congr rfl fun k _ => Finset.card_powersetCard _ _
    _ ≤ Nat.choose (E₀.card + r) r := sum_range_choose_le _ _

/-- **The instance forest sequences of a call**: at most `C(|E₀|+n−1, n−1)^{t²}`. -/
lemma card_forestSeqsOn_le (E₀ : Finset E) (n : ℕ) :
    (Finset.univ.filter (fun F : Fin t × Fin t → Finset E =>
      ∀ p, F p ⊆ E₀ ∧ (F p).card ≤ n - 1)).card ≤
      (Nat.choose (E₀.card + (n - 1)) (n - 1)) ^ (t * t) := by
  classical
  have hinj : Function.Injective
      (fun F : {F : Fin t × Fin t → Finset E // ∀ p, F p ⊆ E₀ ∧ (F p).card ≤ n - 1} =>
        fun p => (⟨F.1 p, F.2 p⟩ : {G : Finset E // G ⊆ E₀ ∧ G.card ≤ n - 1})) := by
    intro a b h
    apply Subtype.ext
    funext p
    exact congrArg (fun g => (g p).1) h
  have h1 : Fintype.card {F : Fin t × Fin t → Finset E // ∀ p, F p ⊆ E₀ ∧ (F p).card ≤ n - 1} ≤
      (Fintype.card {G : Finset E // G ⊆ E₀ ∧ G.card ≤ n - 1}) ^ (t * t) := by
    refine (Fintype.card_le_of_injective _ hinj).trans (le_of_eq ?_)
    rw [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin]
  have h2 : Fintype.card {G : Finset E // G ⊆ E₀ ∧ G.card ≤ n - 1} ≤
      Nat.choose (E₀.card + (n - 1)) (n - 1) := by
    rw [Fintype.card_subtype]
    exact card_subsetsOn_le_choose E₀ (n - 1)
  rw [← Fintype.card_subtype (fun F : Fin t × Fin t → Finset E =>
    ∀ p, F p ⊆ E₀ ∧ (F p).card ≤ n - 1)]
  exact h1.trans (Nat.pow_le_pow_left h2 (t * t))

/-! ## Counting the instance's histories -/

/-- The **legal instance histories**: consistent, with instance-legal spokes and forests contained in
`E₀` of at most `|P| − 1` edges.  Nothing here mentions the schedule, so the family is closed under
"the history induced by any schedule". -/
def LegalOn (P : Finset V) (E₀ : Finset E) (e₀ : E) (H : History V E t) : Prop :=
  H.Consistent (G := G) ∧ (∀ b i, SpokeOKOn (G := G) E₀ e₀ (H.spoke b i)) ∧
    ∀ b i, H.forest b i ⊆ E₀ ∧ (H.forest b i).card ≤ P.card - 1

/-- A Fintype instance for histories (the structure is a subtype of a triple). -/
def historyEquiv {V E : Type*} {t : ℕ} :
    History V E t ≃ ((Fin t → Fin t → V → E) × (Fin t → Fin t → Finset E) ×
      (E → Fin t → Fin t → Pref)) where
  toFun H := (H.spoke, H.forest, H.pref)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv H := by cases H; rfl
  right_inv p := by rcases p with ⟨s, f, pr⟩; rfl

instance {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] {t : ℕ} :
    Fintype (History V E t) :=
  Fintype.ofEquiv _ (historyEquiv (V := V) (E := E) (t := t)).symm

/-- **Lemma 3.10 on the instance, the count.**  A consistent history is determined by its spoke and
forest sequences, so a family of legal instance histories injects into "spoke sequences × forest
sequences"; the two factors are `(∏_{v∈P}(deg_{E₀}(v)+1))^{t²}` and
`C(|E₀|+|P|−1, |P|−1)^{t²}`. -/
theorem card_historiesOn_le (P : Finset V) (E₀ : Finset E) (e₀ : E)
    (hends : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (Hs : Finset (History V E t))
    (hleg : ∀ H ∈ Hs, LegalOn (G := G) P E₀ e₀ H) :
    Hs.card ≤ (∏ v ∈ P, (degOn G E₀ v + 1)) ^ (t * t) *
      (Nat.choose (E₀.card + (P.card - 1)) (P.card - 1)) ^ (t * t) := by
  classical
  set SP := Finset.univ.filter (fun σ : Fin t × Fin t → V → E =>
    ∀ p, SpokeOKOn (G := G) E₀ e₀ (σ p)) with hSP
  set FO := Finset.univ.filter (fun F : Fin t × Fin t → Finset E =>
    ∀ p, F p ⊆ E₀ ∧ (F p).card ≤ P.card - 1) with hFO
  let g : History V E t → (Fin t × Fin t → V → E) × (Fin t × Fin t → Finset E) :=
    fun H => (fun p => H.spoke p.1 p.2, fun p => H.forest p.1 p.2)
  have hmaps : Set.MapsTo g ↑Hs ↑(SP.product FO) := by
    intro H hH
    obtain ⟨hcons, hsp, hfo⟩ := hleg H hH
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · rw [hSP, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, fun p => hsp p.1 p.2⟩
    · rw [hFO, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, fun p => hfo p.1 p.2⟩
  have hinj : Set.InjOn g ↑Hs := by
    intro H₁ h₁ H₂ h₂ heq
    obtain ⟨s1, f1, p1⟩ := H₁
    obtain ⟨s2, f2, p2⟩ := H₂
    have hsp : s1 = s2 := by
      have h := congrArg Prod.fst heq
      funext b i
      exact congrFun h (b, i)
    have hfo : f1 = f2 := by
      have h := congrArg Prod.snd heq
      funext b i
      exact congrFun h (b, i)
    have hpref : p1 = p2 := by
      funext e b i
      have h1 := (hleg ⟨s1, f1, p1⟩ h₁).1 e b i
      have h2 := (hleg ⟨s2, f2, p2⟩ h₂).1 e b i
      rw [hsp] at h1
      rw [hfo] at h1
      exact h1.trans h2.symm
    rw [hsp, hfo, hpref]
  have h1 := Finset.card_le_card_of_injOn g hmaps hinj
  have h2 : (SP.product FO).card = SP.card * FO.card := Finset.card_product SP FO
  rw [h2] at h1
  exact h1.trans (Nat.mul_le_mul (card_spokeSeqsOn_le P E₀ e₀ hends)
    (card_forestSeqsOn_le E₀ P.card))

/-- **Lemma 3.10 on the instance, in logarithmic form**:
`log |Hs| ≤ t²(2√(2|E₀||P|) + 4√(|E₀|(|P|−1)))`. -/
theorem log_card_historiesOn_le (P : Finset V) (E₀ : Finset E) (e₀ : E)
    (hends : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (Hs : Finset (History V E t))
    (hleg : ∀ H ∈ Hs, LegalOn (G := G) P E₀ e₀ H) (hpos : 0 < Hs.card) :
    Real.log (Hs.card : ℝ) ≤ (t : ℝ) ^ 2 *
      (2 * Real.sqrt (2 * (E₀.card : ℝ) * (P.card : ℝ)) +
        4 * Real.sqrt ((E₀.card : ℝ) * (((P.card - 1 : ℕ)) : ℝ))) := by
  classical
  have hpt : (0 : ℝ) < ((∏ v ∈ P, (degOn G E₀ v + 1) : ℕ) : ℝ) := by
    rw [Nat.cast_prod]
    exact Finset.prod_pos fun v _ => by positivity
  have hct : (0 : ℝ) <
      (Nat.choose (E₀.card + (P.card - 1)) (P.card - 1) : ℝ) := by
    have := Nat.choose_pos (show P.card - 1 ≤ E₀.card + (P.card - 1) from Nat.le_add_left _ _)
    exact_mod_cast this
  have hlogP : Real.log (((∏ v ∈ P, (degOn G E₀ v + 1) : ℕ) : ℝ)) =
      ∑ v ∈ P, Real.log ((degOn G E₀ v : ℝ) + 1) := by
    rw [Nat.cast_prod, Real.log_prod (fun v _ => by positivity)]
    exact Finset.sum_congr rfl fun v _ => by push_cast; ring
  have hcard := card_historiesOn_le P E₀ e₀ hends Hs hleg
  have hcardR : (Hs.card : ℝ) ≤
      ((∏ v ∈ P, (degOn G E₀ v + 1) : ℕ) : ℝ) ^ (t * t) *
        ((Nat.choose (E₀.card + (P.card - 1)) (P.card - 1) : ℕ) : ℝ) ^ (t * t) := by
    exact_mod_cast hcard
  have hlog := Real.log_le_log (by exact_mod_cast hpos) hcardR
  have hp1 : (0 : ℝ) < ((∏ v ∈ P, (degOn G E₀ v + 1) : ℕ) : ℝ) ^ (t * t) := pow_pos hpt _
  have hc1 : (0 : ℝ) < ((Nat.choose (E₀.card + (P.card - 1)) (P.card - 1) : ℕ) : ℝ) ^ (t * t) :=
    pow_pos hct _
  rw [Real.log_mul (ne_of_gt hp1) (ne_of_gt hc1), Real.log_pow, Real.log_pow] at hlog
  have hPle : Real.log (((∏ v ∈ P, (degOn G E₀ v + 1) : ℕ) : ℝ)) ≤
      2 * Real.sqrt (2 * (E₀.card : ℝ) * (P.card : ℝ)) := by
    rw [hlogP]
    exact sum_log_degOn_le P E₀
  have hCle : Real.log ((Nat.choose (E₀.card + (P.card - 1)) (P.card - 1) : ℕ) : ℝ) ≤
      4 * Real.sqrt ((E₀.card : ℝ) * (((P.card - 1 : ℕ)) : ℝ)) :=
    log_choose_le _ _
  have ht2 : ((t * t : ℕ) : ℝ) = (t : ℝ) ^ 2 := by push_cast; ring
  calc Real.log (Hs.card : ℝ)
      ≤ ((t * t : ℕ) : ℝ) * Real.log (((∏ v ∈ P, (degOn G E₀ v + 1) : ℕ) : ℝ)) +
          ((t * t : ℕ) : ℝ) * Real.log ((Nat.choose (E₀.card + (P.card - 1))
            (P.card - 1) : ℕ) : ℝ) := hlog
    _ ≤ ((t * t : ℕ) : ℝ) * (2 * Real.sqrt (2 * (E₀.card : ℝ) * (P.card : ℝ))) +
          ((t * t : ℕ) : ℝ) *
            (4 * Real.sqrt ((E₀.card : ℝ) * (((P.card - 1 : ℕ)) : ℝ))) :=
        add_le_add (mul_le_mul_of_nonneg_left hPle (by positivity))
          (mul_le_mul_of_nonneg_left hCle (by positivity))
    _ = (t : ℝ) ^ 2 * (2 * Real.sqrt (2 * (E₀.card : ℝ) * (P.card : ℝ)) +
          4 * Real.sqrt ((E₀.card : ℝ) * (((P.card - 1 : ℕ)) : ℝ))) := by
        rw [ht2]; ring

/-! ## Lemma 3.11 on the instance -/

/-- **Lemma 3.11 + Lemma 3.10 on the instance.**  For a nonempty family of legal instance histories
there is one schedule under which every history has at most
`(2√2+4)t²√(|E₀||P|) + 2|E₀|/t` edges of `E₀` in bad rounds, up to the `log 2` of Lemma 3.11. -/
theorem exists_schedule_lostOn_paper (P : Finset V) (E₀ : Finset E) (e₀ : E)
    (hends : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (ht : 2 ≤ t)
    (Hs : Finset (History V E t)) (hleg : ∀ H ∈ Hs, LegalOn (G := G) P E₀ e₀ H)
    (hpos : 0 < Hs.card) :
    ∃ ρ : Sched E t, ∀ H ∈ Hs,
      (H.lostOn E₀ ρ : ℝ) * Real.log 2 ≤
        (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 *
            Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) + 2 * (E₀.card : ℝ) / (t : ℝ) := by
  classical
  obtain ⟨ρ, hρ⟩ := History.lemma311_on ht Hs E₀
  refine ⟨ρ, fun H hH => ?_⟩
  have hlog := log_card_historiesOn_le P E₀ e₀ hends Hs hleg hpos
  have hm : (0 : ℝ) ≤ (E₀.card : ℝ) := Nat.cast_nonneg _
  have hn1 : (((P.card - 1 : ℕ)) : ℝ) ≤ (P.card : ℝ) := by
    exact_mod_cast Nat.sub_le P.card 1
  have hsq : Real.sqrt ((E₀.card : ℝ) * (((P.card - 1 : ℕ)) : ℝ)) ≤
      Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hn1 hm)
  have hsq2 : Real.sqrt (2 * (E₀.card : ℝ) * (P.card : ℝ)) =
      Real.sqrt 2 * Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) := by
    rw [show 2 * (E₀.card : ℝ) * (P.card : ℝ) =
        2 * ((E₀.card : ℝ) * (P.card : ℝ)) by ring]
    exact Real.sqrt_mul (by norm_num) _
  have hkey : 2 * Real.sqrt (2 * (E₀.card : ℝ) * (P.card : ℝ)) +
      4 * Real.sqrt ((E₀.card : ℝ) * (((P.card - 1 : ℕ)) : ℝ)) ≤
      (2 * Real.sqrt 2 + 4) * Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) := by
    rw [hsq2]
    nlinarith [hsq]
  linarith [hρ H hH, mul_le_mul_of_nonneg_left hkey (sq_nonneg (t : ℝ))]

/-- The **all-default history**: every spoke is `e₀`, every forest empty. -/
noncomputable def canonicalHistory (e₀ : E) : History V E t :=
  History.ofData (G := G) (fun _ _ _ => e₀) (fun _ _ => ∅)

/-- The all-default history is legal on every instance. -/
theorem legalOn_canonical (P : Finset V) (E₀ : Finset E) (e₀ : E) :
    LegalOn (G := G) P E₀ e₀ (canonicalHistory (G := G) (V := V) (E := E) (t := t) e₀) := by
  refine ⟨History.ofData_consistent _ _, ?_, ?_⟩
  · intro b i v
    exact Or.inl rfl
  · intro b i
    show (∅ : Finset E) ⊆ E₀ ∧ (∅ : Finset E).card ≤ P.card - 1
    exact ⟨Finset.empty_subset _, by simp⟩

/-- **A good schedule exists for the whole legal instance family** (Lemma 3.11 + 3.10 with the
family taken to be all legal instance histories). -/
theorem exists_good_scheduleOn (P : Finset V) (E₀ : Finset E) (e₀ : E)
    (hends : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (ht : 2 ≤ t) :
    ∃ ρ : Sched E t, ∀ H : History V E t, LegalOn (G := G) P E₀ e₀ H →
      (H.lostOn E₀ ρ : ℝ) * Real.log 2 ≤
        (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 *
            Real.sqrt ((E₀.card : ℝ) * (P.card : ℝ)) + 2 * (E₀.card : ℝ) / (t : ℝ) := by
  classical
  set Hs := Finset.univ.filter (fun H : History V E t => LegalOn (G := G) P E₀ e₀ H) with hHs
  have hleg : ∀ H ∈ Hs, LegalOn (G := G) P E₀ e₀ H := by
    intro H hH
    rw [hHs, Finset.mem_filter] at hH
    exact hH.2
  have hpos : 0 < Hs.card := by
    rw [hHs]
    exact Finset.card_pos.mpr ⟨canonicalHistory (G := G) (t := t) e₀, by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, legalOn_canonical P E₀ e₀⟩⟩
  obtain ⟨ρ, hρ⟩ := exists_schedule_lostOn_paper P E₀ e₀ hends ht Hs hleg hpos
  exact ⟨ρ, fun H hH => hρ H (by rw [hHs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hH⟩)⟩

end DLMST