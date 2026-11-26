import DLMST.Contract
import DLMST.InstanceBoruvka
import DLMST.InputCount
import DLMST.InstanceSafety

/-!
# The contracted child is smaller

`Contract` proves that the representative set has one vertex per instance component
(`repSet_card`) and that the component count is a contraction invariant.  `InstanceBoruvka`
proves that one phase halves the component count (`compCountOn_halves_phaseIn`) and that `k`
phases leave at most `|P| / 2^k` components.  Together these bound the vertex count of the child
instance the recursion passes down — the measure that makes the recursion terminate.
-/

open Classical

namespace DLMST

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

/-- One phase halves the contracted child's vertex count. -/
theorem repSet_card_halves_phaseIn {P : Finset V} {F B : Finset E}
    (hFf : IsForest G F) (hPF : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P)
    (hPB : ∀ e ∈ B, G.src e ∈ P ∧ G.dst e ∈ P)
    (hact : ∀ v ∈ P, ∃ e ∈ B, leaves G F v e) :
    2 * (repSet G P (F ∪ phaseIn G B F)).card ≤ (repSet G P F).card := by
  rw [repSet_card, repSet_card]
  exact compCountOn_halves_phaseIn hFf hPF hPB hact

/-- After `k` phases the contracted child has at most `|P| / 2^k` vertices. -/
theorem repSet_card_le (K : ℕ) {P : Finset V} (B : Finset E) (F : ℕ → Finset E) (k : ℕ)
    (hF0 : F 0 = ∅) (hstep : ∀ i, F (i + 1) = F i ∪ phaseIn G B (F i))
    (hPB : ∀ e ∈ B, G.src e ∈ P ∧ G.dst e ∈ P)
    (hact : ∀ i, i < K → ∀ v ∈ P, ∃ e ∈ B, leaves G (F i) v e) (hk : k ≤ K) :
    ((repSet G P (F k)).card : ℝ) ≤ (P.card : ℝ) / (2 : ℝ) ^ k := by
  rw [repSet_card]
  exact compCountOn_le_real_phaseIn K B P F k hF0 hstep hPB hact hk

/-- The same bound with the paper's instance size `|P| ≤ 2|E₀|` substituted for `|P|`. -/
theorem repSet_card_le_of_card_le (K : ℕ) {P : Finset V} (B : Finset E) (F : ℕ → Finset E)
    (k : ℕ) {E₀ : Finset E} (hF0 : F 0 = ∅)
    (hstep : ∀ i, F (i + 1) = F i ∪ phaseIn G B (F i))
    (hPB : ∀ e ∈ B, G.src e ∈ P ∧ G.dst e ∈ P)
    (hact : ∀ i, i < K → ∀ v ∈ P, ∃ e ∈ B, leaves G (F i) v e) (hk : k ≤ K)
    (h0 : P.card ≤ 2 * E₀.card) :
    ((repSet G P (F k)).card : ℝ) ≤ 2 * (E₀.card : ℝ) / (2 : ℝ) ^ k := by
  rw [repSet_card]
  exact compCountOn_le_real_phaseIn_of_card_le K B P F k hF0 hstep hPB hact hk h0

/-- **The portal budget, on the contracted child.**  Two phases leave at most `|P| / 4`
representatives, which is the shape `CallOut.hshrink` asks of the children (`4·|kidV| ≤ |P|`). -/
theorem four_mul_repSet_card_le (K : ℕ) (hK : 2 ≤ K) {P : Finset V} (B : Finset E)
    (F : ℕ → Finset E) (hF0 : F 0 = ∅) (hstep : ∀ i, F (i + 1) = F i ∪ phaseIn G B (F i))
    (hPB : ∀ e ∈ B, G.src e ∈ P ∧ G.dst e ∈ P)
    (hact : ∀ i, i < K → ∀ v ∈ P, ∃ e ∈ B, leaves G (F i) v e) :
    4 * (repSet G P (F 2)).card ≤ P.card := by
  have h := repSet_card_le K B F 2 hF0 hstep hPB hact hK
  rw [show ((2 : ℝ) ^ 2) = 4 by norm_num] at h
  have h4 : (4 * ((repSet G P (F 2)).card : ℝ)) ≤ (P.card : ℝ) := by
    have := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 4 by norm_num)
    linarith
  exact_mod_cast h4

/-- **The child's returned forest is bounded by the child instance's size**: a forest on the
contracted edges has at most `|repSet| - 1` edges. -/
theorem child_forest_card_le {P : Finset V} {F : Finset E} {E₀ : Finset E}
    (hP : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    {B' : Finset {e // e ∈ crossE G F E₀}}
    (hB' : IsForest (cGraph G P F E₀) B') (hne : 0 < (repSet G P F).card) :
    B'.card ≤ (repSet G P F).card - 1 := by
  refine card_le_card_sub_one_of_isForest_of_ends (G := cGraph G P F E₀) (P := repSet G P F)
    hB' ?_ hne
  intro e _
  exact ⟨repOf_mem_repSet P F (hP e.1 (crossE_subset (G := G) F E₀ e.2)).1,
    repOf_mem_repSet P F (hP e.1 (crossE_subset (G := G) F E₀ e.2)).2⟩

/-- **The child's forest fits the portal budget**: after two phases, `4·|B| ≤ |P|` — the
`hshrink`/`hFcard` combination for the child instance. -/
theorem four_mul_child_forest_card_le (K : ℕ) (hK : 2 ≤ K) {P : Finset V} (B : Finset E)
    (F : ℕ → Finset E) {E₀ : Finset E} (hF0 : F 0 = ∅)
    (hstep : ∀ i, F (i + 1) = F i ∪ phaseIn G B (F i))
    (hPB : ∀ e ∈ B, G.src e ∈ P ∧ G.dst e ∈ P)
    (hact : ∀ i, i < K → ∀ v ∈ P, ∃ e ∈ B, leaves G (F i) v e)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    {B' : Finset {e // e ∈ crossE G (F 2) E₀}}
    (hB' : IsForest (cGraph G P (F 2) E₀) B') (hPne : 0 < P.card) :
    4 * B'.card ≤ P.card := by
  have hne : 0 < (repSet G P (F 2)).card := by
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hPne
    exact Finset.card_pos.mpr ⟨repOf G P (F 2) v, repOf_mem_repSet P (F 2) hv⟩
  have h1 : B'.card ≤ (repSet G P (F 2)).card :=
    (child_forest_card_le hPE hB' hne).trans (Nat.sub_le _ _)
  calc 4 * B'.card ≤ 4 * (repSet G P (F 2)).card := Nat.mul_le_mul_left 4 h1
    _ ≤ P.card := four_mul_repSet_card_le K hK B F hF0 hstep hPB hact

/-- **A §4 step is sound and small.**  If the level's forest `F₂` is the output of two Borůvka
phases on the instance `(P, E₀)` and the child returns a minimum spanning forest `B'` of the
contracted instance, then `F₂ ∪ B'` is a minimum spanning forest of `G[E₀]` — and the child fits
both portal budgets: `4·|repSet| ≤ |P|` contracted vertices and `4·|B'| ≤ |P|` returned edges. -/
theorem contract_step_sound_and_small (K : ℕ) (hK : 2 ≤ K) {P : Finset V} (B : Finset E)
    (F : ℕ → Finset E) {E₀ : Finset E} (hF0 : F 0 = ∅)
    (hstep : ∀ i, F (i + 1) = F i ∪ phaseIn G B (F i))
    (hPB : ∀ e ∈ B, G.src e ∈ P ∧ G.dst e ∈ P)
    (hact : ∀ i, i < K → ∀ v ∈ P, ∃ e ∈ B, leaves G (F i) v e)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hFf : IsForest G (F 2))
    {M : Finset E} (hM : IsMSFOf G E₀ M) (hFM : F 2 ⊆ M)
    {B' : Finset {e // e ∈ crossE G (F 2) E₀}}
    (hB' : IsMSFOf (cGraph G P (F 2) E₀)
      (Finset.univ : Finset {e // e ∈ crossE G (F 2) E₀}) B')
    (hPne : 0 < P.card) :
    IsMSFOf G E₀ (F 2 ∪ B'.image Subtype.val) ∧
      4 * (repSet G P (F 2)).card ≤ P.card ∧ 4 * B'.card ≤ P.card := by
  refine ⟨isMSFOf_union_cGraph_child (G := G) (P := P) (E₀ := E₀) hPE hFf hM hFM hB', ?_, ?_⟩
  · exact four_mul_repSet_card_le K hK B F hF0 hstep hPB hact
  · exact four_mul_child_forest_card_le K hK B F hF0 hstep hPB hact hPE hB'.1.1 hPne

/-- **§4's step needs no MSF hypothesis.**  `contract_step_sound_and_small` with the MSF `M`
supplied by `phaseChain_safe`: two phases of the instance's own Borůvka rule plus the child's
MSF already imply that the splice is an MSF of the instance and that both portal budgets hold.
The only remaining data are the phases themselves, the instance shape `hPE` and the activation
hypothesis `hact`. -/
theorem contract_step_sound_and_small' (K : ℕ) (hK : 2 ≤ K) {P : Finset V}
    (F : ℕ → Finset E) {E₀ : Finset E} (hF0 : F 0 = ∅)
    (hstep : ∀ i, F (i + 1) = F i ∪ phaseIn G E₀ (F i))
    (hact : ∀ i, i < K → ∀ v ∈ P, ∃ e ∈ E₀, leaves G (F i) v e)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hFf : IsForest G (F 2))
    {B' : Finset {e // e ∈ crossE G (F 2) E₀}}
    (hB' : IsMSFOf (cGraph G P (F 2) E₀)
      (Finset.univ : Finset {e // e ∈ crossE G (F 2) E₀}) B')
    (hPne : 0 < P.card) :
    IsMSFOf G E₀ (F 2 ∪ B'.image Subtype.val) ∧
      4 * (repSet G P (F 2)).card ≤ P.card ∧ 4 * B'.card ≤ P.card := by
  obtain ⟨M, hM, hFM⟩ := phaseChain_safe (G := G) (S := E₀) F hF0 hstep 2
  exact contract_step_sound_and_small K hK E₀ F hF0 hstep hPE hact hPE hFf hM hFM hB' hPne

/-- The contracted instance is nonempty whenever the parent's vertex set is. -/
theorem repSet_card_pos {P : Finset V} (hP : 0 < P.card) : 0 < (repSet G P F).card := by
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hP
  exact Finset.card_pos.mpr ⟨repOf G P F v, repOf_mem_repSet P F hv⟩

/-- **§4 iterates: two contraction levels.**  The child instance `(repSet, univ)` of
`contract_step_sound_and_small'` is again a legitimate §4 instance — its edges end in the
representative set (`cGraph_hP`) and it is nonempty (`repSet_card_pos`) — so the same step runs one
level down.  Assembling both levels returns an MSF of the original instance on `F₂ ∪ (F₂' ∪ B₃)`,
and the measure quarters: `16·|repSet of the child| ≤ |P|` and `16·|B₃| ≤ |P|`. -/
theorem contract_two_levels (K K' : ℕ) (hK : 2 ≤ K) (hK' : 2 ≤ K') {P : Finset V}
    {E₀ : Finset E} (F : ℕ → Finset E) (hF0 : F 0 = ∅)
    (hstep : ∀ i, F (i + 1) = F i ∪ phaseIn G E₀ (F i))
    (hact : ∀ i, i < K → ∀ v ∈ P, ∃ e ∈ E₀, leaves G (F i) v e)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hFf : IsForest G (F 2))
    (F₂ : ℕ → Finset {e // e ∈ crossE G (F 2) E₀}) (hF₂0 : F₂ 0 = ∅)
    (hstep₂ : ∀ i, F₂ (i + 1) =
      F₂ i ∪ phaseIn (cGraph G P (F 2) E₀) (Finset.univ : Finset {e // e ∈ crossE G (F 2) E₀}) (F₂ i))
    (hact₂ : ∀ i, i < K' → ∀ v ∈ repSet G P (F 2),
      ∃ e : {e // e ∈ crossE G (F 2) E₀}, leaves (cGraph G P (F 2) E₀) (F₂ i) v e)
    (hFf₂ : IsForest (cGraph G P (F 2) E₀) (F₂ 2))
    {B₃ : Finset {e // e ∈ crossE (cGraph G P (F 2) E₀) (F₂ 2)
      (Finset.univ : Finset {e // e ∈ crossE G (F 2) E₀})}}
    (hB₃ : IsMSFOf (cGraph (cGraph G P (F 2) E₀) (repSet G P (F 2)) (F₂ 2)
        (Finset.univ : Finset {e // e ∈ crossE G (F 2) E₀}))
      (Finset.univ : Finset {e // e ∈ crossE (cGraph G P (F 2) E₀) (F₂ 2)
        (Finset.univ : Finset {e // e ∈ crossE G (F 2) E₀})}) B₃)
    (hPne : 0 < P.card) :
    IsMSFOf G E₀ (F 2 ∪ (F₂ 2 ∪ B₃.image Subtype.val).image Subtype.val) ∧
      16 * (repSet (cGraph G P (F 2) E₀) (repSet G P (F 2)) (F₂ 2)).card ≤ P.card ∧
      16 * B₃.card ≤ P.card := by
  have hPne₂ : 0 < (repSet G P (F 2)).card := repSet_card_pos (G := G) (F := F 2) hPne
  have hPE₂ : ∀ q ∈ (Finset.univ : Finset {e // e ∈ crossE G (F 2) E₀}),
      (cGraph G P (F 2) E₀).src q ∈ repSet G P (F 2) ∧
        (cGraph G P (F 2) E₀).dst q ∈ repSet G P (F 2) :=
    fun q _ => cGraph_hP (G := G) (P := P) (F := F 2) (E₀ := E₀) hPE q
  have hact₂' : ∀ i, i < K' → ∀ v ∈ repSet G P (F 2),
      ∃ e ∈ (Finset.univ : Finset {e // e ∈ crossE G (F 2) E₀}),
        leaves (cGraph G P (F 2) E₀) (F₂ i) v e := by
    intro i hi v hv
    obtain ⟨e, he⟩ := hact₂ i hi v hv
    exact ⟨e, Finset.mem_univ e, he⟩
  obtain ⟨hinner, hsmall₁, hsmall₂⟩ :=
    contract_step_sound_and_small' (G := cGraph G P (F 2) E₀) K' hK'
      (P := repSet G P (F 2))
      (E₀ := (Finset.univ : Finset {e // e ∈ crossE G (F 2) E₀}))
      F₂ hF₂0 hstep₂ hact₂' hPE₂ hFf₂ hB₃ hPne₂
  obtain ⟨houter, hsmall₀, -⟩ :=
    contract_step_sound_and_small' (G := G) K hK (P := P) (E₀ := E₀) F hF0 hstep hact hPE hFf
      hinner hPne
  refine ⟨houter, ?_, ?_⟩
  · calc 16 * (repSet (cGraph G P (F 2) E₀) (repSet G P (F 2)) (F₂ 2)).card
        = 4 * (4 * (repSet (cGraph G P (F 2) E₀) (repSet G P (F 2)) (F₂ 2)).card) := by ring
      _ ≤ 4 * (repSet G P (F 2)).card := Nat.mul_le_mul_left 4 hsmall₁
      _ ≤ P.card := hsmall₀
  · calc 16 * B₃.card = 4 * (4 * B₃.card) := by ring
      _ ≤ 4 * (repSet G P (F 2)).card := Nat.mul_le_mul_left 4 hsmall₂
      _ ≤ P.card := hsmall₀

/-- A Borůvka phase run on an instance keeps the forest: each phase adds only the instance's own
witness edges, which `boruvka_forest_in_at` proves never close a cycle. -/
theorem isForest_phaseChain (B : Finset E) (F : ℕ → Finset E) (k : ℕ) (hF0 : F 0 = ∅)
    (hstep : ∀ i, F (i + 1) = F i ∪ phaseIn G B (F i)) : IsForest G (F k) := by
  induction k with
  | zero => rw [hF0]; exact IsForest.empty
  | succ n ih =>
      rw [hstep n]
      exact boruvka_forest_in_at (phaseIn_subset B (F n)) ih (phaseIn_borPhaseInAt B (F n))

/-- **§4's step needs neither an MSF nor a forest hypothesis.**  `F` is built from the empty forest
by two phases, so `F 2` is a forest for free. -/
theorem contract_step_sound_and_small'' (K : ℕ) (hK : 2 ≤ K) {P : Finset V}
    (F : ℕ → Finset E) {E₀ : Finset E} (hF0 : F 0 = ∅)
    (hstep : ∀ i, F (i + 1) = F i ∪ phaseIn G E₀ (F i))
    (hact : ∀ i, i < K → ∀ v ∈ P, ∃ e ∈ E₀, leaves G (F i) v e)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    {B' : Finset {e // e ∈ crossE G (F 2) E₀}}
    (hB' : IsMSFOf (cGraph G P (F 2) E₀)
      (Finset.univ : Finset {e // e ∈ crossE G (F 2) E₀}) B')
    (hPne : 0 < P.card) :
    IsMSFOf G E₀ (F 2 ∪ B'.image Subtype.val) ∧
      4 * (repSet G P (F 2)).card ≤ P.card ∧ 4 * B'.card ≤ P.card :=
  contract_step_sound_and_small' (G := G) (P := P) (E₀ := E₀) K hK F hF0 hstep hact hPE
    (isForest_phaseChain E₀ F 2 hF0 hstep) hB' hPne

/-- **Two levels, phase data only.**  `contract_two_levels` without the two forest hypotheses: both
`F 2` and `F₂ 2` are forests because they are two-phase runs from the empty forest. -/
theorem contract_two_levels'' (K K' : ℕ) (hK : 2 ≤ K) (hK' : 2 ≤ K') {P : Finset V}
    {E₀ : Finset E} (F : ℕ → Finset E) (hF0 : F 0 = ∅)
    (hstep : ∀ i, F (i + 1) = F i ∪ phaseIn G E₀ (F i))
    (hact : ∀ i, i < K → ∀ v ∈ P, ∃ e ∈ E₀, leaves G (F i) v e)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (F₂ : ℕ → Finset {e // e ∈ crossE G (F 2) E₀}) (hF₂0 : F₂ 0 = ∅)
    (hstep₂ : ∀ i, F₂ (i + 1) =
      F₂ i ∪ phaseIn (cGraph G P (F 2) E₀) (Finset.univ : Finset {e // e ∈ crossE G (F 2) E₀}) (F₂ i))
    (hact₂ : ∀ i, i < K' → ∀ v ∈ repSet G P (F 2),
      ∃ e : {e // e ∈ crossE G (F 2) E₀}, leaves (cGraph G P (F 2) E₀) (F₂ i) v e)
    {B₃ : Finset {e // e ∈ crossE (cGraph G P (F 2) E₀) (F₂ 2)
      (Finset.univ : Finset {e // e ∈ crossE G (F 2) E₀})}}
    (hB₃ : IsMSFOf (cGraph (cGraph G P (F 2) E₀) (repSet G P (F 2)) (F₂ 2)
        (Finset.univ : Finset {e // e ∈ crossE G (F 2) E₀}))
      (Finset.univ : Finset {e // e ∈ crossE (cGraph G P (F 2) E₀) (F₂ 2)
        (Finset.univ : Finset {e // e ∈ crossE G (F 2) E₀})}) B₃)
    (hPne : 0 < P.card) :
    IsMSFOf G E₀ (F 2 ∪ (F₂ 2 ∪ B₃.image Subtype.val).image Subtype.val) ∧
      16 * (repSet (cGraph G P (F 2) E₀) (repSet G P (F 2)) (F₂ 2)).card ≤ P.card ∧
      16 * B₃.card ≤ P.card :=
  contract_two_levels (G := G) (P := P) (E₀ := E₀) K K' hK hK' F hF0 hstep hact hPE
    (isForest_phaseChain E₀ F 2 hF0 hstep) F₂ hF₂0 hstep₂ hact₂
    (isForest_phaseChain (G := cGraph G P (F 2) E₀)
      (Finset.univ : Finset {e // e ∈ crossE G (F 2) E₀}) F₂ 2 hF₂0 hstep₂)
    hB₃ hPne

/-- **Splicing costs the parent forest plus the child's own account**, in the form the recursion
uses: the child returns a *subtype* forest `B`, not a set of ambient edges. -/
theorem wsum_union_image_eq_add_child {P : Finset V} {E₀ F : Finset E}
    {B : Finset {e // e ∈ crossE G F E₀}} :
    wsum G (F ∪ B.image Subtype.val) =
      wsum G F + wsum (cGraph G P F E₀) B := by
  have hB : ∀ e ∈ B.image Subtype.val, e ∈ crossE G F E₀ := by
    intro e he
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp he
    exact y.2
  rw [wsum_union_eq_child_wsum (G := G) (P := P) (F := F) (E₀ := E₀) hB,
    subtype_image_subtype (G := G) (F := F) (E₀ := E₀)]

/-- **Two levels telescope.**  The assembled forest's weight is the parent forest plus the child
forest plus the grandchild's own account — the recursion's cost bookkeeping, verified across the
nested edge types. -/
theorem wsum_two_levels {P : Finset V} {E₀ : Finset E} (F : ℕ → Finset E)
    (F₂ : ℕ → Finset {e // e ∈ crossE G (F 2) E₀})
    {B₃ : Finset {e // e ∈ crossE (cGraph G P (F 2) E₀) (F₂ 2)
      (Finset.univ : Finset {e // e ∈ crossE G (F 2) E₀})}} :
    wsum G (F 2 ∪ (F₂ 2 ∪ B₃.image Subtype.val).image Subtype.val) =
      wsum G (F 2) + wsum (cGraph G P (F 2) E₀) (F₂ 2) +
        wsum (cGraph (cGraph G P (F 2) E₀) (repSet G P (F 2)) (F₂ 2)
          (Finset.univ : Finset {e // e ∈ crossE G (F 2) E₀})) B₃ := by
  rw [wsum_union_image_eq_add_child (G := G) (P := P) (E₀ := E₀) (F := F 2)]
  rw [wsum_union_image_eq_add_child (G := cGraph G P (F 2) E₀) (P := repSet G P (F 2))
    (E₀ := (Finset.univ : Finset {e // e ∈ crossE G (F 2) E₀})) (F := F₂ 2)]
  ring

/-- **§4's step with activation derived.**  Instead of assuming that every vertex keeps an outgoing
instance edge, require that `E₀` connects the whole vertex set and that no phase has already spanned
it (`hact` becomes `hact_of_conn_E₀`). -/
theorem contract_step_sound_and_small_conn (K : ℕ) (hK : 2 ≤ K) {P : Finset V}
    (F : ℕ → Finset E) {E₀ : Finset E} (hF0 : F 0 = ∅)
    (hstep : ∀ i, F (i + 1) = F i ∪ phaseIn G E₀ (F i))
    (hconn : ∀ u w : V, Conn G E₀ u w)
    (hc : ∀ i, i < K → 2 ≤ compCount G (F i))
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    {B' : Finset {e // e ∈ crossE G (F 2) E₀}}
    (hB' : IsMSFOf (cGraph G P (F 2) E₀)
      (Finset.univ : Finset {e // e ∈ crossE G (F 2) E₀}) B')
    (hPne : 0 < P.card) :
    IsMSFOf G E₀ (F 2 ∪ B'.image Subtype.val) ∧
      4 * (repSet G P (F 2)).card ≤ P.card ∧ 4 * B'.card ≤ P.card :=
  contract_step_sound_and_small'' (G := G) (P := P) (E₀ := E₀) K hK F hF0 hstep
    (hact_of_conn_E₀ K (P := P) F hconn hc) hPE hB' hPne

/-! ## The §4 call record

`ContractCall` packages one level of the §4 recursion.  Its fields are exactly the guarantees the
caller consumes: the splice of the level's phases with the child's answer is an MSF of the
instance, both portal budgets are quartered, and the weight splits between the level and the child.
The child's data live on the contracted edge type `{e // e ∈ crossE G (F 2) E₀}`, so no coverage
field is needed: `E₀ ⊆ F ∪ U ∪ ⋃ kidE` — which fails for supported edges outside `F` — never
arises, unlike in `CallOut`. -/

structure ContractCall (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (F : ℕ → Finset E) where
  B : Finset {e // e ∈ crossE G (F 2) E₀}
  isMSF : IsMSFOf G E₀ (F 2 ∪ B.image Subtype.val)
  smallV : 4 * (repSet G P (F 2)).card ≤ P.card
  smallE : 4 * B.card ≤ P.card
  weight : wsum G (F 2 ∪ B.image Subtype.val) =
    wsum G (F 2) + wsum (cGraph G P (F 2) E₀) B

namespace ContractCall

variable {G : WGraph V E} {P : Finset V} {E₀ : Finset E} {F : ℕ → Finset E}

/-- The child instance's vertex set: one representative per component of the level's forest. -/
noncomputable def kidV (_C : ContractCall G P E₀ F) : Finset V := repSet G P (F 2)

/-- The child instance's edge family: the edges still crossing the level's components. -/
noncomputable def kidE (_C : ContractCall G P E₀ F) : Finset E := crossE G (F 2) E₀

theorem forest (C : ContractCall G P E₀ F) :
    IsForest G (F 2 ∪ C.B.image Subtype.val) := C.isMSF.1.1

theorem subset (C : ContractCall G P E₀ F) :
    F 2 ∪ C.B.image Subtype.val ⊆ E₀ := C.isMSF.1.2.1

theorem spanning (C : ContractCall G P E₀ F) :
    ∀ e ∈ E₀, G.src e ≠ G.dst e →
      Conn G (F 2 ∪ C.B.image Subtype.val) (G.src e) (G.dst e) :=
  C.isMSF.1.2.2

/-- The child is nonempty whenever the instance is. -/
theorem kidV_pos (C : ContractCall G P E₀ F) (hP : 0 < P.card) : 0 < C.kidV.card :=
  repSet_card_pos (G := G) (F := F 2) hP

/-- The child's answer is a forest on the child instance, so it has at most `|kidV| - 1` edges. -/
theorem card_le_kidV (C : ContractCall G P E₀ F)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hne : 0 < C.kidV.card) :
    C.B.card ≤ C.kidV.card - 1 := by
  have hcross : ∀ e ∈ C.B.image Subtype.val, e ∈ crossE G (F 2) E₀ := by
    intro e he
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp he
    exact y.2
  have hf : IsForest (cGraph G P (F 2) E₀)
      ((C.B.image Subtype.val).subtype (fun e => e ∈ crossE G (F 2) E₀)) :=
    isForest_cGraph_of_union (G := G) (P := P) (F := F 2) (E₀ := E₀) hPE _
      hcross C.isMSF.1.1
  rw [subtype_image_subtype (G := G) (F := F 2) (E₀ := E₀)] at hf
  exact child_forest_card_le (G := G) (P := P) (F := F 2) (E₀ := E₀) hPE hf hne

end ContractCall

/-- Build a §4 call record from the phase data alone. -/
def contractCall_of_phases (K : ℕ) (hK : 2 ≤ K) {P : Finset V}
    (F : ℕ → Finset E) {E₀ : Finset E} (hF0 : F 0 = ∅)
    (hstep : ∀ i, F (i + 1) = F i ∪ phaseIn G E₀ (F i))
    (hact : ∀ i, i < K → ∀ v ∈ P, ∃ e ∈ E₀, leaves G (F i) v e)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    {B' : Finset {e // e ∈ crossE G (F 2) E₀}}
    (hB' : IsMSFOf (cGraph G P (F 2) E₀)
      (Finset.univ : Finset {e // e ∈ crossE G (F 2) E₀}) B')
    (hPne : 0 < P.card) : ContractCall G P E₀ F := by
  obtain ⟨hMSF, hV, hE⟩ :=
    contract_step_sound_and_small'' (G := G) (P := P) (E₀ := E₀) K hK F hF0 hstep hact hPE hB' hPne
  exact
    { B := B'
      isMSF := hMSF
      smallV := hV
      smallE := hE
      weight := wsum_union_image_eq_add_child (G := G) (P := P) (E₀ := E₀) (F := F 2) }

/-- Build a §4 call record with activation derived from instance connectivity. -/
def contractCall_of_conn (K : ℕ) (hK : 2 ≤ K) {P : Finset V}
    (F : ℕ → Finset E) {E₀ : Finset E} (hF0 : F 0 = ∅)
    (hstep : ∀ i, F (i + 1) = F i ∪ phaseIn G E₀ (F i))
    (hconn : ∀ u w : V, Conn G E₀ u w)
    (hc : ∀ i, i < K → 2 ≤ compCount G (F i))
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    {B' : Finset {e // e ∈ crossE G (F 2) E₀}}
    (hB' : IsMSFOf (cGraph G P (F 2) E₀)
      (Finset.univ : Finset {e // e ∈ crossE G (F 2) E₀}) B')
    (hPne : 0 < P.card) : ContractCall G P E₀ F := by
  obtain ⟨hMSF, hV, hE⟩ :=
    contract_step_sound_and_small_conn (G := G) (P := P) (E₀ := E₀) K hK F hF0 hstep hconn hc hPE hB' hPne
  exact
    { B := B'
      isMSF := hMSF
      smallV := hV
      smallE := hE
      weight := wsum_union_image_eq_add_child (G := G) (P := P) (E₀ := E₀) (F := F 2) }

/-- **The record is compositional.**  A child that itself hands back a `ContractCall` for its own
instance — the contracted graph, the representative vertices, all crossing edges — yields the
parent's record in one step: the child's splice *is* the forest the parent recursed on. -/
def contractCall_of_two_levels (K : ℕ) (hK : 2 ≤ K) {P : Finset V} {E₀ : Finset E}
    (F : ℕ → Finset E) (hF0 : F 0 = ∅)
    (hstep : ∀ i, F (i + 1) = F i ∪ phaseIn G E₀ (F i))
    (hact : ∀ i, i < K → ∀ v ∈ P, ∃ e ∈ E₀, leaves G (F i) v e)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (F₂ : ℕ → Finset {e // e ∈ crossE G (F 2) E₀})
    (C₂ : ContractCall (cGraph G P (F 2) E₀) (repSet G P (F 2))
      (Finset.univ : Finset {e // e ∈ crossE G (F 2) E₀}) F₂)
    (hPne : 0 < P.card) : ContractCall G P E₀ F := by
  obtain ⟨hMSF, hV, hE⟩ :=
    contract_step_sound_and_small'' (G := G) (P := P) (E₀ := E₀) K hK F hF0 hstep hact hPE
      C₂.isMSF hPne
  exact
    { B := F₂ 2 ∪ C₂.B.image Subtype.val
      isMSF := hMSF
      smallV := hV
      smallE := hE
      weight := wsum_union_image_eq_add_child (G := G) (P := P) (E₀ := E₀) (F := F 2) }

end DLMST
