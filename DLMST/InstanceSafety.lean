import DLMST.Boruvka
import DLMST.InstanceBoruvka
import DLMST.LightSpan

/-!
# Borůvka's blue rule on an instance

`LightSpan` proves the relative versions of the exchange and cut facts — `IsMSFOf.exchange`,
`IsMSFOf.lightest_bridge` — for an edge-induced instance `G[S]`.  `Boruvka` proves the blue rule for
the whole graph: the lightest edge leaving a component lies in *some* minimum spanning forest.

This file joins the two: **the blue rule holds inside an instance**.  If `e ∈ S` leaves the
`F`-component of `G.src e` and is no heavier than any edge of `S` that does, then an MSF of `G[S]`
containing `F` can be replaced by one containing `insert e F`.  This is the step that lets §4's
recursion carry the hypothesis "the Borůvka forest is contained in some MSF of the instance" from
one level to the next without going through the whole graph.
-/

open Classical

namespace DLMST

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

/-- **The blue rule, relative to the instance `S`.**  The exchanged tree edge is found on the
`T`-path of `e` (hence in `T ⊆ S`), so `IsMSFOf.exchange` transfers the optimality and no edge
outside `S` is ever needed. -/
theorem boruvka_blue_rule_of {S F T : Finset E} (hT : IsMSFOf G S T) (hsub : F ⊆ T) (e : E)
    (he : e ∈ S) (hopen : ¬ Conn G F (G.src e) (G.dst e))
    (hlight : ∀ g ∈ S, leaves G F (G.src e) g → G.weight e ≤ G.weight g) :
    ∃ T', IsMSFOf G S T' ∧ insert e F ⊆ T' := by
  classical
  have hTf : IsForest G T := hT.1.1
  have hTS : T ⊆ S := hT.1.2.1
  have hTsp : ∀ x ∈ S, G.src x ≠ G.dst x → Conn G T (G.src x) (G.dst x) := hT.1.2.2
  have hne : G.src e ≠ G.dst e := fun h => hopen (h ▸ Conn.refl (G.src e))
  obtain ⟨es0, p0, hmem0⟩ := path_of_conn (hTsp e he hne)
  obtain ⟨es, p, hmem, hf⟩ := hTf.exists_consecFree_trail es0 p0 hmem0
  let C : Set V := { x | Conn G F (G.src e) x }
  obtain ⟨g, hg, hcr⟩ := crossing p C (Conn.refl (G.src e)) (fun hh => hopen hh)
  have hlv : leaves G F (G.src e) g := by
    rcases hcr with ⟨hs, hd⟩ | ⟨hs, hd⟩
    · exact Or.inl ⟨hs, hd⟩
    · exact Or.inr ⟨hs, hd⟩
  have hgF : g ∉ F := by
    intro hgf
    rcases hcr with ⟨hs, hd⟩ | ⟨hs, hd⟩
    · exact absurd (hs.trans (Conn.step g hgf)) hd
    · exact absurd (hd.trans (Conn.step g hgf).symm) hs
  have hgT : g ∈ T := hmem g hg
  have hsep : ¬ Conn G (T.erase g) (G.src e) (G.dst e) := hTf.sep_of_mem_trail p hmem hf hg
  refine ⟨insert e (T.erase g),
    IsMSFOf.exchange hT hgT he hsep (hlight g (hTS hgT) hlv), ?_⟩
  intro x hx
  rcases Finset.mem_insert.mp hx with hx_eq | hxF
  · rw [hx_eq]
    exact Finset.mem_insert_self _ _
  · refine Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun hxg => absurd (hxg ▸ hxF) hgF, ?_⟩)
    exact hsub hxF

/-- `BoruvkaPhase.exists_trail_crossing` needs the `T`-connectivity of *every* non-loop edge; an
instance spanning forest only guarantees it inside `S`.  For the one edge `e` that matters this
weaker input suffices. -/
theorem exists_trail_crossing_of {F T : Finset E} {e : E} {v : V} (hTf : IsForest G T)
    (hconn : Conn G T (G.src e) (G.dst e)) (hlv : leaves G F v e) :
    ∃ g, g ∈ T ∧ g ∉ F ∧ leaves G F v g ∧ ¬ Conn G (T.erase g) (G.src e) (G.dst e) := by
  classical
  rcases hlv with ⟨hs, hd⟩ | ⟨hs, hd⟩
  · obtain ⟨es0, p0, hmem0⟩ := path_of_conn hconn
    obtain ⟨es, p, hmem, hf⟩ := hTf.exists_consecFree_trail es0 p0 hmem0
    obtain ⟨g, hg, hcr⟩ := crossing p {x : V | Conn G F v x} hs hd
    have hgF : g ∉ F := by
      intro hgf
      rcases hcr with ⟨hsin, hdout⟩ | ⟨hsin, hdout⟩
      · exact absurd (hsin.trans (Conn.step g hgf)) hdout
      · exact absurd (hdout.trans (Conn.step g hgf).symm) hsin
    exact ⟨g, hmem g hg, hgF, hcr, hTf.sep_of_mem_trail p hmem hf hg⟩
  · obtain ⟨es0, p0, hmem0⟩ := path_of_conn (Conn.symm hconn)
    obtain ⟨es, p, hmem, hf⟩ := hTf.exists_consecFree_trail es0 p0 hmem0
    obtain ⟨g, hg, hcr⟩ := crossing p {x : V | Conn G F v x} hd hs
    have hgF : g ∉ F := by
      intro hgf
      rcases hcr with ⟨hsin, hdout⟩ | ⟨hsin, hdout⟩
      · exact absurd (hsin.trans (Conn.step g hgf)) hdout
      · exact absurd (hdout.trans (Conn.step g hgf).symm) hsin
    exact ⟨g, hmem g hg, hgF, hcr, fun hc => hTf.sep_of_mem_trail p hmem hf hg (Conn.symm hc)⟩

/-- **The multi-cut blue rule, relative to the instance `S`.**  If every edge of `A ⊆ S` is the
`wOrd`-least edge of `S` leaving the component that picked it, and some minimum spanning forest of
`G[S]` contains `F`, then some minimum spanning forest of `G[S]` contains all of `F ∪ A`.
`BoruvkaPhase.boruvka_round_at`'s two-level exchange, with the instance as the ambient graph: the
cuts stay inside `S`, so `IsMSFOf.exchange` replaces `isMSF_exchange` and no edge outside `S` is
ever compared. -/
theorem boruvka_round_of {S F A T₀ : Finset E} (hT₀ : IsMSFOf G S T₀) (hsub : F ⊆ T₀)
    (hph : BorPhaseInAt G S F A) (hAS : A ⊆ S) : ∃ T, IsMSFOf G S T ∧ F ∪ A ⊆ T := by
  classical
  obtain ⟨T₁, hT₁mem, hT₁max⟩ :=
    Finset.exists_max_image (Finset.univ.filter fun T : Finset E => IsMSFOf G S T ∧ F ⊆ T)
      (fun T : Finset E => (T ∩ A).card)
      ⟨T₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT₀, hsub⟩⟩
  obtain ⟨T, hTco, hTmin⟩ :=
    Set.exists_min_image
      {T : Finset E | T ∈ Finset.univ.filter fun T : Finset E =>
        IsMSFOf G S T ∧ F ⊆ T ∧ (T ∩ A).card = (T₁ ∩ A).card}
      (fun T : Finset E => (T ∩ A).sum (wRank G A))
      (Set.Finite.subset Set.finite_univ (Set.subset_univ _))
      ⟨T₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hT₁mem).2.1,
        (Finset.mem_filter.mp hT₁mem).2.2, rfl⟩⟩
  obtain ⟨hTmsf, hFT, hTeq⟩ := (Finset.mem_filter.mp hTco).2
  refine ⟨T, hTmsf, Finset.union_subset_iff.mpr ⟨hFT, ?_⟩⟩
  by_contra hnot
  rw [Finset.not_subset] at hnot
  obtain ⟨e, heA, heT⟩ := hnot
  obtain ⟨v, hlv, hmin⟩ := hph.2 e heA
  have hopen : ¬ Conn G F (G.src e) (G.dst e) := hph.1 e heA
  have hne : G.src e ≠ G.dst e := fun h => hopen (h ▸ Conn.refl (G.src e))
  have heS : e ∈ S := hAS heA
  obtain ⟨g, hgT, hgF, hlvg, hsep⟩ :=
    exists_trail_crossing_of hTmsf.1.1 (hTmsf.1.2.2 e heS hne) hlv
  have hwo : wOrd G e g := hmin g (hTmsf.1.2.1 hgT) hlvg
  have hgne : g ≠ e := fun h => heT (h ▸ hgT)
  have hT' : IsMSFOf G S (insert e (T.erase g)) :=
    IsMSFOf.exchange hTmsf hgT heS hsep (weight_le_of_wOrd hwo)
  have hF' : F ⊆ insert e (T.erase g) := fun x hx =>
    Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun hxg => hgF (hxg ▸ hx), hFT hx⟩)
  have hT'Fam : insert e (T.erase g) ∈
      Finset.univ.filter fun T : Finset E => IsMSFOf G S T ∧ F ⊆ T :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT', hF'⟩
  have hinter : (insert e (T.erase g)) ∩ A = insert e ((T ∩ A).erase g) := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · intro h
      obtain ⟨hx, hA⟩ := h
      rcases hx with rfl | hxT
      · exact Or.inl rfl
      · exact Or.inr ⟨hxT.1, hxT.2, hA⟩
    · rintro (rfl | ⟨hxg, hxT, hA⟩)
      · exact ⟨Or.inl rfl, heA⟩
      · exact ⟨Or.inr ⟨hxg, hxT⟩, hA⟩
  have heinter : e ∉ (T ∩ A).erase g := fun h =>
    heT (Finset.mem_inter.mp (Finset.mem_erase.mp h).2).1
  by_cases hgA : g ∈ A
  · have hmemg : g ∈ T ∩ A := Finset.mem_inter.mpr ⟨hgT, hgA⟩
    have hcard' : ((insert e (T.erase g)) ∩ A).card = (T ∩ A).card := by
      rw [hinter, Finset.card_insert_of_notMem heinter, Finset.card_erase_of_mem hmemg]
      have hpos : 0 < (T ∩ A).card := Finset.card_pos.mpr ⟨g, hmemg⟩
      omega
    have hT'co : insert e (T.erase g) ∈
        {T : Finset E | T ∈ Finset.univ.filter fun T : Finset E =>
          IsMSFOf G S T ∧ F ⊆ T ∧ (T ∩ A).card = (T₁ ∩ A).card} :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ⟨hT', hF', by rw [hcard']; exact hTeq⟩⟩
    have hle : (T ∩ A).sum (wRank G A) ≤
        wRank G A e + ((T ∩ A).erase g).sum (wRank G A) := by
      have h := hTmin _ hT'co
      rw [hinter, Finset.sum_insert heinter] at h
      exact h
    have hsum : ((T ∩ A).erase g).sum (wRank G A) + wRank G A g =
        (T ∩ A).sum (wRank G A) := Finset.sum_erase_add _ _ hmemg
    have hrank : wRank G A e < wRank G A g := wRank_lt heA (wOrdLt_of_wOrd hwo (Ne.symm hgne))
    have hpos : wRank G A g ≤ (T ∩ A).sum (wRank G A) :=
      Finset.single_le_sum (f := wRank G A) (fun _ _ => Nat.zero_le _) hmemg
    omega
  · have hgTA : g ∉ T ∩ A := fun h => hgA (Finset.mem_inter.mp h).2
    have her : (T ∩ A).erase g = T ∩ A := by
      ext x
      by_cases hx : x = g
      · subst hx
        simp [hgTA]
      · simp [hx]
    have hcard' : ((insert e (T.erase g)) ∩ A).card = (T ∩ A).card + 1 := by
      rw [hinter, Finset.card_insert_of_notMem heinter, her]
    have hle : ((insert e (T.erase g)) ∩ A).card ≤ (T₁ ∩ A).card := hT₁max _ hT'Fam
    rw [hcard'] at hle
    omega

/-- **Definition 2.8's phase is safe inside an instance.**  If some MSF of `G[S]` contains `F`,
then some MSF of `G[S]` contains `F` together with the whole phase `phaseIn G S F`.  In the
recursion the candidate edges are the instance's own, so the choice rule is compared against `S`. -/
theorem phaseIn_round_of {S : Finset E} (F T₀ : Finset E) (hT₀ : IsMSFOf G S T₀) (hsub : F ⊆ T₀) :
    ∃ T, IsMSFOf G S T ∧ F ∪ phaseIn G S F ⊆ T :=
  boruvka_round_of hT₀ hsub (phaseIn_borPhaseInAt S F) (phaseIn_subset S F)

/-- **Every level of the phase chain stays inside some MSF of the instance.**  Starting from
`F 0 = ∅` and `F (i + 1) = F i ∪ phaseIn G S (F i)`, each `F k` is contained in a minimum spanning
forest of `G[S]` — the hypothesis `hM`/`hFM` of the contraction step, discharged. -/
theorem phaseChain_safe {S : Finset E} (F : ℕ → Finset E) (hF0 : F 0 = ∅)
    (hstep : ∀ i, F (i + 1) = F i ∪ phaseIn G S (F i)) (k : ℕ) :
    ∃ T, IsMSFOf G S T ∧ F k ⊆ T := by
  induction k with
  | zero =>
      obtain ⟨T, hT⟩ := exists_msfof (G := G) S
      exact ⟨T, hT, by rw [hF0]; exact Finset.empty_subset T⟩
  | succ n ih =>
      obtain ⟨T, hT, hsub⟩ := ih
      rw [hstep n]
      exact phaseIn_round_of (F n) T hT hsub

end DLMST