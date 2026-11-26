import DLMST.Assembly
import DLMST.ForestCard

/-!
# §3.6's input counts, from the forests that make up the inputs

`Section36.msf_input_count` and `Assembly.sum_kidE_le_display_form` take the per-round and per-block
input sizes as hypotheses:

* `|roundIn i| ≤ 2(n−1)` — a round's merge-sort input is the old forest plus the round's new forest;
* `|blkIn b| ≤ (n−1) + r²n` — a block's input is the old forest plus the portal-induced edge set.

This file discharges them.  The ingredients are:

* `card_le_card_sub_one_of_isForest_of_ends`: a forest whose ends all lie in a nonempty vertex set `P`
  has at most `|P| − 1` edges.  This is the paper's "each forest uses at most `n − 1` edges", with
  `n` the instance's portal count (the existing `card_le_card_sub_one_of_isForest` is stated for the
  whole vertex set `V`; the `P`-version is what a node of the recursion needs).
* `card_roundIn_le` / `card_blkIn_le`: containment in the union of two sets with known sizes.
* `RoundData.sum_kidE_le_display_form_of_forests`: §3.6's count with both per-round bounds derived
  from the paper's decomposition of the inputs rather than assumed.
-/

namespace DLMST

open Classical

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

/-- **A forest on a nonempty vertex set `P` has at most `|P| − 1` edges.**  Every vertex outside `P`
is isolated (its component is a singleton), and `P` is nonempty, so the component count is at least
`|V \ P| + 1`; the identity `|F| + compCount = |V|` finishes.  This is the bound the paper applies to
each call's old forest and to each round's new forest. -/
theorem card_le_card_sub_one_of_isForest_of_ends {F : Finset E} {P : Finset V} (hF : IsForest G F)
    (hP : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P) (hP0 : 0 < P.card) :
    F.card ≤ P.card - 1 := by
  classical
  have hcomp : ∀ v : V, v ∉ P → comp G F v = {v} := by
    intro v hv
    have key : ∀ {x : V} {es : List E}, Path G v es x → (∀ e ∈ es, e ∈ F) → x = v := by
      intro x es p hmem
      induction p with
      | nil u => rfl
      | fwd e hs _ _ _ =>
          exact absurd (hP e (hmem e (by simp))).1 (by rw [hs]; exact hv)
      | bwd e hd _ _ _ =>
          exact absurd (hP e (hmem e (by simp))).2 (by rw [hd]; exact hv)
    ext x
    rw [mem_comp, Finset.mem_singleton]
    exact ⟨fun h => by
      obtain ⟨es, p, hmem⟩ := path_of_conn h
      exact key p hmem,
      fun hx => by rw [hx]; exact Conn.refl v⟩
  obtain ⟨v, hvP⟩ := Finset.card_pos.mp hP0
  have hsplit : (Finset.univ \ P).card + P.card = Fintype.card V := by
    have h := Finset.card_sdiff_add_card_inter (s := (Finset.univ : Finset V)) (t := P)
    rwa [Finset.univ_inter, Finset.card_univ] at h
  -- the component of `v` is none of the components outside `P`, so it adds one to the count
  have hmissing : comp G F v ∉ (Finset.univ \ P).image (fun u : V => ({u} : Finset V)) := by
    intro h
    obtain ⟨u, hu, hue⟩ := Finset.mem_image.mp h
    have huv : v = u := by
      have : v ∈ comp G F v := comp_self_mem
      rw [← hue] at this
      simpa using this
    exact (Finset.mem_sdiff.mp hu).2 (huv ▸ hvP)
  have hcard_le : (Finset.univ \ P).card + 1 ≤ compCount G F := by
    have hins : insert (comp G F v) ((Finset.univ \ P).image (fun u : V => ({u} : Finset V)))
        ⊆ Finset.univ.image (comp G F) := by
      intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs'
      · exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hs'
        exact Finset.mem_image.mpr ⟨u, Finset.mem_univ u, hcomp u (Finset.mem_sdiff.mp hu).2⟩
    have hcard := Finset.card_le_card hins
    have hinj : ((Finset.univ \ P).image (fun u : V => ({u} : Finset V))).card =
        (Finset.univ \ P).card :=
      Finset.card_image_of_injective _
        (fun a b h => by simpa using congrArg (fun s : Finset V => a ∈ s) h)
    rw [Finset.card_insert_of_notMem hmissing, hinj] at hcard
    simpa [compCount] using hcard
  have hid := card_add_compCount (G := G) hF
  omega

/-- **A round's input.**  If a round's merge-sort input sits inside `old ∪ new` with `|old| ≤ n−1` and
`|new| ≤ n−1`, then it has at most `2(n−1)` edges — the per-round count of `Section36`. -/
theorem card_roundIn_le {R Fold Fnew : Finset E} {n : ℕ} (hR : R ⊆ Fold ∪ Fnew)
    (hFold : Fold.card ≤ n - 1) (hFnew : Fnew.card ≤ n - 1) :
    R.card ≤ 2 * (n - 1) := by
  have h1 : R.card ≤ (Fold ∪ Fnew).card := Finset.card_le_card hR
  have h2 : (Fold ∪ Fnew).card ≤ Fold.card + Fnew.card := Finset.card_union_le _ _
  omega

/-- **A block's input.**  If a block's input sits inside `old ∪ D` with `|old| ≤ n−1` and
`|D| ≤ r²n` (the portal-induced edges), then it has at most `(n−1) + r²n` edges. -/
theorem card_blkIn_le {R Fold Dset : Finset E} {r n : ℕ} (hR : R ⊆ Fold ∪ Dset)
    (hFold : Fold.card ≤ n - 1) (hD : Dset.card ≤ r ^ 2 * n) :
    R.card ≤ (n - 1) + r ^ 2 * n := by
  have h1 : R.card ≤ (Fold ∪ Dset).card := Finset.card_le_card hR
  have h2 : (Fold ∪ Dset).card ≤ Fold.card + Dset.card := Finset.card_union_le _ _
  omega

namespace CallOut

namespace RoundData

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ} {P : Finset V} {E₀ : Finset E}
  (D : RoundData G P E₀ ι t)

/-- **§3.6's per-call input count, with the per-round and per-block sizes derived.**  The children's
inputs sit inside the union of the rounds' inputs and the blocks' inputs (`hsub`); each round's input
is the old forest plus the round's new forest, each of at most `n−1` edges (`hround`, `hFold`,
`hFnew`); each block's input is the old forest plus at most `r²n` portal edges (`hblk`, `hD`).  Then
`Σ|Eᵢ| ≤ |U(F)| + 2t²(n−1) + t((n−1)+r²n)` — p. 24's count, with no per-round size assumed. -/
theorem sum_kidE_le_display_form_of_forests {roundIn : Fin (t ^ 2) → Finset E}
    {blkIn : Fin t → Finset E} {Fold : Finset E} {Fnew : Fin (t ^ 2) → Finset E}
    {Dset : Fin t → Finset E} {r n : ℕ}
    (hsub : ∀ p : Fin (t ^ 2) × ι,
      D.inp' p ⊆ D.toCall.U ∪ (Finset.univ.biUnion roundIn ∪ Finset.univ.biUnion blkIn))
    (hround : ∀ i, roundIn i ⊆ Fold ∪ Fnew i)
    (hblk : ∀ b, blkIn b ⊆ Fold ∪ Dset b)
    (hFold : Fold.card ≤ n - 1) (hFnew : ∀ i, (Fnew i).card ≤ n - 1)
    (hD : ∀ b, (Dset b).card ≤ r ^ 2 * n) :
    (∑ i, ((D.toCall.kidE i).card))
      ≤ (D.toCall.U).card + 2 * t ^ 2 * (n - 1) + t * ((n - 1) + r ^ 2 * n) :=
  D.sum_kidE_le_display_form hsub
    (fun i => card_roundIn_le (hround i) hFold (hFnew i))
    (fun b => card_blkIn_le (hblk b) hFold (hD b))

end RoundData

end CallOut

end DLMST