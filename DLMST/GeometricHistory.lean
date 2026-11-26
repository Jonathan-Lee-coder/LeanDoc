import DLMST.Geometric
import DLMST.Assembly

/-!
# The geometric family of a history: `A r` is `roundCand` at the round's `(σ, F)`

`Geometric.lean` proved `truth ∈ A` for one round's geometry.  This file attaches that family to a
`History` (Definition 3.8): round `r = (b, i)` uses the recorded spoke vector `H.spoke b i` and
forest `H.forest b i`, so

`geomFamily H slot eN r = roundCand (H.spoke r) (H.forest r) (edges of slot r) (eN r)`

is the paper's `A r`, with `slot : E → Fin t × Fin t` assigning each edge to a round.  The main
results are the two facts the driver owes §3.5:

* `truth_of_history` — the history's preferred-action vector is in `geomFamily` (`htruth`), given
  §3.1's consistency of the history, the per-round forest invariant, and the geometric side
  condition `hFsp` (no forest edge is a spoke);
* `est_of_choice` — for any choice of one member per round (`hc`), the induced global estimate
  `est e = c (slot e) e` restricts to that member on every fibre (`hest`), so the estimate can be
  read off the enumerated family without knowing the truth;
* `log_geomFamily_le` — per round `log |A r| ≤ 4√(2n·m_r)` with `m_r = #{e // slot e = r}`, the
  size the sampling's `⌈log |A r|⌉` consumes.
-/

namespace DLMST

open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

/-- **The paper's family `A` per round of a history.**  The candidate vectors for the edges of slot
`r` are decoded from the argmax family over the round's ground set `image σ ∪ F`. -/
noncomputable def geomFamily {t : ℕ} (H : History V E t) (slot : E → Fin t × Fin t)
    (eN : ∀ (b i : Fin t), Ground G (H.spoke b i) (H.forest b i) ≃
      Fin (Fintype.card (Ground G (H.spoke b i) (H.forest b i))))
    (r : Fin t × Fin t) : Finset ({e : E // slot e = r} → Pref) :=
  roundCand (G := G) (σ := H.spoke r.1 r.2) (F := H.forest r.1 r.2)
    (ιE := fun x : {e : E // slot e = r} => x.1) (eN r.1 r.2)

/-- **`htruth`**: a consistent history's action vector lies in the geometric family of its round,
provided each round forest really is a forest and no forest edge is a spoke. -/
theorem truth_of_history {t : ℕ} (H : History V E t) (hcons : H.Consistent (G := G))
    (hF : ∀ b i, IsForest G (H.forest b i))
    (hFsp : ∀ (b i : Fin t) (g : E), g ∈ H.forest b i → ¬ IsSpoke (H.spoke b i) g)
    (slot : E → Fin t × Fin t)
    (eN : ∀ (b i : Fin t), Ground G (H.spoke b i) (H.forest b i) ≃
      Fin (Fintype.card (Ground G (H.spoke b i) (H.forest b i)))) :
    ∀ r : Fin t × Fin t,
      (fun x : {e : E // slot e = r} => H.pref x.1 r.1 r.2) ∈ geomFamily (G := G) H slot eN r := by
  intro r
  have hmem := truth_mem_roundCand (G := G) (σ := H.spoke r.1 r.2) (F := H.forest r.1 r.2)
    (hF r.1 r.2) (hFsp r.1 r.2) (fun x : {e : E // slot e = r} => x.1) (eN r.1 r.2)
  have hv : (fun x : {e : E // slot e = r} => H.pref x.1 r.1 r.2)
      = (fun x : {e : E // slot e = r}
          => actOf G (H.spoke r.1 r.2) (H.forest r.1 r.2) x.1) :=
    funext fun x => hcons x.1 r.1 r.2
  rw [hv]
  exact hmem

theorem geomFamily_nonempty {t : ℕ} (H : History V E t) (hcons : H.Consistent (G := G))
    (hF : ∀ b i, IsForest G (H.forest b i))
    (hFsp : ∀ (b i : Fin t) (g : E), g ∈ H.forest b i → ¬ IsSpoke (H.spoke b i) g)
    (slot : E → Fin t × Fin t)
    (eN : ∀ (b i : Fin t), Ground G (H.spoke b i) (H.forest b i) ≃
      Fin (Fintype.card (Ground G (H.spoke b i) (H.forest b i))))
    (r : Fin t × Fin t) : (geomFamily (G := G) H slot eN r).Nonempty :=
  ⟨_, truth_of_history H hcons hF hFsp slot eN r⟩

/-- **`hest`**: any per-round choice of a family member induces a global estimate whose fibre at `r`
*is* that member — so the algorithm's estimate (read off the enumerated family) satisfies the driver's
membership premise without knowing the truth. -/
theorem est_of_choice {t : ℕ} (H : History V E t) (slot : E → Fin t × Fin t)
    (eN : ∀ (b i : Fin t), Ground G (H.spoke b i) (H.forest b i) ≃
      Fin (Fintype.card (Ground G (H.spoke b i) (H.forest b i))))
    (c : ∀ r : Fin t × Fin t, {e : E // slot e = r} → Pref)
    (hc : ∀ r, c r ∈ geomFamily (G := G) H slot eN r) :
    ∀ r : Fin t × Fin t,
      (fun x : {e : E // slot e = r} =>
        (fun e => c (slot e) ⟨e, rfl⟩) x.1) ∈ geomFamily (G := G) H slot eN r := by
  intro r
  have hv : (fun x : {e : E // slot e = r} => c (slot x.1) ⟨x.1, rfl⟩) = c r := by
    funext x
    obtain ⟨e', he⟩ := x
    cases he
    rfl
  rw [hv]
  exact hc r

/-- **The per-round count**: `|A r| ≤ C(|groundSet| + m_r - 1, m_r)`. -/
theorem geomFamily_card_le {t : ℕ} (H : History V E t) (slot : E → Fin t × Fin t)
    (eN : ∀ (b i : Fin t), Ground G (H.spoke b i) (H.forest b i) ≃
      Fin (Fintype.card (Ground G (H.spoke b i) (H.forest b i))))
    (r : Fin t × Fin t) :
    (geomFamily (G := G) H slot eN r).card ≤
      Nat.choose (Fintype.card (Ground G (H.spoke r.1 r.2) (H.forest r.1 r.2)) +
        Fintype.card {e : E // slot e = r} - 1) (Fintype.card {e : E // slot e = r}) :=
  roundCand_card_le (G := G) (σ := H.spoke r.1 r.2) (F := H.forest r.1 r.2)
    (ιE := fun x : {e : E // slot e = r} => x.1) (eN r.1 r.2)

/-- **Lemma 3.10's third factor per round**: `log |A r| ≤ 4√(2n·m_r)`. -/
theorem log_geomFamily_le {t : ℕ} (H : History V E t) (slot : E → Fin t × Fin t)
    (eN : ∀ (b i : Fin t), Ground G (H.spoke b i) (H.forest b i) ≃
      Fin (Fintype.card (Ground G (H.spoke b i) (H.forest b i))))
    (r : Fin t × Fin t) (hF : IsForest G (H.forest r.1 r.2)) {n : ℕ}
    (hV : Fintype.card V ≤ n) :
    Real.log ((geomFamily (G := G) H slot eN r).card : ℝ) ≤
      4 * Real.sqrt ((2 * n : ℝ) * (Fintype.card {e : E // slot e = r} : ℝ)) :=
  log_roundCand_le (G := G) (σ := H.spoke r.1 r.2) (F := H.forest r.1 r.2)
    (ιE := fun x : {e : E // slot e = r} => x.1) (eN r.1 r.2) hF hV

/-- The same membership in the shape the driver uses, `H.pref · (slot ·)`, at the round of the edge. -/
theorem truth_of_history_slot {t : ℕ} (H : History V E t) (hcons : H.Consistent (G := G))
    (hF : ∀ b i, IsForest G (H.forest b i))
    (hFsp : ∀ (b i : Fin t) (g : E), g ∈ H.forest b i → ¬ IsSpoke (H.spoke b i) g)
    (slot : E → Fin t × Fin t)
    (eN : ∀ (b i : Fin t), Ground G (H.spoke b i) (H.forest b i) ≃
      Fin (Fintype.card (Ground G (H.spoke b i) (H.forest b i)))) :
    ∀ r : Fin t × Fin t,
      (fun x : {e : E // slot e = r} => H.pref x.1 (slot x.1).1 (slot x.1).2) ∈
        geomFamily (G := G) H slot eN r := by
  intro r
  have hmem := truth_of_history H hcons hF hFsp slot eN r
  have hv : (fun x : {e : E // slot e = r} => H.pref x.1 (slot x.1).1 (slot x.1).2)
      = (fun x : {e : E // slot e = r} => H.pref x.1 r.1 r.2) := by
    funext x
    obtain ⟨e', he⟩ := x
    cases he
    rfl
  rw [hv]
  exact hmem

/-- **§3.5's display-form error bound with the geometric family.**  The candidate family `A`, the
memberships `htruth`/`hest` and the estimate itself are no longer hypotheses: `A r` is
`geomFamily H slot eN r`, the truth is in it by `truth_of_history_slot`, the estimate is any choice
`c` of one member per round (`est_of_choice`), and only the geometric side conditions
(`H.Consistent`, per-round `IsForest`, `hFsp`) and Lemma 3.11's `lost` bound remain. -/
theorem card_U_le_display_form_of_geometry {ι : Type*} [Fintype ι] [DecidableEq ι] {t s : ℕ}
    {P : Finset V} {E₀ : Finset E} (D : CallOut.RoundData G P E₀ ι t) (H : History V E s)
    (slot : E → Fin s × Fin s)
    (eN : ∀ (b i : Fin s), Ground G (H.spoke b i) (H.forest b i) ≃
      Fin (Fintype.card (Ground G (H.spoke b i) (H.forest b i))))
    (c : ∀ r : Fin s × Fin s, {e : E // slot e = r} → Pref)
    (hc : ∀ r, c r ∈ geomFamily (G := G) H slot eN r)
    (hcons : H.Consistent (G := G))
    (hF : ∀ b i, IsForest G (H.forest b i))
    (hFsp : ∀ (b i : Fin s) (g : E), g ∈ H.forest b i → ¬ IsSpoke (H.spoke b i) g)
    {m n : ℝ} (ht : 2 ≤ t)
    (h : ∀ e ∈ E₀, ¬ supported G D.toCall.F e →
      H.errOf (fun e => c (slot e) ⟨e, rfl⟩) e (slot e))
    (hlost : (H.lost slot : ℝ) * Real.log 2 ≤
      (2 * Real.sqrt 2 + 4) * (t : ℝ) ^ 2 * Real.sqrt (m * n) + 2 * m / (t : ℝ))
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hmE : (Fintype.card E : ℝ) ≤ m) :
    ∃ S : ∀ r : Fin s × Fin s, Finset {e : E // slot e = r},
      (∀ r, (S r).card ≤
        2 * t * (Nat.ceil (Real.log ((geomFamily (G := G) H slot eN r).card : ℝ)) + 1)) ∧
      ((∀ r (x : {e : E // slot e = r}), x ∈ S r → c (slot x.1) ⟨x.1, rfl⟩ = H.pref x.1 r.1 r.2) →
        ((D.toCall.U).card : ℝ) ≤ 10 * (t : ℝ) ^ 2 * Real.sqrt (m * n) + 4 * m / (t : ℝ)) := by
  have htr := truth_of_history_slot (G := G) H hcons hF hFsp slot eN
  have hest := est_of_choice (G := G) H slot eN c hc
  have hmain := D.card_U_le_display_form (G := G) H (fun e => c (slot e) ⟨e, rfl⟩) slot ht h
    hlost (geomFamily (G := G) H slot eN) htr hest hm hn hmE
  obtain ⟨S, hScard, hcount⟩ := hmain
  refine ⟨S, hScard, fun hagree => hcount (fun r x hx => ?_)⟩
  obtain ⟨e', he⟩ := x
  cases he
  exact hagree _ ⟨e', rfl⟩ hx

end DLMST