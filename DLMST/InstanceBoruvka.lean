import DLMST.InstancePhase
import DLMST.BoruvkaPhase

/-!
# Borůvka phases inside an instance

`Boruvka.BorPhase` states the choice rule against *every* edge leaving the component.  A call of the
recursion, however, may only use its own edge set `E₀`: its phase picks, per component, the
`wOrd`-lightest edge leaving it **among the edges of `E₀`**.  Such a phase is not a `BorPhase`
globally, so this file introduces the ambient-set version

* `BorPhaseIn G B F A` — openness, and each edge is `wOrd`-least among the `B`-edges leaving its
  tail component (with `A ⊆ B`);

and re-proves the two facts the halving needs for it:

* `boruvka_forest_in` — `F ∪ A` stays a forest (the heaviest-edge argument only ever compares
  phase edges with each other, so restricting the candidates to `B` keeps it valid);
* `compCountOn_halves_in` and `compCountOn_pow_halves_in` / `compCountOn_le_real_in` — the instance
  component count halves per phase and is `≤ |P|/2^k` after `k ≤ K` phases.

`BorPhase.toIn` recovers the ambient form from a global `BorPhase` when `A ⊆ B`.
-/

namespace DLMST

open Classical

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]
  {G : WGraph V E}

/-- A Borůvka phase that only competes against the edges of `B`: open edges, each `wOrd`-least among
the `B`-edges leaving its own tail component. -/
def BorPhaseIn (G : WGraph V E) (B F A : Finset E) : Prop :=
  (∀ e ∈ A, ¬ Conn G F (G.src e) (G.dst e)) ∧
    (∀ e ∈ A, ∀ f ∈ B, leaves G F (G.src e) f → wOrd G e f)

/-- A global phase is an ambient phase for any ambient set `B`. -/
theorem BorPhase.toIn {B F A : Finset E} (hph : BorPhase G F A) : BorPhaseIn G B F A :=
  ⟨hph.1, fun e he f _ hl => hph.2 e he f hl⟩

protected theorem BorPhaseIn.erase {B F A : Finset E} (hph : BorPhaseIn G B F A) (a : E) :
    BorPhaseIn G B F (A.erase a) :=
  ⟨fun e he => hph.1 e (Finset.mem_of_mem_erase he),
    fun e he f hf hl => hph.2 e (Finset.mem_of_mem_erase he) f hf hl⟩

/-- An ambient phase edge is never already in the forest. -/
theorem BorPhaseIn.not_mem {B F A : Finset E} (hph : BorPhaseIn G B F A) {e : E}
    (he : e ∈ A) : e ∉ F :=
  not_mem_of_not_conn (hph.1 e he)

/-- An ambient phase edge is not a loop. -/
theorem BorPhaseIn.nloop {B F A : Finset E} (hph : BorPhaseIn G B F A) {e : E} (he : e ∈ A) :
    G.src e ≠ G.dst e :=
  fun h => hph.1 e he (by rw [h]; exact Conn.refl (G.dst e))

/-- **An ambient phase keeps a forest.**  Same heaviest-edge argument as `boruvka_forest`; the only
change is that the choice rule is consulted with the membership proof `g ∈ B` supplied by `A ⊆ B`. -/
theorem boruvka_forest_in {B F A : Finset E} (hAB : A ⊆ B) (hF : IsForest G F)
    (hph : BorPhaseIn G B F A) : IsForest G (F ∪ A) := by
  classical
  have key : ∀ (n : ℕ) (A : Finset E), A.card = n → A ⊆ B →
      BorPhaseIn G B F A → IsForest G (F ∪ A) := by
    intro n
    induction n with
    | zero =>
        intro A hcard _ _
        rw [Finset.card_eq_zero.mp hcard, Finset.union_empty]
        exact hF
    | succ n ih =>
        intro A hcard hAB' hph
        have hne : A.Nonempty := by
          refine Finset.ne_empty_iff_nonempty.mp ?_
          intro h
          rw [h, Finset.card_empty] at hcard
          omega
        obtain ⟨m, hm, hgt⟩ := exists_wOrd_max (G := G) A hne
        have hopen : ¬ Conn G F (G.src m) (G.dst m) := hph.1 m hm
        have hconn : ¬ Conn G (F ∪ A.erase m) (G.src m) (G.dst m) := by
          intro hc
          obtain ⟨es, pes, hmem⟩ := path_of_conn hc
          obtain ⟨g, hg, hcr⟩ := crossing pes {x | Conn G F (G.src m) x} (Conn.refl (G.src m)) hopen
          have hgF : g ∉ F := by
            intro hf
            rcases hcr with ⟨hs, hd⟩ | ⟨hs, hd⟩
            · exact absurd (Conn.trans hs (Conn.step g hf)) hd
            · exact absurd (Conn.trans hd ((Conn.step g hf).symm)) hs
          have hmemg : g ∈ F ∪ A.erase m := hmem g hg
          rw [Finset.mem_union] at hmemg
          have hgA : g ∈ A.erase m := hmemg.resolve_left hgF
          have hlv : leaves G F (G.src m) g := by
            rcases hcr with ⟨hs, hd⟩ | ⟨hs, hd⟩
            · exact Or.inl ⟨hs, hd⟩
            · exact Or.inr ⟨hs, hd⟩
          exact (Finset.mem_erase.mp hgA).1
            (wOrd_antisymm (hph.2 m hm g (hAB' (Finset.mem_of_mem_erase hgA)) hlv)
              (hgt g (Finset.mem_of_mem_erase hgA))).symm
        have hEq : (F ∪ A : Finset E) = insert m (F ∪ A.erase m) := by
          ext x
          rw [Finset.mem_union, Finset.mem_insert, Finset.mem_union, Finset.mem_erase]
          by_cases hx : x = m
          · subst hx
            simp [hm]
          · simp [hx]
        rw [hEq]
        refine IsForest.insert (ih (A.erase m)
          (by rw [Finset.card_erase_of_mem hm, hcard]; omega)
          (fun e he => hAB' (Finset.mem_of_mem_erase he)) (hph.erase m)) ?_ hconn
        intro he
        exact hopen (he ▸ Conn.refl (G.src m))
  exact key A.card A rfl hAB hph

/-- **One ambient phase halves the instance component count** — `compCountOn_halves` with the
choice rule restricted to `B`. -/
theorem compCountOn_halves_in {B : Finset E} {P : Finset V} {F A : Finset E} (hAB : A ⊆ B)
    (hF : IsForest G F) (hP : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P)
    (hph : BorPhaseIn G B F A)
    (hPA : ∀ e ∈ A, G.src e ∈ P ∧ G.dst e ∈ P)
    (hcover : ∀ C ∈ P.image (compOn G P F),
      ∃ e ∈ A, compOn G P F (G.src e) = C ∨ compOn G P F (G.dst e) = C) :
    2 * compCountOn G P (F ∪ A) ≤ compCountOn G P F :=
  compCountOn_halves_of hF (boruvka_forest_in hAB hF hph)
    (Finset.disjoint_left.mpr (fun e heF heA => hph.not_mem heA heF))
    hP (fun e he => by
      rcases Finset.mem_union.mp he with h | h
      · exact hP e h
      · exact hPA e h) hcover

/-- `k` ambient phases divide the instance component count by `2^k`. -/
theorem compCountOn_pow_halves_in (K : ℕ) (B : Finset E) (P : Finset V) (F A : ℕ → Finset E)
    (hAB : ∀ i, A i ⊆ B)
    (hF0 : IsForest G (F 0)) (hP0 : ∀ e ∈ F 0, G.src e ∈ P ∧ G.dst e ∈ P)
    (hstep : ∀ i, F (i + 1) = F i ∪ A i)
    (hph : ∀ i, i < K → BorPhaseIn G B (F i) (A i))
    (hPA : ∀ i, i < K → ∀ e ∈ A i, G.src e ∈ P ∧ G.dst e ∈ P)
    (hcover : ∀ i, i < K → ∀ C ∈ P.image (compOn G P (F i)),
      ∃ e ∈ A i, compOn G P (F i) (G.src e) = C ∨ compOn G P (F i) (G.dst e) = C)
    {k : ℕ} (hk : k ≤ K) :
    2 ^ k * compCountOn G P (F k) ≤ compCountOn G P (F 0) := by
  have hforest : ∀ i, i ≤ K → IsForest G (F i) := by
    intro i hi
    induction i with
    | zero => exact hF0
    | succ n ih =>
        exact (hstep n).symm ▸
          boruvka_forest_in (hAB n) (ih (Nat.le_of_succ_le hi)) (hph n (Nat.lt_of_succ_le hi))
  have hPall : ∀ i, i ≤ K → ∀ e ∈ F i, G.src e ∈ P ∧ G.dst e ∈ P := by
    intro i hi
    induction i with
    | zero => exact hP0
    | succ n ih =>
        have hn : n ≤ K := Nat.le_of_succ_le hi
        intro e he
        rcases Finset.mem_union.mp ((hstep n).symm ▸ he : e ∈ F n ∪ A n) with h | h
        · exact ih hn e h
        · exact hPA n (Nat.lt_of_succ_le hi) e h
  have chain : ∀ i, i < K → 2 * compCountOn G P (F (i + 1)) ≤ compCountOn G P (F i) := by
    intro i hi
    rw [hstep i]
    exact compCountOn_halves_in (hAB i) (hforest i (Nat.le_of_lt hi)) (hPall i (Nat.le_of_lt hi))
      (hph i hi) (hPA i hi) (hcover i hi)
  exact pow_two_mul_le_of_le (fun i => compCountOn G P (F i)) K chain hk

/-- Instance `hn` slot with the ambient choice rule: from the empty forest, `k ≤ K` phases leave at
most `|P| / 2^k` components. -/
theorem compCountOn_le_div_pow_in (K : ℕ) (B : Finset E) (P : Finset V) (F A : ℕ → Finset E) (k : ℕ)
    (hAB : ∀ i, A i ⊆ B) (hF0 : F 0 = ∅)
    (hstep : ∀ i, F (i + 1) = F i ∪ A i)
    (hph : ∀ i, i < K → BorPhaseIn G B (F i) (A i))
    (hPA : ∀ i, i < K → ∀ e ∈ A i, G.src e ∈ P ∧ G.dst e ∈ P)
    (hcover : ∀ i, i < K → ∀ C ∈ P.image (compOn G P (F i)),
      ∃ e ∈ A i, compOn G P (F i) (G.src e) = C ∨ compOn G P (F i) (G.dst e) = C)
    (hk : k ≤ K) :
    compCountOn G P (F k) ≤ P.card / 2 ^ k := by
  have hpow := compCountOn_pow_halves_in K B P F A hAB (by rw [hF0]; exact IsForest.empty)
    (by rw [hF0]; simp) hstep hph hPA hcover hk
  have h1 : compCountOn G P (F k) * 2 ^ k ≤ P.card := by
    rw [Nat.mul_comm]
    exact le_trans hpow (by rw [hF0, compCountOn_empty])
  exact (Nat.le_div_iff_mul_le (pow_pos (by norm_num) k)).mpr h1

/-- Real form of `compCountOn_le_div_pow_in`. -/
theorem compCountOn_le_real_in (K : ℕ) (B : Finset E) (P : Finset V) (F A : ℕ → Finset E) (k : ℕ)
    (hAB : ∀ i, A i ⊆ B) (hF0 : F 0 = ∅)
    (hstep : ∀ i, F (i + 1) = F i ∪ A i)
    (hph : ∀ i, i < K → BorPhaseIn G B (F i) (A i))
    (hPA : ∀ i, i < K → ∀ e ∈ A i, G.src e ∈ P ∧ G.dst e ∈ P)
    (hcover : ∀ i, i < K → ∀ C ∈ P.image (compOn G P (F i)),
      ∃ e ∈ A i, compOn G P (F i) (G.src e) = C ∨ compOn G P (F i) (G.dst e) = C)
    (hk : k ≤ K) :
    (compCountOn G P (F k) : ℝ) ≤ (P.card : ℝ) / (2 : ℝ) ^ k := by
  have hnat := compCountOn_le_div_pow_in K B P F A k hAB hF0 hstep hph hPA hcover hk
  have h1 : compCountOn G P (F k) * 2 ^ k ≤ P.card :=
    (Nat.le_div_iff_mul_le (pow_pos (by norm_num) k)).mp hnat
  have hcast : (compCountOn G P (F k) : ℝ) * (2 : ℝ) ^ k ≤ (P.card : ℝ) := by
    have h2 : ((compCountOn G P (F k) * 2 ^ k : ℕ) : ℝ) ≤ ((P.card : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h2
    linarith
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- The `hcontract` shape with the ambient choice rule and edge budget `|P| ≤ 2|E_child|`. -/
theorem compCountOn_le_real_in_of_card_le (K : ℕ) (B : Finset E) (P : Finset V) (F A : ℕ → Finset E)
    (k : ℕ) {E₀ : Finset E}
    (hAB : ∀ i, A i ⊆ B) (hF0 : F 0 = ∅)
    (hstep : ∀ i, F (i + 1) = F i ∪ A i)
    (hph : ∀ i, i < K → BorPhaseIn G B (F i) (A i))
    (hPA : ∀ i, i < K → ∀ e ∈ A i, G.src e ∈ P ∧ G.dst e ∈ P)
    (hcover : ∀ i, i < K → ∀ C ∈ P.image (compOn G P (F i)),
      ∃ e ∈ A i, compOn G P (F i) (G.src e) = C ∨ compOn G P (F i) (G.dst e) = C)
    (hk : k ≤ K) (h0 : P.card ≤ 2 * E₀.card) :
    (compCountOn G P (F k) : ℝ) ≤ 2 * (E₀.card : ℝ) / (2 : ℝ) ^ k := by
  have h := compCountOn_le_real_in K B P F A k hAB hF0 hstep hph hPA hcover hk
  have h0' : (P.card : ℝ) ≤ 2 * (E₀.card : ℝ) := by exact_mod_cast h0
  rw [le_div_iff₀ (by positivity)] at h ⊢
  nlinarith

/-! ### The witness form of the choice rule (Definition 2.8) -/

/-- `BorPhaseInAt G B F A`: open edges, each with its **own** witness component — some `v` that the
edge leaves, inside which it is `wOrd`-least among the `B`-edges leaving.  This is
`BoruvkaPhase.BorPhaseAt` with the ambient set `B`; it is the shape `boruvkaPhase` is produced in,
and unlike `BorPhaseIn` it does not force the witness to be `G.src e`. -/
def BorPhaseInAt (G : WGraph V E) (B F A : Finset E) : Prop :=
  (∀ e ∈ A, ¬ Conn G F (G.src e) (G.dst e)) ∧
    (∀ e ∈ A, ∃ v, leaves G F v e ∧ ∀ f ∈ B, leaves G F v f → wOrd G e f)

/-- The tail form is the witness form with `v = G.src e`. -/
theorem BorPhaseIn.toAt {B F A : Finset E} (hph : BorPhaseIn G B F A) :
    BorPhaseInAt G B F A :=
  ⟨hph.1, fun e he =>
    ⟨G.src e, Or.inl ⟨Conn.refl (G.src e), hph.1 e he⟩,
      fun f hf hl => hph.2 e he f hf hl⟩⟩

protected theorem BorPhaseInAt.erase {B F A : Finset E} (hph : BorPhaseInAt G B F A) (a : E) :
    BorPhaseInAt G B F (A.erase a) :=
  ⟨fun e he => hph.1 e (Finset.mem_of_mem_erase he),
    fun e he => hph.2 e (Finset.mem_of_mem_erase he)⟩

/-- A witness-form phase edge is never already in the forest. -/
theorem BorPhaseInAt.not_mem {B F A : Finset E} (hph : BorPhaseInAt G B F A) {e : E}
    (he : e ∈ A) : e ∉ F :=
  not_mem_of_not_conn (hph.1 e he)

/-- A witness-form phase edge is not a loop. -/
theorem BorPhaseInAt.nloop {B F A : Finset E} (hph : BorPhaseInAt G B F A) {e : E}
    (he : e ∈ A) : G.src e ≠ G.dst e :=
  fun h => hph.1 e he (by rw [h]; exact Conn.refl (G.dst e))

/-- **A witness-form ambient phase keeps a forest.**  The heaviest edge `m` has a witness `v`; a
closing cycle would cross the cut of `v`'s component in an edge `g`, which `m`'s minimality rule and
the maximality of `m` force to coincide with `m`.  The path is traversed in whichever orientation
starts inside `v`'s component. -/
theorem boruvka_forest_in_at {B F A : Finset E} (hAB : A ⊆ B) (hF : IsForest G F)
    (hph : BorPhaseInAt G B F A) : IsForest G (F ∪ A) := by
  classical
  have key : ∀ (n : ℕ) (A : Finset E), A.card = n → A ⊆ B →
      BorPhaseInAt G B F A → IsForest G (F ∪ A) := by
    intro n
    induction n with
    | zero =>
        intro A hcard _ _
        rw [Finset.card_eq_zero.mp hcard, Finset.union_empty]
        exact hF
    | succ n ih =>
        intro A hcard hAB' hph
        have hne : A.Nonempty := by
          refine Finset.ne_empty_iff_nonempty.mp ?_
          intro h
          rw [h, Finset.card_empty] at hcard
          omega
        obtain ⟨m, hm, hgt⟩ := exists_wOrd_max (G := G) A hne
        obtain ⟨v, hlv, hmin⟩ := hph.2 m hm
        have hopen : ¬ Conn G F (G.src m) (G.dst m) := hph.1 m hm
        have key_step : ∀ (es : List E) (g : E), g ∈ es → (∀ x ∈ es, x ∈ F ∪ A.erase m) →
            ((G.src g ∈ {x | Conn G F v x} ∧ G.dst g ∉ {x | Conn G F v x}) ∨
              (G.src g ∉ {x | Conn G F v x} ∧ G.dst g ∈ {x | Conn G F v x})) → False := by
          intro es g hg hmem hcr
          have hlv' : leaves G F v g := by
            rcases hcr with ⟨hs, hd⟩ | ⟨hs, hd⟩
            · exact Or.inl ⟨hs, hd⟩
            · exact Or.inr ⟨hs, hd⟩
          have hgF : g ∉ F := by
            intro hf
            rcases hcr with ⟨hs, hd⟩ | ⟨hs, hd⟩
            · exact hd (Conn.trans hs (Conn.step g hf))
            · exact hs (Conn.trans hd ((Conn.step g hf).symm))
          have hmemg : g ∈ F ∪ A.erase m := hmem g hg
          rw [Finset.mem_union] at hmemg
          have hgA : g ∈ A.erase m := hmemg.resolve_left hgF
          exact (Finset.mem_erase.mp hgA).1
            (wOrd_antisymm (hmin g (hAB' (Finset.mem_of_mem_erase hgA)) hlv')
              (hgt g (Finset.mem_of_mem_erase hgA))).symm
        have hconn : ¬ Conn G (F ∪ A.erase m) (G.src m) (G.dst m) := by
          intro hc
          rcases hlv with ⟨hs, hd⟩ | ⟨hs, hd⟩
          · obtain ⟨es, pes, hmem⟩ := path_of_conn hc
            obtain ⟨g, hg, hcr⟩ := crossing pes {x | Conn G F v x} hs hd
            exact key_step es g hg hmem hcr
          · obtain ⟨es, pes, hmem⟩ := path_of_conn hc.symm
            obtain ⟨g, hg, hcr⟩ := crossing pes {x | Conn G F v x} hd hs
            exact key_step es g hg hmem hcr
        have hEq : (F ∪ A : Finset E) = insert m (F ∪ A.erase m) := by
          ext x
          rw [Finset.mem_union, Finset.mem_insert, Finset.mem_union, Finset.mem_erase]
          by_cases hx : x = m
          · subst hx
            simp [hm]
          · simp [hx]
        rw [hEq]
        refine IsForest.insert (ih (A.erase m)
          (by rw [Finset.card_erase_of_mem hm, hcard]; omega)
          (fun e he => hAB' (Finset.mem_of_mem_erase he)) (hph.erase m)) ?_ hconn
        intro he
        exact hopen (he ▸ Conn.refl (G.src m))
  exact key A.card A rfl hAB hph

/-- One witness-form ambient phase halves the instance component count. -/
theorem compCountOn_halves_in_at {B : Finset E} {P : Finset V} {F A : Finset E} (hAB : A ⊆ B)
    (hF : IsForest G F) (hP : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P)
    (hph : BorPhaseInAt G B F A)
    (hPA : ∀ e ∈ A, G.src e ∈ P ∧ G.dst e ∈ P)
    (hcover : ∀ C ∈ P.image (compOn G P F),
      ∃ e ∈ A, compOn G P F (G.src e) = C ∨ compOn G P F (G.dst e) = C) :
    2 * compCountOn G P (F ∪ A) ≤ compCountOn G P F :=
  compCountOn_halves_of hF (boruvka_forest_in_at hAB hF hph)
    (Finset.disjoint_left.mpr (fun e heF heA => hph.not_mem heA heF))
    hP (fun e he => by
      rcases Finset.mem_union.mp he with h | h
      · exact hP e h
      · exact hPA e h) hcover

/-- `k` witness-form ambient phases divide the instance component count by `2^k`. -/
theorem compCountOn_pow_halves_in_at (K : ℕ) (B : Finset E) (P : Finset V)
    (F A : ℕ → Finset E)
    (hAB : ∀ i, A i ⊆ B)
    (hF0 : IsForest G (F 0)) (hP0 : ∀ e ∈ F 0, G.src e ∈ P ∧ G.dst e ∈ P)
    (hstep : ∀ i, F (i + 1) = F i ∪ A i)
    (hph : ∀ i, i < K → BorPhaseInAt G B (F i) (A i))
    (hPA : ∀ i, i < K → ∀ e ∈ A i, G.src e ∈ P ∧ G.dst e ∈ P)
    (hcover : ∀ i, i < K → ∀ C ∈ P.image (compOn G P (F i)),
      ∃ e ∈ A i, compOn G P (F i) (G.src e) = C ∨ compOn G P (F i) (G.dst e) = C)
    {k : ℕ} (hk : k ≤ K) :
    2 ^ k * compCountOn G P (F k) ≤ compCountOn G P (F 0) := by
  have hforest : ∀ i, i ≤ K → IsForest G (F i) := by
    intro i hi
    induction i with
    | zero => exact hF0
    | succ n ih =>
        exact (hstep n).symm ▸
          boruvka_forest_in_at (hAB n) (ih (Nat.le_of_succ_le hi)) (hph n (Nat.lt_of_succ_le hi))
  have hPall : ∀ i, i ≤ K → ∀ e ∈ F i, G.src e ∈ P ∧ G.dst e ∈ P := by
    intro i hi
    induction i with
    | zero => exact hP0
    | succ n ih =>
        have hn : n ≤ K := Nat.le_of_succ_le hi
        intro e he
        rcases Finset.mem_union.mp ((hstep n).symm ▸ he : e ∈ F n ∪ A n) with h | h
        · exact ih hn e h
        · exact hPA n (Nat.lt_of_succ_le hi) e h
  have chain : ∀ i, i < K → 2 * compCountOn G P (F (i + 1)) ≤ compCountOn G P (F i) := by
    intro i hi
    rw [hstep i]
    exact compCountOn_halves_in_at (hAB i) (hforest i (Nat.le_of_lt hi))
      (hPall i (Nat.le_of_lt hi)) (hph i hi) (hPA i hi) (hcover i hi)
  exact pow_two_mul_le_of_le (fun i => compCountOn G P (F i)) K chain hk

/-- Instance `hn` slot with the witness-form choice rule: `k ≤ K` phases from the empty forest leave
at most `|P| / 2^k` components. -/
theorem compCountOn_le_real_in_at (K : ℕ) (B : Finset E) (P : Finset V)
    (F A : ℕ → Finset E) (k : ℕ)
    (hAB : ∀ i, A i ⊆ B) (hF0 : F 0 = ∅)
    (hstep : ∀ i, F (i + 1) = F i ∪ A i)
    (hph : ∀ i, i < K → BorPhaseInAt G B (F i) (A i))
    (hPA : ∀ i, i < K → ∀ e ∈ A i, G.src e ∈ P ∧ G.dst e ∈ P)
    (hcover : ∀ i, i < K → ∀ C ∈ P.image (compOn G P (F i)),
      ∃ e ∈ A i, compOn G P (F i) (G.src e) = C ∨ compOn G P (F i) (G.dst e) = C)
    (hk : k ≤ K) :
    (compCountOn G P (F k) : ℝ) ≤ (P.card : ℝ) / (2 : ℝ) ^ k := by
  have hpow := compCountOn_pow_halves_in_at K B P F A hAB (by rw [hF0]; exact IsForest.empty)
    (by rw [hF0]; simp) hstep hph hPA hcover hk
  have h1 : compCountOn G P (F k) * 2 ^ k ≤ P.card := by
    rw [Nat.mul_comm]
    exact le_trans hpow (by rw [hF0, compCountOn_empty])
  have hnat : compCountOn G P (F k) ≤ P.card / 2 ^ k :=
    (Nat.le_div_iff_mul_le (pow_pos (by norm_num) k)).mpr h1
  have h2 : compCountOn G P (F k) * 2 ^ k ≤ P.card :=
    (Nat.le_div_iff_mul_le (pow_pos (by norm_num) k)).mp hnat
  have hcast : (compCountOn G P (F k) : ℝ) * (2 : ℝ) ^ k ≤ (P.card : ℝ) := by
    have h3 : ((compCountOn G P (F k) * 2 ^ k : ℕ) : ℝ) ≤ ((P.card : ℕ) : ℝ) := by
      exact_mod_cast h2
    push_cast at h3
    linarith
  rw [le_div_iff₀ (by positivity)]
  linarith

/-! ### The concrete instance phase: the least `B`-edge of each component -/

/-- `phaseIn G B F`: the edges of `B` that are the `wOrd`-lightest `B`-edge leaving their own
component.  Stated as a filter rather than as the image of a choice function — `wOrd` is total and
antisymmetric, so each component's minimum is unique — mirroring `BoruvkaPhase.boruvkaPhase` with
the candidate set cut down to `B`. -/
noncomputable def phaseIn (G : WGraph V E) (B F : Finset E) : Finset E :=
  B.filter (fun e => ∃ v, leaves G F v e ∧ ∀ f ∈ B, leaves G F v f → wOrd G e f)

theorem mem_phaseIn {B F : Finset E} {e : E} :
    e ∈ phaseIn G B F ↔
      e ∈ B ∧ ∃ v, leaves G F v e ∧ ∀ f ∈ B, leaves G F v f → wOrd G e f := by
  classical
  unfold phaseIn
  rw [Finset.mem_filter]

theorem phaseIn_subset (B F : Finset E) : phaseIn G B F ⊆ B :=
  Finset.filter_subset _ _

/-- The concrete phase satisfies Definition 2.8's witness rule against `B`. -/
theorem phaseIn_borPhaseInAt (B F : Finset E) : BorPhaseInAt G B F (phaseIn G B F) := by
  refine ⟨fun e he => ?_, fun e he => (mem_phaseIn.mp he).2⟩
  obtain ⟨-, v, hlv, -⟩ := mem_phaseIn.mp he
  exact not_conn_of_leaves hlv

/-- **The concrete phase covers every instance component.**  A component that has a `B`-edge
leaving it picks that edge's `wOrd`-least competitor, and one of the two sides of the picked edge
lies in the component, which is what `compCountOn_halves_of` counts. -/
theorem phaseIn_cover {B : Finset E} {P : Finset V} {F : Finset E}
    (hact : ∀ v ∈ P, ∃ e ∈ B, leaves G F v e) :
    ∀ C ∈ P.image (compOn G P F),
      ∃ e ∈ phaseIn G B F,
        compOn G P F (G.src e) = C ∨ compOn G P F (G.dst e) = C := by
  intro C hC
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨e, heB, hlv⟩ := hact v hv
  have hne : (B.filter (fun e => leaves G F v e)).Nonempty :=
    ⟨e, Finset.mem_filter.mpr ⟨heB, hlv⟩⟩
  obtain ⟨m, hm, hmin⟩ := exists_wOrd_min (G := G) _ hne
  have hmB : m ∈ B := (Finset.mem_filter.mp hm).1
  have hlm : leaves G F v m := (Finset.mem_filter.mp hm).2
  refine ⟨m, mem_phaseIn.mpr ⟨hmB, v, hlm,
    fun f hf hlf => hmin f (Finset.mem_filter.mpr ⟨hf, hlf⟩)⟩, ?_⟩
  rcases hlm with ⟨hs, -⟩ | ⟨-, hd⟩
  · exact Or.inl (compOn_congr hs).symm
  · exact Or.inr (compOn_congr hd).symm

/-- **The concrete instance phase halves the instance component count.**  All hypotheses are about
the data of one call: `F` a forest inside `P`, `B` an edge set inside `P`, and every component
meeting `P` having a `B`-edge to leave by. -/
theorem compCountOn_halves_phaseIn {B : Finset E} {P : Finset V} {F : Finset E}
    (hF : IsForest G F) (hP : ∀ e ∈ F, G.src e ∈ P ∧ G.dst e ∈ P)
    (hPB : ∀ e ∈ B, G.src e ∈ P ∧ G.dst e ∈ P)
    (hact : ∀ v ∈ P, ∃ e ∈ B, leaves G F v e) :
    2 * compCountOn G P (F ∪ phaseIn G B F) ≤ compCountOn G P F :=
  compCountOn_halves_in_at (phaseIn_subset B F) hF hP (phaseIn_borPhaseInAt B F)
    (fun e he => hPB e (phaseIn_subset B F he)) (phaseIn_cover hact)

/-- **The paper's phase run on an instance.**  With the concrete phase `phaseIn`, a `k`-step run
from the empty forest keeps the instance component count at most `|P| / 2^k`; every hypothesis is
about the instance's own data. -/
theorem compCountOn_le_real_phaseIn (K : ℕ) (B : Finset E) (P : Finset V) (F : ℕ → Finset E)
    (k : ℕ) (hF0 : F 0 = ∅)
    (hstep : ∀ i, F (i + 1) = F i ∪ phaseIn G B (F i))
    (hPB : ∀ e ∈ B, G.src e ∈ P ∧ G.dst e ∈ P)
    (hact : ∀ i, i < K → ∀ v ∈ P, ∃ e ∈ B, leaves G (F i) v e)
    (hk : k ≤ K) :
    (compCountOn G P (F k) : ℝ) ≤ (P.card : ℝ) / (2 : ℝ) ^ k :=
  compCountOn_le_real_in_at K B P F (fun i => phaseIn G B (F i)) k
    (fun i => phaseIn_subset B (F i)) hF0 hstep
    (fun i _ => phaseIn_borPhaseInAt B (F i))
    (fun i _ e he => hPB e (phaseIn_subset B (F i) he))
    (fun i hi => phaseIn_cover (hact i hi)) hk

/-- The same run with the child's edge budget folded in: `|P| ≤ 2|E₀|` gives the `hcontract`
shape `2|E₀| / 2^k`. -/
theorem compCountOn_le_real_phaseIn_of_card_le (K : ℕ) (B : Finset E) (P : Finset V)
    (F : ℕ → Finset E) (k : ℕ) {E₀ : Finset E} (hF0 : F 0 = ∅)
    (hstep : ∀ i, F (i + 1) = F i ∪ phaseIn G B (F i))
    (hPB : ∀ e ∈ B, G.src e ∈ P ∧ G.dst e ∈ P)
    (hact : ∀ i, i < K → ∀ v ∈ P, ∃ e ∈ B, leaves G (F i) v e)
    (hk : k ≤ K) (h0 : P.card ≤ 2 * E₀.card) :
    (compCountOn G P (F k) : ℝ) ≤ 2 * (E₀.card : ℝ) / (2 : ℝ) ^ k := by
  have h := compCountOn_le_real_phaseIn K B P F k hF0 hstep hPB hact hk
  have h0' : (P.card : ℝ) ≤ 2 * (E₀.card : ℝ) := by exact_mod_cast h0
  rw [le_div_iff₀ (by positivity)] at h ⊢
  nlinarith

/-- **`hcontract` for the concrete instance phase.**  A child vertex set with one vertex per
remaining component (`hsep`), whose edge budget carries the parent's vertex count, satisfies
`|Q| ≤ 2|E_child|/2^{2j}` — the hypothesis `Strategy.cost_linear_of_contraction` consumes, now with
the phase count and the phase itself produced by the instance's own edge budget `B`. -/
theorem hcontract_of_phaseIn (K : ℕ) (B : Finset E) (P : Finset V) (F : ℕ → Finset E) {j : ℕ}
    {Q : Finset V} {Echild : Finset E} (hQ : Q ⊆ P)
    (hsep : ∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → ¬ Conn G (F (2 * j)) u v)
    (hF0 : F 0 = ∅)
    (hstep : ∀ i, F (i + 1) = F i ∪ phaseIn G B (F i))
    (hPB : ∀ e ∈ B, G.src e ∈ P ∧ G.dst e ∈ P)
    (hact : ∀ i, i < K → ∀ v ∈ P, ∃ e ∈ B, leaves G (F i) v e)
    (hjK : 2 * j ≤ K) (h0 : P.card ≤ 2 * Echild.card) :
    (Q.card : ℝ) ≤ 2 * (Echild.card : ℝ) / (2 : ℝ) ^ (2 * j) := by
  have h1 : (Q.card : ℝ) ≤ (compCountOn G P (F (2 * j)) : ℝ) := by
    exact_mod_cast card_le_compCountOn_of_pairwise_not_conn hQ hsep
  have h2 : (compCountOn G P (F (2 * j)) : ℝ) ≤ (P.card : ℝ) / (2 : ℝ) ^ (2 * j) :=
    compCountOn_le_real_phaseIn K B P F (2 * j) hF0 hstep hPB hact hjK
  have h0' : (P.card : ℝ) ≤ 2 * (Echild.card : ℝ) := by exact_mod_cast h0
  have hc : (Q.card : ℝ) * (2 : ℝ) ^ (2 * j)
      ≤ (compCountOn G P (F (2 * j)) : ℝ) * (2 : ℝ) ^ (2 * j) :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  rw [le_div_iff₀ (by positivity)] at h2 ⊢
  linarith

end DLMST
