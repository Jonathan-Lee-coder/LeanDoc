/-
# A concretely evaluated instance for the stopping interface

The hypotheses of `mst_main_stop` are satisfiable.  The smallest interesting witness has four
vertices and three edges

  `0 --1-- 1 --2-- 2 --1-- 3`      (edges `0`, `2`, `1` with weights `1`, `2`, `1`)

so that the first phase contracts each of the pairs `{0,1}`, `{2,3}`, and the second phase picks
the single cross edge `2`, leaving one representative.  The stopping depth is `D = 1`, and the
answer `{0, 1, 2}` is the instance's MSF.  This file checks every step (`phaseChain`, the
activation data, the collapse, and the final `IsMSFOf`) by evaluation; it is the non-vacuity
witness for §4's stopping form.
-/
import DLMST.Main

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]

namespace DLMST

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- The four-vertex, three-edge instance. -/
def G4 : WGraph (Fin 4) (Fin 3) where
  endpoints e := if (e : ℕ) = 0 then (0, 1) else if (e : ℕ) = 1 then (2, 3) else (1, 2)
  weight e := if (e : ℕ) = 2 then 2 else 1

/-- The pair label: `0` for the pair `{0,1}`, `1` for the pair `{2,3}`. -/
def pairCode (x : Fin 4) : Fin 2 := if (x : ℕ) < 2 then 0 else 1

@[simp] theorem G4_src0 : G4.src (0 : Fin 3) = 0 := by decide
@[simp] theorem G4_src1 : G4.src (1 : Fin 3) = 2 := by decide
@[simp] theorem G4_src2 : G4.src (2 : Fin 3) = 1 := by decide
@[simp] theorem G4_dst0 : G4.dst (0 : Fin 3) = 1 := by decide
@[simp] theorem G4_dst1 : G4.dst (1 : Fin 3) = 3 := by decide
@[simp] theorem G4_dst2 : G4.dst (2 : Fin 3) = 2 := by decide
@[simp] theorem G4_w0 : G4.weight (0 : Fin 3) = 1 := by norm_num [G4]
@[simp] theorem G4_w1 : G4.weight (1 : Fin 3) = 1 := by norm_num [G4]
@[simp] theorem G4_w2 : G4.weight (2 : Fin 3) = 2 := by norm_num [G4]

/-- Empty-forest connectivity is equality. -/
theorem conn_empty_iff {G : WGraph V E} {u v : V} :
    Conn G (∅ : Finset E) u v ↔ u = v :=
  ⟨fun h => (conn_empty h).symm, fun h => h ▸ Conn.refl u⟩

/-- A candidate that is constant on every edge of `F` is constant on `F`-paths. -/
theorem conn_color {G : WGraph V E} {F : Finset E} {c : V → Bool}
    (hc : ∀ e ∈ F, c (G.src e) = c (G.dst e)) {u v : V} (h : Conn G F u v) : c u = c v := by
  induction h with
  | refl => rfl
  | step e he => exact hc e he
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## The two phases -/

/-- Phase one on the four-vertex instance keeps exactly the two light interior edges. -/
theorem phaseIn_one :
    phaseIn G4 (Finset.univ : Finset (Fin 3)) (∅ : Finset (Fin 3)) = {0, 1} := by
  ext e
  constructor
  · intro he
    rw [mem_phaseIn] at he
    obtain ⟨-, v, hlv, hmin⟩ := he
    fin_cases e
    · decide
    · decide
    · fin_cases v
      · simp [leaves, conn_empty_iff] at hlv
      · simp [leaves, conn_empty_iff] at hlv
        have h0 : leaves G4 (∅ : Finset (Fin 3)) 1 (0 : Fin 3) := by
          simp [leaves, conn_empty_iff]
        have := hmin 0 (Finset.mem_univ _) h0
        simp [wOrd] at this
      · simp [leaves, conn_empty_iff] at hlv
        have h1 : leaves G4 (∅ : Finset (Fin 3)) 2 (1 : Fin 3) := by
          simp [leaves, conn_empty_iff]
        have := hmin 1 (Finset.mem_univ _) h1
        simp [wOrd] at this
      · simp [leaves, conn_empty_iff] at hlv
  · intro he
    fin_cases e
    · exact mem_phaseIn.mpr ⟨Finset.mem_univ _, 0, by simp [leaves, conn_empty_iff],
        by intro f _ hf; fin_cases f <;> simp_all [leaves, conn_empty_iff, wOrd]⟩
    · exact mem_phaseIn.mpr ⟨Finset.mem_univ _, 2, by simp [leaves, conn_empty_iff],
        by intro f _ hf; fin_cases f <;> simp_all [leaves, conn_empty_iff, wOrd]⟩
    · exact absurd he (by decide)

/-- Inside `{0, 1}` the only connected pairs are the two-element pairs, so paths are detected by
the pair label. -/
theorem conn_pair_iff (u v : Fin 4) :
    Conn G4 ({0, 1} : Finset (Fin 3)) u v ↔ pairCode u = pairCode v := by
  constructor
  · intro h
    have hc' := conn_color (G := G4) (F := ({0, 1} : Finset (Fin 3)))
      (c := fun x => decide ((x : ℕ) < 2)) ?_ h
    · by_cases hu : (u : ℕ) < 2 <;> by_cases hv : (v : ℕ) < 2 <;>
        simp [pairCode, hu, hv] at hc' ⊢
    · intro f hf
      fin_cases f <;> simp_all
  · intro h
    fin_cases u <;> fin_cases v <;> simp_all [pairCode] <;>
      first
        | exact Conn.refl _
        | exact Conn.step 0 (by decide)
        | exact Conn.step 1 (by decide)
        | exact Conn.symm (Conn.step 0 (by decide))
        | exact Conn.symm (Conn.step 1 (by decide))

/-- Phase two picks the single cross edge. -/
theorem phaseIn_two :
    phaseIn G4 (Finset.univ : Finset (Fin 3)) ({0, 1} : Finset (Fin 3)) = {2} := by
  ext e
  constructor
  · intro he
    rw [mem_phaseIn] at he
    obtain ⟨-, v, hlv, hmin⟩ := he
    fin_cases e
    · fin_cases v <;> simp [leaves, conn_pair_iff, pairCode] at hlv
    · fin_cases v <;> simp [leaves, conn_pair_iff, pairCode] at hlv
    · decide
  · intro he
    fin_cases e
    · exact absurd he (by decide)
    · exact absurd he (by decide)
    · exact mem_phaseIn.mpr ⟨Finset.mem_univ _, 1, by simp [leaves, conn_pair_iff, pairCode],
        by intro f _ hf; fin_cases f <;> simp_all [leaves, conn_pair_iff, wOrd, pairCode]⟩

/-- The chain after two phases. -/
theorem phaseChain_one : phaseChain G4 (Finset.univ : Finset (Fin 3)) 1 = {0, 1} := by
  show phaseChain G4 Finset.univ 0 ∪ phaseIn G4 Finset.univ (phaseChain G4 Finset.univ 0) = _
  rw [show phaseChain G4 (Finset.univ : Finset (Fin 3)) 0 = ∅ from rfl, phaseIn_one]
  simp

theorem phaseChain_two : phaseChain G4 (Finset.univ : Finset (Fin 3)) 2 = {0, 1, 2} := by
  show phaseChain G4 Finset.univ 1 ∪ phaseIn G4 Finset.univ (phaseChain G4 Finset.univ 1) = _
  rw [phaseChain_one, phaseIn_two]
  decide

/-! ## The collapse -/

/-- After two phases the whole instance is connected: `0 - 1 - 2 - 3`. -/
@[simp] theorem conn_final (u v : Fin 4) :
    Conn G4 ({0, 1, 2} : Finset (Fin 3)) u v := by
  have e01 : Conn G4 ({0, 1, 2} : Finset (Fin 3)) 0 1 := Conn.step 0 (by decide)
  have e12 : Conn G4 ({0, 1, 2} : Finset (Fin 3)) 1 2 := Conn.step 2 (by decide)
  have e23 : Conn G4 ({0, 1, 2} : Finset (Fin 3)) 2 3 := Conn.step 1 (by decide)
  have e02 : Conn G4 ({0, 1, 2} : Finset (Fin 3)) 0 2 := e01.trans e12
  have e03 : Conn G4 ({0, 1, 2} : Finset (Fin 3)) 0 3 := e02.trans e23
  have e13 : Conn G4 ({0, 1, 2} : Finset (Fin 3)) 1 3 := e12.trans e23
  fin_cases u <;> fin_cases v <;>
    first
      | exact Conn.refl _
      | exact e01 | exact e02 | exact e03
      | exact e12 | exact e13 | exact e23
      | exact e01.symm | exact e02.symm | exact e03.symm
      | exact e12.symm | exact e13.symm | exact e23.symm

/-- Every instance component is the whole vertex set. -/
theorem compOn_final (v : Fin 4) :
    compOn G4 (Finset.univ : Finset (Fin 4)) ({0, 1, 2} : Finset (Fin 3)) v = Finset.univ := by
  ext x
  simp [mem_compOn]

theorem compCount_final :
    compCountOn G4 (Finset.univ : Finset (Fin 4)) ({0, 1, 2} : Finset (Fin 3)) = 1 := by
  rw [compCountOn]
  have h : (Finset.univ : Finset (Fin 4)).image
      (compOn G4 (Finset.univ : Finset (Fin 4)) ({0, 1, 2} : Finset (Fin 3)))
      = {Finset.univ} := by
    ext S
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨v, rfl⟩
      exact compOn_final v
    · intro hS
      subst hS
      exact ⟨0, compOn_final 0⟩
  rw [h]
  simp

/-! ## The stopping interface -/

theorem stop_hPE : ∀ e ∈ (Finset.univ : Finset (Fin 3)),
    G4.src e ∈ (Finset.univ : Finset (Fin 4)) ∧ G4.dst e ∈ (Finset.univ : Finset (Fin 4)) :=
  fun e _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩

theorem stop_hP : 0 < (Finset.univ : Finset (Fin 4)).card := by decide

theorem stop_hstop :
    (lvlVerts G4 (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 3)) 1).card ≤ 1 := by
  have h1 : lvlVerts G4 (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 3)) 1
      = repSet G4 (Finset.univ : Finset (Fin 4))
          (phaseChain G4 (Finset.univ : Finset (Fin 3)) 2) := rfl
  rw [h1, repSet_card, phaseChain_two, compCount_final]

/-- Both phases are active at the (only) level above the stopping depth. -/
theorem stop_hact : ∀ (d i : ℕ), d < 1 → i < 2 →
    ∀ v ∈ lvlVerts G4 (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 3)) d,
      ∃ e ∈ lvlE G4 (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 3)) d,
        leaves (lvlGraph G4 (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 3)) d)
          (phaseChain (lvlGraph G4 (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 3)) d)
            (lvlE G4 (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 3)) d) i) v e := by
  intro d i hd hi v hv
  have hd0 : d = 0 := by omega
  subst hd0
  have hi' : i = 0 ∨ i = 1 := by omega
  change v ∈ (Finset.univ : Finset (Fin 4)) at hv
  change ∃ e ∈ (Finset.univ : Finset (Fin 3)),
    leaves G4 (phaseChain G4 (Finset.univ : Finset (Fin 3)) i) v e
  rcases hi' with rfl | rfl
  · rw [show phaseChain G4 (Finset.univ : Finset (Fin 3)) 0 = ∅ from rfl]
    fin_cases v
    · exact ⟨0, Finset.mem_univ _, by simp [leaves, conn_empty_iff]⟩
    · exact ⟨0, Finset.mem_univ _, by simp [leaves, conn_empty_iff]⟩
    · exact ⟨1, Finset.mem_univ _, by simp [leaves, conn_empty_iff]⟩
    · exact ⟨1, Finset.mem_univ _, by simp [leaves, conn_empty_iff]⟩
  · rw [phaseChain_one]
    fin_cases v
    · exact ⟨2, Finset.mem_univ _, by simp [leaves, conn_pair_iff, pairCode]⟩
    · exact ⟨2, Finset.mem_univ _, by simp [leaves, conn_pair_iff, pairCode]⟩
    · exact ⟨2, Finset.mem_univ _, by simp [leaves, conn_pair_iff, pairCode]⟩
    · exact ⟨2, Finset.mem_univ _, by simp [leaves, conn_pair_iff, pairCode]⟩

/-- The answer at the stopping depth is the three-edge tree. -/
theorem stop_witness_answer :
    answer G4 (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 3)) 1 ∅
      = ({0, 1, 2} : Finset (Fin 3)) := by
  show lvlForest G4 (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 3)) 0 ∪ ∅ = _
  rw [show lvlForest G4 (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 3)) 0
      = phaseChain G4 (Finset.univ : Finset (Fin 3)) 2 from rfl, phaseChain_two]
  simp

/-- **The instance's answer is an MSF**: the concrete value `{0, 1, 2}`. -/
theorem stop_witness_value :
    IsMSFOf G4 (Finset.univ : Finset (Fin 3)) ({0, 1, 2} : Finset (Fin 3)) := by
  have h := tower_msf_of_stop (G := G4) (P := Finset.univ) (E₀ := Finset.univ)
    stop_hPE stop_hP 1 stop_hact stop_hstop
  rwa [stop_witness_answer] at h

/-- **Non-vacuity of `mst_main_stop`**: the four-vertex instance satisfies the stopping interface,
and the interface's conclusion holds with the concrete forest. -/
theorem stop_witness :
    ∃ F : Finset (Fin 3), IsMSFOf G4 (Finset.univ : Finset (Fin 3)) F
      ∧ F.card ≤ (Finset.univ : Finset (Fin 4)).card - 1 :=
  mst_main_stop G4 (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 3)) 1
    stop_hPE stop_hP stop_hact stop_hstop

end DLMST