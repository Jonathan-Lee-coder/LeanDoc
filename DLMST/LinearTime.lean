/-
# What "linear" means for this formalization

The paper's §4 recursion is analysed here in a **counting model**: one "unit of work" is one level's
vertex visit plus one level's edge scan, i.e.

  `levelWork j = |V_j| + |E_j|`,   `totalWork d = Σ_{j<d} levelWork j`.

No machine, word size, data structure or primitive-operation cost is involved, and no executable
program is produced.  So everything below is a statement about **how many items are touched**, not
about runtime.

Two bounds are proved:

* `counting_log_stop` — unconditional in the stopping form: with activation only above the stopping
  depth `D = log₄|P| + 1`, the recursion touches at most `(4/3)·|P| + 3·D·|E₀|` items.  This is
  `O((n+m) log n)`.
* `counting_linear_of_display` — the paper's own route, in counting form: the §3.6 display
  `Σ|kidE| ≤ ρm + C√(m·n′)` plus the phase-halving bound `n′ ≤ 2m/2^{2j}` makes any workload with
  the per-call recurrence `W m ≤ Σ W(children) + c·m` linear, `W m = O(m)`.  It is a direct
  instantiation of `CertificateBuild.linear_of_display`; no per-level edge halving enters, and the
  display itself is discharged from RoundData by `Assembly.sum_kidE_le_paper_bound`.

The per-level edge account of §4 is *not* halving: `hshr_refuted` below gives an 8-vertex,
17-edge instance on which it fails at `j = 0` (`2·9 > 17`).  Hence the `log` in `counting_log_stop`
is not an artefact of the proof, and no edge-halving conditional is kept anywhere in the library:
within this recursion the edge account really is `d·m` in the worst case, and linearity comes from
§3.6's sparsification, which is a different model from the tower.
-/
import DLMST.StopWitness
import DLMST.LevelSize

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]

namespace DLMST

open Classical

/-! ## The counting measure, bounded activation -/

/-- **The measure with activation only above the stopping depth.**  Same proof as
`four_pow_mul_lvlVerts_le`, but the activation hypothesis is needed only for levels `< D`. -/
theorem four_pow_mul_lvlVerts_le_bd {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (_hP : 0 < P.card) (D : ℕ)
    (hact : ∀ (d i : ℕ), d < D → i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e) :
    ∀ d : ℕ, d ≤ D → 4 ^ d * (lvlVerts G P E₀ d).card ≤ P.card := by
  intro d
  induction d with
  | zero => intro _; simp [lvlVerts, lvlData]
  | succ n ih =>
      intro hd
      have hnD : n < D := Nat.lt_of_succ_le hd
      have h4 : 4 * (lvlVerts G P E₀ (n + 1)).card ≤ (lvlVerts G P E₀ n).card := by
        rw [lvlVerts_succ_chain]
        exact four_mul_repSet_card_le (G := lvlGraph G P E₀ n) (P := lvlVerts G P E₀ n) 2
          (by norm_num) (lvlE G P E₀ n) (phaseChain (lvlGraph G P E₀ n) (lvlE G P E₀ n))
          rfl (fun i => rfl) (lvl_hPE hPE n) (fun i hi => hact n i hnD hi)
      calc 4 ^ (n + 1) * (lvlVerts G P E₀ (n + 1)).card
          = 4 ^ n * (4 * (lvlVerts G P E₀ (n + 1)).card) := by
            rw [pow_succ]; ring
        _ ≤ 4 ^ n * (lvlVerts G P E₀ n).card := Nat.mul_le_mul_left _ h4
        _ ≤ P.card := ih (Nat.le_of_succ_le hd)

/-- Geometric vertex account, with activation only above the stopping depth. -/
theorem three_mul_sum_lvlVerts_le_bd {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (D : ℕ)
    (hact : ∀ (d i : ℕ), d < D → i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e) :
    ∀ d : ℕ, d ≤ D →
      3 * (Finset.sum (Finset.range d) (fun j => (lvlVerts G P E₀ j).card)) +
          4 * (lvlVerts G P E₀ d).card ≤ 4 * P.card := by
  intro d
  induction d with
  | zero => intro _; simp [lvlVerts, lvlData]
  | succ n ih =>
      intro hd
      have hnD : n < D := Nat.lt_of_succ_le hd
      have hstep : 4 * (lvlVerts G P E₀ (n + 1)).card ≤ (lvlVerts G P E₀ n).card := by
        rw [lvlVerts_succ_chain]
        exact four_mul_repSet_card_le (G := lvlGraph G P E₀ n) (P := lvlVerts G P E₀ n) 2
          (by norm_num) (lvlE G P E₀ n) (phaseChain (lvlGraph G P E₀ n) (lvlE G P E₀ n))
          rfl (fun i => rfl) (lvl_hPE hPE n) (fun i hi => hact n i hnD hi)
      rw [Finset.sum_range_succ]
      omega

/-- Total items touched by the recursion down to depth `d`. -/
noncomputable def totalWork {G : WGraph V E} (P : Finset V) (E₀ : Finset E) (d : ℕ) : ℕ :=
  Finset.sum (Finset.range d) (fun j => levelWork (G := G) P E₀ j)

/-- **The unconditional counting bound** in the stopping form: vertex visits decay geometrically,
edge scans only repeat the instance's edges `d` times. -/
theorem tower_work_le_bd {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (D : ℕ)
    (hact : ∀ (d i : ℕ), d < D → i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    {d : ℕ} (hd : d ≤ D) :
    3 * totalWork (G := G) P E₀ d ≤ 4 * P.card + 3 * (d * E₀.card) := by
  have hV := three_mul_sum_lvlVerts_le_bd (G := G) (P := P) (E₀ := E₀) hPE D hact d hd
  have hV' : 3 * Finset.sum (Finset.range d) (fun j => (lvlVerts G P E₀ j).card) ≤ 4 * P.card := by
    omega
  have hE : Finset.sum (Finset.range d) (fun j => (lvlE G P E₀ j).card) ≤ d * E₀.card :=
    sum_lvlE_le (G := G) (P := P) (E₀ := E₀) d
  have hsplit : totalWork (G := G) P E₀ d
      = Finset.sum (Finset.range d) (fun j => (lvlVerts G P E₀ j).card)
        + Finset.sum (Finset.range d) (fun j => (lvlE G P E₀ j).card) := by
    simp only [totalWork, levelWork, Finset.sum_add_distrib]
  rw [hsplit]
  have hE3 : 3 * Finset.sum (Finset.range d) (fun j => (lvlE G P E₀ j).card) ≤ 3 * (d * E₀.card) :=
    Nat.mul_le_mul_left 3 hE
  omega

/-- The stopping depth chosen by the measure: `log₄|P| + 1`. -/
noncomputable def stopDepth (P : Finset V) : ℕ := Nat.log 4 P.card + 1

/-- **The counting statement at the self-chosen depth** — this is the precise meaning of
"linear-time skeleton" in this development: `(4/3)·|P| + 3·(log₄|P|+1)·|E₀|` item touches. -/
theorem counting_log_stop {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hact : ∀ (d i : ℕ), d < stopDepth P → i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e) :
    3 * totalWork (G := G) P E₀ (stopDepth P) ≤
      4 * P.card + 3 * (stopDepth P * E₀.card) :=
  tower_work_le_bd hPE (stopDepth P) hact le_rfl

/-- **The satisfiable §4 display package.**  `contractDisplay` bundles MSF + the weight telescope +
`3|answer| ≤ 4|P|` + the per-level `1/4` shrink, but its unbounded activation is inconsistent
(boundary B3), so it is vacuous.  This is the stopping counterpart: activation only above `D`, the
bottom level collapsed to `≤ 1` vertex (`hstop`), and the conclusions that survive are the honest
ones — the answer is an MSF of the instance (`tower_msf_of_stop`), its weight is the sum of the
levels' forests (`tower_wsum`, unconditional), it is a forest so `|answer| ≤ |P| − 1`
(`tower_msf_of_stop_card`; this supersedes the `4/3` budget), every level above the stop shrinks
vertices by `4`, and the counting work is `3·totalWork ≤ 4|P| + 3D|E₀|` (`tower_work_le_bd`). -/
theorem tower_stop_display {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card) (D : ℕ)
    (hact : ∀ (d i : ℕ), d < D → i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (hstop : (lvlVerts G P E₀ D).card ≤ 1) :
    IsMSFOf G E₀ (answer G P E₀ D ∅) ∧
      wsum G (answer G P E₀ D ∅) =
        Finset.sum (Finset.range D) (fun j => wsum G (lvlForest G P E₀ j)) ∧
      (answer G P E₀ D ∅).card ≤ P.card - 1 ∧
      (∀ j, j < D → 4 * (lvlVerts G P E₀ (j + 1)).card ≤ (lvlVerts G P E₀ j).card) ∧
      3 * totalWork (G := G) P E₀ D ≤ 4 * P.card + 3 * (D * E₀.card) :=
  ⟨tower_msf_of_stop hPE hP D hact hstop,
    by
      rw [tower_wsum (G := G) (P := P) (E₀ := E₀) D ∅ (Finset.empty_subset _)]
      simp [wsum],
    tower_msf_of_stop_card hPE hP D hact hstop,
    fun j hj => by
      rw [lvlVerts_succ_chain]
      exact four_mul_repSet_card_le (G := lvlGraph G P E₀ j) (P := lvlVerts G P E₀ j) 2
        (by norm_num) (lvlE G P E₀ j) (phaseChain (lvlGraph G P E₀ j) (lvlE G P E₀ j))
        rfl (fun i => rfl) (lvl_hPE hPE j) (fun i hi => hact j i hj hi),
    tower_work_le_bd hPE D hact le_rfl⟩

/-! ## The paper's linear route: §3.6 display + phase halving

The tower rescans `E₀` at every level, so its own account is `d·m` (the previous section shows no
edge halving can rescue it).  The paper instead recurses on *sparsified* children: the §3.6 display
bounds the total child edges by `ρm + C√(m·n′)`, and `k = 2j` Borůvka phases shrink
`n′ ≤ 2m/2^{2j}`.  That pair is exactly a certificate, and any workload obeying the per-call
recurrence becomes linear.  Below is that route in counting form. -/

section PaperRoute

/-- **Counting form of the paper's linearity.**  A workload `W` over instance sizes with the
per-call recurrence `W m ≤ Σ W(children) + c·m` is linear, provided the children satisfy the §3.6
display `Σ|kidE| ≤ ρm + C√(m·n′)` (`hdisplay`, discharged from RoundData by
`Assembly.sum_kidE_le_paper_bound`) and the phase-halving bound `n′ ≤ 2m/2^{2j}` (`hn`, the
Borůvka phase count).  No per-level edge halving is used.  (If a call's actual work is `|P|+|E₀|`
rather than `c·m`, fold the `|P| ≤ 2|E₀|` factor into `c`.) -/
theorem counting_linear_of_display {C ρ : ℝ} {j : ℕ} (hC : 0 ≤ C) (hρ : ρ ≤ 1 / 8)
    (hj : C * 2 / (2 : ℝ) ^ j ≤ 3 / 8)
    (subSizes : ℕ → List ℕ) (nsub : ℕ → ℕ)
    (hdisplay : ∀ m : ℕ, ((subSizes m).sum : ℝ) ≤
      ρ * (m : ℝ) + C * Real.sqrt ((m : ℝ) * (nsub m : ℝ)))
    (hn : ∀ m : ℕ, (nsub m : ℝ) ≤ 2 * (m : ℝ) / (2 : ℝ) ^ (2 * j))
    (W : ℕ → ℕ) (c : ℝ) (hc : 0 ≤ c) (hW0 : W 0 = 0)
    (hrec : ∀ m : ℕ, (W m : ℝ) ≤ ((subSizes m).map (fun i => (W i : ℝ))).sum + c * m) :
    ∃ c' : ℝ, 0 ≤ c' ∧ ∀ m : ℕ, (W m : ℝ) ≤ c' * m :=
  linear_of_display hC hρ hj subSizes nsub hdisplay hn (fun m => (W m : ℝ)) c hc
    (by simp [hW0]) hrec

end PaperRoute

/-- **The stopping interface without a separate collapse hypothesis.**  At the self-chosen depth,
bounded activation alone forces `|lvlVerts D| ≤ 1`, so `mst_main_stop`'s `hstop` is redundant. -/
theorem mst_main_stop_log {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), d < stopDepth P → i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e) :
    ∃ F : Finset E, IsMSFOf G E₀ F ∧ F.card ≤ P.card - 1 := by
  have h4 := four_pow_mul_lvlVerts_le_bd (G := G) (P := P) (E₀ := E₀) hPE hP (stopDepth P) hact
    (stopDepth P) le_rfl
  have hpow : 0 < 4 ^ stopDepth P := Nat.pow_pos (by norm_num)
  have hle : 4 ^ stopDepth P * (lvlVerts G P E₀ (stopDepth P)).card ≤ 4 ^ stopDepth P * 1 := by
    calc 4 ^ stopDepth P * (lvlVerts G P E₀ (stopDepth P)).card ≤ P.card := h4
      _ ≤ 4 ^ stopDepth P := card_le_pow_log P.card
      _ = 4 ^ stopDepth P * 1 := (Nat.mul_one _).symm
  have hstop : (lvlVerts G P E₀ (stopDepth P)).card ≤ 1 :=
    Nat.le_of_mul_le_mul_left hle hpow
  exact ⟨answer G P E₀ (stopDepth P) ∅,
    tower_msf_of_stop hPE hP (stopDepth P) hact hstop,
    tower_msf_of_stop_card hPE hP (stopDepth P) hact hstop⟩

/-! ## Edge halving fails for the contraction recursion

Eight vertices in four pairs; the four matching edges have indices `0…3`, four "intra-super"
edges `4…7`, and nine "cross-super" edges `8…16`.  All weights are equal, so `wOrd` is just the
edge index order.  The first phase can only keep edges `≤ 3` (each vertex's lightest incident edge
is its matching edge), and the second phase can only keep edges `≤ 7` (each vertex has an intra
edge leaving its pair).  So the two-phase forest lies in `{0,…,7}`, and none of the nine cross
edges is connected by it.  The child's edge set therefore has at least nine edges, while the root
has seventeen: `2·9 > 17`.

This is why no edge-halving conditional is kept: the `log` factor in `counting_log_stop` is real
for this recursion, and linearity has to come from §3.6's display route above. -/

section Refutation

/-- The 8-vertex, 17-edge counterexample.  Indices `0–3`: matching; `4–7`: inside a super-half;
`8–16`: across the two super-halves. -/
def G8 : WGraph (Fin 8) (Fin 17) where
  endpoints e :=
    match (e : ℕ) with
    | 0 => (0, 1)
    | 1 => (2, 3)
    | 2 => (4, 5)
    | 3 => (6, 7)
    | 4 => (0, 2)
    | 5 => (1, 3)
    | 6 => (4, 6)
    | 7 => (5, 7)
    | 8 => (0, 4)
    | 9 => (1, 5)
    | 10 => (2, 6)
    | 11 => (3, 7)
    | 12 => (0, 5)
    | 13 => (1, 4)
    | 14 => (2, 7)
    | 15 => (3, 6)
    | _ => (0, 6)
  weight _ := 0

/-- The matching edge of a vertex (index `v/2`). -/
def matchE (v : Fin 8) : Fin 17 := ⟨v.val / 2, by have := v.isLt; omega⟩

/-- An edge joining the two pairs of `v`'s super-half (one of `4…7`). -/
def intraE (v : Fin 8) : Fin 17 :=
  ⟨4 + 2 * (v.val / 4) + v.val % 2, by have := v.isLt; omega⟩

/-- The super-half label. -/
def half (v : Fin 8) : Bool := decide (v.val < 4)

/-- The pair label. -/
def pairC (v : Fin 8) : ℕ := v.val / 2

/-- With all weights equal, the total order on edges is just the index order. -/
theorem wOrd_G8 {a b : Fin 17} : wOrd G8 a b ↔ a ≤ b := by
  simp [wOrd, G8]

/-- Each vertex's matching edge leaves the empty forest. -/
theorem leaves_matchE (v : Fin 8) : leaves G8 (∅ : Finset (Fin 17)) v (matchE v) := by
  fin_cases v <;> simp [leaves, conn_empty_iff, G8, matchE] <;> decide

theorem src_intra : ∀ v : Fin 8, G8.src (intraE v) = v ∨ G8.dst (intraE v) = v := by
  decide

/-- Matching edges keep the pair label. -/
theorem pairC_match : ∀ e : Fin 17, e.val ≤ 3 → pairC (G8.src e) = pairC (G8.dst e) := by
  decide

/-- Edges `0…7` keep the super-half label. -/
theorem half_match : ∀ e : Fin 17, e.val ≤ 7 → half (G8.src e) = half (G8.dst e) := by
  decide

/-- Cross-super edges change the super-half label. -/
theorem half_cross : ∀ e : Fin 17, 8 ≤ e.val → half (G8.src e) ≠ half (G8.dst e) := by
  decide

theorem conn_pairC {F : Finset (Fin 17)}
    (hF : ∀ e ∈ F, pairC (G8.src e) = pairC (G8.dst e)) {u v : Fin 8}
    (h : Conn G8 F u v) : pairC u = pairC v := by
  induction h with
  | refl => rfl
  | step e he => exact hF e he
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem conn_half {F : Finset (Fin 17)}
    (hF : ∀ e ∈ F, half (G8.src e) = half (G8.dst e)) {u v : Fin 8}
    (h : Conn G8 F u v) : half u = half v := by
  induction h with
  | refl => rfl
  | step e he => exact hF e he
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- Phase one only keeps matching edges: the matching edge is the `wOrd`-least edge leaving every
vertex of the empty forest. -/
theorem F1_subset {e : Fin 17}
    (he : e ∈ phaseIn G8 (Finset.univ : Finset (Fin 17)) (∅ : Finset (Fin 17))) :
    e.val ≤ 3 := by
  obtain ⟨-, v, -, hmin⟩ := mem_phaseIn.mp he
  have h := hmin (matchE v) (Finset.mem_univ _) (leaves_matchE v)
  have hle := (Fin.le_iff_val_le_val).mp (wOrd_G8.mp h)
  have hm : (matchE v).val = v.val / 2 := rfl
  omega

theorem phaseChain1_G8 :
    phaseChain G8 (Finset.univ : Finset (Fin 17)) 1
      = phaseIn G8 (Finset.univ : Finset (Fin 17)) (∅ : Finset (Fin 17)) := by
  show phaseChain G8 Finset.univ 0 ∪ phaseIn G8 Finset.univ (phaseChain G8 Finset.univ 0) = _
  rw [show phaseChain G8 (Finset.univ : Finset (Fin 17)) 0 = ∅ from rfl]
  simp

/-- The intra edge `intraE v` leaves the pair of `v` inside phase one: pairs are preserved by
matching edges, and `intraE` changes the pair label. -/
theorem not_conn_intra (v : Fin 8) :
    ¬ Conn G8 (phaseIn G8 (Finset.univ : Finset (Fin 17)) (∅ : Finset (Fin 17)))
      (G8.src (intraE v)) (G8.dst (intraE v)) := by
  intro h
  have hc := conn_pairC (fun e he => pairC_match e (F1_subset he)) h
  fin_cases v <;> exact absurd hc (by decide)

theorem leaves_of_endpoints {F : Finset (Fin 17)} {e : Fin 17} {v : Fin 8}
    (h : G8.src e = v ∨ G8.dst e = v) (hnc : ¬ Conn G8 F (G8.src e) (G8.dst e)) :
    leaves G8 F v e := by
  rcases h with h | h
  · subst h
    exact Or.inl ⟨Conn.refl _, hnc⟩
  · subst h
    exact Or.inr ⟨fun hc => hnc hc.symm, Conn.refl _⟩

theorem leaves_intra (v : Fin 8) :
    leaves G8 (phaseIn G8 (Finset.univ : Finset (Fin 17)) (∅ : Finset (Fin 17))) v (intraE v) :=
  leaves_of_endpoints (src_intra v) (not_conn_intra v)

/-- Phase two only keeps edges `0…7`, because every vertex has an intra edge leaving its pair. -/
theorem F2_le {e : Fin 17}
    (he : e ∈ phaseIn G8 (Finset.univ : Finset (Fin 17))
      (phaseIn G8 (Finset.univ : Finset (Fin 17)) (∅ : Finset (Fin 17)))) :
    e.val ≤ 7 := by
  obtain ⟨-, v, -, hmin⟩ := mem_phaseIn.mp he
  have h := hmin (intraE v) (Finset.mem_univ _) (leaves_intra v)
  have hle := (Fin.le_iff_val_le_val).mp (wOrd_G8.mp h)
  have hm : (intraE v).val = 4 + 2 * (v.val / 4) + v.val % 2 := rfl
  have hv : v.val ≤ 7 := by have := v.isLt; omega
  omega

theorem phaseChain_two_le {e : Fin 17}
    (he : e ∈ phaseChain G8 (Finset.univ : Finset (Fin 17)) 2) : e.val ≤ 7 := by
  rw [show phaseChain G8 (Finset.univ : Finset (Fin 17)) 2
      = phaseChain G8 Finset.univ 1 ∪ phaseIn G8 Finset.univ (phaseChain G8 Finset.univ 1)
      from rfl, phaseChain1_G8] at he
  rcases Finset.mem_union.mp he with he | he
  · exact le_trans (F1_subset he) (by norm_num)
  · exact F2_le he

theorem phaseChain_two_half {e : Fin 17}
    (he : e ∈ phaseChain G8 (Finset.univ : Finset (Fin 17)) 2) :
    half (G8.src e) = half (G8.dst e) :=
  half_match e (phaseChain_two_le he)

/-- No cross-super edge is connected by the two-phase forest. -/
theorem cross_not_conn {e : Fin 17} (he : 8 ≤ e.val) :
    ¬ Conn G8 (phaseChain G8 (Finset.univ : Finset (Fin 17)) 2) (G8.src e) (G8.dst e) := by
  intro h
  exact half_cross e he (conn_half (fun f hf => phaseChain_two_half hf) h)

/-- The child's edge set has at least the nine cross-super edges. -/
theorem crossE_card_ge :
    9 ≤ (crossE G8 (phaseChain G8 (Finset.univ : Finset (Fin 17)) 2)
      (Finset.univ : Finset (Fin 17))).card := by
  have hsub : (Finset.univ : Finset (Fin 17)).filter (fun e => 8 ≤ e.val)
      ⊆ crossE G8 (phaseChain G8 Finset.univ 2) Finset.univ := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    simp only [crossE, Finset.mem_filter, Finset.mem_univ, true_and]
    exact cross_not_conn he
  have hc : ((Finset.univ : Finset (Fin 17)).filter (fun e => 8 ≤ e.val)).card = 9 := by
    decide
  calc 9 = ((Finset.univ : Finset (Fin 17)).filter (fun e => 8 ≤ e.val)).card := hc.symm
    _ ≤ _ := Finset.card_le_card hsub

theorem lvlE0_G8 :
    lvlE G8 (Finset.univ : Finset (Fin 8)) (Finset.univ : Finset (Fin 17)) 0
      = Finset.univ := rfl

theorem lvlE1_G8 :
    lvlE G8 (Finset.univ : Finset (Fin 8)) (Finset.univ : Finset (Fin 17)) 1
      = crossE G8 (phaseChain G8 (Finset.univ : Finset (Fin 17)) 2) Finset.univ := by
  rw [lvlE_succ]
  rfl

/-- The edge account fails to halve from level `0` to level `1`: `2·9 ≤ 17` is false. -/
theorem not_halving_zero :
    ¬ 2 * (lvlE G8 (Finset.univ : Finset (Fin 8)) (Finset.univ : Finset (Fin 17)) 1).card
      ≤ (lvlE G8 (Finset.univ : Finset (Fin 8)) (Finset.univ : Finset (Fin 17)) 0).card := by
  intro h0
  have h1 : 9 ≤ (lvlE G8 (Finset.univ : Finset (Fin 8))
      (Finset.univ : Finset (Fin 17)) 1).card := by
    rw [lvlE1_G8]
    exact crossE_card_ge
  have h0c : (lvlE G8 (Finset.univ : Finset (Fin 8))
      (Finset.univ : Finset (Fin 17)) 0).card = 17 := by
    rw [lvlE0_G8]
    decide
  omega

/-- **Edge halving is not a theorem of the contraction recursion.** -/
theorem hshr_refuted :
    ¬ ∀ j : ℕ,
      2 * (lvlE G8 (Finset.univ : Finset (Fin 8)) (Finset.univ : Finset (Fin 17))
        (j + 1)).card
        ≤ (lvlE G8 (Finset.univ : Finset (Fin 8)) (Finset.univ : Finset (Fin 17)) j).card := by
  intro h
  exact not_halving_zero (by simpa using h 0)

/-- The same failure at the stopping depth: no edge-halving statement can hold on this instance,
not even one bounded to the depth the recursion actually uses. -/
theorem hshr_refuted_stop :
    ¬ ∀ j : ℕ, j < stopDepth (Finset.univ : Finset (Fin 8)) →
      2 * (lvlE G8 (Finset.univ : Finset (Fin 8)) (Finset.univ : Finset (Fin 17))
        (j + 1)).card
        ≤ (lvlE G8 (Finset.univ : Finset (Fin 8)) (Finset.univ : Finset (Fin 17)) j).card := by
  intro h
  exact not_halving_zero (by simpa using h 0 (by simp [stopDepth]))

end Refutation

/-! ## The stopping display package is non-vacuous

`tower_stop_display` is only useful if its hypotheses are met somewhere.  The four-vertex witness of
`StopWitness` meets them with `D = 1`, and instantiating gives all five conjuncts. -/

section DisplayWitness

/-- **`tower_stop_display` instantiated on `G4`**: the package (MSF, weight telescope, forest
cardinality, per-level `1/4` shrink, counting work) is satisfiable, not just vacuously true. -/
theorem stop_display_witness :
    IsMSFOf G4 (Finset.univ : Finset (Fin 3)) ({0, 1, 2} : Finset (Fin 3)) ∧
      wsum G4 (answer G4 (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 3)) 1 ∅) =
        Finset.sum (Finset.range 1)
          (fun j => wsum G4 (lvlForest G4 (Finset.univ : Finset (Fin 4))
            (Finset.univ : Finset (Fin 3)) j)) ∧
      (answer G4 (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 3)) 1 ∅).card ≤
        (Finset.univ : Finset (Fin 4)).card - 1 ∧
      (∀ j, j < 1 →
        4 * (lvlVerts G4 (Finset.univ : Finset (Fin 4))
          (Finset.univ : Finset (Fin 3)) (j + 1)).card ≤
          (lvlVerts G4 (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 3)) j).card) ∧
      3 * totalWork (G := G4) (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 3)) 1 ≤
        4 * (Finset.univ : Finset (Fin 4)).card +
          3 * (1 * (Finset.univ : Finset (Fin 3)).card) := by
  have h := tower_stop_display (G := G4) (P := Finset.univ) (E₀ := Finset.univ)
    stop_hPE stop_hP 1 stop_hact stop_hstop
  exact ⟨stop_witness_value, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- The same package **evaluated**: the answer is the tree `{0, 1, 2}` of weight `4`, the collapse
leaves one vertex, and the recursion touches `7` items in total. -/
theorem stop_display_witness_values :
    wsum G4 (answer G4 (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 3)) 1 ∅) = 4 ∧
      (answer G4 (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 3)) 1 ∅).card = 3 ∧
      (lvlVerts G4 (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 3)) 1).card = 1 ∧
      totalWork (G := G4) (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 3)) 1 = 7 := by
  have hcard : (lvlVerts G4 (Finset.univ : Finset (Fin 4))
      (Finset.univ : Finset (Fin 3)) 1).card = 1 := by
    have h1 : lvlVerts G4 (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 3)) 1
        = repSet G4 (Finset.univ : Finset (Fin 4))
            (phaseChain G4 (Finset.univ : Finset (Fin 3)) 2) := rfl
    rw [h1, repSet_card, phaseChain_two, compCount_final]
  refine ⟨?_, ?_, hcard, ?_⟩
  · rw [stop_witness_answer, wsum]
    simp [G4]
    norm_num
  · rw [stop_witness_answer]
    decide
  · rw [totalWork, Finset.sum_range_one, levelWork]
    decide

end DisplayWitness

end DLMST
