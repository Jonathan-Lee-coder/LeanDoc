/-
# The §4 recursion as a strategy

`Procedure.lean`'s `CallOut`/`Strategy` are the §3 interface: a call records `P` and `E₀` as
computed data, and `Strategy.Wf` says the returned call answers the instance it was asked about.
The §4 contraction recursion cannot fill a `CallOut`: the cross edges it hands to the child are
unsupported (`crossE_subset_unsupp`), so `CallOut.hUkid` fails.  The child's other option — an
empty child — would drop the cross edges, which is not §4.

So the contraction recursion gets its own call record, `ContractOut`, shaped by §4.  Its instance
is *stored*, not computed: `contractOut` sets the `P` and `E₀` fields to whatever was asked, so
the analogue of `Strategy.Wf` holds by `rfl`.  The substantive content is the `isMSF` field — the
spliced answer is an MSF of the stored instance — and `ContractWf` is exactly what transports that
from the stored instance to the queried one (`contractStrategy_answer_isMSF`).

This keeps `Procedure.lean` untouched: the §3.6 display continues to consume `CallOut`, and the
§4 recursion is certified on its own record.
-/
import DLMST.Tower
import DLMST.Procedure

open Classical

namespace DLMST

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [LinearOrder E]

/-! ## The §4 call record -/

/-- One node of the §4 recursion: the level's phase chain, the child's answer on the contracted
instance, and the one-step guarantees.  The instance is stored (`P`, `E₀`), like `CallOut`, so
well-formedness can be stated and proved. -/
structure ContractOut (G : WGraph V E) where
  P : Finset V
  E₀ : Finset E
  F : ℕ → Finset E
  B : Finset {e // e ∈ crossE G (F 2) E₀}
  answer : Finset E
  answer_eq : answer = F 2 ∪ B.image Subtype.val
  hF0 : F 0 = ∅
  hstep : ∀ i, F (i + 1) = F i ∪ phaseIn G E₀ (F i)
  hact : ∀ i, i < 2 → ∀ v ∈ P, ∃ e ∈ E₀, leaves G (F i) v e
  hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P
  hPne : 0 < P.card
  isMSF : IsMSFOf G E₀ answer
  smallV : 4 * (repSet G P (F 2)).card ≤ P.card
  smallE : 4 * B.card ≤ P.card
  weight : wsum G answer = wsum G (F 2) + wsum (cGraph G P (F 2) E₀) B

/-- **The §4 node on a given instance**, built from the level's phases and the child's MSF.  The
stored instance is the queried one by construction. -/
noncomputable def contractOut (G : WGraph V E) (P : Finset V) (E₀ : Finset E)
    (F : ℕ → Finset E) {B : Finset {e // e ∈ crossE G (F 2) E₀}}
    (hF0 : F 0 = ∅) (hstep : ∀ i, F (i + 1) = F i ∪ phaseIn G E₀ (F i))
    (hact : ∀ i, i < 2 → ∀ v ∈ P, ∃ e ∈ E₀, leaves G (F i) v e)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hPne : 0 < P.card)
    (hB : IsMSFOf (cGraph G P (F 2) E₀)
      (Finset.univ : Finset {e // e ∈ crossE G (F 2) E₀}) B) :
    ContractOut G where
  P := P
  E₀ := E₀
  F := F
  B := B
  answer := F 2 ∪ B.image Subtype.val
  answer_eq := rfl
  hF0 := hF0
  hstep := hstep
  hact := hact
  hPE := hPE
  hPne := hPne
  isMSF := (contract_step_sound_and_small'' (G := G) 2 (by norm_num) F hF0 hstep hact hPE
    hB hPne).1
  smallV := (contract_step_sound_and_small'' (G := G) 2 (by norm_num) F hF0 hstep hact hPE
    hB hPne).2.1
  smallE := (contract_step_sound_and_small'' (G := G) 2 (by norm_num) F hF0 hstep hact hPE
    hB hPne).2.2
  weight := wsum_union_image_eq_add_child

/-- The node's stored vertex set is the queried one. -/
theorem contractOut_P (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (F : ℕ → Finset E)
    {B : Finset {e // e ∈ crossE G (F 2) E₀}}
    (hF0 : F 0 = ∅) (hstep : ∀ i, F (i + 1) = F i ∪ phaseIn G E₀ (F i))
    (hact : ∀ i, i < 2 → ∀ v ∈ P, ∃ e ∈ E₀, leaves G (F i) v e)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hPne : 0 < P.card)
    (hB : IsMSFOf (cGraph G P (F 2) E₀)
      (Finset.univ : Finset {e // e ∈ crossE G (F 2) E₀}) B) :
    (contractOut G P E₀ F hF0 hstep hact hPE hPne hB).P = P := rfl

/-- The node's stored edge set is the queried one. -/
theorem contractOut_E₀ (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (F : ℕ → Finset E)
    {B : Finset {e // e ∈ crossE G (F 2) E₀}}
    (hF0 : F 0 = ∅) (hstep : ∀ i, F (i + 1) = F i ∪ phaseIn G E₀ (F i))
    (hact : ∀ i, i < 2 → ∀ v ∈ P, ∃ e ∈ E₀, leaves G (F i) v e)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hPne : 0 < P.card)
    (hB : IsMSFOf (cGraph G P (F 2) E₀)
      (Finset.univ : Finset {e // e ∈ crossE G (F 2) E₀}) B) :
    (contractOut G P E₀ F hF0 hstep hact hPE hPne hB).E₀ = E₀ := rfl

/-! ## The strategy and its well-formedness -/

/-- A strategy over §4 nodes: one node per instance. -/
abbrev ContractStrategy (G : WGraph V E) : Type _ :=
  (P : Finset V) → (E₀ : Finset E) → ContractOut G

/-- **The `Strategy.Wf` analogue**: the node returned for an instance is about that instance. -/
def ContractWf {G : WGraph V E} (S : ContractStrategy G) : Prop :=
  ∀ (P : Finset V) (E₀ : Finset E), (S P E₀).P = P ∧ (S P E₀).E₀ = E₀

/-- **A §4 strategy from per-instance data.**  Each instance supplies its phase chain and a child
MSF; `contractOut` assembles the node. -/
noncomputable def contractStrategy (G : WGraph V E)
    (F : (P : Finset V) → (E₀ : Finset E) → ℕ → Finset E)
    (B : (P : Finset V) → (E₀ : Finset E) →
      Finset {e // e ∈ crossE G (F P E₀ 2) E₀})
    (hF0 : ∀ (P : Finset V) (E₀ : Finset E), F P E₀ 0 = ∅)
    (hstep : ∀ (P : Finset V) (E₀ : Finset E) (i : ℕ),
      F P E₀ (i + 1) = F P E₀ i ∪ phaseIn G E₀ (F P E₀ i))
    (hact : ∀ (P : Finset V) (E₀ : Finset E) (i : ℕ), i < 2 → ∀ v ∈ P,
      ∃ e ∈ E₀, leaves G (F P E₀ i) v e)
    (hPE : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hPne : ∀ (P : Finset V) (_E₀ : Finset E), 0 < P.card)
    (hB : ∀ (P : Finset V) (E₀ : Finset E), IsMSFOf (cGraph G P (F P E₀ 2) E₀)
      (Finset.univ : Finset {e // e ∈ crossE G (F P E₀ 2) E₀}) (B P E₀)) :
    ContractStrategy G :=
  fun P E₀ =>
    contractOut G P E₀ (F P E₀) (hF0 P E₀) (hstep P E₀) (hact P E₀) (hPE P E₀)
      (hPne P E₀) (hB P E₀)

/-- **§4's strategy is well-formed by construction**: the stored instance is the queried one. -/
theorem contractStrategy_wf (G : WGraph V E)
    (F : (P : Finset V) → (E₀ : Finset E) → ℕ → Finset E)
    (B : (P : Finset V) → (E₀ : Finset E) →
      Finset {e // e ∈ crossE G (F P E₀ 2) E₀})
    (hF0 : ∀ (P : Finset V) (E₀ : Finset E), F P E₀ 0 = ∅)
    (hstep : ∀ (P : Finset V) (E₀ : Finset E) (i : ℕ),
      F P E₀ (i + 1) = F P E₀ i ∪ phaseIn G E₀ (F P E₀ i))
    (hact : ∀ (P : Finset V) (E₀ : Finset E) (i : ℕ), i < 2 → ∀ v ∈ P,
      ∃ e ∈ E₀, leaves G (F P E₀ i) v e)
    (hPE : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hPne : ∀ (P : Finset V) (_E₀ : Finset E), 0 < P.card)
    (hB : ∀ (P : Finset V) (E₀ : Finset E), IsMSFOf (cGraph G P (F P E₀ 2) E₀)
      (Finset.univ : Finset {e // e ∈ crossE G (F P E₀ 2) E₀}) (B P E₀)) :
    ContractWf (contractStrategy G F B hF0 hstep hact hPE hPne hB) :=
  fun _ _ => ⟨rfl, rfl⟩

/-- **What well-formedness buys.**  A node's answer is an MSF of the instance it stored; `ContractWf`
transports this to the queried instance. -/
theorem contractStrategy_answer_isMSF {G : WGraph V E} {S : ContractStrategy G}
    (hS : ContractWf S) (P : Finset V) (E₀ : Finset E) :
    IsMSFOf G E₀ (S P E₀).answer := by
  have hO := (S P E₀).isMSF
  rw [(hS P E₀).2] at hO
  exact hO

/-- The vertex budget transports to the queried instance. -/
theorem contractStrategy_smallV {G : WGraph V E} {S : ContractStrategy G}
    (hS : ContractWf S) (P : Finset V) (E₀ : Finset E) :
    4 * (repSet G P ((S P E₀).F 2)).card ≤ P.card := by
  have h := (S P E₀).smallV
  rwa [(hS P E₀).1] at h

/-- The edge budget transports to the queried instance. -/
theorem contractStrategy_smallE {G : WGraph V E} {S : ContractStrategy G}
    (hS : ContractWf S) (P : Finset V) (E₀ : Finset E) :
    4 * (S P E₀).B.card ≤ P.card := by
  have h := (S P E₀).smallE
  rwa [(hS P E₀).1] at h

/-! ## The child's answer, chosen -/

/-- **The §4 strategy with the child's MSF chosen, not assumed.**  `contractStrategy` takes the
child answer `B` as data; here it is picked by `exists_msfof` on the contracted instance, so the
remaining inputs are only the level's phases, the instance geometry and nonemptiness. -/
noncomputable def contractStrategyAuto (G : WGraph V E)
    (F : (P : Finset V) → (E₀ : Finset E) → ℕ → Finset E)
    (hF0 : ∀ (P : Finset V) (E₀ : Finset E), F P E₀ 0 = ∅)
    (hstep : ∀ (P : Finset V) (E₀ : Finset E) (i : ℕ),
      F P E₀ (i + 1) = F P E₀ i ∪ phaseIn G E₀ (F P E₀ i))
    (hact : ∀ (P : Finset V) (E₀ : Finset E) (i : ℕ), i < 2 → ∀ v ∈ P,
      ∃ e ∈ E₀, leaves G (F P E₀ i) v e)
    (hPE : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hPne : ∀ (P : Finset V) (_E₀ : Finset E), 0 < P.card) :
    ContractStrategy G :=
  contractStrategy G F
    (fun P E₀ =>
      Classical.choose (exists_msfof (G := cGraph G P (F P E₀ 2) E₀)
        (Finset.univ : Finset {e // e ∈ crossE G (F P E₀ 2) E₀})))
    hF0 hstep hact hPE hPne
    (fun P E₀ =>
      Classical.choose_spec (exists_msfof (G := cGraph G P (F P E₀ 2) E₀)
        (Finset.univ : Finset {e // e ∈ crossE G (F P E₀ 2) E₀})))

/-- **The chosen-data strategy is well-formed.** -/
theorem contractStrategyAuto_wf (G : WGraph V E)
    (F : (P : Finset V) → (E₀ : Finset E) → ℕ → Finset E)
    (hF0 : ∀ (P : Finset V) (E₀ : Finset E), F P E₀ 0 = ∅)
    (hstep : ∀ (P : Finset V) (E₀ : Finset E) (i : ℕ),
      F P E₀ (i + 1) = F P E₀ i ∪ phaseIn G E₀ (F P E₀ i))
    (hact : ∀ (P : Finset V) (E₀ : Finset E) (i : ℕ), i < 2 → ∀ v ∈ P,
      ∃ e ∈ E₀, leaves G (F P E₀ i) v e)
    (hPE : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hPne : ∀ (P : Finset V) (_E₀ : Finset E), 0 < P.card) :
    ContractWf (contractStrategyAuto G F hF0 hstep hact hPE hPne) :=
  contractStrategy_wf G F _ hF0 hstep hact hPE hPne _

/-- **Every node of the chosen-data strategy answers its instance.** -/
theorem contractStrategyAuto_answer (G : WGraph V E)
    (F : (P : Finset V) → (E₀ : Finset E) → ℕ → Finset E)
    (hF0 : ∀ (P : Finset V) (E₀ : Finset E), F P E₀ 0 = ∅)
    (hstep : ∀ (P : Finset V) (E₀ : Finset E) (i : ℕ),
      F P E₀ (i + 1) = F P E₀ i ∪ phaseIn G E₀ (F P E₀ i))
    (hact : ∀ (P : Finset V) (E₀ : Finset E) (i : ℕ), i < 2 → ∀ v ∈ P,
      ∃ e ∈ E₀, leaves G (F P E₀ i) v e)
    (hPE : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hPne : ∀ (P : Finset V) (_E₀ : Finset E), 0 < P.card)
    (P : Finset V) (E₀ : Finset E) :
    IsMSFOf G E₀ (contractStrategyAuto G F hF0 hstep hact hPE hPne P E₀).answer :=
  contractStrategy_answer_isMSF
    (contractStrategyAuto_wf G F hF0 hstep hact hPE hPne) P E₀

/-! ## Activation derived -/

/-- **The §4 strategy from per-instance connectivity.**  `hact` is gone: an instance whose edge set
connects all of `V` and whose level forests keep at least two components has an outgoing instance
edge at every vertex of the instance. -/
noncomputable def contractStrategyConn (G : WGraph V E)
    (F : (P : Finset V) → (E₀ : Finset E) → ℕ → Finset E)
    (hF0 : ∀ (P : Finset V) (E₀ : Finset E), F P E₀ 0 = ∅)
    (hstep : ∀ (P : Finset V) (E₀ : Finset E) (i : ℕ),
      F P E₀ (i + 1) = F P E₀ i ∪ phaseIn G E₀ (F P E₀ i))
    (hconn : ∀ (_P : Finset V) (E₀ : Finset E), ∀ u w : V, Conn G E₀ u w)
    (hc : ∀ (P : Finset V) (E₀ : Finset E) (i : ℕ), i < 2 → 2 ≤ compCount G (F P E₀ i))
    (hPE : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hPne : ∀ (P : Finset V) (_E₀ : Finset E), 0 < P.card) :
    ContractStrategy G :=
  contractStrategyAuto G F hF0 hstep
    (fun P E₀ i hi =>
      hact_of_conn_E₀ (G := G) 2 (F P E₀) (hconn P E₀) (fun i hi => hc P E₀ i hi) i hi)
    hPE hPne

/-- The connectivity-fed strategy is well-formed. -/
theorem contractStrategyConn_wf (G : WGraph V E)
    (F : (P : Finset V) → (E₀ : Finset E) → ℕ → Finset E)
    (hF0 : ∀ (P : Finset V) (E₀ : Finset E), F P E₀ 0 = ∅)
    (hstep : ∀ (P : Finset V) (E₀ : Finset E) (i : ℕ),
      F P E₀ (i + 1) = F P E₀ i ∪ phaseIn G E₀ (F P E₀ i))
    (hconn : ∀ (_P : Finset V) (E₀ : Finset E), ∀ u w : V, Conn G E₀ u w)
    (hc : ∀ (P : Finset V) (E₀ : Finset E) (i : ℕ), i < 2 → 2 ≤ compCount G (F P E₀ i))
    (hPE : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hPne : ∀ (P : Finset V) (_E₀ : Finset E), 0 < P.card) :
    ContractWf (contractStrategyConn G F hF0 hstep hconn hc hPE hPne) :=
  contractStrategyAuto_wf G F hF0 hstep _ hPE hPne

/-- Every node of the connectivity-fed strategy answers its instance. -/
theorem contractStrategyConn_answer (G : WGraph V E)
    (F : (P : Finset V) → (E₀ : Finset E) → ℕ → Finset E)
    (hF0 : ∀ (P : Finset V) (E₀ : Finset E), F P E₀ 0 = ∅)
    (hstep : ∀ (P : Finset V) (E₀ : Finset E) (i : ℕ),
      F P E₀ (i + 1) = F P E₀ i ∪ phaseIn G E₀ (F P E₀ i))
    (hconn : ∀ (_P : Finset V) (E₀ : Finset E), ∀ u w : V, Conn G E₀ u w)
    (hc : ∀ (P : Finset V) (E₀ : Finset E) (i : ℕ), i < 2 → 2 ≤ compCount G (F P E₀ i))
    (hPE : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hPne : ∀ (P : Finset V) (_E₀ : Finset E), 0 < P.card)
    (P : Finset V) (E₀ : Finset E) :
    IsMSFOf G E₀ (contractStrategyConn G F hF0 hstep hconn hc hPE hPne P E₀).answer :=
  contractStrategy_answer_isMSF
    (contractStrategyConn_wf G F hF0 hstep hconn hc hPE hPne) P E₀

/-! ## The child is the recursion's own output

`contractStrategyAuto` still takes the child's MSF from `exists_msfof` — *some* MSF of the child
instance.  §4 instead calls itself: the child returns its own run's answer.  By `lvlData_shift` the
child instance is level `1` of the tower, and `tower_terminates_child` says the child's own run at
depth `d` (no bottom call) is an MSF of the child instance.  So the child datum is *computed*, and
the node's answer is `lvlForest 0 ∪ childAnswer` by `answer_splice` — "splice the child's own output
onto this level's forest".

This removes the last piece of data the strategy was taking: `contractOutOfTower` has no `B`
argument.  What it needs instead is the depth at which the child finishes, and that bound is
*derived* one level down (`childBd`), so the recursion closes. -/

section TowerChild

/-- Level `0` is the instance itself. -/
theorem lvlForest_zero (G : WGraph V E) (P : Finset V) (E₀ : Finset E) :
    lvlForest G P E₀ 0 = phaseChain G E₀ 2 := rfl

/-- Level `1` is the contraction of the instance, read back on the ambient edge type. -/
theorem lvlGraph_one (G : WGraph V E) (P : Finset V) (E₀ : Finset E) :
    lvlGraph G P E₀ 1 = cGraphFlat G P (phaseChain G E₀ 2) := rfl

/-- The level-`1` vertex set is the child instance's vertex set. -/
theorem lvlVerts_one (G : WGraph V E) (P : Finset V) (E₀ : Finset E) :
    lvlVerts G P E₀ 1 = repSet G P (phaseChain G E₀ 2) := rfl

/-- The level-`1` edge set is the cross edges of the parent's instance. -/
theorem lvlE_one (G : WGraph V E) (P : Finset V) (E₀ : Finset E) :
    lvlE G P E₀ 1 = crossE G (phaseChain G E₀ 2) E₀ := rfl

/-- **The child's own answer at depth `d`**: the level-`1` instance's tower run with no bottom
call.  This is what the §4 recursion receives from its child. -/
noncomputable def childAnswer (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (d : ℕ) :
    Finset E :=
  answer (lvlGraph G P E₀ 1) (lvlVerts G P E₀ 1) (lvlE G P E₀ 1) d ∅

/-- The child's answer as a set of the *parent's* cross edges — the shape a `ContractOut` stores. -/
noncomputable def crossChild (G : WGraph V E) (P : Finset V) (E₀ : Finset E) (d : ℕ) :
    Finset {e // e ∈ crossE G (phaseChain G E₀ 2) E₀} :=
  (childAnswer G P E₀ d).subtype (fun e => e ∈ crossE G (phaseChain G E₀ 2) E₀)

/-- The child's answer lies in the parent's cross edges. -/
theorem childAnswer_subset {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (hd : (lvlVerts G P E₀ 1).card ≤ 4 ^ d) :
    ∀ e ∈ childAnswer G P E₀ d, e ∈ crossE G (phaseChain G E₀ 2) E₀ := by
  intro e he
  have h := (tower_terminates_child (G := G) (P := P) (E₀ := E₀) hPE hP hact d hd).1.2.1 he
  rwa [lvlE_one] at h

/-- The subtype round trip for the child's answer. -/
theorem crossChild_image {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (hd : (lvlVerts G P E₀ 1).card ≤ 4 ^ d) :
    (crossChild G P E₀ d).image Subtype.val = childAnswer G P E₀ d :=
  image_subtype_crossE (G := G) (F := phaseChain G E₀ 2) (E₀ := E₀)
    (B := childAnswer G P E₀ d) (childAnswer_subset hPE hP hact d hd)

/-- **The child's own run is an MSF of the contracted instance** — in the shape `contractOut`
takes for its child datum.  No choice, no hypothesis: the child's tower supplies it. -/
theorem isMSFOf_crossChild {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (hd : (lvlVerts G P E₀ 1).card ≤ 4 ^ d) :
    IsMSFOf (cGraph G P (phaseChain G E₀ 2) E₀)
      (Finset.univ : Finset {e // e ∈ crossE G (phaseChain G E₀ 2) E₀}) (crossChild G P E₀ d) := by
  have hchild := tower_terminates_child (G := G) (P := P) (E₀ := E₀) hPE hP hact d hd
  refine isMSFOf_cGraph_of_flat (G := G) (P := P) (F := phaseChain G E₀ 2) (E₀ := E₀)
    (B := crossChild G P E₀ d) ?_
  rw [crossChild_image hPE hP hact d hd]
  exact hchild

/-- **The §4 node whose child is the recursion's own run.**  No child answer is supplied; the
child's tower at depth `d` provides it.  The node's answer is the level-`0` forest spliced with
the child's answer, i.e. `answer` at depth `d+1`. -/
noncomputable def contractOutOfTower (G : WGraph V E) (P : Finset V) (E₀ : Finset E)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (hd : (lvlVerts G P E₀ 1).card ≤ 4 ^ d) : ContractOut G :=
  contractOut G P E₀ (phaseChain G E₀) rfl (fun _ => rfl) (fun i hi v hv => hact 0 i hi v hv)
    hPE hP (isMSFOf_crossChild hPE hP hact d hd)

/-- **The node's answer is the tower's answer one level deeper.** -/
theorem contractOutOfTower_answer (G : WGraph V E) (P : Finset V) (E₀ : Finset E)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (hd : (lvlVerts G P E₀ 1).card ≤ 4 ^ d) :
    (contractOutOfTower G P E₀ hPE hP hact d hd).answer = answer G P E₀ (d + 1) ∅ := by
  show phaseChain G E₀ 2 ∪ (crossChild G P E₀ d).image Subtype.val
      = answer G P E₀ (d + 1) ∅
  rw [crossChild_image hPE hP hact d hd, answer_splice (G := G) (P := P) (E₀ := E₀) d ∅]
  rfl

/-- **The recursion splice**: the depth-`d+1` node's answer is this level's forest on top of the
child's *own* depth-`d` node — the strategy applied to the child instance. -/
theorem contractOutOfTower_splice (G : WGraph V E) (P : Finset V) (E₀ : Finset E)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (hd : (lvlVerts G P E₀ 1).card ≤ 4 ^ (d + 1))
    (hd' : (lvlVerts (lvlGraph G P E₀ 1) (lvlVerts G P E₀ 1) (lvlE G P E₀ 1) 1).card ≤ 4 ^ d) :
    (contractOutOfTower G P E₀ hPE hP hact (d + 1) hd).answer
      = lvlForest G P E₀ 0 ∪
        (contractOutOfTower (lvlGraph G P E₀ 1) (lvlVerts G P E₀ 1) (lvlE G P E₀ 1)
          (lvl_hPE hPE 1) (lvlVerts_pos hP 1) (hact_shift hact) d hd').answer := by
  rw [contractOutOfTower_answer, contractOutOfTower_answer]
  exact answer_splice (G := G) (P := P) (E₀ := E₀) (d + 1) ∅

/-- **One level of measure charges the child**: `4·|level 2| ≤ |level 1|` — the level step of
`four_pow_mul_lvlVerts_le`, exposed for the termination descent. -/
theorem four_mul_lvlVerts_succ_le {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) : 4 * (lvlVerts G P E₀ (d + 1)).card ≤ (lvlVerts G P E₀ d).card := by
  rw [lvlVerts_succ_chain]
  exact four_mul_repSet_card_le (G := lvlGraph G P E₀ d) (P := lvlVerts G P E₀ d) 2
    (by norm_num) (lvlE G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d))
    rfl (fun i => rfl) (lvl_hPE hPE d) (hact d)

/-- **The child's depth budget, derived**: if the parent's child set is at most `4^(d+1)`, the
child's *own* child set is at most `4^d`.  This is what lets the recursion descend one level. -/
theorem childBd {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (hd : (lvlVerts G P E₀ 1).card ≤ 4 ^ (d + 1)) :
    (lvlVerts (lvlGraph G P E₀ 1) (lvlVerts G P E₀ 1) (lvlE G P E₀ 1) 1).card ≤ 4 ^ d := by
  rw [← lvlVerts_shift]
  have h4 := four_mul_lvlVerts_succ_le (G := G) (P := P) (E₀ := E₀) hPE hact 1
  have h : 4 * (lvlVerts G P E₀ 2).card ≤ 4 * 4 ^ d := by
    calc 4 * (lvlVerts G P E₀ 2).card ≤ (lvlVerts G P E₀ 1).card := h4
      _ ≤ 4 ^ (d + 1) := hd
      _ = 4 * 4 ^ d := by rw [pow_succ]; ring
  exact Nat.le_of_mul_le_mul_left h (by norm_num)

/-- **The §4 recursion, closed**: the depth-`d+1` node's answer is this level's forest spliced with
the child's own depth-`d` node, whose measure bound is derived by `childBd` — nothing about the
child is assumed. -/
theorem contractOutOfTower_rec (G : WGraph V E) (P : Finset V) (E₀ : Finset E)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (hd : (lvlVerts G P E₀ 1).card ≤ 4 ^ (d + 1)) :
    (contractOutOfTower G P E₀ hPE hP hact (d + 1) hd).answer
      = lvlForest G P E₀ 0 ∪
        (contractOutOfTower (lvlGraph G P E₀ 1) (lvlVerts G P E₀ 1) (lvlE G P E₀ 1)
          (lvl_hPE hPE 1) (lvlVerts_pos hP 1) (hact_shift hact) d
          (childBd hPE hact d hd)).answer :=
  contractOutOfTower_splice G P E₀ hPE hP hact d hd (childBd hPE hact d hd)

/-- **The §4 strategy with the child supplied by the recursion**: a uniform node per instance, the
only datum left being the depth at which every instance's child finishes. -/
noncomputable def contractStrategyTower (G : WGraph V E)
    (hPE : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hPne : ∀ (P : Finset V) (_E₀ : Finset E), 0 < P.card)
    (hact : ∀ (P : Finset V) (E₀ : Finset E) (d i : ℕ), i < 2 →
      ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (hd : ∀ (P : Finset V) (E₀ : Finset E), (lvlVerts G P E₀ 1).card ≤ 4 ^ d) :
    ContractStrategy G :=
  fun P E₀ => contractOutOfTower G P E₀ (hPE P E₀) (hPne P E₀) (hact P E₀) d (hd P E₀)

/-- The recursion-supplied strategy is well-formed. -/
theorem contractStrategyTower_wf (G : WGraph V E)
    (hPE : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hPne : ∀ (P : Finset V) (_E₀ : Finset E), 0 < P.card)
    (hact : ∀ (P : Finset V) (E₀ : Finset E) (d i : ℕ), i < 2 →
      ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (hd : ∀ (P : Finset V) (E₀ : Finset E), (lvlVerts G P E₀ 1).card ≤ 4 ^ d) :
    ContractWf (contractStrategyTower G hPE hPne hact d hd) :=
  fun _ _ => ⟨rfl, rfl⟩

/-- Every node of the recursion-supplied strategy answers its instance, and its answer is the
tower's. -/
theorem contractStrategyTower_answer (G : WGraph V E)
    (hPE : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hPne : ∀ (P : Finset V) (_E₀ : Finset E), 0 < P.card)
    (hact : ∀ (P : Finset V) (E₀ : Finset E) (d i : ℕ), i < 2 →
      ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (hd : ∀ (P : Finset V) (E₀ : Finset E), (lvlVerts G P E₀ 1).card ≤ 4 ^ d)
    (P : Finset V) (E₀ : Finset E) :
    (contractStrategyTower G hPE hPne hact d hd P E₀).answer = answer G P E₀ (d + 1) ∅ :=
  contractOutOfTower_answer G P E₀ (hPE P E₀) (hPne P E₀) (hact P E₀) d (hd P E₀)

end TowerChild

/-! ## §4's display: the recursion's total size is linear

`display_of_strategy` is §3.6's accounting for a `CallOut` strategy, and §4 cannot produce a
`CallOut` (`crossE_subset_unsupp`).  So §4's display is stated on the tower instead.  The measure
`4·|V_{j+1}| ≤ |V_j|` is a geometric decay, so the level forests — and hence the answer — total at
most `4/3` of the instance's vertex count, at every depth.  That is the §4 analogue of §3.6's
display conclusion: correctness at the instance plus a cost bound with an explicit constant. -/

section Display

/-- **The levels decay geometrically**: `3·Σ_{j<d} |V_j| + 4·|V_d| ≤ 4·|P|`, i.e.
`Σ_{j<d} |V_j| ≤ (4/3)(|P| − |V_d|)`.  Strengthening the induction by the `4·|V_d|` slack is what
makes the geometric step go through in `ℕ`. -/
theorem three_mul_sum_lvlVerts_le {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) :
    3 * (Finset.sum (Finset.range d) (fun j => (lvlVerts G P E₀ j).card)) +
        4 * (lvlVerts G P E₀ d).card ≤ 4 * P.card := by
  induction d with
  | zero => simp [lvlVerts, lvlData]
  | succ n ih =>
      have hstep := four_mul_lvlVerts_succ_le (G := G) (P := P) (E₀ := E₀) hPE hact n
      rw [Finset.sum_range_succ]
      omega

/-- A level's forest is carried by the level's vertices. -/
theorem lvlForest_card_le_lvlVerts {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (d : ℕ) :
    (lvlForest G P E₀ d).card ≤ (lvlVerts G P E₀ d).card := by
  have hF : IsForest (lvlGraph G P E₀ d) (lvlForest G P E₀ d) := by
    rw [lvlForest_eq_chain G P E₀ d]
    exact isForest_phaseChain (G := lvlGraph G P E₀ d) (B := lvlE G P E₀ d)
      (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d)) 2 rfl (fun _ => rfl)
  exact card_le_card_of_isForest_of_ends (G := lvlGraph G P E₀ d) (P := lvlVerts G P E₀ d) hF
    fun e he => lvl_hPE hPE d e (lvlForest_subset_lvlE (G := G) (P := P) (E₀ := E₀) d he)

/-- **The whole tower's output is at most `4/3` of the instance**: `3·Σ_{j<d}|F_j| ≤ 4·|P|`. -/
theorem three_mul_sum_lvlForest_le {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) :
    3 * (Finset.sum (Finset.range d) (fun j => (lvlForest G P E₀ j).card)) ≤ 4 * P.card := by
  have hV := three_mul_sum_lvlVerts_le (G := G) (P := P) (E₀ := E₀) hPE hact d
  have hsum : Finset.sum (Finset.range d) (fun j => (lvlForest G P E₀ j).card) ≤
      Finset.sum (Finset.range d) (fun j => (lvlVerts G P E₀ j).card) :=
    Finset.sum_le_sum fun j _ => lvlForest_card_le_lvlVerts hPE j
  omega

/-- **The terminating answer has `3·|answer| ≤ 4·|P|`** — §4's output is linear in the instance,
uniformly in the depth. -/
theorem answer_card_le_third {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) : 3 * (answer G P E₀ d ∅).card ≤ 4 * P.card := by
  rw [tower_card (G := G) (P := P) (E₀ := E₀) d ∅ (Finset.empty_subset _),
    Finset.card_empty, Nat.add_zero]
  exact three_mul_sum_lvlForest_le hPE hact d

/-- **§4's display**: at a depth where the child would terminate, the recursion's answer is an MSF
of the instance, its weight is exactly the sum of the level forests' weights, its size is at most
`4/3` of the instance, and each level quarters the vertex set.  This is what §4 can say in place of
§3.6's `display_of_strategy` — correctness plus cost, with the constants explicit. -/
theorem contractDisplay {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (hd : P.card ≤ 4 ^ d) :
    IsMSFOf G E₀ (answer G P E₀ d ∅) ∧
      wsum G (answer G P E₀ d ∅) =
        Finset.sum (Finset.range d) (fun j => wsum G (lvlForest G P E₀ j)) ∧
      3 * (answer G P E₀ d ∅).card ≤ 4 * P.card ∧
      (∀ j, j < d → 4 * (lvlVerts G P E₀ (j + 1)).card ≤ (lvlVerts G P E₀ j).card) :=
  ⟨tower_terminates hPE hP hact d hd,
    by
      rw [tower_wsum (G := G) (P := P) (E₀ := E₀) d ∅ (Finset.empty_subset _)]
      simp [wsum],
    answer_card_le_third hPE hact d,
    fun j _ => four_mul_lvlVerts_succ_le (G := G) (P := P) (E₀ := E₀) hPE hact j⟩

end Display

/-! ## The child's cost, and the node's -/

section NodeCost

/-- The subtype round trip does not change the size: the child's cross-edge set and the child's
answer have the same cardinality. -/
theorem crossChild_card {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (hd : (lvlVerts G P E₀ 1).card ≤ 4 ^ d) :
    (crossChild G P E₀ d).card = (childAnswer G P E₀ d).card := by
  rw [← crossChild_image hPE hP hact d hd]
  exact (Finset.card_image_of_injective
    (s := crossChild G P E₀ d)
    (f := (Subtype.val : {e // e ∈ crossE G (phaseChain G E₀ 2) E₀} → E))
    Subtype.val_injective).symm

/-- **The child's own answer is a quarter of the parent**: the node's edge budget, read on the
child's answer rather than on the cross-edge subtype. -/
theorem contractOutOfTower_smallE {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (hd : (lvlVerts G P E₀ 1).card ≤ 4 ^ d) :
    4 * (childAnswer G P E₀ d).card ≤ P.card := by
  have h := (contractOutOfTower G P E₀ hPE hP hact d hd).smallE
  change 4 * (crossChild G P E₀ d).card ≤ P.card at h
  rwa [crossChild_card hPE hP hact d hd] at h

/-- The child's answer obeys §4's own display: `3·|child| ≤ 4·|child's vertex set|`. -/
theorem childAnswer_card_le_third {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) :
    3 * (childAnswer G P E₀ d).card ≤ 4 * (lvlVerts G P E₀ 1).card :=
  answer_card_le_third (G := lvlGraph G P E₀ 1) (P := lvlVerts G P E₀ 1) (E₀ := lvlE G P E₀ 1)
    (lvl_hPE hPE 1) (hact_shift hact) d

/-- **The node's answer is no bigger than its instance**: the transported forest bound.  With
`contractStrategy_smallV`/`contractStrategy_smallE` this completes the record's cost transport. -/
theorem contractStrategy_answer_card_le {G : WGraph V E} {S : ContractStrategy G}
    (hS : ContractWf S) (P : Finset V) (E₀ : Finset E)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) :
    (S P E₀).answer.card ≤ P.card := by
  have hO := contractStrategy_answer_isMSF hS P E₀
  exact card_le_card_of_isForest_of_ends (G := G) (P := P) hO.1.1
    fun e he => hPE e (hO.1.2.1 he)

end NodeCost

/-! ## The tower's work measure

The levels shrink in vertices (`4·|V_{j+1}| ≤ |V_j|`) but only weakly in edges
(`lvlE (j+1) ⊆ lvlE j`).  So the *count* of items the recursion touches — one scan of each level's
edges plus one visit per level's vertex — is at most `(4/3)·|P| + d·|E₀|`.  No cost model is
involved: this is a counting statement, and it is what a running-time analysis would have to start
from. -/

section Work

theorem lvlE_card_le {G : WGraph V E} {P : Finset V} {E₀ : Finset E} (d : ℕ) :
    (lvlE G P E₀ (d + 1)).card ≤ (lvlE G P E₀ d).card :=
  Finset.card_le_card (lvlE_succ_subset (G := G) (P := P) (E₀ := E₀) d)

/-- Every level's edge set is no bigger than the instance's. -/
theorem sum_lvlE_le {G : WGraph V E} {P : Finset V} {E₀ : Finset E} (d : ℕ) :
    Finset.sum (Finset.range d) (fun j => (lvlE G P E₀ j).card) ≤ d * E₀.card := by
  have h : ∀ j, (lvlE G P E₀ j).card ≤ E₀.card :=
    fun j => Finset.card_le_card (lvlE_subset G P E₀ j)
  calc Finset.sum (Finset.range d) (fun j => (lvlE G P E₀ j).card)
      ≤ Finset.sum (Finset.range d) (fun _ => E₀.card) := Finset.sum_le_sum fun j _ => h j
    _ = d * E₀.card := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id]

/-- What one level costs to touch: its vertices and its edges. -/
noncomputable def levelWork {G : WGraph V E} (P : Finset V) (E₀ : Finset E) (j : ℕ) : ℕ :=
  (lvlVerts G P E₀ j).card + (lvlE G P E₀ j).card

/-- **The tower touches `(4/3)·|P| + d·|E₀|` items in total**: the vertex part is charged by the
geometric decay, the edge part only by "no level exceeds the root" — the `d`-fold repetition of the
instance's edges is exactly the missing sparsification. -/
theorem tower_work_le {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) :
    3 * Finset.sum (Finset.range d) (fun j => levelWork (G := G) P E₀ j) ≤
      4 * P.card + 3 * (d * E₀.card) := by
  have hV := three_mul_sum_lvlVerts_le (G := G) (P := P) (E₀ := E₀) hPE hact d
  have hE : Finset.sum (Finset.range d) (fun j => (lvlE G P E₀ j).card) ≤ d * E₀.card :=
    sum_lvlE_le (G := G) (P := P) (E₀ := E₀) d
  have hsplit : Finset.sum (Finset.range d) (fun j => levelWork (G := G) P E₀ j)
      = Finset.sum (Finset.range d) (fun j => (lvlVerts G P E₀ j).card)
        + Finset.sum (Finset.range d) (fun j => (lvlE G P E₀ j).card) := by
    simp only [levelWork, Finset.sum_add_distrib]
  rw [hsplit]
  have hE3 : 3 * Finset.sum (Finset.range d) (fun j => (lvlE G P E₀ j).card)
      ≤ 3 * (d * E₀.card) := Nat.mul_le_mul_left 3 hE
  omega

/-- **§4's edge account**: the rounds' forest and the child's edge set are disjoint parts of the
instance. -/
theorem phase_card_add_cross_le {G : WGraph V E} {E₀ : Finset E} :
    (phaseChain G E₀ 2).card + (crossE G (phaseChain G E₀ 2) E₀).card ≤ E₀.card := by
  rw [← Finset.card_union_of_disjoint
    (disjoint_crossE_F (G := G) (F := phaseChain G E₀ 2) (E₀ := E₀))]
  exact Finset.card_le_card
    (Finset.union_subset (phaseChain_subset (G := G) E₀ 2)
      (crossE_subset (G := G) (F := phaseChain G E₀ 2) (E₀ := E₀)))

/-- A node's answer never exceeds its instance. -/
theorem contractStrategy_answer_card_le_edges {G : WGraph V E} {S : ContractStrategy G}
    (hS : ContractWf S) (P : Finset V) (E₀ : Finset E) :
    (S P E₀).answer.card ≤ E₀.card :=
  Finset.card_le_card (contractStrategy_answer_isMSF hS P E₀).1.2.1

/-- **The strategy's display**: every node of the recursion-supplied strategy is an MSF of its own
instance, its weight is the sum of the level forests, and its size obeys §4's bound — all read off
`contractDisplay` at depth `d+1`. -/
theorem contractStrategyTower_display (G : WGraph V E)
    (hPE : ∀ (P : Finset V) (E₀ : Finset E) (e : E), e ∈ E₀ → G.src e ∈ P ∧ G.dst e ∈ P)
    (hPne : ∀ (P : Finset V) (_E₀ : Finset E), 0 < P.card)
    (hact : ∀ (P : Finset V) (E₀ : Finset E) (d i : ℕ), i < 2 →
      ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (hd : ∀ (P : Finset V) (E₀ : Finset E), (lvlVerts G P E₀ 1).card ≤ 4 ^ d)
    (P : Finset V) (E₀ : Finset E) (hPd : P.card ≤ 4 ^ (d + 1)) :
    IsMSFOf G E₀ ((contractStrategyTower G hPE hPne hact d hd P E₀).answer) ∧
      wsum G ((contractStrategyTower G hPE hPne hact d hd P E₀).answer) =
        Finset.sum (Finset.range (d + 1)) (fun j => wsum G (lvlForest G P E₀ j)) ∧
      3 * ((contractStrategyTower G hPE hPne hact d hd P E₀).answer).card ≤ 4 * P.card := by
  have hD := contractDisplay (G := G) (P := P) (E₀ := E₀) (hPE P E₀) (hPne P E₀) (hact P E₀)
    (d + 1) hPd
  rw [contractStrategyTower_answer G hPE hPne hact d hd P E₀]
  exact ⟨hD.1, hD.2.1, hD.2.2.1⟩

end Work

/-! ## The recursion as a depth-indexed tree

`ContractTree G P E₀ (d+1)` is a §4 node plus the subtree of depth `d` at the *contracted* instance.
The depth lives in the type, so "the child is the same procedure one level down" is a typing fact
rather than a side condition. -/

section Tree

/-- A depth-`d` recursion tree: one §4 node per level, the child tree at the contracted instance.
The leaf (`0`) is empty; the tower's termination is what keeps the recursion from having to use it. -/
def ContractTree (G : WGraph V E) (P : Finset V) (E₀ : Finset E) : ℕ → Type _
  | 0 => PUnit
  | d + 1 =>
      ContractOut G ×
        ContractTree (lvlGraph G P E₀ 1) (lvlVerts G P E₀ 1) (lvlE G P E₀ 1) d

/-- **The tree exists** as soon as every instance's child fits in the remaining depth. -/
noncomputable def treeOfBd (G : WGraph V E) (P : Finset V) (E₀ : Finset E)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e) :
    (d : ℕ) → (lvlVerts G P E₀ 1).card ≤ 4 ^ d → ContractTree G P E₀ (d + 1)
  | 0, hd => ⟨contractOutOfTower G P E₀ hPE hP hact 0 hd, PUnit.unit⟩
  | d + 1, hd =>
      ⟨contractOutOfTower G P E₀ hPE hP hact (d + 1) hd,
        treeOfBd (lvlGraph G P E₀ 1) (lvlVerts G P E₀ 1) (lvlE G P E₀ 1)
          (lvl_hPE hPE 1) (lvlVerts_pos hP 1) (hact_shift hact) d
          (childBd hPE hact d hd)⟩

theorem treeOfBd_fst (G : WGraph V E) (P : Finset V) (E₀ : Finset E)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (hd : (lvlVerts G P E₀ 1).card ≤ 4 ^ d) :
    (treeOfBd G P E₀ hPE hP hact d hd).1 = contractOutOfTower G P E₀ hPE hP hact d hd := by
  cases d <;> rfl

/-- Every node in the tree answers with the tower's answer at its own depth. -/
theorem treeOfBd_answer (G : WGraph V E) (P : Finset V) (E₀ : Finset E)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (hd : (lvlVerts G P E₀ 1).card ≤ 4 ^ d) :
    (treeOfBd G P E₀ hPE hP hact d hd).1.answer = answer G P E₀ (d + 1) ∅ := by
  rw [treeOfBd_fst]
  exact contractOutOfTower_answer G P E₀ hPE hP hact d hd

/-- **The parent's answer is the level forest together with the child's** — with the child typed
one level down, not chosen. -/
theorem treeOfBd_splice (G : WGraph V E) (P : Finset V) (E₀ : Finset E)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (hd : (lvlVerts G P E₀ 1).card ≤ 4 ^ (d + 1)) :
    (treeOfBd G P E₀ hPE hP hact (d + 1) hd).1.answer
      = lvlForest G P E₀ 0 ∪
        (treeOfBd (lvlGraph G P E₀ 1) (lvlVerts G P E₀ 1) (lvlE G P E₀ 1)
          (lvl_hPE hPE 1) (lvlVerts_pos hP 1) (hact_shift hact) d
          (childBd hPE hact d hd)).1.answer := by
  rw [treeOfBd_fst, treeOfBd_fst]
  exact contractOutOfTower_splice G P E₀ hPE hP hact d hd (childBd hPE hact d hd)

theorem treeOfBd_wsum (G : WGraph V E) (P : Finset V) (E₀ : Finset E)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (hd : (lvlVerts G P E₀ 1).card ≤ 4 ^ d) :
    wsum G (treeOfBd G P E₀ hPE hP hact d hd).1.answer
      = Finset.sum (Finset.range (d + 1)) (fun j => wsum G (lvlForest G P E₀ j)) := by
  rw [treeOfBd_answer,
    tower_wsum (G := G) (P := P) (E₀ := E₀) (d + 1) ∅ (Finset.empty_subset _)]
  simp [wsum]

theorem treeOfBd_sound (G : WGraph V E) (P : Finset V) (E₀ : Finset E)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (hd : (lvlVerts G P E₀ 1).card ≤ 4 ^ d) :
    IsMSFOf G E₀ (treeOfBd G P E₀ hPE hP hact d hd).1.answer := by
  rw [treeOfBd_fst]
  exact (contractOutOfTower G P E₀ hPE hP hact d hd).isMSF

theorem treeOfBd_card_le (G : WGraph V E) (P : Finset V) (E₀ : Finset E)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (hd : (lvlVerts G P E₀ 1).card ≤ 4 ^ d) :
    (treeOfBd G P E₀ hPE hP hact d hd).1.answer.card ≤ P.card := by
  have h := treeOfBd_sound G P E₀ hPE hP hact d hd
  exact card_le_card_of_isForest_of_ends (G := G) (P := P) h.1.1
    fun e he => hPE e (h.1.2.1 he)

end Tree

/-! ## No per-level edge halving

The vertex side shrinks geometrically (`4·|V_{j+1}| ≤ |V_j|`), the edge side only weakly
(`lvlE (j+1) ⊆ lvlE j`).  An earlier conditional `O(|P| + |E₀|)` statement based on per-level edge
halving has been **removed**: that hypothesis is not merely unproved but false for this recursion.
`LinearTime.hshr_refuted` exhibits an 8-vertex, 17-edge instance whose child keeps 9 edges
(`2·9 > 17`), and `hshr_refuted_stop` the same failure at the stopping depth.

The paper's linearity does not come from this route.  It comes from the §3.6 display
(`Σ|kidE| ≤ ρm + C√(m·n′)`) together with the Borůvka phase halving (`n′ ≤ 2m/2^{2j}`); the
counting form of that route is `LinearTime.counting_linear_of_display`, and the display itself is
discharged from RoundData by `Assembly.sum_kidE_le_paper_bound`. -/

/-! ## The depth is `⌈log₄|P|⌉ + 1`, unconditionally

The tower's only depth requirement is `|P| ≤ 4^d`; taking `d := log₄|P| + 1` discharges it, so the
§4 recursion terminates at every instance without a depth parameter. -/

section LogDepth

/-- `|P| ≤ 4^(log₄|P| + 1)` — the smallest depth that always suffices. -/
theorem card_le_pow_log (n : ℕ) : n ≤ 4 ^ (Nat.log 4 n + 1) :=
  le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) n)

/-! ## The boundary of the activation hypothesis

Unbounded `hact` asks the phases to leave every vertex an outgoing edge at *every* depth.  At the
bottom depth the measure forces the level to a single vertex, where no such edge can exist (every
instance edge is a loop).  So the unbounded form is inconsistent; `tower_sound_bd` and
`tower_msf_of_stop` are the versions that only activate above the stopping level. -/

/-- A level with at most one vertex cannot satisfy even the first phase's activation. -/
theorem not_activated_of_card_le_one {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card) (d : ℕ)
    (hd : (lvlVerts G P E₀ d).card ≤ 1) :
    ¬ (∀ i : ℕ, i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d)
          (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e) := by
  intro h
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (lvlVerts_pos (G := G) (E₀ := E₀) hP d)
  obtain ⟨e, he, hlv⟩ := h 0 (by norm_num) v hv
  rw [show phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) 0 = ∅ from rfl] at hlv
  obtain ⟨hs, hd'⟩ := lvl_hPE hPE d e he
  have hsd : (lvlGraph G P E₀ d).src e = (lvlGraph G P E₀ d).dst e :=
    Finset.card_le_one.mp hd _ hs _ hd'
  rcases hlv with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hsv : (lvlGraph G P E₀ d).src e = v := conn_empty h1
    have hdv : (lvlGraph G P E₀ d).dst e = v := hsd.symm.trans hsv
    exact h2 (by rw [hdv]; exact Conn.refl v)
  · have hdv : (lvlGraph G P E₀ d).dst e = v := conn_empty h2
    have hsv : (lvlGraph G P E₀ d).src e = v := hsd.trans hdv
    exact h1 (by rw [hsv]; exact Conn.refl v)

/-- Unbounded activation is inconsistent with a nonempty instance: the measure at depth
`log₄|P| + 1` forces one vertex, where activation is impossible. -/
theorem activated_false_of_pos {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e) :
    False :=
  not_activated_of_card_le_one hPE hP (Nat.log 4 P.card + 1)
    (lvlVerts_card_le_one hPE hP hact _ (card_le_pow_log P.card))
    (fun i hi => hact _ i hi)

/-- The root-connectivity interface is inconsistent as well: it derives unbounded activation. -/
theorem root_conn_false_of_pos {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hconn : ∀ u ∈ P, ∀ w ∈ P, Conn G E₀ u w)
    (hc : ∀ (d i : ℕ), i < 2 →
      2 ≤ compCountOn (lvlGraph G P E₀ d) (lvlVerts G P E₀ d)
        (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i)) :
    False :=
  activated_false_of_pos hPE hP (tower_hact_of_root_conn hPE hconn hc)

/-- **Termination, unconditionally**: at depth `⌈log₄|P|⌉ + 1` the tower's answer is the instance's
MSF — no depth hypothesis. -/
theorem tower_terminates_log {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e) :
    IsMSFOf G E₀ (answer G P E₀ (Nat.log 4 P.card + 1) ∅) :=
  tower_terminates hPE hP hact _ (card_le_pow_log P.card)

theorem tower_terminates_log_card {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e) :
    (answer G P E₀ (Nat.log 4 P.card + 1) ∅).card ≤ P.card :=
  tower_terminates_card hPE hP hact _ (card_le_pow_log P.card)

/-- **§4's display at its own depth**: correctness, the level-forest weight identity, the `4/3`
bound, and the per-level quartering — at `d = log₄|P| + 1`. -/
theorem contractDisplay_log {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e) :
    IsMSFOf G E₀ (answer G P E₀ (Nat.log 4 P.card + 1) ∅) ∧
      wsum G (answer G P E₀ (Nat.log 4 P.card + 1) ∅) =
        Finset.sum (Finset.range (Nat.log 4 P.card + 1))
          (fun j => wsum G (lvlForest G P E₀ j)) ∧
      3 * (answer G P E₀ (Nat.log 4 P.card + 1) ∅).card ≤ 4 * P.card ∧
      (∀ j, j < Nat.log 4 P.card + 1 →
        4 * (lvlVerts G P E₀ (j + 1)).card ≤ (lvlVerts G P E₀ j).card) :=
  contractDisplay hPE hP hact _ (card_le_pow_log P.card)

/-- **Termination from root connectivity alone**: `E₀` connects the instance's vertices, and every
phase retains at least two instance components.  Per-level connectivity and activation are derived
(`lvl_connOn_of_root_conn`), and the depth is `log₄|P| + 1`. -/
theorem tower_terminates_log_root_conn {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hconn : ∀ u ∈ P, ∀ w ∈ P, Conn G E₀ u w)
    (hc : ∀ (d i : ℕ), i < 2 →
      2 ≤ compCountOn (lvlGraph G P E₀ d) (lvlVerts G P E₀ d)
        (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i)) :
    IsMSFOf G E₀ (answer G P E₀ (Nat.log 4 P.card + 1) ∅) :=
  tower_terminates hPE hP (tower_hact_of_root_conn hPE hconn hc) _ (card_le_pow_log P.card)

end LogDepth

/-! ## The tree exists at its own depth

`treeOfBd` needs a depth bound; at `⌈log₄|P|⌉ + 1` the bound is free, so the recursion tree exists
with no depth parameter at all. -/

section TreeLog

theorem lvlVerts_one_card_le {G : WGraph V E} {P : Finset V} {E₀ : Finset E} :
    (lvlVerts G P E₀ 1).card ≤ P.card :=
  Finset.card_le_card (repSet_subset (G := G) (P := P) (F := phaseChain G E₀ 2))

theorem lvlVerts_one_card_le_pow {G : WGraph V E} {P : Finset V} {E₀ : Finset E} :
    (lvlVerts G P E₀ 1).card ≤ 4 ^ (Nat.log 4 P.card + 1) :=
  le_trans lvlVerts_one_card_le (card_le_pow_log P.card)

/-- **The recursion tree, at its own depth**: `⌈log₄|P|⌉ + 1` levels, no depth hypothesis. -/
noncomputable def treeOfLog (G : WGraph V E) (P : Finset V) (E₀ : Finset E)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e) :
    ContractTree G P E₀ (Nat.log 4 P.card + 2) :=
  treeOfBd G P E₀ hPE hP hact (Nat.log 4 P.card + 1) lvlVerts_one_card_le_pow

theorem treeOfLog_sound (G : WGraph V E) (P : Finset V) (E₀ : Finset E)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e) :
    IsMSFOf G E₀ (treeOfLog G P E₀ hPE hP hact).1.answer := by
  unfold treeOfLog
  exact treeOfBd_sound G P E₀ hPE hP hact (Nat.log 4 P.card + 1) _

theorem treeOfLog_card_le (G : WGraph V E) (P : Finset V) (E₀ : Finset E)
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e) :
    (treeOfLog G P E₀ hPE hP hact).1.answer.card ≤ P.card := by
  unfold treeOfLog
  exact treeOfBd_card_le G P E₀ hPE hP hact (Nat.log 4 P.card + 1) _

end TreeLog

/-! ## Total work at the self-chosen depth

The work bound of `tower_work_le` still carries `d`.  At `d = ⌈log₄|P|⌉ + 1` the depth disappears
into `|P|`, leaving `(4|P| + 3(log₄|P|+1)|E₀|)/3`; with the halving hypothesis it is linear. -/

section WorkLog

/-- **Total work, no depth parameter**: at the self-chosen depth the tower touches at most
`(4|P| + 3(log₄|P|+1)|E₀|)/3` items. -/
theorem tower_work_log {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e) :
    3 * Finset.sum (Finset.range (Nat.log 4 P.card + 1))
        (fun j => levelWork (G := G) P E₀ j) ≤
      4 * P.card + 3 * ((Nat.log 4 P.card + 1) * E₀.card) :=
  tower_work_le (G := G) (P := P) (E₀ := E₀) hPE hact _

end WorkLog

/-! ## The sharp size bound: a forest on `|P|` vertices has at most `|P| - 1` edges

The `4/3` bound of §4 is a *budget*; being a forest with endpoints in `P` gives the sharper
`|P| - 1`, which always beats it. -/

section SizeSharp

/-- **`|answer| ≤ |P| - 1`** whenever the bottom call is a valid level MSF. -/
theorem answer_card_le_sub_one {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e)
    (d : ℕ) (B : Finset E) (hB : IsMSFOf (lvlGraph G P E₀ d) (lvlE G P E₀ d) B) :
    (answer G P E₀ d B).card ≤ P.card - 1 := by
  have h := tower_sound (G := G) (P := P) (E₀ := E₀) hPE hP hact d B hB
  exact card_le_card_sub_one_of_isForest_of_ends (G := G) (F := answer G P E₀ d B)
    h.1.1.1 (fun e he => hPE e (h.1.1.2.1 he)) hP

/-- **The terminated answer obeys the forest bound**: at the self-chosen depth, `|answer| ≤ |P|-1`. -/
theorem tower_terminates_log_card_sub_one {G : WGraph V E} {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card)
    (hact : ∀ (d i : ℕ), i < 2 → ∀ v ∈ lvlVerts G P E₀ d,
      ∃ e ∈ lvlE G P E₀ d,
        leaves (lvlGraph G P E₀ d) (phaseChain (lvlGraph G P E₀ d) (lvlE G P E₀ d) i) v e) :
    (answer G P E₀ (Nat.log 4 P.card + 1) ∅).card ≤ P.card - 1 := by
  have h := tower_terminates_log (G := G) (P := P) (E₀ := E₀) hPE hP hact
  exact card_le_card_sub_one_of_isForest_of_ends (G := G)
    (F := answer G P E₀ (Nat.log 4 P.card + 1) ∅) h.1.1
    (fun e he => hPE e (h.1.2.1 he)) hP

/-- **The strategy's answer is a forest on `P`**, so `|answer| ≤ |P| - 1`. -/
theorem contractStrategy_answer_card_le_sub_one {G : WGraph V E} {S : ContractStrategy G}
    (hS : ContractWf S) {P : Finset V} {E₀ : Finset E}
    (hPE : ∀ e ∈ E₀, G.src e ∈ P ∧ G.dst e ∈ P) (hP : 0 < P.card) :
    (S P E₀).answer.card ≤ P.card - 1 :=
  card_le_card_sub_one_of_isForest_of_ends (G := G) (F := (S P E₀).answer)
    (contractStrategy_answer_isMSF hS P E₀).1.1
    (fun e he => hPE e ((contractStrategy_answer_isMSF hS P E₀).1.2.1 he)) hP

/-! ## §4 cannot fill a `CallOut`: the model conflict, machine-checked

The two interfaces disagree about the child's edge set.  §3.6's `CallOut.hUkid` says a child is
disjoint from the retained set `U(F) = unsupp ∩ E₀`; §4's contraction hands the child exactly the
cross edges, which are unsupported and belong to the instance (`crossE_subset_unsupp`,
`crossE_subset`).  The three lemmas below record the conflict once and for all: every `CallOut`
child edge is *supported* by `F`, every cross edge is not, so a child can only receive cross edges
by being empty — which is not the §4 recursion. -/

/-- **§3.6 child edges are supported.**  `CallOut.hUkid` puts them outside `unsupp ∩ E₀`; together
with `hkidE` they are supported by the call's forest.  This is the property §4's cross edges fail
(`crossE_subset_unsupp`). -/
theorem CallOut.supported_of_mem_kidE {G : WGraph V E} {ι : Type*} [Fintype ι]
    (O : CallOut G ι) (i : ι) {e : E}
    (he : e ∈ O.kidE i) : supported G O.F e := by
  by_contra hns
  exact Finset.disjoint_left.mp (O.hUkid i)
    (Finset.mem_inter.mpr ⟨mem_unsupp.mpr hns, O.hkidE i he⟩) he

/-- **Cross edges never reach a `CallOut` child.**  Since `crossE ⊆ unsupp ∩ E₀`, `hUkid` makes every
child edge set disjoint from the whole cross set. -/
theorem CallOut.disjoint_crossE_kidE {G : WGraph V E} {ι : Type*} [Fintype ι]
    (O : CallOut G ι) (i : ι) :
    Disjoint (crossE G O.F O.E₀) (O.kidE i) := by
  rw [Finset.disjoint_left]
  intro e he hk
  exact Finset.disjoint_left.mp (O.hUkid i)
    (Finset.mem_inter.mpr
      ⟨crossE_subset_unsupp (G := G) (F := O.F) (E₀ := O.E₀) he,
        crossE_subset (G := G) O.F O.E₀ he⟩) hk

/-- **The no-go.**  A nonempty set of cross edges cannot be a `CallOut` child's input.  Hence the
§4 step — whose child receives the cross edges — is not a `CallOut`, and §3.6's display layer
cannot be fed from the contraction recursion without changing one of the two interfaces (boundary
B1 of `CORRESPONDENCE.md`). -/
theorem CallOut.not_subset_kidE_of_crossE {G : WGraph V E} {ι : Type*} [Fintype ι]
    (O : CallOut G ι) (i : ι)
    {B : Finset E} (hB : B ⊆ crossE G O.F O.E₀) (hne : B.Nonempty) : ¬ B ⊆ O.kidE i := by
  intro hsub
  obtain ⟨e, he⟩ := hne
  exact Finset.disjoint_left.mp (O.disjoint_crossE_kidE i) (hB he) (hsub he)

/-- **The conflict is non-vacuous exactly in the §4 regime.**  In a phase — a forest `M ⊇ F` with an
edge `e ∈ M` outside `F`, all inside the instance — `e` is a cross edge (`mem_crossE_of_mem_of_not_mem`
through `IsForest.bridge`), hence no `CallOut` child of this call can receive it.  So §4's child
input and §3.6's child input genuinely differ on the edges the recursion is about. -/
theorem CallOut.not_mem_kidE_of_phase {G : WGraph V E} {ι : Type*} [Fintype ι]
    (O : CallOut G ι) (i : ι) {M : Finset E} (hM : IsForest G M) (hFM : O.F ⊆ M)
    (hME : M ⊆ O.E₀) {e : E} (heM : e ∈ M) (heF : e ∉ O.F) : e ∉ O.kidE i := by
  intro hk
  exact Finset.disjoint_left.mp (O.disjoint_crossE_kidE i)
    (mem_crossE_of_mem_of_not_mem (G := G) (E₀ := O.E₀) (F := O.F) (M := M)
      hM hFM hME heM heF) hk

end SizeSharp

end DLMST
