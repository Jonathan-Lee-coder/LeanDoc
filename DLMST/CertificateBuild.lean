import DLMST.Certificate
import DLMST.Section36

/-!
# From the display to a `Certificate`: the §4 composition

`Certificate.lean` isolates the §2–§3 obligations as four fields and proves that they imply
`T(m) = O(m)`.  `Section36.lean` machine-checks the *numerical* end of the display.  What was still
prose is the step §4 actually takes: the certificate procedure returns children on at most `n′`
vertices, `k = 2j` Borůvka phases make `n′` shrink like `2m/2^{2j}`, and the display
`Σ|Eᵢ| ≤ ρm + C√(m n′)` — originally in `√(mn)` — becomes the `√(m·2m/2^{2j})` shape that
`Bookkeeping.closure` closes.

`certificate_of_display` performs exactly that substitution, so the interface's `hbound` field no
longer has to be assumed in the halved form: it follows from the display with the *un*-halved vertex
count plus the vertex bound.  `linear_of_display` is the composed statement "display + vertex halving
⇒ linear comparisons", which is the paper's §4 claim with its only inputs named.
-/

namespace DLMST

/-- **§4's substitution, machine-checked.**  If every instance's children satisfy the display with the
vertex count `nsub m` (`Σ|Eᵢ| ≤ ρm + C√(m·nsub m)`) and `nsub m ≤ 2m/2^{2j}`, then the halved-form
obligations of `Certificate` hold.  Monotonicity of `√` and of `· ↦ C··` is the whole proof. -/
noncomputable def certificate_of_display {C ρ : ℝ} {j : ℕ} (hC : 0 ≤ C) (hρ : ρ ≤ 1 / 8)
    (hj : C * 2 / (2 : ℝ) ^ j ≤ 3 / 8)
    (subSizes : ℕ → List ℕ) (nsub : ℕ → ℕ)
    (hdisplay : ∀ m : ℕ, ((subSizes m).sum : ℝ) ≤
      ρ * (m : ℝ) + C * Real.sqrt ((m : ℝ) * (nsub m : ℝ)))
    (hn : ∀ m : ℕ, (nsub m : ℝ) ≤ 2 * (m : ℝ) / (2 : ℝ) ^ (2 * j)) :
    Certificate := by
  refine ⟨C, hC, ρ, hρ, j, subSizes, fun m => ?_, hj⟩
  refine le_trans (hdisplay m) ?_
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hprod : (m : ℝ) * (nsub m : ℝ) ≤ (m : ℝ) * (2 * (m : ℝ) / (2 : ℝ) ^ (2 * j)) :=
    mul_le_mul_of_nonneg_left (hn m) hm
  have hsqrt := Real.sqrt_le_sqrt hprod
  have hCsqrt : C * Real.sqrt ((m : ℝ) * (nsub m : ℝ)) ≤
      C * Real.sqrt ((m : ℝ) * (2 * (m : ℝ) / (2 : ℝ) ^ (2 * j))) :=
    mul_le_mul_of_nonneg_left hsqrt hC
  linarith

/-- **Display + vertex halving ⇒ `O(m)` comparisons.**  The composed form of §4: supply the display
with its vertex count and the phase-halving bound, and a routine that recurses as the certificate
prescribes runs in linear comparisons.  No other hypothesis is used. -/
theorem linear_of_display {C ρ : ℝ} {j : ℕ} (hC : 0 ≤ C) (hρ : ρ ≤ 1 / 8)
    (hj : C * 2 / (2 : ℝ) ^ j ≤ 3 / 8)
    (subSizes : ℕ → List ℕ) (nsub : ℕ → ℕ)
    (hdisplay : ∀ m : ℕ, ((subSizes m).sum : ℝ) ≤
      ρ * (m : ℝ) + C * Real.sqrt ((m : ℝ) * (nsub m : ℝ)))
    (hn : ∀ m : ℕ, (nsub m : ℝ) ≤ 2 * (m : ℝ) / (2 : ℝ) ^ (2 * j))
    (T : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c) (hT0 : T 0 ≤ 0)
    (hrec : ∀ m, T m ≤ ((subSizes m).map T).sum + c * m) :
    ∃ c' : ℝ, 0 ≤ c' ∧ ∀ m, T m ≤ c' * m :=
  certificate_implies_linear (certificate_of_display hC hρ hj subSizes nsub hdisplay hn) T c hc hT0 hrec

end DLMST