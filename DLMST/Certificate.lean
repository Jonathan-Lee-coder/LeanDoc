import DLMST.MsfKernel
import DLMST.Bookkeeping
import DLMST.Recurrence

/-!
# Lemma 1.2 ⇒ `T*(m,n) = O(m)`, with the paper's obligations made explicit

`Khanna–Putterman–Song` prove Theorem 4.1 in two moves: the certificate procedure (§2–§3, their
Lemma 1.2) bounds the size of what recurses, and §4 spends `k` Borůvka phases to make that bound
`o(m)`-like so the recursion closes.  The second move is fully machine-checked in
`Bookkeeping.lean`; the recursion itself in `Recurrence.lean`.

What could not be checked by arithmetic alone is the *interface* between them, so it is written
down here as a structure: `Certificate` lists exactly the obligations §2–§3 owe.  The theorem
`certificate_implies_linear` then shows that **nothing else is needed** to conclude linear
comparison complexity — any object satisfying those fields yields `T(m) = O(m)`.  That converts
"the paper is right provided Lemma 1.2 holds" from prose into a checked theorem, and localises the
human judgement to four named fields (`ρ`, `j`, `hbound`, `hj`) instead of a whole section.
-/

namespace DLMST

/-- The obligations of §2–§3, in the shape §4 consumes them.

* `C` is `C_ε` at `ε = 1/8`;
* `ρ` is `(|F| + |U(F)|)/m`, the `ε·m` term of their display (∗);
* `j` is half the number of Borůvka phases (their `k = 2j`), `hj` being the choice
  `C_{1/8}·2^{(1-k)/2} ≤ 3/8` — `Bookkeeping.exists_phase` proves such a `j` always exists;
* `hbound` is (∗) itself, already composed with the vertex halving `n' ≤ 2m/2^{2j}`.

The `portal`/`spoke` construction, the `t²` rounds and matrix scheduling of Lemma 3.11, and the
sampling of Claim 3.12 all live *inside* the proof of `hbound`; they are not formalised here, which
is precisely what this structure says out loud. -/
structure Certificate where
  C : ℝ
  hC : 0 ≤ C
  ρ : ℝ
  hρ : ρ ≤ 1 / 8
  j : ℕ
  subSizes : ℕ → List ℕ
  hbound : ∀ m : ℕ, ((subSizes m).sum : ℝ) ≤
      ρ * (m : ℝ) + C * Real.sqrt ((m : ℝ) * (2 * (m : ℝ) / (2 : ℝ) ^ (2 * j)))
  hj : C * 2 / (2 : ℝ) ^ j ≤ 3 / 8

/-- A `Certificate` splits every instance into subinstances totalling at most `m/2` edges — the
`m/8 + 3m/8` closure, with the `ε·m` term replaced by the explicit fraction `ρ`. -/
theorem Certificate.slack (P : Certificate) (m : ℕ) : (P.subSizes m).sum ≤ m / 2 := by
  classical
  have hc := closure m P.C P.j P.hC P.hj
  have hr : P.ρ * (m : ℝ) ≤ (m : ℝ) / 8 := by
    have h1 : P.ρ * (m : ℝ) ≤ (1 / 8 : ℝ) * (m : ℝ) :=
      mul_le_mul_of_nonneg_right P.hρ (Nat.cast_nonneg m)
    linarith
  have h2 : (2 : ℝ) * ((P.subSizes m).sum : ℝ) ≤ (m : ℝ) := by linarith [P.hbound m, hr, hc]
  have h3 : (2 : ℕ) * (P.subSizes m).sum ≤ m := by exact_mod_cast h2
  omega

/-- **The reduction, machine-checked.**  Given anything satisfying the §2–§3 obligations, a routine
whose per-level cost is `c·m` and which recurses as the certificate prescribes runs in `O(m)`
comparisons. -/
theorem certificate_implies_linear (P : Certificate) (T : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hT0 : T 0 ≤ 0)
    (hrec : ∀ m, T m ≤ ((P.subSizes m).map T).sum + c * m) :
    ∃ c' : ℝ, 0 ≤ c' ∧ ∀ m, T m ≤ c' * m :=
  ⟨2 * c, by linarith, recurrence_linear T c hc P.subSizes hT0 hrec P.slack⟩

/-- Nothing in the interface has to be assumed away for the phase count: `exists_phase` supplies a
`j` for whatever constant `C_ε` the certificate procedure produces. -/
theorem certificate_exists_phase (C ρ : ℝ) (hC : 0 ≤ C) (hρ : ρ ≤ 1 / 8)
    (subSizes : ℕ → List ℕ)
    (hbound : ∀ j : ℕ, ∀ m : ℕ, ((subSizes m).sum : ℝ) ≤
        ρ * (m : ℝ) + C * Real.sqrt ((m : ℝ) * (2 * (m : ℝ) / (2 : ℝ) ^ (2 * j)))) :
    ∃ _ : Certificate, True := by
  classical
  obtain ⟨j, hj⟩ := exists_phase C
  exact ⟨⟨C, hC, ρ, hρ, j, subSizes, hbound j, hj⟩, trivial⟩

end DLMST
