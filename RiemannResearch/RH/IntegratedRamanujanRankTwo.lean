import RiemannResearch.RH.IntegratedRamanujanGram
import RiemannResearch.RH.IntegratedRamanujanMarkedArithmetic
import RiemannResearch.RH.ParetoResidueMean
import RiemannResearch.RH.ParetoPeriodicRegrouping
import RiemannResearch.LinearAlgebra.RankTwoWoodbury
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Totient

/-!
# Exact rank-two reduction of the actual integrated Ramanujan Gram solve

Source: user-provided Ramanujan / Green / Schur calculation, 22 September 2026.
The matrix below is the actual complete Pareto Gram matrix, and the inverse
solve already exists by finite packet independence. The three arithmetic
vectors are the actual Möbius, totient, and von Mangoldt vectors.

The analytic identification of this Gram matrix with the displayed rank-two
perturbation remains an explicit hypothesis. Neither that identification nor
invertibility of its proposed core is claimed here. The conclusion is the
marked inverse quadratic and its progression-weighted version, not an
unconditional identification with `qN`, a uniform bound, or an RH claim.
-/

open Matrix
open scoped BigOperators

namespace RiemannResearch.RH.Pareto
noncomputable section

open RiemannResearch.LinearAlgebra.RankTwoWoodbury

/-- The genuine full-tail Pareto Gram matrix on the specified conductors. -/
def ramanujanGramMatrix (s : Finset ℕ) : Matrix s s ℝ :=
  fun i j => paretoInner (ramanujanPacket i) (ramanujanPacket j)

/-- The Möbius marking; the packet convention has first-site values `-μ`. -/
def ramanujanMoebiusVector (s : Finset ℕ) : s → ℝ :=
  fun q => (ArithmeticFunction.moebius q.val : ℝ)

/-- Euler's actual totient vector on the conductor set. -/
def ramanujanTotientVector (s : Finset ℕ) : s → ℝ :=
  fun q => (Nat.totient q.val : ℝ)

/-- The actual von Mangoldt vector, retaining all prime powers. -/
def ramanujanVonMangoldtVector (s : Finset ℕ) : s → ℝ :=
  fun q => ArithmeticFunction.vonMangoldt q.val

/-- The actual first-site evaluation vector of the packet dictionary. -/
def ramanujanFirstSiteVector (s : Finset ℕ) : s → ℝ :=
  fun q => ramanujanPacket q.val 1

theorem ramanujanFirstSiteVector_eq_neg_moebiusVector
    (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q) :
    ramanujanFirstSiteVector s = -ramanujanMoebiusVector s := by
  funext q
  exact ramanujanPacket_at_one_moebius q.val (hs q.val q.property)

/-- The von Mangoldt entries coincide with the actual complete packet means. -/
theorem ramanujanVonMangoldtVector_eq_mean (s : Finset ℕ) (q : s) :
    ramanujanVonMangoldtVector s q = paretoMean (ramanujanPacket q.val) := by
  exact (paretoMean_ramanujanPacket q.val).symm

theorem ramanujanGramMatrix_mulVec (s : Finset ℕ) (v : s → ℝ) :
    ramanujanGramMatrix s *ᵥ v = ramanujanGramAction s v := by
  rfl

/-- The existing inverse, obtained from independence, solves these actual
matrix equations. No formal inverse or inverse equation is assumed. -/
theorem ramanujanGramMatrix_mulVec_solve (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (v : s → ℝ) :
    ramanujanGramMatrix s *ᵥ ramanujanGramSolve s hs v = v := by
  rw [ramanujanGramMatrix_mulVec]
  exact ramanujanGramSolve_normal_equations s hs v

/-- The actual marked inverse quadratic `μᵀ Ξ⁻¹ μ`, with the inverse supplied
by the already constructed Gram equivalence rather than by a hypothesis. -/
def ramanujanMarkedInverseQuadratic (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) : ℝ :=
  ramanujanMoebiusVector s ⬝ᵥ
    ramanujanGramSolve s hs (ramanujanMoebiusVector s)

/-- Changing both occurrences of the marking from `μ` to the actual packet
first-site vector `-μ` leaves the inverse quadratic unchanged. -/
theorem ramanujanFirstSite_inverseQuadratic_eq_marked (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) :
    ramanujanFirstSiteVector s ⬝ᵥ
        ramanujanGramSolve s hs (ramanujanFirstSiteVector s) =
      ramanujanMarkedInverseQuadratic s hs := by
  rw [ramanujanFirstSiteVector_eq_neg_moebiusVector s hs]
  unfold ramanujanGramSolve ramanujanMarkedInverseQuadratic
  simp [ramanujanGramSolve, dotProduct]

/-- The arithmetic specialization of the matrix Woodbury identity.
`hXi` is the outstanding analytic matrix identification; `hRF`, `hR`, and
`hD` are the supplied core-inverse and nondegeneracy hypotheses. -/
theorem ramanujanMarkedInverseQuadratic_eq_rankTwo (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (F R : Matrix s s ℝ)
    (hRF : R * F = 1) (hR : Rᵀ = R)
    (hXi : ramanujanGramMatrix s = rankTwoMatrix Real.pi F
      (ramanujanVonMangoldtVector s) (ramanujanTotientVector s))
    (hD :
      (ramanujanTotientVector s ⬝ᵥ (R *ᵥ ramanujanTotientVector s)) *
        (ramanujanVonMangoldtVector s ⬝ᵥ (R *ᵥ ramanujanVonMangoldtVector s)) -
      (ramanujanTotientVector s ⬝ᵥ (R *ᵥ ramanujanVonMangoldtVector s) +
        2 * Real.pi) ^ 2 ≠ 0) :
    ramanujanMarkedInverseQuadratic s hs =
      markedFormula Real.pi R (ramanujanTotientVector s)
        (ramanujanVonMangoldtVector s) (ramanujanMoebiusVector s) := by
  unfold ramanujanMarkedInverseQuadratic
  exact solved_marked_quadratic Real.pi F R (ramanujanGramMatrix s)
    (ramanujanTotientVector s) (ramanujanVonMangoldtVector s)
    (ramanujanMoebiusVector s)
    (ramanujanGramSolve s hs (ramanujanMoebiusVector s))
    hRF hR hXi (ramanujanGramMatrix_mulVec_solve s hs _)
    (ne_of_gt Real.pi_pos) hD

/-- Exact progression weighting of the actual marked inverse quadratic.
A separate basis and DPP bridge is needed before identifying this with `qN`. -/
theorem progressionWeight_mul_ramanujanMarkedInverseQuadratic_eq_rankTwo
    (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q) (L : ℕ)
    (F R : Matrix s s ℝ)
    (hRF : R * F = 1) (hR : Rᵀ = R)
    (hXi : ramanujanGramMatrix s = rankTwoMatrix Real.pi F
      (ramanujanVonMangoldtVector s) (ramanujanTotientVector s))
    (hD :
      (ramanujanTotientVector s ⬝ᵥ (R *ᵥ ramanujanTotientVector s)) *
        (ramanujanVonMangoldtVector s ⬝ᵥ (R *ᵥ ramanujanVonMangoldtVector s)) -
      (ramanujanTotientVector s ⬝ᵥ (R *ᵥ ramanujanVonMangoldtVector s) +
        2 * Real.pi) ^ 2 ≠ 0) :
    progressionWeight L 1 * ramanujanMarkedInverseQuadratic s hs =
      progressionWeight L 1 *
        markedFormula Real.pi R (ramanujanTotientVector s)
          (ramanujanVonMangoldtVector s) (ramanujanMoebiusVector s) := by
  rw [ramanujanMarkedInverseQuadratic_eq_rankTwo s hs F R hRF hR hXi hD]

end
end RiemannResearch.RH.Pareto
