import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
An exact finite-dimensional rank-two Woodbury reduction.

The matrix identity and the inverse equation are genuine hypotheses.  The
marked quadratic identity is derived from them; it is not assumed.  No
positivity or analytic convergence assertion is included here.

Source: user-provided Ramanujan / Green / Schur calculation, 22 September 2026.
The argument supports this finite algebraic reduction. Its arithmetic
consumer is the marked inverse Gram formula for the Pareto packet dictionary.
The cotangent evaluation of that Gram matrix is not supplied here.
-/

noncomputable section

open Matrix

namespace RiemannResearch.LinearAlgebra.RankTwoWoodbury

/-- The scalar elimination needed after taking three pairings of the
inverse equation.  The small system has coefficient matrix `[[b,a],[c,b]]`.
-/
theorem scalar_system_quadratic
    (a b c u v z p m s t : ℝ)
    (hp : p ≠ 0) (hD : a * c - b ^ 2 ≠ 0)
    (hs : b * s + a * t = 2 * v)
    (ht : c * s + b * t = 2 * z)
    (hm : p * m + (z * s + v * t) / 2 = u) :
    m = (u - (c * v ^ 2 - 2 * b * v * z + a * z ^ 2) /
      (a * c - b ^ 2)) / p := by
  have hs' : (a * c - b ^ 2) * s = 2 * (a * z - b * v) := by
    nlinarith only [congrArg (fun x : ℝ => a * x) ht,
      congrArg (fun x : ℝ => b * x) hs]
  have ht' : (a * c - b ^ 2) * t = 2 * (c * v - b * z) := by
    nlinarith only [congrArg (fun x : ℝ => c * x) hs,
      congrArg (fun x : ℝ => b * x) ht]
  have htotal : (a * c - b ^ 2) * (p * m - u) +
      (c * v ^ 2 - 2 * b * v * z + a * z ^ 2) = 0 := by
    nlinarith only [congrArg (fun x : ℝ => (a * c - b ^ 2) * x) hm,
      congrArg (fun x : ℝ => z * x) hs',
      congrArg (fun x : ℝ => v * x) ht']
  have hQ : (c * v ^ 2 - 2 * b * v * z + a * z ^ 2) /
      (a * c - b ^ 2) = u - p * m := by
    apply (div_eq_iff hD).2
    nlinarith only [htotal]
  rw [hQ]
  apply (eq_div_iff hp).2
  ring

section FiniteMatrices

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The symmetric rank-two perturbation appearing in the Gram reduction. -/
def rankTwoMatrix (p : ℝ) (F : Matrix ι ι ℝ) (L phi : ι → ℝ) :
    Matrix ι ι ℝ :=
  p • F + (1 / 2 : ℝ) • (vecMulVec L phi + vecMulVec phi L)

omit [DecidableEq ι] in
theorem outer_mulVec_real (r s x : ι → ℝ) :
    vecMulVec r s *ᵥ x = (s ⬝ᵥ x) • r := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply,
    Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [← Finset.mul_sum]
  ring

omit [DecidableEq ι] in
/-- Expansion of the matrix action, deduced from its actual entries. -/
theorem rankTwoMatrix_mulVec (p : ℝ) (F : Matrix ι ι ℝ)
    (L phi x : ι → ℝ) :
    rankTwoMatrix p F L phi *ᵥ x =
      p • (F *ᵥ x) + ((phi ⬝ᵥ x) / 2) • L + ((L ⬝ᵥ x) / 2) • phi := by
  rw [rankTwoMatrix, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.add_mulVec,
    outer_mulVec_real, outer_mulVec_real, smul_add, smul_smul, smul_smul]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The explicit scalar expression for the marked inverse quadratic. -/
def markedFormula (p : ℝ) (R : Matrix ι ι ℝ) (phi L mu : ι → ℝ) : ℝ :=
  let a := phi ⬝ᵥ (R *ᵥ phi)
  let b := phi ⬝ᵥ (R *ᵥ L) + 2 * p
  let c := L ⬝ᵥ (R *ᵥ L)
  let u := mu ⬝ᵥ (R *ᵥ mu)
  let v := mu ⬝ᵥ (R *ᵥ phi)
  let z := mu ⬝ᵥ (R *ᵥ L)
  (u - (c * v ^ 2 - 2 * b * v * z + a * z ^ 2) /
    (a * c - b ^ 2)) / p

/-- A genuine matrix-level Woodbury bridge.  `R * F = 1` supplies an actual
left inverse, and `Rᵀ = R` supplies the required pairing symmetry.  Any
solution of the perturbed system has precisely the displayed quadratic.
-/
theorem solved_marked_quadratic
    (p : ℝ) (F R Xi : Matrix ι ι ℝ) (phi L mu y : ι → ℝ)
    (hRF : R * F = 1) (hR : Rᵀ = R)
    (hXi : Xi = rankTwoMatrix p F L phi)
    (hy : Xi *ᵥ y = mu) (hp : p ≠ 0)
    (hD : (phi ⬝ᵥ (R *ᵥ phi)) * (L ⬝ᵥ (R *ᵥ L)) -
      (phi ⬝ᵥ (R *ᵥ L) + 2 * p) ^ 2 ≠ 0) :
    mu ⬝ᵥ y = markedFormula p R phi L mu := by
  let a : ℝ := phi ⬝ᵥ (R *ᵥ phi)
  let b : ℝ := phi ⬝ᵥ (R *ᵥ L) + 2 * p
  let c : ℝ := L ⬝ᵥ (R *ᵥ L)
  let u : ℝ := mu ⬝ᵥ (R *ᵥ mu)
  let v : ℝ := mu ⬝ᵥ (R *ᵥ phi)
  let z : ℝ := mu ⬝ᵥ (R *ᵥ L)
  let m : ℝ := mu ⬝ᵥ y
  let s : ℝ := phi ⬝ᵥ y
  let t : ℝ := L ⬝ᵥ y
  have hpair (r s : ι → ℝ) : r ⬝ᵥ (R *ᵥ s) = s ⬝ᵥ (R *ᵥ r) := by
    simpa only [hR] using Matrix.dotProduct_transpose_mulVec R r s
  have hleft (x : ι → ℝ) : R *ᵥ (F *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, hRF, Matrix.one_mulVec]
  have hvec : p • y + (s / 2) • (R *ᵥ L) + (t / 2) • (R *ᵥ phi) =
      R *ᵥ mu := by
    have h := congrArg (fun x : ι → ℝ => R *ᵥ x) hy
    rw [hXi, rankTwoMatrix_mulVec] at h
    simpa only [Matrix.mulVec_add, Matrix.mulVec_smul, hleft, s, t] using h
  have hphi := congrArg (fun x : ι → ℝ => phi ⬝ᵥ x) hvec
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at hphi
  rw [hpair phi mu] at hphi
  have hL := congrArg (fun x : ι → ℝ => L ⬝ᵥ x) hvec
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at hL
  rw [hpair L phi, hpair L mu] at hL
  have hmu := congrArg (fun x : ι → ℝ => mu ⬝ᵥ x) hvec
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at hmu
  have hs : b * s + a * t = 2 * v := by
    dsimp only [a, b, s, t, v] at *
    nlinarith only [hphi]
  have ht : c * s + b * t = 2 * z := by
    dsimp only [b, c, s, t, z] at *
    nlinarith only [hL]
  have hm : p * m + (z * s + v * t) / 2 = u := by
    dsimp only [m, s, t, z, v, u] at *
    nlinarith only [hmu]
  change m = (u - (c * v ^ 2 - 2 * b * v * z + a * z ^ 2) /
    (a * c - b ^ 2)) / p
  exact scalar_system_quadratic a b c u v z p m s t hp hD hs ht hm

/-- In particular, any actual right inverse `J` of `Xi` gives the claimed
marked inverse quadratic by taking `y = J *ᵥ mu`. -/
theorem inverse_marked_quadratic
    (p : ℝ) (F R Xi J : Matrix ι ι ℝ) (phi L mu : ι → ℝ)
    (hRF : R * F = 1) (hR : Rᵀ = R)
    (hXi : Xi = rankTwoMatrix p F L phi)
    (hXiJ : Xi * J = 1) (hp : p ≠ 0)
    (hD : (phi ⬝ᵥ (R *ᵥ phi)) * (L ⬝ᵥ (R *ᵥ L)) -
      (phi ⬝ᵥ (R *ᵥ L) + 2 * p) ^ 2 ≠ 0) :
    mu ⬝ᵥ (J *ᵥ mu) = markedFormula p R phi L mu := by
  apply solved_marked_quadratic p F R Xi phi L mu (J *ᵥ mu) hRF hR hXi
  · rw [Matrix.mulVec_mulVec, hXiJ, Matrix.one_mulVec]
  · exact hp
  · exact hD

end FiniteMatrices

end RiemannResearch.LinearAlgebra.RankTwoWoodbury
