/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.ArithmeticFiniteFirstLevelCertificate

/-!
# A positive second-level arithmetic certificate

At the single window R = 1/16, this module proves native PSD of the genuine
finite arithmetic approximation with m = 2, N = 2, J = 4, and transfers a
quantitative positive lower bound to the actual arithmetic Haar matrix.
The three unnormalized Haar atoms are (1,1,-1,-1), (1,-1,0,0), and
(0,0,1,-1). Their exact Toeplitz compression is checked entry by entry.

The full signed range-two von Mangoldt sum, polar contribution, live
screwLinearCoefficient, and four archimedean modes are retained. An
auxiliary model changes only the linear coefficient to 269/100; an exact
sum-of-squares comparison proves that its quadratic lies below the genuine
finite quadratic. The zeroth archimedean exponential cancels one polar
exponential exactly in the normalized primitive, leaving sixteen
exponential values bounded with rational twelfth-order Taylor estimates.

The final lower bound is 21/100000000 times the sum of squares of the three
Haar coefficients. The tail transfer uses q_approx <= q_actual. Neither
all-level arithmetic positivity, completed-Weil positivity, nor RH is asserted.

Source: user-provided argument and the canonical RH continuation v42 support
the second-level Toeplitz/SOS strategy and the proposed arithmetic parameters.
The rational enclosures here are proved from Mathlib's Real.exp_bound.
-/

open scoped BigOperators
namespace RiemannResearch.RH.PrimeGapCurvature
noncomputable section

def finiteDyadicHaarIndexTwoRoot : FiniteDyadicHaarIndex 2 := ⟨0, 0⟩
def finiteDyadicHaarIndexTwoLeft : FiniteDyadicHaarIndex 2 := ⟨1, 0⟩
def finiteDyadicHaarIndexTwoRight : FiniteDyadicHaarIndex 2 := ⟨1, 1⟩

theorem finiteDyadicHaarIndex_two_cases (i : FiniteDyadicHaarIndex 2) :
    i = finiteDyadicHaarIndexTwoRoot ∨
    i = finiteDyadicHaarIndexTwoLeft ∨
    i = finiteDyadicHaarIndexTwoRight := by
  rcases i with ⟨l, q⟩
  fin_cases l <;> fin_cases q <;>
    simp [finiteDyadicHaarIndexTwoRoot, finiteDyadicHaarIndexTwoLeft,
      finiteDyadicHaarIndexTwoRight]

theorem finiteDyadicHaarIndex_two_univ :
    (Finset.univ : Finset (FiniteDyadicHaarIndex 2)) =
      {finiteDyadicHaarIndexTwoRoot, finiteDyadicHaarIndexTwoLeft,
        finiteDyadicHaarIndexTwoRight} := by
  ext i
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  exact finiteDyadicHaarIndex_two_cases i

theorem finiteDyadicHaarAtom_two_root :
    finiteDyadicHaarAtom 2 0 0 = ![(1 : ℝ), 1, -1, -1] := by
  funext j
  fin_cases j <;> norm_num [finiteDyadicHaarAtom]

theorem finiteDyadicHaarAtom_two_left :
    finiteDyadicHaarAtom 2 1 0 = ![(1 : ℝ), -1, 0, 0] := by
  funext j
  fin_cases j <;> norm_num [finiteDyadicHaarAtom]

theorem finiteDyadicHaarAtom_two_right :
    finiteDyadicHaarAtom 2 1 1 = ![(0 : ℝ), 0, 1, -1] := by
  funext j
  fin_cases j <;> norm_num [finiteDyadicHaarAtom]


def secondLevelToeplitzKernel (t0 t1 t2 t3 : ℝ) :
    Matrix (Fin (2 ^ 2)) (Fin (2 ^ 2)) ℝ :=
  ![![t0,t1,t2,t3], ![t1,t0,t1,t2], ![t2,t1,t0,t1], ![t3,t2,t1,t0]]

theorem secondLevelToeplitzCompression_root_root
    (t0 t1 t2 t3 : ℝ) :
    finiteDyadicHaarCompression 2 (secondLevelToeplitzKernel t0 t1 t2 t3)
      finiteDyadicHaarIndexTwoRoot finiteDyadicHaarIndexTwoRoot =
      4*t0+2*t1-4*t2-2*t3 := by
  rw [finiteDyadicHaarCompression_apply]
  change (∑ i : Fin 4, finiteDyadicHaarAtom 2 0 0 i *
    ∑ j : Fin 4, secondLevelToeplitzKernel t0 t1 t2 t3 i j *
      finiteDyadicHaarAtom 2 0 0 j) = _
  norm_num [Fin.sum_univ_succ, finiteDyadicHaarAtom, secondLevelToeplitzKernel]
  ring

theorem secondLevelToeplitzCompression_root_left
    (t0 t1 t2 t3 : ℝ) :
    finiteDyadicHaarCompression 2 (secondLevelToeplitzKernel t0 t1 t2 t3)
      finiteDyadicHaarIndexTwoRoot finiteDyadicHaarIndexTwoLeft =
      t1-t3 := by
  rw [finiteDyadicHaarCompression_apply]
  change (∑ i : Fin 4, finiteDyadicHaarAtom 2 0 0 i *
    ∑ j : Fin 4, secondLevelToeplitzKernel t0 t1 t2 t3 i j *
      finiteDyadicHaarAtom 2 1 0 j) = _
  norm_num [Fin.sum_univ_succ, finiteDyadicHaarAtom, secondLevelToeplitzKernel]
  ring

theorem secondLevelToeplitzCompression_root_right
    (t0 t1 t2 t3 : ℝ) :
    finiteDyadicHaarCompression 2 (secondLevelToeplitzKernel t0 t1 t2 t3)
      finiteDyadicHaarIndexTwoRoot finiteDyadicHaarIndexTwoRight =
      t1-t3 := by
  rw [finiteDyadicHaarCompression_apply]
  change (∑ i : Fin 4, finiteDyadicHaarAtom 2 0 0 i *
    ∑ j : Fin 4, secondLevelToeplitzKernel t0 t1 t2 t3 i j *
      finiteDyadicHaarAtom 2 1 1 j) = _
  norm_num [Fin.sum_univ_succ, finiteDyadicHaarAtom, secondLevelToeplitzKernel]
  ring

theorem secondLevelToeplitzCompression_left_root
    (t0 t1 t2 t3 : ℝ) :
    finiteDyadicHaarCompression 2 (secondLevelToeplitzKernel t0 t1 t2 t3)
      finiteDyadicHaarIndexTwoLeft finiteDyadicHaarIndexTwoRoot =
      t1-t3 := by
  rw [finiteDyadicHaarCompression_apply]
  change (∑ i : Fin 4, finiteDyadicHaarAtom 2 1 0 i *
    ∑ j : Fin 4, secondLevelToeplitzKernel t0 t1 t2 t3 i j *
      finiteDyadicHaarAtom 2 0 0 j) = _
  norm_num [Fin.sum_univ_succ, finiteDyadicHaarAtom, secondLevelToeplitzKernel]
  ring

theorem secondLevelToeplitzCompression_left_left
    (t0 t1 t2 t3 : ℝ) :
    finiteDyadicHaarCompression 2 (secondLevelToeplitzKernel t0 t1 t2 t3)
      finiteDyadicHaarIndexTwoLeft finiteDyadicHaarIndexTwoLeft =
      2*t0-2*t1 := by
  rw [finiteDyadicHaarCompression_apply]
  change (∑ i : Fin 4, finiteDyadicHaarAtom 2 1 0 i *
    ∑ j : Fin 4, secondLevelToeplitzKernel t0 t1 t2 t3 i j *
      finiteDyadicHaarAtom 2 1 0 j) = _
  norm_num [Fin.sum_univ_succ, finiteDyadicHaarAtom, secondLevelToeplitzKernel]
  ring

theorem secondLevelToeplitzCompression_left_right
    (t0 t1 t2 t3 : ℝ) :
    finiteDyadicHaarCompression 2 (secondLevelToeplitzKernel t0 t1 t2 t3)
      finiteDyadicHaarIndexTwoLeft finiteDyadicHaarIndexTwoRight =
      2*t2-t1-t3 := by
  rw [finiteDyadicHaarCompression_apply]
  change (∑ i : Fin 4, finiteDyadicHaarAtom 2 1 0 i *
    ∑ j : Fin 4, secondLevelToeplitzKernel t0 t1 t2 t3 i j *
      finiteDyadicHaarAtom 2 1 1 j) = _
  norm_num [Fin.sum_univ_succ, finiteDyadicHaarAtom, secondLevelToeplitzKernel]
  ring

theorem secondLevelToeplitzCompression_right_root
    (t0 t1 t2 t3 : ℝ) :
    finiteDyadicHaarCompression 2 (secondLevelToeplitzKernel t0 t1 t2 t3)
      finiteDyadicHaarIndexTwoRight finiteDyadicHaarIndexTwoRoot =
      t1-t3 := by
  rw [finiteDyadicHaarCompression_apply]
  change (∑ i : Fin 4, finiteDyadicHaarAtom 2 1 1 i *
    ∑ j : Fin 4, secondLevelToeplitzKernel t0 t1 t2 t3 i j *
      finiteDyadicHaarAtom 2 0 0 j) = _
  norm_num [Fin.sum_univ_succ, finiteDyadicHaarAtom, secondLevelToeplitzKernel]
  ring

theorem secondLevelToeplitzCompression_right_left
    (t0 t1 t2 t3 : ℝ) :
    finiteDyadicHaarCompression 2 (secondLevelToeplitzKernel t0 t1 t2 t3)
      finiteDyadicHaarIndexTwoRight finiteDyadicHaarIndexTwoLeft =
      2*t2-t1-t3 := by
  rw [finiteDyadicHaarCompression_apply]
  change (∑ i : Fin 4, finiteDyadicHaarAtom 2 1 1 i *
    ∑ j : Fin 4, secondLevelToeplitzKernel t0 t1 t2 t3 i j *
      finiteDyadicHaarAtom 2 1 0 j) = _
  norm_num [Fin.sum_univ_succ, finiteDyadicHaarAtom, secondLevelToeplitzKernel]
  ring

theorem secondLevelToeplitzCompression_right_right
    (t0 t1 t2 t3 : ℝ) :
    finiteDyadicHaarCompression 2 (secondLevelToeplitzKernel t0 t1 t2 t3)
      finiteDyadicHaarIndexTwoRight finiteDyadicHaarIndexTwoRight =
      2*t0-2*t1 := by
  rw [finiteDyadicHaarCompression_apply]
  change (∑ i : Fin 4, finiteDyadicHaarAtom 2 1 1 i *
    ∑ j : Fin 4, secondLevelToeplitzKernel t0 t1 t2 t3 i j *
      finiteDyadicHaarAtom 2 1 1 j) = _
  norm_num [Fin.sum_univ_succ, finiteDyadicHaarAtom, secondLevelToeplitzKernel]
  ring


def secondLevelHaarMatrix (a b d e : ℝ) :
    Matrix (FiniteDyadicHaarIndex 2) (FiniteDyadicHaarIndex 2) ℝ :=
  fun i j => if i = finiteDyadicHaarIndexTwoRoot then
    if j = finiteDyadicHaarIndexTwoRoot then a else b
  else if j = finiteDyadicHaarIndexTwoRoot then b
  else if i = j then d else e

def secondLevelHaarForm (a b d e x y z : ℝ) : ℝ :=
  a*x^2+2*b*x*y+2*b*x*z+d*y^2+2*e*y*z+d*z^2

theorem secondLevelHaarMatrix_quadratic (a b d e : ℝ)
    (c : FiniteDyadicHaarIndex 2 → ℝ) :
    dotProduct c ((secondLevelHaarMatrix a b d e).mulVec c) =
      secondLevelHaarForm a b d e (c finiteDyadicHaarIndexTwoRoot)
        (c finiteDyadicHaarIndexTwoLeft) (c finiteDyadicHaarIndexTwoRight) := by
  simp [dotProduct, Matrix.mulVec, finiteDyadicHaarIndex_two_univ,
    secondLevelHaarMatrix, secondLevelHaarForm,
    finiteDyadicHaarIndexTwoRoot, finiteDyadicHaarIndexTwoLeft,
    finiteDyadicHaarIndexTwoRight]
  ring

theorem secondLevelToeplitzCompression_eq (t0 t1 t2 t3 : ℝ) :
    finiteDyadicHaarCompression 2 (secondLevelToeplitzKernel t0 t1 t2 t3) =
      secondLevelHaarMatrix (4*t0+2*t1-4*t2-2*t3)
        (t1-t3) (2*t0-2*t1) (2*t2-t1-t3) := by
  ext i j
  rcases finiteDyadicHaarIndex_two_cases i with rfl | rfl | rfl <;>
    rcases finiteDyadicHaarIndex_two_cases j with rfl | rfl | rfl <;>
    simp only [secondLevelToeplitzCompression_root_root,
      secondLevelToeplitzCompression_root_left,
      secondLevelToeplitzCompression_root_right,
      secondLevelToeplitzCompression_left_root,
      secondLevelToeplitzCompression_left_left,
      secondLevelToeplitzCompression_left_right,
      secondLevelToeplitzCompression_right_root,
      secondLevelToeplitzCompression_right_left,
      secondLevelToeplitzCompression_right_right] <;>
    norm_num [secondLevelHaarMatrix, finiteDyadicHaarIndexTwoRoot,
      finiteDyadicHaarIndexTwoLeft, finiteDyadicHaarIndexTwoRight]

theorem secondLevelToeplitz_relation (t0 t1 t2 t3 : ℝ) :
    (4*t0+2*t1-4*t2-2*t3) - 4*(t1-t3) =
      2*((2*t0-2*t1)-(2*t2-t1-t3)) := by ring

theorem secondLevelHaarForm_sos (a b d e x y z : ℝ) :
    4*secondLevelHaarForm a b d e x y z =
      4*(a+4*b)*x^2 - b*(4*x-y-z)^2 +
      (2*(d+e)+b)*(y+z)^2 + 2*(d-e)*(y-z)^2 := by
  unfold secondLevelHaarForm
  ring

theorem secondLevelHaarForm_nonneg {a b d e : ℝ}
    (ha : 0 ≤ a+4*b) (hb : b ≤ 0)
    (hs : 0 ≤ 2*(d+e)+b) (hd : 0 ≤ d-e) (x y z : ℝ) :
    0 ≤ secondLevelHaarForm a b d e x y z := by
  have h1 := mul_nonneg ha (sq_nonneg x)
  have h2 := mul_nonneg (neg_nonneg.mpr hb) (sq_nonneg (4*x-y-z))
  have h3 := mul_nonneg hs (sq_nonneg (y+z))
  have h4 := mul_nonneg hd (sq_nonneg (y-z))
  linarith [secondLevelHaarForm_sos a b d e x y z]

theorem secondLevelHaarForm_lower_of_intervals {a b d e : ℝ}
    (ha : 310/100000000 ≤ a) (hb : -(72/100000000) ≤ b)
    (hb' : b ≤ -(70/100000000)) (hd : 177/100000000 ≤ d)
    (he : -(120/100000000) ≤ e) (he' : e ≤ -(119/100000000))
    (x y z : ℝ) :
    (21/100000000)*(x^2+y^2+z^2) ≤
      secondLevelHaarForm a b d e x y z := by
  have h1 : 0 ≤ (a+4*b-22/100000000)*x^2 :=
    mul_nonneg (by linarith) (sq_nonneg x)
  have h2 : 0 ≤ (-b-70/100000000)*(4*x-y-z)^2 :=
    mul_nonneg (by linarith) (sq_nonneg (4*x-y-z))
  have h3 : 0 ≤ (2*(d+e)+b-42/100000000)*(y+z)^2 :=
    mul_nonneg (by linarith) (sq_nonneg (y+z))
  have h4 : 0 ≤ (2*(d-e)-592/100000000)*(y-z)^2 :=
    mul_nonneg (by linarith) (sq_nonneg (y-z))
  nlinarith only [secondLevelHaarForm_sos a b d e x y z,
    h1, h2, h3, h4, sq_nonneg x, sq_nonneg (4*x-y-z), sq_nonneg (y-z)]

end
end RiemannResearch.RH.PrimeGapCurvature

namespace RiemannResearch.RH
open RiemannResearch.Analysis RiemannResearch.RH.PrimeGapCurvature
noncomputable section

/-- Only the live linear coefficient is replaced; all signed finite pieces remain. -/
def secondLevelArithmeticCell (C b₁ d₁ b₂ d₂ : ℝ) : ℝ :=
  screwPolarCell b₁ d₁ b₂ d₂ +
    (∑ n ∈ Finset.range 2, primePowerHingeCell n b₁ d₁ b₂ d₂) +
    C * absCell b₁ d₁ b₂ d₂ -
    ∑ k ∈ Finset.range 4, archimedeanScrewCell k b₁ d₁ b₂ d₂

def secondLevelRawPrimitive (C t : ℝ) : ℝ :=
  -16*(Real.exp (t/2)+Real.exp (-t/2)) + 4*t^2 +
    C*hingeKernelSecondPrimitive 0 t +
    ∑ k ∈ Finset.range 4,
      4*archimedeanWeight k*
        (exponentialAbsSecondPrimitive (archimedeanRate k) t - t^2/2)

def secondLevelPrimitive (C u : ℝ) : ℝ :=
  16+8*u+2*u^2+(C/6)*u^3-16*Real.exp (u/2) +
    ∑ q ∈ ({5,9,13} : Finset ℕ),
      ((16/(q : ℝ)^4)*(Real.exp (-(q : ℝ)*u/2)-1+(q : ℝ)*u/2) -
        2*u^2/(q : ℝ)^2)

theorem secondLevelPrimitive_zero (C : ℝ) :
    secondLevelPrimitive C 0 = 0 := by
  norm_num [secondLevelPrimitive]

theorem secondLevelPrimitive_eq_raw (C t : ℝ) :
    secondLevelPrimitive C |t| =
      secondLevelRawPrimitive C t - secondLevelRawPrimitive C 0 := by
  by_cases ht : 0 ≤ t
  · norm_num [secondLevelPrimitive, secondLevelRawPrimitive,
      hingeKernelSecondPrimitive, exponentialAbsSecondPrimitive,
      archimedeanRate, archimedeanWeight, Finset.sum_range_succ,
      abs_of_nonneg ht, max_eq_left ht,
      max_eq_right (show -t ≤ 0 by linarith)]
    ring
  · have ht' : t ≤ 0 := le_of_not_ge ht
    norm_num [secondLevelPrimitive, secondLevelRawPrimitive,
      hingeKernelSecondPrimitive, exponentialAbsSecondPrimitive,
      archimedeanRate, archimedeanWeight, Finset.sum_range_succ,
      abs_of_nonpos ht', max_eq_right ht',
      max_eq_left (show 0 ≤ -t by linarith)]
    ring

theorem secondLevelArithmeticCell_eq_primitive (C b₁ d₁ b₂ d₂ : ℝ) :
    secondLevelArithmeticCell C b₁ d₁ b₂ d₂ =
      secondPrimitiveCell (fun t => secondLevelPrimitive C |t|) b₁ d₁ b₂ d₂ := by
  simp only [secondPrimitiveCell, secondLevelPrimitive_eq_raw]
  norm_num [secondLevelArithmeticCell, secondLevelRawPrimitive,
    screwPolarCell, exponentialCell, absCell, secondPrimitiveCell,
    primePowerHingeCell, primePowerWeight, archimedeanScrewCell,
    exponentialAbsCell, Finset.sum_range_succ]
  ring


def secondLevelCellKernel (C R : ℝ) : Matrix (Fin (2^2)) (Fin (2^2)) ℝ :=
  secondLevelToeplitzKernel
    (2*secondLevelPrimitive C (R/2))
    (secondLevelPrimitive C R-2*secondLevelPrimitive C (R/2))
    (secondLevelPrimitive C (3*R/2)-2*secondLevelPrimitive C R+
      secondLevelPrimitive C (R/2))
    (secondLevelPrimitive C (2*R)-2*secondLevelPrimitive C (3*R/2)+
      secondLevelPrimitive C R)

theorem secondLevelArithmeticCell_grid (C : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    (fun i j : Fin (2^2) =>
      secondLevelArithmeticCell C
        (dyadicCellLeft R 2 i) (dyadicCellRight R 2 i)
        (dyadicCellLeft R 2 j) (dyadicCellRight R 2 j)) =
      secondLevelCellKernel C R := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    rw [secondLevelArithmeticCell_eq_primitive] <;>
    norm_num [dyadicCellLeft, dyadicCellRight, dyadicCellWidth,
      secondPrimitiveCell, secondLevelCellKernel, secondLevelToeplitzKernel] <;>
    ring_nf <;>
    simp only [abs_mul, abs_of_nonneg hR] <;>
    norm_num [secondLevelPrimitive_zero, abs_of_nonneg hR] <;> ring

def secondLevelCoefficientA (C R : ℝ) : ℝ :=
  8*secondLevelPrimitive C R-2*secondLevelPrimitive C (2*R)
def secondLevelCoefficientB (C R : ℝ) : ℝ :=
  -2*secondLevelPrimitive C (R/2)+2*secondLevelPrimitive C (3*R/2)-
    secondLevelPrimitive C (2*R)
def secondLevelCoefficientD (C R : ℝ) : ℝ :=
  8*secondLevelPrimitive C (R/2)-2*secondLevelPrimitive C R
def secondLevelCoefficientE (C R : ℝ) : ℝ :=
  4*secondLevelPrimitive C (R/2)-6*secondLevelPrimitive C R+
    4*secondLevelPrimitive C (3*R/2)-secondLevelPrimitive C (2*R)

def secondLevelHaarModel (C R : ℝ) :
    Matrix (FiniteDyadicHaarIndex 2) (FiniteDyadicHaarIndex 2) ℝ :=
  secondLevelHaarMatrix (secondLevelCoefficientA C R) (secondLevelCoefficientB C R)
    (secondLevelCoefficientD C R) (secondLevelCoefficientE C R)

theorem secondLevelCellKernel_compression (C R : ℝ) :
    finiteDyadicHaarCompression 2 (secondLevelCellKernel C R) =
      secondLevelHaarModel C R := by
  rw [secondLevelCellKernel, secondLevelToeplitzCompression_eq]
  unfold secondLevelHaarModel secondLevelCoefficientA secondLevelCoefficientB
    secondLevelCoefficientD secondLevelCoefficientE
  congr 1 <;> ring

theorem arithmeticScrewApproxHaarMatrix_two_eq_model
    {R : ℝ} (hR : 0 ≤ R) :
    arithmeticScrewApproxHaarMatrix R 2 2 4 =
      secondLevelHaarModel screwLinearCoefficient R := by
  rw [← secondLevelCellKernel_compression]
  unfold arithmeticScrewApproxHaarMatrix
  congr 1
  rw [← secondLevelArithmeticCell_grid screwLinearCoefficient hR]
  ext i j
  exact integral_integral_arithmeticScrewApprox 2 4
    (dyadicCellLeft R 2 i) (dyadicCellRight R 2 i)
    (dyadicCellLeft R 2 j) (dyadicCellRight R 2 j)

def secondLevelForm (C R x y z : ℝ) : ℝ :=
  secondLevelHaarForm (secondLevelCoefficientA C R) (secondLevelCoefficientB C R)
    (secondLevelCoefficientD C R) (secondLevelCoefficientE C R) x y z

theorem secondLevelForm_coefficient_comparison (C C0 R x y z : ℝ) :
    secondLevelForm C R x y z - secondLevelForm C0 R x y z =
      (C0-C)*R^3*(((2*y+3*x)^2+(2*z+3*x)^2)/24+7*x^2/12) := by
  unfold secondLevelForm secondLevelHaarForm secondLevelCoefficientA
    secondLevelCoefficientB secondLevelCoefficientD secondLevelCoefficientE
    secondLevelPrimitive
  ring

theorem secondLevelForm_antitone {C C0 R : ℝ}
    (hC : C ≤ C0) (hR : 0 ≤ R) (x y z : ℝ) :
    secondLevelForm C0 R x y z ≤ secondLevelForm C R x y z := by
  apply sub_nonneg.mp
  rw [secondLevelForm_coefficient_comparison]
  exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hC) (pow_nonneg hR 3))
    (by positivity)

theorem secondLevelHaarModel_quadratic (C R : ℝ)
    (c : FiniteDyadicHaarIndex 2 → ℝ) :
    dotProduct c ((secondLevelHaarModel C R).mulVec c) =
      secondLevelForm C R (c finiteDyadicHaarIndexTwoRoot)
        (c finiteDyadicHaarIndexTwoLeft) (c finiteDyadicHaarIndexTwoRight) :=
  secondLevelHaarMatrix_quadratic _ _ _ _ c

theorem secondLevelPrimitive_sixteenth_1_bounds :
    (-36169/100000000000 : ℝ) ≤ secondLevelPrimitive (269/100) (1/32) ∧
    secondLevelPrimitive (269/100) (1/32) ≤ (-36168/100000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (1/64 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h1 := Real.exp_bound (x := (-5/64 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h2 := Real.exp_bound (x := (-9/64 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h3 := Real.exp_bound (x := (-13/64 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3
  norm_num [secondLevelPrimitive]
  constructor <;>
    linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
      (abs_le.mp h1).1, (abs_le.mp h1).2,
      (abs_le.mp h2).1, (abs_le.mp h2).2,
      (abs_le.mp h3).1, (abs_le.mp h3).2]

theorem secondLevelPrimitive_sixteenth_2_bounds :
    (-233643/100000000000 : ℝ) ≤ secondLevelPrimitive (269/100) (2/32) ∧
    secondLevelPrimitive (269/100) (2/32) ≤ (-233642/100000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (2/64 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h1 := Real.exp_bound (x := (-10/64 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h2 := Real.exp_bound (x := (-18/64 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h3 := Real.exp_bound (x := (-26/64 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3
  norm_num [secondLevelPrimitive]
  constructor <;>
    linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
      (abs_le.mp h1).1, (abs_le.mp h1).2,
      (abs_le.mp h2).1, (abs_le.mp h2).2,
      (abs_le.mp h3).1, (abs_le.mp h3).2]

theorem secondLevelPrimitive_sixteenth_3_bounds :
    (-616721/100000000000 : ℝ) ≤ secondLevelPrimitive (269/100) (3/32) ∧
    secondLevelPrimitive (269/100) (3/32) ≤ (-616720/100000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (3/64 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h1 := Real.exp_bound (x := (-15/64 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h2 := Real.exp_bound (x := (-27/64 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h3 := Real.exp_bound (x := (-39/64 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3
  norm_num [secondLevelPrimitive]
  constructor <;>
    linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
      (abs_le.mp h1).1, (abs_le.mp h1).2,
      (abs_le.mp h2).1, (abs_le.mp h2).2,
      (abs_le.mp h3).1, (abs_le.mp h3).2]

theorem secondLevelPrimitive_sixteenth_4_bounds :
    (-1090251/100000000000 : ℝ) ≤ secondLevelPrimitive (269/100) (4/32) ∧
    secondLevelPrimitive (269/100) (4/32) ≤ (-1090250/100000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (4/64 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h1 := Real.exp_bound (x := (-20/64 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h2 := Real.exp_bound (x := (-36/64 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h3 := Real.exp_bound (x := (-52/64 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3
  norm_num [secondLevelPrimitive]
  constructor <;>
    linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
      (abs_le.mp h1).1, (abs_le.mp h1).2,
      (abs_le.mp h2).1, (abs_le.mp h2).2,
      (abs_le.mp h3).1, (abs_le.mp h3).2]

theorem secondLevelCoefficientA_sixteenth_bounds :
    (310/100000000 : ℝ) ≤ secondLevelCoefficientA (269/100) (1/16) ∧
    secondLevelCoefficientA (269/100) (1/16) ≤ (312/100000000 : ℝ) := by
  have h1 := secondLevelPrimitive_sixteenth_1_bounds
  have h2 := secondLevelPrimitive_sixteenth_2_bounds
  have h3 := secondLevelPrimitive_sixteenth_3_bounds
  have h4 := secondLevelPrimitive_sixteenth_4_bounds
  norm_num at h1 h2 h3 h4
  norm_num [secondLevelCoefficientA]
  constructor <;> linarith

theorem secondLevelCoefficientB_sixteenth_bounds :
    (-72/100000000 : ℝ) ≤ secondLevelCoefficientB (269/100) (1/16) ∧
    secondLevelCoefficientB (269/100) (1/16) ≤ (-70/100000000 : ℝ) := by
  have h1 := secondLevelPrimitive_sixteenth_1_bounds
  have h2 := secondLevelPrimitive_sixteenth_2_bounds
  have h3 := secondLevelPrimitive_sixteenth_3_bounds
  have h4 := secondLevelPrimitive_sixteenth_4_bounds
  norm_num at h1 h2 h3 h4
  norm_num [secondLevelCoefficientB]
  constructor <;> linarith

theorem secondLevelCoefficientD_sixteenth_bounds :
    (177/100000000 : ℝ) ≤ secondLevelCoefficientD (269/100) (1/16) ∧
    secondLevelCoefficientD (269/100) (1/16) ≤ (179/100000000 : ℝ) := by
  have h1 := secondLevelPrimitive_sixteenth_1_bounds
  have h2 := secondLevelPrimitive_sixteenth_2_bounds
  have h3 := secondLevelPrimitive_sixteenth_3_bounds
  have h4 := secondLevelPrimitive_sixteenth_4_bounds
  norm_num at h1 h2 h3 h4
  norm_num [secondLevelCoefficientD]
  constructor <;> linarith

theorem secondLevelCoefficientE_sixteenth_bounds :
    (-120/100000000 : ℝ) ≤ secondLevelCoefficientE (269/100) (1/16) ∧
    secondLevelCoefficientE (269/100) (1/16) ≤ (-119/100000000 : ℝ) := by
  have h1 := secondLevelPrimitive_sixteenth_1_bounds
  have h2 := secondLevelPrimitive_sixteenth_2_bounds
  have h3 := secondLevelPrimitive_sixteenth_3_bounds
  have h4 := secondLevelPrimitive_sixteenth_4_bounds
  norm_num at h1 h2 h3 h4
  norm_num [secondLevelCoefficientE]
  constructor <;> linarith

theorem secondLevelForm_sixteenth_rational_lower (x y z : ℝ) :
    (21/100000000)*(x^2+y^2+z^2) ≤
      secondLevelForm (269/100) (1/16) x y z := by
  exact secondLevelHaarForm_lower_of_intervals
    secondLevelCoefficientA_sixteenth_bounds.1
    (by linarith [secondLevelCoefficientB_sixteenth_bounds.1])
    (by linarith [secondLevelCoefficientB_sixteenth_bounds.2])
    secondLevelCoefficientD_sixteenth_bounds.1
    (by linarith [secondLevelCoefficientE_sixteenth_bounds.1])
    (by linarith [secondLevelCoefficientE_sixteenth_bounds.2]) x y z

/-- Exact finite comparison; only the gamma/pole coefficient changes. -/
theorem arithmeticScrewApproxHaarMatrix_two_quadratic_comparison
    {R : ℝ} (hR : 0 ≤ R) (c : FiniteDyadicHaarIndex 2 → ℝ) :
    dotProduct c ((arithmeticScrewApproxHaarMatrix R 2 2 4).mulVec c) -
      dotProduct c ((secondLevelHaarModel (269/100) R).mulVec c) =
    (269/100-screwLinearCoefficient)*R^3*
      (((2*c finiteDyadicHaarIndexTwoLeft+3*c finiteDyadicHaarIndexTwoRoot)^2+
        (2*c finiteDyadicHaarIndexTwoRight+3*c finiteDyadicHaarIndexTwoRoot)^2)/24+
        7*(c finiteDyadicHaarIndexTwoRoot)^2/12) := by
  rw [arithmeticScrewApproxHaarMatrix_two_eq_model hR,
    secondLevelHaarModel_quadratic, secondLevelHaarModel_quadratic]
  exact secondLevelForm_coefficient_comparison _ _ _ _ _ _

/-- Positive quantitative margin for the genuine signed finite approximation. -/
theorem arithmeticScrewApproxHaarMatrix_sixteenth_level_two_lower
    (c : FiniteDyadicHaarIndex 2 → ℝ) :
    (21/100000000)*((c finiteDyadicHaarIndexTwoRoot)^2+
      (c finiteDyadicHaarIndexTwoLeft)^2+(c finiteDyadicHaarIndexTwoRight)^2) ≤
    dotProduct c ((arithmeticScrewApproxHaarMatrix (1/16) 2 2 4).mulVec c) := by
  rw [arithmeticScrewApproxHaarMatrix_two_eq_model (by norm_num),
    secondLevelHaarModel_quadratic]
  exact (secondLevelForm_sixteenth_rational_lower _ _ _).trans
    (secondLevelForm_antitone screwLinearCoefficient_le_269_div_100
      (by norm_num) _ _ _)

/-- The genuine m=2 approximation at the single window R=1/16 is PSD. -/
theorem arithmeticScrewApproxHaarMatrix_sixteenth_level_two_posSemidef :
    (arithmeticScrewApproxHaarMatrix (1/16) 2 2 4).PosSemidef := by
  rw [arithmeticScrewApproxHaarMatrix_posSemidef_iff]
  intro c
  exact le_trans (by positivity)
    (arithmeticScrewApproxHaarMatrix_sixteenth_level_two_lower c)

/-- The signed tail direction transfers the positive margin to the actual
arithmetic matrix, at this window and level only. -/
theorem arithmeticScrewHaarMatrix_sixteenth_two_lower
    (c : FiniteDyadicHaarIndex 2 → ℝ) :
    (21/100000000)*((c finiteDyadicHaarIndexTwoRoot)^2+
      (c finiteDyadicHaarIndexTwoLeft)^2+(c finiteDyadicHaarIndexTwoRight)^2) ≤
    dotProduct c ((arithmeticScrewHaarMatrix (1/16) 2).mulVec c) :=
  (arithmeticScrewApproxHaarMatrix_sixteenth_level_two_lower c).trans
    (arithmeticScrewApproxHaarMatrix_quadratic_le (by norm_num) 2 2 4
      arithmeticScrewApprox_sixteenth_cutoff c)

/-- Native PSD of the actual m=2 arithmetic Haar matrix. This is not an
all-level arithmetic positivity theorem, completed-Weil positivity, or RH. -/
theorem arithmeticScrewHaarMatrix_sixteenth_two_posSemidef :
    (arithmeticScrewHaarMatrix (1/16) 2).PosSemidef :=
  arithmeticScrewHaarMatrix_posSemidef_of_approx_posSemidef
    (by norm_num) 2 2 4 arithmeticScrewApprox_sixteenth_cutoff
    arithmeticScrewApproxHaarMatrix_sixteenth_level_two_posSemidef
end
end RiemannResearch.RH
