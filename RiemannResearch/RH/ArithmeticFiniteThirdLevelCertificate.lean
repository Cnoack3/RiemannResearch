/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.ArithmeticFiniteSecondLevelCertificate

/-!
# A positive third-level arithmetic certificate

At the single window R = 1/16 this module proves a quantitative lower bound
of 1/1000000000 times the sum of the seven Haar coefficient squares, and
native PSD, for the genuine finite arithmetic approximation m = 3, N = 2,
J = 4 and for the actual arithmetic Haar matrix.

The seven unnormalized atoms are ordered root, left, right, q0, q1, q2, q3.
The eight-cell Toeplitz representation is proved against the literal signed
arithmetic-cell definition, retaining the full range-two von Mangoldt sum,
polar correction, live screwLinearCoefficient, and four archimedean modes.
Only the auxiliary coefficient is replaced by 5373/2000; the arithmetic
kernel is not redefined. The sharper upper bound is proved using the Euler
sequence at 1024 and an exponential comparison for log pi.

The published even-grid primitive enclosures and sixteen new odd-grid
twelfth-order exponential estimates supply exact rational interval bounds.
Reflection splits the Haar matrix into odd and even blocks, with coefficient
Gram diag(1,2,2,2,2,2,2), without square roots. Rational unit-triangular shears
make the epsilon-subtracted blocks strictly row diagonally dominant.
The exact eight-cell prefix-sum SOS proves auxiliary <= genuine before any
inequality is applied; q_approx <= q_actual transfers the final margin.

No all-level or all-window arithmetic positivity, completed-Weil positivity,
or RH is asserted.

Source: user-provided canonical continuation v43 and its corrected m=3
paper argument support the Toeplitz, reflection, rational-shear, and SOS
strategy. Numerical enclosures are proved from Mathlib's Real.exp_bound.
-/
set_option maxRecDepth 16384
open scoped BigOperators
namespace RiemannResearch.RH
open RiemannResearch.Analysis RiemannResearch.RH.PrimeGapCurvature
noncomputable section

set_option maxHeartbeats 2000000 in
/-- Exact Euler-constant upper bound for the sharper third-level auxiliary coefficient. -/
theorem eulerMascheroniConstant_le_5778_div_10000 :
    Real.eulerMascheroniConstant ≤ (5778/10000 : ℝ) := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 1024
  have hH : (harmonic 1024 : ℝ) < 375459/50000 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hlog := Real.log_two_gt_d9
  have hlog1024 : Real.log (1024 : ℝ) = 10 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 10 using 1 <;> norm_num
  norm_num [Real.eulerMascheroniSeq'] at h
  rw [hlog1024] at h
  linarith

/-- Exact exponential-comparison upper bound for log pi. -/
theorem log_pi_le_11449_div_10000 :
    Real.log Real.pi ≤ (11449/10000 : ℝ) := by
  have hπ := Real.pi_lt_d4
  have he := Real.exp_one_gt_d9
  have hx := Real.exp_bound (x := (1449/10000 : ℝ))
    (by norm_num) (n := 5) (by norm_num)
  norm_num [Finset.sum_range_succ] at hx
  have hlower := (abs_le.mp hx).1
  have hxpos := Real.exp_pos (1449/10000 : ℝ)
  apply (Real.log_le_iff_le_exp Real.pi_pos).mpr
  have heq :
      Real.exp (11449/10000 : ℝ) =
        Real.exp 1 * Real.exp (1449/10000 : ℝ) := by
    rw [← Real.exp_add]
    congr 1
    norm_num
  rw [heq]
  nlinarith

/-- The live arithmetic coefficient is bounded without altering its definition. -/
theorem screwLinearCoefficient_le_5373_div_2000 :
    screwLinearCoefficient ≤ (5373/2000 : ℝ) := by
  have hg := eulerMascheroniConstant_le_5778_div_10000
  have hl := log_pi_le_11449_div_10000
  have h2 := Real.log_two_lt_d9
  have hπ := Real.pi_lt_d4
  unfold screwLinearCoefficient
  linarith


/-- The seven columns are ordered root, left, right, then the four quarter atoms. -/
def thirdLevelIndex : Fin 7 → FiniteDyadicHaarIndex 3 :=
  ![⟨0,0⟩,⟨1,0⟩,⟨1,1⟩,⟨2,0⟩,⟨2,1⟩,⟨2,2⟩,⟨2,3⟩]

theorem thirdLevelIndex_surjective : Function.Surjective thirdLevelIndex := by
  rintro ⟨l,q⟩
  fin_cases l <;> fin_cases q
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨3,rfl⟩
  · exact ⟨4,rfl⟩
  · exact ⟨5,rfl⟩
  · exact ⟨6,rfl⟩

theorem thirdLevelIndex_injective : Function.Injective thirdLevelIndex := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [thirdLevelIndex, Matrix.cons_val] at h ⊢

def thirdLevelIndexEquiv : Fin 7 ≃ FiniteDyadicHaarIndex 3 :=
  Equiv.ofBijective thirdLevelIndex ⟨thirdLevelIndex_injective,thirdLevelIndex_surjective⟩

def thirdLevelHaarColumns : Matrix (Fin 8) (Fin 7) ℝ :=
  ![![1,1,0,1,0,0,0],![1,1,0,-1,0,0,0],
    ![1,-1,0,0,1,0,0],![1,-1,0,0,-1,0,0],
    ![-1,0,1,0,0,1,0],![-1,0,1,0,0,-1,0],
    ![-1,0,-1,0,0,0,1],![-1,0,-1,0,0,0,-1]]

theorem thirdLevelHaarColumns_eq (i : Fin 8) (j : Fin 7) :
    thirdLevelHaarColumns i j = finiteDyadicHaarMatrix 3 i (thirdLevelIndex j) := by
  fin_cases i <;> fin_cases j <;>
    simp [thirdLevelHaarColumns, finiteDyadicHaarMatrix, thirdLevelIndex,
      finiteDyadicHaarAtom, Matrix.cons_val]

def thirdLevelToeplitzKernel (t : Fin 8 → ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  ![![t 0,t 1,t 2,t 3,t 4,t 5,t 6,t 7],
    ![t 1,t 0,t 1,t 2,t 3,t 4,t 5,t 6],
    ![t 2,t 1,t 0,t 1,t 2,t 3,t 4,t 5],
    ![t 3,t 2,t 1,t 0,t 1,t 2,t 3,t 4],
    ![t 4,t 3,t 2,t 1,t 0,t 1,t 2,t 3],
    ![t 5,t 4,t 3,t 2,t 1,t 0,t 1,t 2],
    ![t 6,t 5,t 4,t 3,t 2,t 1,t 0,t 1],
    ![t 7,t 6,t 5,t 4,t 3,t 2,t 1,t 0]]

def thirdLevelCellValues (C R : ℝ) : Fin 8 → ℝ :=
  ![2*secondLevelPrimitive C (R/4),
    secondLevelPrimitive C (R/2)-2*secondLevelPrimitive C (R/4),
    secondLevelPrimitive C (3*R/4)-2*secondLevelPrimitive C (R/2)+secondLevelPrimitive C (R/4),
    secondLevelPrimitive C R-2*secondLevelPrimitive C (3*R/4)+secondLevelPrimitive C (R/2),
    secondLevelPrimitive C (5*R/4)-2*secondLevelPrimitive C R+secondLevelPrimitive C (3*R/4),
    secondLevelPrimitive C (3*R/2)-2*secondLevelPrimitive C (5*R/4)+secondLevelPrimitive C R,
    secondLevelPrimitive C (7*R/4)-2*secondLevelPrimitive C (3*R/2)+secondLevelPrimitive C (5*R/4),
    secondLevelPrimitive C (2*R)-2*secondLevelPrimitive C (7*R/4)+secondLevelPrimitive C (3*R/2)]

def thirdLevelCellKernel (C R : ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  thirdLevelToeplitzKernel (thirdLevelCellValues C R)

set_option maxHeartbeats 2000000 in
theorem thirdLevelArithmeticCell_grid (C : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    (fun i j : Fin 8 =>
      secondLevelArithmeticCell C
        (dyadicCellLeft R 3 i) (dyadicCellRight R 3 i)
        (dyadicCellLeft R 3 j) (dyadicCellRight R 3 j)) =
      thirdLevelCellKernel C R := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    rw [secondLevelArithmeticCell_eq_primitive] <;>
    norm_num [dyadicCellLeft, dyadicCellRight, dyadicCellWidth,
      secondPrimitiveCell, thirdLevelCellKernel, thirdLevelToeplitzKernel,
      thirdLevelCellValues] <;>
    (try simp only [Matrix.cons_val]) <;>
    ring_nf <;>
    simp only [abs_mul, abs_of_nonneg hR] <;>
    norm_num [secondLevelPrimitive_zero, abs_of_nonneg hR] <;> ring

def thirdLevelHaarModel (C R : ℝ) :
    Matrix (FiniteDyadicHaarIndex 3) (FiniteDyadicHaarIndex 3) ℝ :=
  finiteDyadicHaarCompression 3 (thirdLevelCellKernel C R)

theorem arithmeticScrewApproxHaarMatrix_three_eq_model
    {R : ℝ} (hR : 0 ≤ R) :
    arithmeticScrewApproxHaarMatrix R 3 2 4 =
      thirdLevelHaarModel screwLinearCoefficient R := by
  unfold thirdLevelHaarModel arithmeticScrewApproxHaarMatrix
  congr 1
  rw [← thirdLevelArithmeticCell_grid screwLinearCoefficient hR]
  ext i j
  exact integral_integral_arithmeticScrewApprox 2 4
    (dyadicCellLeft R 3 i) (dyadicCellRight R 3 i)
    (dyadicCellLeft R 3 j) (dyadicCellRight R 3 j)

/-- Literal H-transpose T H against the genuine signed arithmetic-cell definition. -/
theorem thirdLevelHaarModel_reindex (C R : ℝ) :
    (fun i j : Fin 7 => thirdLevelHaarModel C R (thirdLevelIndex i) (thirdLevelIndex j)) =
      thirdLevelHaarColumns.transpose * thirdLevelCellKernel C R * thirdLevelHaarColumns := by
  ext i j
  simp only [thirdLevelHaarModel, finiteDyadicHaarCompression, Matrix.mul_apply,
    Matrix.transpose_apply, thirdLevelHaarColumns_eq]
  rfl


/-- Symmetric seven-dimensional Haar entry pattern. -/
def thirdLevelHaarEntries (a b c d e f g h i j k l m : ℝ) :
    Matrix (Fin 7) (Fin 7) ℝ :=
  ![![a,b,b,c,d,d,c],![b,e,f,g,g,h,i],![b,f,e,i,h,g,g],
    ![c,g,i,j,k,l,m],![d,g,h,k,j,k,l],![d,h,g,l,k,j,k],![c,i,g,m,l,k,j]]

def thirdLevelToeplitzHaar (t : Fin 8 → ℝ) : Matrix (Fin 7) (Fin 7) ℝ :=
  thirdLevelHaarEntries
    (8*t 0+10*t 1+4*t 2-2*t 3-8*t 4-6*t 5-4*t 6-2*t 7)
    (t 1+2*t 2+t 3-t 5-2*t 6-t 7)
    (-t 1+2*t 3-t 7) (2*t 1-t 3-t 5)
    (4*t 0+2*t 1-4*t 2-2*t 3)
    (-t 1-2*t 2+t 3+4*t 4+t 5-2*t 6-t 7)
    (t 1-t 3) (-t 1+2*t 3-t 5) (-t 3+2*t 5-t 7)
    (2*t 0-2*t 1) (-t 1+2*t 2-t 3) (-t 3+2*t 4-t 5) (-t 5+2*t 6-t 7)

set_option maxHeartbeats 2000000 in
theorem thirdLevelToeplitzHaar_eq (t : Fin 8 → ℝ) :
    thirdLevelHaarColumns.transpose * thirdLevelToeplitzKernel t *
      thirdLevelHaarColumns = thirdLevelToeplitzHaar t := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_succ,
      thirdLevelHaarColumns, thirdLevelToeplitzKernel, thirdLevelToeplitzHaar,
      thirdLevelHaarEntries, Matrix.cons_val] <;> ring

/-- Rational reflection coordinates: the odd columns precede the even columns. -/
def thirdLevelReflection : Matrix (Fin 7) (Fin 7) ℝ :=
  ![![1,0,0,0,0,0,0],![0,1,0,0,1,0,0],![0,1,0,0,-1,0,0],
    ![0,0,1,0,0,1,0],![0,0,0,1,0,0,1],![0,0,0,1,0,0,-1],
    ![0,0,1,0,0,-1,0]]

def thirdLevelOddBlock (a b c d e f g h i j k l m : ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  ![![a,2*b,2*c,2*d],![2*b,2*(e+f),2*(g+i),2*(g+h)],
    ![2*c,2*(g+i),2*(j+m),2*(k+l)],![2*d,2*(g+h),2*(k+l),2*(j+k)]]

def thirdLevelEvenBlock (e f g h i j k l m : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  ![![2*(e-f),2*(g-i),2*(g-h)],![2*(g-i),2*(j-m),2*(k-l)],
    ![2*(g-h),2*(k-l),2*(j-k)]]

def thirdLevelBlockDiagonal (O : Matrix (Fin 4) (Fin 4) ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 7) (Fin 7) ℝ :=
  ![![O 0 0,O 0 1,O 0 2,O 0 3,0,0,0],
    ![O 1 0,O 1 1,O 1 2,O 1 3,0,0,0],
    ![O 2 0,O 2 1,O 2 2,O 2 3,0,0,0],
    ![O 3 0,O 3 1,O 3 2,O 3 3,0,0,0],
    ![0,0,0,0,E 0 0,E 0 1,E 0 2],
    ![0,0,0,0,E 1 0,E 1 1,E 1 2],
    ![0,0,0,0,E 2 0,E 2 1,E 2 2]]

set_option maxHeartbeats 2000000 in
theorem thirdLevelReflection_congruence (a b c d e f g h i j k l m : ℝ) :
    thirdLevelReflection.transpose * thirdLevelHaarEntries a b c d e f g h i j k l m *
      thirdLevelReflection =
      thirdLevelBlockDiagonal (thirdLevelOddBlock a b c d e f g h i j k l m)
        (thirdLevelEvenBlock e f g h i j k l m) := by
  ext r s
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  fin_cases r <;> fin_cases s <;>
    simp [Fin.sum_univ_succ,
      thirdLevelReflection, thirdLevelHaarEntries, thirdLevelBlockDiagonal,
      thirdLevelOddBlock, thirdLevelEvenBlock, Matrix.cons_val] <;> ring

theorem thirdLevelReflection_gram :
    thirdLevelReflection.transpose * thirdLevelReflection =
      Matrix.diagonal ![(1 : ℝ),2,2,2,2,2,2] := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_succ,
      thirdLevelReflection, Matrix.diagonal, Matrix.cons_val] <;> norm_num


theorem thirdLevelPrimitive_coefficient_shift (u : ℝ) :
    secondLevelPrimitive (5373/2000) u =
      secondLevelPrimitive (269/100) u - (7/12000)*u^3 := by
  unfold secondLevelPrimitive
  ring

theorem thirdLevelPrimitive_sixteenth_1_bounds :
    (-4987/100000000000 : ℝ) ≤ secondLevelPrimitive (269/100) (1/64) ∧
    secondLevelPrimitive (269/100) (1/64) ≤ (-4986/100000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (1/128 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h1 := Real.exp_bound (x := (-5/128 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h2 := Real.exp_bound (x := (-9/128 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h3 := Real.exp_bound (x := (-13/128 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3
  norm_num [secondLevelPrimitive]
  constructor <;>
    linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
      (abs_le.mp h1).1, (abs_le.mp h1).2,
      (abs_le.mp h2).1, (abs_le.mp h2).2,
      (abs_le.mp h3).1, (abs_le.mp h3).2]

theorem thirdLevelPrimitive_sixteenth_3_bounds :
    (-110057/100000000000 : ℝ) ≤ secondLevelPrimitive (269/100) (3/64) ∧
    secondLevelPrimitive (269/100) (3/64) ≤ (-110056/100000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (3/128 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h1 := Real.exp_bound (x := (-15/128 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h2 := Real.exp_bound (x := (-27/128 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h3 := Real.exp_bound (x := (-39/128 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3
  norm_num [secondLevelPrimitive]
  constructor <;>
    linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
      (abs_le.mp h1).1, (abs_le.mp h1).2,
      (abs_le.mp h2).1, (abs_le.mp h2).2,
      (abs_le.mp h3).1, (abs_le.mp h3).2]

theorem thirdLevelPrimitive_sixteenth_5_bounds :
    (-405488/100000000000 : ℝ) ≤ secondLevelPrimitive (269/100) (5/64) ∧
    secondLevelPrimitive (269/100) (5/64) ≤ (-405487/100000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (5/128 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h1 := Real.exp_bound (x := (-25/128 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h2 := Real.exp_bound (x := (-45/128 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h3 := Real.exp_bound (x := (-65/128 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3
  norm_num [secondLevelPrimitive]
  constructor <;>
    linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
      (abs_le.mp h1).1, (abs_le.mp h1).2,
      (abs_le.mp h2).1, (abs_le.mp h2).2,
      (abs_le.mp h3).1, (abs_le.mp h3).2]

theorem thirdLevelPrimitive_sixteenth_7_bounds :
    (-851973/100000000000 : ℝ) ≤ secondLevelPrimitive (269/100) (7/64) ∧
    secondLevelPrimitive (269/100) (7/64) ≤ (-851972/100000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (7/128 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h1 := Real.exp_bound (x := (-35/128 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h2 := Real.exp_bound (x := (-63/128 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h3 := Real.exp_bound (x := (-91/128 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3
  norm_num [secondLevelPrimitive]
  constructor <;>
    linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
      (abs_le.mp h1).1, (abs_le.mp h1).2,
      (abs_le.mp h2).1, (abs_le.mp h2).2,
      (abs_le.mp h3).1, (abs_le.mp h3).2]

def thirdLevelForm (C R : ℝ) (c : Fin 7 → ℝ) : ℝ :=
  dotProduct c ((thirdLevelToeplitzHaar (thirdLevelCellValues C R)).mulVec c)

/-- Explicit prefix sums of the eight unnormalized Haar cell amplitudes. -/
def thirdLevelPrefix (c : Fin 7 → ℝ) : Fin 9 → ℝ :=
  ![0,c 0+c 1+c 3,2*c 0+2*c 1,3*c 0+c 1+c 4,4*c 0,
    3*c 0+c 2+c 5,2*c 0+2*c 2,c 0+c 2+c 6,0]

theorem thirdLevelPrefix_zero (c : Fin 7 → ℝ) : thirdLevelPrefix c 0 = 0 := rfl
theorem thirdLevelPrefix_eight (c : Fin 7 → ℝ) : thirdLevelPrefix c 8 = 0 := rfl

theorem thirdLevelPrefix_succ_sub (c : Fin 7 → ℝ) (j : Fin 8) :
    thirdLevelPrefix c j.succ - thirdLevelPrefix c j.castSucc =
      thirdLevelHaarColumns.mulVec c j := by
  simp only [Matrix.mulVec, dotProduct]
  fin_cases j <;>
    simp [thirdLevelPrefix, thirdLevelHaarColumns, Fin.sum_univ_succ, Matrix.cons_val] <;> ring

set_option maxHeartbeats 2000000 in
/-- Exact coefficient comparison, before any inequality is applied. -/
theorem thirdLevelForm_coefficient_comparison (C C0 R : ℝ) (c : Fin 7 → ℝ) :
    thirdLevelForm C R c - thirdLevelForm C0 R c =
      (C0-C)*(R/4)^3/6 *
        ∑ j : Fin 8,
          (3*(thirdLevelPrefix c j.castSucc+thirdLevelPrefix c j.succ)^2+
            (thirdLevelPrefix c j.castSucc-thirdLevelPrefix c j.succ)^2) := by
  simp only [thirdLevelForm, Matrix.mulVec, dotProduct]
  simp [thirdLevelToeplitzHaar, thirdLevelCellValues, thirdLevelHaarEntries,
    thirdLevelPrefix, Fin.sum_univ_succ, Matrix.cons_val]
  unfold secondLevelPrimitive
  ring

theorem thirdLevelForm_antitone {C C0 R : ℝ}
    (hC : C ≤ C0) (hR : 0 ≤ R) (c : Fin 7 → ℝ) :
    thirdLevelForm C0 R c ≤ thirdLevelForm C R c := by
  apply sub_nonneg.mp
  rw [thirdLevelForm_coefficient_comparison]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (by intro j hj; positivity))


def thirdLevelOddToeplitz (t : Fin 8 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  thirdLevelOddBlock
    (8*t 0+10*t 1+4*t 2-2*t 3-8*t 4-6*t 5-4*t 6-2*t 7)
    (t 1+2*t 2+t 3-t 5-2*t 6-t 7)
    (-t 1+2*t 3-t 7) (2*t 1-t 3-t 5)
    (4*t 0+2*t 1-4*t 2-2*t 3)
    (-t 1-2*t 2+t 3+4*t 4+t 5-2*t 6-t 7)
    (t 1-t 3) (-t 1+2*t 3-t 5) (-t 3+2*t 5-t 7)
    (2*t 0-2*t 1) (-t 1+2*t 2-t 3) (-t 3+2*t 4-t 5) (-t 5+2*t 6-t 7)

def thirdLevelEvenToeplitz (t : Fin 8 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  thirdLevelEvenBlock
    (4*t 0+2*t 1-4*t 2-2*t 3)
    (-t 1-2*t 2+t 3+4*t 4+t 5-2*t 6-t 7)
    (t 1-t 3) (-t 1+2*t 3-t 5) (-t 3+2*t 5-t 7)
    (2*t 0-2*t 1) (-t 1+2*t 2-t 3) (-t 3+2*t 4-t 5) (-t 5+2*t 6-t 7)

theorem thirdLevelToeplitz_reflection (t : Fin 8 → ℝ) :
    thirdLevelReflection.transpose * thirdLevelToeplitzHaar t * thirdLevelReflection =
      thirdLevelBlockDiagonal (thirdLevelOddToeplitz t) (thirdLevelEvenToeplitz t) :=
  thirdLevelReflection_congruence _ _ _ _ _ _ _ _ _ _ _ _ _

def thirdLevelOddShear : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![1,233/1000,377/1000,29/1000],![0,1,255/1000,124/1000],
    ![0,0,1,663/1000],![0,0,0,1]]

def thirdLevelEvenShear : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![1,-168/1000,-258/1000],![0,1,392/1000],![0,0,1]]

def thirdLevelOddSheared (C R : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  thirdLevelOddShear.transpose *
    (thirdLevelOddToeplitz (thirdLevelCellValues C R) -
      Matrix.diagonal ![1/1000000000,2/1000000000,2/1000000000,2/1000000000]) *
    thirdLevelOddShear

def thirdLevelEvenSheared (C R : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  thirdLevelEvenShear.transpose *
    (thirdLevelEvenToeplitz (thirdLevelCellValues C R) -
      Matrix.diagonal ![2/1000000000,2/1000000000,2/1000000000]) *
    thirdLevelEvenShear

theorem thirdLevelOddSheared_isHermitian (C R : ℝ) :
    (thirdLevelOddSheared C R).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  ext i j
  simp only [Matrix.transpose_apply, thirdLevelOddSheared, Matrix.mul_apply,
    Matrix.sub_apply, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [thirdLevelOddShear, thirdLevelOddToeplitz, thirdLevelOddBlock,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.cons_val] <;> ring

theorem thirdLevelEvenSheared_isHermitian (C R : ℝ) :
    (thirdLevelEvenSheared C R).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  ext i j
  simp only [Matrix.transpose_apply, thirdLevelEvenSheared, Matrix.mul_apply,
    Matrix.sub_apply, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [thirdLevelEvenShear, thirdLevelEvenToeplitz, thirdLevelEvenBlock,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.cons_val] <;> ring


theorem thirdLevel_reindex_quadratic
    (M : Matrix (FiniteDyadicHaarIndex 3) (FiniteDyadicHaarIndex 3) ℝ)
    (c : FiniteDyadicHaarIndex 3 → ℝ) :
    dotProduct c (M.mulVec c) =
      dotProduct (c ∘ thirdLevelIndex)
        (Matrix.mulVec (fun i j : Fin 7 => M (thirdLevelIndex i) (thirdLevelIndex j))
          (c ∘ thirdLevelIndex)) := by
  unfold Matrix.mulVec dotProduct
  rw [← thirdLevelIndexEquiv.sum_comp (fun i => c i * ∑ j, M i j * c j)]
  apply Finset.sum_congr rfl
  intro i hi
  change c (thirdLevelIndex i) * (∑ j, M (thirdLevelIndex i) j * c j) = _
  rw [← thirdLevelIndexEquiv.sum_comp
    (fun j => M (thirdLevelIndex i) j * c j)]
  rfl

theorem thirdLevelHaarModel_quadratic (C R : ℝ)
    (c : FiniteDyadicHaarIndex 3 → ℝ) :
    dotProduct c ((thirdLevelHaarModel C R).mulVec c) =
      thirdLevelForm C R (c ∘ thirdLevelIndex) := by
  rw [thirdLevel_reindex_quadratic, thirdLevelHaarModel_reindex,
    thirdLevelCellKernel, thirdLevelToeplitzHaar_eq]
  rfl

/-- Exact SOS comparison against the literal arithmetic approximation. -/
theorem arithmeticScrewApproxHaarMatrix_three_quadratic_comparison
    {R : ℝ} (hR : 0 ≤ R) (c : FiniteDyadicHaarIndex 3 → ℝ) :
    dotProduct c ((arithmeticScrewApproxHaarMatrix R 3 2 4).mulVec c) -
      dotProduct c ((thirdLevelHaarModel (5373/2000) R).mulVec c) =
      (5373/2000-screwLinearCoefficient)*(R/4)^3/6 *
        ∑ j : Fin 8,
          (3*(thirdLevelPrefix (c ∘ thirdLevelIndex) j.castSucc+
                thirdLevelPrefix (c ∘ thirdLevelIndex) j.succ)^2+
            (thirdLevelPrefix (c ∘ thirdLevelIndex) j.castSucc-
                thirdLevelPrefix (c ∘ thirdLevelIndex) j.succ)^2) := by
  rw [arithmeticScrewApproxHaarMatrix_three_eq_model hR,
    thirdLevelHaarModel_quadratic, thirdLevelHaarModel_quadratic]
  exact thirdLevelForm_coefficient_comparison _ _ _ _

theorem arithmeticScrewApproxHaarMatrix_three_auxiliary_le
    {R : ℝ} (hR : 0 ≤ R) (c : FiniteDyadicHaarIndex 3 → ℝ) :
    dotProduct c ((thirdLevelHaarModel (5373/2000) R).mulVec c) ≤
      dotProduct c ((arithmeticScrewApproxHaarMatrix R 3 2 4).mulVec c) := by
  rw [arithmeticScrewApproxHaarMatrix_three_eq_model hR,
    thirdLevelHaarModel_quadratic, thirdLevelHaarModel_quadratic]
  exact thirdLevelForm_antitone screwLinearCoefficient_le_5373_div_2000 hR _


def thirdLevelOddLower : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![4251,0,0,-1],![0,1221,-1,0],![0,-1,61,-1],![-1,0,-1,273]]
def thirdLevelOddUpper : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![4252,1,1,0],![1,1223,0,1],![1,0,63,1],![0,1,1,276]]

set_option maxHeartbeats 2000000 in
theorem thirdLevelOddSheared_bounds (i j : Fin 4) :
    thirdLevelOddLower i j / 1000000000 ≤ thirdLevelOddSheared (5373/2000) (1/16) i j ∧
    thirdLevelOddSheared (5373/2000) (1/16) i j ≤ thirdLevelOddUpper i j / 1000000000 := by
  rcases thirdLevelPrimitive_sixteenth_1_bounds with ⟨h1,h1'⟩
  rcases secondLevelPrimitive_sixteenth_1_bounds with ⟨h2,h2'⟩
  rcases thirdLevelPrimitive_sixteenth_3_bounds with ⟨h3,h3'⟩
  rcases secondLevelPrimitive_sixteenth_2_bounds with ⟨h4,h4'⟩
  rcases thirdLevelPrimitive_sixteenth_5_bounds with ⟨h5,h5'⟩
  rcases secondLevelPrimitive_sixteenth_3_bounds with ⟨h6,h6'⟩
  rcases thirdLevelPrimitive_sixteenth_7_bounds with ⟨h7,h7'⟩
  rcases secondLevelPrimitive_sixteenth_4_bounds with ⟨h8,h8'⟩
  norm_num at h1 h1' h2 h2' h3 h3' h4 h4' h5 h5' h6 h6' h7 h7' h8 h8'
  simp only [thirdLevelOddSheared, Matrix.mul_apply, Matrix.transpose_apply, Matrix.sub_apply]
  fin_cases i <;> fin_cases j <;>
    simp [thirdLevelOddShear, thirdLevelOddToeplitz, thirdLevelOddBlock,
      thirdLevelCellValues, thirdLevelPrimitive_coefficient_shift,
      thirdLevelOddLower, thirdLevelOddUpper,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.cons_val] <;>
    norm_num <;> constructor <;> linarith


def thirdLevelEvenLower : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![6230,-3,1],![-3,619,-1],![1,-1,546]]
def thirdLevelEvenUpper : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![6231,-2,2],![-2,621,1],![2,1,548]]

set_option maxHeartbeats 2000000 in
theorem thirdLevelEvenSheared_bounds (i j : Fin 3) :
    thirdLevelEvenLower i j / 1000000000 ≤ thirdLevelEvenSheared (5373/2000) (1/16) i j ∧
    thirdLevelEvenSheared (5373/2000) (1/16) i j ≤ thirdLevelEvenUpper i j / 1000000000 := by
  rcases thirdLevelPrimitive_sixteenth_1_bounds with ⟨h1,h1'⟩
  rcases secondLevelPrimitive_sixteenth_1_bounds with ⟨h2,h2'⟩
  rcases thirdLevelPrimitive_sixteenth_3_bounds with ⟨h3,h3'⟩
  rcases secondLevelPrimitive_sixteenth_2_bounds with ⟨h4,h4'⟩
  rcases thirdLevelPrimitive_sixteenth_5_bounds with ⟨h5,h5'⟩
  rcases secondLevelPrimitive_sixteenth_3_bounds with ⟨h6,h6'⟩
  rcases thirdLevelPrimitive_sixteenth_7_bounds with ⟨h7,h7'⟩
  rcases secondLevelPrimitive_sixteenth_4_bounds with ⟨h8,h8'⟩
  norm_num at h1 h1' h2 h2' h3 h3' h4 h4' h5 h5' h6 h6' h7 h7' h8 h8'
  simp only [thirdLevelEvenSheared, Matrix.mul_apply, Matrix.transpose_apply, Matrix.sub_apply]
  fin_cases i <;> fin_cases j <;>
    simp [thirdLevelEvenShear, thirdLevelEvenToeplitz, thirdLevelEvenBlock,
      thirdLevelCellValues, thirdLevelPrimitive_coefficient_shift,
      thirdLevelEvenLower, thirdLevelEvenUpper,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.cons_val] <;>
    norm_num <;> constructor <;> linarith


def thirdLevelOddAbsUpper : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![0,1,1,1],![1,0,1,1],![1,1,0,1],![1,1,1,0]]
def thirdLevelEvenAbsUpper : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![0,3,2],![3,0,1],![2,1,0]]

theorem thirdLevelOddSheared_posDef :
    (thirdLevelOddSheared (5373/2000) (1/16)).PosDef := by
  apply StrictDiagonalDominance.posDef_of_entrywise_interval_certificate
    (thirdLevelOddSheared_isHermitian _ _)
    (fun i j => thirdLevelOddLower i j / 1000000000)
    (fun i j => thirdLevelOddAbsUpper i j / 1000000000)
  · intro i
    exact (thirdLevelOddSheared_bounds i i).1
  · intro i j hij
    have hb := thirdLevelOddSheared_bounds i j
    rw [Real.norm_eq_abs, abs_le]
    fin_cases i <;> fin_cases j <;>
      (try exact (hij rfl).elim) <;>
      norm_num [thirdLevelOddLower, thirdLevelOddUpper, thirdLevelOddAbsUpper] at hb ⊢ <;>
      constructor <;> linarith
  · intro i
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    fin_cases i <;>
      norm_num [thirdLevelOddAbsUpper, thirdLevelOddLower, Fin.sum_univ_succ]

theorem thirdLevelEvenSheared_posDef :
    (thirdLevelEvenSheared (5373/2000) (1/16)).PosDef := by
  apply StrictDiagonalDominance.posDef_of_entrywise_interval_certificate
    (thirdLevelEvenSheared_isHermitian _ _)
    (fun i j => thirdLevelEvenLower i j / 1000000000)
    (fun i j => thirdLevelEvenAbsUpper i j / 1000000000)
  · intro i
    exact (thirdLevelEvenSheared_bounds i i).1
  · intro i j hij
    have hb := thirdLevelEvenSheared_bounds i j
    rw [Real.norm_eq_abs, abs_le]
    fin_cases i <;> fin_cases j <;>
      (try exact (hij rfl).elim) <;>
      norm_num [thirdLevelEvenLower, thirdLevelEvenUpper, thirdLevelEvenAbsUpper] at hb ⊢ <;>
      constructor <;> linarith
  · intro i
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    fin_cases i <;>
      norm_num [thirdLevelEvenAbsUpper, thirdLevelEvenLower, Fin.sum_univ_succ]

def thirdLevelOddUnshear (v : Fin 4 → ℝ) : Fin 4 → ℝ :=
  let w2 := v 2 - (663/1000)*v 3
  let w1 := v 1 - (255/1000)*w2 - (124/1000)*v 3
  ![v 0-(233/1000)*w1-(377/1000)*w2-(29/1000)*v 3,w1,w2,v 3]

def thirdLevelEvenUnshear (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  let w1 := v 1 - (392/1000)*v 2
  ![v 0+(168/1000)*w1+(258/1000)*v 2,w1,v 2]

theorem thirdLevelOddShear_unshear (v : Fin 4 → ℝ) :
    thirdLevelOddShear.mulVec (thirdLevelOddUnshear v) = v := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, thirdLevelOddShear, thirdLevelOddUnshear,
      Fin.sum_univ_succ, Matrix.cons_val] <;> ring

theorem thirdLevelEvenShear_unshear (v : Fin 3 → ℝ) :
    thirdLevelEvenShear.mulVec (thirdLevelEvenUnshear v) = v := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, thirdLevelEvenShear, thirdLevelEvenUnshear,
      Fin.sum_univ_succ, Matrix.cons_val] <;> ring

private theorem realMatrix_congruence_quadratic {n m : Type*} [Fintype n] [Fintype m]
    (S : Matrix n m ℝ) (B : Matrix n n ℝ) (w : m → ℝ) :
    dotProduct w ((S.transpose * B * S).mulVec w) =
      dotProduct (S.mulVec w) (B.mulVec (S.mulVec w)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  congr 1
  ext i
  simp [Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]

theorem thirdLevelOddBlock_lower (v : Fin 4 → ℝ) :
    (1/1000000000)*(v 0)^2+
      (2/1000000000)*((v 1)^2+(v 2)^2+(v 3)^2) ≤
      dotProduct v ((thirdLevelOddToeplitz (thirdLevelCellValues (5373/2000) (1/16))).mulVec v) := by
  have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp
    thirdLevelOddSheared_posDef.posSemidef).2 (thirdLevelOddUnshear v)
  simp only [star_trivial, thirdLevelOddSheared, realMatrix_congruence_quadratic,
    thirdLevelOddShear_unshear] at h
  simp [Matrix.sub_mulVec, dotProduct, Fin.sum_univ_succ, Matrix.mulVec_diagonal] at h ⊢
  linarith

theorem thirdLevelEvenBlock_lower (v : Fin 3 → ℝ) :
    (2/1000000000)*((v 0)^2+(v 1)^2+(v 2)^2) ≤
      dotProduct v ((thirdLevelEvenToeplitz (thirdLevelCellValues (5373/2000) (1/16))).mulVec v) := by
  have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp
    thirdLevelEvenSheared_posDef.posSemidef).2 (thirdLevelEvenUnshear v)
  simp only [star_trivial, thirdLevelEvenSheared, realMatrix_congruence_quadratic,
    thirdLevelEvenShear_unshear] at h
  simp [Matrix.sub_mulVec, dotProduct, Fin.sum_univ_succ, Matrix.mulVec_diagonal] at h ⊢
  linarith


def thirdLevelUnreflect (c : Fin 7 → ℝ) : Fin 7 → ℝ :=
  ![c 0,(c 1+c 2)/2,(c 3+c 6)/2,(c 4+c 5)/2,
    (c 1-c 2)/2,(c 3-c 6)/2,(c 4-c 5)/2]

theorem thirdLevelReflection_unreflect (c : Fin 7 → ℝ) :
    thirdLevelReflection.mulVec (thirdLevelUnreflect c) = c := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, thirdLevelReflection, thirdLevelUnreflect,
      Fin.sum_univ_succ, Matrix.cons_val] <;> ring

theorem thirdLevelUnreflect_norm (c : Fin 7 → ℝ) :
    (thirdLevelUnreflect c 0)^2+
      2*((thirdLevelUnreflect c 1)^2+(thirdLevelUnreflect c 2)^2+
        (thirdLevelUnreflect c 3)^2+(thirdLevelUnreflect c 4)^2+
        (thirdLevelUnreflect c 5)^2+(thirdLevelUnreflect c 6)^2) =
      ∑ i : Fin 7, (c i)^2 := by
  simp [thirdLevelUnreflect, Fin.sum_univ_succ, Matrix.cons_val]
  ring

theorem thirdLevelBlockDiagonal_quadratic
    (O : Matrix (Fin 4) (Fin 4) ℝ) (E : Matrix (Fin 3) (Fin 3) ℝ)
    (v : Fin 7 → ℝ) :
    dotProduct v ((thirdLevelBlockDiagonal O E).mulVec v) =
      dotProduct ![v 0,v 1,v 2,v 3] (O.mulVec ![v 0,v 1,v 2,v 3])+
      dotProduct ![v 4,v 5,v 6] (E.mulVec ![v 4,v 5,v 6]) := by
  simp [Matrix.mulVec, dotProduct, thirdLevelBlockDiagonal, Fin.sum_univ_succ]
  ring

/-- Quantitative auxiliary certificate in the original unnormalized coefficient norm. -/
theorem thirdLevelForm_sixteenth_lower (c : Fin 7 → ℝ) :
    (1/1000000000)*(∑ i : Fin 7, (c i)^2) ≤
      thirdLevelForm (5373/2000) (1/16) c := by
  let v := thirdLevelUnreflect c
  have ho := thirdLevelOddBlock_lower ![v 0,v 1,v 2,v 3]
  have he := thirdLevelEvenBlock_lower ![v 4,v 5,v 6]
  have hc := realMatrix_congruence_quadratic thirdLevelReflection
    (thirdLevelToeplitzHaar (thirdLevelCellValues (5373/2000) (1/16))) v
  rw [thirdLevelToeplitz_reflection, thirdLevelBlockDiagonal_quadratic] at hc
  have hv : thirdLevelReflection.mulVec v = c := thirdLevelReflection_unreflect c
  rw [hv] at hc
  have hn := thirdLevelUnreflect_norm c
  change (v 0)^2+2*((v 1)^2+(v 2)^2+(v 3)^2+(v 4)^2+(v 5)^2+(v 6)^2) =
    ∑ i : Fin 7, (c i)^2 at hn
  simp only [Matrix.cons_val] at ho he
  unfold thirdLevelForm
  linarith only [ho,he,hc,hn]

/-- Positive lower bound for the genuine finite arithmetic m=3 matrix,
at R=1/16, N=2, J=4 only. -/
theorem arithmeticScrewApproxHaarMatrix_sixteenth_level_three_lower
    (c : FiniteDyadicHaarIndex 3 → ℝ) :
    (1/1000000000)*(∑ i, (c i)^2) ≤
      dotProduct c ((arithmeticScrewApproxHaarMatrix (1/16) 3 2 4).mulVec c) := by
  have h := thirdLevelForm_sixteenth_lower (c ∘ thirdLevelIndex)
  have he : (∑ i : Fin 7, ((c ∘ thirdLevelIndex) i)^2) = ∑ i, (c i)^2 :=
    thirdLevelIndexEquiv.sum_comp (fun i => (c i)^2)
  rw [he, ← thirdLevelHaarModel_quadratic] at h
  exact h.trans (arithmeticScrewApproxHaarMatrix_three_auxiliary_le (by norm_num) c)

/-- Native PSD of the genuine fixed-window, fixed-level finite approximation. -/
theorem arithmeticScrewApproxHaarMatrix_sixteenth_level_three_posSemidef :
    (arithmeticScrewApproxHaarMatrix (1/16) 3 2 4).PosSemidef := by
  rw [arithmeticScrewApproxHaarMatrix_posSemidef_iff]
  intro c
  exact le_trans (by positivity)
    (arithmeticScrewApproxHaarMatrix_sixteenth_level_three_lower c)

/-- The signed tail theorem transfers the same lower bound to the actual arithmetic matrix. -/
theorem arithmeticScrewHaarMatrix_sixteenth_three_lower
    (c : FiniteDyadicHaarIndex 3 → ℝ) :
    (1/1000000000)*(∑ i, (c i)^2) ≤
      dotProduct c ((arithmeticScrewHaarMatrix (1/16) 3).mulVec c) :=
  (arithmeticScrewApproxHaarMatrix_sixteenth_level_three_lower c).trans
    (arithmeticScrewApproxHaarMatrix_quadratic_le (by norm_num) 3 2 4
      arithmeticScrewApprox_sixteenth_cutoff c)

/-- Native PSD at m=3 and R=1/16. This asserts neither all-level positivity,
completed-Weil positivity, nor RH. -/
theorem arithmeticScrewHaarMatrix_sixteenth_three_posSemidef :
    (arithmeticScrewHaarMatrix (1/16) 3).PosSemidef :=
  arithmeticScrewHaarMatrix_posSemidef_of_approx_posSemidef
    (by norm_num) 3 2 4 arithmeticScrewApprox_sixteenth_cutoff
    arithmeticScrewApproxHaarMatrix_sixteenth_level_three_posSemidef


end
end RiemannResearch.RH
