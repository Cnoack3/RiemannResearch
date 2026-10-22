/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.ArithmeticFiniteThirdLevelCertificate

/-!
# A positive fourth-level arithmetic certificate

At the single window `R = 1/16`, this module proves the quantitative lower
bound `1/1000000000` times the sum of all fifteen native unnormalized Haar
coefficient squares, and native positive semidefiniteness, for the finite
arithmetic approximation with `m = 4`, `N = 2`, `J = 5` and for the actual
arithmetic Haar matrix at that same window and level.

The proof reconstructs the literal sixteen-cell arithmetic matrix, retaining
the complete range-two von Mangoldt sum, polar correction, live
`screwLinearCoefficient`, and all five subtracted archimedean modes. Exact
jump-stencil and Toeplitz identities split the form into reflection blocks of
dimensions eight and seven. Rigorous exponential enclosures and rational
unit-triangular shears prove strict row diagonal dominance after subtracting
the coefficient-space Gram correction. The established signed comparison
then transfers the finite lower bound to the actual matrix.

This is fixed-window, fixed-level arithmetic positivity only. It does not prove
all-level or all-window positivity, completed-Weil positivity, or RH.

Source: user-provided RH continuation program and the exact finite arithmetic
strategy developed in the preceding first-, second-, and third-level
certificate modules. The source supports the proof strategy and terminology.
-/
set_option maxRecDepth 16384
open scoped BigOperators
namespace RiemannResearch.RH
open RiemannResearch.Analysis RiemannResearch.RH.PrimeGapCurvature
noncomputable section

/-- The fifth archimedean mode is retained with its original subtracted sign. -/
def fourthLevelArithmeticCell (C b₁ d₁ b₂ d₂ : ℝ) : ℝ :=
  screwPolarCell b₁ d₁ b₂ d₂ +
    (∑ n ∈ Finset.range 2, primePowerHingeCell n b₁ d₁ b₂ d₂) +
    C * absCell b₁ d₁ b₂ d₂ -
    ∑ k ∈ Finset.range 5, archimedeanScrewCell k b₁ d₁ b₂ d₂

def fourthLevelRawPrimitive (C t : ℝ) : ℝ :=
  -16*(Real.exp (t/2)+Real.exp (-t/2)) + 4*t^2 +
    C*hingeKernelSecondPrimitive 0 t +
    ∑ k ∈ Finset.range 5,
      4*archimedeanWeight k*
        (exponentialAbsSecondPrimitive (archimedeanRate k) t - t^2/2)

def fourthLevelPrimitive (C u : ℝ) : ℝ :=
  16+8*u+2*u^2+(C/6)*u^3-16*Real.exp (u/2) +
    ∑ q ∈ ({5,9,13,17} : Finset ℕ),
      ((16/(q : ℝ)^4)*(Real.exp (-(q : ℝ)*u/2)-1+(q : ℝ)*u/2) -
        2*u^2/(q : ℝ)^2)

theorem fourthLevelPrimitive_zero (C : ℝ) :
    fourthLevelPrimitive C 0 = 0 := by
  norm_num [fourthLevelPrimitive]

theorem fourthLevelPrimitive_eq_raw (C t : ℝ) :
    fourthLevelPrimitive C |t| =
      fourthLevelRawPrimitive C t - fourthLevelRawPrimitive C 0 := by
  by_cases ht : 0 ≤ t
  · norm_num [fourthLevelPrimitive, fourthLevelRawPrimitive,
      hingeKernelSecondPrimitive, exponentialAbsSecondPrimitive,
      archimedeanRate, archimedeanWeight, Finset.sum_range_succ,
      abs_of_nonneg ht, max_eq_left ht,
      max_eq_right (show -t ≤ 0 by linarith)]
    ring
  · have ht' : t ≤ 0 := le_of_not_ge ht
    norm_num [fourthLevelPrimitive, fourthLevelRawPrimitive,
      hingeKernelSecondPrimitive, exponentialAbsSecondPrimitive,
      archimedeanRate, archimedeanWeight, Finset.sum_range_succ,
      abs_of_nonpos ht', max_eq_right ht',
      max_eq_left (show 0 ≤ -t by linarith)]
    ring

theorem fourthLevelArithmeticCell_eq_primitive (C b₁ d₁ b₂ d₂ : ℝ) :
    fourthLevelArithmeticCell C b₁ d₁ b₂ d₂ =
      secondPrimitiveCell (fun t => fourthLevelPrimitive C |t|) b₁ d₁ b₂ d₂ := by
  simp only [secondPrimitiveCell, fourthLevelPrimitive_eq_raw]
  norm_num [fourthLevelArithmeticCell, fourthLevelRawPrimitive,
    screwPolarCell, exponentialCell, absCell, secondPrimitiveCell,
    primePowerHingeCell, primePowerWeight, archimedeanScrewCell,
    exponentialAbsCell, Finset.sum_range_succ]
  ring

theorem fourthLevelPrimitive_eq_second (C u : ℝ) :
    fourthLevelPrimitive C u = secondLevelPrimitive C u +
      (16/17^4)*(Real.exp (-17*u/2)-1+17*u/2)-2*u^2/17^2 := by
  norm_num [fourthLevelPrimitive, secondLevelPrimitive]
  ring

def cellEndpointIncidence (n : ℕ) : Matrix (Fin (n+1)) (Fin n) ℝ :=
  fun r i => (if r = i.castSucc then 1 else 0) - (if r = i.succ then 1 else 0)

theorem cellEndpointIncidence_congruence {n : ℕ}
    (F : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (i j : Fin n) :
    ((cellEndpointIncidence n).transpose * F * cellEndpointIncidence n) i j =
    F i.castSucc j.castSucc - F i.succ j.castSucc -
      F i.castSucc j.succ + F i.succ j.succ := by
  simp [Matrix.mul_apply, Matrix.transpose_apply, cellEndpointIncidence,
    sub_mul, mul_sub, Finset.sum_sub_distrib]
  ring
def endpointPrimitiveMatrix {n : ℕ} (P : ℝ → ℝ) (x : Fin (n+1) → ℝ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i j => P (x i - x j)

theorem secondPrimitiveCell_incidence {n : ℕ} (P : ℝ → ℝ)
    (x : Fin (n+1) → ℝ) :
    (fun i j : Fin n =>
      secondPrimitiveCell P (x i.castSucc) (x i.succ) (x j.castSucc) (x j.succ)) =
      -((cellEndpointIncidence n).transpose * endpointPrimitiveMatrix P x *
        cellEndpointIncidence n) := by
  ext i j
  simp only [Matrix.neg_apply, cellEndpointIncidence_congruence,
    endpointPrimitiveMatrix, secondPrimitiveCell]
  ring

theorem cellHaar_jump_congruence {n κ : Type*} [Fintype n] [Fintype κ]
    {p : Type*} [Fintype p] (D : Matrix p n ℝ) (F : Matrix p p ℝ)
    (H : Matrix n κ ℝ) :
    H.transpose * (-(D.transpose * F * D)) * H =
      -((D*H).transpose * F * (D*H)) := by
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

def threePointJumps {n κ : Type*} [DecidableEq n]
    (a b d : κ → n) : Matrix n κ ℝ :=
  fun r i => (if r = a i then 1 else 0) -
    2*(if r = b i then 1 else 0) + (if r = d i then 1 else 0)

theorem threePointJumps_congruence {n κ : Type*} [Fintype n] [Fintype κ]
    [DecidableEq n] (a b d : κ → n) (F : Matrix n n ℝ) (i j : κ) :
    ((threePointJumps a b d).transpose * F * threePointJumps a b d) i j =
      F (a i) (a j)-2*F (a i) (b j)+F (a i) (d j) -
      2*F (b i) (a j)+4*F (b i) (b j)-2*F (b i) (d j) +
      F (d i) (a j)-2*F (d i) (b j)+F (d i) (d j) := by
  simp [Matrix.mul_apply, Matrix.transpose_apply, threePointJumps,
    sub_mul, add_mul, mul_sub, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  ring

def fourthLevelIndex : Fin 15 → FiniteDyadicHaarIndex 4 :=
  ![⟨0,0⟩,⟨1,0⟩,⟨1,1⟩,⟨2,0⟩,⟨2,1⟩,⟨2,2⟩,⟨2,3⟩,
    ⟨3,0⟩,⟨3,1⟩,⟨3,2⟩,⟨3,3⟩,⟨3,4⟩,⟨3,5⟩,⟨3,6⟩,⟨3,7⟩]

theorem fourthLevelIndex_surjective : Function.Surjective fourthLevelIndex := by
  rintro ⟨l,q⟩
  fin_cases l <;> fin_cases q
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨3,rfl⟩
  · exact ⟨4,rfl⟩
  · exact ⟨5,rfl⟩
  · exact ⟨6,rfl⟩
  · exact ⟨7,rfl⟩
  · exact ⟨8,rfl⟩
  · exact ⟨9,rfl⟩
  · exact ⟨10,rfl⟩
  · exact ⟨11,rfl⟩
  · exact ⟨12,rfl⟩
  · exact ⟨13,rfl⟩
  · exact ⟨14,rfl⟩

theorem fourthLevelIndex_injective : Function.Injective fourthLevelIndex := by
  apply ((Fintype.bijective_iff_surjective_and_card fourthLevelIndex).mpr
    ⟨fourthLevelIndex_surjective, ?_⟩).1
  rw [card_finiteDyadicHaarIndex]
  rfl

def fourthLevelIndexEquiv : Fin 15 ≃ FiniteDyadicHaarIndex 4 :=
  Equiv.ofBijective fourthLevelIndex ⟨fourthLevelIndex_injective,fourthLevelIndex_surjective⟩

def fourthLevelHaarColumns : Matrix (Fin 16) (Fin 15) ℝ :=
  fun i j => finiteDyadicHaarMatrix 4 i (fourthLevelIndex j)

def fourthLevelLeft : Fin 15 → Fin 17 := ![0,0,8,0,4,8,12,0,2,4,6,8,10,12,14]
def fourthLevelMid : Fin 15 → Fin 17 := ![8,4,12,2,6,10,14,1,3,5,7,9,11,13,15]
def fourthLevelRight : Fin 15 → Fin 17 := ![16,8,16,4,8,12,16,2,4,6,8,10,12,14,16]
def fourthLevelJumps : Matrix (Fin 17) (Fin 15) ℝ :=
  threePointJumps fourthLevelLeft fourthLevelMid fourthLevelRight

theorem cellEndpointIncidence_mul_interior {κ : Type*} [Fintype κ]
    {N : ℕ} (H : Matrix (Fin (N+2)) κ ℝ) (r : Fin (N+1)) (j : κ) :
    (cellEndpointIncidence (N+2) * H) r.succ.castSucc j =
      H r.succ j - H r.castSucc j := by
  have hr : r.succ.castSucc = r.castSucc.succ := rfl
  simp only [Matrix.mul_apply, cellEndpointIncidence, sub_mul,
    Finset.sum_sub_distrib, Fin.castSucc_inj]
  rw [hr]
  simp

theorem cellEndpointIncidence_mul_first {κ : Type*} [Fintype κ]
    {N : ℕ} (H : Matrix (Fin (N+1)) κ ℝ) (j : κ) :
    (cellEndpointIncidence (N+1) * H) 0 j = H 0 j := by
  change (cellEndpointIncidence (N+1) * H) (0 : Fin (N+1)).castSucc j = _
  simp [Matrix.mul_apply, cellEndpointIncidence, sub_mul,
    Finset.sum_sub_distrib, eq_comm]

theorem cellEndpointIncidence_mul_last {κ : Type*} [Fintype κ]
    {N : ℕ} (H : Matrix (Fin (N+1)) κ ℝ) (j : κ) :
    (cellEndpointIncidence (N+1) * H) (Fin.last (N+1)) j =
      -H (Fin.last N) j := by
  have hlast (x : Fin (N+1)) :
      Fin.last (N+1) = x.succ ↔ Fin.last N = x := by
    simp only [Fin.ext_iff, Fin.val_last, Fin.val_succ]
    omega
  simp [Matrix.mul_apply, cellEndpointIncidence, sub_mul,
    Finset.sum_sub_distrib, hlast, eq_comm]


theorem fourthLevelHaarColumns_jumps_interior (s : Fin 15) (j : Fin 15) :
    (cellEndpointIncidence 16 * fourthLevelHaarColumns) s.succ.castSucc j =
      fourthLevelJumps s.succ.castSucc j := by
  rw [cellEndpointIncidence_mul_interior]
  have hd := finiteDyadicHaarAtom_slopeDifference 4 (fourthLevelIndex j).1.val
    (fourthLevelIndex j).2 s
  change fourthLevelHaarColumns s.succ j - fourthLevelHaarColumns s.castSucc j = _ at hd
  rw [hd]
  fin_cases j <;>
    dsimp [fourthLevelIndex, fourthLevelJumps, threePointJumps,
      fourthLevelLeft, fourthLevelMid, fourthLevelRight, Matrix.cons_val] <;>
    simp only [Fin.ext_iff, Fin.val_succ, Fin.val_castSucc] <;> norm_num

theorem fourthLevelHaarColumns_jumps_first (j : Fin 15) :
    (cellEndpointIncidence 16 * fourthLevelHaarColumns) 0 j =
      fourthLevelJumps 0 j := by
  rw [cellEndpointIncidence_mul_first]
  fin_cases j <;>
    dsimp [fourthLevelHaarColumns, finiteDyadicHaarMatrix,
      finiteDyadicHaarAtom, fourthLevelIndex, fourthLevelJumps,
      threePointJumps, fourthLevelLeft, fourthLevelMid, fourthLevelRight,
      Matrix.cons_val] <;> norm_num

theorem fourthLevelHaarColumns_jumps_last (j : Fin 15) :
    (cellEndpointIncidence 16 * fourthLevelHaarColumns) (Fin.last 16) j =
      fourthLevelJumps (Fin.last 16) j := by
  rw [cellEndpointIncidence_mul_last]
  fin_cases j <;>
    dsimp [fourthLevelHaarColumns, finiteDyadicHaarMatrix,
      finiteDyadicHaarAtom, fourthLevelIndex, fourthLevelJumps,
      threePointJumps, fourthLevelLeft, fourthLevelMid, fourthLevelRight,
      Matrix.cons_val, Fin.last] <;> norm_num

theorem fourthLevelHaarColumns_jumps :
    cellEndpointIncidence 16 * fourthLevelHaarColumns = fourthLevelJumps := by
  ext i j
  refine Fin.cases (fourthLevelHaarColumns_jumps_first j) (fun r => ?_) i
  refine Fin.lastCases (fourthLevelHaarColumns_jumps_last j)
    (fun s => fourthLevelHaarColumns_jumps_interior s j) r
def fourthLevelEndpoint (R : ℝ) (i : Fin 17) : ℝ := -R+(i.val : ℝ)*(R/8)

def fourthLevelPrimitiveMatrix (C R : ℝ) : Matrix (Fin 17) (Fin 17) ℝ :=
  endpointPrimitiveMatrix (fun t => fourthLevelPrimitive C |t|) (fourthLevelEndpoint R)

def fourthLevelCellKernel (C R : ℝ) : Matrix (Fin 16) (Fin 16) ℝ :=
  -((cellEndpointIncidence 16).transpose * fourthLevelPrimitiveMatrix C R *
    cellEndpointIncidence 16)

theorem fourthLevelArithmeticCell_grid (C R : ℝ) :
    (fun i j : Fin 16 =>
      fourthLevelArithmeticCell C
        (dyadicCellLeft R 4 i) (dyadicCellRight R 4 i)
        (dyadicCellLeft R 4 j) (dyadicCellRight R 4 j)) =
      fourthLevelCellKernel C R := by
  rw [fourthLevelCellKernel, fourthLevelPrimitiveMatrix, ← secondPrimitiveCell_incidence]
  ext i j
  rw [fourthLevelArithmeticCell_eq_primitive]
  congr 1 <;>
    norm_num [dyadicCellLeft, dyadicCellRight, dyadicCellWidth,
      fourthLevelEndpoint, Fin.val_castSucc, Fin.val_succ] <;> ring

def fourthLevelHaarModel (C R : ℝ) :
    Matrix (FiniteDyadicHaarIndex 4) (FiniteDyadicHaarIndex 4) ℝ :=
  finiteDyadicHaarCompression 4 (fourthLevelCellKernel C R)

theorem arithmeticScrewApproxHaarMatrix_four_eq_model (R : ℝ) :
    arithmeticScrewApproxHaarMatrix R 4 2 5 =
      fourthLevelHaarModel screwLinearCoefficient R := by
  unfold fourthLevelHaarModel arithmeticScrewApproxHaarMatrix
  congr 1
  rw [← fourthLevelArithmeticCell_grid screwLinearCoefficient R]
  ext i j
  exact integral_integral_arithmeticScrewApprox 2 5
    (dyadicCellLeft R 4 i) (dyadicCellRight R 4 i)
    (dyadicCellLeft R 4 j) (dyadicCellRight R 4 j)

def fourthLevelJumpHaar (C R : ℝ) : Matrix (Fin 15) (Fin 15) ℝ :=
  -(fourthLevelJumps.transpose * fourthLevelPrimitiveMatrix C R * fourthLevelJumps)

theorem fourthLevelHaarModel_reindex (C R : ℝ) :
    (fun i j : Fin 15 => fourthLevelHaarModel C R (fourthLevelIndex i) (fourthLevelIndex j)) =
      fourthLevelJumpHaar C R := by
  have h : (fun i j : Fin 15 =>
      fourthLevelHaarModel C R (fourthLevelIndex i) (fourthLevelIndex j)) =
      fourthLevelHaarColumns.transpose * fourthLevelCellKernel C R * fourthLevelHaarColumns := by
    ext i j
    rfl
  rw [h, fourthLevelCellKernel, cellHaar_jump_congruence, fourthLevelHaarColumns_jumps]
  rfl

/-- Signed-distance primitive on the literal sixteenth-cell grid. -/
def fourthLevelGridPrimitive (C R : ℝ) (k : ℤ) : ℝ :=
  fourthLevelPrimitive C (|(k : ℝ)| * (R/8))

def fourthLevelToeplitzValue (C R : ℝ) (k : ℤ) : ℝ :=
  fourthLevelGridPrimitive C R (k+1) -
    2*fourthLevelGridPrimitive C R k + fourthLevelGridPrimitive C R (k-1)

theorem fourthLevelGridPrimitive_neg (C R : ℝ) (k : ℤ) :
    fourthLevelGridPrimitive C R (-k) = fourthLevelGridPrimitive C R k := by
  simp [fourthLevelGridPrimitive]

theorem fourthLevelToeplitzValue_neg (C R : ℝ) (k : ℤ) :
    fourthLevelToeplitzValue C R (-k) = fourthLevelToeplitzValue C R k := by
  unfold fourthLevelToeplitzValue
  rw [show -k+1 = -(k-1) by ring, show -k-1 = -(k+1) by ring]
  simp only [fourthLevelGridPrimitive_neg]
  ring

theorem fourthLevelPrimitiveMatrix_grid (C : ℝ) {R : ℝ} (hR : 0 ≤ R)
    (i j : Fin 17) :
    fourthLevelPrimitiveMatrix C R i j =
      fourthLevelGridPrimitive C R ((i.val : ℤ) - j.val) := by
  unfold fourthLevelPrimitiveMatrix endpointPrimitiveMatrix
    fourthLevelGridPrimitive fourthLevelEndpoint
  dsimp only
  rw [show -R+(i.val : ℝ)*(R/8)-(-R+(j.val : ℝ)*(R/8)) =
    ((i.val : ℝ)-j.val)*(R/8) by ring, abs_mul,
    abs_of_nonneg (show 0 ≤ R/8 by positivity)]
  norm_cast

/-- Every one of the 256 cells has this exact even Toeplitz second difference. -/
theorem fourthLevelCellKernel_toeplitz (C : ℝ) {R : ℝ} (hR : 0 ≤ R)
    (i j : Fin 16) :
    fourthLevelCellKernel C R i j =
      fourthLevelToeplitzValue C R ((i.val : ℤ)-j.val) := by
  simp only [fourthLevelCellKernel, Matrix.neg_apply, cellEndpointIncidence_congruence,
    fourthLevelPrimitiveMatrix_grid C hR, Fin.val_castSucc, Fin.val_succ,
    Nat.cast_add, Nat.cast_one, fourthLevelToeplitzValue]
  rw [show (i.val : ℤ)+1-j.val = ((i.val : ℤ)-j.val)+1 by ring,
    show (i.val : ℤ)+1-(j.val+1) = (i.val : ℤ)-j.val by ring,
    show (i.val : ℤ)-(j.val+1) = ((i.val : ℤ)-j.val)-1 by ring]
  ring

theorem fourthLevelPrimitiveMatrix_symm (C R : ℝ) :
    (fourthLevelPrimitiveMatrix C R).IsSymm := by
  ext i j
  exact congrArg (fourthLevelPrimitive C) (abs_sub_comm _ _)

theorem fourthLevelPrimitiveMatrix_reflect (C R : ℝ) (i j : Fin 17) :
    fourthLevelPrimitiveMatrix C R i.rev j.rev =
      fourthLevelPrimitiveMatrix C R i j := by
  unfold fourthLevelPrimitiveMatrix endpointPrimitiveMatrix fourthLevelEndpoint
  dsimp only
  have hi : (i.rev.val : ℝ) = 16-i.val := by
    rw [Fin.val_rev, Nat.cast_sub (by omega)]
    norm_num
    ring
  have hj : (j.rev.val : ℝ) = 16-j.val := by
    rw [Fin.val_rev, Nat.cast_sub (by omega)]
    norm_num
    ring
  rw [hi,hj]
  congr 1
  rw [show -R+(16-(i.val : ℝ))*(R/8)-(-R+(16-(j.val : ℝ))*(R/8)) =
    -(-R+(i.val : ℝ)*(R/8)-(-R+(j.val : ℝ)*(R/8))) by ring, abs_neg]

def fourthLevelReflectIndex : Fin 15 → Fin 15 :=
  ![0,2,1,6,5,4,3,14,13,12,11,10,9,8,7]

theorem fourthLevelReflectIndex_involutive :
    Function.Involutive fourthLevelReflectIndex := by
  intro i
  fin_cases i <;> rfl


theorem fourthLevelReflectIndex_left (j : Fin 15) :
    fourthLevelLeft (fourthLevelReflectIndex j) = (fourthLevelRight j).rev := by
  fin_cases j <;> rfl

theorem fourthLevelReflectIndex_mid (j : Fin 15) :
    fourthLevelMid (fourthLevelReflectIndex j) = (fourthLevelMid j).rev := by
  fin_cases j <;> rfl

theorem fourthLevelReflectIndex_right (j : Fin 15) :
    fourthLevelRight (fourthLevelReflectIndex j) = (fourthLevelLeft j).rev := by
  fin_cases j <;> rfl

theorem fourthLevelJumpHaar_reflect (C R : ℝ) (i j : Fin 15) :
    fourthLevelJumpHaar C R (fourthLevelReflectIndex i) (fourthLevelReflectIndex j) =
      fourthLevelJumpHaar C R i j := by
  simp only [fourthLevelJumpHaar, fourthLevelJumps, Matrix.neg_apply,
    threePointJumps_congruence, fourthLevelReflectIndex_left,
    fourthLevelReflectIndex_mid, fourthLevelReflectIndex_right,
    fourthLevelPrimitiveMatrix_reflect]
  ring

theorem fourthLevelJumpHaar_symm (C R : ℝ) :
    (fourthLevelJumpHaar C R).IsSymm := by
  change (fourthLevelJumpHaar C R).transpose = _
  simp [fourthLevelJumpHaar, (fourthLevelPrimitiveMatrix_symm C R).eq,
    Matrix.mul_assoc]

/-- A weighted two-endpoint column, used for exact reflection coordinates. -/
def twoPointColumns {n κ : Type*} [DecidableEq n]
    (a b : κ → n) (u v : κ → ℝ) : Matrix n κ ℝ :=
  fun r i => u i*(if r = a i then 1 else 0) + v i*(if r = b i then 1 else 0)

theorem twoPointColumns_congruence {n κ : Type*} [Fintype n] [Fintype κ]
    [DecidableEq n] (a b : κ → n) (u v : κ → ℝ) (K : Matrix n n ℝ) (i j : κ) :
    ((twoPointColumns a b u v).transpose * K * twoPointColumns a b u v) i j =
      u i*u j*K (a i) (a j) + u i*v j*K (a i) (b j) +
      v i*u j*K (b i) (a j) + v i*v j*K (b i) (b j) := by
  simp [Matrix.mul_apply, Matrix.transpose_apply, twoPointColumns,
    mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  ring

def fourthLevelOddPick : Fin 8 → Fin 15 := ![0,1,3,4,7,8,9,10]
def fourthLevelEvenPick : Fin 7 → Fin 15 := fun i => fourthLevelOddPick i.succ
def fourthLevelOddWeight (i : Fin 8) : ℝ := if i = 0 then 1/2 else 1

def fourthLevelReflectionPick : Fin 8 ⊕ Fin 7 → Fin 15 :=
  Sum.elim fourthLevelOddPick fourthLevelEvenPick
def fourthLevelReflectionU : Fin 8 ⊕ Fin 7 → ℝ :=
  Sum.elim fourthLevelOddWeight (fun _ => 1)
def fourthLevelReflectionV : Fin 8 ⊕ Fin 7 → ℝ :=
  Sum.elim fourthLevelOddWeight (fun _ => -1)

/-- Unnormalized reflection: root, seven symmetric pairs, seven antisymmetric pairs. -/
def fourthLevelReflection : Matrix (Fin 15) (Fin 8 ⊕ Fin 7) ℝ :=
  twoPointColumns fourthLevelReflectionPick
    (fourthLevelReflectIndex ∘ fourthLevelReflectionPick)
    fourthLevelReflectionU fourthLevelReflectionV

def fourthLevelOddBlock (K : Matrix (Fin 15) (Fin 15) ℝ) :
    Matrix (Fin 8) (Fin 8) ℝ :=
  fun i j => 2*fourthLevelOddWeight i*fourthLevelOddWeight j*
    (K (fourthLevelOddPick i) (fourthLevelOddPick j) +
      K (fourthLevelOddPick i) (fourthLevelReflectIndex (fourthLevelOddPick j)))

def fourthLevelEvenBlock (K : Matrix (Fin 15) (Fin 15) ℝ) :
    Matrix (Fin 7) (Fin 7) ℝ :=
  fun i j => 2*(K (fourthLevelEvenPick i) (fourthLevelEvenPick j) -
    K (fourthLevelEvenPick i) (fourthLevelReflectIndex (fourthLevelEvenPick j)))

theorem fourthLevelReflection_congruence
    (K : Matrix (Fin 15) (Fin 15) ℝ)
    (hK : ∀ i j, K (fourthLevelReflectIndex i) (fourthLevelReflectIndex j) = K i j) :
    fourthLevelReflection.transpose * K * fourthLevelReflection =
      Matrix.fromBlocks (fourthLevelOddBlock K) 0 0 (fourthLevelEvenBlock K) := by
  have hcross (i j : Fin 15) :
      K (fourthLevelReflectIndex i) j = K i (fourthLevelReflectIndex j) := by
    simpa only [fourthLevelReflectIndex_involutive j] using hK i (fourthLevelReflectIndex j)
  ext i j
  simp only [fourthLevelReflection, twoPointColumns_congruence]
  cases i <;> cases j <;>
    simp only [fourthLevelReflectionPick, fourthLevelReflectionU,
      fourthLevelReflectionV, Sum.elim_inl, Sum.elim_inr, Function.comp_apply,
      Matrix.fromBlocks, Matrix.of_apply, Matrix.zero_apply, fourthLevelOddBlock, fourthLevelEvenBlock,
      hK, hcross] <;> ring

theorem fourthLevelJumpHaar_reflection_congruence (C R : ℝ) :
    fourthLevelReflection.transpose * fourthLevelJumpHaar C R * fourthLevelReflection =
      Matrix.fromBlocks (fourthLevelOddBlock (fourthLevelJumpHaar C R)) 0 0
        (fourthLevelEvenBlock (fourthLevelJumpHaar C R)) :=
  fourthLevelReflection_congruence _ (fourthLevelJumpHaar_reflect C R)

theorem fourthLevelReflection_odd_gram :
    fourthLevelOddBlock (1 : Matrix (Fin 15) (Fin 15) ℝ) =
      Matrix.diagonal (fun i => if i = 0 then 1 else 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    dsimp [fourthLevelOddBlock, fourthLevelOddWeight, fourthLevelOddPick,
      fourthLevelReflectIndex, Matrix.one_apply, Matrix.diagonal, Matrix.cons_val] <;> norm_num [Fin.ext_iff]

theorem fourthLevelReflection_even_gram :
    fourthLevelEvenBlock (1 : Matrix (Fin 15) (Fin 15) ℝ) =
      Matrix.diagonal (fun _ => 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    dsimp [fourthLevelEvenBlock, fourthLevelEvenPick, fourthLevelOddPick,
      fourthLevelReflectIndex, Matrix.one_apply, Matrix.diagonal, Matrix.cons_val] <;> norm_num [Fin.ext_iff]

theorem fourthLevelReflection_gram :
    fourthLevelReflection.transpose * fourthLevelReflection =
      Matrix.fromBlocks (Matrix.diagonal (fun i : Fin 8 => if i = 0 then 1 else 2))
        0 0 (Matrix.diagonal (fun _ : Fin 7 => 2)) := by
  have h := fourthLevelReflection_congruence (1 : Matrix (Fin 15) (Fin 15) ℝ)
    (by intro i j
        simp only [Matrix.one_apply, fourthLevelReflectIndex_involutive.injective.eq_iff])
  simpa only [Matrix.mul_one, fourthLevelReflection_odd_gram,
    fourthLevelReflection_even_gram] using h

def fourthLevelReflectionCoordinates (c : Fin 15 → ℝ) : Fin 8 ⊕ Fin 7 → ℝ :=
  Sum.elim
    (fun i => if i = 0 then c 0 else
      (c (fourthLevelOddPick i) + c (fourthLevelReflectIndex (fourthLevelOddPick i)))/2)
    (fun i => (c (fourthLevelEvenPick i) -
      c (fourthLevelReflectIndex (fourthLevelEvenPick i)))/2)

theorem fourthLevelReflection_mulVec_coordinates (c : Fin 15 → ℝ) :
    fourthLevelReflection.mulVec (fourthLevelReflectionCoordinates c) = c := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_succ,
      fourthLevelReflection, twoPointColumns, fourthLevelReflectionPick,
      fourthLevelReflectionU, fourthLevelReflectionV, fourthLevelReflectionCoordinates,
      fourthLevelOddPick, fourthLevelEvenPick, fourthLevelOddWeight,
      fourthLevelReflectIndex, Matrix.cons_val] <;> ring


/-- The auxiliary changes only the live linear coefficient. -/
theorem fourthLevelCellKernel_coefficient_difference (C C0 R : ℝ) :
    fourthLevelCellKernel C R - fourthLevelCellKernel C0 R =
      (C-C0) • dyadicCellKernel R 4 (fun x y => |x-y|) := by
  rw [← fourthLevelArithmeticCell_grid C R, ← fourthLevelArithmeticCell_grid C0 R]
  ext i j
  change fourthLevelArithmeticCell C _ _ _ _ - fourthLevelArithmeticCell C0 _ _ _ _ =
    (C-C0) * (∫ x in dyadicCellLeft R 4 i..dyadicCellRight R 4 i,
      ∫ y in dyadicCellLeft R 4 j..dyadicCellRight R 4 j, |x-y|)
  rw [integral_integral_abs_sub]
  unfold fourthLevelArithmeticCell
  ring

theorem fourthLevelHaarModel_coefficient_difference (C C0 R : ℝ) :
    fourthLevelHaarModel C R - fourthLevelHaarModel C0 R =
      (C-C0) • finiteDyadicHaarCompression 4
        (dyadicCellKernel R 4 (fun x y => |x-y|)) := by
  unfold fourthLevelHaarModel finiteDyadicHaarCompression
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, fourthLevelCellKernel_coefficient_difference]
  simp only [Matrix.mul_smul, Matrix.smul_mul]

/-- Exact coefficient comparison through the established negative absolute-kernel energy. -/
theorem fourthLevelHaarModel_quadratic_coefficient_difference
    (C C0 : ℝ) {R : ℝ} (hR : 0 ≤ R) (c : FiniteDyadicHaarIndex 4 → ℝ) :
    dotProduct c ((fourthLevelHaarModel C R).mulVec c) -
      dotProduct c ((fourthLevelHaarModel C0 R).mulVec c) =
      2*(C0-C)*(∫ t, (∫ x in Set.Iic t, dyadicHaarStep R 4 c x)^2) := by
  rw [← dotProduct_sub, ← Matrix.sub_mulVec, fourthLevelHaarModel_coefficient_difference,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    ← dyadicHaarStep_quadratic_reconstruction hR 4
      (fun x y => |x-y|) ((continuous_fst.sub continuous_snd).abs),
    dyadicHaarStep_absKernel_integral_eq hR 4 c]
  ring

theorem fourthLevelHaarModel_antitone {C C0 R : ℝ}
    (hC : C ≤ C0) (hR : 0 ≤ R) (c : FiniteDyadicHaarIndex 4 → ℝ) :
    dotProduct c ((fourthLevelHaarModel C0 R).mulVec c) ≤
      dotProduct c ((fourthLevelHaarModel C R).mulVec c) := by
  apply sub_nonneg.mp
  rw [fourthLevelHaarModel_quadratic_coefficient_difference C C0 hR]
  exact mul_nonneg (by positivity)
    (MeasureTheory.integral_nonneg (fun _ => sq_nonneg _))

theorem fourthLevelHaarModel_auxiliary_le_finite
    {R : ℝ} (hR : 0 ≤ R) (c : FiniteDyadicHaarIndex 4 → ℝ) :
    dotProduct c ((fourthLevelHaarModel (5373/2000) R).mulVec c) ≤
      dotProduct c ((arithmeticScrewApproxHaarMatrix R 4 2 5).mulVec c) := by
  rw [arithmeticScrewApproxHaarMatrix_four_eq_model]
  exact fourthLevelHaarModel_antitone screwLinearCoefficient_le_5373_div_2000 hR c

/-- The established admissible signed comparison, specialized to the next exact parameters. -/
theorem arithmeticScrewApproxHaarMatrix_four_sixteenth_le_actual
    (c : FiniteDyadicHaarIndex 4 → ℝ) :
    dotProduct c ((arithmeticScrewApproxHaarMatrix (1/16) 4 2 5).mulVec c) ≤
      dotProduct c ((arithmeticScrewHaarMatrix (1/16) 4).mulVec c) :=
  arithmeticScrewApproxHaarMatrix_quadratic_le (by norm_num) 4 2 5
    arithmeticScrewApprox_sixteenth_cutoff c

/-- Exact endpoint distance, with no modular wrapping. -/
def fourthLevelDistance (i j : Fin 17) : Fin 17 :=
  ⟨i.val-j.val+(j.val-i.val), by omega⟩

theorem fourthLevelDistance_cast (i j : Fin 17) :
    ((fourthLevelDistance i j).val : ℝ) = |(i.val : ℝ)-j.val| := by
  by_cases hij : i.val ≤ j.val
  · have hh : (i.val : ℝ) ≤ j.val := by exact_mod_cast hij
    simp [fourthLevelDistance, Nat.sub_eq_zero_of_le hij, Nat.cast_sub hij,
      abs_of_nonpos (sub_nonpos.mpr hh)]
  · have hji : j.val ≤ i.val := by omega
    have hh : (j.val : ℝ) ≤ i.val := by exact_mod_cast hji
    simp [fourthLevelDistance, Nat.sub_eq_zero_of_le hji, Nat.cast_sub hji,
      abs_of_nonneg (sub_nonneg.mpr hh)]

def fourthLevelValueMatrix (p : Fin 17 → ℝ) : Matrix (Fin 17) (Fin 17) ℝ :=
  fun i j => p (fourthLevelDistance i j)

def fourthLevelValueHaar (p : Fin 17 → ℝ) : Matrix (Fin 15) (Fin 15) ℝ :=
  -(fourthLevelJumps.transpose * fourthLevelValueMatrix p * fourthLevelJumps)

theorem fourthLevelValueHaar_apply (p : Fin 17 → ℝ) (i j : Fin 15) :
    fourthLevelValueHaar p i j =
      -(fourthLevelValueMatrix p (fourthLevelLeft i) (fourthLevelLeft j) -
      2*fourthLevelValueMatrix p (fourthLevelLeft i) (fourthLevelMid j) +
      fourthLevelValueMatrix p (fourthLevelLeft i) (fourthLevelRight j) -
      2*fourthLevelValueMatrix p (fourthLevelMid i) (fourthLevelLeft j) +
      4*fourthLevelValueMatrix p (fourthLevelMid i) (fourthLevelMid j) -
      2*fourthLevelValueMatrix p (fourthLevelMid i) (fourthLevelRight j) +
      fourthLevelValueMatrix p (fourthLevelRight i) (fourthLevelLeft j) -
      2*fourthLevelValueMatrix p (fourthLevelRight i) (fourthLevelMid j) +
      fourthLevelValueMatrix p (fourthLevelRight i) (fourthLevelRight j)) := by
  simp only [fourthLevelValueHaar, Matrix.neg_apply, fourthLevelJumps,
    threePointJumps_congruence]

theorem fourthLevelPrimitiveMatrix_sixteenth (C : ℝ) :
    fourthLevelPrimitiveMatrix C (1/16) =
      fourthLevelValueMatrix (fun i => fourthLevelPrimitive C (i.val/128)) := by
  ext i j
  rw [fourthLevelPrimitiveMatrix_grid C (by norm_num)]
  unfold fourthLevelGridPrimitive fourthLevelValueMatrix
  dsimp only
  rw [fourthLevelDistance_cast]
  push_cast
  congr 1
  ring

theorem fourthLevelJumpHaar_sixteenth (C : ℝ) :
    fourthLevelJumpHaar C (1/16) =
      fourthLevelValueHaar (fun i => fourthLevelPrimitive C (i.val/128)) := by
  rw [fourthLevelJumpHaar, fourthLevelPrimitiveMatrix_sixteenth]
  rfl


theorem exp_double_bounds_of_abs {x a b : ℝ}
    (h : |Real.exp x-a| ≤ b) (ha : 0 ≤ a-b) :
    (a-b)^2 ≤ Real.exp (2*x) ∧ Real.exp (2*x) ≤ (a+b)^2 := by
  have hl : a-b ≤ Real.exp x := by linarith [(abs_le.mp h).1]
  have hu : Real.exp x ≤ a+b := by linarith [(abs_le.mp h).2]
  have he : Real.exp (2*x) = (Real.exp x)^2 := by
    rw [show 2*x = x+x by ring, Real.exp_add]
    ring
  rw [he]
  exact ⟨(sq_le_sq₀ ha (Real.exp_pos x).le).mpr hl,
    (sq_le_sq₀ (Real.exp_pos x).le ((Real.exp_pos x).le.trans hu)).mpr hu⟩

theorem fourthLevelPrimitive_sixteenth_1_bounds :
    (-16007754766/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (1/128) ∧
    fourthLevelPrimitive (5373/2000) (1/128) ≤ (-16007754765/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (1/256 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-5/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-9/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-13/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-17/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]


theorem fourthLevelPrimitive_sixteenth_2_bounds :
    (-124465267437/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (2/128) ∧
    fourthLevelPrimitive (5373/2000) (2/128) ≤ (-124465267436/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (2/256 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-10/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-18/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-26/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-34/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]


theorem fourthLevelPrimitive_sixteenth_3_bounds :
    (-408211913058/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (3/128) ∧
    fourthLevelPrimitive (5373/2000) (3/128) ≤ (-408211913057/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (3/256 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-15/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-27/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-39/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-51/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]


theorem fourthLevelPrimitive_sixteenth_4_bounds :
    (-940154374694/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (4/128) ∧
    fourthLevelPrimitive (5373/2000) (4/128) ≤ (-940154374693/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (4/256 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-20/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-36/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-52/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-68/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]


theorem fourthLevelPrimitive_sixteenth_5_bounds :
    (-1783847058417/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (5/128) ∧
    fourthLevelPrimitive (5373/2000) (5/128) ≤ (-1783847058416/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (5/256 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-25/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-45/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-65/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-85/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]


theorem fourthLevelPrimitive_sixteenth_6_bounds :
    (-2994045351101/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (6/128) ∧
    fourthLevelPrimitive (5373/2000) (6/128) ≤ (-2994045351100/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (6/256 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-30/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-54/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-78/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-102/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]


theorem fourthLevelPrimitive_sixteenth_7_bounds :
    (-4617233164834/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (7/128) ∧
    fourthLevelPrimitive (5373/2000) (7/128) ≤ (-4617233164833/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (7/256 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-35/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-63/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-91/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-119/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]


theorem fourthLevelPrimitive_sixteenth_8_bounds :
    (-6692126130458/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (8/128) ∧
    fourthLevelPrimitive (5373/2000) (8/128) ≤ (-6692126130457/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (8/256 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-40/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-72/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-104/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-136/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]


theorem fourthLevelPrimitive_sixteenth_9_bounds :
    (-9250151726173/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (9/128) ∧
    fourthLevelPrimitive (5373/2000) (9/128) ≤ (-9250151726172/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (9/256 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-45/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-81/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-117/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-153/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]


theorem fourthLevelPrimitive_sixteenth_10_bounds :
    (-12315907555091/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (10/128) ∧
    fourthLevelPrimitive (5373/2000) (10/128) ≤ (-12315907555090/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (10/256 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-50/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-90/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-130/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-170/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]


theorem fourthLevelPrimitive_sixteenth_11_bounds :
    (-15907598917710/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (11/128) ∧
    fourthLevelPrimitive (5373/2000) (11/128) ≤ (-15907598917709/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (11/256 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-55/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-99/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-143/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-187/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]


theorem fourthLevelPrimitive_sixteenth_12_bounds :
    (-20037456761388/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (12/128) ∧
    fourthLevelPrimitive (5373/2000) (12/128) ≤ (-20037456761387/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (12/256 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-60/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-108/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-156/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-204/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]


theorem fourthLevelPrimitive_sixteenth_13_bounds :
    (-24712137028672/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (13/128) ∧
    fourthLevelPrimitive (5373/2000) (13/128) ≤ (-24712137028671/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (13/256 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-65/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-117/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-169/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-221/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]


theorem fourthLevelPrimitive_sixteenth_14_bounds :
    (-29933102369600/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (14/128) ∧
    fourthLevelPrimitive (5373/2000) (14/128) ≤ (-29933102369599/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (14/256 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-70/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-126/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-182/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-238/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]


theorem fourthLevelPrimitive_sixteenth_15_bounds :
    (-35696987129701/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (15/128) ∧
    fourthLevelPrimitive (5373/2000) (15/128) ≤ (-35696987129700/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (15/256 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-75/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-135/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-195/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-255/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]


theorem fourthLevelPrimitive_sixteenth_16_bounds :
    (-41995946475046/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (16/128) ∧
    fourthLevelPrimitive (5373/2000) (16/128) ≤ (-41995946475045/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (16/256 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-80/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-144/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-208/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-272/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]


theorem fourthLevelOddEntry_0_0 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 0 0 = 8*p 8 - 2*p 16 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1/2) * (1/2) * (-(p 0-2*p 8+p 16-2*p 8+4*p 0-2*p 8+p 16-2*p 8+p 0) + -(p 0-2*p 8+p 16-2*p 8+4*p 0-2*p 8+p 16-2*p 8+p 0)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_0_1 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 0 1 = - 4*p 4 + 4*p 12 - 2*p 16 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1/2) * 1 * (-(p 0-2*p 4+p 8-2*p 8+4*p 4-2*p 0+p 16-2*p 12+p 8) + -(p 8-2*p 12+p 16-2*p 0+4*p 4-2*p 8+p 8-2*p 4+p 0)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_0_2 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 0 2 = 4*p 2 + 2*p 4 - 8*p 6 + 4*p 8 - 2*p 12 + 4*p 14 - 2*p 16 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1/2) * 1 * (-(p 0-2*p 2+p 4-2*p 8+4*p 6-2*p 4+p 16-2*p 14+p 12) + -(p 12-2*p 14+p 16-2*p 4+4*p 6-2*p 8+p 4-2*p 2+p 0)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_0_3 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 0 3 = - 8*p 2 + 2*p 4 + 4*p 6 - 4*p 8 + 4*p 10 - 2*p 12 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1/2) * 1 * (-(p 4-2*p 6+p 8-2*p 4+4*p 2-2*p 0+p 12-2*p 10+p 8) + -(p 8-2*p 10+p 12-2*p 0+4*p 2-2*p 4+p 8-2*p 6+p 4)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_0_4 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 0 4 = 4*p 1 - 2*p 2 + 4*p 6 - 8*p 7 + 4*p 8 - 2*p 14 + 4*p 15 - 2*p 16 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1/2) * 1 * (-(p 0-2*p 1+p 2-2*p 8+4*p 7-2*p 6+p 16-2*p 15+p 14) + -(p 14-2*p 15+p 16-2*p 6+4*p 7-2*p 8+p 2-2*p 1+p 0)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_0_5 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 0 5 = - 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 2*p 12 + 4*p 13 - 2*p 14 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1/2) * 1 * (-(p 2-2*p 3+p 4-2*p 6+4*p 5-2*p 4+p 14-2*p 13+p 12) + -(p 12-2*p 13+p 14-2*p 4+4*p 5-2*p 6+p 4-2*p 3+p 2)) = _

  ring

theorem fourthLevelOddEntry_0_6 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 0 6 = 4*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 2*p 6 - 2*p 10 + 4*p 11 - 2*p 12 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1/2) * 1 * (-(p 4-2*p 5+p 6-2*p 4+4*p 3-2*p 2+p 12-2*p 11+p 10) + -(p 10-2*p 11+p 12-2*p 2+4*p 3-2*p 4+p 6-2*p 5+p 4)) = _

  ring

theorem fourthLevelOddEntry_0_7 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 0 7 = - 8*p 1 + 4*p 2 - 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1/2) * 1 * (-(p 6-2*p 7+p 8-2*p 2+4*p 1-2*p 0+p 10-2*p 9+p 8) + -(p 8-2*p 9+p 10-2*p 0+4*p 1-2*p 2+p 8-2*p 7+p 6)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_1_0 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 1 0 = - 4*p 4 + 4*p 12 - 2*p 16 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * (1/2) * (-(p 0-2*p 8+p 16-2*p 4+4*p 4-2*p 12+p 8-2*p 0+p 8) + -(p 0-2*p 8+p 16-2*p 4+4*p 4-2*p 12+p 8-2*p 0+p 8)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_1_1 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 1 1 = 24*p 4 - 16*p 8 + 8*p 12 - 2*p 16 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 0-2*p 4+p 8-2*p 4+4*p 0-2*p 4+p 8-2*p 4+p 0) + -(p 8-2*p 12+p 16-2*p 4+4*p 8-2*p 12+p 0-2*p 4+p 8)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_1_2 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 1 2 = - 4*p 2 - 2*p 4 + 8*p 6 - 8*p 10 + 2*p 12 + 4*p 14 - 2*p 16 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 0-2*p 2+p 4-2*p 4+4*p 2-2*p 0+p 8-2*p 6+p 4) + -(p 12-2*p 14+p 16-2*p 8+4*p 10-2*p 12+p 4-2*p 6+p 8)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_1_3 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 1 3 = 2*p 4 - 4*p 6 + 4*p 10 - 2*p 12 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 4-2*p 6+p 8-2*p 0+4*p 2-2*p 4+p 4-2*p 2+p 0) + -(p 8-2*p 10+p 12-2*p 4+4*p 6-2*p 8+p 0-2*p 2+p 4)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_1_4 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 1 4 = 4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 4*p 8 + 4*p 10 - 8*p 11 + 4*p 12 - 2*p 14 + 4*p 15 - 2*p 16 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 0-2*p 1+p 2-2*p 4+4*p 3-2*p 2+p 8-2*p 7+p 6) + -(p 14-2*p 15+p 16-2*p 10+4*p 11-2*p 12+p 6-2*p 7+p 8)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_1_5 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 1 5 = - 8*p 1 + 2*p 2 + 4*p 3 - 6*p 4 + 8*p 5 - 4*p 6 + 4*p 8 - 8*p 9 + 4*p 10 - 2*p 12 + 4*p 13 - 2*p 14 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 2-2*p 3+p 4-2*p 2+4*p 1-2*p 0+p 6-2*p 5+p 4) + -(p 12-2*p 13+p 14-2*p 8+4*p 9-2*p 10+p 4-2*p 5+p 6)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_1_6 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 1 6 = - 8*p 1 + 8*p 3 - 6*p 4 + 4*p 5 + 2*p 6 - 8*p 7 + 4*p 8 - 2*p 10 + 4*p 11 - 2*p 12 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 4-2*p 5+p 6-2*p 0+4*p 1-2*p 2+p 4-2*p 3+p 2) + -(p 10-2*p 11+p 12-2*p 6+4*p 7-2*p 8+p 2-2*p 3+p 4)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_1_7 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 1 7 = 8*p 1 - 8*p 3 + 8*p 4 - 8*p 5 + 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 6-2*p 7+p 8-2*p 2+4*p 3-2*p 4+p 2-2*p 1+p 0) + -(p 8-2*p 9+p 10-2*p 4+4*p 5-2*p 6+p 0-2*p 1+p 2)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_2_0 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 2 0 = 4*p 2 + 2*p 4 - 8*p 6 + 4*p 8 - 2*p 12 + 4*p 14 - 2*p 16 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * (1/2) * (-(p 0-2*p 8+p 16-2*p 2+4*p 6-2*p 14+p 4-2*p 4+p 12) + -(p 0-2*p 8+p 16-2*p 2+4*p 6-2*p 14+p 4-2*p 4+p 12)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_2_1 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 2 1 = - 4*p 2 - 2*p 4 + 8*p 6 - 8*p 10 + 2*p 12 + 4*p 14 - 2*p 16 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 0-2*p 4+p 8-2*p 2+4*p 2-2*p 6+p 4-2*p 0+p 4) + -(p 8-2*p 12+p 16-2*p 6+4*p 10-2*p 14+p 4-2*p 8+p 12)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_2_2 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 2 2 = 16*p 2 - 4*p 4 - 2*p 8 + 8*p 10 - 12*p 12 + 8*p 14 - 2*p 16 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 0-2*p 2+p 4-2*p 2+4*p 0-2*p 2+p 4-2*p 2+p 0) + -(p 12-2*p 14+p 16-2*p 10+4*p 12-2*p 14+p 8-2*p 10+p 12)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_2_3 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 2 3 = 8*p 2 - 14*p 4 + 16*p 6 - 14*p 8 + 8*p 10 - 2*p 12 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 4-2*p 6+p 8-2*p 2+4*p 4-2*p 6+p 0-2*p 2+p 4) + -(p 8-2*p 10+p 12-2*p 6+4*p 8-2*p 10+p 4-2*p 6+p 8)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_2_4 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 2 4 = - 4*p 1 + 4*p 3 - 2*p 4 - 2*p 10 + 4*p 11 + 2*p 12 - 8*p 13 + 2*p 14 + 4*p 15 - 2*p 16 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 0-2*p 1+p 2-2*p 2+4*p 1-2*p 0+p 4-2*p 3+p 2) + -(p 14-2*p 15+p 16-2*p 12+4*p 13-2*p 14+p 10-2*p 11+p 12)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_2_5 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 2 5 = - 4*p 1 + 4*p 3 - 2*p 4 - 2*p 8 + 4*p 9 + 2*p 10 - 8*p 11 + 2*p 12 + 4*p 13 - 2*p 14 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 2-2*p 3+p 4-2*p 0+4*p 1-2*p 2+p 2-2*p 1+p 0) + -(p 12-2*p 13+p 14-2*p 10+4*p 11-2*p 12+p 8-2*p 9+p 10)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_2_6 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 2 6 = 4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 6 + 4*p 7 + 2*p 8 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 4-2*p 5+p 6-2*p 2+4*p 3-2*p 4+p 0-2*p 1+p 2) + -(p 10-2*p 11+p 12-2*p 8+4*p 9-2*p 10+p 6-2*p 7+p 8)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_2_7 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 2 7 = - 2*p 2 + 4*p 3 - 4*p 5 + 4*p 6 - 4*p 7 + 4*p 9 - 2*p 10 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 6-2*p 7+p 8-2*p 4+4*p 5-2*p 6+p 2-2*p 3+p 4) + -(p 8-2*p 9+p 10-2*p 6+4*p 7-2*p 8+p 4-2*p 5+p 6)) = _

  ring

theorem fourthLevelOddEntry_3_0 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 3 0 = - 8*p 2 + 2*p 4 + 4*p 6 - 4*p 8 + 4*p 10 - 2*p 12 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * (1/2) * (-(p 4-2*p 4+p 12-2*p 6+4*p 2-2*p 10+p 8-2*p 0+p 8) + -(p 4-2*p 4+p 12-2*p 6+4*p 2-2*p 10+p 8-2*p 0+p 8)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_3_1 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 3 1 = 2*p 4 - 4*p 6 + 4*p 10 - 2*p 12 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 4-2*p 0+p 4-2*p 6+4*p 2-2*p 2+p 8-2*p 4+p 0) + -(p 4-2*p 8+p 12-2*p 2+4*p 6-2*p 10+p 0-2*p 4+p 8)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_3_2 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 3 2 = 8*p 2 - 14*p 4 + 16*p 6 - 14*p 8 + 8*p 10 - 2*p 12 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 4-2*p 2+p 0-2*p 6+4*p 4-2*p 2+p 8-2*p 6+p 4) + -(p 8-2*p 10+p 12-2*p 6+4*p 8-2*p 10+p 4-2*p 6+p 8)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_3_3 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 3 3 = 24*p 2 - 16*p 4 + 8*p 6 - 2*p 8 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 0-2*p 2+p 4-2*p 2+4*p 0-2*p 2+p 4-2*p 2+p 0) + -(p 4-2*p 6+p 8-2*p 2+4*p 4-2*p 6+p 0-2*p 2+p 4)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_3_4 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 3 4 = - 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 8*p 7 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 4-2*p 3+p 2-2*p 6+4*p 5-2*p 4+p 8-2*p 7+p 6) + -(p 10-2*p 11+p 12-2*p 8+4*p 9-2*p 10+p 6-2*p 7+p 8)) = _

  ring

theorem fourthLevelOddEntry_3_5 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 3 5 = 4*p 1 + 2*p 2 - 8*p 3 + 8*p 5 - 8*p 7 + 2*p 8 + 4*p 9 - 2*p 10 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 2-2*p 1+p 0-2*p 4+4*p 3-2*p 2+p 6-2*p 5+p 4) + -(p 8-2*p 9+p 10-2*p 6+4*p 7-2*p 8+p 4-2*p 5+p 6)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_3_6 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 3 6 = - 4*p 1 - 2*p 2 + 8*p 3 - 8*p 5 + 2*p 6 + 4*p 7 - 2*p 8 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 0-2*p 1+p 2-2*p 2+4*p 1-2*p 0+p 4-2*p 3+p 2) + -(p 6-2*p 7+p 8-2*p 4+4*p 5-2*p 6+p 2-2*p 3+p 4)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_3_7 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 3 7 = 2*p 2 - 4*p 3 + 4*p 5 - 2*p 6 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 2-2*p 3+p 4-2*p 0+4*p 1-2*p 2+p 2-2*p 1+p 0) + -(p 4-2*p 5+p 6-2*p 2+4*p 3-2*p 4+p 0-2*p 1+p 2)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_4_0 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 4 0 = 4*p 1 - 2*p 2 + 4*p 6 - 8*p 7 + 4*p 8 - 2*p 14 + 4*p 15 - 2*p 16 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * (1/2) * (-(p 0-2*p 8+p 16-2*p 1+4*p 7-2*p 15+p 2-2*p 6+p 14) + -(p 0-2*p 8+p 16-2*p 1+4*p 7-2*p 15+p 2-2*p 6+p 14)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_4_1 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 4 1 = 4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 4*p 8 + 4*p 10 - 8*p 11 + 4*p 12 - 2*p 14 + 4*p 15 - 2*p 16 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 0-2*p 4+p 8-2*p 1+4*p 3-2*p 7+p 2-2*p 2+p 6) + -(p 8-2*p 12+p 16-2*p 7+4*p 11-2*p 15+p 6-2*p 10+p 14)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_4_2 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 4 2 = - 4*p 1 + 4*p 3 - 2*p 4 - 2*p 10 + 4*p 11 + 2*p 12 - 8*p 13 + 2*p 14 + 4*p 15 - 2*p 16 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 0-2*p 2+p 4-2*p 1+4*p 1-2*p 3+p 2-2*p 0+p 2) + -(p 12-2*p 14+p 16-2*p 11+4*p 13-2*p 15+p 10-2*p 12+p 14)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_4_3 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 4 3 = - 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 8*p 7 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 4-2*p 6+p 8-2*p 3+4*p 5-2*p 7+p 2-2*p 4+p 6) + -(p 8-2*p 10+p 12-2*p 7+4*p 9-2*p 11+p 6-2*p 8+p 10)) = _

  ring

theorem fourthLevelOddEntry_4_4 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 4 4 = 16*p 1 - 4*p 2 - 2*p 12 + 8*p 13 - 12*p 14 + 8*p 15 - 2*p 16 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 0-2*p 1+p 2-2*p 1+4*p 0-2*p 1+p 2-2*p 1+p 0) + -(p 14-2*p 15+p 16-2*p 13+4*p 14-2*p 15+p 12-2*p 13+p 14)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_4_5 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 4 5 = 8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 10 + 8*p 11 - 12*p 12 + 8*p 13 - 2*p 14 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 2-2*p 3+p 4-2*p 1+4*p 2-2*p 3+p 0-2*p 1+p 2) + -(p 12-2*p 13+p 14-2*p 11+4*p 12-2*p 13+p 10-2*p 11+p 12)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_4_6 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 4 6 = - 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 - 2*p 8 + 8*p 9 - 12*p 10 + 8*p 11 - 2*p 12 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 4-2*p 5+p 6-2*p 3+4*p 4-2*p 5+p 2-2*p 3+p 4) + -(p 10-2*p 11+p 12-2*p 9+4*p 10-2*p 11+p 8-2*p 9+p 10)) = _

  ring

theorem fourthLevelOddEntry_4_7 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 4 7 = - 2*p 4 + 8*p 5 - 14*p 6 + 16*p 7 - 14*p 8 + 8*p 9 - 2*p 10 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 6-2*p 7+p 8-2*p 5+4*p 6-2*p 7+p 4-2*p 5+p 6) + -(p 8-2*p 9+p 10-2*p 7+4*p 8-2*p 9+p 6-2*p 7+p 8)) = _

  ring

theorem fourthLevelOddEntry_5_0 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 5 0 = - 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 2*p 12 + 4*p 13 - 2*p 14 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * (1/2) * (-(p 2-2*p 6+p 14-2*p 3+4*p 5-2*p 13+p 4-2*p 4+p 12) + -(p 2-2*p 6+p 14-2*p 3+4*p 5-2*p 13+p 4-2*p 4+p 12)) = _

  ring

theorem fourthLevelOddEntry_5_1 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 5 1 = - 8*p 1 + 2*p 2 + 4*p 3 - 6*p 4 + 8*p 5 - 4*p 6 + 4*p 8 - 8*p 9 + 4*p 10 - 2*p 12 + 4*p 13 - 2*p 14 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 2-2*p 2+p 6-2*p 3+4*p 1-2*p 5+p 4-2*p 0+p 4) + -(p 6-2*p 10+p 14-2*p 5+4*p 9-2*p 13+p 4-2*p 8+p 12)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_5_2 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 5 2 = - 4*p 1 + 4*p 3 - 2*p 4 - 2*p 8 + 4*p 9 + 2*p 10 - 8*p 11 + 2*p 12 + 4*p 13 - 2*p 14 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 2-2*p 0+p 2-2*p 3+4*p 1-2*p 1+p 4-2*p 2+p 0) + -(p 10-2*p 12+p 14-2*p 9+4*p 11-2*p 13+p 8-2*p 10+p 12)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_5_3 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 5 3 = 4*p 1 + 2*p 2 - 8*p 3 + 8*p 5 - 8*p 7 + 2*p 8 + 4*p 9 - 2*p 10 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 2-2*p 4+p 6-2*p 1+4*p 3-2*p 5+p 0-2*p 2+p 4) + -(p 6-2*p 8+p 10-2*p 5+4*p 7-2*p 9+p 4-2*p 6+p 8)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_5_4 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 5 4 = 8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 10 + 8*p 11 - 12*p 12 + 8*p 13 - 2*p 14 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 2-2*p 1+p 0-2*p 3+4*p 2-2*p 1+p 4-2*p 3+p 2) + -(p 12-2*p 13+p 14-2*p 11+4*p 12-2*p 13+p 10-2*p 11+p 12)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_5_5 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 5 5 = 16*p 1 - 4*p 2 - 2*p 8 + 8*p 9 - 12*p 10 + 8*p 11 - 2*p 12 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 0-2*p 1+p 2-2*p 1+4*p 0-2*p 1+p 2-2*p 1+p 0) + -(p 10-2*p 11+p 12-2*p 9+4*p 10-2*p 11+p 8-2*p 9+p 10)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_5_6 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 5 6 = 8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 6 + 8*p 7 - 12*p 8 + 8*p 9 - 2*p 10 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 2-2*p 3+p 4-2*p 1+4*p 2-2*p 3+p 0-2*p 1+p 2) + -(p 8-2*p 9+p 10-2*p 7+4*p 8-2*p 9+p 6-2*p 7+p 8)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_5_7 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 5 7 = - 2*p 2 + 8*p 3 - 14*p 4 + 16*p 5 - 14*p 6 + 8*p 7 - 2*p 8 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 4-2*p 5+p 6-2*p 3+4*p 4-2*p 5+p 2-2*p 3+p 4) + -(p 6-2*p 7+p 8-2*p 5+4*p 6-2*p 7+p 4-2*p 5+p 6)) = _

  ring

theorem fourthLevelOddEntry_6_0 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 6 0 = 4*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 2*p 6 - 2*p 10 + 4*p 11 - 2*p 12 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * (1/2) * (-(p 4-2*p 4+p 12-2*p 5+4*p 3-2*p 11+p 6-2*p 2+p 10) + -(p 4-2*p 4+p 12-2*p 5+4*p 3-2*p 11+p 6-2*p 2+p 10)) = _

  ring

theorem fourthLevelOddEntry_6_1 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 6 1 = - 8*p 1 + 8*p 3 - 6*p 4 + 4*p 5 + 2*p 6 - 8*p 7 + 4*p 8 - 2*p 10 + 4*p 11 - 2*p 12 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 4-2*p 0+p 4-2*p 5+4*p 1-2*p 3+p 6-2*p 2+p 2) + -(p 4-2*p 8+p 12-2*p 3+4*p 7-2*p 11+p 2-2*p 6+p 10)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_6_2 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 6 2 = 4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 6 + 4*p 7 + 2*p 8 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 4-2*p 2+p 0-2*p 5+4*p 3-2*p 1+p 6-2*p 4+p 2) + -(p 8-2*p 10+p 12-2*p 7+4*p 9-2*p 11+p 6-2*p 8+p 10)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_6_3 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 6 3 = - 4*p 1 - 2*p 2 + 8*p 3 - 8*p 5 + 2*p 6 + 4*p 7 - 2*p 8 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 0-2*p 2+p 4-2*p 1+4*p 1-2*p 3+p 2-2*p 0+p 2) + -(p 4-2*p 6+p 8-2*p 3+4*p 5-2*p 7+p 2-2*p 4+p 6)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_6_4 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 6 4 = - 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 - 2*p 8 + 8*p 9 - 12*p 10 + 8*p 11 - 2*p 12 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 4-2*p 3+p 2-2*p 5+4*p 4-2*p 3+p 6-2*p 5+p 4) + -(p 10-2*p 11+p 12-2*p 9+4*p 10-2*p 11+p 8-2*p 9+p 10)) = _

  ring

theorem fourthLevelOddEntry_6_5 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 6 5 = 8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 6 + 8*p 7 - 12*p 8 + 8*p 9 - 2*p 10 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 2-2*p 1+p 0-2*p 3+4*p 2-2*p 1+p 4-2*p 3+p 2) + -(p 8-2*p 9+p 10-2*p 7+4*p 8-2*p 9+p 6-2*p 7+p 8)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_6_6 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 6 6 = 16*p 1 - 4*p 2 - 2*p 4 + 8*p 5 - 12*p 6 + 8*p 7 - 2*p 8 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 0-2*p 1+p 2-2*p 1+4*p 0-2*p 1+p 2-2*p 1+p 0) + -(p 6-2*p 7+p 8-2*p 5+4*p 6-2*p 7+p 4-2*p 5+p 6)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_6_7 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 6 7 = 8*p 1 - 14*p 2 + 16*p 3 - 14*p 4 + 8*p 5 - 2*p 6 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 2-2*p 3+p 4-2*p 1+4*p 2-2*p 3+p 0-2*p 1+p 2) + -(p 4-2*p 5+p 6-2*p 3+4*p 4-2*p 5+p 2-2*p 3+p 4)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_7_0 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 7 0 = - 8*p 1 + 4*p 2 - 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * (1/2) * (-(p 6-2*p 2+p 10-2*p 7+4*p 1-2*p 9+p 8-2*p 0+p 8) + -(p 6-2*p 2+p 10-2*p 7+4*p 1-2*p 9+p 8-2*p 0+p 8)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_7_1 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 7 1 = 8*p 1 - 8*p 3 + 8*p 4 - 8*p 5 + 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 6-2*p 2+p 2-2*p 7+4*p 3-2*p 1+p 8-2*p 4+p 0) + -(p 2-2*p 6+p 10-2*p 1+4*p 5-2*p 9+p 0-2*p 4+p 8)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_7_2 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 7 2 = - 2*p 2 + 4*p 3 - 4*p 5 + 4*p 6 - 4*p 7 + 4*p 9 - 2*p 10 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 6-2*p 4+p 2-2*p 7+4*p 5-2*p 3+p 8-2*p 6+p 4) + -(p 6-2*p 8+p 10-2*p 5+4*p 7-2*p 9+p 4-2*p 6+p 8)) = _

  ring

theorem fourthLevelOddEntry_7_3 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 7 3 = 2*p 2 - 4*p 3 + 4*p 5 - 2*p 6 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 2-2*p 0+p 2-2*p 3+4*p 1-2*p 1+p 4-2*p 2+p 0) + -(p 2-2*p 4+p 6-2*p 1+4*p 3-2*p 5+p 0-2*p 2+p 4)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_7_4 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 7 4 = - 2*p 4 + 8*p 5 - 14*p 6 + 16*p 7 - 14*p 8 + 8*p 9 - 2*p 10 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 6-2*p 5+p 4-2*p 7+4*p 6-2*p 5+p 8-2*p 7+p 6) + -(p 8-2*p 9+p 10-2*p 7+4*p 8-2*p 9+p 6-2*p 7+p 8)) = _

  ring

theorem fourthLevelOddEntry_7_5 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 7 5 = - 2*p 2 + 8*p 3 - 14*p 4 + 16*p 5 - 14*p 6 + 8*p 7 - 2*p 8 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 4-2*p 3+p 2-2*p 5+4*p 4-2*p 3+p 6-2*p 5+p 4) + -(p 6-2*p 7+p 8-2*p 5+4*p 6-2*p 7+p 4-2*p 5+p 6)) = _

  ring

theorem fourthLevelOddEntry_7_6 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 7 6 = 8*p 1 - 14*p 2 + 16*p 3 - 14*p 4 + 8*p 5 - 2*p 6 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 2-2*p 1+p 0-2*p 3+4*p 2-2*p 1+p 4-2*p 3+p 2) + -(p 4-2*p 5+p 6-2*p 3+4*p 4-2*p 5+p 2-2*p 3+p 4)) = _
  rw [hp0]
  ring

theorem fourthLevelOddEntry_7_7 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 7 7 = 24*p 1 - 16*p 2 + 8*p 3 - 2*p 4 := by
  simp only [fourthLevelOddBlock, fourthLevelValueHaar_apply]
  change 2 * (1:ℝ) * 1 * (-(p 0-2*p 1+p 2-2*p 1+4*p 0-2*p 1+p 2-2*p 1+p 0) + -(p 2-2*p 3+p 4-2*p 1+4*p 2-2*p 3+p 0-2*p 1+p 2)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_0_0 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 0 0 = 8*p 4 + 8*p 8 - 8*p 12 + 2*p 16 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 0-2*p 4+p 8-2*p 4+4*p 0-2*p 4+p 8-2*p 4+p 0) - -(p 8-2*p 12+p 16-2*p 4+4*p 8-2*p 12+p 0-2*p 4+p 8)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_0_1 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 0 1 = - 4*p 2 + 2*p 4 - 4*p 8 + 8*p 10 - 2*p 12 - 4*p 14 + 2*p 16 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 0-2*p 2+p 4-2*p 4+4*p 2-2*p 0+p 8-2*p 6+p 4) - -(p 12-2*p 14+p 16-2*p 8+4*p 10-2*p 12+p 4-2*p 6+p 8)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_0_2 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 0 2 = - 8*p 2 - 2*p 4 + 12*p 6 - 4*p 8 - 4*p 10 + 2*p 12 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 4-2*p 6+p 8-2*p 0+4*p 2-2*p 4+p 4-2*p 2+p 0) - -(p 8-2*p 10+p 12-2*p 4+4*p 6-2*p 8+p 0-2*p 2+p 4)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_0_3 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 0 3 = 4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 10 + 8*p 11 - 4*p 12 + 2*p 14 - 4*p 15 + 2*p 16 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 0-2*p 1+p 2-2*p 4+4*p 3-2*p 2+p 8-2*p 7+p 6) - -(p 14-2*p 15+p 16-2*p 10+4*p 11-2*p 12+p 6-2*p 7+p 8)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_0_4 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 0 4 = - 8*p 1 + 2*p 2 + 4*p 3 - 2*p 4 - 4*p 8 + 8*p 9 - 4*p 10 + 2*p 12 - 4*p 13 + 2*p 14 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 2-2*p 3+p 4-2*p 2+4*p 1-2*p 0+p 6-2*p 5+p 4) - -(p 12-2*p 13+p 14-2*p 8+4*p 9-2*p 10+p 4-2*p 5+p 6)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_0_5 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 0 5 = - 8*p 1 + 4*p 2 - 2*p 4 + 4*p 5 - 6*p 6 + 8*p 7 - 4*p 8 + 2*p 10 - 4*p 11 + 2*p 12 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 4-2*p 5+p 6-2*p 0+4*p 1-2*p 2+p 4-2*p 3+p 2) - -(p 10-2*p 11+p 12-2*p 6+4*p 7-2*p 8+p 2-2*p 3+p 4)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_0_6 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 0 6 = 4*p 2 - 8*p 3 + 8*p 5 - 6*p 6 + 4*p 7 - 4*p 9 + 2*p 10 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 6-2*p 7+p 8-2*p 2+4*p 3-2*p 4+p 2-2*p 1+p 0) - -(p 8-2*p 9+p 10-2*p 4+4*p 5-2*p 6+p 0-2*p 1+p 2)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_1_0 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 1 0 = - 4*p 2 + 2*p 4 - 4*p 8 + 8*p 10 - 2*p 12 - 4*p 14 + 2*p 16 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 0-2*p 4+p 8-2*p 2+4*p 2-2*p 6+p 4-2*p 0+p 4) - -(p 8-2*p 12+p 16-2*p 6+4*p 10-2*p 14+p 4-2*p 8+p 12)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_1_1 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 1 1 = 16*p 2 - 4*p 4 + 2*p 8 - 8*p 10 + 12*p 12 - 8*p 14 + 2*p 16 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 0-2*p 2+p 4-2*p 2+4*p 0-2*p 2+p 4-2*p 2+p 0) - -(p 12-2*p 14+p 16-2*p 10+4*p 12-2*p 14+p 8-2*p 10+p 12)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_1_2 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 1 2 = 8*p 2 - 10*p 4 + 10*p 8 - 8*p 10 + 2*p 12 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 4-2*p 6+p 8-2*p 2+4*p 4-2*p 6+p 0-2*p 2+p 4) - -(p 8-2*p 10+p 12-2*p 6+4*p 8-2*p 10+p 4-2*p 6+p 8)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_1_3 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 1 3 = - 4*p 1 + 4*p 3 - 2*p 4 + 2*p 10 - 4*p 11 - 2*p 12 + 8*p 13 - 2*p 14 - 4*p 15 + 2*p 16 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 0-2*p 1+p 2-2*p 2+4*p 1-2*p 0+p 4-2*p 3+p 2) - -(p 14-2*p 15+p 16-2*p 12+4*p 13-2*p 14+p 10-2*p 11+p 12)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_1_4 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 1 4 = - 4*p 1 + 4*p 3 - 2*p 4 + 2*p 8 - 4*p 9 - 2*p 10 + 8*p 11 - 2*p 12 - 4*p 13 + 2*p 14 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 2-2*p 3+p 4-2*p 0+4*p 1-2*p 2+p 2-2*p 1+p 0) - -(p 12-2*p 13+p 14-2*p 10+4*p 11-2*p 12+p 8-2*p 9+p 10)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_1_5 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 1 5 = 4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 7 - 2*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 4-2*p 5+p 6-2*p 2+4*p 3-2*p 4+p 0-2*p 1+p 2) - -(p 10-2*p 11+p 12-2*p 8+4*p 9-2*p 10+p 6-2*p 7+p 8)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_1_6 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 1 6 = - 2*p 2 + 4*p 3 + 4*p 4 - 12*p 5 + 12*p 7 - 4*p 8 - 4*p 9 + 2*p 10 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 6-2*p 7+p 8-2*p 4+4*p 5-2*p 6+p 2-2*p 3+p 4) - -(p 8-2*p 9+p 10-2*p 6+4*p 7-2*p 8+p 4-2*p 5+p 6)) = _

  ring

theorem fourthLevelEvenEntry_2_0 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 2 0 = - 8*p 2 - 2*p 4 + 12*p 6 - 4*p 8 - 4*p 10 + 2*p 12 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 4-2*p 0+p 4-2*p 6+4*p 2-2*p 2+p 8-2*p 4+p 0) - -(p 4-2*p 8+p 12-2*p 2+4*p 6-2*p 10+p 0-2*p 4+p 8)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_2_1 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 2 1 = 8*p 2 - 10*p 4 + 10*p 8 - 8*p 10 + 2*p 12 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 4-2*p 2+p 0-2*p 6+4*p 4-2*p 2+p 8-2*p 6+p 4) - -(p 8-2*p 10+p 12-2*p 6+4*p 8-2*p 10+p 4-2*p 6+p 8)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_2_2 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 2 2 = 8*p 2 + 8*p 4 - 8*p 6 + 2*p 8 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 0-2*p 2+p 4-2*p 2+4*p 0-2*p 2+p 4-2*p 2+p 0) - -(p 4-2*p 6+p 8-2*p 2+4*p 4-2*p 6+p 0-2*p 2+p 4)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_2_3 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 2 3 = - 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 4*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 4-2*p 3+p 2-2*p 6+4*p 5-2*p 4+p 8-2*p 7+p 6) - -(p 10-2*p 11+p 12-2*p 8+4*p 9-2*p 10+p 6-2*p 7+p 8)) = _

  ring

theorem fourthLevelEvenEntry_2_4 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 2 4 = 4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 2*p 8 - 4*p 9 + 2*p 10 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 2-2*p 1+p 0-2*p 4+4*p 3-2*p 2+p 6-2*p 5+p 4) - -(p 8-2*p 9+p 10-2*p 6+4*p 7-2*p 8+p 4-2*p 5+p 6)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_2_5 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 2 5 = - 4*p 1 + 2*p 2 - 4*p 4 + 8*p 5 - 2*p 6 - 4*p 7 + 2*p 8 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 0-2*p 1+p 2-2*p 2+4*p 1-2*p 0+p 4-2*p 3+p 2) - -(p 6-2*p 7+p 8-2*p 4+4*p 5-2*p 6+p 2-2*p 3+p 4)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_2_6 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 2 6 = - 8*p 1 - 2*p 2 + 12*p 3 - 4*p 4 - 4*p 5 + 2*p 6 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 2-2*p 3+p 4-2*p 0+4*p 1-2*p 2+p 2-2*p 1+p 0) - -(p 4-2*p 5+p 6-2*p 2+4*p 3-2*p 4+p 0-2*p 1+p 2)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_3_0 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 3 0 = 4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 10 + 8*p 11 - 4*p 12 + 2*p 14 - 4*p 15 + 2*p 16 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 0-2*p 4+p 8-2*p 1+4*p 3-2*p 7+p 2-2*p 2+p 6) - -(p 8-2*p 12+p 16-2*p 7+4*p 11-2*p 15+p 6-2*p 10+p 14)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_3_1 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 3 1 = - 4*p 1 + 4*p 3 - 2*p 4 + 2*p 10 - 4*p 11 - 2*p 12 + 8*p 13 - 2*p 14 - 4*p 15 + 2*p 16 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 0-2*p 2+p 4-2*p 1+4*p 1-2*p 3+p 2-2*p 0+p 2) - -(p 12-2*p 14+p 16-2*p 11+4*p 13-2*p 15+p 10-2*p 12+p 14)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_3_2 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 3 2 = - 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 4*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 4-2*p 6+p 8-2*p 3+4*p 5-2*p 7+p 2-2*p 4+p 6) - -(p 8-2*p 10+p 12-2*p 7+4*p 9-2*p 11+p 6-2*p 8+p 10)) = _

  ring

theorem fourthLevelEvenEntry_3_3 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 3 3 = 16*p 1 - 4*p 2 + 2*p 12 - 8*p 13 + 12*p 14 - 8*p 15 + 2*p 16 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 0-2*p 1+p 2-2*p 1+4*p 0-2*p 1+p 2-2*p 1+p 0) - -(p 14-2*p 15+p 16-2*p 13+4*p 14-2*p 15+p 12-2*p 13+p 14)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_3_4 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 3 4 = 8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 10 - 8*p 11 + 12*p 12 - 8*p 13 + 2*p 14 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 2-2*p 3+p 4-2*p 1+4*p 2-2*p 3+p 0-2*p 1+p 2) - -(p 12-2*p 13+p 14-2*p 11+4*p 12-2*p 13+p 10-2*p 11+p 12)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_3_5 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 3 5 = - 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 + 2*p 8 - 8*p 9 + 12*p 10 - 8*p 11 + 2*p 12 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 4-2*p 5+p 6-2*p 3+4*p 4-2*p 5+p 2-2*p 3+p 4) - -(p 10-2*p 11+p 12-2*p 9+4*p 10-2*p 11+p 8-2*p 9+p 10)) = _

  ring

theorem fourthLevelEvenEntry_3_6 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 3 6 = - 2*p 4 + 8*p 5 - 10*p 6 + 10*p 8 - 8*p 9 + 2*p 10 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 6-2*p 7+p 8-2*p 5+4*p 6-2*p 7+p 4-2*p 5+p 6) - -(p 8-2*p 9+p 10-2*p 7+4*p 8-2*p 9+p 6-2*p 7+p 8)) = _

  ring

theorem fourthLevelEvenEntry_4_0 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 4 0 = - 8*p 1 + 2*p 2 + 4*p 3 - 2*p 4 - 4*p 8 + 8*p 9 - 4*p 10 + 2*p 12 - 4*p 13 + 2*p 14 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 2-2*p 2+p 6-2*p 3+4*p 1-2*p 5+p 4-2*p 0+p 4) - -(p 6-2*p 10+p 14-2*p 5+4*p 9-2*p 13+p 4-2*p 8+p 12)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_4_1 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 4 1 = - 4*p 1 + 4*p 3 - 2*p 4 + 2*p 8 - 4*p 9 - 2*p 10 + 8*p 11 - 2*p 12 - 4*p 13 + 2*p 14 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 2-2*p 0+p 2-2*p 3+4*p 1-2*p 1+p 4-2*p 2+p 0) - -(p 10-2*p 12+p 14-2*p 9+4*p 11-2*p 13+p 8-2*p 10+p 12)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_4_2 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 4 2 = 4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 2*p 8 - 4*p 9 + 2*p 10 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 2-2*p 4+p 6-2*p 1+4*p 3-2*p 5+p 0-2*p 2+p 4) - -(p 6-2*p 8+p 10-2*p 5+4*p 7-2*p 9+p 4-2*p 6+p 8)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_4_3 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 4 3 = 8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 10 - 8*p 11 + 12*p 12 - 8*p 13 + 2*p 14 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 2-2*p 1+p 0-2*p 3+4*p 2-2*p 1+p 4-2*p 3+p 2) - -(p 12-2*p 13+p 14-2*p 11+4*p 12-2*p 13+p 10-2*p 11+p 12)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_4_4 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 4 4 = 16*p 1 - 4*p 2 + 2*p 8 - 8*p 9 + 12*p 10 - 8*p 11 + 2*p 12 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 0-2*p 1+p 2-2*p 1+4*p 0-2*p 1+p 2-2*p 1+p 0) - -(p 10-2*p 11+p 12-2*p 9+4*p 10-2*p 11+p 8-2*p 9+p 10)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_4_5 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 4 5 = 8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 6 - 8*p 7 + 12*p 8 - 8*p 9 + 2*p 10 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 2-2*p 3+p 4-2*p 1+4*p 2-2*p 3+p 0-2*p 1+p 2) - -(p 8-2*p 9+p 10-2*p 7+4*p 8-2*p 9+p 6-2*p 7+p 8)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_4_6 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 4 6 = - 2*p 2 + 8*p 3 - 10*p 4 + 10*p 6 - 8*p 7 + 2*p 8 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 4-2*p 5+p 6-2*p 3+4*p 4-2*p 5+p 2-2*p 3+p 4) - -(p 6-2*p 7+p 8-2*p 5+4*p 6-2*p 7+p 4-2*p 5+p 6)) = _

  ring

theorem fourthLevelEvenEntry_5_0 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 5 0 = - 8*p 1 + 4*p 2 - 2*p 4 + 4*p 5 - 6*p 6 + 8*p 7 - 4*p 8 + 2*p 10 - 4*p 11 + 2*p 12 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 4-2*p 0+p 4-2*p 5+4*p 1-2*p 3+p 6-2*p 2+p 2) - -(p 4-2*p 8+p 12-2*p 3+4*p 7-2*p 11+p 2-2*p 6+p 10)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_5_1 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 5 1 = 4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 7 - 2*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 4-2*p 2+p 0-2*p 5+4*p 3-2*p 1+p 6-2*p 4+p 2) - -(p 8-2*p 10+p 12-2*p 7+4*p 9-2*p 11+p 6-2*p 8+p 10)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_5_2 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 5 2 = - 4*p 1 + 2*p 2 - 4*p 4 + 8*p 5 - 2*p 6 - 4*p 7 + 2*p 8 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 0-2*p 2+p 4-2*p 1+4*p 1-2*p 3+p 2-2*p 0+p 2) - -(p 4-2*p 6+p 8-2*p 3+4*p 5-2*p 7+p 2-2*p 4+p 6)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_5_3 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 5 3 = - 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 + 2*p 8 - 8*p 9 + 12*p 10 - 8*p 11 + 2*p 12 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 4-2*p 3+p 2-2*p 5+4*p 4-2*p 3+p 6-2*p 5+p 4) - -(p 10-2*p 11+p 12-2*p 9+4*p 10-2*p 11+p 8-2*p 9+p 10)) = _

  ring

theorem fourthLevelEvenEntry_5_4 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 5 4 = 8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 6 - 8*p 7 + 12*p 8 - 8*p 9 + 2*p 10 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 2-2*p 1+p 0-2*p 3+4*p 2-2*p 1+p 4-2*p 3+p 2) - -(p 8-2*p 9+p 10-2*p 7+4*p 8-2*p 9+p 6-2*p 7+p 8)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_5_5 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 5 5 = 16*p 1 - 4*p 2 + 2*p 4 - 8*p 5 + 12*p 6 - 8*p 7 + 2*p 8 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 0-2*p 1+p 2-2*p 1+4*p 0-2*p 1+p 2-2*p 1+p 0) - -(p 6-2*p 7+p 8-2*p 5+4*p 6-2*p 7+p 4-2*p 5+p 6)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_5_6 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 5 6 = 8*p 1 - 10*p 2 + 10*p 4 - 8*p 5 + 2*p 6 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 2-2*p 3+p 4-2*p 1+4*p 2-2*p 3+p 0-2*p 1+p 2) - -(p 4-2*p 5+p 6-2*p 3+4*p 4-2*p 5+p 2-2*p 3+p 4)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_6_0 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 6 0 = 4*p 2 - 8*p 3 + 8*p 5 - 6*p 6 + 4*p 7 - 4*p 9 + 2*p 10 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 6-2*p 2+p 2-2*p 7+4*p 3-2*p 1+p 8-2*p 4+p 0) - -(p 2-2*p 6+p 10-2*p 1+4*p 5-2*p 9+p 0-2*p 4+p 8)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_6_1 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 6 1 = - 2*p 2 + 4*p 3 + 4*p 4 - 12*p 5 + 12*p 7 - 4*p 8 - 4*p 9 + 2*p 10 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 6-2*p 4+p 2-2*p 7+4*p 5-2*p 3+p 8-2*p 6+p 4) - -(p 6-2*p 8+p 10-2*p 5+4*p 7-2*p 9+p 4-2*p 6+p 8)) = _

  ring

theorem fourthLevelEvenEntry_6_2 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 6 2 = - 8*p 1 - 2*p 2 + 12*p 3 - 4*p 4 - 4*p 5 + 2*p 6 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 2-2*p 0+p 2-2*p 3+4*p 1-2*p 1+p 4-2*p 2+p 0) - -(p 2-2*p 4+p 6-2*p 1+4*p 3-2*p 5+p 0-2*p 2+p 4)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_6_3 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 6 3 = - 2*p 4 + 8*p 5 - 10*p 6 + 10*p 8 - 8*p 9 + 2*p 10 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 6-2*p 5+p 4-2*p 7+4*p 6-2*p 5+p 8-2*p 7+p 6) - -(p 8-2*p 9+p 10-2*p 7+4*p 8-2*p 9+p 6-2*p 7+p 8)) = _

  ring

theorem fourthLevelEvenEntry_6_4 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 6 4 = - 2*p 2 + 8*p 3 - 10*p 4 + 10*p 6 - 8*p 7 + 2*p 8 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 4-2*p 3+p 2-2*p 5+4*p 4-2*p 3+p 6-2*p 5+p 4) - -(p 6-2*p 7+p 8-2*p 5+4*p 6-2*p 7+p 4-2*p 5+p 6)) = _

  ring

theorem fourthLevelEvenEntry_6_5 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 6 5 = 8*p 1 - 10*p 2 + 10*p 4 - 8*p 5 + 2*p 6 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 2-2*p 1+p 0-2*p 3+4*p 2-2*p 1+p 4-2*p 3+p 2) - -(p 4-2*p 5+p 6-2*p 3+4*p 4-2*p 5+p 2-2*p 3+p 4)) = _
  rw [hp0]
  ring

theorem fourthLevelEvenEntry_6_6 (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 6 6 = 8*p 1 + 8*p 2 - 8*p 3 + 2*p 4 := by
  simp only [fourthLevelEvenBlock, fourthLevelValueHaar_apply]
  change 2 * (-(p 0-2*p 1+p 2-2*p 1+4*p 0-2*p 1+p 2-2*p 1+p 0) - -(p 2-2*p 3+p 4-2*p 1+4*p 2-2*p 3+p 0-2*p 1+p 2)) = _
  rw [hp0]
  ring

def fourthLevelOddPolynomial (p : Fin 17 → ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  ![![8*p 8 - 2*p 16,
    - 4*p 4 + 4*p 12 - 2*p 16,
    4*p 2 + 2*p 4 - 8*p 6 + 4*p 8 - 2*p 12 + 4*p 14 - 2*p 16,
    - 8*p 2 + 2*p 4 + 4*p 6 - 4*p 8 + 4*p 10 - 2*p 12,
    4*p 1 - 2*p 2 + 4*p 6 - 8*p 7 + 4*p 8 - 2*p 14 + 4*p 15 - 2*p 16,
    - 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 2*p 12 + 4*p 13 - 2*p 14,
    4*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 2*p 6 - 2*p 10 + 4*p 11 - 2*p 12,
    - 8*p 1 + 4*p 2 - 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10],
  ![- 4*p 4 + 4*p 12 - 2*p 16,
    24*p 4 - 16*p 8 + 8*p 12 - 2*p 16,
    - 4*p 2 - 2*p 4 + 8*p 6 - 8*p 10 + 2*p 12 + 4*p 14 - 2*p 16,
    2*p 4 - 4*p 6 + 4*p 10 - 2*p 12,
    4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 4*p 8 + 4*p 10 - 8*p 11 + 4*p 12 - 2*p 14 + 4*p 15 - 2*p 16,
    - 8*p 1 + 2*p 2 + 4*p 3 - 6*p 4 + 8*p 5 - 4*p 6 + 4*p 8 - 8*p 9 + 4*p 10 - 2*p 12 + 4*p 13 - 2*p 14,
    - 8*p 1 + 8*p 3 - 6*p 4 + 4*p 5 + 2*p 6 - 8*p 7 + 4*p 8 - 2*p 10 + 4*p 11 - 2*p 12,
    8*p 1 - 8*p 3 + 8*p 4 - 8*p 5 + 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10],
  ![4*p 2 + 2*p 4 - 8*p 6 + 4*p 8 - 2*p 12 + 4*p 14 - 2*p 16,
    - 4*p 2 - 2*p 4 + 8*p 6 - 8*p 10 + 2*p 12 + 4*p 14 - 2*p 16,
    16*p 2 - 4*p 4 - 2*p 8 + 8*p 10 - 12*p 12 + 8*p 14 - 2*p 16,
    8*p 2 - 14*p 4 + 16*p 6 - 14*p 8 + 8*p 10 - 2*p 12,
    - 4*p 1 + 4*p 3 - 2*p 4 - 2*p 10 + 4*p 11 + 2*p 12 - 8*p 13 + 2*p 14 + 4*p 15 - 2*p 16,
    - 4*p 1 + 4*p 3 - 2*p 4 - 2*p 8 + 4*p 9 + 2*p 10 - 8*p 11 + 2*p 12 + 4*p 13 - 2*p 14,
    4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 6 + 4*p 7 + 2*p 8 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12,
    - 2*p 2 + 4*p 3 - 4*p 5 + 4*p 6 - 4*p 7 + 4*p 9 - 2*p 10],
  ![- 8*p 2 + 2*p 4 + 4*p 6 - 4*p 8 + 4*p 10 - 2*p 12,
    2*p 4 - 4*p 6 + 4*p 10 - 2*p 12,
    8*p 2 - 14*p 4 + 16*p 6 - 14*p 8 + 8*p 10 - 2*p 12,
    24*p 2 - 16*p 4 + 8*p 6 - 2*p 8,
    - 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 8*p 7 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12,
    4*p 1 + 2*p 2 - 8*p 3 + 8*p 5 - 8*p 7 + 2*p 8 + 4*p 9 - 2*p 10,
    - 4*p 1 - 2*p 2 + 8*p 3 - 8*p 5 + 2*p 6 + 4*p 7 - 2*p 8,
    2*p 2 - 4*p 3 + 4*p 5 - 2*p 6],
  ![4*p 1 - 2*p 2 + 4*p 6 - 8*p 7 + 4*p 8 - 2*p 14 + 4*p 15 - 2*p 16,
    4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 4*p 8 + 4*p 10 - 8*p 11 + 4*p 12 - 2*p 14 + 4*p 15 - 2*p 16,
    - 4*p 1 + 4*p 3 - 2*p 4 - 2*p 10 + 4*p 11 + 2*p 12 - 8*p 13 + 2*p 14 + 4*p 15 - 2*p 16,
    - 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 8*p 7 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12,
    16*p 1 - 4*p 2 - 2*p 12 + 8*p 13 - 12*p 14 + 8*p 15 - 2*p 16,
    8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 10 + 8*p 11 - 12*p 12 + 8*p 13 - 2*p 14,
    - 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 - 2*p 8 + 8*p 9 - 12*p 10 + 8*p 11 - 2*p 12,
    - 2*p 4 + 8*p 5 - 14*p 6 + 16*p 7 - 14*p 8 + 8*p 9 - 2*p 10],
  ![- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 2*p 12 + 4*p 13 - 2*p 14,
    - 8*p 1 + 2*p 2 + 4*p 3 - 6*p 4 + 8*p 5 - 4*p 6 + 4*p 8 - 8*p 9 + 4*p 10 - 2*p 12 + 4*p 13 - 2*p 14,
    - 4*p 1 + 4*p 3 - 2*p 4 - 2*p 8 + 4*p 9 + 2*p 10 - 8*p 11 + 2*p 12 + 4*p 13 - 2*p 14,
    4*p 1 + 2*p 2 - 8*p 3 + 8*p 5 - 8*p 7 + 2*p 8 + 4*p 9 - 2*p 10,
    8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 10 + 8*p 11 - 12*p 12 + 8*p 13 - 2*p 14,
    16*p 1 - 4*p 2 - 2*p 8 + 8*p 9 - 12*p 10 + 8*p 11 - 2*p 12,
    8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 6 + 8*p 7 - 12*p 8 + 8*p 9 - 2*p 10,
    - 2*p 2 + 8*p 3 - 14*p 4 + 16*p 5 - 14*p 6 + 8*p 7 - 2*p 8],
  ![4*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 2*p 6 - 2*p 10 + 4*p 11 - 2*p 12,
    - 8*p 1 + 8*p 3 - 6*p 4 + 4*p 5 + 2*p 6 - 8*p 7 + 4*p 8 - 2*p 10 + 4*p 11 - 2*p 12,
    4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 6 + 4*p 7 + 2*p 8 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12,
    - 4*p 1 - 2*p 2 + 8*p 3 - 8*p 5 + 2*p 6 + 4*p 7 - 2*p 8,
    - 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 - 2*p 8 + 8*p 9 - 12*p 10 + 8*p 11 - 2*p 12,
    8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 6 + 8*p 7 - 12*p 8 + 8*p 9 - 2*p 10,
    16*p 1 - 4*p 2 - 2*p 4 + 8*p 5 - 12*p 6 + 8*p 7 - 2*p 8,
    8*p 1 - 14*p 2 + 16*p 3 - 14*p 4 + 8*p 5 - 2*p 6],
  ![- 8*p 1 + 4*p 2 - 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10,
    8*p 1 - 8*p 3 + 8*p 4 - 8*p 5 + 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10,
    - 2*p 2 + 4*p 3 - 4*p 5 + 4*p 6 - 4*p 7 + 4*p 9 - 2*p 10,
    2*p 2 - 4*p 3 + 4*p 5 - 2*p 6,
    - 2*p 4 + 8*p 5 - 14*p 6 + 16*p 7 - 14*p 8 + 8*p 9 - 2*p 10,
    - 2*p 2 + 8*p 3 - 14*p 4 + 16*p 5 - 14*p 6 + 8*p 7 - 2*p 8,
    8*p 1 - 14*p 2 + 16*p 3 - 14*p 4 + 8*p 5 - 2*p 6,
    24*p 1 - 16*p 2 + 8*p 3 - 2*p 4]]

theorem fourthLevelOddBlock_row0_eq_polynomial (p : Fin 17 → ℝ)
    (hp0 : p 0 = 0) (j : Fin 8) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 0 j = fourthLevelOddPolynomial p 0 j := by
  fin_cases j
  · exact fourthLevelOddEntry_0_0 p hp0
  · exact fourthLevelOddEntry_0_1 p hp0
  · exact fourthLevelOddEntry_0_2 p hp0
  · exact fourthLevelOddEntry_0_3 p hp0
  · exact fourthLevelOddEntry_0_4 p hp0
  · exact fourthLevelOddEntry_0_5 p hp0
  · exact fourthLevelOddEntry_0_6 p hp0
  · exact fourthLevelOddEntry_0_7 p hp0

theorem fourthLevelOddBlock_row1_eq_polynomial (p : Fin 17 → ℝ)
    (hp0 : p 0 = 0) (j : Fin 8) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 1 j = fourthLevelOddPolynomial p 1 j := by
  fin_cases j
  · exact fourthLevelOddEntry_1_0 p hp0
  · exact fourthLevelOddEntry_1_1 p hp0
  · exact fourthLevelOddEntry_1_2 p hp0
  · exact fourthLevelOddEntry_1_3 p hp0
  · exact fourthLevelOddEntry_1_4 p hp0
  · exact fourthLevelOddEntry_1_5 p hp0
  · exact fourthLevelOddEntry_1_6 p hp0
  · exact fourthLevelOddEntry_1_7 p hp0

theorem fourthLevelOddBlock_row2_eq_polynomial (p : Fin 17 → ℝ)
    (hp0 : p 0 = 0) (j : Fin 8) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 2 j = fourthLevelOddPolynomial p 2 j := by
  fin_cases j
  · exact fourthLevelOddEntry_2_0 p hp0
  · exact fourthLevelOddEntry_2_1 p hp0
  · exact fourthLevelOddEntry_2_2 p hp0
  · exact fourthLevelOddEntry_2_3 p hp0
  · exact fourthLevelOddEntry_2_4 p hp0
  · exact fourthLevelOddEntry_2_5 p hp0
  · exact fourthLevelOddEntry_2_6 p hp0
  · exact fourthLevelOddEntry_2_7 p hp0

theorem fourthLevelOddBlock_row3_eq_polynomial (p : Fin 17 → ℝ)
    (hp0 : p 0 = 0) (j : Fin 8) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 3 j = fourthLevelOddPolynomial p 3 j := by
  fin_cases j
  · exact fourthLevelOddEntry_3_0 p hp0
  · exact fourthLevelOddEntry_3_1 p hp0
  · exact fourthLevelOddEntry_3_2 p hp0
  · exact fourthLevelOddEntry_3_3 p hp0
  · exact fourthLevelOddEntry_3_4 p hp0
  · exact fourthLevelOddEntry_3_5 p hp0
  · exact fourthLevelOddEntry_3_6 p hp0
  · exact fourthLevelOddEntry_3_7 p hp0

theorem fourthLevelOddBlock_row4_eq_polynomial (p : Fin 17 → ℝ)
    (hp0 : p 0 = 0) (j : Fin 8) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 4 j = fourthLevelOddPolynomial p 4 j := by
  fin_cases j
  · exact fourthLevelOddEntry_4_0 p hp0
  · exact fourthLevelOddEntry_4_1 p hp0
  · exact fourthLevelOddEntry_4_2 p hp0
  · exact fourthLevelOddEntry_4_3 p hp0
  · exact fourthLevelOddEntry_4_4 p hp0
  · exact fourthLevelOddEntry_4_5 p hp0
  · exact fourthLevelOddEntry_4_6 p hp0
  · exact fourthLevelOddEntry_4_7 p hp0

theorem fourthLevelOddBlock_row5_eq_polynomial (p : Fin 17 → ℝ)
    (hp0 : p 0 = 0) (j : Fin 8) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 5 j = fourthLevelOddPolynomial p 5 j := by
  fin_cases j
  · exact fourthLevelOddEntry_5_0 p hp0
  · exact fourthLevelOddEntry_5_1 p hp0
  · exact fourthLevelOddEntry_5_2 p hp0
  · exact fourthLevelOddEntry_5_3 p hp0
  · exact fourthLevelOddEntry_5_4 p hp0
  · exact fourthLevelOddEntry_5_5 p hp0
  · exact fourthLevelOddEntry_5_6 p hp0
  · exact fourthLevelOddEntry_5_7 p hp0

theorem fourthLevelOddBlock_row6_eq_polynomial (p : Fin 17 → ℝ)
    (hp0 : p 0 = 0) (j : Fin 8) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 6 j = fourthLevelOddPolynomial p 6 j := by
  fin_cases j
  · exact fourthLevelOddEntry_6_0 p hp0
  · exact fourthLevelOddEntry_6_1 p hp0
  · exact fourthLevelOddEntry_6_2 p hp0
  · exact fourthLevelOddEntry_6_3 p hp0
  · exact fourthLevelOddEntry_6_4 p hp0
  · exact fourthLevelOddEntry_6_5 p hp0
  · exact fourthLevelOddEntry_6_6 p hp0
  · exact fourthLevelOddEntry_6_7 p hp0

theorem fourthLevelOddBlock_row7_eq_polynomial (p : Fin 17 → ℝ)
    (hp0 : p 0 = 0) (j : Fin 8) :
    fourthLevelOddBlock (fourthLevelValueHaar p) 7 j = fourthLevelOddPolynomial p 7 j := by
  fin_cases j
  · exact fourthLevelOddEntry_7_0 p hp0
  · exact fourthLevelOddEntry_7_1 p hp0
  · exact fourthLevelOddEntry_7_2 p hp0
  · exact fourthLevelOddEntry_7_3 p hp0
  · exact fourthLevelOddEntry_7_4 p hp0
  · exact fourthLevelOddEntry_7_5 p hp0
  · exact fourthLevelOddEntry_7_6 p hp0
  · exact fourthLevelOddEntry_7_7 p hp0

theorem fourthLevelOddBlock_eq_polynomial (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelOddBlock (fourthLevelValueHaar p) = fourthLevelOddPolynomial p := by
  ext i j
  fin_cases i
  · exact fourthLevelOddBlock_row0_eq_polynomial p hp0 j
  · exact fourthLevelOddBlock_row1_eq_polynomial p hp0 j
  · exact fourthLevelOddBlock_row2_eq_polynomial p hp0 j
  · exact fourthLevelOddBlock_row3_eq_polynomial p hp0 j
  · exact fourthLevelOddBlock_row4_eq_polynomial p hp0 j
  · exact fourthLevelOddBlock_row5_eq_polynomial p hp0 j
  · exact fourthLevelOddBlock_row6_eq_polynomial p hp0 j
  · exact fourthLevelOddBlock_row7_eq_polynomial p hp0 j

def fourthLevelEvenPolynomial (p : Fin 17 → ℝ) : Matrix (Fin 7) (Fin 7) ℝ :=
  ![![8*p 4 + 8*p 8 - 8*p 12 + 2*p 16,
    - 4*p 2 + 2*p 4 - 4*p 8 + 8*p 10 - 2*p 12 - 4*p 14 + 2*p 16,
    - 8*p 2 - 2*p 4 + 12*p 6 - 4*p 8 - 4*p 10 + 2*p 12,
    4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 10 + 8*p 11 - 4*p 12 + 2*p 14 - 4*p 15 + 2*p 16,
    - 8*p 1 + 2*p 2 + 4*p 3 - 2*p 4 - 4*p 8 + 8*p 9 - 4*p 10 + 2*p 12 - 4*p 13 + 2*p 14,
    - 8*p 1 + 4*p 2 - 2*p 4 + 4*p 5 - 6*p 6 + 8*p 7 - 4*p 8 + 2*p 10 - 4*p 11 + 2*p 12,
    4*p 2 - 8*p 3 + 8*p 5 - 6*p 6 + 4*p 7 - 4*p 9 + 2*p 10],
  ![- 4*p 2 + 2*p 4 - 4*p 8 + 8*p 10 - 2*p 12 - 4*p 14 + 2*p 16,
    16*p 2 - 4*p 4 + 2*p 8 - 8*p 10 + 12*p 12 - 8*p 14 + 2*p 16,
    8*p 2 - 10*p 4 + 10*p 8 - 8*p 10 + 2*p 12,
    - 4*p 1 + 4*p 3 - 2*p 4 + 2*p 10 - 4*p 11 - 2*p 12 + 8*p 13 - 2*p 14 - 4*p 15 + 2*p 16,
    - 4*p 1 + 4*p 3 - 2*p 4 + 2*p 8 - 4*p 9 - 2*p 10 + 8*p 11 - 2*p 12 - 4*p 13 + 2*p 14,
    4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 7 - 2*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12,
    - 2*p 2 + 4*p 3 + 4*p 4 - 12*p 5 + 12*p 7 - 4*p 8 - 4*p 9 + 2*p 10],
  ![- 8*p 2 - 2*p 4 + 12*p 6 - 4*p 8 - 4*p 10 + 2*p 12,
    8*p 2 - 10*p 4 + 10*p 8 - 8*p 10 + 2*p 12,
    8*p 2 + 8*p 4 - 8*p 6 + 2*p 8,
    - 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 4*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12,
    4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 2*p 8 - 4*p 9 + 2*p 10,
    - 4*p 1 + 2*p 2 - 4*p 4 + 8*p 5 - 2*p 6 - 4*p 7 + 2*p 8,
    - 8*p 1 - 2*p 2 + 12*p 3 - 4*p 4 - 4*p 5 + 2*p 6],
  ![4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 10 + 8*p 11 - 4*p 12 + 2*p 14 - 4*p 15 + 2*p 16,
    - 4*p 1 + 4*p 3 - 2*p 4 + 2*p 10 - 4*p 11 - 2*p 12 + 8*p 13 - 2*p 14 - 4*p 15 + 2*p 16,
    - 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 4*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12,
    16*p 1 - 4*p 2 + 2*p 12 - 8*p 13 + 12*p 14 - 8*p 15 + 2*p 16,
    8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 10 - 8*p 11 + 12*p 12 - 8*p 13 + 2*p 14,
    - 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 + 2*p 8 - 8*p 9 + 12*p 10 - 8*p 11 + 2*p 12,
    - 2*p 4 + 8*p 5 - 10*p 6 + 10*p 8 - 8*p 9 + 2*p 10],
  ![- 8*p 1 + 2*p 2 + 4*p 3 - 2*p 4 - 4*p 8 + 8*p 9 - 4*p 10 + 2*p 12 - 4*p 13 + 2*p 14,
    - 4*p 1 + 4*p 3 - 2*p 4 + 2*p 8 - 4*p 9 - 2*p 10 + 8*p 11 - 2*p 12 - 4*p 13 + 2*p 14,
    4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 2*p 8 - 4*p 9 + 2*p 10,
    8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 10 - 8*p 11 + 12*p 12 - 8*p 13 + 2*p 14,
    16*p 1 - 4*p 2 + 2*p 8 - 8*p 9 + 12*p 10 - 8*p 11 + 2*p 12,
    8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 6 - 8*p 7 + 12*p 8 - 8*p 9 + 2*p 10,
    - 2*p 2 + 8*p 3 - 10*p 4 + 10*p 6 - 8*p 7 + 2*p 8],
  ![- 8*p 1 + 4*p 2 - 2*p 4 + 4*p 5 - 6*p 6 + 8*p 7 - 4*p 8 + 2*p 10 - 4*p 11 + 2*p 12,
    4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 7 - 2*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12,
    - 4*p 1 + 2*p 2 - 4*p 4 + 8*p 5 - 2*p 6 - 4*p 7 + 2*p 8,
    - 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 + 2*p 8 - 8*p 9 + 12*p 10 - 8*p 11 + 2*p 12,
    8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 6 - 8*p 7 + 12*p 8 - 8*p 9 + 2*p 10,
    16*p 1 - 4*p 2 + 2*p 4 - 8*p 5 + 12*p 6 - 8*p 7 + 2*p 8,
    8*p 1 - 10*p 2 + 10*p 4 - 8*p 5 + 2*p 6],
  ![4*p 2 - 8*p 3 + 8*p 5 - 6*p 6 + 4*p 7 - 4*p 9 + 2*p 10,
    - 2*p 2 + 4*p 3 + 4*p 4 - 12*p 5 + 12*p 7 - 4*p 8 - 4*p 9 + 2*p 10,
    - 8*p 1 - 2*p 2 + 12*p 3 - 4*p 4 - 4*p 5 + 2*p 6,
    - 2*p 4 + 8*p 5 - 10*p 6 + 10*p 8 - 8*p 9 + 2*p 10,
    - 2*p 2 + 8*p 3 - 10*p 4 + 10*p 6 - 8*p 7 + 2*p 8,
    8*p 1 - 10*p 2 + 10*p 4 - 8*p 5 + 2*p 6,
    8*p 1 + 8*p 2 - 8*p 3 + 2*p 4]]

theorem fourthLevelEvenBlock_row0_eq_polynomial (p : Fin 17 → ℝ)
    (hp0 : p 0 = 0) (j : Fin 7) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 0 j = fourthLevelEvenPolynomial p 0 j := by
  fin_cases j
  · exact fourthLevelEvenEntry_0_0 p hp0
  · exact fourthLevelEvenEntry_0_1 p hp0
  · exact fourthLevelEvenEntry_0_2 p hp0
  · exact fourthLevelEvenEntry_0_3 p hp0
  · exact fourthLevelEvenEntry_0_4 p hp0
  · exact fourthLevelEvenEntry_0_5 p hp0
  · exact fourthLevelEvenEntry_0_6 p hp0

theorem fourthLevelEvenBlock_row1_eq_polynomial (p : Fin 17 → ℝ)
    (hp0 : p 0 = 0) (j : Fin 7) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 1 j = fourthLevelEvenPolynomial p 1 j := by
  fin_cases j
  · exact fourthLevelEvenEntry_1_0 p hp0
  · exact fourthLevelEvenEntry_1_1 p hp0
  · exact fourthLevelEvenEntry_1_2 p hp0
  · exact fourthLevelEvenEntry_1_3 p hp0
  · exact fourthLevelEvenEntry_1_4 p hp0
  · exact fourthLevelEvenEntry_1_5 p hp0
  · exact fourthLevelEvenEntry_1_6 p hp0

theorem fourthLevelEvenBlock_row2_eq_polynomial (p : Fin 17 → ℝ)
    (hp0 : p 0 = 0) (j : Fin 7) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 2 j = fourthLevelEvenPolynomial p 2 j := by
  fin_cases j
  · exact fourthLevelEvenEntry_2_0 p hp0
  · exact fourthLevelEvenEntry_2_1 p hp0
  · exact fourthLevelEvenEntry_2_2 p hp0
  · exact fourthLevelEvenEntry_2_3 p hp0
  · exact fourthLevelEvenEntry_2_4 p hp0
  · exact fourthLevelEvenEntry_2_5 p hp0
  · exact fourthLevelEvenEntry_2_6 p hp0

theorem fourthLevelEvenBlock_row3_eq_polynomial (p : Fin 17 → ℝ)
    (hp0 : p 0 = 0) (j : Fin 7) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 3 j = fourthLevelEvenPolynomial p 3 j := by
  fin_cases j
  · exact fourthLevelEvenEntry_3_0 p hp0
  · exact fourthLevelEvenEntry_3_1 p hp0
  · exact fourthLevelEvenEntry_3_2 p hp0
  · exact fourthLevelEvenEntry_3_3 p hp0
  · exact fourthLevelEvenEntry_3_4 p hp0
  · exact fourthLevelEvenEntry_3_5 p hp0
  · exact fourthLevelEvenEntry_3_6 p hp0

theorem fourthLevelEvenBlock_row4_eq_polynomial (p : Fin 17 → ℝ)
    (hp0 : p 0 = 0) (j : Fin 7) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 4 j = fourthLevelEvenPolynomial p 4 j := by
  fin_cases j
  · exact fourthLevelEvenEntry_4_0 p hp0
  · exact fourthLevelEvenEntry_4_1 p hp0
  · exact fourthLevelEvenEntry_4_2 p hp0
  · exact fourthLevelEvenEntry_4_3 p hp0
  · exact fourthLevelEvenEntry_4_4 p hp0
  · exact fourthLevelEvenEntry_4_5 p hp0
  · exact fourthLevelEvenEntry_4_6 p hp0

theorem fourthLevelEvenBlock_row5_eq_polynomial (p : Fin 17 → ℝ)
    (hp0 : p 0 = 0) (j : Fin 7) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 5 j = fourthLevelEvenPolynomial p 5 j := by
  fin_cases j
  · exact fourthLevelEvenEntry_5_0 p hp0
  · exact fourthLevelEvenEntry_5_1 p hp0
  · exact fourthLevelEvenEntry_5_2 p hp0
  · exact fourthLevelEvenEntry_5_3 p hp0
  · exact fourthLevelEvenEntry_5_4 p hp0
  · exact fourthLevelEvenEntry_5_5 p hp0
  · exact fourthLevelEvenEntry_5_6 p hp0

theorem fourthLevelEvenBlock_row6_eq_polynomial (p : Fin 17 → ℝ)
    (hp0 : p 0 = 0) (j : Fin 7) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) 6 j = fourthLevelEvenPolynomial p 6 j := by
  fin_cases j
  · exact fourthLevelEvenEntry_6_0 p hp0
  · exact fourthLevelEvenEntry_6_1 p hp0
  · exact fourthLevelEvenEntry_6_2 p hp0
  · exact fourthLevelEvenEntry_6_3 p hp0
  · exact fourthLevelEvenEntry_6_4 p hp0
  · exact fourthLevelEvenEntry_6_5 p hp0
  · exact fourthLevelEvenEntry_6_6 p hp0

theorem fourthLevelEvenBlock_eq_polynomial (p : Fin 17 → ℝ) (hp0 : p 0 = 0) :
    fourthLevelEvenBlock (fourthLevelValueHaar p) = fourthLevelEvenPolynomial p := by
  ext i j
  fin_cases i
  · exact fourthLevelEvenBlock_row0_eq_polynomial p hp0 j
  · exact fourthLevelEvenBlock_row1_eq_polynomial p hp0 j
  · exact fourthLevelEvenBlock_row2_eq_polynomial p hp0 j
  · exact fourthLevelEvenBlock_row3_eq_polynomial p hp0 j
  · exact fourthLevelEvenBlock_row4_eq_polynomial p hp0 j
  · exact fourthLevelEvenBlock_row5_eq_polynomial p hp0 j
  · exact fourthLevelEvenBlock_row6_eq_polynomial p hp0 j

def fourthLevelOddShearNumerator : Matrix (Fin 8) (Fin 8) ℝ :=
  ![![1000,-250,82,-146,11,-5,19,-74],
  ![0,1000,-215,-9,33,-67,-123,68],
  ![0,0,1000,241,-202,-138,88,5],
  ![0,0,0,1000,-44,124,-89,-5],
  ![0,0,0,0,1000,322,24,1],
  ![0,0,0,0,0,1000,339,20],
  ![0,0,0,0,0,0,1000,259],
  ![0,0,0,0,0,0,0,1000]]

def fourthLevelEvenShearNumerator : Matrix (Fin 7) (Fin 7) ℝ :=
  ![![1000,-175,-259,28,-72,-108,-10],
  ![0,1000,391,-222,-140,91,9],
  ![0,0,1000,-40,108,-26,-253],
  ![0,0,0,1000,320,25,2],
  ![0,0,0,0,1000,351,33],
  ![0,0,0,0,0,1000,427],
  ![0,0,0,0,0,0,1000]]

theorem fourthLevelOddRightEntry_0_0 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 0 0 =
      8000*p 8 - 2000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (8*p 8 - 2*p 16) * (1000) + ((- 4*p 4 + 4*p 12 - 2*p 16) * (0) + ((4*p 2 + 2*p 4 - 8*p 6 + 4*p 8 - 2*p 12 + 4*p 14 - 2*p 16) * (0) + ((- 8*p 2 + 2*p 4 + 4*p 6 - 4*p 8 + 4*p 10 - 2*p 12) * (0) + ((4*p 1 - 2*p 2 + 4*p 6 - 8*p 7 + 4*p 8 - 2*p 14 + 4*p 15 - 2*p 16) * (0) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 2*p 12 + 4*p 13 - 2*p 14) * (0) + ((4*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 2*p 6 - 2*p 10 + 4*p 11 - 2*p 12) * (0) + ((- 8*p 1 + 4*p 2 - 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_0_1 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 0 1 =
      - 4000*p 4 - 2000*p 8 + 4000*p 12 - 1500*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (8*p 8 - 2*p 16) * (-250) + ((- 4*p 4 + 4*p 12 - 2*p 16) * (1000) + ((4*p 2 + 2*p 4 - 8*p 6 + 4*p 8 - 2*p 12 + 4*p 14 - 2*p 16) * (0) + ((- 8*p 2 + 2*p 4 + 4*p 6 - 4*p 8 + 4*p 10 - 2*p 12) * (0) + ((4*p 1 - 2*p 2 + 4*p 6 - 8*p 7 + 4*p 8 - 2*p 14 + 4*p 15 - 2*p 16) * (0) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 2*p 12 + 4*p 13 - 2*p 14) * (0) + ((4*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 2*p 6 - 2*p 10 + 4*p 11 - 2*p 12) * (0) + ((- 8*p 1 + 4*p 2 - 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_0_2 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 0 2 =
      4000*p 2 + 2860*p 4 - 8000*p 6 + 4656*p 8 - 2860*p 12 + 4000*p 14 - 1734*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (8*p 8 - 2*p 16) * (82) + ((- 4*p 4 + 4*p 12 - 2*p 16) * (-215) + ((4*p 2 + 2*p 4 - 8*p 6 + 4*p 8 - 2*p 12 + 4*p 14 - 2*p 16) * (1000) + ((- 8*p 2 + 2*p 4 + 4*p 6 - 4*p 8 + 4*p 10 - 2*p 12) * (0) + ((4*p 1 - 2*p 2 + 4*p 6 - 8*p 7 + 4*p 8 - 2*p 14 + 4*p 15 - 2*p 16) * (0) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 2*p 12 + 4*p 13 - 2*p 14) * (0) + ((4*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 2*p 6 - 2*p 10 + 4*p 11 - 2*p 12) * (0) + ((- 8*p 1 + 4*p 2 - 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_0_3 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 0 3 =
      - 7036*p 2 + 2518*p 4 + 2072*p 6 - 4204*p 8 + 4000*p 10 - 2518*p 12 + 964*p 14 - 172*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (8*p 8 - 2*p 16) * (-146) + ((- 4*p 4 + 4*p 12 - 2*p 16) * (-9) + ((4*p 2 + 2*p 4 - 8*p 6 + 4*p 8 - 2*p 12 + 4*p 14 - 2*p 16) * (241) + ((- 8*p 2 + 2*p 4 + 4*p 6 - 4*p 8 + 4*p 10 - 2*p 12) * (1000) + ((4*p 1 - 2*p 2 + 4*p 6 - 8*p 7 + 4*p 8 - 2*p 14 + 4*p 15 - 2*p 16) * (0) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 2*p 12 + 4*p 13 - 2*p 14) * (0) + ((4*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 2*p 6 - 2*p 10 + 4*p 11 - 2*p 12) * (0) + ((- 8*p 1 + 4*p 2 - 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_0_4 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 0 4 =
      4000*p 1 - 2456*p 2 - 624*p 4 + 5440*p 6 - 8000*p 7 + 3456*p 8 - 176*p 10 + 624*p 12 - 2808*p 14 + 4000*p 15 - 1684*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (8*p 8 - 2*p 16) * (11) + ((- 4*p 4 + 4*p 12 - 2*p 16) * (33) + ((4*p 2 + 2*p 4 - 8*p 6 + 4*p 8 - 2*p 12 + 4*p 14 - 2*p 16) * (-202) + ((- 8*p 2 + 2*p 4 + 4*p 6 - 4*p 8 + 4*p 10 - 2*p 12) * (-44) + ((4*p 1 - 2*p 2 + 4*p 6 - 8*p 7 + 4*p 8 - 2*p 14 + 4*p 15 - 2*p 16) * (1000) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 2*p 12 + 4*p 13 - 2*p 14) * (0) + ((4*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 2*p 6 - 2*p 10 + 4*p 11 - 2*p 12) * (0) + ((- 8*p 1 + 4*p 2 - 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_0_5 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 0 5 =
      1288*p 1 - 4188*p 2 + 4000*p 3 + 2240*p 4 - 8000*p 5 + 6888*p 6 - 2576*p 7 + 200*p 8 + 496*p 10 - 2240*p 12 + 4000*p 13 - 3196*p 14 + 1288*p 15 - 224*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (8*p 8 - 2*p 16) * (-5) + ((- 4*p 4 + 4*p 12 - 2*p 16) * (-67) + ((4*p 2 + 2*p 4 - 8*p 6 + 4*p 8 - 2*p 12 + 4*p 14 - 2*p 16) * (-138) + ((- 8*p 2 + 2*p 4 + 4*p 6 - 4*p 8 + 4*p 10 - 2*p 12) * (124) + ((4*p 1 - 2*p 2 + 4*p 6 - 8*p 7 + 4*p 8 - 2*p 14 + 4*p 15 - 2*p 16) * (322) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 2*p 12 + 4*p 13 - 2*p 14) * (1000) + ((4*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 2*p 6 - 2*p 10 + 4*p 11 - 2*p 12) * (0) + ((- 8*p 1 + 4*p 2 - 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_0_6 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 0 6 =
      96*p 1 + 4338*p 2 - 6644*p 3 + 3168*p 4 + 1288*p 5 - 1608*p 6 - 192*p 7 + 956*p 8 - 2356*p 10 + 4000*p 11 - 3168*p 12 + 1356*p 13 - 374*p 14 + 96*p 15 - 16*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (8*p 8 - 2*p 16) * (19) + ((- 4*p 4 + 4*p 12 - 2*p 16) * (-123) + ((4*p 2 + 2*p 4 - 8*p 6 + 4*p 8 - 2*p 12 + 4*p 14 - 2*p 16) * (88) + ((- 8*p 2 + 2*p 4 + 4*p 6 - 4*p 8 + 4*p 10 - 2*p 12) * (-89) + ((4*p 1 - 2*p 2 + 4*p 6 - 8*p 7 + 4*p 8 - 2*p 14 + 4*p 15 - 2*p 16) * (24) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 2*p 12 + 4*p 13 - 2*p 14) * (339) + ((4*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 2*p 6 - 2*p 10 + 4*p 11 - 2*p 12) * (1000) + ((- 8*p 1 + 4*p 2 - 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_0_7 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 0 7 =
      - 7996*p 1 + 5054*p 2 - 1992*p 3 + 286*p 4 + 876*p 5 - 2494*p 6 + 3992*p 7 - 4548*p 8 + 4000*p 9 - 2538*p 10 + 1036*p 11 - 286*p 12 + 80*p 13 - 22*p 14 + 4*p 15 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (8*p 8 - 2*p 16) * (-74) + ((- 4*p 4 + 4*p 12 - 2*p 16) * (68) + ((4*p 2 + 2*p 4 - 8*p 6 + 4*p 8 - 2*p 12 + 4*p 14 - 2*p 16) * (5) + ((- 8*p 2 + 2*p 4 + 4*p 6 - 4*p 8 + 4*p 10 - 2*p 12) * (-5) + ((4*p 1 - 2*p 2 + 4*p 6 - 8*p 7 + 4*p 8 - 2*p 14 + 4*p 15 - 2*p 16) * (1) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 2*p 12 + 4*p 13 - 2*p 14) * (20) + ((4*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 2*p 6 - 2*p 10 + 4*p 11 - 2*p 12) * (259) + ((- 8*p 1 + 4*p 2 - 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (1000) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_1_0 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 1 0 =
      - 4000*p 4 + 4000*p 12 - 2000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 4*p 4 + 4*p 12 - 2*p 16) * (1000) + ((24*p 4 - 16*p 8 + 8*p 12 - 2*p 16) * (0) + ((- 4*p 2 - 2*p 4 + 8*p 6 - 8*p 10 + 2*p 12 + 4*p 14 - 2*p 16) * (0) + ((2*p 4 - 4*p 6 + 4*p 10 - 2*p 12) * (0) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 4*p 8 + 4*p 10 - 8*p 11 + 4*p 12 - 2*p 14 + 4*p 15 - 2*p 16) * (0) + ((- 8*p 1 + 2*p 2 + 4*p 3 - 6*p 4 + 8*p 5 - 4*p 6 + 4*p 8 - 8*p 9 + 4*p 10 - 2*p 12 + 4*p 13 - 2*p 14) * (0) + ((- 8*p 1 + 8*p 3 - 6*p 4 + 4*p 5 + 2*p 6 - 8*p 7 + 4*p 8 - 2*p 10 + 4*p 11 - 2*p 12) * (0) + ((8*p 1 - 8*p 3 + 8*p 4 - 8*p 5 + 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_1_1 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 1 1 =
      25000*p 4 - 16000*p 8 + 7000*p 12 - 1500*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 4*p 4 + 4*p 12 - 2*p 16) * (-250) + ((24*p 4 - 16*p 8 + 8*p 12 - 2*p 16) * (1000) + ((- 4*p 2 - 2*p 4 + 8*p 6 - 8*p 10 + 2*p 12 + 4*p 14 - 2*p 16) * (0) + ((2*p 4 - 4*p 6 + 4*p 10 - 2*p 12) * (0) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 4*p 8 + 4*p 10 - 8*p 11 + 4*p 12 - 2*p 14 + 4*p 15 - 2*p 16) * (0) + ((- 8*p 1 + 2*p 2 + 4*p 3 - 6*p 4 + 8*p 5 - 4*p 6 + 4*p 8 - 8*p 9 + 4*p 10 - 2*p 12 + 4*p 13 - 2*p 14) * (0) + ((- 8*p 1 + 8*p 3 - 6*p 4 + 4*p 5 + 2*p 6 - 8*p 7 + 4*p 8 - 2*p 10 + 4*p 11 - 2*p 12) * (0) + ((8*p 1 - 8*p 3 + 8*p 4 - 8*p 5 + 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_1_2 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 1 2 =
      - 4000*p 2 - 7488*p 4 + 8000*p 6 + 3440*p 8 - 8000*p 10 + 608*p 12 + 4000*p 14 - 1734*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 4*p 4 + 4*p 12 - 2*p 16) * (82) + ((24*p 4 - 16*p 8 + 8*p 12 - 2*p 16) * (-215) + ((- 4*p 2 - 2*p 4 + 8*p 6 - 8*p 10 + 2*p 12 + 4*p 14 - 2*p 16) * (1000) + ((2*p 4 - 4*p 6 + 4*p 10 - 2*p 12) * (0) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 4*p 8 + 4*p 10 - 8*p 11 + 4*p 12 - 2*p 14 + 4*p 15 - 2*p 16) * (0) + ((- 8*p 1 + 2*p 2 + 4*p 3 - 6*p 4 + 8*p 5 - 4*p 6 + 4*p 8 - 8*p 9 + 4*p 10 - 2*p 12 + 4*p 13 - 2*p 14) * (0) + ((- 8*p 1 + 8*p 3 - 6*p 4 + 4*p 5 + 2*p 6 - 8*p 7 + 4*p 8 - 2*p 10 + 4*p 11 - 2*p 12) * (0) + ((8*p 1 - 8*p 3 + 8*p 4 - 8*p 5 + 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_1_3 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 1 3 =
      - 964*p 2 + 1886*p 4 - 2072*p 6 + 144*p 8 + 2072*p 10 - 2174*p 12 + 964*p 14 - 172*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 4*p 4 + 4*p 12 - 2*p 16) * (-146) + ((24*p 4 - 16*p 8 + 8*p 12 - 2*p 16) * (-9) + ((- 4*p 2 - 2*p 4 + 8*p 6 - 8*p 10 + 2*p 12 + 4*p 14 - 2*p 16) * (241) + ((2*p 4 - 4*p 6 + 4*p 10 - 2*p 12) * (1000) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 4*p 8 + 4*p 10 - 8*p 11 + 4*p 12 - 2*p 14 + 4*p 15 - 2*p 16) * (0) + ((- 8*p 1 + 2*p 2 + 4*p 3 - 6*p 4 + 8*p 5 - 4*p 6 + 4*p 8 - 8*p 9 + 4*p 10 - 2*p 12 + 4*p 13 - 2*p 14) * (0) + ((- 8*p 1 + 8*p 3 - 6*p 4 + 4*p 5 + 2*p 6 - 8*p 7 + 4*p 8 - 2*p 10 + 4*p 11 - 2*p 12) * (0) + ((8*p 1 - 8*p 3 + 8*p 4 - 8*p 5 + 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_1_4 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 1 4 =
      4000*p 1 + 2808*p 2 - 8000*p 3 + 5064*p 4 - 5440*p 6 + 8000*p 7 - 4528*p 8 + 5440*p 10 - 8000*p 11 + 3992*p 12 - 2808*p 14 + 4000*p 15 - 1684*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 4*p 4 + 4*p 12 - 2*p 16) * (11) + ((24*p 4 - 16*p 8 + 8*p 12 - 2*p 16) * (33) + ((- 4*p 2 - 2*p 4 + 8*p 6 - 8*p 10 + 2*p 12 + 4*p 14 - 2*p 16) * (-202) + ((2*p 4 - 4*p 6 + 4*p 10 - 2*p 12) * (-44) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 4*p 8 + 4*p 10 - 8*p 11 + 4*p 12 - 2*p 14 + 4*p 15 - 2*p 16) * (1000) + ((- 8*p 1 + 2*p 2 + 4*p 3 - 6*p 4 + 8*p 5 - 4*p 6 + 4*p 8 - 8*p 9 + 4*p 10 - 2*p 12 + 4*p 13 - 2*p 14) * (0) + ((- 8*p 1 + 8*p 3 - 6*p 4 + 4*p 5 + 2*p 6 - 8*p 7 + 4*p 8 - 2*p 10 + 4*p 11 - 2*p 12) * (0) + ((8*p 1 - 8*p 3 + 8*p 4 - 8*p 5 + 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_1_5 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 1 5 =
      - 6712*p 1 + 3196*p 2 + 1424*p 3 - 5776*p 4 + 8000*p 5 - 6888*p 6 + 2576*p 7 + 3784*p 8 - 8000*p 9 + 6888*p 10 - 2576*p 11 - 1792*p 12 + 4000*p 13 - 3196*p 14 + 1288*p 15 - 224*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 4*p 4 + 4*p 12 - 2*p 16) * (-5) + ((24*p 4 - 16*p 8 + 8*p 12 - 2*p 16) * (-67) + ((- 4*p 2 - 2*p 4 + 8*p 6 - 8*p 10 + 2*p 12 + 4*p 14 - 2*p 16) * (-138) + ((2*p 4 - 4*p 6 + 4*p 10 - 2*p 12) * (124) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 4*p 8 + 4*p 10 - 8*p 11 + 4*p 12 - 2*p 14 + 4*p 15 - 2*p 16) * (322) + ((- 8*p 1 + 2*p 2 + 4*p 3 - 6*p 4 + 8*p 5 - 4*p 6 + 4*p 8 - 8*p 9 + 4*p 10 - 2*p 12 + 4*p 13 - 2*p 14) * (1000) + ((- 8*p 1 + 8*p 3 - 6*p 4 + 4*p 5 + 2*p 6 - 8*p 7 + 4*p 8 - 2*p 10 + 4*p 11 - 2*p 12) * (0) + ((8*p 1 - 8*p 3 + 8*p 4 - 8*p 5 + 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_1_6 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 1 6 =
      - 10616*p 1 + 374*p 2 + 9164*p 3 - 11320*p 4 + 6712*p 5 + 1608*p 6 - 7808*p 7 + 7228*p 8 - 2712*p 9 - 1608*p 10 + 3808*p 11 - 3136*p 12 + 1356*p 13 - 374*p 14 + 96*p 15 - 16*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 4*p 4 + 4*p 12 - 2*p 16) * (19) + ((24*p 4 - 16*p 8 + 8*p 12 - 2*p 16) * (-123) + ((- 4*p 2 - 2*p 4 + 8*p 6 - 8*p 10 + 2*p 12 + 4*p 14 - 2*p 16) * (88) + ((2*p 4 - 4*p 6 + 4*p 10 - 2*p 12) * (-89) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 4*p 8 + 4*p 10 - 8*p 11 + 4*p 12 - 2*p 14 + 4*p 15 - 2*p 16) * (24) + ((- 8*p 1 + 2*p 2 + 4*p 3 - 6*p 4 + 8*p 5 - 4*p 6 + 4*p 8 - 8*p 9 + 4*p 10 - 2*p 12 + 4*p 13 - 2*p 14) * (339) + ((- 8*p 1 + 8*p 3 - 6*p 4 + 4*p 5 + 2*p 6 - 8*p 7 + 4*p 8 - 2*p 10 + 4*p 11 - 2*p 12) * (1000) + ((8*p 1 - 8*p 3 + 8*p 4 - 8*p 5 + 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_1_7 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 1 7 =
      5772*p 1 + 22*p 2 - 5856*p 3 + 8238*p 4 - 6804*p 5 + 2494*p 6 + 1936*p 7 - 3976*p 8 + 3840*p 9 - 2494*p 10 + 1028*p 11 - 286*p 12 + 80*p 13 - 22*p 14 + 4*p 15 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 4*p 4 + 4*p 12 - 2*p 16) * (-74) + ((24*p 4 - 16*p 8 + 8*p 12 - 2*p 16) * (68) + ((- 4*p 2 - 2*p 4 + 8*p 6 - 8*p 10 + 2*p 12 + 4*p 14 - 2*p 16) * (5) + ((2*p 4 - 4*p 6 + 4*p 10 - 2*p 12) * (-5) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 4*p 8 + 4*p 10 - 8*p 11 + 4*p 12 - 2*p 14 + 4*p 15 - 2*p 16) * (1) + ((- 8*p 1 + 2*p 2 + 4*p 3 - 6*p 4 + 8*p 5 - 4*p 6 + 4*p 8 - 8*p 9 + 4*p 10 - 2*p 12 + 4*p 13 - 2*p 14) * (20) + ((- 8*p 1 + 8*p 3 - 6*p 4 + 4*p 5 + 2*p 6 - 8*p 7 + 4*p 8 - 2*p 10 + 4*p 11 - 2*p 12) * (259) + ((8*p 1 - 8*p 3 + 8*p 4 - 8*p 5 + 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (1000) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_2_0 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 2 0 =
      4000*p 2 + 2000*p 4 - 8000*p 6 + 4000*p 8 - 2000*p 12 + 4000*p 14 - 2000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 2 + 2*p 4 - 8*p 6 + 4*p 8 - 2*p 12 + 4*p 14 - 2*p 16) * (1000) + ((- 4*p 2 - 2*p 4 + 8*p 6 - 8*p 10 + 2*p 12 + 4*p 14 - 2*p 16) * (0) + ((16*p 2 - 4*p 4 - 2*p 8 + 8*p 10 - 12*p 12 + 8*p 14 - 2*p 16) * (0) + ((8*p 2 - 14*p 4 + 16*p 6 - 14*p 8 + 8*p 10 - 2*p 12) * (0) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 10 + 4*p 11 + 2*p 12 - 8*p 13 + 2*p 14 + 4*p 15 - 2*p 16) * (0) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 8 + 4*p 9 + 2*p 10 - 8*p 11 + 2*p 12 + 4*p 13 - 2*p 14) * (0) + ((4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 6 + 4*p 7 + 2*p 8 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (0) + ((- 2*p 2 + 4*p 3 - 4*p 5 + 4*p 6 - 4*p 7 + 4*p 9 - 2*p 10) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_2_1 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 2 1 =
      - 5000*p 2 - 2500*p 4 + 10000*p 6 - 1000*p 8 - 8000*p 10 + 2500*p 12 + 3000*p 14 - 1500*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 2 + 2*p 4 - 8*p 6 + 4*p 8 - 2*p 12 + 4*p 14 - 2*p 16) * (-250) + ((- 4*p 2 - 2*p 4 + 8*p 6 - 8*p 10 + 2*p 12 + 4*p 14 - 2*p 16) * (1000) + ((16*p 2 - 4*p 4 - 2*p 8 + 8*p 10 - 12*p 12 + 8*p 14 - 2*p 16) * (0) + ((8*p 2 - 14*p 4 + 16*p 6 - 14*p 8 + 8*p 10 - 2*p 12) * (0) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 10 + 4*p 11 + 2*p 12 - 8*p 13 + 2*p 14 + 4*p 15 - 2*p 16) * (0) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 8 + 4*p 9 + 2*p 10 - 8*p 11 + 2*p 12 + 4*p 13 - 2*p 14) * (0) + ((4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 6 + 4*p 7 + 2*p 8 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (0) + ((- 2*p 2 + 4*p 3 - 4*p 5 + 4*p 6 - 4*p 7 + 4*p 9 - 2*p 10) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_2_2 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 2 2 =
      17188*p 2 - 3406*p 4 - 2376*p 6 - 1672*p 8 + 9720*p 10 - 12594*p 12 + 7468*p 14 - 1734*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 2 + 2*p 4 - 8*p 6 + 4*p 8 - 2*p 12 + 4*p 14 - 2*p 16) * (82) + ((- 4*p 2 - 2*p 4 + 8*p 6 - 8*p 10 + 2*p 12 + 4*p 14 - 2*p 16) * (-215) + ((16*p 2 - 4*p 4 - 2*p 8 + 8*p 10 - 12*p 12 + 8*p 14 - 2*p 16) * (1000) + ((8*p 2 - 14*p 4 + 16*p 6 - 14*p 8 + 8*p 10 - 2*p 12) * (0) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 10 + 4*p 11 + 2*p 12 - 8*p 13 + 2*p 14 + 4*p 15 - 2*p 16) * (0) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 8 + 4*p 9 + 2*p 10 - 8*p 11 + 2*p 12 + 4*p 13 - 2*p 14) * (0) + ((4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 6 + 4*p 7 + 2*p 8 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (0) + ((- 2*p 2 + 4*p 3 - 4*p 5 + 4*p 6 - 4*p 7 + 4*p 9 - 2*p 10) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_2_3 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 2 3 =
      11308*p 2 - 15238*p 4 + 17096*p 6 - 15066*p 8 + 10000*p 10 - 4618*p 12 + 1308*p 14 - 172*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 2 + 2*p 4 - 8*p 6 + 4*p 8 - 2*p 12 + 4*p 14 - 2*p 16) * (-146) + ((- 4*p 2 - 2*p 4 + 8*p 6 - 8*p 10 + 2*p 12 + 4*p 14 - 2*p 16) * (-9) + ((16*p 2 - 4*p 4 - 2*p 8 + 8*p 10 - 12*p 12 + 8*p 14 - 2*p 16) * (241) + ((8*p 2 - 14*p 4 + 16*p 6 - 14*p 8 + 8*p 10 - 2*p 12) * (1000) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 10 + 4*p 11 + 2*p 12 - 8*p 13 + 2*p 14 + 4*p 15 - 2*p 16) * (0) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 8 + 4*p 9 + 2*p 10 - 8*p 11 + 2*p 12 + 4*p 13 - 2*p 14) * (0) + ((4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 6 + 4*p 7 + 2*p 8 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (0) + ((- 2*p 2 + 4*p 3 - 4*p 5 + 4*p 6 - 4*p 7 + 4*p 9 - 2*p 10) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_2_4 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 2 4 =
      - 4000*p 1 - 3672*p 2 + 4000*p 3 - 620*p 4 - 528*p 6 + 1064*p 8 - 4232*p 10 + 4000*p 11 + 4556*p 12 - 8000*p 13 + 560*p 14 + 4000*p 15 - 1684*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 2 + 2*p 4 - 8*p 6 + 4*p 8 - 2*p 12 + 4*p 14 - 2*p 16) * (11) + ((- 4*p 2 - 2*p 4 + 8*p 6 - 8*p 10 + 2*p 12 + 4*p 14 - 2*p 16) * (33) + ((16*p 2 - 4*p 4 - 2*p 8 + 8*p 10 - 12*p 12 + 8*p 14 - 2*p 16) * (-202) + ((8*p 2 - 14*p 4 + 16*p 6 - 14*p 8 + 8*p 10 - 2*p 12) * (-44) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 10 + 4*p 11 + 2*p 12 - 8*p 13 + 2*p 14 + 4*p 15 - 2*p 16) * (1000) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 8 + 4*p 9 + 2*p 10 - 8*p 11 + 2*p 12 + 4*p 13 - 2*p 14) * (0) + ((4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 6 + 4*p 7 + 2*p 8 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (0) + ((- 2*p 2 + 4*p 3 - 4*p 5 + 4*p 6 - 4*p 7 + 4*p 9 - 2*p 10) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_2_5 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 2 5 =
      - 5288*p 1 - 968*p 2 + 5288*p 3 - 3704*p 4 + 1488*p 6 - 3480*p 8 + 4000*p 9 + 1780*p 10 - 6712*p 11 + 3928*p 12 + 1424*p 13 - 2748*p 14 + 1288*p 15 - 224*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 2 + 2*p 4 - 8*p 6 + 4*p 8 - 2*p 12 + 4*p 14 - 2*p 16) * (-5) + ((- 4*p 2 - 2*p 4 + 8*p 6 - 8*p 10 + 2*p 12 + 4*p 14 - 2*p 16) * (-67) + ((16*p 2 - 4*p 4 - 2*p 8 + 8*p 10 - 12*p 12 + 8*p 14 - 2*p 16) * (-138) + ((8*p 2 - 14*p 4 + 16*p 6 - 14*p 8 + 8*p 10 - 2*p 12) * (124) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 10 + 4*p 11 + 2*p 12 - 8*p 13 + 2*p 14 + 4*p 15 - 2*p 16) * (322) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 8 + 4*p 9 + 2*p 10 - 8*p 11 + 2*p 12 + 4*p 13 - 2*p 14) * (1000) + ((4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 6 + 4*p 7 + 2*p 8 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (0) + ((- 2*p 2 + 4*p 3 - 4*p 5 + 4*p 6 - 4*p 7 + 4*p 9 - 2*p 10) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_2_6 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 2 6 =
      2548*p 1 + 3264*p 2 - 6548*p 3 + 2452*p 4 + 4000*p 5 - 6560*p 6 + 4000*p 7 + 2468*p 8 - 6644*p 9 + 3606*p 10 + 1384*p 11 - 2436*p 12 + 1164*p 13 - 342*p 14 + 96*p 15 - 16*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 2 + 2*p 4 - 8*p 6 + 4*p 8 - 2*p 12 + 4*p 14 - 2*p 16) * (19) + ((- 4*p 2 - 2*p 4 + 8*p 6 - 8*p 10 + 2*p 12 + 4*p 14 - 2*p 16) * (-123) + ((16*p 2 - 4*p 4 - 2*p 8 + 8*p 10 - 12*p 12 + 8*p 14 - 2*p 16) * (88) + ((8*p 2 - 14*p 4 + 16*p 6 - 14*p 8 + 8*p 10 - 2*p 12) * (-89) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 10 + 4*p 11 + 2*p 12 - 8*p 13 + 2*p 14 + 4*p 15 - 2*p 16) * (24) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 8 + 4*p 9 + 2*p 10 - 8*p 11 + 2*p 12 + 4*p 13 - 2*p 14) * (339) + ((4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 6 + 4*p 7 + 2*p 8 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (1000) + ((- 2*p 2 + 4*p 3 - 4*p 5 + 4*p 6 - 4*p 7 + 4*p 9 - 2*p 10) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_2_7 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 2 7 =
      952*p 1 - 2010*p 2 + 2012*p 3 + 242*p 4 - 2964*p 5 + 4020*p 6 - 2964*p 7 + 242*p 8 + 2008*p 9 - 1988*p 10 + 880*p 11 - 242*p 12 + 72*p 13 - 22*p 14 + 4*p 15 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 2 + 2*p 4 - 8*p 6 + 4*p 8 - 2*p 12 + 4*p 14 - 2*p 16) * (-74) + ((- 4*p 2 - 2*p 4 + 8*p 6 - 8*p 10 + 2*p 12 + 4*p 14 - 2*p 16) * (68) + ((16*p 2 - 4*p 4 - 2*p 8 + 8*p 10 - 12*p 12 + 8*p 14 - 2*p 16) * (5) + ((8*p 2 - 14*p 4 + 16*p 6 - 14*p 8 + 8*p 10 - 2*p 12) * (-5) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 10 + 4*p 11 + 2*p 12 - 8*p 13 + 2*p 14 + 4*p 15 - 2*p 16) * (1) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 8 + 4*p 9 + 2*p 10 - 8*p 11 + 2*p 12 + 4*p 13 - 2*p 14) * (20) + ((4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 6 + 4*p 7 + 2*p 8 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (259) + ((- 2*p 2 + 4*p 3 - 4*p 5 + 4*p 6 - 4*p 7 + 4*p 9 - 2*p 10) * (1000) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_3_0 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 3 0 =
      - 8000*p 2 + 2000*p 4 + 4000*p 6 - 4000*p 8 + 4000*p 10 - 2000*p 12 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 2 + 2*p 4 + 4*p 6 - 4*p 8 + 4*p 10 - 2*p 12) * (1000) + ((2*p 4 - 4*p 6 + 4*p 10 - 2*p 12) * (0) + ((8*p 2 - 14*p 4 + 16*p 6 - 14*p 8 + 8*p 10 - 2*p 12) * (0) + ((24*p 2 - 16*p 4 + 8*p 6 - 2*p 8) * (0) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 8*p 7 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (0) + ((4*p 1 + 2*p 2 - 8*p 3 + 8*p 5 - 8*p 7 + 2*p 8 + 4*p 9 - 2*p 10) * (0) + ((- 4*p 1 - 2*p 2 + 8*p 3 - 8*p 5 + 2*p 6 + 4*p 7 - 2*p 8) * (0) + ((2*p 2 - 4*p 3 + 4*p 5 - 2*p 6) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_3_1 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 3 1 =
      2000*p 2 + 1500*p 4 - 5000*p 6 + 1000*p 8 + 3000*p 10 - 1500*p 12 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 2 + 2*p 4 + 4*p 6 - 4*p 8 + 4*p 10 - 2*p 12) * (-250) + ((2*p 4 - 4*p 6 + 4*p 10 - 2*p 12) * (1000) + ((8*p 2 - 14*p 4 + 16*p 6 - 14*p 8 + 8*p 10 - 2*p 12) * (0) + ((24*p 2 - 16*p 4 + 8*p 6 - 2*p 8) * (0) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 8*p 7 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (0) + ((4*p 1 + 2*p 2 - 8*p 3 + 8*p 5 - 8*p 7 + 2*p 8 + 4*p 9 - 2*p 10) * (0) + ((- 4*p 1 - 2*p 2 + 8*p 3 - 8*p 5 + 2*p 6 + 4*p 7 - 2*p 8) * (0) + ((2*p 2 - 4*p 3 + 4*p 5 - 2*p 6) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_3_2 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 3 2 =
      7344*p 2 - 14266*p 4 + 17188*p 6 - 14328*p 8 + 7468*p 10 - 1734*p 12 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 2 + 2*p 4 + 4*p 6 - 4*p 8 + 4*p 10 - 2*p 12) * (82) + ((2*p 4 - 4*p 6 + 4*p 10 - 2*p 12) * (-215) + ((8*p 2 - 14*p 4 + 16*p 6 - 14*p 8 + 8*p 10 - 2*p 12) * (1000) + ((24*p 2 - 16*p 4 + 8*p 6 - 2*p 8) * (0) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 8*p 7 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (0) + ((4*p 1 + 2*p 2 - 8*p 3 + 8*p 5 - 8*p 7 + 2*p 8 + 4*p 9 - 2*p 10) * (0) + ((- 4*p 1 - 2*p 2 + 8*p 3 - 8*p 5 + 2*p 6 + 4*p 7 - 2*p 8) * (0) + ((2*p 2 - 4*p 3 + 4*p 5 - 2*p 6) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_3_3 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 3 3 =
      27096*p 2 - 19684*p 4 + 11308*p 6 - 4790*p 8 + 1308*p 10 - 172*p 12 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 2 + 2*p 4 + 4*p 6 - 4*p 8 + 4*p 10 - 2*p 12) * (-146) + ((2*p 4 - 4*p 6 + 4*p 10 - 2*p 12) * (-9) + ((8*p 2 - 14*p 4 + 16*p 6 - 14*p 8 + 8*p 10 - 2*p 12) * (241) + ((24*p 2 - 16*p 4 + 8*p 6 - 2*p 8) * (1000) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 8*p 7 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (0) + ((4*p 1 + 2*p 2 - 8*p 3 + 8*p 5 - 8*p 7 + 2*p 8 + 4*p 9 - 2*p 10) * (0) + ((- 4*p 1 - 2*p 2 + 8*p 3 - 8*p 5 + 2*p 6 + 4*p 7 - 2*p 8) * (0) + ((2*p 2 - 4*p 3 + 4*p 5 - 2*p 6) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_3_4 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 3 4 =
      - 4760*p 2 + 4000*p 3 + 5620*p 4 - 8000*p 5 - 3672*p 6 + 8000*p 7 + 2872*p 8 - 8000*p 9 + 560*p 10 + 4000*p 11 - 1684*p 12 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 2 + 2*p 4 + 4*p 6 - 4*p 8 + 4*p 10 - 2*p 12) * (11) + ((2*p 4 - 4*p 6 + 4*p 10 - 2*p 12) * (33) + ((8*p 2 - 14*p 4 + 16*p 6 - 14*p 8 + 8*p 10 - 2*p 12) * (-202) + ((24*p 2 - 16*p 4 + 8*p 6 - 2*p 8) * (-44) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 8*p 7 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (1000) + ((4*p 1 + 2*p 2 - 8*p 3 + 8*p 5 - 8*p 7 + 2*p 8 + 4*p 9 - 2*p 10) * (0) + ((- 4*p 1 - 2*p 2 + 8*p 3 - 8*p 5 + 2*p 6 + 4*p 7 - 2*p 8) * (0) + ((2*p 2 - 4*p 3 + 4*p 5 - 2*p 6) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_3_5 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 3 5 =
      4000*p 1 + 3268*p 2 - 6712*p 3 + 448*p 4 + 5424*p 5 - 968*p 6 - 5424*p 7 + 3704*p 8 + 1424*p 9 - 2748*p 10 + 1288*p 11 - 224*p 12 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 2 + 2*p 4 + 4*p 6 - 4*p 8 + 4*p 10 - 2*p 12) * (-5) + ((2*p 4 - 4*p 6 + 4*p 10 - 2*p 12) * (-67) + ((8*p 2 - 14*p 4 + 16*p 6 - 14*p 8 + 8*p 10 - 2*p 12) * (-138) + ((24*p 2 - 16*p 4 + 8*p 6 - 2*p 8) * (124) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 8*p 7 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (322) + ((4*p 1 + 2*p 2 - 8*p 3 + 8*p 5 - 8*p 7 + 2*p 8 + 4*p 9 - 2*p 10) * (1000) + ((- 4*p 1 - 2*p 2 + 8*p 3 - 8*p 5 + 2*p 6 + 4*p 7 - 2*p 8) * (0) + ((2*p 2 - 4*p 3 + 4*p 5 - 2*p 6) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_3_6 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 3 6 =
      - 2644*p 1 - 2954*p 2 + 5384*p 3 + 32*p 4 - 5480*p 5 + 3264*p 6 + 1480*p 7 - 2452*p 8 + 1164*p 9 - 342*p 10 + 96*p 11 - 16*p 12 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 2 + 2*p 4 + 4*p 6 - 4*p 8 + 4*p 10 - 2*p 12) * (19) + ((2*p 4 - 4*p 6 + 4*p 10 - 2*p 12) * (-123) + ((8*p 2 - 14*p 4 + 16*p 6 - 14*p 8 + 8*p 10 - 2*p 12) * (88) + ((24*p 2 - 16*p 4 + 8*p 6 - 2*p 8) * (-89) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 8*p 7 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (24) + ((4*p 1 + 2*p 2 - 8*p 3 + 8*p 5 - 8*p 7 + 2*p 8 + 4*p 9 - 2*p 10) * (339) + ((- 4*p 1 - 2*p 2 + 8*p 3 - 8*p 5 + 2*p 6 + 4*p 7 - 2*p 8) * (1000) + ((2*p 2 - 4*p 3 + 4*p 5 - 2*p 6) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_3_7 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 3 7 =
      - 956*p 1 + 2032*p 2 - 2084*p 3 + 2080*p 5 - 2010*p 6 + 884*p 7 - 242*p 8 + 72*p 9 - 22*p 10 + 4*p 11 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 2 + 2*p 4 + 4*p 6 - 4*p 8 + 4*p 10 - 2*p 12) * (-74) + ((2*p 4 - 4*p 6 + 4*p 10 - 2*p 12) * (68) + ((8*p 2 - 14*p 4 + 16*p 6 - 14*p 8 + 8*p 10 - 2*p 12) * (5) + ((24*p 2 - 16*p 4 + 8*p 6 - 2*p 8) * (-5) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 8*p 7 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (1) + ((4*p 1 + 2*p 2 - 8*p 3 + 8*p 5 - 8*p 7 + 2*p 8 + 4*p 9 - 2*p 10) * (20) + ((- 4*p 1 - 2*p 2 + 8*p 3 - 8*p 5 + 2*p 6 + 4*p 7 - 2*p 8) * (259) + ((2*p 2 - 4*p 3 + 4*p 5 - 2*p 6) * (1000) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_4_0 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 4 0 =
      4000*p 1 - 2000*p 2 + 4000*p 6 - 8000*p 7 + 4000*p 8 - 2000*p 14 + 4000*p 15 - 2000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 1 - 2*p 2 + 4*p 6 - 8*p 7 + 4*p 8 - 2*p 14 + 4*p 15 - 2*p 16) * (1000) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 4*p 8 + 4*p 10 - 8*p 11 + 4*p 12 - 2*p 14 + 4*p 15 - 2*p 16) * (0) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 10 + 4*p 11 + 2*p 12 - 8*p 13 + 2*p 14 + 4*p 15 - 2*p 16) * (0) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 8*p 7 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (0) + ((16*p 1 - 4*p 2 - 2*p 12 + 8*p 13 - 12*p 14 + 8*p 15 - 2*p 16) * (0) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 10 + 8*p 11 - 12*p 12 + 8*p 13 - 2*p 14) * (0) + ((- 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 - 2*p 8 + 8*p 9 - 12*p 10 + 8*p 11 - 2*p 12) * (0) + ((- 2*p 4 + 8*p 5 - 14*p 6 + 16*p 7 - 14*p 8 + 8*p 9 - 2*p 10) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_4_1 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 4 1 =
      3000*p 1 + 2500*p 2 - 8000*p 3 + 4000*p 4 - 5000*p 6 + 10000*p 7 - 5000*p 8 + 4000*p 10 - 8000*p 11 + 4000*p 12 - 1500*p 14 + 3000*p 15 - 1500*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 1 - 2*p 2 + 4*p 6 - 8*p 7 + 4*p 8 - 2*p 14 + 4*p 15 - 2*p 16) * (-250) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 4*p 8 + 4*p 10 - 8*p 11 + 4*p 12 - 2*p 14 + 4*p 15 - 2*p 16) * (1000) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 10 + 4*p 11 + 2*p 12 - 8*p 13 + 2*p 14 + 4*p 15 - 2*p 16) * (0) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 8*p 7 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (0) + ((16*p 1 - 4*p 2 - 2*p 12 + 8*p 13 - 12*p 14 + 8*p 15 - 2*p 16) * (0) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 10 + 8*p 11 - 12*p 12 + 8*p 13 - 2*p 14) * (0) + ((- 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 - 2*p 8 + 8*p 9 - 12*p 10 + 8*p 11 - 2*p 12) * (0) + ((- 2*p 4 + 8*p 5 - 14*p 6 + 16*p 7 - 14*p 8 + 8*p 9 - 2*p 10) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_4_2 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 4 2 =
      - 4532*p 1 - 594*p 2 + 5720*p 3 - 2860*p 4 + 1188*p 6 - 2376*p 7 + 1188*p 8 - 2860*p 10 + 5720*p 11 + 1140*p 12 - 8000*p 13 + 2266*p 14 + 3468*p 15 - 1734*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 1 - 2*p 2 + 4*p 6 - 8*p 7 + 4*p 8 - 2*p 14 + 4*p 15 - 2*p 16) * (82) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 4*p 8 + 4*p 10 - 8*p 11 + 4*p 12 - 2*p 14 + 4*p 15 - 2*p 16) * (-215) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 10 + 4*p 11 + 2*p 12 - 8*p 13 + 2*p 14 + 4*p 15 - 2*p 16) * (1000) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 8*p 7 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (0) + ((16*p 1 - 4*p 2 - 2*p 12 + 8*p 13 - 12*p 14 + 8*p 15 - 2*p 16) * (0) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 10 + 8*p 11 - 12*p 12 + 8*p 13 - 2*p 14) * (0) + ((- 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 - 2*p 8 + 8*p 9 - 12*p 10 + 8*p 11 - 2*p 12) * (0) + ((- 2*p 4 + 8*p 5 - 14*p 6 + 16*p 7 - 14*p 8 + 8*p 9 - 2*p 10) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_4_3 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 4 3 =
      - 1584*p 1 - 1726*p 2 + 5036*p 3 + 1482*p 4 - 8000*p 5 - 548*p 6 + 9096*p 7 - 548*p 8 - 8000*p 9 + 1482*p 10 + 5036*p 11 - 1554*p 12 - 1928*p 13 + 792*p 14 + 344*p 15 - 172*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 1 - 2*p 2 + 4*p 6 - 8*p 7 + 4*p 8 - 2*p 14 + 4*p 15 - 2*p 16) * (-146) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 4*p 8 + 4*p 10 - 8*p 11 + 4*p 12 - 2*p 14 + 4*p 15 - 2*p 16) * (-9) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 10 + 4*p 11 + 2*p 12 - 8*p 13 + 2*p 14 + 4*p 15 - 2*p 16) * (241) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 8*p 7 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (1000) + ((16*p 1 - 4*p 2 - 2*p 12 + 8*p 13 - 12*p 14 + 8*p 15 - 2*p 16) * (0) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 10 + 8*p 11 - 12*p 12 + 8*p 13 - 2*p 14) * (0) + ((- 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 - 2*p 8 + 8*p 9 - 12*p 10 + 8*p 11 - 2*p 12) * (0) + ((- 2*p 4 + 8*p 5 - 14*p 6 + 16*p 7 - 14*p 8 + 8*p 9 - 2*p 10) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_4_4 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 4 4 =
      16984*p 1 - 3868*p 2 - 1248*p 3 + 448*p 4 + 352*p 5 - 88*p 6 - 176*p 7 - 88*p 8 + 352*p 9 + 448*p 10 - 1248*p 11 - 2184*p 12 + 9616*p 13 - 12492*p 14 + 7368*p 15 - 1684*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 1 - 2*p 2 + 4*p 6 - 8*p 7 + 4*p 8 - 2*p 14 + 4*p 15 - 2*p 16) * (11) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 4*p 8 + 4*p 10 - 8*p 11 + 4*p 12 - 2*p 14 + 4*p 15 - 2*p 16) * (33) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 10 + 4*p 11 + 2*p 12 - 8*p 13 + 2*p 14 + 4*p 15 - 2*p 16) * (-202) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 8*p 7 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (-44) + ((16*p 1 - 4*p 2 - 2*p 12 + 8*p 13 - 12*p 14 + 8*p 15 - 2*p 16) * (1000) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 10 + 8*p 11 - 12*p 12 + 8*p 13 - 2*p 14) * (0) + ((- 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 - 2*p 8 + 8*p 9 - 12*p 10 + 8*p 11 - 2*p 12) * (0) + ((- 2*p 4 + 8*p 5 - 14*p 6 + 16*p 7 - 14*p 8 + 8*p 9 - 2*p 10) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_4_5 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 4 5 =
      13416*p 1 - 13660*p 2 + 8480*p 3 - 1744*p 4 - 992*p 5 + 248*p 6 + 496*p 7 + 248*p 8 - 992*p 9 - 1744*p 10 + 8480*p 11 - 13436*p 12 + 11680*p 13 - 5996*p 14 + 1736*p 15 - 224*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 1 - 2*p 2 + 4*p 6 - 8*p 7 + 4*p 8 - 2*p 14 + 4*p 15 - 2*p 16) * (-5) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 4*p 8 + 4*p 10 - 8*p 11 + 4*p 12 - 2*p 14 + 4*p 15 - 2*p 16) * (-67) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 10 + 4*p 11 + 2*p 12 - 8*p 13 + 2*p 14 + 4*p 15 - 2*p 16) * (-138) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 8*p 7 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (124) + ((16*p 1 - 4*p 2 - 2*p 12 + 8*p 13 - 12*p 14 + 8*p 15 - 2*p 16) * (322) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 10 + 8*p 11 - 12*p 12 + 8*p 13 - 2*p 14) * (1000) + ((- 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 - 2*p 8 + 8*p 9 - 12*p 10 + 8*p 11 - 2*p 12) * (0) + ((- 2*p 4 + 8*p 5 - 14*p 6 + 16*p 7 - 14*p 8 + 8*p 9 - 2*p 10) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_4_6 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 4 6 =
      2328*p 1 - 6270*p 2 + 11692*p 3 - 13524*p 4 + 8712*p 5 - 1432*p 6 - 1848*p 7 - 1432*p 8 + 8712*p 9 - 13524*p 10 + 11692*p 11 - 6254*p 12 + 2200*p 13 - 582*p 14 + 128*p 15 - 16*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 1 - 2*p 2 + 4*p 6 - 8*p 7 + 4*p 8 - 2*p 14 + 4*p 15 - 2*p 16) * (19) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 4*p 8 + 4*p 10 - 8*p 11 + 4*p 12 - 2*p 14 + 4*p 15 - 2*p 16) * (-123) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 10 + 4*p 11 + 2*p 12 - 8*p 13 + 2*p 14 + 4*p 15 - 2*p 16) * (88) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 8*p 7 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (-89) + ((16*p 1 - 4*p 2 - 2*p 12 + 8*p 13 - 12*p 14 + 8*p 15 - 2*p 16) * (24) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 10 + 8*p 11 - 12*p 12 + 8*p 13 - 2*p 14) * (339) + ((- 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 - 2*p 8 + 8*p 9 - 12*p 10 + 8*p 11 - 2*p 12) * (1000) + ((- 2*p 4 + 8*p 5 - 14*p 6 + 16*p 7 - 14*p 8 + 8*p 9 - 2*p 10) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_4_7 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 4 7 =
      132*p 1 - 468*p 2 + 1688*p 3 - 4896*p 4 + 10112*p 5 - 15086*p 6 + 17096*p 7 - 15086*p 8 + 10112*p 9 - 4896*p 10 + 1688*p 11 - 468*p 12 + 128*p 13 - 30*p 14 + 4*p 15 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 1 - 2*p 2 + 4*p 6 - 8*p 7 + 4*p 8 - 2*p 14 + 4*p 15 - 2*p 16) * (-74) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 4*p 8 + 4*p 10 - 8*p 11 + 4*p 12 - 2*p 14 + 4*p 15 - 2*p 16) * (68) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 10 + 4*p 11 + 2*p 12 - 8*p 13 + 2*p 14 + 4*p 15 - 2*p 16) * (5) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 8*p 7 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (-5) + ((16*p 1 - 4*p 2 - 2*p 12 + 8*p 13 - 12*p 14 + 8*p 15 - 2*p 16) * (1) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 10 + 8*p 11 - 12*p 12 + 8*p 13 - 2*p 14) * (20) + ((- 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 - 2*p 8 + 8*p 9 - 12*p 10 + 8*p 11 - 2*p 12) * (259) + ((- 2*p 4 + 8*p 5 - 14*p 6 + 16*p 7 - 14*p 8 + 8*p 9 - 2*p 10) * (1000) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_5_0 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 5 0 =
      - 2000*p 2 + 4000*p 3 + 2000*p 4 - 8000*p 5 + 4000*p 6 - 2000*p 12 + 4000*p 13 - 2000*p 14 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 2*p 12 + 4*p 13 - 2*p 14) * (1000) + ((- 8*p 1 + 2*p 2 + 4*p 3 - 6*p 4 + 8*p 5 - 4*p 6 + 4*p 8 - 8*p 9 + 4*p 10 - 2*p 12 + 4*p 13 - 2*p 14) * (0) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 8 + 4*p 9 + 2*p 10 - 8*p 11 + 2*p 12 + 4*p 13 - 2*p 14) * (0) + ((4*p 1 + 2*p 2 - 8*p 3 + 8*p 5 - 8*p 7 + 2*p 8 + 4*p 9 - 2*p 10) * (0) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 10 + 8*p 11 - 12*p 12 + 8*p 13 - 2*p 14) * (0) + ((16*p 1 - 4*p 2 - 2*p 8 + 8*p 9 - 12*p 10 + 8*p 11 - 2*p 12) * (0) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 6 + 8*p 7 - 12*p 8 + 8*p 9 - 2*p 10) * (0) + ((- 2*p 2 + 8*p 3 - 14*p 4 + 16*p 5 - 14*p 6 + 8*p 7 - 2*p 8) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_5_1 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 5 1 =
      - 8000*p 1 + 2500*p 2 + 3000*p 3 - 6500*p 4 + 10000*p 5 - 5000*p 6 + 4000*p 8 - 8000*p 9 + 4000*p 10 - 1500*p 12 + 3000*p 13 - 1500*p 14 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 2*p 12 + 4*p 13 - 2*p 14) * (-250) + ((- 8*p 1 + 2*p 2 + 4*p 3 - 6*p 4 + 8*p 5 - 4*p 6 + 4*p 8 - 8*p 9 + 4*p 10 - 2*p 12 + 4*p 13 - 2*p 14) * (1000) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 8 + 4*p 9 + 2*p 10 - 8*p 11 + 2*p 12 + 4*p 13 - 2*p 14) * (0) + ((4*p 1 + 2*p 2 - 8*p 3 + 8*p 5 - 8*p 7 + 2*p 8 + 4*p 9 - 2*p 10) * (0) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 10 + 8*p 11 - 12*p 12 + 8*p 13 - 2*p 14) * (0) + ((16*p 1 - 4*p 2 - 2*p 8 + 8*p 9 - 12*p 10 + 8*p 11 - 2*p 12) * (0) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 6 + 8*p 7 - 12*p 8 + 8*p 9 - 2*p 10) * (0) + ((- 2*p 2 + 8*p 3 - 14*p 4 + 16*p 5 - 14*p 6 + 8*p 7 - 2*p 8) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_5_2 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 5 2 =
      - 2280*p 1 - 594*p 2 + 3468*p 3 - 546*p 4 - 2376*p 5 + 1188*p 6 - 2860*p 8 + 5720*p 9 + 1140*p 10 - 8000*p 11 + 2266*p 12 + 3468*p 13 - 1734*p 14 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 2*p 12 + 4*p 13 - 2*p 14) * (82) + ((- 8*p 1 + 2*p 2 + 4*p 3 - 6*p 4 + 8*p 5 - 4*p 6 + 4*p 8 - 8*p 9 + 4*p 10 - 2*p 12 + 4*p 13 - 2*p 14) * (-215) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 8 + 4*p 9 + 2*p 10 - 8*p 11 + 2*p 12 + 4*p 13 - 2*p 14) * (1000) + ((4*p 1 + 2*p 2 - 8*p 3 + 8*p 5 - 8*p 7 + 2*p 8 + 4*p 9 - 2*p 10) * (0) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 10 + 8*p 11 - 12*p 12 + 8*p 13 - 2*p 14) * (0) + ((16*p 1 - 4*p 2 - 2*p 8 + 8*p 9 - 12*p 10 + 8*p 11 - 2*p 12) * (0) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 6 + 8*p 7 - 12*p 8 + 8*p 9 - 2*p 10) * (0) + ((- 2*p 2 + 8*p 3 - 14*p 4 + 16*p 5 - 14*p 6 + 8*p 7 - 2*p 8) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_5_3 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 5 3 =
      3108*p 1 + 2274*p 2 - 7656*p 3 - 720*p 4 + 9096*p 5 - 548*p 6 - 8000*p 7 + 1482*p 8 + 5036*p 9 - 1554*p 10 - 1928*p 11 + 792*p 12 + 344*p 13 - 172*p 14 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 2*p 12 + 4*p 13 - 2*p 14) * (-146) + ((- 8*p 1 + 2*p 2 + 4*p 3 - 6*p 4 + 8*p 5 - 4*p 6 + 4*p 8 - 8*p 9 + 4*p 10 - 2*p 12 + 4*p 13 - 2*p 14) * (-9) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 8 + 4*p 9 + 2*p 10 - 8*p 11 + 2*p 12 + 4*p 13 - 2*p 14) * (241) + ((4*p 1 + 2*p 2 - 8*p 3 + 8*p 5 - 8*p 7 + 2*p 8 + 4*p 9 - 2*p 10) * (1000) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 10 + 8*p 11 - 12*p 12 + 8*p 13 - 2*p 14) * (0) + ((16*p 1 - 4*p 2 - 2*p 8 + 8*p 9 - 12*p 10 + 8*p 11 - 2*p 12) * (0) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 6 + 8*p 7 - 12*p 8 + 8*p 9 - 2*p 10) * (0) + ((- 2*p 2 + 8*p 3 - 14*p 4 + 16*p 5 - 14*p 6 + 8*p 7 - 2*p 8) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_5_4 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 5 4 =
      8368*p 1 - 12044*p 2 + 7720*p 3 - 1772*p 4 - 176*p 5 - 88*p 6 + 352*p 7 + 448*p 8 - 1248*p 9 - 2184*p 10 + 9616*p 11 - 12492*p 12 + 7368*p 13 - 1684*p 14 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 2*p 12 + 4*p 13 - 2*p 14) * (11) + ((- 8*p 1 + 2*p 2 + 4*p 3 - 6*p 4 + 8*p 5 - 4*p 6 + 4*p 8 - 8*p 9 + 4*p 10 - 2*p 12 + 4*p 13 - 2*p 14) * (33) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 8 + 4*p 9 + 2*p 10 - 8*p 11 + 2*p 12 + 4*p 13 - 2*p 14) * (-202) + ((4*p 1 + 2*p 2 - 8*p 3 + 8*p 5 - 8*p 7 + 2*p 8 + 4*p 9 - 2*p 10) * (-44) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 10 + 8*p 11 - 12*p 12 + 8*p 13 - 2*p 14) * (1000) + ((16*p 1 - 4*p 2 - 2*p 8 + 8*p 9 - 12*p 10 + 8*p 11 - 2*p 12) * (0) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 6 + 8*p 7 - 12*p 8 + 8*p 9 - 2*p 10) * (0) + ((- 2*p 2 + 8*p 3 - 14*p 4 + 16*p 5 - 14*p 6 + 8*p 7 - 2*p 8) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_5_5 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 5 5 =
      20160*p 1 - 7740*p 2 + 744*p 3 + 24*p 4 + 496*p 5 + 248*p 6 - 992*p 7 - 1744*p 8 + 8480*p 9 - 13436*p 10 + 11680*p 11 - 5996*p 12 + 1736*p 13 - 224*p 14 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 2*p 12 + 4*p 13 - 2*p 14) * (-5) + ((- 8*p 1 + 2*p 2 + 4*p 3 - 6*p 4 + 8*p 5 - 4*p 6 + 4*p 8 - 8*p 9 + 4*p 10 - 2*p 12 + 4*p 13 - 2*p 14) * (-67) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 8 + 4*p 9 + 2*p 10 - 8*p 11 + 2*p 12 + 4*p 13 - 2*p 14) * (-138) + ((4*p 1 + 2*p 2 - 8*p 3 + 8*p 5 - 8*p 7 + 2*p 8 + 4*p 9 - 2*p 10) * (124) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 10 + 8*p 11 - 12*p 12 + 8*p 13 - 2*p 14) * (322) + ((16*p 1 - 4*p 2 - 2*p 8 + 8*p 9 - 12*p 10 + 8*p 11 - 2*p 12) * (1000) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 6 + 8*p 7 - 12*p 8 + 8*p 9 - 2*p 10) * (0) + ((- 2*p 2 + 8*p 3 - 14*p 4 + 16*p 5 - 14*p 6 + 8*p 7 - 2*p 8) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_5_6 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 5 6 =
      13892*p 1 - 14106*p 2 + 8840*p 3 - 1448*p 4 - 1848*p 5 - 1432*p 6 + 8712*p 7 - 13524*p 8 + 11692*p 9 - 6254*p 10 + 2200*p 11 - 582*p 12 + 128*p 13 - 16*p 14 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 2*p 12 + 4*p 13 - 2*p 14) * (19) + ((- 8*p 1 + 2*p 2 + 4*p 3 - 6*p 4 + 8*p 5 - 4*p 6 + 4*p 8 - 8*p 9 + 4*p 10 - 2*p 12 + 4*p 13 - 2*p 14) * (-123) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 8 + 4*p 9 + 2*p 10 - 8*p 11 + 2*p 12 + 4*p 13 - 2*p 14) * (88) + ((4*p 1 + 2*p 2 - 8*p 3 + 8*p 5 - 8*p 7 + 2*p 8 + 4*p 9 - 2*p 10) * (-89) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 10 + 8*p 11 - 12*p 12 + 8*p 13 - 2*p 14) * (24) + ((16*p 1 - 4*p 2 - 2*p 8 + 8*p 9 - 12*p 10 + 8*p 11 - 2*p 12) * (339) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 6 + 8*p 7 - 12*p 8 + 8*p 9 - 2*p 10) * (1000) + ((- 2*p 2 + 8*p 3 - 14*p 4 + 16*p 5 - 14*p 6 + 8*p 7 - 2*p 8) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_5_7 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 5 7 =
      1816*p 1 - 4926*p 2 + 10116*p 3 - 15086*p 4 + 17096*p 5 - 15086*p 6 + 10112*p 7 - 4896*p 8 + 1688*p 9 - 468*p 10 + 128*p 11 - 30*p 12 + 4*p 13 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 2*p 12 + 4*p 13 - 2*p 14) * (-74) + ((- 8*p 1 + 2*p 2 + 4*p 3 - 6*p 4 + 8*p 5 - 4*p 6 + 4*p 8 - 8*p 9 + 4*p 10 - 2*p 12 + 4*p 13 - 2*p 14) * (68) + ((- 4*p 1 + 4*p 3 - 2*p 4 - 2*p 8 + 4*p 9 + 2*p 10 - 8*p 11 + 2*p 12 + 4*p 13 - 2*p 14) * (5) + ((4*p 1 + 2*p 2 - 8*p 3 + 8*p 5 - 8*p 7 + 2*p 8 + 4*p 9 - 2*p 10) * (-5) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 10 + 8*p 11 - 12*p 12 + 8*p 13 - 2*p 14) * (1) + ((16*p 1 - 4*p 2 - 2*p 8 + 8*p 9 - 12*p 10 + 8*p 11 - 2*p 12) * (20) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 6 + 8*p 7 - 12*p 8 + 8*p 9 - 2*p 10) * (259) + ((- 2*p 2 + 8*p 3 - 14*p 4 + 16*p 5 - 14*p 6 + 8*p 7 - 2*p 8) * (1000) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_6_0 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 6 0 =
      4000*p 2 - 8000*p 3 + 2000*p 4 + 4000*p 5 - 2000*p 6 - 2000*p 10 + 4000*p 11 - 2000*p 12 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 2*p 6 - 2*p 10 + 4*p 11 - 2*p 12) * (1000) + ((- 8*p 1 + 8*p 3 - 6*p 4 + 4*p 5 + 2*p 6 - 8*p 7 + 4*p 8 - 2*p 10 + 4*p 11 - 2*p 12) * (0) + ((4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 6 + 4*p 7 + 2*p 8 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (0) + ((- 4*p 1 - 2*p 2 + 8*p 3 - 8*p 5 + 2*p 6 + 4*p 7 - 2*p 8) * (0) + ((- 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 - 2*p 8 + 8*p 9 - 12*p 10 + 8*p 11 - 2*p 12) * (0) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 6 + 8*p 7 - 12*p 8 + 8*p 9 - 2*p 10) * (0) + ((16*p 1 - 4*p 2 - 2*p 4 + 8*p 5 - 12*p 6 + 8*p 7 - 2*p 8) * (0) + ((8*p 1 - 14*p 2 + 16*p 3 - 14*p 4 + 8*p 5 - 2*p 6) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_6_1 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 6 1 =
      - 8000*p 1 - 1000*p 2 + 10000*p 3 - 6500*p 4 + 3000*p 5 + 2500*p 6 - 8000*p 7 + 4000*p 8 - 1500*p 10 + 3000*p 11 - 1500*p 12 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 2*p 6 - 2*p 10 + 4*p 11 - 2*p 12) * (-250) + ((- 8*p 1 + 8*p 3 - 6*p 4 + 4*p 5 + 2*p 6 - 8*p 7 + 4*p 8 - 2*p 10 + 4*p 11 - 2*p 12) * (1000) + ((4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 6 + 4*p 7 + 2*p 8 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (0) + ((- 4*p 1 - 2*p 2 + 8*p 3 - 8*p 5 + 2*p 6 + 4*p 7 - 2*p 8) * (0) + ((- 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 - 2*p 8 + 8*p 9 - 12*p 10 + 8*p 11 - 2*p 12) * (0) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 6 + 8*p 7 - 12*p 8 + 8*p 9 - 2*p 10) * (0) + ((16*p 1 - 4*p 2 - 2*p 4 + 8*p 5 - 12*p 6 + 8*p 7 - 2*p 8) * (0) + ((8*p 1 - 14*p 2 + 16*p 3 - 14*p 4 + 8*p 5 - 2*p 6) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_6_2 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 6 2 =
      5720*p 1 + 2328*p 2 - 10376*p 3 + 3454*p 4 + 3468*p 5 - 4594*p 6 + 5720*p 7 + 1140*p 8 - 8000*p 9 + 2266*p 10 + 3468*p 11 - 1734*p 12 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 2*p 6 - 2*p 10 + 4*p 11 - 2*p 12) * (82) + ((- 8*p 1 + 8*p 3 - 6*p 4 + 4*p 5 + 2*p 6 - 8*p 7 + 4*p 8 - 2*p 10 + 4*p 11 - 2*p 12) * (-215) + ((4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 6 + 4*p 7 + 2*p 8 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (1000) + ((- 4*p 1 - 2*p 2 + 8*p 3 - 8*p 5 + 2*p 6 + 4*p 7 - 2*p 8) * (0) + ((- 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 - 2*p 8 + 8*p 9 - 12*p 10 + 8*p 11 - 2*p 12) * (0) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 6 + 8*p 7 - 12*p 8 + 8*p 9 - 2*p 10) * (0) + ((16*p 1 - 4*p 2 - 2*p 4 + 8*p 5 - 12*p 6 + 8*p 7 - 2*p 8) * (0) + ((8*p 1 - 14*p 2 + 16*p 3 - 14*p 4 + 8*p 5 - 2*p 6) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_6_3 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 6 3 =
      - 2964*p 1 - 2102*p 2 + 7168*p 3 + 244*p 4 - 7656*p 5 + 1310*p 6 + 5036*p 7 - 1554*p 8 - 1928*p 9 + 792*p 10 + 344*p 11 - 172*p 12 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 2*p 6 - 2*p 10 + 4*p 11 - 2*p 12) * (-146) + ((- 8*p 1 + 8*p 3 - 6*p 4 + 4*p 5 + 2*p 6 - 8*p 7 + 4*p 8 - 2*p 10 + 4*p 11 - 2*p 12) * (-9) + ((4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 6 + 4*p 7 + 2*p 8 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (241) + ((- 4*p 1 - 2*p 2 + 8*p 3 - 8*p 5 + 2*p 6 + 4*p 7 - 2*p 8) * (1000) + ((- 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 - 2*p 8 + 8*p 9 - 12*p 10 + 8*p 11 - 2*p 12) * (0) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 6 + 8*p 7 - 12*p 8 + 8*p 9 - 2*p 10) * (0) + ((16*p 1 - 4*p 2 - 2*p 4 + 8*p 5 - 12*p 6 + 8*p 7 - 2*p 8) * (0) + ((8*p 1 - 14*p 2 + 16*p 3 - 14*p 4 + 8*p 5 - 2*p 6) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_6_4 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 6 4 =
      - 896*p 1 - 2272*p 2 + 9440*p 3 - 12580*p 4 + 7720*p 5 - 1236*p 6 - 1248*p 7 - 2184*p 8 + 9616*p 9 - 12492*p 10 + 7368*p 11 - 1684*p 12 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 2*p 6 - 2*p 10 + 4*p 11 - 2*p 12) * (11) + ((- 8*p 1 + 8*p 3 - 6*p 4 + 4*p 5 + 2*p 6 - 8*p 7 + 4*p 8 - 2*p 10 + 4*p 11 - 2*p 12) * (33) + ((4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 6 + 4*p 7 + 2*p 8 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (-202) + ((- 4*p 1 - 2*p 2 + 8*p 3 - 8*p 5 + 2*p 6 + 4*p 7 - 2*p 8) * (-44) + ((- 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 - 2*p 8 + 8*p 9 - 12*p 10 + 8*p 11 - 2*p 12) * (1000) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 6 + 8*p 7 - 12*p 8 + 8*p 9 - 2*p 10) * (0) + ((16*p 1 - 4*p 2 - 2*p 4 + 8*p 5 - 12*p 6 + 8*p 7 - 2*p 8) * (0) + ((8*p 1 - 14*p 2 + 16*p 3 - 14*p 4 + 8*p 5 - 2*p 6) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_6_5 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 6 5 =
      7488*p 1 - 13188*p 2 + 12176*p 3 - 5748*p 4 + 744*p 5 - 1968*p 6 + 8480*p 7 - 13436*p 8 + 11680*p 9 - 5996*p 10 + 1736*p 11 - 224*p 12 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 2*p 6 - 2*p 10 + 4*p 11 - 2*p 12) * (-5) + ((- 8*p 1 + 8*p 3 - 6*p 4 + 4*p 5 + 2*p 6 - 8*p 7 + 4*p 8 - 2*p 10 + 4*p 11 - 2*p 12) * (-67) + ((4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 6 + 4*p 7 + 2*p 8 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (-138) + ((- 4*p 1 - 2*p 2 + 8*p 3 - 8*p 5 + 2*p 6 + 4*p 7 - 2*p 8) * (124) + ((- 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 - 2*p 8 + 8*p 9 - 12*p 10 + 8*p 11 - 2*p 12) * (322) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 6 + 8*p 7 - 12*p 8 + 8*p 9 - 2*p 10) * (1000) + ((16*p 1 - 4*p 2 - 2*p 4 + 8*p 5 - 12*p 6 + 8*p 7 - 2*p 8) * (0) + ((8*p 1 - 14*p 2 + 16*p 3 - 14*p 4 + 8*p 5 - 2*p 6) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_6_6 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 6 6 =
      20404*p 1 - 7686*p 2 + 352*p 3 - 2014*p 4 + 8840*p 5 - 13540*p 6 + 11692*p 7 - 6254*p 8 + 2200*p 9 - 582*p 10 + 128*p 11 - 16*p 12 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 2*p 6 - 2*p 10 + 4*p 11 - 2*p 12) * (19) + ((- 8*p 1 + 8*p 3 - 6*p 4 + 4*p 5 + 2*p 6 - 8*p 7 + 4*p 8 - 2*p 10 + 4*p 11 - 2*p 12) * (-123) + ((4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 6 + 4*p 7 + 2*p 8 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (88) + ((- 4*p 1 - 2*p 2 + 8*p 3 - 8*p 5 + 2*p 6 + 4*p 7 - 2*p 8) * (-89) + ((- 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 - 2*p 8 + 8*p 9 - 12*p 10 + 8*p 11 - 2*p 12) * (24) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 6 + 8*p 7 - 12*p 8 + 8*p 9 - 2*p 10) * (339) + ((16*p 1 - 4*p 2 - 2*p 4 + 8*p 5 - 12*p 6 + 8*p 7 - 2*p 8) * (1000) + ((8*p 1 - 14*p 2 + 16*p 3 - 14*p 4 + 8*p 5 - 2*p 6) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_6_7 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 6 7 =
      11800*p 1 - 15554*p 2 + 17224*p 3 - 15116*p 4 + 10116*p 5 - 4896*p 6 + 1688*p 7 - 468*p 8 + 128*p 9 - 30*p 10 + 4*p 11 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 2*p 6 - 2*p 10 + 4*p 11 - 2*p 12) * (-74) + ((- 8*p 1 + 8*p 3 - 6*p 4 + 4*p 5 + 2*p 6 - 8*p 7 + 4*p 8 - 2*p 10 + 4*p 11 - 2*p 12) * (68) + ((4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 6 + 4*p 7 + 2*p 8 - 8*p 9 + 2*p 10 + 4*p 11 - 2*p 12) * (5) + ((- 4*p 1 - 2*p 2 + 8*p 3 - 8*p 5 + 2*p 6 + 4*p 7 - 2*p 8) * (-5) + ((- 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 - 2*p 8 + 8*p 9 - 12*p 10 + 8*p 11 - 2*p 12) * (1) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 - 2*p 6 + 8*p 7 - 12*p 8 + 8*p 9 - 2*p 10) * (20) + ((16*p 1 - 4*p 2 - 2*p 4 + 8*p 5 - 12*p 6 + 8*p 7 - 2*p 8) * (259) + ((8*p 1 - 14*p 2 + 16*p 3 - 14*p 4 + 8*p 5 - 2*p 6) * (1000) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_7_0 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 7 0 =
      - 8000*p 1 + 4000*p 2 - 2000*p 6 + 4000*p 7 - 4000*p 8 + 4000*p 9 - 2000*p 10 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 1 + 4*p 2 - 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (1000) + ((8*p 1 - 8*p 3 + 8*p 4 - 8*p 5 + 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (0) + ((- 2*p 2 + 4*p 3 - 4*p 5 + 4*p 6 - 4*p 7 + 4*p 9 - 2*p 10) * (0) + ((2*p 2 - 4*p 3 + 4*p 5 - 2*p 6) * (0) + ((- 2*p 4 + 8*p 5 - 14*p 6 + 16*p 7 - 14*p 8 + 8*p 9 - 2*p 10) * (0) + ((- 2*p 2 + 8*p 3 - 14*p 4 + 16*p 5 - 14*p 6 + 8*p 7 - 2*p 8) * (0) + ((8*p 1 - 14*p 2 + 16*p 3 - 14*p 4 + 8*p 5 - 2*p 6) * (0) + ((24*p 1 - 16*p 2 + 8*p 3 - 2*p 4) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_7_1 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 7 1 =
      10000*p 1 - 1000*p 2 - 8000*p 3 + 8000*p 4 - 8000*p 5 + 2500*p 6 + 3000*p 7 - 3000*p 8 + 3000*p 9 - 1500*p 10 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 1 + 4*p 2 - 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (-250) + ((8*p 1 - 8*p 3 + 8*p 4 - 8*p 5 + 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (1000) + ((- 2*p 2 + 4*p 3 - 4*p 5 + 4*p 6 - 4*p 7 + 4*p 9 - 2*p 10) * (0) + ((2*p 2 - 4*p 3 + 4*p 5 - 2*p 6) * (0) + ((- 2*p 4 + 8*p 5 - 14*p 6 + 16*p 7 - 14*p 8 + 8*p 9 - 2*p 10) * (0) + ((- 2*p 2 + 8*p 3 - 14*p 4 + 16*p 5 - 14*p 6 + 8*p 7 - 2*p 8) * (0) + ((8*p 1 - 14*p 2 + 16*p 3 - 14*p 4 + 8*p 5 - 2*p 6) * (0) + ((24*p 1 - 16*p 2 + 8*p 3 - 2*p 4) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_7_2 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 7 2 =
      - 2376*p 1 - 1672*p 2 + 5720*p 3 - 1720*p 4 - 2280*p 5 + 3406*p 6 - 4532*p 7 + 532*p 8 + 3468*p 9 - 1734*p 10 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 1 + 4*p 2 - 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (82) + ((8*p 1 - 8*p 3 + 8*p 4 - 8*p 5 + 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (-215) + ((- 2*p 2 + 4*p 3 - 4*p 5 + 4*p 6 - 4*p 7 + 4*p 9 - 2*p 10) * (1000) + ((2*p 2 - 4*p 3 + 4*p 5 - 2*p 6) * (0) + ((- 2*p 4 + 8*p 5 - 14*p 6 + 16*p 7 - 14*p 8 + 8*p 9 - 2*p 10) * (0) + ((- 2*p 2 + 8*p 3 - 14*p 4 + 16*p 5 - 14*p 6 + 8*p 7 - 2*p 8) * (0) + ((8*p 1 - 14*p 2 + 16*p 3 - 14*p 4 + 8*p 5 - 2*p 6) * (0) + ((24*p 1 - 16*p 2 + 8*p 3 - 2*p 4) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_7_3 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 7 3 =
      1096*p 1 + 934*p 2 - 2964*p 3 - 72*p 4 + 3108*p 5 - 762*p 6 - 1584*p 7 + 620*p 8 + 344*p 9 - 172*p 10 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 1 + 4*p 2 - 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (-146) + ((8*p 1 - 8*p 3 + 8*p 4 - 8*p 5 + 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (-9) + ((- 2*p 2 + 4*p 3 - 4*p 5 + 4*p 6 - 4*p 7 + 4*p 9 - 2*p 10) * (241) + ((2*p 2 - 4*p 3 + 4*p 5 - 2*p 6) * (1000) + ((- 2*p 4 + 8*p 5 - 14*p 6 + 16*p 7 - 14*p 8 + 8*p 9 - 2*p 10) * (0) + ((- 2*p 2 + 8*p 3 - 14*p 4 + 16*p 5 - 14*p 6 + 8*p 7 - 2*p 8) * (0) + ((8*p 1 - 14*p 2 + 16*p 3 - 14*p 4 + 8*p 5 - 2*p 6) * (0) + ((24*p 1 - 16*p 2 + 8*p 3 - 2*p 4) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_7_4 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 7 4 =
      176*p 1 + 360*p 2 - 896*p 3 - 1736*p 4 + 8368*p 5 - 14676*p 6 + 16984*p 7 - 14176*p 8 + 7368*p 9 - 1684*p 10 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 1 + 4*p 2 - 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (11) + ((8*p 1 - 8*p 3 + 8*p 4 - 8*p 5 + 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (33) + ((- 2*p 2 + 4*p 3 - 4*p 5 + 4*p 6 - 4*p 7 + 4*p 9 - 2*p 10) * (-202) + ((2*p 2 - 4*p 3 + 4*p 5 - 2*p 6) * (-44) + ((- 2*p 4 + 8*p 5 - 14*p 6 + 16*p 7 - 14*p 8 + 8*p 9 - 2*p 10) * (1000) + ((- 2*p 2 + 8*p 3 - 14*p 4 + 16*p 5 - 14*p 6 + 8*p 7 - 2*p 8) * (0) + ((8*p 1 - 14*p 2 + 16*p 3 - 14*p 4 + 8*p 5 - 2*p 6) * (0) + ((24*p 1 - 16*p 2 + 8*p 3 - 2*p 4) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_7_5 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 7 5 =
      - 496*p 1 - 1496*p 2 + 7488*p 3 - 15180*p 4 + 20160*p 5 - 19432*p 6 + 13416*p 7 - 6220*p 8 + 1736*p 9 - 224*p 10 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 1 + 4*p 2 - 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (-5) + ((8*p 1 - 8*p 3 + 8*p 4 - 8*p 5 + 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (-67) + ((- 2*p 2 + 4*p 3 - 4*p 5 + 4*p 6 - 4*p 7 + 4*p 9 - 2*p 10) * (-138) + ((2*p 2 - 4*p 3 + 4*p 5 - 2*p 6) * (124) + ((- 2*p 4 + 8*p 5 - 14*p 6 + 16*p 7 - 14*p 8 + 8*p 9 - 2*p 10) * (322) + ((- 2*p 2 + 8*p 3 - 14*p 4 + 16*p 5 - 14*p 6 + 8*p 7 - 2*p 8) * (1000) + ((8*p 1 - 14*p 2 + 16*p 3 - 14*p 4 + 8*p 5 - 2*p 6) * (0) + ((24*p 1 - 16*p 2 + 8*p 3 - 2*p 4) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_7_6 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 7 6 =
      6864*p 1 - 14956*p 2 + 20404*p 3 - 19778*p 4 + 13892*p 5 - 6836*p 6 + 2328*p 7 - 598*p 8 + 128*p 9 - 16*p 10 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 1 + 4*p 2 - 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (19) + ((8*p 1 - 8*p 3 + 8*p 4 - 8*p 5 + 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (-123) + ((- 2*p 2 + 4*p 3 - 4*p 5 + 4*p 6 - 4*p 7 + 4*p 9 - 2*p 10) * (88) + ((2*p 2 - 4*p 3 + 4*p 5 - 2*p 6) * (-89) + ((- 2*p 4 + 8*p 5 - 14*p 6 + 16*p 7 - 14*p 8 + 8*p 9 - 2*p 10) * (24) + ((- 2*p 2 + 8*p 3 - 14*p 4 + 16*p 5 - 14*p 6 + 8*p 7 - 2*p 8) * (339) + ((8*p 1 - 14*p 2 + 16*p 3 - 14*p 4 + 8*p 5 - 2*p 6) * (1000) + ((24*p 1 - 16*p 2 + 8*p 3 - 2*p 4) * (0) + (0)))))))) = _
  ring

theorem fourthLevelOddRightEntry_7_7 (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 7 7 =
      27208*p 1 - 19982*p 2 + 11800*p 3 - 5364*p 4 + 1816*p 5 - 498*p 6 + 132*p 7 - 30*p 8 + 4*p 9 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 1 + 4*p 2 - 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (-74) + ((8*p 1 - 8*p 3 + 8*p 4 - 8*p 5 + 2*p 6 + 4*p 7 - 4*p 8 + 4*p 9 - 2*p 10) * (68) + ((- 2*p 2 + 4*p 3 - 4*p 5 + 4*p 6 - 4*p 7 + 4*p 9 - 2*p 10) * (5) + ((2*p 2 - 4*p 3 + 4*p 5 - 2*p 6) * (-5) + ((- 2*p 4 + 8*p 5 - 14*p 6 + 16*p 7 - 14*p 8 + 8*p 9 - 2*p 10) * (1) + ((- 2*p 2 + 8*p 3 - 14*p 4 + 16*p 5 - 14*p 6 + 8*p 7 - 2*p 8) * (20) + ((8*p 1 - 14*p 2 + 16*p 3 - 14*p 4 + 8*p 5 - 2*p 6) * (259) + ((24*p 1 - 16*p 2 + 8*p 3 - 2*p 4) * (1000) + (0)))))))) = _
  ring

def fourthLevelOddRightPolynomial (p : Fin 17 → ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  ![![8000*p 8 - 2000*p 16,
    - 4000*p 4 - 2000*p 8 + 4000*p 12 - 1500*p 16,
    4000*p 2 + 2860*p 4 - 8000*p 6 + 4656*p 8 - 2860*p 12 + 4000*p 14 - 1734*p 16,
    - 7036*p 2 + 2518*p 4 + 2072*p 6 - 4204*p 8 + 4000*p 10 - 2518*p 12 + 964*p 14 - 172*p 16,
    4000*p 1 - 2456*p 2 - 624*p 4 + 5440*p 6 - 8000*p 7 + 3456*p 8 - 176*p 10 + 624*p 12 - 2808*p 14 + 4000*p 15 - 1684*p 16,
    1288*p 1 - 4188*p 2 + 4000*p 3 + 2240*p 4 - 8000*p 5 + 6888*p 6 - 2576*p 7 + 200*p 8 + 496*p 10 - 2240*p 12 + 4000*p 13 - 3196*p 14 + 1288*p 15 - 224*p 16,
    96*p 1 + 4338*p 2 - 6644*p 3 + 3168*p 4 + 1288*p 5 - 1608*p 6 - 192*p 7 + 956*p 8 - 2356*p 10 + 4000*p 11 - 3168*p 12 + 1356*p 13 - 374*p 14 + 96*p 15 - 16*p 16,
    - 7996*p 1 + 5054*p 2 - 1992*p 3 + 286*p 4 + 876*p 5 - 2494*p 6 + 3992*p 7 - 4548*p 8 + 4000*p 9 - 2538*p 10 + 1036*p 11 - 286*p 12 + 80*p 13 - 22*p 14 + 4*p 15],
  ![- 4000*p 4 + 4000*p 12 - 2000*p 16,
    25000*p 4 - 16000*p 8 + 7000*p 12 - 1500*p 16,
    - 4000*p 2 - 7488*p 4 + 8000*p 6 + 3440*p 8 - 8000*p 10 + 608*p 12 + 4000*p 14 - 1734*p 16,
    - 964*p 2 + 1886*p 4 - 2072*p 6 + 144*p 8 + 2072*p 10 - 2174*p 12 + 964*p 14 - 172*p 16,
    4000*p 1 + 2808*p 2 - 8000*p 3 + 5064*p 4 - 5440*p 6 + 8000*p 7 - 4528*p 8 + 5440*p 10 - 8000*p 11 + 3992*p 12 - 2808*p 14 + 4000*p 15 - 1684*p 16,
    - 6712*p 1 + 3196*p 2 + 1424*p 3 - 5776*p 4 + 8000*p 5 - 6888*p 6 + 2576*p 7 + 3784*p 8 - 8000*p 9 + 6888*p 10 - 2576*p 11 - 1792*p 12 + 4000*p 13 - 3196*p 14 + 1288*p 15 - 224*p 16,
    - 10616*p 1 + 374*p 2 + 9164*p 3 - 11320*p 4 + 6712*p 5 + 1608*p 6 - 7808*p 7 + 7228*p 8 - 2712*p 9 - 1608*p 10 + 3808*p 11 - 3136*p 12 + 1356*p 13 - 374*p 14 + 96*p 15 - 16*p 16,
    5772*p 1 + 22*p 2 - 5856*p 3 + 8238*p 4 - 6804*p 5 + 2494*p 6 + 1936*p 7 - 3976*p 8 + 3840*p 9 - 2494*p 10 + 1028*p 11 - 286*p 12 + 80*p 13 - 22*p 14 + 4*p 15],
  ![4000*p 2 + 2000*p 4 - 8000*p 6 + 4000*p 8 - 2000*p 12 + 4000*p 14 - 2000*p 16,
    - 5000*p 2 - 2500*p 4 + 10000*p 6 - 1000*p 8 - 8000*p 10 + 2500*p 12 + 3000*p 14 - 1500*p 16,
    17188*p 2 - 3406*p 4 - 2376*p 6 - 1672*p 8 + 9720*p 10 - 12594*p 12 + 7468*p 14 - 1734*p 16,
    11308*p 2 - 15238*p 4 + 17096*p 6 - 15066*p 8 + 10000*p 10 - 4618*p 12 + 1308*p 14 - 172*p 16,
    - 4000*p 1 - 3672*p 2 + 4000*p 3 - 620*p 4 - 528*p 6 + 1064*p 8 - 4232*p 10 + 4000*p 11 + 4556*p 12 - 8000*p 13 + 560*p 14 + 4000*p 15 - 1684*p 16,
    - 5288*p 1 - 968*p 2 + 5288*p 3 - 3704*p 4 + 1488*p 6 - 3480*p 8 + 4000*p 9 + 1780*p 10 - 6712*p 11 + 3928*p 12 + 1424*p 13 - 2748*p 14 + 1288*p 15 - 224*p 16,
    2548*p 1 + 3264*p 2 - 6548*p 3 + 2452*p 4 + 4000*p 5 - 6560*p 6 + 4000*p 7 + 2468*p 8 - 6644*p 9 + 3606*p 10 + 1384*p 11 - 2436*p 12 + 1164*p 13 - 342*p 14 + 96*p 15 - 16*p 16,
    952*p 1 - 2010*p 2 + 2012*p 3 + 242*p 4 - 2964*p 5 + 4020*p 6 - 2964*p 7 + 242*p 8 + 2008*p 9 - 1988*p 10 + 880*p 11 - 242*p 12 + 72*p 13 - 22*p 14 + 4*p 15],
  ![- 8000*p 2 + 2000*p 4 + 4000*p 6 - 4000*p 8 + 4000*p 10 - 2000*p 12,
    2000*p 2 + 1500*p 4 - 5000*p 6 + 1000*p 8 + 3000*p 10 - 1500*p 12,
    7344*p 2 - 14266*p 4 + 17188*p 6 - 14328*p 8 + 7468*p 10 - 1734*p 12,
    27096*p 2 - 19684*p 4 + 11308*p 6 - 4790*p 8 + 1308*p 10 - 172*p 12,
    - 4760*p 2 + 4000*p 3 + 5620*p 4 - 8000*p 5 - 3672*p 6 + 8000*p 7 + 2872*p 8 - 8000*p 9 + 560*p 10 + 4000*p 11 - 1684*p 12,
    4000*p 1 + 3268*p 2 - 6712*p 3 + 448*p 4 + 5424*p 5 - 968*p 6 - 5424*p 7 + 3704*p 8 + 1424*p 9 - 2748*p 10 + 1288*p 11 - 224*p 12,
    - 2644*p 1 - 2954*p 2 + 5384*p 3 + 32*p 4 - 5480*p 5 + 3264*p 6 + 1480*p 7 - 2452*p 8 + 1164*p 9 - 342*p 10 + 96*p 11 - 16*p 12,
    - 956*p 1 + 2032*p 2 - 2084*p 3 + 2080*p 5 - 2010*p 6 + 884*p 7 - 242*p 8 + 72*p 9 - 22*p 10 + 4*p 11],
  ![4000*p 1 - 2000*p 2 + 4000*p 6 - 8000*p 7 + 4000*p 8 - 2000*p 14 + 4000*p 15 - 2000*p 16,
    3000*p 1 + 2500*p 2 - 8000*p 3 + 4000*p 4 - 5000*p 6 + 10000*p 7 - 5000*p 8 + 4000*p 10 - 8000*p 11 + 4000*p 12 - 1500*p 14 + 3000*p 15 - 1500*p 16,
    - 4532*p 1 - 594*p 2 + 5720*p 3 - 2860*p 4 + 1188*p 6 - 2376*p 7 + 1188*p 8 - 2860*p 10 + 5720*p 11 + 1140*p 12 - 8000*p 13 + 2266*p 14 + 3468*p 15 - 1734*p 16,
    - 1584*p 1 - 1726*p 2 + 5036*p 3 + 1482*p 4 - 8000*p 5 - 548*p 6 + 9096*p 7 - 548*p 8 - 8000*p 9 + 1482*p 10 + 5036*p 11 - 1554*p 12 - 1928*p 13 + 792*p 14 + 344*p 15 - 172*p 16,
    16984*p 1 - 3868*p 2 - 1248*p 3 + 448*p 4 + 352*p 5 - 88*p 6 - 176*p 7 - 88*p 8 + 352*p 9 + 448*p 10 - 1248*p 11 - 2184*p 12 + 9616*p 13 - 12492*p 14 + 7368*p 15 - 1684*p 16,
    13416*p 1 - 13660*p 2 + 8480*p 3 - 1744*p 4 - 992*p 5 + 248*p 6 + 496*p 7 + 248*p 8 - 992*p 9 - 1744*p 10 + 8480*p 11 - 13436*p 12 + 11680*p 13 - 5996*p 14 + 1736*p 15 - 224*p 16,
    2328*p 1 - 6270*p 2 + 11692*p 3 - 13524*p 4 + 8712*p 5 - 1432*p 6 - 1848*p 7 - 1432*p 8 + 8712*p 9 - 13524*p 10 + 11692*p 11 - 6254*p 12 + 2200*p 13 - 582*p 14 + 128*p 15 - 16*p 16,
    132*p 1 - 468*p 2 + 1688*p 3 - 4896*p 4 + 10112*p 5 - 15086*p 6 + 17096*p 7 - 15086*p 8 + 10112*p 9 - 4896*p 10 + 1688*p 11 - 468*p 12 + 128*p 13 - 30*p 14 + 4*p 15],
  ![- 2000*p 2 + 4000*p 3 + 2000*p 4 - 8000*p 5 + 4000*p 6 - 2000*p 12 + 4000*p 13 - 2000*p 14,
    - 8000*p 1 + 2500*p 2 + 3000*p 3 - 6500*p 4 + 10000*p 5 - 5000*p 6 + 4000*p 8 - 8000*p 9 + 4000*p 10 - 1500*p 12 + 3000*p 13 - 1500*p 14,
    - 2280*p 1 - 594*p 2 + 3468*p 3 - 546*p 4 - 2376*p 5 + 1188*p 6 - 2860*p 8 + 5720*p 9 + 1140*p 10 - 8000*p 11 + 2266*p 12 + 3468*p 13 - 1734*p 14,
    3108*p 1 + 2274*p 2 - 7656*p 3 - 720*p 4 + 9096*p 5 - 548*p 6 - 8000*p 7 + 1482*p 8 + 5036*p 9 - 1554*p 10 - 1928*p 11 + 792*p 12 + 344*p 13 - 172*p 14,
    8368*p 1 - 12044*p 2 + 7720*p 3 - 1772*p 4 - 176*p 5 - 88*p 6 + 352*p 7 + 448*p 8 - 1248*p 9 - 2184*p 10 + 9616*p 11 - 12492*p 12 + 7368*p 13 - 1684*p 14,
    20160*p 1 - 7740*p 2 + 744*p 3 + 24*p 4 + 496*p 5 + 248*p 6 - 992*p 7 - 1744*p 8 + 8480*p 9 - 13436*p 10 + 11680*p 11 - 5996*p 12 + 1736*p 13 - 224*p 14,
    13892*p 1 - 14106*p 2 + 8840*p 3 - 1448*p 4 - 1848*p 5 - 1432*p 6 + 8712*p 7 - 13524*p 8 + 11692*p 9 - 6254*p 10 + 2200*p 11 - 582*p 12 + 128*p 13 - 16*p 14,
    1816*p 1 - 4926*p 2 + 10116*p 3 - 15086*p 4 + 17096*p 5 - 15086*p 6 + 10112*p 7 - 4896*p 8 + 1688*p 9 - 468*p 10 + 128*p 11 - 30*p 12 + 4*p 13],
  ![4000*p 2 - 8000*p 3 + 2000*p 4 + 4000*p 5 - 2000*p 6 - 2000*p 10 + 4000*p 11 - 2000*p 12,
    - 8000*p 1 - 1000*p 2 + 10000*p 3 - 6500*p 4 + 3000*p 5 + 2500*p 6 - 8000*p 7 + 4000*p 8 - 1500*p 10 + 3000*p 11 - 1500*p 12,
    5720*p 1 + 2328*p 2 - 10376*p 3 + 3454*p 4 + 3468*p 5 - 4594*p 6 + 5720*p 7 + 1140*p 8 - 8000*p 9 + 2266*p 10 + 3468*p 11 - 1734*p 12,
    - 2964*p 1 - 2102*p 2 + 7168*p 3 + 244*p 4 - 7656*p 5 + 1310*p 6 + 5036*p 7 - 1554*p 8 - 1928*p 9 + 792*p 10 + 344*p 11 - 172*p 12,
    - 896*p 1 - 2272*p 2 + 9440*p 3 - 12580*p 4 + 7720*p 5 - 1236*p 6 - 1248*p 7 - 2184*p 8 + 9616*p 9 - 12492*p 10 + 7368*p 11 - 1684*p 12,
    7488*p 1 - 13188*p 2 + 12176*p 3 - 5748*p 4 + 744*p 5 - 1968*p 6 + 8480*p 7 - 13436*p 8 + 11680*p 9 - 5996*p 10 + 1736*p 11 - 224*p 12,
    20404*p 1 - 7686*p 2 + 352*p 3 - 2014*p 4 + 8840*p 5 - 13540*p 6 + 11692*p 7 - 6254*p 8 + 2200*p 9 - 582*p 10 + 128*p 11 - 16*p 12,
    11800*p 1 - 15554*p 2 + 17224*p 3 - 15116*p 4 + 10116*p 5 - 4896*p 6 + 1688*p 7 - 468*p 8 + 128*p 9 - 30*p 10 + 4*p 11],
  ![- 8000*p 1 + 4000*p 2 - 2000*p 6 + 4000*p 7 - 4000*p 8 + 4000*p 9 - 2000*p 10,
    10000*p 1 - 1000*p 2 - 8000*p 3 + 8000*p 4 - 8000*p 5 + 2500*p 6 + 3000*p 7 - 3000*p 8 + 3000*p 9 - 1500*p 10,
    - 2376*p 1 - 1672*p 2 + 5720*p 3 - 1720*p 4 - 2280*p 5 + 3406*p 6 - 4532*p 7 + 532*p 8 + 3468*p 9 - 1734*p 10,
    1096*p 1 + 934*p 2 - 2964*p 3 - 72*p 4 + 3108*p 5 - 762*p 6 - 1584*p 7 + 620*p 8 + 344*p 9 - 172*p 10,
    176*p 1 + 360*p 2 - 896*p 3 - 1736*p 4 + 8368*p 5 - 14676*p 6 + 16984*p 7 - 14176*p 8 + 7368*p 9 - 1684*p 10,
    - 496*p 1 - 1496*p 2 + 7488*p 3 - 15180*p 4 + 20160*p 5 - 19432*p 6 + 13416*p 7 - 6220*p 8 + 1736*p 9 - 224*p 10,
    6864*p 1 - 14956*p 2 + 20404*p 3 - 19778*p 4 + 13892*p 5 - 6836*p 6 + 2328*p 7 - 598*p 8 + 128*p 9 - 16*p 10,
    27208*p 1 - 19982*p 2 + 11800*p 3 - 5364*p 4 + 1816*p 5 - 498*p 6 + 132*p 7 - 30*p 8 + 4*p 9]]

theorem fourthLevelOddRight_row0 (p : Fin 17 → ℝ) (j : Fin 8) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 0 j =
      fourthLevelOddRightPolynomial p 0 j := by
  fin_cases j
  · exact fourthLevelOddRightEntry_0_0 p
  · exact fourthLevelOddRightEntry_0_1 p
  · exact fourthLevelOddRightEntry_0_2 p
  · exact fourthLevelOddRightEntry_0_3 p
  · exact fourthLevelOddRightEntry_0_4 p
  · exact fourthLevelOddRightEntry_0_5 p
  · exact fourthLevelOddRightEntry_0_6 p
  · exact fourthLevelOddRightEntry_0_7 p

theorem fourthLevelOddRight_row1 (p : Fin 17 → ℝ) (j : Fin 8) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 1 j =
      fourthLevelOddRightPolynomial p 1 j := by
  fin_cases j
  · exact fourthLevelOddRightEntry_1_0 p
  · exact fourthLevelOddRightEntry_1_1 p
  · exact fourthLevelOddRightEntry_1_2 p
  · exact fourthLevelOddRightEntry_1_3 p
  · exact fourthLevelOddRightEntry_1_4 p
  · exact fourthLevelOddRightEntry_1_5 p
  · exact fourthLevelOddRightEntry_1_6 p
  · exact fourthLevelOddRightEntry_1_7 p

theorem fourthLevelOddRight_row2 (p : Fin 17 → ℝ) (j : Fin 8) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 2 j =
      fourthLevelOddRightPolynomial p 2 j := by
  fin_cases j
  · exact fourthLevelOddRightEntry_2_0 p
  · exact fourthLevelOddRightEntry_2_1 p
  · exact fourthLevelOddRightEntry_2_2 p
  · exact fourthLevelOddRightEntry_2_3 p
  · exact fourthLevelOddRightEntry_2_4 p
  · exact fourthLevelOddRightEntry_2_5 p
  · exact fourthLevelOddRightEntry_2_6 p
  · exact fourthLevelOddRightEntry_2_7 p

theorem fourthLevelOddRight_row3 (p : Fin 17 → ℝ) (j : Fin 8) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 3 j =
      fourthLevelOddRightPolynomial p 3 j := by
  fin_cases j
  · exact fourthLevelOddRightEntry_3_0 p
  · exact fourthLevelOddRightEntry_3_1 p
  · exact fourthLevelOddRightEntry_3_2 p
  · exact fourthLevelOddRightEntry_3_3 p
  · exact fourthLevelOddRightEntry_3_4 p
  · exact fourthLevelOddRightEntry_3_5 p
  · exact fourthLevelOddRightEntry_3_6 p
  · exact fourthLevelOddRightEntry_3_7 p

theorem fourthLevelOddRight_row4 (p : Fin 17 → ℝ) (j : Fin 8) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 4 j =
      fourthLevelOddRightPolynomial p 4 j := by
  fin_cases j
  · exact fourthLevelOddRightEntry_4_0 p
  · exact fourthLevelOddRightEntry_4_1 p
  · exact fourthLevelOddRightEntry_4_2 p
  · exact fourthLevelOddRightEntry_4_3 p
  · exact fourthLevelOddRightEntry_4_4 p
  · exact fourthLevelOddRightEntry_4_5 p
  · exact fourthLevelOddRightEntry_4_6 p
  · exact fourthLevelOddRightEntry_4_7 p

theorem fourthLevelOddRight_row5 (p : Fin 17 → ℝ) (j : Fin 8) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 5 j =
      fourthLevelOddRightPolynomial p 5 j := by
  fin_cases j
  · exact fourthLevelOddRightEntry_5_0 p
  · exact fourthLevelOddRightEntry_5_1 p
  · exact fourthLevelOddRightEntry_5_2 p
  · exact fourthLevelOddRightEntry_5_3 p
  · exact fourthLevelOddRightEntry_5_4 p
  · exact fourthLevelOddRightEntry_5_5 p
  · exact fourthLevelOddRightEntry_5_6 p
  · exact fourthLevelOddRightEntry_5_7 p

theorem fourthLevelOddRight_row6 (p : Fin 17 → ℝ) (j : Fin 8) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 6 j =
      fourthLevelOddRightPolynomial p 6 j := by
  fin_cases j
  · exact fourthLevelOddRightEntry_6_0 p
  · exact fourthLevelOddRightEntry_6_1 p
  · exact fourthLevelOddRightEntry_6_2 p
  · exact fourthLevelOddRightEntry_6_3 p
  · exact fourthLevelOddRightEntry_6_4 p
  · exact fourthLevelOddRightEntry_6_5 p
  · exact fourthLevelOddRightEntry_6_6 p
  · exact fourthLevelOddRightEntry_6_7 p

theorem fourthLevelOddRight_row7 (p : Fin 17 → ℝ) (j : Fin 8) :
    (fourthLevelOddPolynomial p * fourthLevelOddShearNumerator) 7 j =
      fourthLevelOddRightPolynomial p 7 j := by
  fin_cases j
  · exact fourthLevelOddRightEntry_7_0 p
  · exact fourthLevelOddRightEntry_7_1 p
  · exact fourthLevelOddRightEntry_7_2 p
  · exact fourthLevelOddRightEntry_7_3 p
  · exact fourthLevelOddRightEntry_7_4 p
  · exact fourthLevelOddRightEntry_7_5 p
  · exact fourthLevelOddRightEntry_7_6 p
  · exact fourthLevelOddRightEntry_7_7 p

theorem fourthLevelOddRight_eq (p : Fin 17 → ℝ) :
    fourthLevelOddPolynomial p * fourthLevelOddShearNumerator =
      fourthLevelOddRightPolynomial p := by
  ext i j
  fin_cases i
  · exact fourthLevelOddRight_row0 p j
  · exact fourthLevelOddRight_row1 p j
  · exact fourthLevelOddRight_row2 p j
  · exact fourthLevelOddRight_row3 p j
  · exact fourthLevelOddRight_row4 p j
  · exact fourthLevelOddRight_row5 p j
  · exact fourthLevelOddRight_row6 p j
  · exact fourthLevelOddRight_row7 p j

theorem fourthLevelEvenRightEntry_0_0 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 0 0 =
      8000*p 4 + 8000*p 8 - 8000*p 12 + 2000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (8*p 4 + 8*p 8 - 8*p 12 + 2*p 16) * (1000) + ((- 4*p 2 + 2*p 4 - 4*p 8 + 8*p 10 - 2*p 12 - 4*p 14 + 2*p 16) * (0) + ((- 8*p 2 - 2*p 4 + 12*p 6 - 4*p 8 - 4*p 10 + 2*p 12) * (0) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 10 + 8*p 11 - 4*p 12 + 2*p 14 - 4*p 15 + 2*p 16) * (0) + ((- 8*p 1 + 2*p 2 + 4*p 3 - 2*p 4 - 4*p 8 + 8*p 9 - 4*p 10 + 2*p 12 - 4*p 13 + 2*p 14) * (0) + ((- 8*p 1 + 4*p 2 - 2*p 4 + 4*p 5 - 6*p 6 + 8*p 7 - 4*p 8 + 2*p 10 - 4*p 11 + 2*p 12) * (0) + ((4*p 2 - 8*p 3 + 8*p 5 - 6*p 6 + 4*p 7 - 4*p 9 + 2*p 10) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_0_1 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 0 1 =
      - 4000*p 2 + 600*p 4 - 5400*p 8 + 8000*p 10 - 600*p 12 - 4000*p 14 + 1650*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (8*p 4 + 8*p 8 - 8*p 12 + 2*p 16) * (-175) + ((- 4*p 2 + 2*p 4 - 4*p 8 + 8*p 10 - 2*p 12 - 4*p 14 + 2*p 16) * (1000) + ((- 8*p 2 - 2*p 4 + 12*p 6 - 4*p 8 - 4*p 10 + 2*p 12) * (0) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 10 + 8*p 11 - 4*p 12 + 2*p 14 - 4*p 15 + 2*p 16) * (0) + ((- 8*p 1 + 2*p 2 + 4*p 3 - 2*p 4 - 4*p 8 + 8*p 9 - 4*p 10 + 2*p 12 - 4*p 13 + 2*p 14) * (0) + ((- 8*p 1 + 4*p 2 - 2*p 4 + 4*p 5 - 6*p 6 + 8*p 7 - 4*p 8 + 2*p 10 - 4*p 11 + 2*p 12) * (0) + ((4*p 2 - 8*p 3 + 8*p 5 - 6*p 6 + 4*p 7 - 4*p 9 + 2*p 10) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_0_2 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 0 2 =
      - 9564*p 2 - 3290*p 4 + 12000*p 6 - 7636*p 8 - 872*p 10 + 3290*p 12 - 1564*p 14 + 264*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (8*p 4 + 8*p 8 - 8*p 12 + 2*p 16) * (-259) + ((- 4*p 2 + 2*p 4 - 4*p 8 + 8*p 10 - 2*p 12 - 4*p 14 + 2*p 16) * (391) + ((- 8*p 2 - 2*p 4 + 12*p 6 - 4*p 8 - 4*p 10 + 2*p 12) * (1000) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 10 + 8*p 11 - 4*p 12 + 2*p 14 - 4*p 15 + 2*p 16) * (0) + ((- 8*p 1 + 2*p 2 + 4*p 3 - 2*p 4 - 4*p 8 + 8*p 9 - 4*p 10 + 2*p 12 - 4*p 13 + 2*p 14) * (0) + ((- 8*p 1 + 4*p 2 - 2*p 4 + 4*p 5 - 6*p 6 + 8*p 7 - 4*p 8 + 2*p 10 - 4*p 11 + 2*p 12) * (0) + ((4*p 2 - 8*p 3 + 8*p 5 - 6*p 6 + 4*p 7 - 4*p 9 + 2*p 10) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_0_3 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 0 3 =
      4000*p 1 + 3208*p 2 - 8000*p 3 + 3860*p 4 - 480*p 6 + 1272*p 8 - 5616*p 10 + 8000*p 11 - 3860*p 12 + 2888*p 14 - 4000*p 15 + 1612*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (8*p 4 + 8*p 8 - 8*p 12 + 2*p 16) * (28) + ((- 4*p 2 + 2*p 4 - 4*p 8 + 8*p 10 - 2*p 12 - 4*p 14 + 2*p 16) * (-222) + ((- 8*p 2 - 2*p 4 + 12*p 6 - 4*p 8 - 4*p 10 + 2*p 12) * (-40) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 10 + 8*p 11 - 4*p 12 + 2*p 14 - 4*p 15 + 2*p 16) * (1000) + ((- 8*p 1 + 2*p 2 + 4*p 3 - 2*p 4 - 4*p 8 + 8*p 9 - 4*p 10 + 2*p 12 - 4*p 13 + 2*p 14) * (0) + ((- 8*p 1 + 4*p 2 - 2*p 4 + 4*p 5 - 6*p 6 + 8*p 7 - 4*p 8 + 2*p 10 - 4*p 11 + 2*p 12) * (0) + ((4*p 2 - 8*p 3 + 8*p 5 - 6*p 6 + 4*p 7 - 4*p 9 + 2*p 10) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_0_4 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 0 4 =
      - 6720*p 1 + 2336*p 2 + 1440*p 3 - 1792*p 4 + 1296*p 6 - 4448*p 8 + 8000*p 9 - 6832*p 10 + 2560*p 11 + 1792*p 12 - 4000*p 13 + 3200*p 14 - 1280*p 15 + 216*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (8*p 4 + 8*p 8 - 8*p 12 + 2*p 16) * (-72) + ((- 4*p 2 + 2*p 4 - 4*p 8 + 8*p 10 - 2*p 12 - 4*p 14 + 2*p 16) * (-140) + ((- 8*p 2 - 2*p 4 + 12*p 6 - 4*p 8 - 4*p 10 + 2*p 12) * (108) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 10 + 8*p 11 - 4*p 12 + 2*p 14 - 4*p 15 + 2*p 16) * (320) + ((- 8*p 1 + 2*p 2 + 4*p 3 - 2*p 4 - 4*p 8 + 8*p 9 - 4*p 10 + 2*p 12 - 4*p 13 + 2*p 14) * (1000) + ((- 8*p 1 + 4*p 2 - 2*p 4 + 4*p 5 - 6*p 6 + 8*p 7 - 4*p 8 + 2*p 10 - 4*p 11 + 2*p 12) * (0) + ((4*p 2 - 8*p 3 + 8*p 5 - 6*p 6 + 4*p 7 - 4*p 9 + 2*p 10) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_0_5 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 0 5 =
      - 10708*p 1 + 4596*p 2 + 1204*p 3 - 3232*p 4 + 4000*p 5 - 6312*p 6 + 8000*p 7 - 6528*p 8 + 2808*p 9 + 1328*p 10 - 3800*p 11 + 3232*p 12 - 1404*p 13 + 388*p 14 - 100*p 15 + 16*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (8*p 4 + 8*p 8 - 8*p 12 + 2*p 16) * (-108) + ((- 4*p 2 + 2*p 4 - 4*p 8 + 8*p 10 - 2*p 12 - 4*p 14 + 2*p 16) * (91) + ((- 8*p 2 - 2*p 4 + 12*p 6 - 4*p 8 - 4*p 10 + 2*p 12) * (-26) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 10 + 8*p 11 - 4*p 12 + 2*p 14 - 4*p 15 + 2*p 16) * (25) + ((- 8*p 1 + 2*p 2 + 4*p 3 - 2*p 4 - 4*p 8 + 8*p 9 - 4*p 10 + 2*p 12 - 4*p 13 + 2*p 14) * (351) + ((- 8*p 1 + 4*p 2 - 2*p 4 + 4*p 5 - 6*p 6 + 8*p 7 - 4*p 8 + 2*p 10 - 4*p 11 + 2*p 12) * (1000) + ((4*p 2 - 8*p 3 + 8*p 5 - 6*p 6 + 4*p 7 - 4*p 9 + 2*p 10) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_0_6 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 0 6 =
      - 3672*p 1 + 7766*p 2 - 7884*p 3 - 468*p 4 + 9708*p 5 - 11598*p 6 + 7416*p 7 - 944*p 8 - 3736*p 9 + 3798*p 10 - 1692*p 11 + 468*p 12 - 132*p 13 + 34*p 14 - 8*p 15 + 2*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (8*p 4 + 8*p 8 - 8*p 12 + 2*p 16) * (-10) + ((- 4*p 2 + 2*p 4 - 4*p 8 + 8*p 10 - 2*p 12 - 4*p 14 + 2*p 16) * (9) + ((- 8*p 2 - 2*p 4 + 12*p 6 - 4*p 8 - 4*p 10 + 2*p 12) * (-253) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 10 + 8*p 11 - 4*p 12 + 2*p 14 - 4*p 15 + 2*p 16) * (2) + ((- 8*p 1 + 2*p 2 + 4*p 3 - 2*p 4 - 4*p 8 + 8*p 9 - 4*p 10 + 2*p 12 - 4*p 13 + 2*p 14) * (33) + ((- 8*p 1 + 4*p 2 - 2*p 4 + 4*p 5 - 6*p 6 + 8*p 7 - 4*p 8 + 2*p 10 - 4*p 11 + 2*p 12) * (427) + ((4*p 2 - 8*p 3 + 8*p 5 - 6*p 6 + 4*p 7 - 4*p 9 + 2*p 10) * (1000) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_1_0 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 1 0 =
      - 4000*p 2 + 2000*p 4 - 4000*p 8 + 8000*p 10 - 2000*p 12 - 4000*p 14 + 2000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 4*p 2 + 2*p 4 - 4*p 8 + 8*p 10 - 2*p 12 - 4*p 14 + 2*p 16) * (1000) + ((16*p 2 - 4*p 4 + 2*p 8 - 8*p 10 + 12*p 12 - 8*p 14 + 2*p 16) * (0) + ((8*p 2 - 10*p 4 + 10*p 8 - 8*p 10 + 2*p 12) * (0) + ((- 4*p 1 + 4*p 3 - 2*p 4 + 2*p 10 - 4*p 11 - 2*p 12 + 8*p 13 - 2*p 14 - 4*p 15 + 2*p 16) * (0) + ((- 4*p 1 + 4*p 3 - 2*p 4 + 2*p 8 - 4*p 9 - 2*p 10 + 8*p 11 - 2*p 12 - 4*p 13 + 2*p 14) * (0) + ((4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 7 - 2*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12) * (0) + ((- 2*p 2 + 4*p 3 + 4*p 4 - 12*p 5 + 12*p 7 - 4*p 8 - 4*p 9 + 2*p 10) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_1_1 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 1 1 =
      16700*p 2 - 4350*p 4 + 2700*p 8 - 9400*p 10 + 12350*p 12 - 7300*p 14 + 1650*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 4*p 2 + 2*p 4 - 4*p 8 + 8*p 10 - 2*p 12 - 4*p 14 + 2*p 16) * (-175) + ((16*p 2 - 4*p 4 + 2*p 8 - 8*p 10 + 12*p 12 - 8*p 14 + 2*p 16) * (1000) + ((8*p 2 - 10*p 4 + 10*p 8 - 8*p 10 + 2*p 12) * (0) + ((- 4*p 1 + 4*p 3 - 2*p 4 + 2*p 10 - 4*p 11 - 2*p 12 + 8*p 13 - 2*p 14 - 4*p 15 + 2*p 16) * (0) + ((- 4*p 1 + 4*p 3 - 2*p 4 + 2*p 8 - 4*p 9 - 2*p 10 + 8*p 11 - 2*p 12 - 4*p 13 + 2*p 14) * (0) + ((4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 7 - 2*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12) * (0) + ((- 2*p 2 + 4*p 3 + 4*p 4 - 12*p 5 + 12*p 7 - 4*p 8 - 4*p 9 + 2*p 10) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_1_2 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 1 2 =
      15292*p 2 - 12082*p 4 + 11818*p 8 - 13200*p 10 + 7210*p 12 - 2092*p 14 + 264*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 4*p 2 + 2*p 4 - 4*p 8 + 8*p 10 - 2*p 12 - 4*p 14 + 2*p 16) * (-259) + ((16*p 2 - 4*p 4 + 2*p 8 - 8*p 10 + 12*p 12 - 8*p 14 + 2*p 16) * (391) + ((8*p 2 - 10*p 4 + 10*p 8 - 8*p 10 + 2*p 12) * (1000) + ((- 4*p 1 + 4*p 3 - 2*p 4 + 2*p 10 - 4*p 11 - 2*p 12 + 8*p 13 - 2*p 14 - 4*p 15 + 2*p 16) * (0) + ((- 4*p 1 + 4*p 3 - 2*p 4 + 2*p 8 - 4*p 9 - 2*p 10 + 8*p 11 - 2*p 12 - 4*p 13 + 2*p 14) * (0) + ((4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 7 - 2*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12) * (0) + ((- 2*p 2 + 4*p 3 + 4*p 4 - 12*p 5 + 12*p 7 - 4*p 8 - 4*p 9 + 2*p 10) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_1_3 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 1 3 =
      - 4000*p 1 - 3984*p 2 + 4000*p 3 - 656*p 4 - 956*p 8 + 4320*p 10 - 4000*p 11 - 4800*p 12 + 8000*p 13 - 336*p 14 - 4000*p 15 + 1612*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 4*p 2 + 2*p 4 - 4*p 8 + 8*p 10 - 2*p 12 - 4*p 14 + 2*p 16) * (28) + ((16*p 2 - 4*p 4 + 2*p 8 - 8*p 10 + 12*p 12 - 8*p 14 + 2*p 16) * (-222) + ((8*p 2 - 10*p 4 + 10*p 8 - 8*p 10 + 2*p 12) * (-40) + ((- 4*p 1 + 4*p 3 - 2*p 4 + 2*p 10 - 4*p 11 - 2*p 12 + 8*p 13 - 2*p 14 - 4*p 15 + 2*p 16) * (1000) + ((- 4*p 1 + 4*p 3 - 2*p 4 + 2*p 8 - 4*p 9 - 2*p 10 + 8*p 11 - 2*p 12 - 4*p 13 + 2*p 14) * (0) + ((4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 7 - 2*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12) * (0) + ((- 2*p 2 + 4*p 3 + 4*p 4 - 12*p 5 + 12*p 7 - 4*p 8 - 4*p 9 + 2*p 10) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_1_4 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 1 4 =
      - 5280*p 1 - 1088*p 2 + 5280*p 3 - 3304*p 4 + 3088*p 8 - 4000*p 9 - 1680*p 10 + 6720*p 11 - 3960*p 12 - 1440*p 13 + 2768*p 14 - 1280*p 15 + 216*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 4*p 2 + 2*p 4 - 4*p 8 + 8*p 10 - 2*p 12 - 4*p 14 + 2*p 16) * (-72) + ((16*p 2 - 4*p 4 + 2*p 8 - 8*p 10 + 12*p 12 - 8*p 14 + 2*p 16) * (-140) + ((8*p 2 - 10*p 4 + 10*p 8 - 8*p 10 + 2*p 12) * (108) + ((- 4*p 1 + 4*p 3 - 2*p 4 + 2*p 10 - 4*p 11 - 2*p 12 + 8*p 13 - 2*p 14 - 4*p 15 + 2*p 16) * (320) + ((- 4*p 1 + 4*p 3 - 2*p 4 + 2*p 8 - 4*p 9 - 2*p 10 + 8*p 11 - 2*p 12 - 4*p 13 + 2*p 14) * (1000) + ((4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 7 - 2*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12) * (0) + ((- 2*p 2 + 4*p 3 + 4*p 4 - 12*p 5 + 12*p 7 - 4*p 8 - 4*p 9 + 2*p 10) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_1_5 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 1 5 =
      2496*p 1 + 3680*p 2 - 6496*p 3 + 928*p 4 + 4000*p 5 - 4000*p 7 - 944*p 8 + 6596*p 9 - 4036*p 10 - 1292*p 11 + 2504*p 12 - 1204*p 13 + 356*p 14 - 100*p 15 + 16*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 4*p 2 + 2*p 4 - 4*p 8 + 8*p 10 - 2*p 12 - 4*p 14 + 2*p 16) * (-108) + ((16*p 2 - 4*p 4 + 2*p 8 - 8*p 10 + 12*p 12 - 8*p 14 + 2*p 16) * (91) + ((8*p 2 - 10*p 4 + 10*p 8 - 8*p 10 + 2*p 12) * (-26) + ((- 4*p 1 + 4*p 3 - 2*p 4 + 2*p 10 - 4*p 11 - 2*p 12 + 8*p 13 - 2*p 14 - 4*p 15 + 2*p 16) * (25) + ((- 4*p 1 + 4*p 3 - 2*p 4 + 2*p 8 - 4*p 9 - 2*p 10 + 8*p 11 - 2*p 12 - 4*p 13 + 2*p 14) * (351) + ((4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 7 - 2*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12) * (1000) + ((- 2*p 2 + 4*p 3 + 4*p 4 - 12*p 5 + 12*p 7 - 4*p 8 - 4*p 9 + 2*p 10) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_1_6 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 1 6 =
      1568*p 1 - 2986*p 2 + 724*p 3 + 7258*p 4 - 10292*p 5 + 10292*p 7 - 7260*p 8 - 716*p 9 + 2956*p 10 - 1452*p 11 + 406*p 12 - 116*p 13 + 30*p 14 - 8*p 15 + 2*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 4*p 2 + 2*p 4 - 4*p 8 + 8*p 10 - 2*p 12 - 4*p 14 + 2*p 16) * (-10) + ((16*p 2 - 4*p 4 + 2*p 8 - 8*p 10 + 12*p 12 - 8*p 14 + 2*p 16) * (9) + ((8*p 2 - 10*p 4 + 10*p 8 - 8*p 10 + 2*p 12) * (-253) + ((- 4*p 1 + 4*p 3 - 2*p 4 + 2*p 10 - 4*p 11 - 2*p 12 + 8*p 13 - 2*p 14 - 4*p 15 + 2*p 16) * (2) + ((- 4*p 1 + 4*p 3 - 2*p 4 + 2*p 8 - 4*p 9 - 2*p 10 + 8*p 11 - 2*p 12 - 4*p 13 + 2*p 14) * (33) + ((4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 7 - 2*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12) * (427) + ((- 2*p 2 + 4*p 3 + 4*p 4 - 12*p 5 + 12*p 7 - 4*p 8 - 4*p 9 + 2*p 10) * (1000) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_2_0 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 2 0 =
      - 8000*p 2 - 2000*p 4 + 12000*p 6 - 4000*p 8 - 4000*p 10 + 2000*p 12 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 2 - 2*p 4 + 12*p 6 - 4*p 8 - 4*p 10 + 2*p 12) * (1000) + ((8*p 2 - 10*p 4 + 10*p 8 - 8*p 10 + 2*p 12) * (0) + ((8*p 2 + 8*p 4 - 8*p 6 + 2*p 8) * (0) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 4*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12) * (0) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 2*p 8 - 4*p 9 + 2*p 10) * (0) + ((- 4*p 1 + 2*p 2 - 4*p 4 + 8*p 5 - 2*p 6 - 4*p 7 + 2*p 8) * (0) + ((- 8*p 1 - 2*p 2 + 12*p 3 - 4*p 4 - 4*p 5 + 2*p 6) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_2_1 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 2 1 =
      9400*p 2 - 9650*p 4 - 2100*p 6 + 10700*p 8 - 7300*p 10 + 1650*p 12 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 2 - 2*p 4 + 12*p 6 - 4*p 8 - 4*p 10 + 2*p 12) * (-175) + ((8*p 2 - 10*p 4 + 10*p 8 - 8*p 10 + 2*p 12) * (1000) + ((8*p 2 + 8*p 4 - 8*p 6 + 2*p 8) * (0) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 4*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12) * (0) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 2*p 8 - 4*p 9 + 2*p 10) * (0) + ((- 4*p 1 + 2*p 2 - 4*p 4 + 8*p 5 - 2*p 6 - 4*p 7 + 2*p 8) * (0) + ((- 8*p 1 - 2*p 2 + 12*p 3 - 4*p 4 - 4*p 5 + 2*p 6) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_2_2 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 2 2 =
      13200*p 2 + 4608*p 4 - 11108*p 6 + 6946*p 8 - 2092*p 10 + 264*p 12 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 2 - 2*p 4 + 12*p 6 - 4*p 8 - 4*p 10 + 2*p 12) * (-259) + ((8*p 2 - 10*p 4 + 10*p 8 - 8*p 10 + 2*p 12) * (391) + ((8*p 2 + 8*p 4 - 8*p 6 + 2*p 8) * (1000) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 4*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12) * (0) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 2*p 8 - 4*p 9 + 2*p 10) * (0) + ((- 4*p 1 + 2*p 2 - 4*p 4 + 8*p 5 - 2*p 6 - 4*p 7 + 2*p 8) * (0) + ((- 8*p 1 - 2*p 2 + 12*p 3 - 4*p 4 - 4*p 5 + 2*p 6) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_2_3 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 2 3 =
      - 4320*p 2 + 4000*p 3 + 3844*p 4 - 8000*p 5 + 4656*p 6 - 6412*p 8 + 8000*p 9 - 336*p 10 - 4000*p 11 + 1612*p 12 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 2 - 2*p 4 + 12*p 6 - 4*p 8 - 4*p 10 + 2*p 12) * (28) + ((8*p 2 - 10*p 4 + 10*p 8 - 8*p 10 + 2*p 12) * (-222) + ((8*p 2 + 8*p 4 - 8*p 6 + 2*p 8) * (-40) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 4*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12) * (1000) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 2*p 8 - 4*p 9 + 2*p 10) * (0) + ((- 4*p 1 + 2*p 2 - 4*p 4 + 8*p 5 - 2*p 6 - 4*p 7 + 2*p 8) * (0) + ((- 8*p 1 - 2*p 2 + 12*p 3 - 4*p 4 - 4*p 5 + 2*p 6) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_2_4 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 2 4 =
      4000*p 1 + 1680*p 2 - 6720*p 3 + 7048*p 4 - 2560*p 5 - 4448*p 6 + 8000*p 7 - 4176*p 8 - 1440*p 9 + 2768*p 10 - 1280*p 11 + 216*p 12 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 2 - 2*p 4 + 12*p 6 - 4*p 8 - 4*p 10 + 2*p 12) * (-72) + ((8*p 2 - 10*p 4 + 10*p 8 - 8*p 10 + 2*p 12) * (-140) + ((8*p 2 + 8*p 4 - 8*p 6 + 2*p 8) * (108) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 4*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12) * (320) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 2*p 8 - 4*p 9 + 2*p 10) * (1000) + ((- 4*p 1 + 2*p 2 - 4*p 4 + 8*p 5 - 2*p 6 - 4*p 7 + 2*p 8) * (0) + ((- 8*p 1 - 2*p 2 + 12*p 3 - 4*p 4 - 4*p 5 + 2*p 6) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_2_5 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 2 5 =
      - 2596*p 1 + 4036*p 2 - 2708*p 3 - 3448*p 4 + 7800*p 5 - 4392*p 6 - 1192*p 7 + 2488*p 8 - 1204*p 9 + 356*p 10 - 100*p 11 + 16*p 12 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 2 - 2*p 4 + 12*p 6 - 4*p 8 - 4*p 10 + 2*p 12) * (-108) + ((8*p 2 - 10*p 4 + 10*p 8 - 8*p 10 + 2*p 12) * (91) + ((8*p 2 + 8*p 4 - 8*p 6 + 2*p 8) * (-26) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 4*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12) * (25) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 2*p 8 - 4*p 9 + 2*p 10) * (351) + ((- 4*p 1 + 2*p 2 - 4*p 4 + 8*p 5 - 2*p 6 - 4*p 7 + 2*p 8) * (1000) + ((- 8*p 1 - 2*p 2 + 12*p 3 - 4*p 4 - 4*p 5 + 2*p 6) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_2_6 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 2 6 =
      - 9576*p 1 - 2956*p 2 + 11744*p 3 - 7666*p 4 - 600*p 5 + 2926*p 6 - 1444*p 7 + 404*p 8 - 116*p 9 + 30*p 10 - 8*p 11 + 2*p 12 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 2 - 2*p 4 + 12*p 6 - 4*p 8 - 4*p 10 + 2*p 12) * (-10) + ((8*p 2 - 10*p 4 + 10*p 8 - 8*p 10 + 2*p 12) * (9) + ((8*p 2 + 8*p 4 - 8*p 6 + 2*p 8) * (-253) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 4*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12) * (2) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 2*p 8 - 4*p 9 + 2*p 10) * (33) + ((- 4*p 1 + 2*p 2 - 4*p 4 + 8*p 5 - 2*p 6 - 4*p 7 + 2*p 8) * (427) + ((- 8*p 1 - 2*p 2 + 12*p 3 - 4*p 4 - 4*p 5 + 2*p 6) * (1000) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_3_0 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 3 0 =
      4000*p 1 + 2000*p 2 - 8000*p 3 + 4000*p 4 - 4000*p 10 + 8000*p 11 - 4000*p 12 + 2000*p 14 - 4000*p 15 + 2000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 10 + 8*p 11 - 4*p 12 + 2*p 14 - 4*p 15 + 2*p 16) * (1000) + ((- 4*p 1 + 4*p 3 - 2*p 4 + 2*p 10 - 4*p 11 - 2*p 12 + 8*p 13 - 2*p 14 - 4*p 15 + 2*p 16) * (0) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 4*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12) * (0) + ((16*p 1 - 4*p 2 + 2*p 12 - 8*p 13 + 12*p 14 - 8*p 15 + 2*p 16) * (0) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 10 - 8*p 11 + 12*p 12 - 8*p 13 + 2*p 14) * (0) + ((- 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 + 2*p 8 - 8*p 9 + 12*p 10 - 8*p 11 + 2*p 12) * (0) + ((- 2*p 4 + 8*p 5 - 10*p 6 + 10*p 8 - 8*p 9 + 2*p 10) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_3_1 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 3 1 =
      - 4700*p 1 - 350*p 2 + 5400*p 3 - 2700*p 4 + 2700*p 10 - 5400*p 11 - 1300*p 12 + 8000*p 13 - 2350*p 14 - 3300*p 15 + 1650*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 10 + 8*p 11 - 4*p 12 + 2*p 14 - 4*p 15 + 2*p 16) * (-175) + ((- 4*p 1 + 4*p 3 - 2*p 4 + 2*p 10 - 4*p 11 - 2*p 12 + 8*p 13 - 2*p 14 - 4*p 15 + 2*p 16) * (1000) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 4*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12) * (0) + ((16*p 1 - 4*p 2 + 2*p 12 - 8*p 13 + 12*p 14 - 8*p 15 + 2*p 16) * (0) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 10 - 8*p 11 + 12*p 12 - 8*p 13 + 2*p 14) * (0) + ((- 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 + 2*p 8 - 8*p 9 + 12*p 10 - 8*p 11 + 2*p 12) * (0) + ((- 2*p 4 + 8*p 5 - 10*p 6 + 10*p 8 - 8*p 9 + 2*p 10) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_3_2 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 3 2 =
      - 2600*p 1 - 2518*p 2 + 7636*p 3 + 182*p 4 - 8000*p 5 + 4000*p 6 - 4000*p 8 + 8000*p 9 - 182*p 10 - 7636*p 11 + 2254*p 12 + 3128*p 13 - 1300*p 14 - 528*p 15 + 264*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 10 + 8*p 11 - 4*p 12 + 2*p 14 - 4*p 15 + 2*p 16) * (-259) + ((- 4*p 1 + 4*p 3 - 2*p 4 + 2*p 10 - 4*p 11 - 2*p 12 + 8*p 13 - 2*p 14 - 4*p 15 + 2*p 16) * (391) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 4*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12) * (1000) + ((16*p 1 - 4*p 2 + 2*p 12 - 8*p 13 + 12*p 14 - 8*p 15 + 2*p 16) * (0) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 10 - 8*p 11 + 12*p 12 - 8*p 13 + 2*p 14) * (0) + ((- 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 + 2*p 8 - 8*p 9 + 12*p 10 - 8*p 11 + 2*p 12) * (0) + ((- 2*p 4 + 8*p 5 - 10*p 6 + 10*p 8 - 8*p 9 + 2*p 10) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_3_3 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 3 3 =
      17000*p 1 - 3864*p 2 - 1272*p 3 + 476*p 4 + 320*p 5 - 160*p 6 + 160*p 8 - 320*p 9 - 476*p 10 + 1272*p 11 + 2252*p 12 - 9776*p 13 + 12500*p 14 - 7224*p 15 + 1612*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 10 + 8*p 11 - 4*p 12 + 2*p 14 - 4*p 15 + 2*p 16) * (28) + ((- 4*p 1 + 4*p 3 - 2*p 4 + 2*p 10 - 4*p 11 - 2*p 12 + 8*p 13 - 2*p 14 - 4*p 15 + 2*p 16) * (-222) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 4*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12) * (-40) + ((16*p 1 - 4*p 2 + 2*p 12 - 8*p 13 + 12*p 14 - 8*p 15 + 2*p 16) * (1000) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 10 - 8*p 11 + 12*p 12 - 8*p 13 + 2*p 14) * (0) + ((- 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 + 2*p 8 - 8*p 9 + 12*p 10 - 8*p 11 + 2*p 12) * (0) + ((- 2*p 4 + 8*p 5 - 10*p 6 + 10*p 8 - 8*p 9 + 2*p 10) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_3_4 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 3 4 =
      13392*p 1 - 13640*p 2 + 8448*p 3 - 1792*p 4 - 864*p 5 + 432*p 6 - 432*p 8 + 864*p 9 + 1792*p 10 - 8448*p 11 + 13424*p 12 - 11680*p 13 + 5976*p 14 - 1712*p 15 + 216*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 10 + 8*p 11 - 4*p 12 + 2*p 14 - 4*p 15 + 2*p 16) * (-72) + ((- 4*p 1 + 4*p 3 - 2*p 4 + 2*p 10 - 4*p 11 - 2*p 12 + 8*p 13 - 2*p 14 - 4*p 15 + 2*p 16) * (-140) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 4*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12) * (108) + ((16*p 1 - 4*p 2 + 2*p 12 - 8*p 13 + 12*p 14 - 8*p 15 + 2*p 16) * (320) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 10 - 8*p 11 + 12*p 12 - 8*p 13 + 2*p 14) * (1000) + ((- 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 + 2*p 8 - 8*p 9 + 12*p 10 - 8*p 11 + 2*p 12) * (0) + ((- 2*p 4 + 8*p 5 - 10*p 6 + 10*p 8 - 8*p 9 + 2*p 10) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_3_5 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 3 5 =
      2412*p 1 - 6476*p 2 + 11932*p 3 - 13368*p 4 + 8208*p 5 - 2104*p 6 + 2104*p 8 - 8208*p 9 + 13368*p 10 - 11932*p 11 + 6460*p 12 - 2280*p 13 + 604*p 14 - 132*p 15 + 16*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 10 + 8*p 11 - 4*p 12 + 2*p 14 - 4*p 15 + 2*p 16) * (-108) + ((- 4*p 1 + 4*p 3 - 2*p 4 + 2*p 10 - 4*p 11 - 2*p 12 + 8*p 13 - 2*p 14 - 4*p 15 + 2*p 16) * (91) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 4*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12) * (-26) + ((16*p 1 - 4*p 2 + 2*p 12 - 8*p 13 + 12*p 14 - 8*p 15 + 2*p 16) * (25) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 10 - 8*p 11 + 12*p 12 - 8*p 13 + 2*p 14) * (351) + ((- 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 + 2*p 8 - 8*p 9 + 12*p 10 - 8*p 11 + 2*p 12) * (1000) + ((- 2*p 4 + 8*p 5 - 10*p 6 + 10*p 8 - 8*p 9 + 2*p 10) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_3_6 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 3 6 =
      220*p 1 - 772*p 2 + 2784*p 3 - 7754*p 4 + 13440*p 5 - 11866*p 6 + 11866*p 8 - 13440*p 9 + 7754*p 10 - 2784*p 11 + 770*p 12 - 208*p 13 + 52*p 14 - 12*p 15 + 2*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 10 + 8*p 11 - 4*p 12 + 2*p 14 - 4*p 15 + 2*p 16) * (-10) + ((- 4*p 1 + 4*p 3 - 2*p 4 + 2*p 10 - 4*p 11 - 2*p 12 + 8*p 13 - 2*p 14 - 4*p 15 + 2*p 16) * (9) + ((- 2*p 2 + 4*p 3 + 2*p 4 - 8*p 5 + 4*p 6 - 4*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12) * (-253) + ((16*p 1 - 4*p 2 + 2*p 12 - 8*p 13 + 12*p 14 - 8*p 15 + 2*p 16) * (2) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 10 - 8*p 11 + 12*p 12 - 8*p 13 + 2*p 14) * (33) + ((- 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 + 2*p 8 - 8*p 9 + 12*p 10 - 8*p 11 + 2*p 12) * (427) + ((- 2*p 4 + 8*p 5 - 10*p 6 + 10*p 8 - 8*p 9 + 2*p 10) * (1000) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_4_0 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 4 0 =
      - 8000*p 1 + 2000*p 2 + 4000*p 3 - 2000*p 4 - 4000*p 8 + 8000*p 9 - 4000*p 10 + 2000*p 12 - 4000*p 13 + 2000*p 14 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 1 + 2*p 2 + 4*p 3 - 2*p 4 - 4*p 8 + 8*p 9 - 4*p 10 + 2*p 12 - 4*p 13 + 2*p 14) * (1000) + ((- 4*p 1 + 4*p 3 - 2*p 4 + 2*p 8 - 4*p 9 - 2*p 10 + 8*p 11 - 2*p 12 - 4*p 13 + 2*p 14) * (0) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 2*p 8 - 4*p 9 + 2*p 10) * (0) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 10 - 8*p 11 + 12*p 12 - 8*p 13 + 2*p 14) * (0) + ((16*p 1 - 4*p 2 + 2*p 8 - 8*p 9 + 12*p 10 - 8*p 11 + 2*p 12) * (0) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 6 - 8*p 7 + 12*p 8 - 8*p 9 + 2*p 10) * (0) + ((- 2*p 2 + 8*p 3 - 10*p 4 + 10*p 6 - 8*p 7 + 2*p 8) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_4_1 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 4 1 =
      - 2600*p 1 - 350*p 2 + 3300*p 3 - 1650*p 4 + 2700*p 8 - 5400*p 9 - 1300*p 10 + 8000*p 11 - 2350*p 12 - 3300*p 13 + 1650*p 14 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 1 + 2*p 2 + 4*p 3 - 2*p 4 - 4*p 8 + 8*p 9 - 4*p 10 + 2*p 12 - 4*p 13 + 2*p 14) * (-175) + ((- 4*p 1 + 4*p 3 - 2*p 4 + 2*p 8 - 4*p 9 - 2*p 10 + 8*p 11 - 2*p 12 - 4*p 13 + 2*p 14) * (1000) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 2*p 8 - 4*p 9 + 2*p 10) * (0) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 10 - 8*p 11 + 12*p 12 - 8*p 13 + 2*p 14) * (0) + ((16*p 1 - 4*p 2 + 2*p 8 - 8*p 9 + 12*p 10 - 8*p 11 + 2*p 12) * (0) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 6 - 8*p 7 + 12*p 8 - 8*p 9 + 2*p 10) * (0) + ((- 2*p 2 + 8*p 3 - 10*p 4 + 10*p 6 - 8*p 7 + 2*p 8) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_4_2 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 4 2 =
      4508*p 1 + 1482*p 2 - 7472*p 3 + 3736*p 4 - 4000*p 6 + 8000*p 7 - 182*p 8 - 7636*p 9 + 2254*p 10 + 3128*p 11 - 1300*p 12 - 528*p 13 + 264*p 14 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 1 + 2*p 2 + 4*p 3 - 2*p 4 - 4*p 8 + 8*p 9 - 4*p 10 + 2*p 12 - 4*p 13 + 2*p 14) * (-259) + ((- 4*p 1 + 4*p 3 - 2*p 4 + 2*p 8 - 4*p 9 - 2*p 10 + 8*p 11 - 2*p 12 - 4*p 13 + 2*p 14) * (391) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 2*p 8 - 4*p 9 + 2*p 10) * (1000) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 10 - 8*p 11 + 12*p 12 - 8*p 13 + 2*p 14) * (0) + ((16*p 1 - 4*p 2 + 2*p 8 - 8*p 9 + 12*p 10 - 8*p 11 + 2*p 12) * (0) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 6 - 8*p 7 + 12*p 8 - 8*p 9 + 2*p 10) * (0) + ((- 2*p 2 + 8*p 3 - 10*p 4 + 10*p 6 - 8*p 7 + 2*p 8) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_4_3 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 4 3 =
      8504*p 1 - 12024*p 2 + 7544*p 3 - 1772*p 4 + 160*p 6 - 320*p 7 - 476*p 8 + 1272*p 9 + 2252*p 10 - 9776*p 11 + 12500*p 12 - 7224*p 13 + 1612*p 14 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 1 + 2*p 2 + 4*p 3 - 2*p 4 - 4*p 8 + 8*p 9 - 4*p 10 + 2*p 12 - 4*p 13 + 2*p 14) * (28) + ((- 4*p 1 + 4*p 3 - 2*p 4 + 2*p 8 - 4*p 9 - 2*p 10 + 8*p 11 - 2*p 12 - 4*p 13 + 2*p 14) * (-222) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 2*p 8 - 4*p 9 + 2*p 10) * (-40) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 10 - 8*p 11 + 12*p 12 - 8*p 13 + 2*p 14) * (1000) + ((16*p 1 - 4*p 2 + 2*p 8 - 8*p 9 + 12*p 10 - 8*p 11 + 2*p 12) * (0) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 6 - 8*p 7 + 12*p 8 - 8*p 9 + 2*p 10) * (0) + ((- 2*p 2 + 8*p 3 - 10*p 4 + 10*p 6 - 8*p 7 + 2*p 8) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_4_4 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 4 4 =
      20128*p 1 - 7768*p 2 + 848*p 3 + 216*p 4 - 432*p 6 + 864*p 7 + 1792*p 8 - 8448*p 9 + 13424*p 10 - 11680*p 11 + 5976*p 12 - 1712*p 13 + 216*p 14 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 1 + 2*p 2 + 4*p 3 - 2*p 4 - 4*p 8 + 8*p 9 - 4*p 10 + 2*p 12 - 4*p 13 + 2*p 14) * (-72) + ((- 4*p 1 + 4*p 3 - 2*p 4 + 2*p 8 - 4*p 9 - 2*p 10 + 8*p 11 - 2*p 12 - 4*p 13 + 2*p 14) * (-140) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 2*p 8 - 4*p 9 + 2*p 10) * (108) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 10 - 8*p 11 + 12*p 12 - 8*p 13 + 2*p 14) * (320) + ((16*p 1 - 4*p 2 + 2*p 8 - 8*p 9 + 12*p 10 - 8*p 11 + 2*p 12) * (1000) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 6 - 8*p 7 + 12*p 8 - 8*p 9 + 2*p 10) * (0) + ((- 2*p 2 + 8*p 3 - 10*p 4 + 10*p 6 - 8*p 7 + 2*p 8) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_4_5 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 4 5 =
      14212*p 1 - 13972*p 2 + 8340*p 3 - 2120*p 4 + 2104*p 6 - 8208*p 7 + 13368*p 8 - 11932*p 9 + 6460*p 10 - 2280*p 11 + 604*p 12 - 132*p 13 + 16*p 14 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 1 + 2*p 2 + 4*p 3 - 2*p 4 - 4*p 8 + 8*p 9 - 4*p 10 + 2*p 12 - 4*p 13 + 2*p 14) * (-108) + ((- 4*p 1 + 4*p 3 - 2*p 4 + 2*p 8 - 4*p 9 - 2*p 10 + 8*p 11 - 2*p 12 - 4*p 13 + 2*p 14) * (91) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 2*p 8 - 4*p 9 + 2*p 10) * (-26) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 10 - 8*p 11 + 12*p 12 - 8*p 13 + 2*p 14) * (25) + ((16*p 1 - 4*p 2 + 2*p 8 - 8*p 9 + 12*p 10 - 8*p 11 + 2*p 12) * (351) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 6 - 8*p 7 + 12*p 8 - 8*p 9 + 2*p 10) * (1000) + ((- 2*p 2 + 8*p 3 - 10*p 4 + 10*p 6 - 8*p 7 + 2*p 8) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_4_6 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 4 6 =
      2992*p 1 - 7806*p 2 + 13452*p 3 - 11868*p 4 + 11866*p 6 - 13440*p 7 + 7754*p 8 - 2784*p 9 + 770*p 10 - 208*p 11 + 52*p 12 - 12*p 13 + 2*p 14 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 1 + 2*p 2 + 4*p 3 - 2*p 4 - 4*p 8 + 8*p 9 - 4*p 10 + 2*p 12 - 4*p 13 + 2*p 14) * (-10) + ((- 4*p 1 + 4*p 3 - 2*p 4 + 2*p 8 - 4*p 9 - 2*p 10 + 8*p 11 - 2*p 12 - 4*p 13 + 2*p 14) * (9) + ((4*p 1 + 2*p 2 - 8*p 3 + 4*p 4 - 4*p 6 + 8*p 7 - 2*p 8 - 4*p 9 + 2*p 10) * (-253) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 10 - 8*p 11 + 12*p 12 - 8*p 13 + 2*p 14) * (2) + ((16*p 1 - 4*p 2 + 2*p 8 - 8*p 9 + 12*p 10 - 8*p 11 + 2*p 12) * (33) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 6 - 8*p 7 + 12*p 8 - 8*p 9 + 2*p 10) * (427) + ((- 2*p 2 + 8*p 3 - 10*p 4 + 10*p 6 - 8*p 7 + 2*p 8) * (1000) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_5_0 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 5 0 =
      - 8000*p 1 + 4000*p 2 - 2000*p 4 + 4000*p 5 - 6000*p 6 + 8000*p 7 - 4000*p 8 + 2000*p 10 - 4000*p 11 + 2000*p 12 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 1 + 4*p 2 - 2*p 4 + 4*p 5 - 6*p 6 + 8*p 7 - 4*p 8 + 2*p 10 - 4*p 11 + 2*p 12) * (1000) + ((4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 7 - 2*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12) * (0) + ((- 4*p 1 + 2*p 2 - 4*p 4 + 8*p 5 - 2*p 6 - 4*p 7 + 2*p 8) * (0) + ((- 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 + 2*p 8 - 8*p 9 + 12*p 10 - 8*p 11 + 2*p 12) * (0) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 6 - 8*p 7 + 12*p 8 - 8*p 9 + 2*p 10) * (0) + ((16*p 1 - 4*p 2 + 2*p 4 - 8*p 5 + 12*p 6 - 8*p 7 + 2*p 8) * (0) + ((8*p 1 - 10*p 2 + 10*p 4 - 8*p 5 + 2*p 6) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_5_1 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 5 1 =
      5400*p 1 + 1300*p 2 - 8000*p 3 + 2350*p 4 + 3300*p 5 + 1050*p 6 - 5400*p 7 - 1300*p 8 + 8000*p 9 - 2350*p 10 - 3300*p 11 + 1650*p 12 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 1 + 4*p 2 - 2*p 4 + 4*p 5 - 6*p 6 + 8*p 7 - 4*p 8 + 2*p 10 - 4*p 11 + 2*p 12) * (-175) + ((4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 7 - 2*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12) * (1000) + ((- 4*p 1 + 2*p 2 - 4*p 4 + 8*p 5 - 2*p 6 - 4*p 7 + 2*p 8) * (0) + ((- 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 + 2*p 8 - 8*p 9 + 12*p 10 - 8*p 11 + 2*p 12) * (0) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 6 - 8*p 7 + 12*p 8 - 8*p 9 + 2*p 10) * (0) + ((16*p 1 - 4*p 2 + 2*p 4 - 8*p 5 + 12*p 6 - 8*p 7 + 2*p 8) * (0) + ((8*p 1 - 10*p 2 + 10*p 4 - 8*p 5 + 2*p 6) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_5_2 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 5 2 =
      - 364*p 1 + 1746*p 2 - 3128*p 3 - 2700*p 4 + 8528*p 5 - 446*p 6 - 7636*p 7 + 2254*p 8 + 3128*p 9 - 1300*p 10 - 528*p 11 + 264*p 12 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 1 + 4*p 2 - 2*p 4 + 4*p 5 - 6*p 6 + 8*p 7 - 4*p 8 + 2*p 10 - 4*p 11 + 2*p 12) * (-259) + ((4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 7 - 2*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12) * (391) + ((- 4*p 1 + 2*p 2 - 4*p 4 + 8*p 5 - 2*p 6 - 4*p 7 + 2*p 8) * (1000) + ((- 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 + 2*p 8 - 8*p 9 + 12*p 10 - 8*p 11 + 2*p 12) * (0) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 6 - 8*p 7 + 12*p 8 - 8*p 9 + 2*p 10) * (0) + ((16*p 1 - 4*p 2 + 2*p 4 - 8*p 5 + 12*p 6 - 8*p 7 + 2*p 8) * (0) + ((8*p 1 - 10*p 2 + 10*p 4 - 8*p 5 + 2*p 6) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_5_3 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 5 3 =
      - 952*p 1 - 2412*p 2 + 9776*p 3 - 12340*p 4 + 6904*p 5 - 2088*p 6 + 1272*p 7 + 2252*p 8 - 9776*p 9 + 12500*p 10 - 7224*p 11 + 1612*p 12 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 1 + 4*p 2 - 2*p 4 + 4*p 5 - 6*p 6 + 8*p 7 - 4*p 8 + 2*p 10 - 4*p 11 + 2*p 12) * (28) + ((4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 7 - 2*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12) * (-222) + ((- 4*p 1 + 2*p 2 - 4*p 4 + 8*p 5 - 2*p 6 - 4*p 7 + 2*p 8) * (-40) + ((- 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 + 2*p 8 - 8*p 9 + 12*p 10 - 8*p 11 + 2*p 12) * (1000) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 6 - 8*p 7 + 12*p 8 - 8*p 9 + 2*p 10) * (0) + ((16*p 1 - 4*p 2 + 2*p 4 - 8*p 5 + 12*p 6 - 8*p 7 + 2*p 8) * (0) + ((8*p 1 - 10*p 2 + 10*p 4 - 8*p 5 + 2*p 6) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_5_4 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 5 4 =
      7584*p 1 - 12992*p 2 + 11680*p 3 - 6408*p 4 + 2576*p 5 + 1576*p 6 - 8448*p 7 + 13424*p 8 - 11680*p 9 + 5976*p 10 - 1712*p 11 + 216*p 12 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 1 + 4*p 2 - 2*p 4 + 4*p 5 - 6*p 6 + 8*p 7 - 4*p 8 + 2*p 10 - 4*p 11 + 2*p 12) * (-72) + ((4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 7 - 2*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12) * (-140) + ((- 4*p 1 + 2*p 2 - 4*p 4 + 8*p 5 - 2*p 6 - 4*p 7 + 2*p 8) * (108) + ((- 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 + 2*p 8 - 8*p 9 + 12*p 10 - 8*p 11 + 2*p 12) * (320) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 6 - 8*p 7 + 12*p 8 - 8*p 9 + 2*p 10) * (1000) + ((16*p 1 - 4*p 2 + 2*p 4 - 8*p 5 + 12*p 6 - 8*p 7 + 2*p 8) * (0) + ((8*p 1 - 10*p 2 + 10*p 4 - 8*p 5 + 2*p 6) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_5_5 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 5 5 =
      20140*p 1 - 8564*p 2 + 2280*p 3 + 1500*p 4 - 8076*p 5 + 13352*p 6 - 11932*p 7 + 6460*p 8 - 2280*p 9 + 604*p 10 - 132*p 11 + 16*p 12 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 1 + 4*p 2 - 2*p 4 + 4*p 5 - 6*p 6 + 8*p 7 - 4*p 8 + 2*p 10 - 4*p 11 + 2*p 12) * (-108) + ((4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 7 - 2*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12) * (91) + ((- 4*p 1 + 2*p 2 - 4*p 4 + 8*p 5 - 2*p 6 - 4*p 7 + 2*p 8) * (-26) + ((- 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 + 2*p 8 - 8*p 9 + 12*p 10 - 8*p 11 + 2*p 12) * (25) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 6 - 8*p 7 + 12*p 8 - 8*p 9 + 2*p 10) * (351) + ((16*p 1 - 4*p 2 + 2*p 4 - 8*p 5 + 12*p 6 - 8*p 7 + 2*p 8) * (1000) + ((8*p 1 - 10*p 2 + 10*p 4 - 8*p 5 + 2*p 6) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_5_6 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 5 6 =
      16224*p 1 - 12636*p 2 + 208*p 3 + 11814*p 4 - 13428*p 5 + 7752*p 6 - 2784*p 7 + 770*p 8 - 208*p 9 + 52*p 10 - 12*p 11 + 2*p 12 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (- 8*p 1 + 4*p 2 - 2*p 4 + 4*p 5 - 6*p 6 + 8*p 7 - 4*p 8 + 2*p 10 - 4*p 11 + 2*p 12) * (-10) + ((4*p 1 + 2*p 2 - 8*p 3 + 2*p 4 + 4*p 5 - 4*p 7 - 2*p 8 + 8*p 9 - 2*p 10 - 4*p 11 + 2*p 12) * (9) + ((- 4*p 1 + 2*p 2 - 4*p 4 + 8*p 5 - 2*p 6 - 4*p 7 + 2*p 8) * (-253) + ((- 2*p 2 + 8*p 3 - 12*p 4 + 8*p 5 - 2*p 6 + 2*p 8 - 8*p 9 + 12*p 10 - 8*p 11 + 2*p 12) * (2) + ((8*p 1 - 12*p 2 + 8*p 3 - 2*p 4 + 2*p 6 - 8*p 7 + 12*p 8 - 8*p 9 + 2*p 10) * (33) + ((16*p 1 - 4*p 2 + 2*p 4 - 8*p 5 + 12*p 6 - 8*p 7 + 2*p 8) * (427) + ((8*p 1 - 10*p 2 + 10*p 4 - 8*p 5 + 2*p 6) * (1000) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_6_0 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 6 0 =
      4000*p 2 - 8000*p 3 + 8000*p 5 - 6000*p 6 + 4000*p 7 - 4000*p 9 + 2000*p 10 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 2 - 8*p 3 + 8*p 5 - 6*p 6 + 4*p 7 - 4*p 9 + 2*p 10) * (1000) + ((- 2*p 2 + 4*p 3 + 4*p 4 - 12*p 5 + 12*p 7 - 4*p 8 - 4*p 9 + 2*p 10) * (0) + ((- 8*p 1 - 2*p 2 + 12*p 3 - 4*p 4 - 4*p 5 + 2*p 6) * (0) + ((- 2*p 4 + 8*p 5 - 10*p 6 + 10*p 8 - 8*p 9 + 2*p 10) * (0) + ((- 2*p 2 + 8*p 3 - 10*p 4 + 10*p 6 - 8*p 7 + 2*p 8) * (0) + ((8*p 1 - 10*p 2 + 10*p 4 - 8*p 5 + 2*p 6) * (0) + ((8*p 1 + 8*p 2 - 8*p 3 + 2*p 4) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_6_1 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 6 1 =
      - 2700*p 2 + 5400*p 3 + 4000*p 4 - 13400*p 5 + 1050*p 6 + 11300*p 7 - 4000*p 8 - 3300*p 9 + 1650*p 10 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 2 - 8*p 3 + 8*p 5 - 6*p 6 + 4*p 7 - 4*p 9 + 2*p 10) * (-175) + ((- 2*p 2 + 4*p 3 + 4*p 4 - 12*p 5 + 12*p 7 - 4*p 8 - 4*p 9 + 2*p 10) * (1000) + ((- 8*p 1 - 2*p 2 + 12*p 3 - 4*p 4 - 4*p 5 + 2*p 6) * (0) + ((- 2*p 4 + 8*p 5 - 10*p 6 + 10*p 8 - 8*p 9 + 2*p 10) * (0) + ((- 2*p 2 + 8*p 3 - 10*p 4 + 10*p 6 - 8*p 7 + 2*p 8) * (0) + ((8*p 1 - 10*p 2 + 10*p 4 - 8*p 5 + 2*p 6) * (0) + ((8*p 1 + 8*p 2 - 8*p 3 + 2*p 4) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_6_2 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 6 2 =
      - 8000*p 1 - 3818*p 2 + 15636*p 3 - 2436*p 4 - 10764*p 5 + 3554*p 6 + 3656*p 7 - 1564*p 8 - 528*p 9 + 264*p 10 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 2 - 8*p 3 + 8*p 5 - 6*p 6 + 4*p 7 - 4*p 9 + 2*p 10) * (-259) + ((- 2*p 2 + 4*p 3 + 4*p 4 - 12*p 5 + 12*p 7 - 4*p 8 - 4*p 9 + 2*p 10) * (391) + ((- 8*p 1 - 2*p 2 + 12*p 3 - 4*p 4 - 4*p 5 + 2*p 6) * (1000) + ((- 2*p 4 + 8*p 5 - 10*p 6 + 10*p 8 - 8*p 9 + 2*p 10) * (0) + ((- 2*p 2 + 8*p 3 - 10*p 4 + 10*p 6 - 8*p 7 + 2*p 8) * (0) + ((8*p 1 - 10*p 2 + 10*p 4 - 8*p 5 + 2*p 6) * (0) + ((8*p 1 + 8*p 2 - 8*p 3 + 2*p 4) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_6_3 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 6 3 =
      320*p 1 + 636*p 2 - 1592*p 3 - 2728*p 4 + 11048*p 5 - 10248*p 6 - 2552*p 7 + 10888*p 8 - 7224*p 9 + 1612*p 10 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 2 - 8*p 3 + 8*p 5 - 6*p 6 + 4*p 7 - 4*p 9 + 2*p 10) * (28) + ((- 2*p 2 + 4*p 3 + 4*p 4 - 12*p 5 + 12*p 7 - 4*p 8 - 4*p 9 + 2*p 10) * (-222) + ((- 8*p 1 - 2*p 2 + 12*p 3 - 4*p 4 - 4*p 5 + 2*p 6) * (-40) + ((- 2*p 4 + 8*p 5 - 10*p 6 + 10*p 8 - 8*p 9 + 2*p 10) * (1000) + ((- 2*p 2 + 8*p 3 - 10*p 4 + 10*p 6 - 8*p 7 + 2*p 8) * (0) + ((8*p 1 - 10*p 2 + 10*p 4 - 8*p 5 + 2*p 6) * (0) + ((8*p 1 + 8*p 2 - 8*p 3 + 2*p 4) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_6_4 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 6 4 =
      - 864*p 1 - 2224*p 2 + 9312*p 3 - 11632*p 4 + 3232*p 5 + 7448*p 6 - 9968*p 7 + 5760*p 8 - 1712*p 9 + 216*p 10 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 2 - 8*p 3 + 8*p 5 - 6*p 6 + 4*p 7 - 4*p 9 + 2*p 10) * (-72) + ((- 2*p 2 + 4*p 3 + 4*p 4 - 12*p 5 + 12*p 7 - 4*p 8 - 4*p 9 + 2*p 10) * (-140) + ((- 8*p 1 - 2*p 2 + 12*p 3 - 4*p 4 - 4*p 5 + 2*p 6) * (108) + ((- 2*p 4 + 8*p 5 - 10*p 6 + 10*p 8 - 8*p 9 + 2*p 10) * (320) + ((- 2*p 2 + 8*p 3 - 10*p 4 + 10*p 6 - 8*p 7 + 2*p 8) * (1000) + ((8*p 1 - 10*p 2 + 10*p 4 - 8*p 5 + 2*p 6) * (0) + ((8*p 1 + 8*p 2 - 8*p 3 + 2*p 4) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_6_5 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 6 5 =
      8208*p 1 - 11264*p 2 + 3724*p 3 + 6908*p 4 - 9652*p 5 + 5856*p 6 - 2148*p 7 + 588*p 8 - 132*p 9 + 16*p 10 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 2 - 8*p 3 + 8*p 5 - 6*p 6 + 4*p 7 - 4*p 9 + 2*p 10) * (-108) + ((- 2*p 2 + 4*p 3 + 4*p 4 - 12*p 5 + 12*p 7 - 4*p 8 - 4*p 9 + 2*p 10) * (91) + ((- 8*p 1 - 2*p 2 + 12*p 3 - 4*p 4 - 4*p 5 + 2*p 6) * (-26) + ((- 2*p 4 + 8*p 5 - 10*p 6 + 10*p 8 - 8*p 9 + 2*p 10) * (25) + ((- 2*p 2 + 8*p 3 - 10*p 4 + 10*p 6 - 8*p 7 + 2*p 8) * (351) + ((8*p 1 - 10*p 2 + 10*p 4 - 8*p 5 + 2*p 6) * (1000) + ((8*p 1 + 8*p 2 - 8*p 3 + 2*p 4) * (0) + (0))))))) = _
  ring

theorem fourthLevelEvenRightEntry_6_6 (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 6 6 =
      13440*p 1 + 4112*p 2 - 10656*p 3 + 6984*p 4 - 2576*p 5 + 718*p 6 - 196*p 7 + 50*p 8 - 12*p 9 + 2*p 10 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (4*p 2 - 8*p 3 + 8*p 5 - 6*p 6 + 4*p 7 - 4*p 9 + 2*p 10) * (-10) + ((- 2*p 2 + 4*p 3 + 4*p 4 - 12*p 5 + 12*p 7 - 4*p 8 - 4*p 9 + 2*p 10) * (9) + ((- 8*p 1 - 2*p 2 + 12*p 3 - 4*p 4 - 4*p 5 + 2*p 6) * (-253) + ((- 2*p 4 + 8*p 5 - 10*p 6 + 10*p 8 - 8*p 9 + 2*p 10) * (2) + ((- 2*p 2 + 8*p 3 - 10*p 4 + 10*p 6 - 8*p 7 + 2*p 8) * (33) + ((8*p 1 - 10*p 2 + 10*p 4 - 8*p 5 + 2*p 6) * (427) + ((8*p 1 + 8*p 2 - 8*p 3 + 2*p 4) * (1000) + (0))))))) = _
  ring

def fourthLevelEvenRightPolynomial (p : Fin 17 → ℝ) : Matrix (Fin 7) (Fin 7) ℝ :=
  ![![8000*p 4 + 8000*p 8 - 8000*p 12 + 2000*p 16,
    - 4000*p 2 + 600*p 4 - 5400*p 8 + 8000*p 10 - 600*p 12 - 4000*p 14 + 1650*p 16,
    - 9564*p 2 - 3290*p 4 + 12000*p 6 - 7636*p 8 - 872*p 10 + 3290*p 12 - 1564*p 14 + 264*p 16,
    4000*p 1 + 3208*p 2 - 8000*p 3 + 3860*p 4 - 480*p 6 + 1272*p 8 - 5616*p 10 + 8000*p 11 - 3860*p 12 + 2888*p 14 - 4000*p 15 + 1612*p 16,
    - 6720*p 1 + 2336*p 2 + 1440*p 3 - 1792*p 4 + 1296*p 6 - 4448*p 8 + 8000*p 9 - 6832*p 10 + 2560*p 11 + 1792*p 12 - 4000*p 13 + 3200*p 14 - 1280*p 15 + 216*p 16,
    - 10708*p 1 + 4596*p 2 + 1204*p 3 - 3232*p 4 + 4000*p 5 - 6312*p 6 + 8000*p 7 - 6528*p 8 + 2808*p 9 + 1328*p 10 - 3800*p 11 + 3232*p 12 - 1404*p 13 + 388*p 14 - 100*p 15 + 16*p 16,
    - 3672*p 1 + 7766*p 2 - 7884*p 3 - 468*p 4 + 9708*p 5 - 11598*p 6 + 7416*p 7 - 944*p 8 - 3736*p 9 + 3798*p 10 - 1692*p 11 + 468*p 12 - 132*p 13 + 34*p 14 - 8*p 15 + 2*p 16],
  ![- 4000*p 2 + 2000*p 4 - 4000*p 8 + 8000*p 10 - 2000*p 12 - 4000*p 14 + 2000*p 16,
    16700*p 2 - 4350*p 4 + 2700*p 8 - 9400*p 10 + 12350*p 12 - 7300*p 14 + 1650*p 16,
    15292*p 2 - 12082*p 4 + 11818*p 8 - 13200*p 10 + 7210*p 12 - 2092*p 14 + 264*p 16,
    - 4000*p 1 - 3984*p 2 + 4000*p 3 - 656*p 4 - 956*p 8 + 4320*p 10 - 4000*p 11 - 4800*p 12 + 8000*p 13 - 336*p 14 - 4000*p 15 + 1612*p 16,
    - 5280*p 1 - 1088*p 2 + 5280*p 3 - 3304*p 4 + 3088*p 8 - 4000*p 9 - 1680*p 10 + 6720*p 11 - 3960*p 12 - 1440*p 13 + 2768*p 14 - 1280*p 15 + 216*p 16,
    2496*p 1 + 3680*p 2 - 6496*p 3 + 928*p 4 + 4000*p 5 - 4000*p 7 - 944*p 8 + 6596*p 9 - 4036*p 10 - 1292*p 11 + 2504*p 12 - 1204*p 13 + 356*p 14 - 100*p 15 + 16*p 16,
    1568*p 1 - 2986*p 2 + 724*p 3 + 7258*p 4 - 10292*p 5 + 10292*p 7 - 7260*p 8 - 716*p 9 + 2956*p 10 - 1452*p 11 + 406*p 12 - 116*p 13 + 30*p 14 - 8*p 15 + 2*p 16],
  ![- 8000*p 2 - 2000*p 4 + 12000*p 6 - 4000*p 8 - 4000*p 10 + 2000*p 12,
    9400*p 2 - 9650*p 4 - 2100*p 6 + 10700*p 8 - 7300*p 10 + 1650*p 12,
    13200*p 2 + 4608*p 4 - 11108*p 6 + 6946*p 8 - 2092*p 10 + 264*p 12,
    - 4320*p 2 + 4000*p 3 + 3844*p 4 - 8000*p 5 + 4656*p 6 - 6412*p 8 + 8000*p 9 - 336*p 10 - 4000*p 11 + 1612*p 12,
    4000*p 1 + 1680*p 2 - 6720*p 3 + 7048*p 4 - 2560*p 5 - 4448*p 6 + 8000*p 7 - 4176*p 8 - 1440*p 9 + 2768*p 10 - 1280*p 11 + 216*p 12,
    - 2596*p 1 + 4036*p 2 - 2708*p 3 - 3448*p 4 + 7800*p 5 - 4392*p 6 - 1192*p 7 + 2488*p 8 - 1204*p 9 + 356*p 10 - 100*p 11 + 16*p 12,
    - 9576*p 1 - 2956*p 2 + 11744*p 3 - 7666*p 4 - 600*p 5 + 2926*p 6 - 1444*p 7 + 404*p 8 - 116*p 9 + 30*p 10 - 8*p 11 + 2*p 12],
  ![4000*p 1 + 2000*p 2 - 8000*p 3 + 4000*p 4 - 4000*p 10 + 8000*p 11 - 4000*p 12 + 2000*p 14 - 4000*p 15 + 2000*p 16,
    - 4700*p 1 - 350*p 2 + 5400*p 3 - 2700*p 4 + 2700*p 10 - 5400*p 11 - 1300*p 12 + 8000*p 13 - 2350*p 14 - 3300*p 15 + 1650*p 16,
    - 2600*p 1 - 2518*p 2 + 7636*p 3 + 182*p 4 - 8000*p 5 + 4000*p 6 - 4000*p 8 + 8000*p 9 - 182*p 10 - 7636*p 11 + 2254*p 12 + 3128*p 13 - 1300*p 14 - 528*p 15 + 264*p 16,
    17000*p 1 - 3864*p 2 - 1272*p 3 + 476*p 4 + 320*p 5 - 160*p 6 + 160*p 8 - 320*p 9 - 476*p 10 + 1272*p 11 + 2252*p 12 - 9776*p 13 + 12500*p 14 - 7224*p 15 + 1612*p 16,
    13392*p 1 - 13640*p 2 + 8448*p 3 - 1792*p 4 - 864*p 5 + 432*p 6 - 432*p 8 + 864*p 9 + 1792*p 10 - 8448*p 11 + 13424*p 12 - 11680*p 13 + 5976*p 14 - 1712*p 15 + 216*p 16,
    2412*p 1 - 6476*p 2 + 11932*p 3 - 13368*p 4 + 8208*p 5 - 2104*p 6 + 2104*p 8 - 8208*p 9 + 13368*p 10 - 11932*p 11 + 6460*p 12 - 2280*p 13 + 604*p 14 - 132*p 15 + 16*p 16,
    220*p 1 - 772*p 2 + 2784*p 3 - 7754*p 4 + 13440*p 5 - 11866*p 6 + 11866*p 8 - 13440*p 9 + 7754*p 10 - 2784*p 11 + 770*p 12 - 208*p 13 + 52*p 14 - 12*p 15 + 2*p 16],
  ![- 8000*p 1 + 2000*p 2 + 4000*p 3 - 2000*p 4 - 4000*p 8 + 8000*p 9 - 4000*p 10 + 2000*p 12 - 4000*p 13 + 2000*p 14,
    - 2600*p 1 - 350*p 2 + 3300*p 3 - 1650*p 4 + 2700*p 8 - 5400*p 9 - 1300*p 10 + 8000*p 11 - 2350*p 12 - 3300*p 13 + 1650*p 14,
    4508*p 1 + 1482*p 2 - 7472*p 3 + 3736*p 4 - 4000*p 6 + 8000*p 7 - 182*p 8 - 7636*p 9 + 2254*p 10 + 3128*p 11 - 1300*p 12 - 528*p 13 + 264*p 14,
    8504*p 1 - 12024*p 2 + 7544*p 3 - 1772*p 4 + 160*p 6 - 320*p 7 - 476*p 8 + 1272*p 9 + 2252*p 10 - 9776*p 11 + 12500*p 12 - 7224*p 13 + 1612*p 14,
    20128*p 1 - 7768*p 2 + 848*p 3 + 216*p 4 - 432*p 6 + 864*p 7 + 1792*p 8 - 8448*p 9 + 13424*p 10 - 11680*p 11 + 5976*p 12 - 1712*p 13 + 216*p 14,
    14212*p 1 - 13972*p 2 + 8340*p 3 - 2120*p 4 + 2104*p 6 - 8208*p 7 + 13368*p 8 - 11932*p 9 + 6460*p 10 - 2280*p 11 + 604*p 12 - 132*p 13 + 16*p 14,
    2992*p 1 - 7806*p 2 + 13452*p 3 - 11868*p 4 + 11866*p 6 - 13440*p 7 + 7754*p 8 - 2784*p 9 + 770*p 10 - 208*p 11 + 52*p 12 - 12*p 13 + 2*p 14],
  ![- 8000*p 1 + 4000*p 2 - 2000*p 4 + 4000*p 5 - 6000*p 6 + 8000*p 7 - 4000*p 8 + 2000*p 10 - 4000*p 11 + 2000*p 12,
    5400*p 1 + 1300*p 2 - 8000*p 3 + 2350*p 4 + 3300*p 5 + 1050*p 6 - 5400*p 7 - 1300*p 8 + 8000*p 9 - 2350*p 10 - 3300*p 11 + 1650*p 12,
    - 364*p 1 + 1746*p 2 - 3128*p 3 - 2700*p 4 + 8528*p 5 - 446*p 6 - 7636*p 7 + 2254*p 8 + 3128*p 9 - 1300*p 10 - 528*p 11 + 264*p 12,
    - 952*p 1 - 2412*p 2 + 9776*p 3 - 12340*p 4 + 6904*p 5 - 2088*p 6 + 1272*p 7 + 2252*p 8 - 9776*p 9 + 12500*p 10 - 7224*p 11 + 1612*p 12,
    7584*p 1 - 12992*p 2 + 11680*p 3 - 6408*p 4 + 2576*p 5 + 1576*p 6 - 8448*p 7 + 13424*p 8 - 11680*p 9 + 5976*p 10 - 1712*p 11 + 216*p 12,
    20140*p 1 - 8564*p 2 + 2280*p 3 + 1500*p 4 - 8076*p 5 + 13352*p 6 - 11932*p 7 + 6460*p 8 - 2280*p 9 + 604*p 10 - 132*p 11 + 16*p 12,
    16224*p 1 - 12636*p 2 + 208*p 3 + 11814*p 4 - 13428*p 5 + 7752*p 6 - 2784*p 7 + 770*p 8 - 208*p 9 + 52*p 10 - 12*p 11 + 2*p 12],
  ![4000*p 2 - 8000*p 3 + 8000*p 5 - 6000*p 6 + 4000*p 7 - 4000*p 9 + 2000*p 10,
    - 2700*p 2 + 5400*p 3 + 4000*p 4 - 13400*p 5 + 1050*p 6 + 11300*p 7 - 4000*p 8 - 3300*p 9 + 1650*p 10,
    - 8000*p 1 - 3818*p 2 + 15636*p 3 - 2436*p 4 - 10764*p 5 + 3554*p 6 + 3656*p 7 - 1564*p 8 - 528*p 9 + 264*p 10,
    320*p 1 + 636*p 2 - 1592*p 3 - 2728*p 4 + 11048*p 5 - 10248*p 6 - 2552*p 7 + 10888*p 8 - 7224*p 9 + 1612*p 10,
    - 864*p 1 - 2224*p 2 + 9312*p 3 - 11632*p 4 + 3232*p 5 + 7448*p 6 - 9968*p 7 + 5760*p 8 - 1712*p 9 + 216*p 10,
    8208*p 1 - 11264*p 2 + 3724*p 3 + 6908*p 4 - 9652*p 5 + 5856*p 6 - 2148*p 7 + 588*p 8 - 132*p 9 + 16*p 10,
    13440*p 1 + 4112*p 2 - 10656*p 3 + 6984*p 4 - 2576*p 5 + 718*p 6 - 196*p 7 + 50*p 8 - 12*p 9 + 2*p 10]]

theorem fourthLevelEvenRight_row0 (p : Fin 17 → ℝ) (j : Fin 7) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 0 j =
      fourthLevelEvenRightPolynomial p 0 j := by
  fin_cases j
  · exact fourthLevelEvenRightEntry_0_0 p
  · exact fourthLevelEvenRightEntry_0_1 p
  · exact fourthLevelEvenRightEntry_0_2 p
  · exact fourthLevelEvenRightEntry_0_3 p
  · exact fourthLevelEvenRightEntry_0_4 p
  · exact fourthLevelEvenRightEntry_0_5 p
  · exact fourthLevelEvenRightEntry_0_6 p

theorem fourthLevelEvenRight_row1 (p : Fin 17 → ℝ) (j : Fin 7) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 1 j =
      fourthLevelEvenRightPolynomial p 1 j := by
  fin_cases j
  · exact fourthLevelEvenRightEntry_1_0 p
  · exact fourthLevelEvenRightEntry_1_1 p
  · exact fourthLevelEvenRightEntry_1_2 p
  · exact fourthLevelEvenRightEntry_1_3 p
  · exact fourthLevelEvenRightEntry_1_4 p
  · exact fourthLevelEvenRightEntry_1_5 p
  · exact fourthLevelEvenRightEntry_1_6 p

theorem fourthLevelEvenRight_row2 (p : Fin 17 → ℝ) (j : Fin 7) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 2 j =
      fourthLevelEvenRightPolynomial p 2 j := by
  fin_cases j
  · exact fourthLevelEvenRightEntry_2_0 p
  · exact fourthLevelEvenRightEntry_2_1 p
  · exact fourthLevelEvenRightEntry_2_2 p
  · exact fourthLevelEvenRightEntry_2_3 p
  · exact fourthLevelEvenRightEntry_2_4 p
  · exact fourthLevelEvenRightEntry_2_5 p
  · exact fourthLevelEvenRightEntry_2_6 p

theorem fourthLevelEvenRight_row3 (p : Fin 17 → ℝ) (j : Fin 7) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 3 j =
      fourthLevelEvenRightPolynomial p 3 j := by
  fin_cases j
  · exact fourthLevelEvenRightEntry_3_0 p
  · exact fourthLevelEvenRightEntry_3_1 p
  · exact fourthLevelEvenRightEntry_3_2 p
  · exact fourthLevelEvenRightEntry_3_3 p
  · exact fourthLevelEvenRightEntry_3_4 p
  · exact fourthLevelEvenRightEntry_3_5 p
  · exact fourthLevelEvenRightEntry_3_6 p

theorem fourthLevelEvenRight_row4 (p : Fin 17 → ℝ) (j : Fin 7) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 4 j =
      fourthLevelEvenRightPolynomial p 4 j := by
  fin_cases j
  · exact fourthLevelEvenRightEntry_4_0 p
  · exact fourthLevelEvenRightEntry_4_1 p
  · exact fourthLevelEvenRightEntry_4_2 p
  · exact fourthLevelEvenRightEntry_4_3 p
  · exact fourthLevelEvenRightEntry_4_4 p
  · exact fourthLevelEvenRightEntry_4_5 p
  · exact fourthLevelEvenRightEntry_4_6 p

theorem fourthLevelEvenRight_row5 (p : Fin 17 → ℝ) (j : Fin 7) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 5 j =
      fourthLevelEvenRightPolynomial p 5 j := by
  fin_cases j
  · exact fourthLevelEvenRightEntry_5_0 p
  · exact fourthLevelEvenRightEntry_5_1 p
  · exact fourthLevelEvenRightEntry_5_2 p
  · exact fourthLevelEvenRightEntry_5_3 p
  · exact fourthLevelEvenRightEntry_5_4 p
  · exact fourthLevelEvenRightEntry_5_5 p
  · exact fourthLevelEvenRightEntry_5_6 p

theorem fourthLevelEvenRight_row6 (p : Fin 17 → ℝ) (j : Fin 7) :
    (fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator) 6 j =
      fourthLevelEvenRightPolynomial p 6 j := by
  fin_cases j
  · exact fourthLevelEvenRightEntry_6_0 p
  · exact fourthLevelEvenRightEntry_6_1 p
  · exact fourthLevelEvenRightEntry_6_2 p
  · exact fourthLevelEvenRightEntry_6_3 p
  · exact fourthLevelEvenRightEntry_6_4 p
  · exact fourthLevelEvenRightEntry_6_5 p
  · exact fourthLevelEvenRightEntry_6_6 p

theorem fourthLevelEvenRight_eq (p : Fin 17 → ℝ) :
    fourthLevelEvenPolynomial p * fourthLevelEvenShearNumerator =
      fourthLevelEvenRightPolynomial p := by
  ext i j
  fin_cases i
  · exact fourthLevelEvenRight_row0 p j
  · exact fourthLevelEvenRight_row1 p j
  · exact fourthLevelEvenRight_row2 p j
  · exact fourthLevelEvenRight_row3 p j
  · exact fourthLevelEvenRight_row4 p j
  · exact fourthLevelEvenRight_row5 p j
  · exact fourthLevelEvenRight_row6 p j

theorem fourthLevelOddCongruenceEntry_0_0 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 0 0 =
      8000000*p 8 - 2000000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (1000) * (8000*p 8 - 2000*p 16) + ((0) * (- 4000*p 4 + 4000*p 12 - 2000*p 16) + ((0) * (4000*p 2 + 2000*p 4 - 8000*p 6 + 4000*p 8 - 2000*p 12 + 4000*p 14 - 2000*p 16) + ((0) * (- 8000*p 2 + 2000*p 4 + 4000*p 6 - 4000*p 8 + 4000*p 10 - 2000*p 12) + ((0) * (4000*p 1 - 2000*p 2 + 4000*p 6 - 8000*p 7 + 4000*p 8 - 2000*p 14 + 4000*p 15 - 2000*p 16) + ((0) * (- 2000*p 2 + 4000*p 3 + 2000*p 4 - 8000*p 5 + 4000*p 6 - 2000*p 12 + 4000*p 13 - 2000*p 14) + ((0) * (4000*p 2 - 8000*p 3 + 2000*p 4 + 4000*p 5 - 2000*p 6 - 2000*p 10 + 4000*p 11 - 2000*p 12) + ((0) * (- 8000*p 1 + 4000*p 2 - 2000*p 6 + 4000*p 7 - 4000*p 8 + 4000*p 9 - 2000*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_0_1 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 0 1 =
      - 4000000*p 4 - 2000000*p 8 + 4000000*p 12 - 1500000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (1000) * (- 4000*p 4 - 2000*p 8 + 4000*p 12 - 1500*p 16) + ((0) * (25000*p 4 - 16000*p 8 + 7000*p 12 - 1500*p 16) + ((0) * (- 5000*p 2 - 2500*p 4 + 10000*p 6 - 1000*p 8 - 8000*p 10 + 2500*p 12 + 3000*p 14 - 1500*p 16) + ((0) * (2000*p 2 + 1500*p 4 - 5000*p 6 + 1000*p 8 + 3000*p 10 - 1500*p 12) + ((0) * (3000*p 1 + 2500*p 2 - 8000*p 3 + 4000*p 4 - 5000*p 6 + 10000*p 7 - 5000*p 8 + 4000*p 10 - 8000*p 11 + 4000*p 12 - 1500*p 14 + 3000*p 15 - 1500*p 16) + ((0) * (- 8000*p 1 + 2500*p 2 + 3000*p 3 - 6500*p 4 + 10000*p 5 - 5000*p 6 + 4000*p 8 - 8000*p 9 + 4000*p 10 - 1500*p 12 + 3000*p 13 - 1500*p 14) + ((0) * (- 8000*p 1 - 1000*p 2 + 10000*p 3 - 6500*p 4 + 3000*p 5 + 2500*p 6 - 8000*p 7 + 4000*p 8 - 1500*p 10 + 3000*p 11 - 1500*p 12) + ((0) * (10000*p 1 - 1000*p 2 - 8000*p 3 + 8000*p 4 - 8000*p 5 + 2500*p 6 + 3000*p 7 - 3000*p 8 + 3000*p 9 - 1500*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_0_2 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 0 2 =
      4000000*p 2 + 2860000*p 4 - 8000000*p 6 + 4656000*p 8 - 2860000*p 12 + 4000000*p 14 - 1734000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (1000) * (4000*p 2 + 2860*p 4 - 8000*p 6 + 4656*p 8 - 2860*p 12 + 4000*p 14 - 1734*p 16) + ((0) * (- 4000*p 2 - 7488*p 4 + 8000*p 6 + 3440*p 8 - 8000*p 10 + 608*p 12 + 4000*p 14 - 1734*p 16) + ((0) * (17188*p 2 - 3406*p 4 - 2376*p 6 - 1672*p 8 + 9720*p 10 - 12594*p 12 + 7468*p 14 - 1734*p 16) + ((0) * (7344*p 2 - 14266*p 4 + 17188*p 6 - 14328*p 8 + 7468*p 10 - 1734*p 12) + ((0) * (- 4532*p 1 - 594*p 2 + 5720*p 3 - 2860*p 4 + 1188*p 6 - 2376*p 7 + 1188*p 8 - 2860*p 10 + 5720*p 11 + 1140*p 12 - 8000*p 13 + 2266*p 14 + 3468*p 15 - 1734*p 16) + ((0) * (- 2280*p 1 - 594*p 2 + 3468*p 3 - 546*p 4 - 2376*p 5 + 1188*p 6 - 2860*p 8 + 5720*p 9 + 1140*p 10 - 8000*p 11 + 2266*p 12 + 3468*p 13 - 1734*p 14) + ((0) * (5720*p 1 + 2328*p 2 - 10376*p 3 + 3454*p 4 + 3468*p 5 - 4594*p 6 + 5720*p 7 + 1140*p 8 - 8000*p 9 + 2266*p 10 + 3468*p 11 - 1734*p 12) + ((0) * (- 2376*p 1 - 1672*p 2 + 5720*p 3 - 1720*p 4 - 2280*p 5 + 3406*p 6 - 4532*p 7 + 532*p 8 + 3468*p 9 - 1734*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_0_3 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 0 3 =
      - 7036000*p 2 + 2518000*p 4 + 2072000*p 6 - 4204000*p 8 + 4000000*p 10 - 2518000*p 12 + 964000*p 14 - 172000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (1000) * (- 7036*p 2 + 2518*p 4 + 2072*p 6 - 4204*p 8 + 4000*p 10 - 2518*p 12 + 964*p 14 - 172*p 16) + ((0) * (- 964*p 2 + 1886*p 4 - 2072*p 6 + 144*p 8 + 2072*p 10 - 2174*p 12 + 964*p 14 - 172*p 16) + ((0) * (11308*p 2 - 15238*p 4 + 17096*p 6 - 15066*p 8 + 10000*p 10 - 4618*p 12 + 1308*p 14 - 172*p 16) + ((0) * (27096*p 2 - 19684*p 4 + 11308*p 6 - 4790*p 8 + 1308*p 10 - 172*p 12) + ((0) * (- 1584*p 1 - 1726*p 2 + 5036*p 3 + 1482*p 4 - 8000*p 5 - 548*p 6 + 9096*p 7 - 548*p 8 - 8000*p 9 + 1482*p 10 + 5036*p 11 - 1554*p 12 - 1928*p 13 + 792*p 14 + 344*p 15 - 172*p 16) + ((0) * (3108*p 1 + 2274*p 2 - 7656*p 3 - 720*p 4 + 9096*p 5 - 548*p 6 - 8000*p 7 + 1482*p 8 + 5036*p 9 - 1554*p 10 - 1928*p 11 + 792*p 12 + 344*p 13 - 172*p 14) + ((0) * (- 2964*p 1 - 2102*p 2 + 7168*p 3 + 244*p 4 - 7656*p 5 + 1310*p 6 + 5036*p 7 - 1554*p 8 - 1928*p 9 + 792*p 10 + 344*p 11 - 172*p 12) + ((0) * (1096*p 1 + 934*p 2 - 2964*p 3 - 72*p 4 + 3108*p 5 - 762*p 6 - 1584*p 7 + 620*p 8 + 344*p 9 - 172*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_0_4 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 0 4 =
      4000000*p 1 - 2456000*p 2 - 624000*p 4 + 5440000*p 6 - 8000000*p 7 + 3456000*p 8 - 176000*p 10 + 624000*p 12 - 2808000*p 14 + 4000000*p 15 - 1684000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (1000) * (4000*p 1 - 2456*p 2 - 624*p 4 + 5440*p 6 - 8000*p 7 + 3456*p 8 - 176*p 10 + 624*p 12 - 2808*p 14 + 4000*p 15 - 1684*p 16) + ((0) * (4000*p 1 + 2808*p 2 - 8000*p 3 + 5064*p 4 - 5440*p 6 + 8000*p 7 - 4528*p 8 + 5440*p 10 - 8000*p 11 + 3992*p 12 - 2808*p 14 + 4000*p 15 - 1684*p 16) + ((0) * (- 4000*p 1 - 3672*p 2 + 4000*p 3 - 620*p 4 - 528*p 6 + 1064*p 8 - 4232*p 10 + 4000*p 11 + 4556*p 12 - 8000*p 13 + 560*p 14 + 4000*p 15 - 1684*p 16) + ((0) * (- 4760*p 2 + 4000*p 3 + 5620*p 4 - 8000*p 5 - 3672*p 6 + 8000*p 7 + 2872*p 8 - 8000*p 9 + 560*p 10 + 4000*p 11 - 1684*p 12) + ((0) * (16984*p 1 - 3868*p 2 - 1248*p 3 + 448*p 4 + 352*p 5 - 88*p 6 - 176*p 7 - 88*p 8 + 352*p 9 + 448*p 10 - 1248*p 11 - 2184*p 12 + 9616*p 13 - 12492*p 14 + 7368*p 15 - 1684*p 16) + ((0) * (8368*p 1 - 12044*p 2 + 7720*p 3 - 1772*p 4 - 176*p 5 - 88*p 6 + 352*p 7 + 448*p 8 - 1248*p 9 - 2184*p 10 + 9616*p 11 - 12492*p 12 + 7368*p 13 - 1684*p 14) + ((0) * (- 896*p 1 - 2272*p 2 + 9440*p 3 - 12580*p 4 + 7720*p 5 - 1236*p 6 - 1248*p 7 - 2184*p 8 + 9616*p 9 - 12492*p 10 + 7368*p 11 - 1684*p 12) + ((0) * (176*p 1 + 360*p 2 - 896*p 3 - 1736*p 4 + 8368*p 5 - 14676*p 6 + 16984*p 7 - 14176*p 8 + 7368*p 9 - 1684*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_0_5 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 0 5 =
      1288000*p 1 - 4188000*p 2 + 4000000*p 3 + 2240000*p 4 - 8000000*p 5 + 6888000*p 6 - 2576000*p 7 + 200000*p 8 + 496000*p 10 - 2240000*p 12 + 4000000*p 13 - 3196000*p 14 + 1288000*p 15 - 224000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (1000) * (1288*p 1 - 4188*p 2 + 4000*p 3 + 2240*p 4 - 8000*p 5 + 6888*p 6 - 2576*p 7 + 200*p 8 + 496*p 10 - 2240*p 12 + 4000*p 13 - 3196*p 14 + 1288*p 15 - 224*p 16) + ((0) * (- 6712*p 1 + 3196*p 2 + 1424*p 3 - 5776*p 4 + 8000*p 5 - 6888*p 6 + 2576*p 7 + 3784*p 8 - 8000*p 9 + 6888*p 10 - 2576*p 11 - 1792*p 12 + 4000*p 13 - 3196*p 14 + 1288*p 15 - 224*p 16) + ((0) * (- 5288*p 1 - 968*p 2 + 5288*p 3 - 3704*p 4 + 1488*p 6 - 3480*p 8 + 4000*p 9 + 1780*p 10 - 6712*p 11 + 3928*p 12 + 1424*p 13 - 2748*p 14 + 1288*p 15 - 224*p 16) + ((0) * (4000*p 1 + 3268*p 2 - 6712*p 3 + 448*p 4 + 5424*p 5 - 968*p 6 - 5424*p 7 + 3704*p 8 + 1424*p 9 - 2748*p 10 + 1288*p 11 - 224*p 12) + ((0) * (13416*p 1 - 13660*p 2 + 8480*p 3 - 1744*p 4 - 992*p 5 + 248*p 6 + 496*p 7 + 248*p 8 - 992*p 9 - 1744*p 10 + 8480*p 11 - 13436*p 12 + 11680*p 13 - 5996*p 14 + 1736*p 15 - 224*p 16) + ((0) * (20160*p 1 - 7740*p 2 + 744*p 3 + 24*p 4 + 496*p 5 + 248*p 6 - 992*p 7 - 1744*p 8 + 8480*p 9 - 13436*p 10 + 11680*p 11 - 5996*p 12 + 1736*p 13 - 224*p 14) + ((0) * (7488*p 1 - 13188*p 2 + 12176*p 3 - 5748*p 4 + 744*p 5 - 1968*p 6 + 8480*p 7 - 13436*p 8 + 11680*p 9 - 5996*p 10 + 1736*p 11 - 224*p 12) + ((0) * (- 496*p 1 - 1496*p 2 + 7488*p 3 - 15180*p 4 + 20160*p 5 - 19432*p 6 + 13416*p 7 - 6220*p 8 + 1736*p 9 - 224*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_0_6 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 0 6 =
      96000*p 1 + 4338000*p 2 - 6644000*p 3 + 3168000*p 4 + 1288000*p 5 - 1608000*p 6 - 192000*p 7 + 956000*p 8 - 2356000*p 10 + 4000000*p 11 - 3168000*p 12 + 1356000*p 13 - 374000*p 14 + 96000*p 15 - 16000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (1000) * (96*p 1 + 4338*p 2 - 6644*p 3 + 3168*p 4 + 1288*p 5 - 1608*p 6 - 192*p 7 + 956*p 8 - 2356*p 10 + 4000*p 11 - 3168*p 12 + 1356*p 13 - 374*p 14 + 96*p 15 - 16*p 16) + ((0) * (- 10616*p 1 + 374*p 2 + 9164*p 3 - 11320*p 4 + 6712*p 5 + 1608*p 6 - 7808*p 7 + 7228*p 8 - 2712*p 9 - 1608*p 10 + 3808*p 11 - 3136*p 12 + 1356*p 13 - 374*p 14 + 96*p 15 - 16*p 16) + ((0) * (2548*p 1 + 3264*p 2 - 6548*p 3 + 2452*p 4 + 4000*p 5 - 6560*p 6 + 4000*p 7 + 2468*p 8 - 6644*p 9 + 3606*p 10 + 1384*p 11 - 2436*p 12 + 1164*p 13 - 342*p 14 + 96*p 15 - 16*p 16) + ((0) * (- 2644*p 1 - 2954*p 2 + 5384*p 3 + 32*p 4 - 5480*p 5 + 3264*p 6 + 1480*p 7 - 2452*p 8 + 1164*p 9 - 342*p 10 + 96*p 11 - 16*p 12) + ((0) * (2328*p 1 - 6270*p 2 + 11692*p 3 - 13524*p 4 + 8712*p 5 - 1432*p 6 - 1848*p 7 - 1432*p 8 + 8712*p 9 - 13524*p 10 + 11692*p 11 - 6254*p 12 + 2200*p 13 - 582*p 14 + 128*p 15 - 16*p 16) + ((0) * (13892*p 1 - 14106*p 2 + 8840*p 3 - 1448*p 4 - 1848*p 5 - 1432*p 6 + 8712*p 7 - 13524*p 8 + 11692*p 9 - 6254*p 10 + 2200*p 11 - 582*p 12 + 128*p 13 - 16*p 14) + ((0) * (20404*p 1 - 7686*p 2 + 352*p 3 - 2014*p 4 + 8840*p 5 - 13540*p 6 + 11692*p 7 - 6254*p 8 + 2200*p 9 - 582*p 10 + 128*p 11 - 16*p 12) + ((0) * (6864*p 1 - 14956*p 2 + 20404*p 3 - 19778*p 4 + 13892*p 5 - 6836*p 6 + 2328*p 7 - 598*p 8 + 128*p 9 - 16*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_0_7 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 0 7 =
      - 7996000*p 1 + 5054000*p 2 - 1992000*p 3 + 286000*p 4 + 876000*p 5 - 2494000*p 6 + 3992000*p 7 - 4548000*p 8 + 4000000*p 9 - 2538000*p 10 + 1036000*p 11 - 286000*p 12 + 80000*p 13 - 22000*p 14 + 4000*p 15 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (1000) * (- 7996*p 1 + 5054*p 2 - 1992*p 3 + 286*p 4 + 876*p 5 - 2494*p 6 + 3992*p 7 - 4548*p 8 + 4000*p 9 - 2538*p 10 + 1036*p 11 - 286*p 12 + 80*p 13 - 22*p 14 + 4*p 15) + ((0) * (5772*p 1 + 22*p 2 - 5856*p 3 + 8238*p 4 - 6804*p 5 + 2494*p 6 + 1936*p 7 - 3976*p 8 + 3840*p 9 - 2494*p 10 + 1028*p 11 - 286*p 12 + 80*p 13 - 22*p 14 + 4*p 15) + ((0) * (952*p 1 - 2010*p 2 + 2012*p 3 + 242*p 4 - 2964*p 5 + 4020*p 6 - 2964*p 7 + 242*p 8 + 2008*p 9 - 1988*p 10 + 880*p 11 - 242*p 12 + 72*p 13 - 22*p 14 + 4*p 15) + ((0) * (- 956*p 1 + 2032*p 2 - 2084*p 3 + 2080*p 5 - 2010*p 6 + 884*p 7 - 242*p 8 + 72*p 9 - 22*p 10 + 4*p 11) + ((0) * (132*p 1 - 468*p 2 + 1688*p 3 - 4896*p 4 + 10112*p 5 - 15086*p 6 + 17096*p 7 - 15086*p 8 + 10112*p 9 - 4896*p 10 + 1688*p 11 - 468*p 12 + 128*p 13 - 30*p 14 + 4*p 15) + ((0) * (1816*p 1 - 4926*p 2 + 10116*p 3 - 15086*p 4 + 17096*p 5 - 15086*p 6 + 10112*p 7 - 4896*p 8 + 1688*p 9 - 468*p 10 + 128*p 11 - 30*p 12 + 4*p 13) + ((0) * (11800*p 1 - 15554*p 2 + 17224*p 3 - 15116*p 4 + 10116*p 5 - 4896*p 6 + 1688*p 7 - 468*p 8 + 128*p 9 - 30*p 10 + 4*p 11) + ((0) * (27208*p 1 - 19982*p 2 + 11800*p 3 - 5364*p 4 + 1816*p 5 - 498*p 6 + 132*p 7 - 30*p 8 + 4*p 9) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_1_0 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 1 0 =
      - 4000000*p 4 - 2000000*p 8 + 4000000*p 12 - 1500000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-250) * (8000*p 8 - 2000*p 16) + ((1000) * (- 4000*p 4 + 4000*p 12 - 2000*p 16) + ((0) * (4000*p 2 + 2000*p 4 - 8000*p 6 + 4000*p 8 - 2000*p 12 + 4000*p 14 - 2000*p 16) + ((0) * (- 8000*p 2 + 2000*p 4 + 4000*p 6 - 4000*p 8 + 4000*p 10 - 2000*p 12) + ((0) * (4000*p 1 - 2000*p 2 + 4000*p 6 - 8000*p 7 + 4000*p 8 - 2000*p 14 + 4000*p 15 - 2000*p 16) + ((0) * (- 2000*p 2 + 4000*p 3 + 2000*p 4 - 8000*p 5 + 4000*p 6 - 2000*p 12 + 4000*p 13 - 2000*p 14) + ((0) * (4000*p 2 - 8000*p 3 + 2000*p 4 + 4000*p 5 - 2000*p 6 - 2000*p 10 + 4000*p 11 - 2000*p 12) + ((0) * (- 8000*p 1 + 4000*p 2 - 2000*p 6 + 4000*p 7 - 4000*p 8 + 4000*p 9 - 2000*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_1_1 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 1 1 =
      26000000*p 4 - 15500000*p 8 + 6000000*p 12 - 1125000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-250) * (- 4000*p 4 - 2000*p 8 + 4000*p 12 - 1500*p 16) + ((1000) * (25000*p 4 - 16000*p 8 + 7000*p 12 - 1500*p 16) + ((0) * (- 5000*p 2 - 2500*p 4 + 10000*p 6 - 1000*p 8 - 8000*p 10 + 2500*p 12 + 3000*p 14 - 1500*p 16) + ((0) * (2000*p 2 + 1500*p 4 - 5000*p 6 + 1000*p 8 + 3000*p 10 - 1500*p 12) + ((0) * (3000*p 1 + 2500*p 2 - 8000*p 3 + 4000*p 4 - 5000*p 6 + 10000*p 7 - 5000*p 8 + 4000*p 10 - 8000*p 11 + 4000*p 12 - 1500*p 14 + 3000*p 15 - 1500*p 16) + ((0) * (- 8000*p 1 + 2500*p 2 + 3000*p 3 - 6500*p 4 + 10000*p 5 - 5000*p 6 + 4000*p 8 - 8000*p 9 + 4000*p 10 - 1500*p 12 + 3000*p 13 - 1500*p 14) + ((0) * (- 8000*p 1 - 1000*p 2 + 10000*p 3 - 6500*p 4 + 3000*p 5 + 2500*p 6 - 8000*p 7 + 4000*p 8 - 1500*p 10 + 3000*p 11 - 1500*p 12) + ((0) * (10000*p 1 - 1000*p 2 - 8000*p 3 + 8000*p 4 - 8000*p 5 + 2500*p 6 + 3000*p 7 - 3000*p 8 + 3000*p 9 - 1500*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_1_2 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 1 2 =
      - 5000000*p 2 - 8203000*p 4 + 10000000*p 6 + 2276000*p 8 - 8000000*p 10 + 1323000*p 12 + 3000000*p 14 - 1300500*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-250) * (4000*p 2 + 2860*p 4 - 8000*p 6 + 4656*p 8 - 2860*p 12 + 4000*p 14 - 1734*p 16) + ((1000) * (- 4000*p 2 - 7488*p 4 + 8000*p 6 + 3440*p 8 - 8000*p 10 + 608*p 12 + 4000*p 14 - 1734*p 16) + ((0) * (17188*p 2 - 3406*p 4 - 2376*p 6 - 1672*p 8 + 9720*p 10 - 12594*p 12 + 7468*p 14 - 1734*p 16) + ((0) * (7344*p 2 - 14266*p 4 + 17188*p 6 - 14328*p 8 + 7468*p 10 - 1734*p 12) + ((0) * (- 4532*p 1 - 594*p 2 + 5720*p 3 - 2860*p 4 + 1188*p 6 - 2376*p 7 + 1188*p 8 - 2860*p 10 + 5720*p 11 + 1140*p 12 - 8000*p 13 + 2266*p 14 + 3468*p 15 - 1734*p 16) + ((0) * (- 2280*p 1 - 594*p 2 + 3468*p 3 - 546*p 4 - 2376*p 5 + 1188*p 6 - 2860*p 8 + 5720*p 9 + 1140*p 10 - 8000*p 11 + 2266*p 12 + 3468*p 13 - 1734*p 14) + ((0) * (5720*p 1 + 2328*p 2 - 10376*p 3 + 3454*p 4 + 3468*p 5 - 4594*p 6 + 5720*p 7 + 1140*p 8 - 8000*p 9 + 2266*p 10 + 3468*p 11 - 1734*p 12) + ((0) * (- 2376*p 1 - 1672*p 2 + 5720*p 3 - 1720*p 4 - 2280*p 5 + 3406*p 6 - 4532*p 7 + 532*p 8 + 3468*p 9 - 1734*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_1_3 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 1 3 =
      795000*p 2 + 1256500*p 4 - 2590000*p 6 + 1195000*p 8 + 1072000*p 10 - 1544500*p 12 + 723000*p 14 - 129000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-250) * (- 7036*p 2 + 2518*p 4 + 2072*p 6 - 4204*p 8 + 4000*p 10 - 2518*p 12 + 964*p 14 - 172*p 16) + ((1000) * (- 964*p 2 + 1886*p 4 - 2072*p 6 + 144*p 8 + 2072*p 10 - 2174*p 12 + 964*p 14 - 172*p 16) + ((0) * (11308*p 2 - 15238*p 4 + 17096*p 6 - 15066*p 8 + 10000*p 10 - 4618*p 12 + 1308*p 14 - 172*p 16) + ((0) * (27096*p 2 - 19684*p 4 + 11308*p 6 - 4790*p 8 + 1308*p 10 - 172*p 12) + ((0) * (- 1584*p 1 - 1726*p 2 + 5036*p 3 + 1482*p 4 - 8000*p 5 - 548*p 6 + 9096*p 7 - 548*p 8 - 8000*p 9 + 1482*p 10 + 5036*p 11 - 1554*p 12 - 1928*p 13 + 792*p 14 + 344*p 15 - 172*p 16) + ((0) * (3108*p 1 + 2274*p 2 - 7656*p 3 - 720*p 4 + 9096*p 5 - 548*p 6 - 8000*p 7 + 1482*p 8 + 5036*p 9 - 1554*p 10 - 1928*p 11 + 792*p 12 + 344*p 13 - 172*p 14) + ((0) * (- 2964*p 1 - 2102*p 2 + 7168*p 3 + 244*p 4 - 7656*p 5 + 1310*p 6 + 5036*p 7 - 1554*p 8 - 1928*p 9 + 792*p 10 + 344*p 11 - 172*p 12) + ((0) * (1096*p 1 + 934*p 2 - 2964*p 3 - 72*p 4 + 3108*p 5 - 762*p 6 - 1584*p 7 + 620*p 8 + 344*p 9 - 172*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_1_4 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 1 4 =
      3000000*p 1 + 3422000*p 2 - 8000000*p 3 + 5220000*p 4 - 6800000*p 6 + 10000000*p 7 - 5392000*p 8 + 5484000*p 10 - 8000000*p 11 + 3836000*p 12 - 2106000*p 14 + 3000000*p 15 - 1263000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-250) * (4000*p 1 - 2456*p 2 - 624*p 4 + 5440*p 6 - 8000*p 7 + 3456*p 8 - 176*p 10 + 624*p 12 - 2808*p 14 + 4000*p 15 - 1684*p 16) + ((1000) * (4000*p 1 + 2808*p 2 - 8000*p 3 + 5064*p 4 - 5440*p 6 + 8000*p 7 - 4528*p 8 + 5440*p 10 - 8000*p 11 + 3992*p 12 - 2808*p 14 + 4000*p 15 - 1684*p 16) + ((0) * (- 4000*p 1 - 3672*p 2 + 4000*p 3 - 620*p 4 - 528*p 6 + 1064*p 8 - 4232*p 10 + 4000*p 11 + 4556*p 12 - 8000*p 13 + 560*p 14 + 4000*p 15 - 1684*p 16) + ((0) * (- 4760*p 2 + 4000*p 3 + 5620*p 4 - 8000*p 5 - 3672*p 6 + 8000*p 7 + 2872*p 8 - 8000*p 9 + 560*p 10 + 4000*p 11 - 1684*p 12) + ((0) * (16984*p 1 - 3868*p 2 - 1248*p 3 + 448*p 4 + 352*p 5 - 88*p 6 - 176*p 7 - 88*p 8 + 352*p 9 + 448*p 10 - 1248*p 11 - 2184*p 12 + 9616*p 13 - 12492*p 14 + 7368*p 15 - 1684*p 16) + ((0) * (8368*p 1 - 12044*p 2 + 7720*p 3 - 1772*p 4 - 176*p 5 - 88*p 6 + 352*p 7 + 448*p 8 - 1248*p 9 - 2184*p 10 + 9616*p 11 - 12492*p 12 + 7368*p 13 - 1684*p 14) + ((0) * (- 896*p 1 - 2272*p 2 + 9440*p 3 - 12580*p 4 + 7720*p 5 - 1236*p 6 - 1248*p 7 - 2184*p 8 + 9616*p 9 - 12492*p 10 + 7368*p 11 - 1684*p 12) + ((0) * (176*p 1 + 360*p 2 - 896*p 3 - 1736*p 4 + 8368*p 5 - 14676*p 6 + 16984*p 7 - 14176*p 8 + 7368*p 9 - 1684*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_1_5 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 1 5 =
      - 7034000*p 1 + 4243000*p 2 + 424000*p 3 - 6336000*p 4 + 10000000*p 5 - 8610000*p 6 + 3220000*p 7 + 3734000*p 8 - 8000000*p 9 + 6764000*p 10 - 2576000*p 11 - 1232000*p 12 + 3000000*p 13 - 2397000*p 14 + 966000*p 15 - 168000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-250) * (1288*p 1 - 4188*p 2 + 4000*p 3 + 2240*p 4 - 8000*p 5 + 6888*p 6 - 2576*p 7 + 200*p 8 + 496*p 10 - 2240*p 12 + 4000*p 13 - 3196*p 14 + 1288*p 15 - 224*p 16) + ((1000) * (- 6712*p 1 + 3196*p 2 + 1424*p 3 - 5776*p 4 + 8000*p 5 - 6888*p 6 + 2576*p 7 + 3784*p 8 - 8000*p 9 + 6888*p 10 - 2576*p 11 - 1792*p 12 + 4000*p 13 - 3196*p 14 + 1288*p 15 - 224*p 16) + ((0) * (- 5288*p 1 - 968*p 2 + 5288*p 3 - 3704*p 4 + 1488*p 6 - 3480*p 8 + 4000*p 9 + 1780*p 10 - 6712*p 11 + 3928*p 12 + 1424*p 13 - 2748*p 14 + 1288*p 15 - 224*p 16) + ((0) * (4000*p 1 + 3268*p 2 - 6712*p 3 + 448*p 4 + 5424*p 5 - 968*p 6 - 5424*p 7 + 3704*p 8 + 1424*p 9 - 2748*p 10 + 1288*p 11 - 224*p 12) + ((0) * (13416*p 1 - 13660*p 2 + 8480*p 3 - 1744*p 4 - 992*p 5 + 248*p 6 + 496*p 7 + 248*p 8 - 992*p 9 - 1744*p 10 + 8480*p 11 - 13436*p 12 + 11680*p 13 - 5996*p 14 + 1736*p 15 - 224*p 16) + ((0) * (20160*p 1 - 7740*p 2 + 744*p 3 + 24*p 4 + 496*p 5 + 248*p 6 - 992*p 7 - 1744*p 8 + 8480*p 9 - 13436*p 10 + 11680*p 11 - 5996*p 12 + 1736*p 13 - 224*p 14) + ((0) * (7488*p 1 - 13188*p 2 + 12176*p 3 - 5748*p 4 + 744*p 5 - 1968*p 6 + 8480*p 7 - 13436*p 8 + 11680*p 9 - 5996*p 10 + 1736*p 11 - 224*p 12) + ((0) * (- 496*p 1 - 1496*p 2 + 7488*p 3 - 15180*p 4 + 20160*p 5 - 19432*p 6 + 13416*p 7 - 6220*p 8 + 1736*p 9 - 224*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_1_6 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 1 6 =
      - 10640000*p 1 - 710500*p 2 + 10825000*p 3 - 12112000*p 4 + 6390000*p 5 + 2010000*p 6 - 7760000*p 7 + 6989000*p 8 - 2712000*p 9 - 1019000*p 10 + 2808000*p 11 - 2344000*p 12 + 1017000*p 13 - 280500*p 14 + 72000*p 15 - 12000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-250) * (96*p 1 + 4338*p 2 - 6644*p 3 + 3168*p 4 + 1288*p 5 - 1608*p 6 - 192*p 7 + 956*p 8 - 2356*p 10 + 4000*p 11 - 3168*p 12 + 1356*p 13 - 374*p 14 + 96*p 15 - 16*p 16) + ((1000) * (- 10616*p 1 + 374*p 2 + 9164*p 3 - 11320*p 4 + 6712*p 5 + 1608*p 6 - 7808*p 7 + 7228*p 8 - 2712*p 9 - 1608*p 10 + 3808*p 11 - 3136*p 12 + 1356*p 13 - 374*p 14 + 96*p 15 - 16*p 16) + ((0) * (2548*p 1 + 3264*p 2 - 6548*p 3 + 2452*p 4 + 4000*p 5 - 6560*p 6 + 4000*p 7 + 2468*p 8 - 6644*p 9 + 3606*p 10 + 1384*p 11 - 2436*p 12 + 1164*p 13 - 342*p 14 + 96*p 15 - 16*p 16) + ((0) * (- 2644*p 1 - 2954*p 2 + 5384*p 3 + 32*p 4 - 5480*p 5 + 3264*p 6 + 1480*p 7 - 2452*p 8 + 1164*p 9 - 342*p 10 + 96*p 11 - 16*p 12) + ((0) * (2328*p 1 - 6270*p 2 + 11692*p 3 - 13524*p 4 + 8712*p 5 - 1432*p 6 - 1848*p 7 - 1432*p 8 + 8712*p 9 - 13524*p 10 + 11692*p 11 - 6254*p 12 + 2200*p 13 - 582*p 14 + 128*p 15 - 16*p 16) + ((0) * (13892*p 1 - 14106*p 2 + 8840*p 3 - 1448*p 4 - 1848*p 5 - 1432*p 6 + 8712*p 7 - 13524*p 8 + 11692*p 9 - 6254*p 10 + 2200*p 11 - 582*p 12 + 128*p 13 - 16*p 14) + ((0) * (20404*p 1 - 7686*p 2 + 352*p 3 - 2014*p 4 + 8840*p 5 - 13540*p 6 + 11692*p 7 - 6254*p 8 + 2200*p 9 - 582*p 10 + 128*p 11 - 16*p 12) + ((0) * (6864*p 1 - 14956*p 2 + 20404*p 3 - 19778*p 4 + 13892*p 5 - 6836*p 6 + 2328*p 7 - 598*p 8 + 128*p 9 - 16*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_1_7 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 1 7 =
      7771000*p 1 - 1241500*p 2 - 5358000*p 3 + 8166500*p 4 - 7023000*p 5 + 3117500*p 6 + 938000*p 7 - 2839000*p 8 + 2840000*p 9 - 1859500*p 10 + 769000*p 11 - 214500*p 12 + 60000*p 13 - 16500*p 14 + 3000*p 15 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-250) * (- 7996*p 1 + 5054*p 2 - 1992*p 3 + 286*p 4 + 876*p 5 - 2494*p 6 + 3992*p 7 - 4548*p 8 + 4000*p 9 - 2538*p 10 + 1036*p 11 - 286*p 12 + 80*p 13 - 22*p 14 + 4*p 15) + ((1000) * (5772*p 1 + 22*p 2 - 5856*p 3 + 8238*p 4 - 6804*p 5 + 2494*p 6 + 1936*p 7 - 3976*p 8 + 3840*p 9 - 2494*p 10 + 1028*p 11 - 286*p 12 + 80*p 13 - 22*p 14 + 4*p 15) + ((0) * (952*p 1 - 2010*p 2 + 2012*p 3 + 242*p 4 - 2964*p 5 + 4020*p 6 - 2964*p 7 + 242*p 8 + 2008*p 9 - 1988*p 10 + 880*p 11 - 242*p 12 + 72*p 13 - 22*p 14 + 4*p 15) + ((0) * (- 956*p 1 + 2032*p 2 - 2084*p 3 + 2080*p 5 - 2010*p 6 + 884*p 7 - 242*p 8 + 72*p 9 - 22*p 10 + 4*p 11) + ((0) * (132*p 1 - 468*p 2 + 1688*p 3 - 4896*p 4 + 10112*p 5 - 15086*p 6 + 17096*p 7 - 15086*p 8 + 10112*p 9 - 4896*p 10 + 1688*p 11 - 468*p 12 + 128*p 13 - 30*p 14 + 4*p 15) + ((0) * (1816*p 1 - 4926*p 2 + 10116*p 3 - 15086*p 4 + 17096*p 5 - 15086*p 6 + 10112*p 7 - 4896*p 8 + 1688*p 9 - 468*p 10 + 128*p 11 - 30*p 12 + 4*p 13) + ((0) * (11800*p 1 - 15554*p 2 + 17224*p 3 - 15116*p 4 + 10116*p 5 - 4896*p 6 + 1688*p 7 - 468*p 8 + 128*p 9 - 30*p 10 + 4*p 11) + ((0) * (27208*p 1 - 19982*p 2 + 11800*p 3 - 5364*p 4 + 1816*p 5 - 498*p 6 + 132*p 7 - 30*p 8 + 4*p 9) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_2_0 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 2 0 =
      4000000*p 2 + 2860000*p 4 - 8000000*p 6 + 4656000*p 8 - 2860000*p 12 + 4000000*p 14 - 1734000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (82) * (8000*p 8 - 2000*p 16) + ((-215) * (- 4000*p 4 + 4000*p 12 - 2000*p 16) + ((1000) * (4000*p 2 + 2000*p 4 - 8000*p 6 + 4000*p 8 - 2000*p 12 + 4000*p 14 - 2000*p 16) + ((0) * (- 8000*p 2 + 2000*p 4 + 4000*p 6 - 4000*p 8 + 4000*p 10 - 2000*p 12) + ((0) * (4000*p 1 - 2000*p 2 + 4000*p 6 - 8000*p 7 + 4000*p 8 - 2000*p 14 + 4000*p 15 - 2000*p 16) + ((0) * (- 2000*p 2 + 4000*p 3 + 2000*p 4 - 8000*p 5 + 4000*p 6 - 2000*p 12 + 4000*p 13 - 2000*p 14) + ((0) * (4000*p 2 - 8000*p 3 + 2000*p 4 + 4000*p 5 - 2000*p 6 - 2000*p 10 + 4000*p 11 - 2000*p 12) + ((0) * (- 8000*p 1 + 4000*p 2 - 2000*p 6 + 4000*p 7 - 4000*p 8 + 4000*p 9 - 2000*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_2_1 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 2 1 =
      - 5000000*p 2 - 8203000*p 4 + 10000000*p 6 + 2276000*p 8 - 8000000*p 10 + 1323000*p 12 + 3000000*p 14 - 1300500*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (82) * (- 4000*p 4 - 2000*p 8 + 4000*p 12 - 1500*p 16) + ((-215) * (25000*p 4 - 16000*p 8 + 7000*p 12 - 1500*p 16) + ((1000) * (- 5000*p 2 - 2500*p 4 + 10000*p 6 - 1000*p 8 - 8000*p 10 + 2500*p 12 + 3000*p 14 - 1500*p 16) + ((0) * (2000*p 2 + 1500*p 4 - 5000*p 6 + 1000*p 8 + 3000*p 10 - 1500*p 12) + ((0) * (3000*p 1 + 2500*p 2 - 8000*p 3 + 4000*p 4 - 5000*p 6 + 10000*p 7 - 5000*p 8 + 4000*p 10 - 8000*p 11 + 4000*p 12 - 1500*p 14 + 3000*p 15 - 1500*p 16) + ((0) * (- 8000*p 1 + 2500*p 2 + 3000*p 3 - 6500*p 4 + 10000*p 5 - 5000*p 6 + 4000*p 8 - 8000*p 9 + 4000*p 10 - 1500*p 12 + 3000*p 13 - 1500*p 14) + ((0) * (- 8000*p 1 - 1000*p 2 + 10000*p 3 - 6500*p 4 + 3000*p 5 + 2500*p 6 - 8000*p 7 + 4000*p 8 - 1500*p 10 + 3000*p 11 - 1500*p 12) + ((0) * (10000*p 1 - 1000*p 2 - 8000*p 3 + 8000*p 4 - 8000*p 5 + 2500*p 6 + 3000*p 7 - 3000*p 8 + 3000*p 9 - 1500*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_2_2 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 2 2 =
      18376000*p 2 - 1561560*p 4 - 4752000*p 6 - 2029808*p 8 + 11440000*p 10 - 12959240*p 12 + 6936000*p 14 - 1503378*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (82) * (4000*p 2 + 2860*p 4 - 8000*p 6 + 4656*p 8 - 2860*p 12 + 4000*p 14 - 1734*p 16) + ((-215) * (- 4000*p 2 - 7488*p 4 + 8000*p 6 + 3440*p 8 - 8000*p 10 + 608*p 12 + 4000*p 14 - 1734*p 16) + ((1000) * (17188*p 2 - 3406*p 4 - 2376*p 6 - 1672*p 8 + 9720*p 10 - 12594*p 12 + 7468*p 14 - 1734*p 16) + ((0) * (7344*p 2 - 14266*p 4 + 17188*p 6 - 14328*p 8 + 7468*p 10 - 1734*p 12) + ((0) * (- 4532*p 1 - 594*p 2 + 5720*p 3 - 2860*p 4 + 1188*p 6 - 2376*p 7 + 1188*p 8 - 2860*p 10 + 5720*p 11 + 1140*p 12 - 8000*p 13 + 2266*p 14 + 3468*p 15 - 1734*p 16) + ((0) * (- 2280*p 1 - 594*p 2 + 3468*p 3 - 546*p 4 - 2376*p 5 + 1188*p 6 - 2860*p 8 + 5720*p 9 + 1140*p 10 - 8000*p 11 + 2266*p 12 + 3468*p 13 - 1734*p 14) + ((0) * (5720*p 1 + 2328*p 2 - 10376*p 3 + 3454*p 4 + 3468*p 5 - 4594*p 6 + 5720*p 7 + 1140*p 8 - 8000*p 9 + 2266*p 10 + 3468*p 11 - 1734*p 12) + ((0) * (- 2376*p 1 - 1672*p 2 + 5720*p 3 - 1720*p 4 - 2280*p 5 + 3406*p 6 - 4532*p 7 + 532*p 8 + 3468*p 9 - 1734*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_2_3 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 2 3 =
      10938308*p 2 - 15437014*p 4 + 17711384*p 6 - 15441688*p 8 + 9882520*p 10 - 4357066*p 12 + 1179788*p 14 - 149124*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (82) * (- 7036*p 2 + 2518*p 4 + 2072*p 6 - 4204*p 8 + 4000*p 10 - 2518*p 12 + 964*p 14 - 172*p 16) + ((-215) * (- 964*p 2 + 1886*p 4 - 2072*p 6 + 144*p 8 + 2072*p 10 - 2174*p 12 + 964*p 14 - 172*p 16) + ((1000) * (11308*p 2 - 15238*p 4 + 17096*p 6 - 15066*p 8 + 10000*p 10 - 4618*p 12 + 1308*p 14 - 172*p 16) + ((0) * (27096*p 2 - 19684*p 4 + 11308*p 6 - 4790*p 8 + 1308*p 10 - 172*p 12) + ((0) * (- 1584*p 1 - 1726*p 2 + 5036*p 3 + 1482*p 4 - 8000*p 5 - 548*p 6 + 9096*p 7 - 548*p 8 - 8000*p 9 + 1482*p 10 + 5036*p 11 - 1554*p 12 - 1928*p 13 + 792*p 14 + 344*p 15 - 172*p 16) + ((0) * (3108*p 1 + 2274*p 2 - 7656*p 3 - 720*p 4 + 9096*p 5 - 548*p 6 - 8000*p 7 + 1482*p 8 + 5036*p 9 - 1554*p 10 - 1928*p 11 + 792*p 12 + 344*p 13 - 172*p 14) + ((0) * (- 2964*p 1 - 2102*p 2 + 7168*p 3 + 244*p 4 - 7656*p 5 + 1310*p 6 + 5036*p 7 - 1554*p 8 - 1928*p 9 + 792*p 10 + 344*p 11 - 172*p 12) + ((0) * (1096*p 1 + 934*p 2 - 2964*p 3 - 72*p 4 + 3108*p 5 - 762*p 6 - 1584*p 7 + 620*p 8 + 344*p 9 - 172*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_2_4 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 2 4 =
      - 4532000*p 1 - 4477112*p 2 + 5720000*p 3 - 1759928*p 4 + 1087680*p 6 - 2376000*p 7 + 2320912*p 8 - 5416032*p 10 + 5720000*p 11 + 3748888*p 12 - 8000000*p 13 + 933464*p 14 + 3468000*p 15 - 1460028*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (82) * (4000*p 1 - 2456*p 2 - 624*p 4 + 5440*p 6 - 8000*p 7 + 3456*p 8 - 176*p 10 + 624*p 12 - 2808*p 14 + 4000*p 15 - 1684*p 16) + ((-215) * (4000*p 1 + 2808*p 2 - 8000*p 3 + 5064*p 4 - 5440*p 6 + 8000*p 7 - 4528*p 8 + 5440*p 10 - 8000*p 11 + 3992*p 12 - 2808*p 14 + 4000*p 15 - 1684*p 16) + ((1000) * (- 4000*p 1 - 3672*p 2 + 4000*p 3 - 620*p 4 - 528*p 6 + 1064*p 8 - 4232*p 10 + 4000*p 11 + 4556*p 12 - 8000*p 13 + 560*p 14 + 4000*p 15 - 1684*p 16) + ((0) * (- 4760*p 2 + 4000*p 3 + 5620*p 4 - 8000*p 5 - 3672*p 6 + 8000*p 7 + 2872*p 8 - 8000*p 9 + 560*p 10 + 4000*p 11 - 1684*p 12) + ((0) * (16984*p 1 - 3868*p 2 - 1248*p 3 + 448*p 4 + 352*p 5 - 88*p 6 - 176*p 7 - 88*p 8 + 352*p 9 + 448*p 10 - 1248*p 11 - 2184*p 12 + 9616*p 13 - 12492*p 14 + 7368*p 15 - 1684*p 16) + ((0) * (8368*p 1 - 12044*p 2 + 7720*p 3 - 1772*p 4 - 176*p 5 - 88*p 6 + 352*p 7 + 448*p 8 - 1248*p 9 - 2184*p 10 + 9616*p 11 - 12492*p 12 + 7368*p 13 - 1684*p 14) + ((0) * (- 896*p 1 - 2272*p 2 + 9440*p 3 - 12580*p 4 + 7720*p 5 - 1236*p 6 - 1248*p 7 - 2184*p 8 + 9616*p 9 - 12492*p 10 + 7368*p 11 - 1684*p 12) + ((0) * (176*p 1 + 360*p 2 - 896*p 3 - 1736*p 4 + 8368*p 5 - 14676*p 6 + 16984*p 7 - 14176*p 8 + 7368*p 9 - 1684*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_2_5 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 2 5 =
      - 3739304*p 1 - 1998556*p 2 + 5309840*p 3 - 2278480*p 4 - 2376000*p 5 + 3533736*p 6 - 765072*p 7 - 4277160*p 8 + 5720000*p 9 + 339752*p 10 - 6158160*p 11 + 4129600*p 12 + 892000*p 13 - 2322932*p 14 + 1116696*p 15 - 194208*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (82) * (1288*p 1 - 4188*p 2 + 4000*p 3 + 2240*p 4 - 8000*p 5 + 6888*p 6 - 2576*p 7 + 200*p 8 + 496*p 10 - 2240*p 12 + 4000*p 13 - 3196*p 14 + 1288*p 15 - 224*p 16) + ((-215) * (- 6712*p 1 + 3196*p 2 + 1424*p 3 - 5776*p 4 + 8000*p 5 - 6888*p 6 + 2576*p 7 + 3784*p 8 - 8000*p 9 + 6888*p 10 - 2576*p 11 - 1792*p 12 + 4000*p 13 - 3196*p 14 + 1288*p 15 - 224*p 16) + ((1000) * (- 5288*p 1 - 968*p 2 + 5288*p 3 - 3704*p 4 + 1488*p 6 - 3480*p 8 + 4000*p 9 + 1780*p 10 - 6712*p 11 + 3928*p 12 + 1424*p 13 - 2748*p 14 + 1288*p 15 - 224*p 16) + ((0) * (4000*p 1 + 3268*p 2 - 6712*p 3 + 448*p 4 + 5424*p 5 - 968*p 6 - 5424*p 7 + 3704*p 8 + 1424*p 9 - 2748*p 10 + 1288*p 11 - 224*p 12) + ((0) * (13416*p 1 - 13660*p 2 + 8480*p 3 - 1744*p 4 - 992*p 5 + 248*p 6 + 496*p 7 + 248*p 8 - 992*p 9 - 1744*p 10 + 8480*p 11 - 13436*p 12 + 11680*p 13 - 5996*p 14 + 1736*p 15 - 224*p 16) + ((0) * (20160*p 1 - 7740*p 2 + 744*p 3 + 24*p 4 + 496*p 5 + 248*p 6 - 992*p 7 - 1744*p 8 + 8480*p 9 - 13436*p 10 + 11680*p 11 - 5996*p 12 + 1736*p 13 - 224*p 14) + ((0) * (7488*p 1 - 13188*p 2 + 12176*p 3 - 5748*p 4 + 744*p 5 - 1968*p 6 + 8480*p 7 - 13436*p 8 + 11680*p 9 - 5996*p 10 + 1736*p 11 - 224*p 12) + ((0) * (- 496*p 1 - 1496*p 2 + 7488*p 3 - 15180*p 4 + 20160*p 5 - 19432*p 6 + 13416*p 7 - 6220*p 8 + 1736*p 9 - 224*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_2_6 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 2 6 =
      4838312*p 1 + 3539306*p 2 - 9063068*p 3 + 5145576*p 4 + 2662536*p 5 - 7037576*p 6 + 5662976*p 7 + 992372*p 8 - 6060920*p 9 + 3758528*p 10 + 893280*p 11 - 2021536*p 12 + 983652*p 13 - 292258*p 14 + 83232*p 15 - 13872*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (82) * (96*p 1 + 4338*p 2 - 6644*p 3 + 3168*p 4 + 1288*p 5 - 1608*p 6 - 192*p 7 + 956*p 8 - 2356*p 10 + 4000*p 11 - 3168*p 12 + 1356*p 13 - 374*p 14 + 96*p 15 - 16*p 16) + ((-215) * (- 10616*p 1 + 374*p 2 + 9164*p 3 - 11320*p 4 + 6712*p 5 + 1608*p 6 - 7808*p 7 + 7228*p 8 - 2712*p 9 - 1608*p 10 + 3808*p 11 - 3136*p 12 + 1356*p 13 - 374*p 14 + 96*p 15 - 16*p 16) + ((1000) * (2548*p 1 + 3264*p 2 - 6548*p 3 + 2452*p 4 + 4000*p 5 - 6560*p 6 + 4000*p 7 + 2468*p 8 - 6644*p 9 + 3606*p 10 + 1384*p 11 - 2436*p 12 + 1164*p 13 - 342*p 14 + 96*p 15 - 16*p 16) + ((0) * (- 2644*p 1 - 2954*p 2 + 5384*p 3 + 32*p 4 - 5480*p 5 + 3264*p 6 + 1480*p 7 - 2452*p 8 + 1164*p 9 - 342*p 10 + 96*p 11 - 16*p 12) + ((0) * (2328*p 1 - 6270*p 2 + 11692*p 3 - 13524*p 4 + 8712*p 5 - 1432*p 6 - 1848*p 7 - 1432*p 8 + 8712*p 9 - 13524*p 10 + 11692*p 11 - 6254*p 12 + 2200*p 13 - 582*p 14 + 128*p 15 - 16*p 16) + ((0) * (13892*p 1 - 14106*p 2 + 8840*p 3 - 1448*p 4 - 1848*p 5 - 1432*p 6 + 8712*p 7 - 13524*p 8 + 11692*p 9 - 6254*p 10 + 2200*p 11 - 582*p 12 + 128*p 13 - 16*p 14) + ((0) * (20404*p 1 - 7686*p 2 + 352*p 3 - 2014*p 4 + 8840*p 5 - 13540*p 6 + 11692*p 7 - 6254*p 8 + 2200*p 9 - 582*p 10 + 128*p 11 - 16*p 12) + ((0) * (6864*p 1 - 14956*p 2 + 20404*p 3 - 19778*p 4 + 13892*p 5 - 6836*p 6 + 2328*p 7 - 598*p 8 + 128*p 9 - 16*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_2_7 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 2 7 =
      - 944652*p 1 - 1600302*p 2 + 3107696*p 3 - 1505718*p 4 - 1429308*p 5 + 3279282*p 6 - 3052896*p 7 + 723904*p 8 + 1510400*p 9 - 1659906*p 10 + 743932*p 11 - 203962*p 12 + 61360*p 13 - 19074*p 14 + 3468*p 15 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (82) * (- 7996*p 1 + 5054*p 2 - 1992*p 3 + 286*p 4 + 876*p 5 - 2494*p 6 + 3992*p 7 - 4548*p 8 + 4000*p 9 - 2538*p 10 + 1036*p 11 - 286*p 12 + 80*p 13 - 22*p 14 + 4*p 15) + ((-215) * (5772*p 1 + 22*p 2 - 5856*p 3 + 8238*p 4 - 6804*p 5 + 2494*p 6 + 1936*p 7 - 3976*p 8 + 3840*p 9 - 2494*p 10 + 1028*p 11 - 286*p 12 + 80*p 13 - 22*p 14 + 4*p 15) + ((1000) * (952*p 1 - 2010*p 2 + 2012*p 3 + 242*p 4 - 2964*p 5 + 4020*p 6 - 2964*p 7 + 242*p 8 + 2008*p 9 - 1988*p 10 + 880*p 11 - 242*p 12 + 72*p 13 - 22*p 14 + 4*p 15) + ((0) * (- 956*p 1 + 2032*p 2 - 2084*p 3 + 2080*p 5 - 2010*p 6 + 884*p 7 - 242*p 8 + 72*p 9 - 22*p 10 + 4*p 11) + ((0) * (132*p 1 - 468*p 2 + 1688*p 3 - 4896*p 4 + 10112*p 5 - 15086*p 6 + 17096*p 7 - 15086*p 8 + 10112*p 9 - 4896*p 10 + 1688*p 11 - 468*p 12 + 128*p 13 - 30*p 14 + 4*p 15) + ((0) * (1816*p 1 - 4926*p 2 + 10116*p 3 - 15086*p 4 + 17096*p 5 - 15086*p 6 + 10112*p 7 - 4896*p 8 + 1688*p 9 - 468*p 10 + 128*p 11 - 30*p 12 + 4*p 13) + ((0) * (11800*p 1 - 15554*p 2 + 17224*p 3 - 15116*p 4 + 10116*p 5 - 4896*p 6 + 1688*p 7 - 468*p 8 + 128*p 9 - 30*p 10 + 4*p 11) + ((0) * (27208*p 1 - 19982*p 2 + 11800*p 3 - 5364*p 4 + 1816*p 5 - 498*p 6 + 132*p 7 - 30*p 8 + 4*p 9) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_3_0 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 3 0 =
      - 7036000*p 2 + 2518000*p 4 + 2072000*p 6 - 4204000*p 8 + 4000000*p 10 - 2518000*p 12 + 964000*p 14 - 172000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-146) * (8000*p 8 - 2000*p 16) + ((-9) * (- 4000*p 4 + 4000*p 12 - 2000*p 16) + ((241) * (4000*p 2 + 2000*p 4 - 8000*p 6 + 4000*p 8 - 2000*p 12 + 4000*p 14 - 2000*p 16) + ((1000) * (- 8000*p 2 + 2000*p 4 + 4000*p 6 - 4000*p 8 + 4000*p 10 - 2000*p 12) + ((0) * (4000*p 1 - 2000*p 2 + 4000*p 6 - 8000*p 7 + 4000*p 8 - 2000*p 14 + 4000*p 15 - 2000*p 16) + ((0) * (- 2000*p 2 + 4000*p 3 + 2000*p 4 - 8000*p 5 + 4000*p 6 - 2000*p 12 + 4000*p 13 - 2000*p 14) + ((0) * (4000*p 2 - 8000*p 3 + 2000*p 4 + 4000*p 5 - 2000*p 6 - 2000*p 10 + 4000*p 11 - 2000*p 12) + ((0) * (- 8000*p 1 + 4000*p 2 - 2000*p 6 + 4000*p 7 - 4000*p 8 + 4000*p 9 - 2000*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_3_1 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 3 1 =
      795000*p 2 + 1256500*p 4 - 2590000*p 6 + 1195000*p 8 + 1072000*p 10 - 1544500*p 12 + 723000*p 14 - 129000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-146) * (- 4000*p 4 - 2000*p 8 + 4000*p 12 - 1500*p 16) + ((-9) * (25000*p 4 - 16000*p 8 + 7000*p 12 - 1500*p 16) + ((241) * (- 5000*p 2 - 2500*p 4 + 10000*p 6 - 1000*p 8 - 8000*p 10 + 2500*p 12 + 3000*p 14 - 1500*p 16) + ((1000) * (2000*p 2 + 1500*p 4 - 5000*p 6 + 1000*p 8 + 3000*p 10 - 1500*p 12) + ((0) * (3000*p 1 + 2500*p 2 - 8000*p 3 + 4000*p 4 - 5000*p 6 + 10000*p 7 - 5000*p 8 + 4000*p 10 - 8000*p 11 + 4000*p 12 - 1500*p 14 + 3000*p 15 - 1500*p 16) + ((0) * (- 8000*p 1 + 2500*p 2 + 3000*p 3 - 6500*p 4 + 10000*p 5 - 5000*p 6 + 4000*p 8 - 8000*p 9 + 4000*p 10 - 1500*p 12 + 3000*p 13 - 1500*p 14) + ((0) * (- 8000*p 1 - 1000*p 2 + 10000*p 3 - 6500*p 4 + 3000*p 5 + 2500*p 6 - 8000*p 7 + 4000*p 8 - 1500*p 10 + 3000*p 11 - 1500*p 12) + ((0) * (10000*p 1 - 1000*p 2 - 8000*p 3 + 8000*p 4 - 8000*p 5 + 2500*p 6 + 3000*p 7 - 3000*p 8 + 3000*p 9 - 1500*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_3_2 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 3 2 =
      10938308*p 2 - 15437014*p 4 + 17711384*p 6 - 15441688*p 8 + 9882520*p 10 - 4357066*p 12 + 1179788*p 14 - 149124*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-146) * (4000*p 2 + 2860*p 4 - 8000*p 6 + 4656*p 8 - 2860*p 12 + 4000*p 14 - 1734*p 16) + ((-9) * (- 4000*p 2 - 7488*p 4 + 8000*p 6 + 3440*p 8 - 8000*p 10 + 608*p 12 + 4000*p 14 - 1734*p 16) + ((241) * (17188*p 2 - 3406*p 4 - 2376*p 6 - 1672*p 8 + 9720*p 10 - 12594*p 12 + 7468*p 14 - 1734*p 16) + ((1000) * (7344*p 2 - 14266*p 4 + 17188*p 6 - 14328*p 8 + 7468*p 10 - 1734*p 12) + ((0) * (- 4532*p 1 - 594*p 2 + 5720*p 3 - 2860*p 4 + 1188*p 6 - 2376*p 7 + 1188*p 8 - 2860*p 10 + 5720*p 11 + 1140*p 12 - 8000*p 13 + 2266*p 14 + 3468*p 15 - 1734*p 16) + ((0) * (- 2280*p 1 - 594*p 2 + 3468*p 3 - 546*p 4 - 2376*p 5 + 1188*p 6 - 2860*p 8 + 5720*p 9 + 1140*p 10 - 8000*p 11 + 2266*p 12 + 3468*p 13 - 1734*p 14) + ((0) * (5720*p 1 + 2328*p 2 - 10376*p 3 + 3454*p 4 + 3468*p 5 - 4594*p 6 + 5720*p 7 + 1140*p 8 - 8000*p 9 + 2266*p 10 + 3468*p 11 - 1734*p 12) + ((0) * (- 2376*p 1 - 1672*p 2 + 5720*p 3 - 1720*p 4 - 2280*p 5 + 3406*p 6 - 4532*p 7 + 532*p 8 + 3468*p 9 - 1734*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_3_3 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 3 3 =
      30857160*p 2 - 23740960*p 4 + 15144272*p 6 - 7808418*p 8 + 3115352*p 10 - 897744*p 12 + 165808*p 14 - 14792*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-146) * (- 7036*p 2 + 2518*p 4 + 2072*p 6 - 4204*p 8 + 4000*p 10 - 2518*p 12 + 964*p 14 - 172*p 16) + ((-9) * (- 964*p 2 + 1886*p 4 - 2072*p 6 + 144*p 8 + 2072*p 10 - 2174*p 12 + 964*p 14 - 172*p 16) + ((241) * (11308*p 2 - 15238*p 4 + 17096*p 6 - 15066*p 8 + 10000*p 10 - 4618*p 12 + 1308*p 14 - 172*p 16) + ((1000) * (27096*p 2 - 19684*p 4 + 11308*p 6 - 4790*p 8 + 1308*p 10 - 172*p 12) + ((0) * (- 1584*p 1 - 1726*p 2 + 5036*p 3 + 1482*p 4 - 8000*p 5 - 548*p 6 + 9096*p 7 - 548*p 8 - 8000*p 9 + 1482*p 10 + 5036*p 11 - 1554*p 12 - 1928*p 13 + 792*p 14 + 344*p 15 - 172*p 16) + ((0) * (3108*p 1 + 2274*p 2 - 7656*p 3 - 720*p 4 + 9096*p 5 - 548*p 6 - 8000*p 7 + 1482*p 8 + 5036*p 9 - 1554*p 10 - 1928*p 11 + 792*p 12 + 344*p 13 - 172*p 14) + ((0) * (- 2964*p 1 - 2102*p 2 + 7168*p 3 + 244*p 4 - 7656*p 5 + 1310*p 6 + 5036*p 7 - 1554*p 8 - 1928*p 9 + 792*p 10 + 344*p 11 - 172*p 12) + ((0) * (1096*p 1 + 934*p 2 - 2964*p 3 - 72*p 4 + 3108*p 5 - 762*p 6 - 1584*p 7 + 620*p 8 + 344*p 9 - 172*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_3_4 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 3 4 =
      - 1584000*p 1 - 5311648*p 2 + 5036000*p 3 + 5516108*p 4 - 8000000*p 5 - 4544528*p 6 + 9096000*p 7 + 2664600*p 8 - 8000000*p 9 - 483176*p 10 + 5036000*p 11 - 713036*p 12 - 1928000*p 13 + 570200*p 14 + 344000*p 15 - 144824*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-146) * (4000*p 1 - 2456*p 2 - 624*p 4 + 5440*p 6 - 8000*p 7 + 3456*p 8 - 176*p 10 + 624*p 12 - 2808*p 14 + 4000*p 15 - 1684*p 16) + ((-9) * (4000*p 1 + 2808*p 2 - 8000*p 3 + 5064*p 4 - 5440*p 6 + 8000*p 7 - 4528*p 8 + 5440*p 10 - 8000*p 11 + 3992*p 12 - 2808*p 14 + 4000*p 15 - 1684*p 16) + ((241) * (- 4000*p 1 - 3672*p 2 + 4000*p 3 - 620*p 4 - 528*p 6 + 1064*p 8 - 4232*p 10 + 4000*p 11 + 4556*p 12 - 8000*p 13 + 560*p 14 + 4000*p 15 - 1684*p 16) + ((1000) * (- 4760*p 2 + 4000*p 3 + 5620*p 4 - 8000*p 5 - 3672*p 6 + 8000*p 7 + 2872*p 8 - 8000*p 9 + 560*p 10 + 4000*p 11 - 1684*p 12) + ((0) * (16984*p 1 - 3868*p 2 - 1248*p 3 + 448*p 4 + 352*p 5 - 88*p 6 - 176*p 7 - 88*p 8 + 352*p 9 + 448*p 10 - 1248*p 11 - 2184*p 12 + 9616*p 13 - 12492*p 14 + 7368*p 15 - 1684*p 16) + ((0) * (8368*p 1 - 12044*p 2 + 7720*p 3 - 1772*p 4 - 176*p 5 - 88*p 6 + 352*p 7 + 448*p 8 - 1248*p 9 - 2184*p 10 + 9616*p 11 - 12492*p 12 + 7368*p 13 - 1684*p 14) + ((0) * (- 896*p 1 - 2272*p 2 + 9440*p 3 - 12580*p 4 + 7720*p 5 - 1236*p 6 - 1248*p 7 - 2184*p 8 + 9616*p 9 - 12492*p 10 + 7368*p 11 - 1684*p 12) + ((0) * (176*p 1 + 360*p 2 - 896*p 3 - 1736*p 4 + 8368*p 5 - 14676*p 6 + 16984*p 7 - 14176*p 8 + 7368*p 9 - 1684*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_3_5 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 3 5 =
      2597952*p 1 + 3617396*p 2 - 6034408*p 3 - 719720*p 4 + 6520000*p 5 - 1553048*p 6 - 5071088*p 7 + 2802064*p 8 + 2460000*p 9 - 2453428*p 10 - 306408*p 11 + 1065816*p 12 - 276816*p 13 - 166888*p 14 + 110768*p 15 - 19264*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-146) * (1288*p 1 - 4188*p 2 + 4000*p 3 + 2240*p 4 - 8000*p 5 + 6888*p 6 - 2576*p 7 + 200*p 8 + 496*p 10 - 2240*p 12 + 4000*p 13 - 3196*p 14 + 1288*p 15 - 224*p 16) + ((-9) * (- 6712*p 1 + 3196*p 2 + 1424*p 3 - 5776*p 4 + 8000*p 5 - 6888*p 6 + 2576*p 7 + 3784*p 8 - 8000*p 9 + 6888*p 10 - 2576*p 11 - 1792*p 12 + 4000*p 13 - 3196*p 14 + 1288*p 15 - 224*p 16) + ((241) * (- 5288*p 1 - 968*p 2 + 5288*p 3 - 3704*p 4 + 1488*p 6 - 3480*p 8 + 4000*p 9 + 1780*p 10 - 6712*p 11 + 3928*p 12 + 1424*p 13 - 2748*p 14 + 1288*p 15 - 224*p 16) + ((1000) * (4000*p 1 + 3268*p 2 - 6712*p 3 + 448*p 4 + 5424*p 5 - 968*p 6 - 5424*p 7 + 3704*p 8 + 1424*p 9 - 2748*p 10 + 1288*p 11 - 224*p 12) + ((0) * (13416*p 1 - 13660*p 2 + 8480*p 3 - 1744*p 4 - 992*p 5 + 248*p 6 + 496*p 7 + 248*p 8 - 992*p 9 - 1744*p 10 + 8480*p 11 - 13436*p 12 + 11680*p 13 - 5996*p 14 + 1736*p 15 - 224*p 16) + ((0) * (20160*p 1 - 7740*p 2 + 744*p 3 + 24*p 4 + 496*p 5 + 248*p 6 - 992*p 7 - 1744*p 8 + 8480*p 9 - 13436*p 10 + 11680*p 11 - 5996*p 12 + 1736*p 13 - 224*p 14) + ((0) * (7488*p 1 - 13188*p 2 + 12176*p 3 - 5748*p 4 + 744*p 5 - 1968*p 6 + 8480*p 7 - 13436*p 8 + 11680*p 9 - 5996*p 10 + 1736*p 11 - 224*p 12) + ((0) * (- 496*p 1 - 1496*p 2 + 7488*p 3 - 15180*p 4 + 20160*p 5 - 19432*p 6 + 13416*p 7 - 6220*p 8 + 1736*p 9 - 224*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_3_6 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 3 6 =
      - 1948404*p 1 - 2804090*p 2 + 4693480*p 3 + 262284*p 4 - 4764456*p 5 + 1903336*p 6 + 2542304*p 7 - 2061840*p 8 - 412796*p 9 + 885494*p 10 - 188728*p 11 - 112324*p 12 + 70344*p 13 - 24452*p 14 + 8256*p 15 - 1376*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-146) * (96*p 1 + 4338*p 2 - 6644*p 3 + 3168*p 4 + 1288*p 5 - 1608*p 6 - 192*p 7 + 956*p 8 - 2356*p 10 + 4000*p 11 - 3168*p 12 + 1356*p 13 - 374*p 14 + 96*p 15 - 16*p 16) + ((-9) * (- 10616*p 1 + 374*p 2 + 9164*p 3 - 11320*p 4 + 6712*p 5 + 1608*p 6 - 7808*p 7 + 7228*p 8 - 2712*p 9 - 1608*p 10 + 3808*p 11 - 3136*p 12 + 1356*p 13 - 374*p 14 + 96*p 15 - 16*p 16) + ((241) * (2548*p 1 + 3264*p 2 - 6548*p 3 + 2452*p 4 + 4000*p 5 - 6560*p 6 + 4000*p 7 + 2468*p 8 - 6644*p 9 + 3606*p 10 + 1384*p 11 - 2436*p 12 + 1164*p 13 - 342*p 14 + 96*p 15 - 16*p 16) + ((1000) * (- 2644*p 1 - 2954*p 2 + 5384*p 3 + 32*p 4 - 5480*p 5 + 3264*p 6 + 1480*p 7 - 2452*p 8 + 1164*p 9 - 342*p 10 + 96*p 11 - 16*p 12) + ((0) * (2328*p 1 - 6270*p 2 + 11692*p 3 - 13524*p 4 + 8712*p 5 - 1432*p 6 - 1848*p 7 - 1432*p 8 + 8712*p 9 - 13524*p 10 + 11692*p 11 - 6254*p 12 + 2200*p 13 - 582*p 14 + 128*p 15 - 16*p 16) + ((0) * (13892*p 1 - 14106*p 2 + 8840*p 3 - 1448*p 4 - 1848*p 5 - 1432*p 6 + 8712*p 7 - 13524*p 8 + 11692*p 9 - 6254*p 10 + 2200*p 11 - 582*p 12 + 128*p 13 - 16*p 14) + ((0) * (20404*p 1 - 7686*p 2 + 352*p 3 - 2014*p 4 + 8840*p 5 - 13540*p 6 + 11692*p 7 - 6254*p 8 + 2200*p 9 - 582*p 10 + 128*p 11 - 16*p 12) + ((0) * (6864*p 1 - 14956*p 2 + 20404*p 3 - 19778*p 4 + 13892*p 5 - 6836*p 6 + 2328*p 7 - 598*p 8 + 128*p 9 - 16*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_3_7 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 3 7 =
      388900*p 1 + 809508*p 2 - 1255572*p 3 - 57576*p 4 + 1299016*p 5 - 699502*p 6 - 430580*p 7 + 516114*p 8 - 62632*p 9 - 108114*p 10 + 55572*p 11 - 13992*p 12 + 4952*p 13 - 1892*p 14 + 344*p 15 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-146) * (- 7996*p 1 + 5054*p 2 - 1992*p 3 + 286*p 4 + 876*p 5 - 2494*p 6 + 3992*p 7 - 4548*p 8 + 4000*p 9 - 2538*p 10 + 1036*p 11 - 286*p 12 + 80*p 13 - 22*p 14 + 4*p 15) + ((-9) * (5772*p 1 + 22*p 2 - 5856*p 3 + 8238*p 4 - 6804*p 5 + 2494*p 6 + 1936*p 7 - 3976*p 8 + 3840*p 9 - 2494*p 10 + 1028*p 11 - 286*p 12 + 80*p 13 - 22*p 14 + 4*p 15) + ((241) * (952*p 1 - 2010*p 2 + 2012*p 3 + 242*p 4 - 2964*p 5 + 4020*p 6 - 2964*p 7 + 242*p 8 + 2008*p 9 - 1988*p 10 + 880*p 11 - 242*p 12 + 72*p 13 - 22*p 14 + 4*p 15) + ((1000) * (- 956*p 1 + 2032*p 2 - 2084*p 3 + 2080*p 5 - 2010*p 6 + 884*p 7 - 242*p 8 + 72*p 9 - 22*p 10 + 4*p 11) + ((0) * (132*p 1 - 468*p 2 + 1688*p 3 - 4896*p 4 + 10112*p 5 - 15086*p 6 + 17096*p 7 - 15086*p 8 + 10112*p 9 - 4896*p 10 + 1688*p 11 - 468*p 12 + 128*p 13 - 30*p 14 + 4*p 15) + ((0) * (1816*p 1 - 4926*p 2 + 10116*p 3 - 15086*p 4 + 17096*p 5 - 15086*p 6 + 10112*p 7 - 4896*p 8 + 1688*p 9 - 468*p 10 + 128*p 11 - 30*p 12 + 4*p 13) + ((0) * (11800*p 1 - 15554*p 2 + 17224*p 3 - 15116*p 4 + 10116*p 5 - 4896*p 6 + 1688*p 7 - 468*p 8 + 128*p 9 - 30*p 10 + 4*p 11) + ((0) * (27208*p 1 - 19982*p 2 + 11800*p 3 - 5364*p 4 + 1816*p 5 - 498*p 6 + 132*p 7 - 30*p 8 + 4*p 9) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_4_0 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 4 0 =
      4000000*p 1 - 2456000*p 2 - 624000*p 4 + 5440000*p 6 - 8000000*p 7 + 3456000*p 8 - 176000*p 10 + 624000*p 12 - 2808000*p 14 + 4000000*p 15 - 1684000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (11) * (8000*p 8 - 2000*p 16) + ((33) * (- 4000*p 4 + 4000*p 12 - 2000*p 16) + ((-202) * (4000*p 2 + 2000*p 4 - 8000*p 6 + 4000*p 8 - 2000*p 12 + 4000*p 14 - 2000*p 16) + ((-44) * (- 8000*p 2 + 2000*p 4 + 4000*p 6 - 4000*p 8 + 4000*p 10 - 2000*p 12) + ((1000) * (4000*p 1 - 2000*p 2 + 4000*p 6 - 8000*p 7 + 4000*p 8 - 2000*p 14 + 4000*p 15 - 2000*p 16) + ((0) * (- 2000*p 2 + 4000*p 3 + 2000*p 4 - 8000*p 5 + 4000*p 6 - 2000*p 12 + 4000*p 13 - 2000*p 14) + ((0) * (4000*p 2 - 8000*p 3 + 2000*p 4 + 4000*p 5 - 2000*p 6 - 2000*p 10 + 4000*p 11 - 2000*p 12) + ((0) * (- 8000*p 1 + 4000*p 2 - 2000*p 6 + 4000*p 7 - 4000*p 8 + 4000*p 9 - 2000*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_4_1 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 4 1 =
      3000000*p 1 + 3422000*p 2 - 8000000*p 3 + 5220000*p 4 - 6800000*p 6 + 10000000*p 7 - 5392000*p 8 + 5484000*p 10 - 8000000*p 11 + 3836000*p 12 - 2106000*p 14 + 3000000*p 15 - 1263000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (11) * (- 4000*p 4 - 2000*p 8 + 4000*p 12 - 1500*p 16) + ((33) * (25000*p 4 - 16000*p 8 + 7000*p 12 - 1500*p 16) + ((-202) * (- 5000*p 2 - 2500*p 4 + 10000*p 6 - 1000*p 8 - 8000*p 10 + 2500*p 12 + 3000*p 14 - 1500*p 16) + ((-44) * (2000*p 2 + 1500*p 4 - 5000*p 6 + 1000*p 8 + 3000*p 10 - 1500*p 12) + ((1000) * (3000*p 1 + 2500*p 2 - 8000*p 3 + 4000*p 4 - 5000*p 6 + 10000*p 7 - 5000*p 8 + 4000*p 10 - 8000*p 11 + 4000*p 12 - 1500*p 14 + 3000*p 15 - 1500*p 16) + ((0) * (- 8000*p 1 + 2500*p 2 + 3000*p 3 - 6500*p 4 + 10000*p 5 - 5000*p 6 + 4000*p 8 - 8000*p 9 + 4000*p 10 - 1500*p 12 + 3000*p 13 - 1500*p 14) + ((0) * (- 8000*p 1 - 1000*p 2 + 10000*p 3 - 6500*p 4 + 3000*p 5 + 2500*p 6 - 8000*p 7 + 4000*p 8 - 1500*p 10 + 3000*p 11 - 1500*p 12) + ((0) * (10000*p 1 - 1000*p 2 - 8000*p 3 + 8000*p 4 - 8000*p 5 + 2500*p 6 + 3000*p 7 - 3000*p 8 + 3000*p 9 - 1500*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_4_2 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 4 2 =
      - 4532000*p 1 - 4477112*p 2 + 5720000*p 3 - 1759928*p 4 + 1087680*p 6 - 2376000*p 7 + 2320912*p 8 - 5416032*p 10 + 5720000*p 11 + 3748888*p 12 - 8000000*p 13 + 933464*p 14 + 3468000*p 15 - 1460028*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (11) * (4000*p 2 + 2860*p 4 - 8000*p 6 + 4656*p 8 - 2860*p 12 + 4000*p 14 - 1734*p 16) + ((33) * (- 4000*p 2 - 7488*p 4 + 8000*p 6 + 3440*p 8 - 8000*p 10 + 608*p 12 + 4000*p 14 - 1734*p 16) + ((-202) * (17188*p 2 - 3406*p 4 - 2376*p 6 - 1672*p 8 + 9720*p 10 - 12594*p 12 + 7468*p 14 - 1734*p 16) + ((-44) * (7344*p 2 - 14266*p 4 + 17188*p 6 - 14328*p 8 + 7468*p 10 - 1734*p 12) + ((1000) * (- 4532*p 1 - 594*p 2 + 5720*p 3 - 2860*p 4 + 1188*p 6 - 2376*p 7 + 1188*p 8 - 2860*p 10 + 5720*p 11 + 1140*p 12 - 8000*p 13 + 2266*p 14 + 3468*p 15 - 1734*p 16) + ((0) * (- 2280*p 1 - 594*p 2 + 3468*p 3 - 546*p 4 - 2376*p 5 + 1188*p 6 - 2860*p 8 + 5720*p 9 + 1140*p 10 - 8000*p 11 + 2266*p 12 + 3468*p 13 - 1734*p 14) + ((0) * (5720*p 1 + 2328*p 2 - 10376*p 3 + 3454*p 4 + 3468*p 5 - 4594*p 6 + 5720*p 7 + 1140*p 8 - 8000*p 9 + 2266*p 10 + 3468*p 11 - 1734*p 12) + ((0) * (- 2376*p 1 - 1672*p 2 + 5720*p 3 - 1720*p 4 - 2280*p 5 + 3406*p 6 - 4532*p 7 + 532*p 8 + 3468*p 9 - 1734*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_4_3 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 4 3 =
      - 1584000*p 1 - 5311648*p 2 + 5036000*p 3 + 5516108*p 4 - 8000000*p 5 - 4544528*p 6 + 9096000*p 7 + 2664600*p 8 - 8000000*p 9 - 483176*p 10 + 5036000*p 11 - 713036*p 12 - 1928000*p 13 + 570200*p 14 + 344000*p 15 - 144824*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (11) * (- 7036*p 2 + 2518*p 4 + 2072*p 6 - 4204*p 8 + 4000*p 10 - 2518*p 12 + 964*p 14 - 172*p 16) + ((33) * (- 964*p 2 + 1886*p 4 - 2072*p 6 + 144*p 8 + 2072*p 10 - 2174*p 12 + 964*p 14 - 172*p 16) + ((-202) * (11308*p 2 - 15238*p 4 + 17096*p 6 - 15066*p 8 + 10000*p 10 - 4618*p 12 + 1308*p 14 - 172*p 16) + ((-44) * (27096*p 2 - 19684*p 4 + 11308*p 6 - 4790*p 8 + 1308*p 10 - 172*p 12) + ((1000) * (- 1584*p 1 - 1726*p 2 + 5036*p 3 + 1482*p 4 - 8000*p 5 - 548*p 6 + 9096*p 7 - 548*p 8 - 8000*p 9 + 1482*p 10 + 5036*p 11 - 1554*p 12 - 1928*p 13 + 792*p 14 + 344*p 15 - 172*p 16) + ((0) * (3108*p 1 + 2274*p 2 - 7656*p 3 - 720*p 4 + 9096*p 5 - 548*p 6 - 8000*p 7 + 1482*p 8 + 5036*p 9 - 1554*p 10 - 1928*p 11 + 792*p 12 + 344*p 13 - 172*p 14) + ((0) * (- 2964*p 1 - 2102*p 2 + 7168*p 3 + 244*p 4 - 7656*p 5 + 1310*p 6 + 5036*p 7 - 1554*p 8 - 1928*p 9 + 792*p 10 + 344*p 11 - 172*p 12) + ((0) * (1096*p 1 + 934*p 2 - 2964*p 3 - 72*p 4 + 3108*p 5 - 762*p 6 - 1584*p 7 + 620*p 8 + 344*p 9 - 172*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_4_4 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 4 4 =
      17968000*p 1 - 2851168*p 2 - 2496000*p 3 + 486208*p 4 + 704000*p 5 + 60544*p 6 - 352000*p 7 - 540704*p 8 + 704000*p 9 + 1455808*p 10 - 2496000*p 11 - 2891616*p 12 + 11232000*p 13 - 12728672*p 14 + 6736000*p 15 - 1417928*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (11) * (4000*p 1 - 2456*p 2 - 624*p 4 + 5440*p 6 - 8000*p 7 + 3456*p 8 - 176*p 10 + 624*p 12 - 2808*p 14 + 4000*p 15 - 1684*p 16) + ((33) * (4000*p 1 + 2808*p 2 - 8000*p 3 + 5064*p 4 - 5440*p 6 + 8000*p 7 - 4528*p 8 + 5440*p 10 - 8000*p 11 + 3992*p 12 - 2808*p 14 + 4000*p 15 - 1684*p 16) + ((-202) * (- 4000*p 1 - 3672*p 2 + 4000*p 3 - 620*p 4 - 528*p 6 + 1064*p 8 - 4232*p 10 + 4000*p 11 + 4556*p 12 - 8000*p 13 + 560*p 14 + 4000*p 15 - 1684*p 16) + ((-44) * (- 4760*p 2 + 4000*p 3 + 5620*p 4 - 8000*p 5 - 3672*p 6 + 8000*p 7 + 2872*p 8 - 8000*p 9 + 560*p 10 + 4000*p 11 - 1684*p 12) + ((1000) * (16984*p 1 - 3868*p 2 - 1248*p 3 + 448*p 4 + 352*p 5 - 88*p 6 - 176*p 7 - 88*p 8 + 352*p 9 + 448*p 10 - 1248*p 11 - 2184*p 12 + 9616*p 13 - 12492*p 14 + 7368*p 15 - 1684*p 16) + ((0) * (8368*p 1 - 12044*p 2 + 7720*p 3 - 1772*p 4 - 176*p 5 - 88*p 6 + 352*p 7 + 448*p 8 - 1248*p 9 - 2184*p 10 + 9616*p 11 - 12492*p 12 + 7368*p 13 - 1684*p 14) + ((0) * (- 896*p 1 - 2272*p 2 + 9440*p 3 - 12580*p 4 + 7720*p 5 - 1236*p 6 - 1248*p 7 - 2184*p 8 + 9616*p 9 - 12492*p 10 + 7368*p 11 - 1684*p 12) + ((0) * (176*p 1 + 360*p 2 - 896*p 3 - 1736*p 4 + 8368*p 5 - 14676*p 6 + 16984*p 7 - 14176*p 8 + 7368*p 9 - 1684*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_4_5 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 4 5 =
      14100848*p 1 - 13548856*p 2 + 7798144*p 3 - 1181472*p 4 - 1054656*p 5 - 161520*p 6 + 791328*p 7 + 915056*p 8 - 2126656*p 9 - 1749888*p 10 + 9694144*p 11 - 14303376*p 12 + 11568352*p 13 - 5581528*p 14 + 1532496*p 15 - 188608*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (11) * (1288*p 1 - 4188*p 2 + 4000*p 3 + 2240*p 4 - 8000*p 5 + 6888*p 6 - 2576*p 7 + 200*p 8 + 496*p 10 - 2240*p 12 + 4000*p 13 - 3196*p 14 + 1288*p 15 - 224*p 16) + ((33) * (- 6712*p 1 + 3196*p 2 + 1424*p 3 - 5776*p 4 + 8000*p 5 - 6888*p 6 + 2576*p 7 + 3784*p 8 - 8000*p 9 + 6888*p 10 - 2576*p 11 - 1792*p 12 + 4000*p 13 - 3196*p 14 + 1288*p 15 - 224*p 16) + ((-202) * (- 5288*p 1 - 968*p 2 + 5288*p 3 - 3704*p 4 + 1488*p 6 - 3480*p 8 + 4000*p 9 + 1780*p 10 - 6712*p 11 + 3928*p 12 + 1424*p 13 - 2748*p 14 + 1288*p 15 - 224*p 16) + ((-44) * (4000*p 1 + 3268*p 2 - 6712*p 3 + 448*p 4 + 5424*p 5 - 968*p 6 - 5424*p 7 + 3704*p 8 + 1424*p 9 - 2748*p 10 + 1288*p 11 - 224*p 12) + ((1000) * (13416*p 1 - 13660*p 2 + 8480*p 3 - 1744*p 4 - 992*p 5 + 248*p 6 + 496*p 7 + 248*p 8 - 992*p 9 - 1744*p 10 + 8480*p 11 - 13436*p 12 + 11680*p 13 - 5996*p 14 + 1736*p 15 - 224*p 16) + ((0) * (20160*p 1 - 7740*p 2 + 744*p 3 + 24*p 4 + 496*p 5 + 248*p 6 - 992*p 7 - 1744*p 8 + 8480*p 9 - 13436*p 10 + 11680*p 11 - 5996*p 12 + 1736*p 13 - 224*p 14) + ((0) * (7488*p 1 - 13188*p 2 + 12176*p 3 - 5748*p 4 + 744*p 5 - 1968*p 6 + 8480*p 7 - 13436*p 8 + 11680*p 9 - 5996*p 10 + 1736*p 11 - 224*p 12) + ((0) * (- 496*p 1 - 1496*p 2 + 7488*p 3 - 15180*p 4 + 20160*p 5 - 19432*p 6 + 13416*p 7 - 6220*p 8 + 1736*p 9 - 224*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_4_6 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 4 6 =
      1580368*p 1 - 6739292*p 2 + 13007128*p 3 - 14359424*p 4 + 8380784*p 5 - 215120*p 6 - 2980896*p 7 - 1573608*p 8 + 9913376*p 9 - 14316344*p 10 + 11577872*p 11 - 5899560*p 12 + 2024536*p 13 - 529372*p 14 + 112832*p 15 - 13472*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (11) * (96*p 1 + 4338*p 2 - 6644*p 3 + 3168*p 4 + 1288*p 5 - 1608*p 6 - 192*p 7 + 956*p 8 - 2356*p 10 + 4000*p 11 - 3168*p 12 + 1356*p 13 - 374*p 14 + 96*p 15 - 16*p 16) + ((33) * (- 10616*p 1 + 374*p 2 + 9164*p 3 - 11320*p 4 + 6712*p 5 + 1608*p 6 - 7808*p 7 + 7228*p 8 - 2712*p 9 - 1608*p 10 + 3808*p 11 - 3136*p 12 + 1356*p 13 - 374*p 14 + 96*p 15 - 16*p 16) + ((-202) * (2548*p 1 + 3264*p 2 - 6548*p 3 + 2452*p 4 + 4000*p 5 - 6560*p 6 + 4000*p 7 + 2468*p 8 - 6644*p 9 + 3606*p 10 + 1384*p 11 - 2436*p 12 + 1164*p 13 - 342*p 14 + 96*p 15 - 16*p 16) + ((-44) * (- 2644*p 1 - 2954*p 2 + 5384*p 3 + 32*p 4 - 5480*p 5 + 3264*p 6 + 1480*p 7 - 2452*p 8 + 1164*p 9 - 342*p 10 + 96*p 11 - 16*p 12) + ((1000) * (2328*p 1 - 6270*p 2 + 11692*p 3 - 13524*p 4 + 8712*p 5 - 1432*p 6 - 1848*p 7 - 1432*p 8 + 8712*p 9 - 13524*p 10 + 11692*p 11 - 6254*p 12 + 2200*p 13 - 582*p 14 + 128*p 15 - 16*p 16) + ((0) * (13892*p 1 - 14106*p 2 + 8840*p 3 - 1448*p 4 - 1848*p 5 - 1432*p 6 + 8712*p 7 - 13524*p 8 + 11692*p 9 - 6254*p 10 + 2200*p 11 - 582*p 12 + 128*p 13 - 16*p 14) + ((0) * (20404*p 1 - 7686*p 2 + 352*p 3 - 2014*p 4 + 8840*p 5 - 13540*p 6 + 11692*p 7 - 6254*p 8 + 2200*p 9 - 582*p 10 + 128*p 11 - 16*p 12) + ((0) * (6864*p 1 - 14956*p 2 + 20404*p 3 - 19778*p 4 + 13892*p 5 - 6836*p 6 + 2328*p 7 - 598*p 8 + 128*p 9 - 16*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_4_7 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 4 7 =
      84280*p 1 - 95068*p 2 + 1158112*p 3 - 4669884*p 4 + 10404312*p 5 - 15754732*p 6 + 17763632*p 7 - 15305472*p 8 + 9873936*p 9 - 4603676*p 10 + 1555384*p 11 - 431700*p 12 + 116976*p 13 - 26524*p 14 + 3368*p 15 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (11) * (- 7996*p 1 + 5054*p 2 - 1992*p 3 + 286*p 4 + 876*p 5 - 2494*p 6 + 3992*p 7 - 4548*p 8 + 4000*p 9 - 2538*p 10 + 1036*p 11 - 286*p 12 + 80*p 13 - 22*p 14 + 4*p 15) + ((33) * (5772*p 1 + 22*p 2 - 5856*p 3 + 8238*p 4 - 6804*p 5 + 2494*p 6 + 1936*p 7 - 3976*p 8 + 3840*p 9 - 2494*p 10 + 1028*p 11 - 286*p 12 + 80*p 13 - 22*p 14 + 4*p 15) + ((-202) * (952*p 1 - 2010*p 2 + 2012*p 3 + 242*p 4 - 2964*p 5 + 4020*p 6 - 2964*p 7 + 242*p 8 + 2008*p 9 - 1988*p 10 + 880*p 11 - 242*p 12 + 72*p 13 - 22*p 14 + 4*p 15) + ((-44) * (- 956*p 1 + 2032*p 2 - 2084*p 3 + 2080*p 5 - 2010*p 6 + 884*p 7 - 242*p 8 + 72*p 9 - 22*p 10 + 4*p 11) + ((1000) * (132*p 1 - 468*p 2 + 1688*p 3 - 4896*p 4 + 10112*p 5 - 15086*p 6 + 17096*p 7 - 15086*p 8 + 10112*p 9 - 4896*p 10 + 1688*p 11 - 468*p 12 + 128*p 13 - 30*p 14 + 4*p 15) + ((0) * (1816*p 1 - 4926*p 2 + 10116*p 3 - 15086*p 4 + 17096*p 5 - 15086*p 6 + 10112*p 7 - 4896*p 8 + 1688*p 9 - 468*p 10 + 128*p 11 - 30*p 12 + 4*p 13) + ((0) * (11800*p 1 - 15554*p 2 + 17224*p 3 - 15116*p 4 + 10116*p 5 - 4896*p 6 + 1688*p 7 - 468*p 8 + 128*p 9 - 30*p 10 + 4*p 11) + ((0) * (27208*p 1 - 19982*p 2 + 11800*p 3 - 5364*p 4 + 1816*p 5 - 498*p 6 + 132*p 7 - 30*p 8 + 4*p 9) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_5_0 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 5 0 =
      1288000*p 1 - 4188000*p 2 + 4000000*p 3 + 2240000*p 4 - 8000000*p 5 + 6888000*p 6 - 2576000*p 7 + 200000*p 8 + 496000*p 10 - 2240000*p 12 + 4000000*p 13 - 3196000*p 14 + 1288000*p 15 - 224000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-5) * (8000*p 8 - 2000*p 16) + ((-67) * (- 4000*p 4 + 4000*p 12 - 2000*p 16) + ((-138) * (4000*p 2 + 2000*p 4 - 8000*p 6 + 4000*p 8 - 2000*p 12 + 4000*p 14 - 2000*p 16) + ((124) * (- 8000*p 2 + 2000*p 4 + 4000*p 6 - 4000*p 8 + 4000*p 10 - 2000*p 12) + ((322) * (4000*p 1 - 2000*p 2 + 4000*p 6 - 8000*p 7 + 4000*p 8 - 2000*p 14 + 4000*p 15 - 2000*p 16) + ((1000) * (- 2000*p 2 + 4000*p 3 + 2000*p 4 - 8000*p 5 + 4000*p 6 - 2000*p 12 + 4000*p 13 - 2000*p 14) + ((0) * (4000*p 2 - 8000*p 3 + 2000*p 4 + 4000*p 5 - 2000*p 6 - 2000*p 10 + 4000*p 11 - 2000*p 12) + ((0) * (- 8000*p 1 + 4000*p 2 - 2000*p 6 + 4000*p 7 - 4000*p 8 + 4000*p 9 - 2000*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_5_1 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 5 1 =
      - 7034000*p 1 + 4243000*p 2 + 424000*p 3 - 6336000*p 4 + 10000000*p 5 - 8610000*p 6 + 3220000*p 7 + 3734000*p 8 - 8000000*p 9 + 6764000*p 10 - 2576000*p 11 - 1232000*p 12 + 3000000*p 13 - 2397000*p 14 + 966000*p 15 - 168000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-5) * (- 4000*p 4 - 2000*p 8 + 4000*p 12 - 1500*p 16) + ((-67) * (25000*p 4 - 16000*p 8 + 7000*p 12 - 1500*p 16) + ((-138) * (- 5000*p 2 - 2500*p 4 + 10000*p 6 - 1000*p 8 - 8000*p 10 + 2500*p 12 + 3000*p 14 - 1500*p 16) + ((124) * (2000*p 2 + 1500*p 4 - 5000*p 6 + 1000*p 8 + 3000*p 10 - 1500*p 12) + ((322) * (3000*p 1 + 2500*p 2 - 8000*p 3 + 4000*p 4 - 5000*p 6 + 10000*p 7 - 5000*p 8 + 4000*p 10 - 8000*p 11 + 4000*p 12 - 1500*p 14 + 3000*p 15 - 1500*p 16) + ((1000) * (- 8000*p 1 + 2500*p 2 + 3000*p 3 - 6500*p 4 + 10000*p 5 - 5000*p 6 + 4000*p 8 - 8000*p 9 + 4000*p 10 - 1500*p 12 + 3000*p 13 - 1500*p 14) + ((0) * (- 8000*p 1 - 1000*p 2 + 10000*p 3 - 6500*p 4 + 3000*p 5 + 2500*p 6 - 8000*p 7 + 4000*p 8 - 1500*p 10 + 3000*p 11 - 1500*p 12) + ((0) * (10000*p 1 - 1000*p 2 - 8000*p 3 + 8000*p 4 - 8000*p 5 + 2500*p 6 + 3000*p 7 - 3000*p 8 + 3000*p 9 - 1500*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_5_2 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 5 2 =
      - 3739304*p 1 - 1998556*p 2 + 5309840*p 3 - 2278480*p 4 - 2376000*p 5 + 3533736*p 6 - 765072*p 7 - 4277160*p 8 + 5720000*p 9 + 339752*p 10 - 6158160*p 11 + 4129600*p 12 + 892000*p 13 - 2322932*p 14 + 1116696*p 15 - 194208*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-5) * (4000*p 2 + 2860*p 4 - 8000*p 6 + 4656*p 8 - 2860*p 12 + 4000*p 14 - 1734*p 16) + ((-67) * (- 4000*p 2 - 7488*p 4 + 8000*p 6 + 3440*p 8 - 8000*p 10 + 608*p 12 + 4000*p 14 - 1734*p 16) + ((-138) * (17188*p 2 - 3406*p 4 - 2376*p 6 - 1672*p 8 + 9720*p 10 - 12594*p 12 + 7468*p 14 - 1734*p 16) + ((124) * (7344*p 2 - 14266*p 4 + 17188*p 6 - 14328*p 8 + 7468*p 10 - 1734*p 12) + ((322) * (- 4532*p 1 - 594*p 2 + 5720*p 3 - 2860*p 4 + 1188*p 6 - 2376*p 7 + 1188*p 8 - 2860*p 10 + 5720*p 11 + 1140*p 12 - 8000*p 13 + 2266*p 14 + 3468*p 15 - 1734*p 16) + ((1000) * (- 2280*p 1 - 594*p 2 + 3468*p 3 - 546*p 4 - 2376*p 5 + 1188*p 6 - 2860*p 8 + 5720*p 9 + 1140*p 10 - 8000*p 11 + 2266*p 12 + 3468*p 13 - 1734*p 14) + ((0) * (5720*p 1 + 2328*p 2 - 10376*p 3 + 3454*p 4 + 3468*p 5 - 4594*p 6 + 5720*p 7 + 1140*p 8 - 8000*p 9 + 2266*p 10 + 3468*p 11 - 1734*p 12) + ((0) * (- 2376*p 1 - 1672*p 2 + 5720*p 3 - 1720*p 4 - 2280*p 5 + 3406*p 6 - 4532*p 7 + 532*p 8 + 3468*p 9 - 1734*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_5_3 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 5 3 =
      2597952*p 1 + 3617396*p 2 - 6034408*p 3 - 719720*p 4 + 6520000*p 5 - 1553048*p 6 - 5071088*p 7 + 2802064*p 8 + 2460000*p 9 - 2453428*p 10 - 306408*p 11 + 1065816*p 12 - 276816*p 13 - 166888*p 14 + 110768*p 15 - 19264*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-5) * (- 7036*p 2 + 2518*p 4 + 2072*p 6 - 4204*p 8 + 4000*p 10 - 2518*p 12 + 964*p 14 - 172*p 16) + ((-67) * (- 964*p 2 + 1886*p 4 - 2072*p 6 + 144*p 8 + 2072*p 10 - 2174*p 12 + 964*p 14 - 172*p 16) + ((-138) * (11308*p 2 - 15238*p 4 + 17096*p 6 - 15066*p 8 + 10000*p 10 - 4618*p 12 + 1308*p 14 - 172*p 16) + ((124) * (27096*p 2 - 19684*p 4 + 11308*p 6 - 4790*p 8 + 1308*p 10 - 172*p 12) + ((322) * (- 1584*p 1 - 1726*p 2 + 5036*p 3 + 1482*p 4 - 8000*p 5 - 548*p 6 + 9096*p 7 - 548*p 8 - 8000*p 9 + 1482*p 10 + 5036*p 11 - 1554*p 12 - 1928*p 13 + 792*p 14 + 344*p 15 - 172*p 16) + ((1000) * (3108*p 1 + 2274*p 2 - 7656*p 3 - 720*p 4 + 9096*p 5 - 548*p 6 - 8000*p 7 + 1482*p 8 + 5036*p 9 - 1554*p 10 - 1928*p 11 + 792*p 12 + 344*p 13 - 172*p 14) + ((0) * (- 2964*p 1 - 2102*p 2 + 7168*p 3 + 244*p 4 - 7656*p 5 + 1310*p 6 + 5036*p 7 - 1554*p 8 - 1928*p 9 + 792*p 10 + 344*p 11 - 172*p 12) + ((0) * (1096*p 1 + 934*p 2 - 2964*p 3 - 72*p 4 + 3108*p 5 - 762*p 6 - 1584*p 7 + 620*p 8 + 344*p 9 - 172*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_5_4 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 5 4 =
      14100848*p 1 - 13548856*p 2 + 7798144*p 3 - 1181472*p 4 - 1054656*p 5 - 161520*p 6 + 791328*p 7 + 915056*p 8 - 2126656*p 9 - 1749888*p 10 + 9694144*p 11 - 14303376*p 12 + 11568352*p 13 - 5581528*p 14 + 1532496*p 15 - 188608*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-5) * (4000*p 1 - 2456*p 2 - 624*p 4 + 5440*p 6 - 8000*p 7 + 3456*p 8 - 176*p 10 + 624*p 12 - 2808*p 14 + 4000*p 15 - 1684*p 16) + ((-67) * (4000*p 1 + 2808*p 2 - 8000*p 3 + 5064*p 4 - 5440*p 6 + 8000*p 7 - 4528*p 8 + 5440*p 10 - 8000*p 11 + 3992*p 12 - 2808*p 14 + 4000*p 15 - 1684*p 16) + ((-138) * (- 4000*p 1 - 3672*p 2 + 4000*p 3 - 620*p 4 - 528*p 6 + 1064*p 8 - 4232*p 10 + 4000*p 11 + 4556*p 12 - 8000*p 13 + 560*p 14 + 4000*p 15 - 1684*p 16) + ((124) * (- 4760*p 2 + 4000*p 3 + 5620*p 4 - 8000*p 5 - 3672*p 6 + 8000*p 7 + 2872*p 8 - 8000*p 9 + 560*p 10 + 4000*p 11 - 1684*p 12) + ((322) * (16984*p 1 - 3868*p 2 - 1248*p 3 + 448*p 4 + 352*p 5 - 88*p 6 - 176*p 7 - 88*p 8 + 352*p 9 + 448*p 10 - 1248*p 11 - 2184*p 12 + 9616*p 13 - 12492*p 14 + 7368*p 15 - 1684*p 16) + ((1000) * (8368*p 1 - 12044*p 2 + 7720*p 3 - 1772*p 4 - 176*p 5 - 88*p 6 + 352*p 7 + 448*p 8 - 1248*p 9 - 2184*p 10 + 9616*p 11 - 12492*p 12 + 7368*p 13 - 1684*p 14) + ((0) * (- 896*p 1 - 2272*p 2 + 9440*p 3 - 12580*p 4 + 7720*p 5 - 1236*p 6 - 1248*p 7 - 2184*p 8 + 9616*p 9 - 12492*p 10 + 7368*p 11 - 1684*p 12) + ((0) * (176*p 1 + 360*p 2 - 896*p 3 - 1736*p 4 + 8368*p 5 - 14676*p 6 + 16984*p 7 - 14176*p 8 + 7368*p 9 - 1684*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_5_5 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 5 5 =
      26148960*p 1 - 11792896*p 2 + 1797120*p 3 + 404928*p 4 + 353152*p 5 + 429536*p 6 - 1664576*p 7 - 979136*p 8 + 8321152*p 9 - 15047936*p 10 + 15669120*p 11 - 10760968*p 12 + 5012448*p 13 - 1545376*p 14 + 288512*p 15 - 25088*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-5) * (1288*p 1 - 4188*p 2 + 4000*p 3 + 2240*p 4 - 8000*p 5 + 6888*p 6 - 2576*p 7 + 200*p 8 + 496*p 10 - 2240*p 12 + 4000*p 13 - 3196*p 14 + 1288*p 15 - 224*p 16) + ((-67) * (- 6712*p 1 + 3196*p 2 + 1424*p 3 - 5776*p 4 + 8000*p 5 - 6888*p 6 + 2576*p 7 + 3784*p 8 - 8000*p 9 + 6888*p 10 - 2576*p 11 - 1792*p 12 + 4000*p 13 - 3196*p 14 + 1288*p 15 - 224*p 16) + ((-138) * (- 5288*p 1 - 968*p 2 + 5288*p 3 - 3704*p 4 + 1488*p 6 - 3480*p 8 + 4000*p 9 + 1780*p 10 - 6712*p 11 + 3928*p 12 + 1424*p 13 - 2748*p 14 + 1288*p 15 - 224*p 16) + ((124) * (4000*p 1 + 3268*p 2 - 6712*p 3 + 448*p 4 + 5424*p 5 - 968*p 6 - 5424*p 7 + 3704*p 8 + 1424*p 9 - 2748*p 10 + 1288*p 11 - 224*p 12) + ((322) * (13416*p 1 - 13660*p 2 + 8480*p 3 - 1744*p 4 - 992*p 5 + 248*p 6 + 496*p 7 + 248*p 8 - 992*p 9 - 1744*p 10 + 8480*p 11 - 13436*p 12 + 11680*p 13 - 5996*p 14 + 1736*p 15 - 224*p 16) + ((1000) * (20160*p 1 - 7740*p 2 + 744*p 3 + 24*p 4 + 496*p 5 + 248*p 6 - 992*p 7 - 1744*p 8 + 8480*p 9 - 13436*p 10 + 11680*p 11 - 5996*p 12 + 1736*p 13 - 224*p 14) + ((0) * (7488*p 1 - 13188*p 2 + 12176*p 3 - 5748*p 4 + 744*p 5 - 1968*p 6 + 8480*p 7 - 13436*p 8 + 11680*p 9 - 5996*p 10 + 1736*p 11 - 224*p 12) + ((0) * (- 496*p 1 - 1496*p 2 + 7488*p 3 - 15180*p 4 + 20160*p 5 - 19432*p 6 + 13416*p 7 - 6220*p 8 + 1736*p 9 - 224*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_5_6 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 5 6 =
      14672928*p 1 - 16988416*p 2 + 13595296*p 3 - 5394536*p 4 - 730400*p 5 - 682784*p 6 + 8272560*p 7 - 15118792*p 8 + 15740176*p 9 - 11029248*p 10 + 5510600*p 11 - 2035652*p 12 + 578136*p 13 - 129280*p 14 + 21056*p 15 - 1792*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-5) * (96*p 1 + 4338*p 2 - 6644*p 3 + 3168*p 4 + 1288*p 5 - 1608*p 6 - 192*p 7 + 956*p 8 - 2356*p 10 + 4000*p 11 - 3168*p 12 + 1356*p 13 - 374*p 14 + 96*p 15 - 16*p 16) + ((-67) * (- 10616*p 1 + 374*p 2 + 9164*p 3 - 11320*p 4 + 6712*p 5 + 1608*p 6 - 7808*p 7 + 7228*p 8 - 2712*p 9 - 1608*p 10 + 3808*p 11 - 3136*p 12 + 1356*p 13 - 374*p 14 + 96*p 15 - 16*p 16) + ((-138) * (2548*p 1 + 3264*p 2 - 6548*p 3 + 2452*p 4 + 4000*p 5 - 6560*p 6 + 4000*p 7 + 2468*p 8 - 6644*p 9 + 3606*p 10 + 1384*p 11 - 2436*p 12 + 1164*p 13 - 342*p 14 + 96*p 15 - 16*p 16) + ((124) * (- 2644*p 1 - 2954*p 2 + 5384*p 3 + 32*p 4 - 5480*p 5 + 3264*p 6 + 1480*p 7 - 2452*p 8 + 1164*p 9 - 342*p 10 + 96*p 11 - 16*p 12) + ((322) * (2328*p 1 - 6270*p 2 + 11692*p 3 - 13524*p 4 + 8712*p 5 - 1432*p 6 - 1848*p 7 - 1432*p 8 + 8712*p 9 - 13524*p 10 + 11692*p 11 - 6254*p 12 + 2200*p 13 - 582*p 14 + 128*p 15 - 16*p 16) + ((1000) * (13892*p 1 - 14106*p 2 + 8840*p 3 - 1448*p 4 - 1848*p 5 - 1432*p 6 + 8712*p 7 - 13524*p 8 + 11692*p 9 - 6254*p 10 + 2200*p 11 - 582*p 12 + 128*p 13 - 16*p 14) + ((0) * (20404*p 1 - 7686*p 2 + 352*p 3 - 2014*p 4 + 8840*p 5 - 13540*p 6 + 11692*p 7 - 6254*p 8 + 2200*p 9 - 582*p 10 + 128*p 11 - 16*p 12) + ((0) * (6864*p 1 - 14956*p 2 + 20404*p 3 - 19778*p 4 + 13892*p 5 - 6836*p 6 + 2328*p 7 - 598*p 8 + 128*p 9 - 16*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_5_7 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 5 7 =
      1261840*p 1 - 4574092*p 2 + 10525776*p 3 - 17249284*p 4 + 21470504*p 5 - 20902320*p 6 + 15985888*p 7 - 9527964*p 8 + 4398608*p 9 - 1593108*p 10 + 476536*p 11 - 126708*p 12 + 29520*p 13 - 5040*p 14 + 448*p 15 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-5) * (- 7996*p 1 + 5054*p 2 - 1992*p 3 + 286*p 4 + 876*p 5 - 2494*p 6 + 3992*p 7 - 4548*p 8 + 4000*p 9 - 2538*p 10 + 1036*p 11 - 286*p 12 + 80*p 13 - 22*p 14 + 4*p 15) + ((-67) * (5772*p 1 + 22*p 2 - 5856*p 3 + 8238*p 4 - 6804*p 5 + 2494*p 6 + 1936*p 7 - 3976*p 8 + 3840*p 9 - 2494*p 10 + 1028*p 11 - 286*p 12 + 80*p 13 - 22*p 14 + 4*p 15) + ((-138) * (952*p 1 - 2010*p 2 + 2012*p 3 + 242*p 4 - 2964*p 5 + 4020*p 6 - 2964*p 7 + 242*p 8 + 2008*p 9 - 1988*p 10 + 880*p 11 - 242*p 12 + 72*p 13 - 22*p 14 + 4*p 15) + ((124) * (- 956*p 1 + 2032*p 2 - 2084*p 3 + 2080*p 5 - 2010*p 6 + 884*p 7 - 242*p 8 + 72*p 9 - 22*p 10 + 4*p 11) + ((322) * (132*p 1 - 468*p 2 + 1688*p 3 - 4896*p 4 + 10112*p 5 - 15086*p 6 + 17096*p 7 - 15086*p 8 + 10112*p 9 - 4896*p 10 + 1688*p 11 - 468*p 12 + 128*p 13 - 30*p 14 + 4*p 15) + ((1000) * (1816*p 1 - 4926*p 2 + 10116*p 3 - 15086*p 4 + 17096*p 5 - 15086*p 6 + 10112*p 7 - 4896*p 8 + 1688*p 9 - 468*p 10 + 128*p 11 - 30*p 12 + 4*p 13) + ((0) * (11800*p 1 - 15554*p 2 + 17224*p 3 - 15116*p 4 + 10116*p 5 - 4896*p 6 + 1688*p 7 - 468*p 8 + 128*p 9 - 30*p 10 + 4*p 11) + ((0) * (27208*p 1 - 19982*p 2 + 11800*p 3 - 5364*p 4 + 1816*p 5 - 498*p 6 + 132*p 7 - 30*p 8 + 4*p 9) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_6_0 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 6 0 =
      96000*p 1 + 4338000*p 2 - 6644000*p 3 + 3168000*p 4 + 1288000*p 5 - 1608000*p 6 - 192000*p 7 + 956000*p 8 - 2356000*p 10 + 4000000*p 11 - 3168000*p 12 + 1356000*p 13 - 374000*p 14 + 96000*p 15 - 16000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (19) * (8000*p 8 - 2000*p 16) + ((-123) * (- 4000*p 4 + 4000*p 12 - 2000*p 16) + ((88) * (4000*p 2 + 2000*p 4 - 8000*p 6 + 4000*p 8 - 2000*p 12 + 4000*p 14 - 2000*p 16) + ((-89) * (- 8000*p 2 + 2000*p 4 + 4000*p 6 - 4000*p 8 + 4000*p 10 - 2000*p 12) + ((24) * (4000*p 1 - 2000*p 2 + 4000*p 6 - 8000*p 7 + 4000*p 8 - 2000*p 14 + 4000*p 15 - 2000*p 16) + ((339) * (- 2000*p 2 + 4000*p 3 + 2000*p 4 - 8000*p 5 + 4000*p 6 - 2000*p 12 + 4000*p 13 - 2000*p 14) + ((1000) * (4000*p 2 - 8000*p 3 + 2000*p 4 + 4000*p 5 - 2000*p 6 - 2000*p 10 + 4000*p 11 - 2000*p 12) + ((0) * (- 8000*p 1 + 4000*p 2 - 2000*p 6 + 4000*p 7 - 4000*p 8 + 4000*p 9 - 2000*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_6_1 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 6 1 =
      - 10640000*p 1 - 710500*p 2 + 10825000*p 3 - 12112000*p 4 + 6390000*p 5 + 2010000*p 6 - 7760000*p 7 + 6989000*p 8 - 2712000*p 9 - 1019000*p 10 + 2808000*p 11 - 2344000*p 12 + 1017000*p 13 - 280500*p 14 + 72000*p 15 - 12000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (19) * (- 4000*p 4 - 2000*p 8 + 4000*p 12 - 1500*p 16) + ((-123) * (25000*p 4 - 16000*p 8 + 7000*p 12 - 1500*p 16) + ((88) * (- 5000*p 2 - 2500*p 4 + 10000*p 6 - 1000*p 8 - 8000*p 10 + 2500*p 12 + 3000*p 14 - 1500*p 16) + ((-89) * (2000*p 2 + 1500*p 4 - 5000*p 6 + 1000*p 8 + 3000*p 10 - 1500*p 12) + ((24) * (3000*p 1 + 2500*p 2 - 8000*p 3 + 4000*p 4 - 5000*p 6 + 10000*p 7 - 5000*p 8 + 4000*p 10 - 8000*p 11 + 4000*p 12 - 1500*p 14 + 3000*p 15 - 1500*p 16) + ((339) * (- 8000*p 1 + 2500*p 2 + 3000*p 3 - 6500*p 4 + 10000*p 5 - 5000*p 6 + 4000*p 8 - 8000*p 9 + 4000*p 10 - 1500*p 12 + 3000*p 13 - 1500*p 14) + ((1000) * (- 8000*p 1 - 1000*p 2 + 10000*p 3 - 6500*p 4 + 3000*p 5 + 2500*p 6 - 8000*p 7 + 4000*p 8 - 1500*p 10 + 3000*p 11 - 1500*p 12) + ((0) * (10000*p 1 - 1000*p 2 - 8000*p 3 + 8000*p 4 - 8000*p 5 + 2500*p 6 + 3000*p 7 - 3000*p 8 + 3000*p 9 - 1500*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_6_2 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 6 2 =
      4838312*p 1 + 3539306*p 2 - 9063068*p 3 + 5145576*p 4 + 2662536*p 5 - 7037576*p 6 + 5662976*p 7 + 992372*p 8 - 6060920*p 9 + 3758528*p 10 + 893280*p 11 - 2021536*p 12 + 983652*p 13 - 292258*p 14 + 83232*p 15 - 13872*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (19) * (4000*p 2 + 2860*p 4 - 8000*p 6 + 4656*p 8 - 2860*p 12 + 4000*p 14 - 1734*p 16) + ((-123) * (- 4000*p 2 - 7488*p 4 + 8000*p 6 + 3440*p 8 - 8000*p 10 + 608*p 12 + 4000*p 14 - 1734*p 16) + ((88) * (17188*p 2 - 3406*p 4 - 2376*p 6 - 1672*p 8 + 9720*p 10 - 12594*p 12 + 7468*p 14 - 1734*p 16) + ((-89) * (7344*p 2 - 14266*p 4 + 17188*p 6 - 14328*p 8 + 7468*p 10 - 1734*p 12) + ((24) * (- 4532*p 1 - 594*p 2 + 5720*p 3 - 2860*p 4 + 1188*p 6 - 2376*p 7 + 1188*p 8 - 2860*p 10 + 5720*p 11 + 1140*p 12 - 8000*p 13 + 2266*p 14 + 3468*p 15 - 1734*p 16) + ((339) * (- 2280*p 1 - 594*p 2 + 3468*p 3 - 546*p 4 - 2376*p 5 + 1188*p 6 - 2860*p 8 + 5720*p 9 + 1140*p 10 - 8000*p 11 + 2266*p 12 + 3468*p 13 - 1734*p 14) + ((1000) * (5720*p 1 + 2328*p 2 - 10376*p 3 + 3454*p 4 + 3468*p 5 - 4594*p 6 + 5720*p 7 + 1140*p 8 - 8000*p 9 + 2266*p 10 + 3468*p 11 - 1734*p 12) + ((0) * (- 2376*p 1 - 1672*p 2 + 5720*p 3 - 1720*p 4 - 2280*p 5 + 3406*p 6 - 4532*p 7 + 532*p 8 + 3468*p 9 - 1734*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_6_3 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 6 3 =
      - 1948404*p 1 - 2804090*p 2 + 4693480*p 3 + 262284*p 4 - 4764456*p 5 + 1903336*p 6 + 2542304*p 7 - 2061840*p 8 - 412796*p 9 + 885494*p 10 - 188728*p 11 - 112324*p 12 + 70344*p 13 - 24452*p 14 + 8256*p 15 - 1376*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (19) * (- 7036*p 2 + 2518*p 4 + 2072*p 6 - 4204*p 8 + 4000*p 10 - 2518*p 12 + 964*p 14 - 172*p 16) + ((-123) * (- 964*p 2 + 1886*p 4 - 2072*p 6 + 144*p 8 + 2072*p 10 - 2174*p 12 + 964*p 14 - 172*p 16) + ((88) * (11308*p 2 - 15238*p 4 + 17096*p 6 - 15066*p 8 + 10000*p 10 - 4618*p 12 + 1308*p 14 - 172*p 16) + ((-89) * (27096*p 2 - 19684*p 4 + 11308*p 6 - 4790*p 8 + 1308*p 10 - 172*p 12) + ((24) * (- 1584*p 1 - 1726*p 2 + 5036*p 3 + 1482*p 4 - 8000*p 5 - 548*p 6 + 9096*p 7 - 548*p 8 - 8000*p 9 + 1482*p 10 + 5036*p 11 - 1554*p 12 - 1928*p 13 + 792*p 14 + 344*p 15 - 172*p 16) + ((339) * (3108*p 1 + 2274*p 2 - 7656*p 3 - 720*p 4 + 9096*p 5 - 548*p 6 - 8000*p 7 + 1482*p 8 + 5036*p 9 - 1554*p 10 - 1928*p 11 + 792*p 12 + 344*p 13 - 172*p 14) + ((1000) * (- 2964*p 1 - 2102*p 2 + 7168*p 3 + 244*p 4 - 7656*p 5 + 1310*p 6 + 5036*p 7 - 1554*p 8 - 1928*p 9 + 792*p 10 + 344*p 11 - 172*p 12) + ((0) * (1096*p 1 + 934*p 2 - 2964*p 3 - 72*p 4 + 3108*p 5 - 762*p 6 - 1584*p 7 + 620*p 8 + 344*p 9 - 172*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_6_4 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 6 4 =
      1580368*p 1 - 6739292*p 2 + 13007128*p 3 - 14359424*p 4 + 8380784*p 5 - 215120*p 6 - 2980896*p 7 - 1573608*p 8 + 9913376*p 9 - 14316344*p 10 + 11577872*p 11 - 5899560*p 12 + 2024536*p 13 - 529372*p 14 + 112832*p 15 - 13472*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (19) * (4000*p 1 - 2456*p 2 - 624*p 4 + 5440*p 6 - 8000*p 7 + 3456*p 8 - 176*p 10 + 624*p 12 - 2808*p 14 + 4000*p 15 - 1684*p 16) + ((-123) * (4000*p 1 + 2808*p 2 - 8000*p 3 + 5064*p 4 - 5440*p 6 + 8000*p 7 - 4528*p 8 + 5440*p 10 - 8000*p 11 + 3992*p 12 - 2808*p 14 + 4000*p 15 - 1684*p 16) + ((88) * (- 4000*p 1 - 3672*p 2 + 4000*p 3 - 620*p 4 - 528*p 6 + 1064*p 8 - 4232*p 10 + 4000*p 11 + 4556*p 12 - 8000*p 13 + 560*p 14 + 4000*p 15 - 1684*p 16) + ((-89) * (- 4760*p 2 + 4000*p 3 + 5620*p 4 - 8000*p 5 - 3672*p 6 + 8000*p 7 + 2872*p 8 - 8000*p 9 + 560*p 10 + 4000*p 11 - 1684*p 12) + ((24) * (16984*p 1 - 3868*p 2 - 1248*p 3 + 448*p 4 + 352*p 5 - 88*p 6 - 176*p 7 - 88*p 8 + 352*p 9 + 448*p 10 - 1248*p 11 - 2184*p 12 + 9616*p 13 - 12492*p 14 + 7368*p 15 - 1684*p 16) + ((339) * (8368*p 1 - 12044*p 2 + 7720*p 3 - 1772*p 4 - 176*p 5 - 88*p 6 + 352*p 7 + 448*p 8 - 1248*p 9 - 2184*p 10 + 9616*p 11 - 12492*p 12 + 7368*p 13 - 1684*p 14) + ((1000) * (- 896*p 1 - 2272*p 2 + 9440*p 3 - 12580*p 4 + 7720*p 5 - 1236*p 6 - 1248*p 7 - 2184*p 8 + 9616*p 9 - 12492*p 10 + 7368*p 11 - 1684*p 12) + ((0) * (176*p 1 + 360*p 2 - 896*p 3 - 1736*p 4 + 8368*p 5 - 14676*p 6 + 16984*p 7 - 14176*p 8 + 7368*p 9 - 1684*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_6_5 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 6 5 =
      14672928*p 1 - 16988416*p 2 + 13595296*p 3 - 5394536*p 4 - 730400*p 5 - 682784*p 6 + 8272560*p 7 - 15118792*p 8 + 15740176*p 9 - 11029248*p 10 + 5510600*p 11 - 2035652*p 12 + 578136*p 13 - 129280*p 14 + 21056*p 15 - 1792*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (19) * (1288*p 1 - 4188*p 2 + 4000*p 3 + 2240*p 4 - 8000*p 5 + 6888*p 6 - 2576*p 7 + 200*p 8 + 496*p 10 - 2240*p 12 + 4000*p 13 - 3196*p 14 + 1288*p 15 - 224*p 16) + ((-123) * (- 6712*p 1 + 3196*p 2 + 1424*p 3 - 5776*p 4 + 8000*p 5 - 6888*p 6 + 2576*p 7 + 3784*p 8 - 8000*p 9 + 6888*p 10 - 2576*p 11 - 1792*p 12 + 4000*p 13 - 3196*p 14 + 1288*p 15 - 224*p 16) + ((88) * (- 5288*p 1 - 968*p 2 + 5288*p 3 - 3704*p 4 + 1488*p 6 - 3480*p 8 + 4000*p 9 + 1780*p 10 - 6712*p 11 + 3928*p 12 + 1424*p 13 - 2748*p 14 + 1288*p 15 - 224*p 16) + ((-89) * (4000*p 1 + 3268*p 2 - 6712*p 3 + 448*p 4 + 5424*p 5 - 968*p 6 - 5424*p 7 + 3704*p 8 + 1424*p 9 - 2748*p 10 + 1288*p 11 - 224*p 12) + ((24) * (13416*p 1 - 13660*p 2 + 8480*p 3 - 1744*p 4 - 992*p 5 + 248*p 6 + 496*p 7 + 248*p 8 - 992*p 9 - 1744*p 10 + 8480*p 11 - 13436*p 12 + 11680*p 13 - 5996*p 14 + 1736*p 15 - 224*p 16) + ((339) * (20160*p 1 - 7740*p 2 + 744*p 3 + 24*p 4 + 496*p 5 + 248*p 6 - 992*p 7 - 1744*p 8 + 8480*p 9 - 13436*p 10 + 11680*p 11 - 5996*p 12 + 1736*p 13 - 224*p 14) + ((1000) * (7488*p 1 - 13188*p 2 + 12176*p 3 - 5748*p 4 + 744*p 5 - 1968*p 6 + 8480*p 7 - 13436*p 8 + 11680*p 9 - 5996*p 10 + 1736*p 11 - 224*p 12) + ((0) * (- 496*p 1 - 1496*p 2 + 7488*p 3 - 15180*p 4 + 20160*p 5 - 19432*p 6 + 13416*p 7 - 6220*p 8 + 1736*p 9 - 224*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_6_6 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 6 6 =
      26936392*p 1 - 12031856*p 2 + 1320560*p 3 - 1163968*p 4 + 8461232*p 5 - 15155928*p 6 + 15778032*p 7 - 11308472*p 8 + 6017984*p 9 - 2525896*p 10 + 875272*p 11 - 250802*p 12 + 57600*p 13 - 10592*p 14 + 1536*p 15 - 128*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (19) * (96*p 1 + 4338*p 2 - 6644*p 3 + 3168*p 4 + 1288*p 5 - 1608*p 6 - 192*p 7 + 956*p 8 - 2356*p 10 + 4000*p 11 - 3168*p 12 + 1356*p 13 - 374*p 14 + 96*p 15 - 16*p 16) + ((-123) * (- 10616*p 1 + 374*p 2 + 9164*p 3 - 11320*p 4 + 6712*p 5 + 1608*p 6 - 7808*p 7 + 7228*p 8 - 2712*p 9 - 1608*p 10 + 3808*p 11 - 3136*p 12 + 1356*p 13 - 374*p 14 + 96*p 15 - 16*p 16) + ((88) * (2548*p 1 + 3264*p 2 - 6548*p 3 + 2452*p 4 + 4000*p 5 - 6560*p 6 + 4000*p 7 + 2468*p 8 - 6644*p 9 + 3606*p 10 + 1384*p 11 - 2436*p 12 + 1164*p 13 - 342*p 14 + 96*p 15 - 16*p 16) + ((-89) * (- 2644*p 1 - 2954*p 2 + 5384*p 3 + 32*p 4 - 5480*p 5 + 3264*p 6 + 1480*p 7 - 2452*p 8 + 1164*p 9 - 342*p 10 + 96*p 11 - 16*p 12) + ((24) * (2328*p 1 - 6270*p 2 + 11692*p 3 - 13524*p 4 + 8712*p 5 - 1432*p 6 - 1848*p 7 - 1432*p 8 + 8712*p 9 - 13524*p 10 + 11692*p 11 - 6254*p 12 + 2200*p 13 - 582*p 14 + 128*p 15 - 16*p 16) + ((339) * (13892*p 1 - 14106*p 2 + 8840*p 3 - 1448*p 4 - 1848*p 5 - 1432*p 6 + 8712*p 7 - 13524*p 8 + 11692*p 9 - 6254*p 10 + 2200*p 11 - 582*p 12 + 128*p 13 - 16*p 14) + ((1000) * (20404*p 1 - 7686*p 2 + 352*p 3 - 2014*p 4 + 8840*p 5 - 13540*p 6 + 11692*p 7 - 6254*p 8 + 2200*p 9 - 582*p 10 + 128*p 11 - 16*p 12) + ((0) * (6864*p 1 - 14956*p 2 + 20404*p 3 - 19778*p 4 + 13892*p 5 - 6836*p 6 + 2328*p 7 - 598*p 8 + 128*p 9 - 16*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_6_7 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 6 7 =
      11725772*p 1 - 17499554*p 2 + 21738808*p 3 - 21334202*p 4 + 16561816*p 5 - 10193716*p 6 + 5024484*p 7 - 2044338*p 8 + 716896*p 9 - 220602*p 10 + 58228*p 11 - 12954*p 12 + 2444*p 13 - 368*p 14 + 32*p 15 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (19) * (- 7996*p 1 + 5054*p 2 - 1992*p 3 + 286*p 4 + 876*p 5 - 2494*p 6 + 3992*p 7 - 4548*p 8 + 4000*p 9 - 2538*p 10 + 1036*p 11 - 286*p 12 + 80*p 13 - 22*p 14 + 4*p 15) + ((-123) * (5772*p 1 + 22*p 2 - 5856*p 3 + 8238*p 4 - 6804*p 5 + 2494*p 6 + 1936*p 7 - 3976*p 8 + 3840*p 9 - 2494*p 10 + 1028*p 11 - 286*p 12 + 80*p 13 - 22*p 14 + 4*p 15) + ((88) * (952*p 1 - 2010*p 2 + 2012*p 3 + 242*p 4 - 2964*p 5 + 4020*p 6 - 2964*p 7 + 242*p 8 + 2008*p 9 - 1988*p 10 + 880*p 11 - 242*p 12 + 72*p 13 - 22*p 14 + 4*p 15) + ((-89) * (- 956*p 1 + 2032*p 2 - 2084*p 3 + 2080*p 5 - 2010*p 6 + 884*p 7 - 242*p 8 + 72*p 9 - 22*p 10 + 4*p 11) + ((24) * (132*p 1 - 468*p 2 + 1688*p 3 - 4896*p 4 + 10112*p 5 - 15086*p 6 + 17096*p 7 - 15086*p 8 + 10112*p 9 - 4896*p 10 + 1688*p 11 - 468*p 12 + 128*p 13 - 30*p 14 + 4*p 15) + ((339) * (1816*p 1 - 4926*p 2 + 10116*p 3 - 15086*p 4 + 17096*p 5 - 15086*p 6 + 10112*p 7 - 4896*p 8 + 1688*p 9 - 468*p 10 + 128*p 11 - 30*p 12 + 4*p 13) + ((1000) * (11800*p 1 - 15554*p 2 + 17224*p 3 - 15116*p 4 + 10116*p 5 - 4896*p 6 + 1688*p 7 - 468*p 8 + 128*p 9 - 30*p 10 + 4*p 11) + ((0) * (27208*p 1 - 19982*p 2 + 11800*p 3 - 5364*p 4 + 1816*p 5 - 498*p 6 + 132*p 7 - 30*p 8 + 4*p 9) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_7_0 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 7 0 =
      - 7996000*p 1 + 5054000*p 2 - 1992000*p 3 + 286000*p 4 + 876000*p 5 - 2494000*p 6 + 3992000*p 7 - 4548000*p 8 + 4000000*p 9 - 2538000*p 10 + 1036000*p 11 - 286000*p 12 + 80000*p 13 - 22000*p 14 + 4000*p 15 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-74) * (8000*p 8 - 2000*p 16) + ((68) * (- 4000*p 4 + 4000*p 12 - 2000*p 16) + ((5) * (4000*p 2 + 2000*p 4 - 8000*p 6 + 4000*p 8 - 2000*p 12 + 4000*p 14 - 2000*p 16) + ((-5) * (- 8000*p 2 + 2000*p 4 + 4000*p 6 - 4000*p 8 + 4000*p 10 - 2000*p 12) + ((1) * (4000*p 1 - 2000*p 2 + 4000*p 6 - 8000*p 7 + 4000*p 8 - 2000*p 14 + 4000*p 15 - 2000*p 16) + ((20) * (- 2000*p 2 + 4000*p 3 + 2000*p 4 - 8000*p 5 + 4000*p 6 - 2000*p 12 + 4000*p 13 - 2000*p 14) + ((259) * (4000*p 2 - 8000*p 3 + 2000*p 4 + 4000*p 5 - 2000*p 6 - 2000*p 10 + 4000*p 11 - 2000*p 12) + ((1000) * (- 8000*p 1 + 4000*p 2 - 2000*p 6 + 4000*p 7 - 4000*p 8 + 4000*p 9 - 2000*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_7_1 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 7 1 =
      7771000*p 1 - 1241500*p 2 - 5358000*p 3 + 8166500*p 4 - 7023000*p 5 + 3117500*p 6 + 938000*p 7 - 2839000*p 8 + 2840000*p 9 - 1859500*p 10 + 769000*p 11 - 214500*p 12 + 60000*p 13 - 16500*p 14 + 3000*p 15 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-74) * (- 4000*p 4 - 2000*p 8 + 4000*p 12 - 1500*p 16) + ((68) * (25000*p 4 - 16000*p 8 + 7000*p 12 - 1500*p 16) + ((5) * (- 5000*p 2 - 2500*p 4 + 10000*p 6 - 1000*p 8 - 8000*p 10 + 2500*p 12 + 3000*p 14 - 1500*p 16) + ((-5) * (2000*p 2 + 1500*p 4 - 5000*p 6 + 1000*p 8 + 3000*p 10 - 1500*p 12) + ((1) * (3000*p 1 + 2500*p 2 - 8000*p 3 + 4000*p 4 - 5000*p 6 + 10000*p 7 - 5000*p 8 + 4000*p 10 - 8000*p 11 + 4000*p 12 - 1500*p 14 + 3000*p 15 - 1500*p 16) + ((20) * (- 8000*p 1 + 2500*p 2 + 3000*p 3 - 6500*p 4 + 10000*p 5 - 5000*p 6 + 4000*p 8 - 8000*p 9 + 4000*p 10 - 1500*p 12 + 3000*p 13 - 1500*p 14) + ((259) * (- 8000*p 1 - 1000*p 2 + 10000*p 3 - 6500*p 4 + 3000*p 5 + 2500*p 6 - 8000*p 7 + 4000*p 8 - 1500*p 10 + 3000*p 11 - 1500*p 12) + ((1000) * (10000*p 1 - 1000*p 2 - 8000*p 3 + 8000*p 4 - 8000*p 5 + 2500*p 6 + 3000*p 7 - 3000*p 8 + 3000*p 9 - 1500*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_7_2 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 7 2 =
      - 944652*p 1 - 1600302*p 2 + 3107696*p 3 - 1505718*p 4 - 1429308*p 5 + 3279282*p 6 - 3052896*p 7 + 723904*p 8 + 1510400*p 9 - 1659906*p 10 + 743932*p 11 - 203962*p 12 + 61360*p 13 - 19074*p 14 + 3468*p 15 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-74) * (4000*p 2 + 2860*p 4 - 8000*p 6 + 4656*p 8 - 2860*p 12 + 4000*p 14 - 1734*p 16) + ((68) * (- 4000*p 2 - 7488*p 4 + 8000*p 6 + 3440*p 8 - 8000*p 10 + 608*p 12 + 4000*p 14 - 1734*p 16) + ((5) * (17188*p 2 - 3406*p 4 - 2376*p 6 - 1672*p 8 + 9720*p 10 - 12594*p 12 + 7468*p 14 - 1734*p 16) + ((-5) * (7344*p 2 - 14266*p 4 + 17188*p 6 - 14328*p 8 + 7468*p 10 - 1734*p 12) + ((1) * (- 4532*p 1 - 594*p 2 + 5720*p 3 - 2860*p 4 + 1188*p 6 - 2376*p 7 + 1188*p 8 - 2860*p 10 + 5720*p 11 + 1140*p 12 - 8000*p 13 + 2266*p 14 + 3468*p 15 - 1734*p 16) + ((20) * (- 2280*p 1 - 594*p 2 + 3468*p 3 - 546*p 4 - 2376*p 5 + 1188*p 6 - 2860*p 8 + 5720*p 9 + 1140*p 10 - 8000*p 11 + 2266*p 12 + 3468*p 13 - 1734*p 14) + ((259) * (5720*p 1 + 2328*p 2 - 10376*p 3 + 3454*p 4 + 3468*p 5 - 4594*p 6 + 5720*p 7 + 1140*p 8 - 8000*p 9 + 2266*p 10 + 3468*p 11 - 1734*p 12) + ((1000) * (- 2376*p 1 - 1672*p 2 + 5720*p 3 - 1720*p 4 - 2280*p 5 + 3406*p 6 - 4532*p 7 + 532*p 8 + 3468*p 9 - 1734*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_7_3 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 7 3 =
      388900*p 1 + 809508*p 2 - 1255572*p 3 - 57576*p 4 + 1299016*p 5 - 699502*p 6 - 430580*p 7 + 516114*p 8 - 62632*p 9 - 108114*p 10 + 55572*p 11 - 13992*p 12 + 4952*p 13 - 1892*p 14 + 344*p 15 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-74) * (- 7036*p 2 + 2518*p 4 + 2072*p 6 - 4204*p 8 + 4000*p 10 - 2518*p 12 + 964*p 14 - 172*p 16) + ((68) * (- 964*p 2 + 1886*p 4 - 2072*p 6 + 144*p 8 + 2072*p 10 - 2174*p 12 + 964*p 14 - 172*p 16) + ((5) * (11308*p 2 - 15238*p 4 + 17096*p 6 - 15066*p 8 + 10000*p 10 - 4618*p 12 + 1308*p 14 - 172*p 16) + ((-5) * (27096*p 2 - 19684*p 4 + 11308*p 6 - 4790*p 8 + 1308*p 10 - 172*p 12) + ((1) * (- 1584*p 1 - 1726*p 2 + 5036*p 3 + 1482*p 4 - 8000*p 5 - 548*p 6 + 9096*p 7 - 548*p 8 - 8000*p 9 + 1482*p 10 + 5036*p 11 - 1554*p 12 - 1928*p 13 + 792*p 14 + 344*p 15 - 172*p 16) + ((20) * (3108*p 1 + 2274*p 2 - 7656*p 3 - 720*p 4 + 9096*p 5 - 548*p 6 - 8000*p 7 + 1482*p 8 + 5036*p 9 - 1554*p 10 - 1928*p 11 + 792*p 12 + 344*p 13 - 172*p 14) + ((259) * (- 2964*p 1 - 2102*p 2 + 7168*p 3 + 244*p 4 - 7656*p 5 + 1310*p 6 + 5036*p 7 - 1554*p 8 - 1928*p 9 + 792*p 10 + 344*p 11 - 172*p 12) + ((1000) * (1096*p 1 + 934*p 2 - 2964*p 3 - 72*p 4 + 3108*p 5 - 762*p 6 - 1584*p 7 + 620*p 8 + 344*p 9 - 172*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_7_4 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 7 4 =
      84280*p 1 - 95068*p 2 + 1158112*p 3 - 4669884*p 4 + 10404312*p 5 - 15754732*p 6 + 17763632*p 7 - 15305472*p 8 + 9873936*p 9 - 4603676*p 10 + 1555384*p 11 - 431700*p 12 + 116976*p 13 - 26524*p 14 + 3368*p 15 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-74) * (4000*p 1 - 2456*p 2 - 624*p 4 + 5440*p 6 - 8000*p 7 + 3456*p 8 - 176*p 10 + 624*p 12 - 2808*p 14 + 4000*p 15 - 1684*p 16) + ((68) * (4000*p 1 + 2808*p 2 - 8000*p 3 + 5064*p 4 - 5440*p 6 + 8000*p 7 - 4528*p 8 + 5440*p 10 - 8000*p 11 + 3992*p 12 - 2808*p 14 + 4000*p 15 - 1684*p 16) + ((5) * (- 4000*p 1 - 3672*p 2 + 4000*p 3 - 620*p 4 - 528*p 6 + 1064*p 8 - 4232*p 10 + 4000*p 11 + 4556*p 12 - 8000*p 13 + 560*p 14 + 4000*p 15 - 1684*p 16) + ((-5) * (- 4760*p 2 + 4000*p 3 + 5620*p 4 - 8000*p 5 - 3672*p 6 + 8000*p 7 + 2872*p 8 - 8000*p 9 + 560*p 10 + 4000*p 11 - 1684*p 12) + ((1) * (16984*p 1 - 3868*p 2 - 1248*p 3 + 448*p 4 + 352*p 5 - 88*p 6 - 176*p 7 - 88*p 8 + 352*p 9 + 448*p 10 - 1248*p 11 - 2184*p 12 + 9616*p 13 - 12492*p 14 + 7368*p 15 - 1684*p 16) + ((20) * (8368*p 1 - 12044*p 2 + 7720*p 3 - 1772*p 4 - 176*p 5 - 88*p 6 + 352*p 7 + 448*p 8 - 1248*p 9 - 2184*p 10 + 9616*p 11 - 12492*p 12 + 7368*p 13 - 1684*p 14) + ((259) * (- 896*p 1 - 2272*p 2 + 9440*p 3 - 12580*p 4 + 7720*p 5 - 1236*p 6 - 1248*p 7 - 2184*p 8 + 9616*p 9 - 12492*p 10 + 7368*p 11 - 1684*p 12) + ((1000) * (176*p 1 + 360*p 2 - 896*p 3 - 1736*p 4 + 8368*p 5 - 14676*p 6 + 16984*p 7 - 14176*p 8 + 7368*p 9 - 1684*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_7_5 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 7 5 =
      1261840*p 1 - 4574092*p 2 + 10525776*p 3 - 17249284*p 4 + 21470504*p 5 - 20902320*p 6 + 15985888*p 7 - 9527964*p 8 + 4398608*p 9 - 1593108*p 10 + 476536*p 11 - 126708*p 12 + 29520*p 13 - 5040*p 14 + 448*p 15 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-74) * (1288*p 1 - 4188*p 2 + 4000*p 3 + 2240*p 4 - 8000*p 5 + 6888*p 6 - 2576*p 7 + 200*p 8 + 496*p 10 - 2240*p 12 + 4000*p 13 - 3196*p 14 + 1288*p 15 - 224*p 16) + ((68) * (- 6712*p 1 + 3196*p 2 + 1424*p 3 - 5776*p 4 + 8000*p 5 - 6888*p 6 + 2576*p 7 + 3784*p 8 - 8000*p 9 + 6888*p 10 - 2576*p 11 - 1792*p 12 + 4000*p 13 - 3196*p 14 + 1288*p 15 - 224*p 16) + ((5) * (- 5288*p 1 - 968*p 2 + 5288*p 3 - 3704*p 4 + 1488*p 6 - 3480*p 8 + 4000*p 9 + 1780*p 10 - 6712*p 11 + 3928*p 12 + 1424*p 13 - 2748*p 14 + 1288*p 15 - 224*p 16) + ((-5) * (4000*p 1 + 3268*p 2 - 6712*p 3 + 448*p 4 + 5424*p 5 - 968*p 6 - 5424*p 7 + 3704*p 8 + 1424*p 9 - 2748*p 10 + 1288*p 11 - 224*p 12) + ((1) * (13416*p 1 - 13660*p 2 + 8480*p 3 - 1744*p 4 - 992*p 5 + 248*p 6 + 496*p 7 + 248*p 8 - 992*p 9 - 1744*p 10 + 8480*p 11 - 13436*p 12 + 11680*p 13 - 5996*p 14 + 1736*p 15 - 224*p 16) + ((20) * (20160*p 1 - 7740*p 2 + 744*p 3 + 24*p 4 + 496*p 5 + 248*p 6 - 992*p 7 - 1744*p 8 + 8480*p 9 - 13436*p 10 + 11680*p 11 - 5996*p 12 + 1736*p 13 - 224*p 14) + ((259) * (7488*p 1 - 13188*p 2 + 12176*p 3 - 5748*p 4 + 744*p 5 - 1968*p 6 + 8480*p 7 - 13436*p 8 + 11680*p 9 - 5996*p 10 + 1736*p 11 - 224*p 12) + ((1000) * (- 496*p 1 - 1496*p 2 + 7488*p 3 - 15180*p 4 + 20160*p 5 - 19432*p 6 + 13416*p 7 - 6220*p 8 + 1736*p 9 - 224*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_7_6 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 7 6 =
      11725772*p 1 - 17499554*p 2 + 21738808*p 3 - 21334202*p 4 + 16561816*p 5 - 10193716*p 6 + 5024484*p 7 - 2044338*p 8 + 716896*p 9 - 220602*p 10 + 58228*p 11 - 12954*p 12 + 2444*p 13 - 368*p 14 + 32*p 15 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-74) * (96*p 1 + 4338*p 2 - 6644*p 3 + 3168*p 4 + 1288*p 5 - 1608*p 6 - 192*p 7 + 956*p 8 - 2356*p 10 + 4000*p 11 - 3168*p 12 + 1356*p 13 - 374*p 14 + 96*p 15 - 16*p 16) + ((68) * (- 10616*p 1 + 374*p 2 + 9164*p 3 - 11320*p 4 + 6712*p 5 + 1608*p 6 - 7808*p 7 + 7228*p 8 - 2712*p 9 - 1608*p 10 + 3808*p 11 - 3136*p 12 + 1356*p 13 - 374*p 14 + 96*p 15 - 16*p 16) + ((5) * (2548*p 1 + 3264*p 2 - 6548*p 3 + 2452*p 4 + 4000*p 5 - 6560*p 6 + 4000*p 7 + 2468*p 8 - 6644*p 9 + 3606*p 10 + 1384*p 11 - 2436*p 12 + 1164*p 13 - 342*p 14 + 96*p 15 - 16*p 16) + ((-5) * (- 2644*p 1 - 2954*p 2 + 5384*p 3 + 32*p 4 - 5480*p 5 + 3264*p 6 + 1480*p 7 - 2452*p 8 + 1164*p 9 - 342*p 10 + 96*p 11 - 16*p 12) + ((1) * (2328*p 1 - 6270*p 2 + 11692*p 3 - 13524*p 4 + 8712*p 5 - 1432*p 6 - 1848*p 7 - 1432*p 8 + 8712*p 9 - 13524*p 10 + 11692*p 11 - 6254*p 12 + 2200*p 13 - 582*p 14 + 128*p 15 - 16*p 16) + ((20) * (13892*p 1 - 14106*p 2 + 8840*p 3 - 1448*p 4 - 1848*p 5 - 1432*p 6 + 8712*p 7 - 13524*p 8 + 11692*p 9 - 6254*p 10 + 2200*p 11 - 582*p 12 + 128*p 13 - 16*p 14) + ((259) * (20404*p 1 - 7686*p 2 + 352*p 3 - 2014*p 4 + 8840*p 5 - 13540*p 6 + 11692*p 7 - 6254*p 8 + 2200*p 9 - 582*p 10 + 128*p 11 - 16*p 12) + ((1000) * (6864*p 1 - 14956*p 2 + 20404*p 3 - 19778*p 4 + 13892*p 5 - 6836*p 6 + 2328*p 7 - 598*p 8 + 128*p 9 - 16*p 10) + (0)))))))) = _
  ring

theorem fourthLevelOddCongruenceEntry_7_7 (p : Fin 17 → ℝ) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 7 7 =
      31294392*p 1 - 24502184*p 2 + 16234704*p 3 - 9045430*p 4 + 4235360*p 5 - 1698572*p 6 + 605528*p 7 - 195614*p 8 + 55824*p 9 - 13636*p 10 + 2904*p 11 - 562*p 12 + 88*p 13 - 8*p 14 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-74) * (- 7996*p 1 + 5054*p 2 - 1992*p 3 + 286*p 4 + 876*p 5 - 2494*p 6 + 3992*p 7 - 4548*p 8 + 4000*p 9 - 2538*p 10 + 1036*p 11 - 286*p 12 + 80*p 13 - 22*p 14 + 4*p 15) + ((68) * (5772*p 1 + 22*p 2 - 5856*p 3 + 8238*p 4 - 6804*p 5 + 2494*p 6 + 1936*p 7 - 3976*p 8 + 3840*p 9 - 2494*p 10 + 1028*p 11 - 286*p 12 + 80*p 13 - 22*p 14 + 4*p 15) + ((5) * (952*p 1 - 2010*p 2 + 2012*p 3 + 242*p 4 - 2964*p 5 + 4020*p 6 - 2964*p 7 + 242*p 8 + 2008*p 9 - 1988*p 10 + 880*p 11 - 242*p 12 + 72*p 13 - 22*p 14 + 4*p 15) + ((-5) * (- 956*p 1 + 2032*p 2 - 2084*p 3 + 2080*p 5 - 2010*p 6 + 884*p 7 - 242*p 8 + 72*p 9 - 22*p 10 + 4*p 11) + ((1) * (132*p 1 - 468*p 2 + 1688*p 3 - 4896*p 4 + 10112*p 5 - 15086*p 6 + 17096*p 7 - 15086*p 8 + 10112*p 9 - 4896*p 10 + 1688*p 11 - 468*p 12 + 128*p 13 - 30*p 14 + 4*p 15) + ((20) * (1816*p 1 - 4926*p 2 + 10116*p 3 - 15086*p 4 + 17096*p 5 - 15086*p 6 + 10112*p 7 - 4896*p 8 + 1688*p 9 - 468*p 10 + 128*p 11 - 30*p 12 + 4*p 13) + ((259) * (11800*p 1 - 15554*p 2 + 17224*p 3 - 15116*p 4 + 10116*p 5 - 4896*p 6 + 1688*p 7 - 468*p 8 + 128*p 9 - 30*p 10 + 4*p 11) + ((1000) * (27208*p 1 - 19982*p 2 + 11800*p 3 - 5364*p 4 + 1816*p 5 - 498*p 6 + 132*p 7 - 30*p 8 + 4*p 9) + (0)))))))) = _
  ring

def fourthLevelOddCongruencePolynomial (p : Fin 17 → ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  ![![8000000*p 8 - 2000000*p 16,
    - 4000000*p 4 - 2000000*p 8 + 4000000*p 12 - 1500000*p 16,
    4000000*p 2 + 2860000*p 4 - 8000000*p 6 + 4656000*p 8 - 2860000*p 12 + 4000000*p 14 - 1734000*p 16,
    - 7036000*p 2 + 2518000*p 4 + 2072000*p 6 - 4204000*p 8 + 4000000*p 10 - 2518000*p 12 + 964000*p 14 - 172000*p 16,
    4000000*p 1 - 2456000*p 2 - 624000*p 4 + 5440000*p 6 - 8000000*p 7 + 3456000*p 8 - 176000*p 10 + 624000*p 12 - 2808000*p 14 + 4000000*p 15 - 1684000*p 16,
    1288000*p 1 - 4188000*p 2 + 4000000*p 3 + 2240000*p 4 - 8000000*p 5 + 6888000*p 6 - 2576000*p 7 + 200000*p 8 + 496000*p 10 - 2240000*p 12 + 4000000*p 13 - 3196000*p 14 + 1288000*p 15 - 224000*p 16,
    96000*p 1 + 4338000*p 2 - 6644000*p 3 + 3168000*p 4 + 1288000*p 5 - 1608000*p 6 - 192000*p 7 + 956000*p 8 - 2356000*p 10 + 4000000*p 11 - 3168000*p 12 + 1356000*p 13 - 374000*p 14 + 96000*p 15 - 16000*p 16,
    - 7996000*p 1 + 5054000*p 2 - 1992000*p 3 + 286000*p 4 + 876000*p 5 - 2494000*p 6 + 3992000*p 7 - 4548000*p 8 + 4000000*p 9 - 2538000*p 10 + 1036000*p 11 - 286000*p 12 + 80000*p 13 - 22000*p 14 + 4000*p 15],
  ![- 4000000*p 4 - 2000000*p 8 + 4000000*p 12 - 1500000*p 16,
    26000000*p 4 - 15500000*p 8 + 6000000*p 12 - 1125000*p 16,
    - 5000000*p 2 - 8203000*p 4 + 10000000*p 6 + 2276000*p 8 - 8000000*p 10 + 1323000*p 12 + 3000000*p 14 - 1300500*p 16,
    795000*p 2 + 1256500*p 4 - 2590000*p 6 + 1195000*p 8 + 1072000*p 10 - 1544500*p 12 + 723000*p 14 - 129000*p 16,
    3000000*p 1 + 3422000*p 2 - 8000000*p 3 + 5220000*p 4 - 6800000*p 6 + 10000000*p 7 - 5392000*p 8 + 5484000*p 10 - 8000000*p 11 + 3836000*p 12 - 2106000*p 14 + 3000000*p 15 - 1263000*p 16,
    - 7034000*p 1 + 4243000*p 2 + 424000*p 3 - 6336000*p 4 + 10000000*p 5 - 8610000*p 6 + 3220000*p 7 + 3734000*p 8 - 8000000*p 9 + 6764000*p 10 - 2576000*p 11 - 1232000*p 12 + 3000000*p 13 - 2397000*p 14 + 966000*p 15 - 168000*p 16,
    - 10640000*p 1 - 710500*p 2 + 10825000*p 3 - 12112000*p 4 + 6390000*p 5 + 2010000*p 6 - 7760000*p 7 + 6989000*p 8 - 2712000*p 9 - 1019000*p 10 + 2808000*p 11 - 2344000*p 12 + 1017000*p 13 - 280500*p 14 + 72000*p 15 - 12000*p 16,
    7771000*p 1 - 1241500*p 2 - 5358000*p 3 + 8166500*p 4 - 7023000*p 5 + 3117500*p 6 + 938000*p 7 - 2839000*p 8 + 2840000*p 9 - 1859500*p 10 + 769000*p 11 - 214500*p 12 + 60000*p 13 - 16500*p 14 + 3000*p 15],
  ![4000000*p 2 + 2860000*p 4 - 8000000*p 6 + 4656000*p 8 - 2860000*p 12 + 4000000*p 14 - 1734000*p 16,
    - 5000000*p 2 - 8203000*p 4 + 10000000*p 6 + 2276000*p 8 - 8000000*p 10 + 1323000*p 12 + 3000000*p 14 - 1300500*p 16,
    18376000*p 2 - 1561560*p 4 - 4752000*p 6 - 2029808*p 8 + 11440000*p 10 - 12959240*p 12 + 6936000*p 14 - 1503378*p 16,
    10938308*p 2 - 15437014*p 4 + 17711384*p 6 - 15441688*p 8 + 9882520*p 10 - 4357066*p 12 + 1179788*p 14 - 149124*p 16,
    - 4532000*p 1 - 4477112*p 2 + 5720000*p 3 - 1759928*p 4 + 1087680*p 6 - 2376000*p 7 + 2320912*p 8 - 5416032*p 10 + 5720000*p 11 + 3748888*p 12 - 8000000*p 13 + 933464*p 14 + 3468000*p 15 - 1460028*p 16,
    - 3739304*p 1 - 1998556*p 2 + 5309840*p 3 - 2278480*p 4 - 2376000*p 5 + 3533736*p 6 - 765072*p 7 - 4277160*p 8 + 5720000*p 9 + 339752*p 10 - 6158160*p 11 + 4129600*p 12 + 892000*p 13 - 2322932*p 14 + 1116696*p 15 - 194208*p 16,
    4838312*p 1 + 3539306*p 2 - 9063068*p 3 + 5145576*p 4 + 2662536*p 5 - 7037576*p 6 + 5662976*p 7 + 992372*p 8 - 6060920*p 9 + 3758528*p 10 + 893280*p 11 - 2021536*p 12 + 983652*p 13 - 292258*p 14 + 83232*p 15 - 13872*p 16,
    - 944652*p 1 - 1600302*p 2 + 3107696*p 3 - 1505718*p 4 - 1429308*p 5 + 3279282*p 6 - 3052896*p 7 + 723904*p 8 + 1510400*p 9 - 1659906*p 10 + 743932*p 11 - 203962*p 12 + 61360*p 13 - 19074*p 14 + 3468*p 15],
  ![- 7036000*p 2 + 2518000*p 4 + 2072000*p 6 - 4204000*p 8 + 4000000*p 10 - 2518000*p 12 + 964000*p 14 - 172000*p 16,
    795000*p 2 + 1256500*p 4 - 2590000*p 6 + 1195000*p 8 + 1072000*p 10 - 1544500*p 12 + 723000*p 14 - 129000*p 16,
    10938308*p 2 - 15437014*p 4 + 17711384*p 6 - 15441688*p 8 + 9882520*p 10 - 4357066*p 12 + 1179788*p 14 - 149124*p 16,
    30857160*p 2 - 23740960*p 4 + 15144272*p 6 - 7808418*p 8 + 3115352*p 10 - 897744*p 12 + 165808*p 14 - 14792*p 16,
    - 1584000*p 1 - 5311648*p 2 + 5036000*p 3 + 5516108*p 4 - 8000000*p 5 - 4544528*p 6 + 9096000*p 7 + 2664600*p 8 - 8000000*p 9 - 483176*p 10 + 5036000*p 11 - 713036*p 12 - 1928000*p 13 + 570200*p 14 + 344000*p 15 - 144824*p 16,
    2597952*p 1 + 3617396*p 2 - 6034408*p 3 - 719720*p 4 + 6520000*p 5 - 1553048*p 6 - 5071088*p 7 + 2802064*p 8 + 2460000*p 9 - 2453428*p 10 - 306408*p 11 + 1065816*p 12 - 276816*p 13 - 166888*p 14 + 110768*p 15 - 19264*p 16,
    - 1948404*p 1 - 2804090*p 2 + 4693480*p 3 + 262284*p 4 - 4764456*p 5 + 1903336*p 6 + 2542304*p 7 - 2061840*p 8 - 412796*p 9 + 885494*p 10 - 188728*p 11 - 112324*p 12 + 70344*p 13 - 24452*p 14 + 8256*p 15 - 1376*p 16,
    388900*p 1 + 809508*p 2 - 1255572*p 3 - 57576*p 4 + 1299016*p 5 - 699502*p 6 - 430580*p 7 + 516114*p 8 - 62632*p 9 - 108114*p 10 + 55572*p 11 - 13992*p 12 + 4952*p 13 - 1892*p 14 + 344*p 15],
  ![4000000*p 1 - 2456000*p 2 - 624000*p 4 + 5440000*p 6 - 8000000*p 7 + 3456000*p 8 - 176000*p 10 + 624000*p 12 - 2808000*p 14 + 4000000*p 15 - 1684000*p 16,
    3000000*p 1 + 3422000*p 2 - 8000000*p 3 + 5220000*p 4 - 6800000*p 6 + 10000000*p 7 - 5392000*p 8 + 5484000*p 10 - 8000000*p 11 + 3836000*p 12 - 2106000*p 14 + 3000000*p 15 - 1263000*p 16,
    - 4532000*p 1 - 4477112*p 2 + 5720000*p 3 - 1759928*p 4 + 1087680*p 6 - 2376000*p 7 + 2320912*p 8 - 5416032*p 10 + 5720000*p 11 + 3748888*p 12 - 8000000*p 13 + 933464*p 14 + 3468000*p 15 - 1460028*p 16,
    - 1584000*p 1 - 5311648*p 2 + 5036000*p 3 + 5516108*p 4 - 8000000*p 5 - 4544528*p 6 + 9096000*p 7 + 2664600*p 8 - 8000000*p 9 - 483176*p 10 + 5036000*p 11 - 713036*p 12 - 1928000*p 13 + 570200*p 14 + 344000*p 15 - 144824*p 16,
    17968000*p 1 - 2851168*p 2 - 2496000*p 3 + 486208*p 4 + 704000*p 5 + 60544*p 6 - 352000*p 7 - 540704*p 8 + 704000*p 9 + 1455808*p 10 - 2496000*p 11 - 2891616*p 12 + 11232000*p 13 - 12728672*p 14 + 6736000*p 15 - 1417928*p 16,
    14100848*p 1 - 13548856*p 2 + 7798144*p 3 - 1181472*p 4 - 1054656*p 5 - 161520*p 6 + 791328*p 7 + 915056*p 8 - 2126656*p 9 - 1749888*p 10 + 9694144*p 11 - 14303376*p 12 + 11568352*p 13 - 5581528*p 14 + 1532496*p 15 - 188608*p 16,
    1580368*p 1 - 6739292*p 2 + 13007128*p 3 - 14359424*p 4 + 8380784*p 5 - 215120*p 6 - 2980896*p 7 - 1573608*p 8 + 9913376*p 9 - 14316344*p 10 + 11577872*p 11 - 5899560*p 12 + 2024536*p 13 - 529372*p 14 + 112832*p 15 - 13472*p 16,
    84280*p 1 - 95068*p 2 + 1158112*p 3 - 4669884*p 4 + 10404312*p 5 - 15754732*p 6 + 17763632*p 7 - 15305472*p 8 + 9873936*p 9 - 4603676*p 10 + 1555384*p 11 - 431700*p 12 + 116976*p 13 - 26524*p 14 + 3368*p 15],
  ![1288000*p 1 - 4188000*p 2 + 4000000*p 3 + 2240000*p 4 - 8000000*p 5 + 6888000*p 6 - 2576000*p 7 + 200000*p 8 + 496000*p 10 - 2240000*p 12 + 4000000*p 13 - 3196000*p 14 + 1288000*p 15 - 224000*p 16,
    - 7034000*p 1 + 4243000*p 2 + 424000*p 3 - 6336000*p 4 + 10000000*p 5 - 8610000*p 6 + 3220000*p 7 + 3734000*p 8 - 8000000*p 9 + 6764000*p 10 - 2576000*p 11 - 1232000*p 12 + 3000000*p 13 - 2397000*p 14 + 966000*p 15 - 168000*p 16,
    - 3739304*p 1 - 1998556*p 2 + 5309840*p 3 - 2278480*p 4 - 2376000*p 5 + 3533736*p 6 - 765072*p 7 - 4277160*p 8 + 5720000*p 9 + 339752*p 10 - 6158160*p 11 + 4129600*p 12 + 892000*p 13 - 2322932*p 14 + 1116696*p 15 - 194208*p 16,
    2597952*p 1 + 3617396*p 2 - 6034408*p 3 - 719720*p 4 + 6520000*p 5 - 1553048*p 6 - 5071088*p 7 + 2802064*p 8 + 2460000*p 9 - 2453428*p 10 - 306408*p 11 + 1065816*p 12 - 276816*p 13 - 166888*p 14 + 110768*p 15 - 19264*p 16,
    14100848*p 1 - 13548856*p 2 + 7798144*p 3 - 1181472*p 4 - 1054656*p 5 - 161520*p 6 + 791328*p 7 + 915056*p 8 - 2126656*p 9 - 1749888*p 10 + 9694144*p 11 - 14303376*p 12 + 11568352*p 13 - 5581528*p 14 + 1532496*p 15 - 188608*p 16,
    26148960*p 1 - 11792896*p 2 + 1797120*p 3 + 404928*p 4 + 353152*p 5 + 429536*p 6 - 1664576*p 7 - 979136*p 8 + 8321152*p 9 - 15047936*p 10 + 15669120*p 11 - 10760968*p 12 + 5012448*p 13 - 1545376*p 14 + 288512*p 15 - 25088*p 16,
    14672928*p 1 - 16988416*p 2 + 13595296*p 3 - 5394536*p 4 - 730400*p 5 - 682784*p 6 + 8272560*p 7 - 15118792*p 8 + 15740176*p 9 - 11029248*p 10 + 5510600*p 11 - 2035652*p 12 + 578136*p 13 - 129280*p 14 + 21056*p 15 - 1792*p 16,
    1261840*p 1 - 4574092*p 2 + 10525776*p 3 - 17249284*p 4 + 21470504*p 5 - 20902320*p 6 + 15985888*p 7 - 9527964*p 8 + 4398608*p 9 - 1593108*p 10 + 476536*p 11 - 126708*p 12 + 29520*p 13 - 5040*p 14 + 448*p 15],
  ![96000*p 1 + 4338000*p 2 - 6644000*p 3 + 3168000*p 4 + 1288000*p 5 - 1608000*p 6 - 192000*p 7 + 956000*p 8 - 2356000*p 10 + 4000000*p 11 - 3168000*p 12 + 1356000*p 13 - 374000*p 14 + 96000*p 15 - 16000*p 16,
    - 10640000*p 1 - 710500*p 2 + 10825000*p 3 - 12112000*p 4 + 6390000*p 5 + 2010000*p 6 - 7760000*p 7 + 6989000*p 8 - 2712000*p 9 - 1019000*p 10 + 2808000*p 11 - 2344000*p 12 + 1017000*p 13 - 280500*p 14 + 72000*p 15 - 12000*p 16,
    4838312*p 1 + 3539306*p 2 - 9063068*p 3 + 5145576*p 4 + 2662536*p 5 - 7037576*p 6 + 5662976*p 7 + 992372*p 8 - 6060920*p 9 + 3758528*p 10 + 893280*p 11 - 2021536*p 12 + 983652*p 13 - 292258*p 14 + 83232*p 15 - 13872*p 16,
    - 1948404*p 1 - 2804090*p 2 + 4693480*p 3 + 262284*p 4 - 4764456*p 5 + 1903336*p 6 + 2542304*p 7 - 2061840*p 8 - 412796*p 9 + 885494*p 10 - 188728*p 11 - 112324*p 12 + 70344*p 13 - 24452*p 14 + 8256*p 15 - 1376*p 16,
    1580368*p 1 - 6739292*p 2 + 13007128*p 3 - 14359424*p 4 + 8380784*p 5 - 215120*p 6 - 2980896*p 7 - 1573608*p 8 + 9913376*p 9 - 14316344*p 10 + 11577872*p 11 - 5899560*p 12 + 2024536*p 13 - 529372*p 14 + 112832*p 15 - 13472*p 16,
    14672928*p 1 - 16988416*p 2 + 13595296*p 3 - 5394536*p 4 - 730400*p 5 - 682784*p 6 + 8272560*p 7 - 15118792*p 8 + 15740176*p 9 - 11029248*p 10 + 5510600*p 11 - 2035652*p 12 + 578136*p 13 - 129280*p 14 + 21056*p 15 - 1792*p 16,
    26936392*p 1 - 12031856*p 2 + 1320560*p 3 - 1163968*p 4 + 8461232*p 5 - 15155928*p 6 + 15778032*p 7 - 11308472*p 8 + 6017984*p 9 - 2525896*p 10 + 875272*p 11 - 250802*p 12 + 57600*p 13 - 10592*p 14 + 1536*p 15 - 128*p 16,
    11725772*p 1 - 17499554*p 2 + 21738808*p 3 - 21334202*p 4 + 16561816*p 5 - 10193716*p 6 + 5024484*p 7 - 2044338*p 8 + 716896*p 9 - 220602*p 10 + 58228*p 11 - 12954*p 12 + 2444*p 13 - 368*p 14 + 32*p 15],
  ![- 7996000*p 1 + 5054000*p 2 - 1992000*p 3 + 286000*p 4 + 876000*p 5 - 2494000*p 6 + 3992000*p 7 - 4548000*p 8 + 4000000*p 9 - 2538000*p 10 + 1036000*p 11 - 286000*p 12 + 80000*p 13 - 22000*p 14 + 4000*p 15,
    7771000*p 1 - 1241500*p 2 - 5358000*p 3 + 8166500*p 4 - 7023000*p 5 + 3117500*p 6 + 938000*p 7 - 2839000*p 8 + 2840000*p 9 - 1859500*p 10 + 769000*p 11 - 214500*p 12 + 60000*p 13 - 16500*p 14 + 3000*p 15,
    - 944652*p 1 - 1600302*p 2 + 3107696*p 3 - 1505718*p 4 - 1429308*p 5 + 3279282*p 6 - 3052896*p 7 + 723904*p 8 + 1510400*p 9 - 1659906*p 10 + 743932*p 11 - 203962*p 12 + 61360*p 13 - 19074*p 14 + 3468*p 15,
    388900*p 1 + 809508*p 2 - 1255572*p 3 - 57576*p 4 + 1299016*p 5 - 699502*p 6 - 430580*p 7 + 516114*p 8 - 62632*p 9 - 108114*p 10 + 55572*p 11 - 13992*p 12 + 4952*p 13 - 1892*p 14 + 344*p 15,
    84280*p 1 - 95068*p 2 + 1158112*p 3 - 4669884*p 4 + 10404312*p 5 - 15754732*p 6 + 17763632*p 7 - 15305472*p 8 + 9873936*p 9 - 4603676*p 10 + 1555384*p 11 - 431700*p 12 + 116976*p 13 - 26524*p 14 + 3368*p 15,
    1261840*p 1 - 4574092*p 2 + 10525776*p 3 - 17249284*p 4 + 21470504*p 5 - 20902320*p 6 + 15985888*p 7 - 9527964*p 8 + 4398608*p 9 - 1593108*p 10 + 476536*p 11 - 126708*p 12 + 29520*p 13 - 5040*p 14 + 448*p 15,
    11725772*p 1 - 17499554*p 2 + 21738808*p 3 - 21334202*p 4 + 16561816*p 5 - 10193716*p 6 + 5024484*p 7 - 2044338*p 8 + 716896*p 9 - 220602*p 10 + 58228*p 11 - 12954*p 12 + 2444*p 13 - 368*p 14 + 32*p 15,
    31294392*p 1 - 24502184*p 2 + 16234704*p 3 - 9045430*p 4 + 4235360*p 5 - 1698572*p 6 + 605528*p 7 - 195614*p 8 + 55824*p 9 - 13636*p 10 + 2904*p 11 - 562*p 12 + 88*p 13 - 8*p 14]]

theorem fourthLevelOddCongruence_row0 (p : Fin 17 → ℝ) (j : Fin 8) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 0 j =
      fourthLevelOddCongruencePolynomial p 0 j := by
  fin_cases j
  · exact fourthLevelOddCongruenceEntry_0_0 p
  · exact fourthLevelOddCongruenceEntry_0_1 p
  · exact fourthLevelOddCongruenceEntry_0_2 p
  · exact fourthLevelOddCongruenceEntry_0_3 p
  · exact fourthLevelOddCongruenceEntry_0_4 p
  · exact fourthLevelOddCongruenceEntry_0_5 p
  · exact fourthLevelOddCongruenceEntry_0_6 p
  · exact fourthLevelOddCongruenceEntry_0_7 p

theorem fourthLevelOddCongruence_row1 (p : Fin 17 → ℝ) (j : Fin 8) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 1 j =
      fourthLevelOddCongruencePolynomial p 1 j := by
  fin_cases j
  · exact fourthLevelOddCongruenceEntry_1_0 p
  · exact fourthLevelOddCongruenceEntry_1_1 p
  · exact fourthLevelOddCongruenceEntry_1_2 p
  · exact fourthLevelOddCongruenceEntry_1_3 p
  · exact fourthLevelOddCongruenceEntry_1_4 p
  · exact fourthLevelOddCongruenceEntry_1_5 p
  · exact fourthLevelOddCongruenceEntry_1_6 p
  · exact fourthLevelOddCongruenceEntry_1_7 p

theorem fourthLevelOddCongruence_row2 (p : Fin 17 → ℝ) (j : Fin 8) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 2 j =
      fourthLevelOddCongruencePolynomial p 2 j := by
  fin_cases j
  · exact fourthLevelOddCongruenceEntry_2_0 p
  · exact fourthLevelOddCongruenceEntry_2_1 p
  · exact fourthLevelOddCongruenceEntry_2_2 p
  · exact fourthLevelOddCongruenceEntry_2_3 p
  · exact fourthLevelOddCongruenceEntry_2_4 p
  · exact fourthLevelOddCongruenceEntry_2_5 p
  · exact fourthLevelOddCongruenceEntry_2_6 p
  · exact fourthLevelOddCongruenceEntry_2_7 p

theorem fourthLevelOddCongruence_row3 (p : Fin 17 → ℝ) (j : Fin 8) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 3 j =
      fourthLevelOddCongruencePolynomial p 3 j := by
  fin_cases j
  · exact fourthLevelOddCongruenceEntry_3_0 p
  · exact fourthLevelOddCongruenceEntry_3_1 p
  · exact fourthLevelOddCongruenceEntry_3_2 p
  · exact fourthLevelOddCongruenceEntry_3_3 p
  · exact fourthLevelOddCongruenceEntry_3_4 p
  · exact fourthLevelOddCongruenceEntry_3_5 p
  · exact fourthLevelOddCongruenceEntry_3_6 p
  · exact fourthLevelOddCongruenceEntry_3_7 p

theorem fourthLevelOddCongruence_row4 (p : Fin 17 → ℝ) (j : Fin 8) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 4 j =
      fourthLevelOddCongruencePolynomial p 4 j := by
  fin_cases j
  · exact fourthLevelOddCongruenceEntry_4_0 p
  · exact fourthLevelOddCongruenceEntry_4_1 p
  · exact fourthLevelOddCongruenceEntry_4_2 p
  · exact fourthLevelOddCongruenceEntry_4_3 p
  · exact fourthLevelOddCongruenceEntry_4_4 p
  · exact fourthLevelOddCongruenceEntry_4_5 p
  · exact fourthLevelOddCongruenceEntry_4_6 p
  · exact fourthLevelOddCongruenceEntry_4_7 p

theorem fourthLevelOddCongruence_row5 (p : Fin 17 → ℝ) (j : Fin 8) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 5 j =
      fourthLevelOddCongruencePolynomial p 5 j := by
  fin_cases j
  · exact fourthLevelOddCongruenceEntry_5_0 p
  · exact fourthLevelOddCongruenceEntry_5_1 p
  · exact fourthLevelOddCongruenceEntry_5_2 p
  · exact fourthLevelOddCongruenceEntry_5_3 p
  · exact fourthLevelOddCongruenceEntry_5_4 p
  · exact fourthLevelOddCongruenceEntry_5_5 p
  · exact fourthLevelOddCongruenceEntry_5_6 p
  · exact fourthLevelOddCongruenceEntry_5_7 p

theorem fourthLevelOddCongruence_row6 (p : Fin 17 → ℝ) (j : Fin 8) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 6 j =
      fourthLevelOddCongruencePolynomial p 6 j := by
  fin_cases j
  · exact fourthLevelOddCongruenceEntry_6_0 p
  · exact fourthLevelOddCongruenceEntry_6_1 p
  · exact fourthLevelOddCongruenceEntry_6_2 p
  · exact fourthLevelOddCongruenceEntry_6_3 p
  · exact fourthLevelOddCongruenceEntry_6_4 p
  · exact fourthLevelOddCongruenceEntry_6_5 p
  · exact fourthLevelOddCongruenceEntry_6_6 p
  · exact fourthLevelOddCongruenceEntry_6_7 p

theorem fourthLevelOddCongruence_row7 (p : Fin 17 → ℝ) (j : Fin 8) :
    (fourthLevelOddShearNumerator.transpose * fourthLevelOddRightPolynomial p) 7 j =
      fourthLevelOddCongruencePolynomial p 7 j := by
  fin_cases j
  · exact fourthLevelOddCongruenceEntry_7_0 p
  · exact fourthLevelOddCongruenceEntry_7_1 p
  · exact fourthLevelOddCongruenceEntry_7_2 p
  · exact fourthLevelOddCongruenceEntry_7_3 p
  · exact fourthLevelOddCongruenceEntry_7_4 p
  · exact fourthLevelOddCongruenceEntry_7_5 p
  · exact fourthLevelOddCongruenceEntry_7_6 p
  · exact fourthLevelOddCongruenceEntry_7_7 p

theorem fourthLevelOddCongruence_eq (p : Fin 17 → ℝ) :
    fourthLevelOddShearNumerator.transpose * fourthLevelOddPolynomial p *
        fourthLevelOddShearNumerator =
      fourthLevelOddCongruencePolynomial p := by
  rw [Matrix.mul_assoc, fourthLevelOddRight_eq]
  ext i j
  fin_cases i
  · exact fourthLevelOddCongruence_row0 p j
  · exact fourthLevelOddCongruence_row1 p j
  · exact fourthLevelOddCongruence_row2 p j
  · exact fourthLevelOddCongruence_row3 p j
  · exact fourthLevelOddCongruence_row4 p j
  · exact fourthLevelOddCongruence_row5 p j
  · exact fourthLevelOddCongruence_row6 p j
  · exact fourthLevelOddCongruence_row7 p j

theorem fourthLevelEvenCongruenceEntry_0_0 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 0 0 =
      8000000*p 4 + 8000000*p 8 - 8000000*p 12 + 2000000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (1000) * (8000*p 4 + 8000*p 8 - 8000*p 12 + 2000*p 16) + ((0) * (- 4000*p 2 + 2000*p 4 - 4000*p 8 + 8000*p 10 - 2000*p 12 - 4000*p 14 + 2000*p 16) + ((0) * (- 8000*p 2 - 2000*p 4 + 12000*p 6 - 4000*p 8 - 4000*p 10 + 2000*p 12) + ((0) * (4000*p 1 + 2000*p 2 - 8000*p 3 + 4000*p 4 - 4000*p 10 + 8000*p 11 - 4000*p 12 + 2000*p 14 - 4000*p 15 + 2000*p 16) + ((0) * (- 8000*p 1 + 2000*p 2 + 4000*p 3 - 2000*p 4 - 4000*p 8 + 8000*p 9 - 4000*p 10 + 2000*p 12 - 4000*p 13 + 2000*p 14) + ((0) * (- 8000*p 1 + 4000*p 2 - 2000*p 4 + 4000*p 5 - 6000*p 6 + 8000*p 7 - 4000*p 8 + 2000*p 10 - 4000*p 11 + 2000*p 12) + ((0) * (4000*p 2 - 8000*p 3 + 8000*p 5 - 6000*p 6 + 4000*p 7 - 4000*p 9 + 2000*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_0_1 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 0 1 =
      - 4000000*p 2 + 600000*p 4 - 5400000*p 8 + 8000000*p 10 - 600000*p 12 - 4000000*p 14 + 1650000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (1000) * (- 4000*p 2 + 600*p 4 - 5400*p 8 + 8000*p 10 - 600*p 12 - 4000*p 14 + 1650*p 16) + ((0) * (16700*p 2 - 4350*p 4 + 2700*p 8 - 9400*p 10 + 12350*p 12 - 7300*p 14 + 1650*p 16) + ((0) * (9400*p 2 - 9650*p 4 - 2100*p 6 + 10700*p 8 - 7300*p 10 + 1650*p 12) + ((0) * (- 4700*p 1 - 350*p 2 + 5400*p 3 - 2700*p 4 + 2700*p 10 - 5400*p 11 - 1300*p 12 + 8000*p 13 - 2350*p 14 - 3300*p 15 + 1650*p 16) + ((0) * (- 2600*p 1 - 350*p 2 + 3300*p 3 - 1650*p 4 + 2700*p 8 - 5400*p 9 - 1300*p 10 + 8000*p 11 - 2350*p 12 - 3300*p 13 + 1650*p 14) + ((0) * (5400*p 1 + 1300*p 2 - 8000*p 3 + 2350*p 4 + 3300*p 5 + 1050*p 6 - 5400*p 7 - 1300*p 8 + 8000*p 9 - 2350*p 10 - 3300*p 11 + 1650*p 12) + ((0) * (- 2700*p 2 + 5400*p 3 + 4000*p 4 - 13400*p 5 + 1050*p 6 + 11300*p 7 - 4000*p 8 - 3300*p 9 + 1650*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_0_2 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 0 2 =
      - 9564000*p 2 - 3290000*p 4 + 12000000*p 6 - 7636000*p 8 - 872000*p 10 + 3290000*p 12 - 1564000*p 14 + 264000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (1000) * (- 9564*p 2 - 3290*p 4 + 12000*p 6 - 7636*p 8 - 872*p 10 + 3290*p 12 - 1564*p 14 + 264*p 16) + ((0) * (15292*p 2 - 12082*p 4 + 11818*p 8 - 13200*p 10 + 7210*p 12 - 2092*p 14 + 264*p 16) + ((0) * (13200*p 2 + 4608*p 4 - 11108*p 6 + 6946*p 8 - 2092*p 10 + 264*p 12) + ((0) * (- 2600*p 1 - 2518*p 2 + 7636*p 3 + 182*p 4 - 8000*p 5 + 4000*p 6 - 4000*p 8 + 8000*p 9 - 182*p 10 - 7636*p 11 + 2254*p 12 + 3128*p 13 - 1300*p 14 - 528*p 15 + 264*p 16) + ((0) * (4508*p 1 + 1482*p 2 - 7472*p 3 + 3736*p 4 - 4000*p 6 + 8000*p 7 - 182*p 8 - 7636*p 9 + 2254*p 10 + 3128*p 11 - 1300*p 12 - 528*p 13 + 264*p 14) + ((0) * (- 364*p 1 + 1746*p 2 - 3128*p 3 - 2700*p 4 + 8528*p 5 - 446*p 6 - 7636*p 7 + 2254*p 8 + 3128*p 9 - 1300*p 10 - 528*p 11 + 264*p 12) + ((0) * (- 8000*p 1 - 3818*p 2 + 15636*p 3 - 2436*p 4 - 10764*p 5 + 3554*p 6 + 3656*p 7 - 1564*p 8 - 528*p 9 + 264*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_0_3 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 0 3 =
      4000000*p 1 + 3208000*p 2 - 8000000*p 3 + 3860000*p 4 - 480000*p 6 + 1272000*p 8 - 5616000*p 10 + 8000000*p 11 - 3860000*p 12 + 2888000*p 14 - 4000000*p 15 + 1612000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (1000) * (4000*p 1 + 3208*p 2 - 8000*p 3 + 3860*p 4 - 480*p 6 + 1272*p 8 - 5616*p 10 + 8000*p 11 - 3860*p 12 + 2888*p 14 - 4000*p 15 + 1612*p 16) + ((0) * (- 4000*p 1 - 3984*p 2 + 4000*p 3 - 656*p 4 - 956*p 8 + 4320*p 10 - 4000*p 11 - 4800*p 12 + 8000*p 13 - 336*p 14 - 4000*p 15 + 1612*p 16) + ((0) * (- 4320*p 2 + 4000*p 3 + 3844*p 4 - 8000*p 5 + 4656*p 6 - 6412*p 8 + 8000*p 9 - 336*p 10 - 4000*p 11 + 1612*p 12) + ((0) * (17000*p 1 - 3864*p 2 - 1272*p 3 + 476*p 4 + 320*p 5 - 160*p 6 + 160*p 8 - 320*p 9 - 476*p 10 + 1272*p 11 + 2252*p 12 - 9776*p 13 + 12500*p 14 - 7224*p 15 + 1612*p 16) + ((0) * (8504*p 1 - 12024*p 2 + 7544*p 3 - 1772*p 4 + 160*p 6 - 320*p 7 - 476*p 8 + 1272*p 9 + 2252*p 10 - 9776*p 11 + 12500*p 12 - 7224*p 13 + 1612*p 14) + ((0) * (- 952*p 1 - 2412*p 2 + 9776*p 3 - 12340*p 4 + 6904*p 5 - 2088*p 6 + 1272*p 7 + 2252*p 8 - 9776*p 9 + 12500*p 10 - 7224*p 11 + 1612*p 12) + ((0) * (320*p 1 + 636*p 2 - 1592*p 3 - 2728*p 4 + 11048*p 5 - 10248*p 6 - 2552*p 7 + 10888*p 8 - 7224*p 9 + 1612*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_0_4 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 0 4 =
      - 6720000*p 1 + 2336000*p 2 + 1440000*p 3 - 1792000*p 4 + 1296000*p 6 - 4448000*p 8 + 8000000*p 9 - 6832000*p 10 + 2560000*p 11 + 1792000*p 12 - 4000000*p 13 + 3200000*p 14 - 1280000*p 15 + 216000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (1000) * (- 6720*p 1 + 2336*p 2 + 1440*p 3 - 1792*p 4 + 1296*p 6 - 4448*p 8 + 8000*p 9 - 6832*p 10 + 2560*p 11 + 1792*p 12 - 4000*p 13 + 3200*p 14 - 1280*p 15 + 216*p 16) + ((0) * (- 5280*p 1 - 1088*p 2 + 5280*p 3 - 3304*p 4 + 3088*p 8 - 4000*p 9 - 1680*p 10 + 6720*p 11 - 3960*p 12 - 1440*p 13 + 2768*p 14 - 1280*p 15 + 216*p 16) + ((0) * (4000*p 1 + 1680*p 2 - 6720*p 3 + 7048*p 4 - 2560*p 5 - 4448*p 6 + 8000*p 7 - 4176*p 8 - 1440*p 9 + 2768*p 10 - 1280*p 11 + 216*p 12) + ((0) * (13392*p 1 - 13640*p 2 + 8448*p 3 - 1792*p 4 - 864*p 5 + 432*p 6 - 432*p 8 + 864*p 9 + 1792*p 10 - 8448*p 11 + 13424*p 12 - 11680*p 13 + 5976*p 14 - 1712*p 15 + 216*p 16) + ((0) * (20128*p 1 - 7768*p 2 + 848*p 3 + 216*p 4 - 432*p 6 + 864*p 7 + 1792*p 8 - 8448*p 9 + 13424*p 10 - 11680*p 11 + 5976*p 12 - 1712*p 13 + 216*p 14) + ((0) * (7584*p 1 - 12992*p 2 + 11680*p 3 - 6408*p 4 + 2576*p 5 + 1576*p 6 - 8448*p 7 + 13424*p 8 - 11680*p 9 + 5976*p 10 - 1712*p 11 + 216*p 12) + ((0) * (- 864*p 1 - 2224*p 2 + 9312*p 3 - 11632*p 4 + 3232*p 5 + 7448*p 6 - 9968*p 7 + 5760*p 8 - 1712*p 9 + 216*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_0_5 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 0 5 =
      - 10708000*p 1 + 4596000*p 2 + 1204000*p 3 - 3232000*p 4 + 4000000*p 5 - 6312000*p 6 + 8000000*p 7 - 6528000*p 8 + 2808000*p 9 + 1328000*p 10 - 3800000*p 11 + 3232000*p 12 - 1404000*p 13 + 388000*p 14 - 100000*p 15 + 16000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (1000) * (- 10708*p 1 + 4596*p 2 + 1204*p 3 - 3232*p 4 + 4000*p 5 - 6312*p 6 + 8000*p 7 - 6528*p 8 + 2808*p 9 + 1328*p 10 - 3800*p 11 + 3232*p 12 - 1404*p 13 + 388*p 14 - 100*p 15 + 16*p 16) + ((0) * (2496*p 1 + 3680*p 2 - 6496*p 3 + 928*p 4 + 4000*p 5 - 4000*p 7 - 944*p 8 + 6596*p 9 - 4036*p 10 - 1292*p 11 + 2504*p 12 - 1204*p 13 + 356*p 14 - 100*p 15 + 16*p 16) + ((0) * (- 2596*p 1 + 4036*p 2 - 2708*p 3 - 3448*p 4 + 7800*p 5 - 4392*p 6 - 1192*p 7 + 2488*p 8 - 1204*p 9 + 356*p 10 - 100*p 11 + 16*p 12) + ((0) * (2412*p 1 - 6476*p 2 + 11932*p 3 - 13368*p 4 + 8208*p 5 - 2104*p 6 + 2104*p 8 - 8208*p 9 + 13368*p 10 - 11932*p 11 + 6460*p 12 - 2280*p 13 + 604*p 14 - 132*p 15 + 16*p 16) + ((0) * (14212*p 1 - 13972*p 2 + 8340*p 3 - 2120*p 4 + 2104*p 6 - 8208*p 7 + 13368*p 8 - 11932*p 9 + 6460*p 10 - 2280*p 11 + 604*p 12 - 132*p 13 + 16*p 14) + ((0) * (20140*p 1 - 8564*p 2 + 2280*p 3 + 1500*p 4 - 8076*p 5 + 13352*p 6 - 11932*p 7 + 6460*p 8 - 2280*p 9 + 604*p 10 - 132*p 11 + 16*p 12) + ((0) * (8208*p 1 - 11264*p 2 + 3724*p 3 + 6908*p 4 - 9652*p 5 + 5856*p 6 - 2148*p 7 + 588*p 8 - 132*p 9 + 16*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_0_6 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 0 6 =
      - 3672000*p 1 + 7766000*p 2 - 7884000*p 3 - 468000*p 4 + 9708000*p 5 - 11598000*p 6 + 7416000*p 7 - 944000*p 8 - 3736000*p 9 + 3798000*p 10 - 1692000*p 11 + 468000*p 12 - 132000*p 13 + 34000*p 14 - 8000*p 15 + 2000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (1000) * (- 3672*p 1 + 7766*p 2 - 7884*p 3 - 468*p 4 + 9708*p 5 - 11598*p 6 + 7416*p 7 - 944*p 8 - 3736*p 9 + 3798*p 10 - 1692*p 11 + 468*p 12 - 132*p 13 + 34*p 14 - 8*p 15 + 2*p 16) + ((0) * (1568*p 1 - 2986*p 2 + 724*p 3 + 7258*p 4 - 10292*p 5 + 10292*p 7 - 7260*p 8 - 716*p 9 + 2956*p 10 - 1452*p 11 + 406*p 12 - 116*p 13 + 30*p 14 - 8*p 15 + 2*p 16) + ((0) * (- 9576*p 1 - 2956*p 2 + 11744*p 3 - 7666*p 4 - 600*p 5 + 2926*p 6 - 1444*p 7 + 404*p 8 - 116*p 9 + 30*p 10 - 8*p 11 + 2*p 12) + ((0) * (220*p 1 - 772*p 2 + 2784*p 3 - 7754*p 4 + 13440*p 5 - 11866*p 6 + 11866*p 8 - 13440*p 9 + 7754*p 10 - 2784*p 11 + 770*p 12 - 208*p 13 + 52*p 14 - 12*p 15 + 2*p 16) + ((0) * (2992*p 1 - 7806*p 2 + 13452*p 3 - 11868*p 4 + 11866*p 6 - 13440*p 7 + 7754*p 8 - 2784*p 9 + 770*p 10 - 208*p 11 + 52*p 12 - 12*p 13 + 2*p 14) + ((0) * (16224*p 1 - 12636*p 2 + 208*p 3 + 11814*p 4 - 13428*p 5 + 7752*p 6 - 2784*p 7 + 770*p 8 - 208*p 9 + 52*p 10 - 12*p 11 + 2*p 12) + ((0) * (13440*p 1 + 4112*p 2 - 10656*p 3 + 6984*p 4 - 2576*p 5 + 718*p 6 - 196*p 7 + 50*p 8 - 12*p 9 + 2*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_1_0 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 1 0 =
      - 4000000*p 2 + 600000*p 4 - 5400000*p 8 + 8000000*p 10 - 600000*p 12 - 4000000*p 14 + 1650000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-175) * (8000*p 4 + 8000*p 8 - 8000*p 12 + 2000*p 16) + ((1000) * (- 4000*p 2 + 2000*p 4 - 4000*p 8 + 8000*p 10 - 2000*p 12 - 4000*p 14 + 2000*p 16) + ((0) * (- 8000*p 2 - 2000*p 4 + 12000*p 6 - 4000*p 8 - 4000*p 10 + 2000*p 12) + ((0) * (4000*p 1 + 2000*p 2 - 8000*p 3 + 4000*p 4 - 4000*p 10 + 8000*p 11 - 4000*p 12 + 2000*p 14 - 4000*p 15 + 2000*p 16) + ((0) * (- 8000*p 1 + 2000*p 2 + 4000*p 3 - 2000*p 4 - 4000*p 8 + 8000*p 9 - 4000*p 10 + 2000*p 12 - 4000*p 13 + 2000*p 14) + ((0) * (- 8000*p 1 + 4000*p 2 - 2000*p 4 + 4000*p 5 - 6000*p 6 + 8000*p 7 - 4000*p 8 + 2000*p 10 - 4000*p 11 + 2000*p 12) + ((0) * (4000*p 2 - 8000*p 3 + 8000*p 5 - 6000*p 6 + 4000*p 7 - 4000*p 9 + 2000*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_1_1 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 1 1 =
      17400000*p 2 - 4455000*p 4 + 3645000*p 8 - 10800000*p 10 + 12455000*p 12 - 6600000*p 14 + 1361250*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-175) * (- 4000*p 2 + 600*p 4 - 5400*p 8 + 8000*p 10 - 600*p 12 - 4000*p 14 + 1650*p 16) + ((1000) * (16700*p 2 - 4350*p 4 + 2700*p 8 - 9400*p 10 + 12350*p 12 - 7300*p 14 + 1650*p 16) + ((0) * (9400*p 2 - 9650*p 4 - 2100*p 6 + 10700*p 8 - 7300*p 10 + 1650*p 12) + ((0) * (- 4700*p 1 - 350*p 2 + 5400*p 3 - 2700*p 4 + 2700*p 10 - 5400*p 11 - 1300*p 12 + 8000*p 13 - 2350*p 14 - 3300*p 15 + 1650*p 16) + ((0) * (- 2600*p 1 - 350*p 2 + 3300*p 3 - 1650*p 4 + 2700*p 8 - 5400*p 9 - 1300*p 10 + 8000*p 11 - 2350*p 12 - 3300*p 13 + 1650*p 14) + ((0) * (5400*p 1 + 1300*p 2 - 8000*p 3 + 2350*p 4 + 3300*p 5 + 1050*p 6 - 5400*p 7 - 1300*p 8 + 8000*p 9 - 2350*p 10 - 3300*p 11 + 1650*p 12) + ((0) * (- 2700*p 2 + 5400*p 3 + 4000*p 4 - 13400*p 5 + 1050*p 6 + 11300*p 7 - 4000*p 8 - 3300*p 9 + 1650*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_1_2 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 1 2 =
      16965700*p 2 - 11506250*p 4 - 2100000*p 6 + 13154300*p 8 - 13047400*p 10 + 6634250*p 12 - 1818300*p 14 + 217800*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-175) * (- 9564*p 2 - 3290*p 4 + 12000*p 6 - 7636*p 8 - 872*p 10 + 3290*p 12 - 1564*p 14 + 264*p 16) + ((1000) * (15292*p 2 - 12082*p 4 + 11818*p 8 - 13200*p 10 + 7210*p 12 - 2092*p 14 + 264*p 16) + ((0) * (13200*p 2 + 4608*p 4 - 11108*p 6 + 6946*p 8 - 2092*p 10 + 264*p 12) + ((0) * (- 2600*p 1 - 2518*p 2 + 7636*p 3 + 182*p 4 - 8000*p 5 + 4000*p 6 - 4000*p 8 + 8000*p 9 - 182*p 10 - 7636*p 11 + 2254*p 12 + 3128*p 13 - 1300*p 14 - 528*p 15 + 264*p 16) + ((0) * (4508*p 1 + 1482*p 2 - 7472*p 3 + 3736*p 4 - 4000*p 6 + 8000*p 7 - 182*p 8 - 7636*p 9 + 2254*p 10 + 3128*p 11 - 1300*p 12 - 528*p 13 + 264*p 14) + ((0) * (- 364*p 1 + 1746*p 2 - 3128*p 3 - 2700*p 4 + 8528*p 5 - 446*p 6 - 7636*p 7 + 2254*p 8 + 3128*p 9 - 1300*p 10 - 528*p 11 + 264*p 12) + ((0) * (- 8000*p 1 - 3818*p 2 + 15636*p 3 - 2436*p 4 - 10764*p 5 + 3554*p 6 + 3656*p 7 - 1564*p 8 - 528*p 9 + 264*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_1_3 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 1 3 =
      - 4700000*p 1 - 4545400*p 2 + 5400000*p 3 - 1331500*p 4 + 84000*p 6 - 1178600*p 8 + 5302800*p 10 - 5400000*p 11 - 4124500*p 12 + 8000000*p 13 - 841400*p 14 - 3300000*p 15 + 1329900*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-175) * (4000*p 1 + 3208*p 2 - 8000*p 3 + 3860*p 4 - 480*p 6 + 1272*p 8 - 5616*p 10 + 8000*p 11 - 3860*p 12 + 2888*p 14 - 4000*p 15 + 1612*p 16) + ((1000) * (- 4000*p 1 - 3984*p 2 + 4000*p 3 - 656*p 4 - 956*p 8 + 4320*p 10 - 4000*p 11 - 4800*p 12 + 8000*p 13 - 336*p 14 - 4000*p 15 + 1612*p 16) + ((0) * (- 4320*p 2 + 4000*p 3 + 3844*p 4 - 8000*p 5 + 4656*p 6 - 6412*p 8 + 8000*p 9 - 336*p 10 - 4000*p 11 + 1612*p 12) + ((0) * (17000*p 1 - 3864*p 2 - 1272*p 3 + 476*p 4 + 320*p 5 - 160*p 6 + 160*p 8 - 320*p 9 - 476*p 10 + 1272*p 11 + 2252*p 12 - 9776*p 13 + 12500*p 14 - 7224*p 15 + 1612*p 16) + ((0) * (8504*p 1 - 12024*p 2 + 7544*p 3 - 1772*p 4 + 160*p 6 - 320*p 7 - 476*p 8 + 1272*p 9 + 2252*p 10 - 9776*p 11 + 12500*p 12 - 7224*p 13 + 1612*p 14) + ((0) * (- 952*p 1 - 2412*p 2 + 9776*p 3 - 12340*p 4 + 6904*p 5 - 2088*p 6 + 1272*p 7 + 2252*p 8 - 9776*p 9 + 12500*p 10 - 7224*p 11 + 1612*p 12) + ((0) * (320*p 1 + 636*p 2 - 1592*p 3 - 2728*p 4 + 11048*p 5 - 10248*p 6 - 2552*p 7 + 10888*p 8 - 7224*p 9 + 1612*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_1_4 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 1 4 =
      - 4104000*p 1 - 1496800*p 2 + 5028000*p 3 - 2990400*p 4 - 226800*p 6 + 3866400*p 8 - 5400000*p 9 - 484400*p 10 + 6272000*p 11 - 4273600*p 12 - 740000*p 13 + 2208000*p 14 - 1056000*p 15 + 178200*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-175) * (- 6720*p 1 + 2336*p 2 + 1440*p 3 - 1792*p 4 + 1296*p 6 - 4448*p 8 + 8000*p 9 - 6832*p 10 + 2560*p 11 + 1792*p 12 - 4000*p 13 + 3200*p 14 - 1280*p 15 + 216*p 16) + ((1000) * (- 5280*p 1 - 1088*p 2 + 5280*p 3 - 3304*p 4 + 3088*p 8 - 4000*p 9 - 1680*p 10 + 6720*p 11 - 3960*p 12 - 1440*p 13 + 2768*p 14 - 1280*p 15 + 216*p 16) + ((0) * (4000*p 1 + 1680*p 2 - 6720*p 3 + 7048*p 4 - 2560*p 5 - 4448*p 6 + 8000*p 7 - 4176*p 8 - 1440*p 9 + 2768*p 10 - 1280*p 11 + 216*p 12) + ((0) * (13392*p 1 - 13640*p 2 + 8448*p 3 - 1792*p 4 - 864*p 5 + 432*p 6 - 432*p 8 + 864*p 9 + 1792*p 10 - 8448*p 11 + 13424*p 12 - 11680*p 13 + 5976*p 14 - 1712*p 15 + 216*p 16) + ((0) * (20128*p 1 - 7768*p 2 + 848*p 3 + 216*p 4 - 432*p 6 + 864*p 7 + 1792*p 8 - 8448*p 9 + 13424*p 10 - 11680*p 11 + 5976*p 12 - 1712*p 13 + 216*p 14) + ((0) * (7584*p 1 - 12992*p 2 + 11680*p 3 - 6408*p 4 + 2576*p 5 + 1576*p 6 - 8448*p 7 + 13424*p 8 - 11680*p 9 + 5976*p 10 - 1712*p 11 + 216*p 12) + ((0) * (- 864*p 1 - 2224*p 2 + 9312*p 3 - 11632*p 4 + 3232*p 5 + 7448*p 6 - 9968*p 7 + 5760*p 8 - 1712*p 9 + 216*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_1_5 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 1 5 =
      4369900*p 1 + 2875700*p 2 - 6706700*p 3 + 1493600*p 4 + 3300000*p 5 + 1104600*p 6 - 5400000*p 7 + 198400*p 8 + 6104600*p 9 - 4268400*p 10 - 627000*p 11 + 1938400*p 12 - 958300*p 13 + 288100*p 14 - 82500*p 15 + 13200*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-175) * (- 10708*p 1 + 4596*p 2 + 1204*p 3 - 3232*p 4 + 4000*p 5 - 6312*p 6 + 8000*p 7 - 6528*p 8 + 2808*p 9 + 1328*p 10 - 3800*p 11 + 3232*p 12 - 1404*p 13 + 388*p 14 - 100*p 15 + 16*p 16) + ((1000) * (2496*p 1 + 3680*p 2 - 6496*p 3 + 928*p 4 + 4000*p 5 - 4000*p 7 - 944*p 8 + 6596*p 9 - 4036*p 10 - 1292*p 11 + 2504*p 12 - 1204*p 13 + 356*p 14 - 100*p 15 + 16*p 16) + ((0) * (- 2596*p 1 + 4036*p 2 - 2708*p 3 - 3448*p 4 + 7800*p 5 - 4392*p 6 - 1192*p 7 + 2488*p 8 - 1204*p 9 + 356*p 10 - 100*p 11 + 16*p 12) + ((0) * (2412*p 1 - 6476*p 2 + 11932*p 3 - 13368*p 4 + 8208*p 5 - 2104*p 6 + 2104*p 8 - 8208*p 9 + 13368*p 10 - 11932*p 11 + 6460*p 12 - 2280*p 13 + 604*p 14 - 132*p 15 + 16*p 16) + ((0) * (14212*p 1 - 13972*p 2 + 8340*p 3 - 2120*p 4 + 2104*p 6 - 8208*p 7 + 13368*p 8 - 11932*p 9 + 6460*p 10 - 2280*p 11 + 604*p 12 - 132*p 13 + 16*p 14) + ((0) * (20140*p 1 - 8564*p 2 + 2280*p 3 + 1500*p 4 - 8076*p 5 + 13352*p 6 - 11932*p 7 + 6460*p 8 - 2280*p 9 + 604*p 10 - 132*p 11 + 16*p 12) + ((0) * (8208*p 1 - 11264*p 2 + 3724*p 3 + 6908*p 4 - 9652*p 5 + 5856*p 6 - 2148*p 7 + 588*p 8 - 132*p 9 + 16*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_1_6 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 1 6 =
      2210600*p 1 - 4345050*p 2 + 2103700*p 3 + 7339900*p 4 - 11990900*p 5 + 2029650*p 6 + 8994200*p 7 - 7094800*p 8 - 62200*p 9 + 2291350*p 10 - 1155900*p 11 + 324100*p 12 - 92900*p 13 + 24050*p 14 - 6600*p 15 + 1650*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-175) * (- 3672*p 1 + 7766*p 2 - 7884*p 3 - 468*p 4 + 9708*p 5 - 11598*p 6 + 7416*p 7 - 944*p 8 - 3736*p 9 + 3798*p 10 - 1692*p 11 + 468*p 12 - 132*p 13 + 34*p 14 - 8*p 15 + 2*p 16) + ((1000) * (1568*p 1 - 2986*p 2 + 724*p 3 + 7258*p 4 - 10292*p 5 + 10292*p 7 - 7260*p 8 - 716*p 9 + 2956*p 10 - 1452*p 11 + 406*p 12 - 116*p 13 + 30*p 14 - 8*p 15 + 2*p 16) + ((0) * (- 9576*p 1 - 2956*p 2 + 11744*p 3 - 7666*p 4 - 600*p 5 + 2926*p 6 - 1444*p 7 + 404*p 8 - 116*p 9 + 30*p 10 - 8*p 11 + 2*p 12) + ((0) * (220*p 1 - 772*p 2 + 2784*p 3 - 7754*p 4 + 13440*p 5 - 11866*p 6 + 11866*p 8 - 13440*p 9 + 7754*p 10 - 2784*p 11 + 770*p 12 - 208*p 13 + 52*p 14 - 12*p 15 + 2*p 16) + ((0) * (2992*p 1 - 7806*p 2 + 13452*p 3 - 11868*p 4 + 11866*p 6 - 13440*p 7 + 7754*p 8 - 2784*p 9 + 770*p 10 - 208*p 11 + 52*p 12 - 12*p 13 + 2*p 14) + ((0) * (16224*p 1 - 12636*p 2 + 208*p 3 + 11814*p 4 - 13428*p 5 + 7752*p 6 - 2784*p 7 + 770*p 8 - 208*p 9 + 52*p 10 - 12*p 11 + 2*p 12) + ((0) * (13440*p 1 + 4112*p 2 - 10656*p 3 + 6984*p 4 - 2576*p 5 + 718*p 6 - 196*p 7 + 50*p 8 - 12*p 9 + 2*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_2_0 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 2 0 =
      - 9564000*p 2 - 3290000*p 4 + 12000000*p 6 - 7636000*p 8 - 872000*p 10 + 3290000*p 12 - 1564000*p 14 + 264000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-259) * (8000*p 4 + 8000*p 8 - 8000*p 12 + 2000*p 16) + ((391) * (- 4000*p 2 + 2000*p 4 - 4000*p 8 + 8000*p 10 - 2000*p 12 - 4000*p 14 + 2000*p 16) + ((1000) * (- 8000*p 2 - 2000*p 4 + 12000*p 6 - 4000*p 8 - 4000*p 10 + 2000*p 12) + ((0) * (4000*p 1 + 2000*p 2 - 8000*p 3 + 4000*p 4 - 4000*p 10 + 8000*p 11 - 4000*p 12 + 2000*p 14 - 4000*p 15 + 2000*p 16) + ((0) * (- 8000*p 1 + 2000*p 2 + 4000*p 3 - 2000*p 4 - 4000*p 8 + 8000*p 9 - 4000*p 10 + 2000*p 12 - 4000*p 13 + 2000*p 14) + ((0) * (- 8000*p 1 + 4000*p 2 - 2000*p 4 + 4000*p 5 - 6000*p 6 + 8000*p 7 - 4000*p 8 + 2000*p 10 - 4000*p 11 + 2000*p 12) + ((0) * (4000*p 2 - 8000*p 3 + 8000*p 5 - 6000*p 6 + 4000*p 7 - 4000*p 9 + 2000*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_2_1 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 2 1 =
      16965700*p 2 - 11506250*p 4 - 2100000*p 6 + 13154300*p 8 - 13047400*p 10 + 6634250*p 12 - 1818300*p 14 + 217800*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-259) * (- 4000*p 2 + 600*p 4 - 5400*p 8 + 8000*p 10 - 600*p 12 - 4000*p 14 + 1650*p 16) + ((391) * (16700*p 2 - 4350*p 4 + 2700*p 8 - 9400*p 10 + 12350*p 12 - 7300*p 14 + 1650*p 16) + ((1000) * (9400*p 2 - 9650*p 4 - 2100*p 6 + 10700*p 8 - 7300*p 10 + 1650*p 12) + ((0) * (- 4700*p 1 - 350*p 2 + 5400*p 3 - 2700*p 4 + 2700*p 10 - 5400*p 11 - 1300*p 12 + 8000*p 13 - 2350*p 14 - 3300*p 15 + 1650*p 16) + ((0) * (- 2600*p 1 - 350*p 2 + 3300*p 3 - 1650*p 4 + 2700*p 8 - 5400*p 9 - 1300*p 10 + 8000*p 11 - 2350*p 12 - 3300*p 13 + 1650*p 14) + ((0) * (5400*p 1 + 1300*p 2 - 8000*p 3 + 2350*p 4 + 3300*p 5 + 1050*p 6 - 5400*p 7 - 1300*p 8 + 8000*p 9 - 2350*p 10 - 3300*p 11 + 1650*p 12) + ((0) * (- 2700*p 2 + 5400*p 3 + 4000*p 4 - 13400*p 5 + 1050*p 6 + 11300*p 7 - 4000*p 8 - 3300*p 9 + 1650*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_2_2 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 2 2 =
      21656248*p 2 + 736048*p 4 - 14216000*p 6 + 13544562*p 8 - 7027352*p 10 + 2231000*p 12 - 412896*p 14 + 34848*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-259) * (- 9564*p 2 - 3290*p 4 + 12000*p 6 - 7636*p 8 - 872*p 10 + 3290*p 12 - 1564*p 14 + 264*p 16) + ((391) * (15292*p 2 - 12082*p 4 + 11818*p 8 - 13200*p 10 + 7210*p 12 - 2092*p 14 + 264*p 16) + ((1000) * (13200*p 2 + 4608*p 4 - 11108*p 6 + 6946*p 8 - 2092*p 10 + 264*p 12) + ((0) * (- 2600*p 1 - 2518*p 2 + 7636*p 3 + 182*p 4 - 8000*p 5 + 4000*p 6 - 4000*p 8 + 8000*p 9 - 182*p 10 - 7636*p 11 + 2254*p 12 + 3128*p 13 - 1300*p 14 - 528*p 15 + 264*p 16) + ((0) * (4508*p 1 + 1482*p 2 - 7472*p 3 + 3736*p 4 - 4000*p 6 + 8000*p 7 - 182*p 8 - 7636*p 9 + 2254*p 10 + 3128*p 11 - 1300*p 12 - 528*p 13 + 264*p 14) + ((0) * (- 364*p 1 + 1746*p 2 - 3128*p 3 - 2700*p 4 + 8528*p 5 - 446*p 6 - 7636*p 7 + 2254*p 8 + 3128*p 9 - 1300*p 10 - 528*p 11 + 264*p 12) + ((0) * (- 8000*p 1 - 3818*p 2 + 15636*p 3 - 2436*p 4 - 10764*p 5 + 3554*p 6 + 3656*p 7 - 1564*p 8 - 528*p 9 + 264*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_2_3 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 2 3 =
      - 2600000*p 1 - 6708616*p 2 + 7636000*p 3 + 2587764*p 4 - 8000000*p 5 + 4780320*p 6 - 7115244*p 8 + 8000000*p 9 + 2807664*p 10 - 7636000*p 11 + 734940*p 12 + 3128000*p 13 - 879368*p 14 - 528000*p 15 + 212784*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-259) * (4000*p 1 + 3208*p 2 - 8000*p 3 + 3860*p 4 - 480*p 6 + 1272*p 8 - 5616*p 10 + 8000*p 11 - 3860*p 12 + 2888*p 14 - 4000*p 15 + 1612*p 16) + ((391) * (- 4000*p 1 - 3984*p 2 + 4000*p 3 - 656*p 4 - 956*p 8 + 4320*p 10 - 4000*p 11 - 4800*p 12 + 8000*p 13 - 336*p 14 - 4000*p 15 + 1612*p 16) + ((1000) * (- 4320*p 2 + 4000*p 3 + 3844*p 4 - 8000*p 5 + 4656*p 6 - 6412*p 8 + 8000*p 9 - 336*p 10 - 4000*p 11 + 1612*p 12) + ((0) * (17000*p 1 - 3864*p 2 - 1272*p 3 + 476*p 4 + 320*p 5 - 160*p 6 + 160*p 8 - 320*p 9 - 476*p 10 + 1272*p 11 + 2252*p 12 - 9776*p 13 + 12500*p 14 - 7224*p 15 + 1612*p 16) + ((0) * (8504*p 1 - 12024*p 2 + 7544*p 3 - 1772*p 4 + 160*p 6 - 320*p 7 - 476*p 8 + 1272*p 9 + 2252*p 10 - 9776*p 11 + 12500*p 12 - 7224*p 13 + 1612*p 14) + ((0) * (- 952*p 1 - 2412*p 2 + 9776*p 3 - 12340*p 4 + 6904*p 5 - 2088*p 6 + 1272*p 7 + 2252*p 8 - 9776*p 9 + 12500*p 10 - 7224*p 11 + 1612*p 12) + ((0) * (320*p 1 + 636*p 2 - 1592*p 3 - 2728*p 4 + 11048*p 5 - 10248*p 6 - 2552*p 7 + 10888*p 8 - 7224*p 9 + 1612*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_2_4 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 2 4 =
      3676000*p 1 + 649568*p 2 - 5028480*p 3 + 6220264*p 4 - 2560000*p 5 - 4783664*p 6 + 8000000*p 7 - 1816560*p 8 - 5076000*p 9 + 3880608*p 10 + 684480*p 11 - 1796488*p 12 + 472960*p 13 + 253488*p 14 - 168960*p 15 + 28512*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-259) * (- 6720*p 1 + 2336*p 2 + 1440*p 3 - 1792*p 4 + 1296*p 6 - 4448*p 8 + 8000*p 9 - 6832*p 10 + 2560*p 11 + 1792*p 12 - 4000*p 13 + 3200*p 14 - 1280*p 15 + 216*p 16) + ((391) * (- 5280*p 1 - 1088*p 2 + 5280*p 3 - 3304*p 4 + 3088*p 8 - 4000*p 9 - 1680*p 10 + 6720*p 11 - 3960*p 12 - 1440*p 13 + 2768*p 14 - 1280*p 15 + 216*p 16) + ((1000) * (4000*p 1 + 1680*p 2 - 6720*p 3 + 7048*p 4 - 2560*p 5 - 4448*p 6 + 8000*p 7 - 4176*p 8 - 1440*p 9 + 2768*p 10 - 1280*p 11 + 216*p 12) + ((0) * (13392*p 1 - 13640*p 2 + 8448*p 3 - 1792*p 4 - 864*p 5 + 432*p 6 - 432*p 8 + 864*p 9 + 1792*p 10 - 8448*p 11 + 13424*p 12 - 11680*p 13 + 5976*p 14 - 1712*p 15 + 216*p 16) + ((0) * (20128*p 1 - 7768*p 2 + 848*p 3 + 216*p 4 - 432*p 6 + 864*p 7 + 1792*p 8 - 8448*p 9 + 13424*p 10 - 11680*p 11 + 5976*p 12 - 1712*p 13 + 216*p 14) + ((0) * (7584*p 1 - 12992*p 2 + 11680*p 3 - 6408*p 4 + 2576*p 5 + 1576*p 6 - 8448*p 7 + 13424*p 8 - 11680*p 9 + 5976*p 10 - 1712*p 11 + 216*p 12) + ((0) * (- 864*p 1 - 2224*p 2 + 9312*p 3 - 11632*p 4 + 3232*p 5 + 7448*p 6 - 9968*p 7 + 5760*p 8 - 1712*p 9 + 216*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_2_5 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 2 5 =
      1153308*p 1 + 4284516*p 2 - 5559772*p 3 - 2248064*p 4 + 8328000*p 5 - 2757192*p 6 - 4828000*p 7 + 3809648*p 8 + 647764*p 9 - 1566028*p 10 + 379028*p 11 + 157976*p 12 - 107128*p 13 + 38704*p 14 - 13200*p 15 + 2112*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-259) * (- 10708*p 1 + 4596*p 2 + 1204*p 3 - 3232*p 4 + 4000*p 5 - 6312*p 6 + 8000*p 7 - 6528*p 8 + 2808*p 9 + 1328*p 10 - 3800*p 11 + 3232*p 12 - 1404*p 13 + 388*p 14 - 100*p 15 + 16*p 16) + ((391) * (2496*p 1 + 3680*p 2 - 6496*p 3 + 928*p 4 + 4000*p 5 - 4000*p 7 - 944*p 8 + 6596*p 9 - 4036*p 10 - 1292*p 11 + 2504*p 12 - 1204*p 13 + 356*p 14 - 100*p 15 + 16*p 16) + ((1000) * (- 2596*p 1 + 4036*p 2 - 2708*p 3 - 3448*p 4 + 7800*p 5 - 4392*p 6 - 1192*p 7 + 2488*p 8 - 1204*p 9 + 356*p 10 - 100*p 11 + 16*p 12) + ((0) * (2412*p 1 - 6476*p 2 + 11932*p 3 - 13368*p 4 + 8208*p 5 - 2104*p 6 + 2104*p 8 - 8208*p 9 + 13368*p 10 - 11932*p 11 + 6460*p 12 - 2280*p 13 + 604*p 14 - 132*p 15 + 16*p 16) + ((0) * (14212*p 1 - 13972*p 2 + 8340*p 3 - 2120*p 4 + 2104*p 6 - 8208*p 7 + 13368*p 8 - 11932*p 9 + 6460*p 10 - 2280*p 11 + 604*p 12 - 132*p 13 + 16*p 14) + ((0) * (20140*p 1 - 8564*p 2 + 2280*p 3 + 1500*p 4 - 8076*p 5 + 13352*p 6 - 11932*p 7 + 6460*p 8 - 2280*p 9 + 604*p 10 - 132*p 11 + 16*p 12) + ((0) * (8208*p 1 - 11264*p 2 + 3724*p 3 + 6908*p 4 - 9652*p 5 + 5856*p 6 - 2148*p 7 + 588*p 8 - 132*p 9 + 16*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_2_6 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 2 6 =
      - 8011864*p 1 - 6134920*p 2 + 14069040*p 3 - 4706910*p 4 - 7138544*p 5 + 5929882*p 6 + 659428*p 7 - 2190164*p 8 + 571668*p 9 + 202114*p 10 - 137504*p 11 + 39534*p 12 - 11168*p 13 + 2924*p 14 - 1056*p 15 + 264*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-259) * (- 3672*p 1 + 7766*p 2 - 7884*p 3 - 468*p 4 + 9708*p 5 - 11598*p 6 + 7416*p 7 - 944*p 8 - 3736*p 9 + 3798*p 10 - 1692*p 11 + 468*p 12 - 132*p 13 + 34*p 14 - 8*p 15 + 2*p 16) + ((391) * (1568*p 1 - 2986*p 2 + 724*p 3 + 7258*p 4 - 10292*p 5 + 10292*p 7 - 7260*p 8 - 716*p 9 + 2956*p 10 - 1452*p 11 + 406*p 12 - 116*p 13 + 30*p 14 - 8*p 15 + 2*p 16) + ((1000) * (- 9576*p 1 - 2956*p 2 + 11744*p 3 - 7666*p 4 - 600*p 5 + 2926*p 6 - 1444*p 7 + 404*p 8 - 116*p 9 + 30*p 10 - 8*p 11 + 2*p 12) + ((0) * (220*p 1 - 772*p 2 + 2784*p 3 - 7754*p 4 + 13440*p 5 - 11866*p 6 + 11866*p 8 - 13440*p 9 + 7754*p 10 - 2784*p 11 + 770*p 12 - 208*p 13 + 52*p 14 - 12*p 15 + 2*p 16) + ((0) * (2992*p 1 - 7806*p 2 + 13452*p 3 - 11868*p 4 + 11866*p 6 - 13440*p 7 + 7754*p 8 - 2784*p 9 + 770*p 10 - 208*p 11 + 52*p 12 - 12*p 13 + 2*p 14) + ((0) * (16224*p 1 - 12636*p 2 + 208*p 3 + 11814*p 4 - 13428*p 5 + 7752*p 6 - 2784*p 7 + 770*p 8 - 208*p 9 + 52*p 10 - 12*p 11 + 2*p 12) + ((0) * (13440*p 1 + 4112*p 2 - 10656*p 3 + 6984*p 4 - 2576*p 5 + 718*p 6 - 196*p 7 + 50*p 8 - 12*p 9 + 2*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_3_0 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 3 0 =
      4000000*p 1 + 3208000*p 2 - 8000000*p 3 + 3860000*p 4 - 480000*p 6 + 1272000*p 8 - 5616000*p 10 + 8000000*p 11 - 3860000*p 12 + 2888000*p 14 - 4000000*p 15 + 1612000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (28) * (8000*p 4 + 8000*p 8 - 8000*p 12 + 2000*p 16) + ((-222) * (- 4000*p 2 + 2000*p 4 - 4000*p 8 + 8000*p 10 - 2000*p 12 - 4000*p 14 + 2000*p 16) + ((-40) * (- 8000*p 2 - 2000*p 4 + 12000*p 6 - 4000*p 8 - 4000*p 10 + 2000*p 12) + ((1000) * (4000*p 1 + 2000*p 2 - 8000*p 3 + 4000*p 4 - 4000*p 10 + 8000*p 11 - 4000*p 12 + 2000*p 14 - 4000*p 15 + 2000*p 16) + ((0) * (- 8000*p 1 + 2000*p 2 + 4000*p 3 - 2000*p 4 - 4000*p 8 + 8000*p 9 - 4000*p 10 + 2000*p 12 - 4000*p 13 + 2000*p 14) + ((0) * (- 8000*p 1 + 4000*p 2 - 2000*p 4 + 4000*p 5 - 6000*p 6 + 8000*p 7 - 4000*p 8 + 2000*p 10 - 4000*p 11 + 2000*p 12) + ((0) * (4000*p 2 - 8000*p 3 + 8000*p 5 - 6000*p 6 + 4000*p 7 - 4000*p 9 + 2000*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_3_1 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 3 1 =
      - 4700000*p 1 - 4545400*p 2 + 5400000*p 3 - 1331500*p 4 + 84000*p 6 - 1178600*p 8 + 5302800*p 10 - 5400000*p 11 - 4124500*p 12 + 8000000*p 13 - 841400*p 14 - 3300000*p 15 + 1329900*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (28) * (- 4000*p 2 + 600*p 4 - 5400*p 8 + 8000*p 10 - 600*p 12 - 4000*p 14 + 1650*p 16) + ((-222) * (16700*p 2 - 4350*p 4 + 2700*p 8 - 9400*p 10 + 12350*p 12 - 7300*p 14 + 1650*p 16) + ((-40) * (9400*p 2 - 9650*p 4 - 2100*p 6 + 10700*p 8 - 7300*p 10 + 1650*p 12) + ((1000) * (- 4700*p 1 - 350*p 2 + 5400*p 3 - 2700*p 4 + 2700*p 10 - 5400*p 11 - 1300*p 12 + 8000*p 13 - 2350*p 14 - 3300*p 15 + 1650*p 16) + ((0) * (- 2600*p 1 - 350*p 2 + 3300*p 3 - 1650*p 4 + 2700*p 8 - 5400*p 9 - 1300*p 10 + 8000*p 11 - 2350*p 12 - 3300*p 13 + 1650*p 14) + ((0) * (5400*p 1 + 1300*p 2 - 8000*p 3 + 2350*p 4 + 3300*p 5 + 1050*p 6 - 5400*p 7 - 1300*p 8 + 8000*p 9 - 2350*p 10 - 3300*p 11 + 1650*p 12) + ((0) * (- 2700*p 2 + 5400*p 3 + 4000*p 4 - 13400*p 5 + 1050*p 6 + 11300*p 7 - 4000*p 8 - 3300*p 9 + 1650*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_3_2 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 3 2 =
      - 2600000*p 1 - 6708616*p 2 + 7636000*p 3 + 2587764*p 4 - 8000000*p 5 + 4780320*p 6 - 7115244*p 8 + 8000000*p 9 + 2807664*p 10 - 7636000*p 11 + 734940*p 12 + 3128000*p 13 - 879368*p 14 - 528000*p 15 + 212784*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (28) * (- 9564*p 2 - 3290*p 4 + 12000*p 6 - 7636*p 8 - 872*p 10 + 3290*p 12 - 1564*p 14 + 264*p 16) + ((-222) * (15292*p 2 - 12082*p 4 + 11818*p 8 - 13200*p 10 + 7210*p 12 - 2092*p 14 + 264*p 16) + ((-40) * (13200*p 2 + 4608*p 4 - 11108*p 6 + 6946*p 8 - 2092*p 10 + 264*p 12) + ((1000) * (- 2600*p 1 - 2518*p 2 + 7636*p 3 + 182*p 4 - 8000*p 5 + 4000*p 6 - 4000*p 8 + 8000*p 9 - 182*p 10 - 7636*p 11 + 2254*p 12 + 3128*p 13 - 1300*p 14 - 528*p 15 + 264*p 16) + ((0) * (4508*p 1 + 1482*p 2 - 7472*p 3 + 3736*p 4 - 4000*p 6 + 8000*p 7 - 182*p 8 - 7636*p 9 + 2254*p 10 + 3128*p 11 - 1300*p 12 - 528*p 13 + 264*p 14) + ((0) * (- 364*p 1 + 1746*p 2 - 3128*p 3 - 2700*p 4 + 8528*p 5 - 446*p 6 - 7636*p 7 + 2254*p 8 + 3128*p 9 - 1300*p 10 - 528*p 11 + 264*p 12) + ((0) * (- 8000*p 1 - 3818*p 2 + 15636*p 3 - 2436*p 4 - 10764*p 5 + 3554*p 6 + 3656*p 7 - 1564*p 8 - 528*p 9 + 264*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_3_3 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 3 3 =
      18000000*p 1 - 2716928*p 2 - 2544000*p 3 + 575952*p 4 + 640000*p 5 - 359680*p 6 + 664328*p 8 - 640000*p 9 - 1578848*p 10 + 2544000*p 11 + 3145040*p 12 - 11552000*p 13 + 12655456*p 14 - 6448000*p 15 + 1299272*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (28) * (4000*p 1 + 3208*p 2 - 8000*p 3 + 3860*p 4 - 480*p 6 + 1272*p 8 - 5616*p 10 + 8000*p 11 - 3860*p 12 + 2888*p 14 - 4000*p 15 + 1612*p 16) + ((-222) * (- 4000*p 1 - 3984*p 2 + 4000*p 3 - 656*p 4 - 956*p 8 + 4320*p 10 - 4000*p 11 - 4800*p 12 + 8000*p 13 - 336*p 14 - 4000*p 15 + 1612*p 16) + ((-40) * (- 4320*p 2 + 4000*p 3 + 3844*p 4 - 8000*p 5 + 4656*p 6 - 6412*p 8 + 8000*p 9 - 336*p 10 - 4000*p 11 + 1612*p 12) + ((1000) * (17000*p 1 - 3864*p 2 - 1272*p 3 + 476*p 4 + 320*p 5 - 160*p 6 + 160*p 8 - 320*p 9 - 476*p 10 + 1272*p 11 + 2252*p 12 - 9776*p 13 + 12500*p 14 - 7224*p 15 + 1612*p 16) + ((0) * (8504*p 1 - 12024*p 2 + 7544*p 3 - 1772*p 4 + 160*p 6 - 320*p 7 - 476*p 8 + 1272*p 9 + 2252*p 10 - 9776*p 11 + 12500*p 12 - 7224*p 13 + 1612*p 14) + ((0) * (- 952*p 1 - 2412*p 2 + 9776*p 3 - 12340*p 4 + 6904*p 5 - 2088*p 6 + 1272*p 7 + 2252*p 8 - 9776*p 9 + 12500*p 10 - 7224*p 11 + 1612*p 12) + ((0) * (320*p 1 + 636*p 2 - 1592*p 3 - 2728*p 4 + 11048*p 5 - 10248*p 6 - 2552*p 7 + 10888*p 8 - 7224*p 9 + 1612*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_3_4 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 3 4 =
      14216000*p 1 - 13400256*p 2 + 7584960*p 3 - 1390608*p 4 - 761600*p 5 + 646208*p 6 - 320000*p 7 - 1075040*p 8 + 2033600*p 9 + 1862944*p 10 - 9816960*p 11 + 14344656*p 12 - 11472320*p 13 + 5451104*p 14 - 1463680*p 15 + 174096*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (28) * (- 6720*p 1 + 2336*p 2 + 1440*p 3 - 1792*p 4 + 1296*p 6 - 4448*p 8 + 8000*p 9 - 6832*p 10 + 2560*p 11 + 1792*p 12 - 4000*p 13 + 3200*p 14 - 1280*p 15 + 216*p 16) + ((-222) * (- 5280*p 1 - 1088*p 2 + 5280*p 3 - 3304*p 4 + 3088*p 8 - 4000*p 9 - 1680*p 10 + 6720*p 11 - 3960*p 12 - 1440*p 13 + 2768*p 14 - 1280*p 15 + 216*p 16) + ((-40) * (4000*p 1 + 1680*p 2 - 6720*p 3 + 7048*p 4 - 2560*p 5 - 4448*p 6 + 8000*p 7 - 4176*p 8 - 1440*p 9 + 2768*p 10 - 1280*p 11 + 216*p 12) + ((1000) * (13392*p 1 - 13640*p 2 + 8448*p 3 - 1792*p 4 - 864*p 5 + 432*p 6 - 432*p 8 + 864*p 9 + 1792*p 10 - 8448*p 11 + 13424*p 12 - 11680*p 13 + 5976*p 14 - 1712*p 15 + 216*p 16) + ((0) * (20128*p 1 - 7768*p 2 + 848*p 3 + 216*p 4 - 432*p 6 + 864*p 7 + 1792*p 8 - 8448*p 9 + 13424*p 10 - 11680*p 11 + 5976*p 12 - 1712*p 13 + 216*p 14) + ((0) * (7584*p 1 - 12992*p 2 + 11680*p 3 - 6408*p 4 + 2576*p 5 + 1576*p 6 - 8448*p 7 + 13424*p 8 - 11680*p 9 + 5976*p 10 - 1712*p 11 + 216*p 12) + ((0) * (- 864*p 1 - 2224*p 2 + 9312*p 3 - 11632*p 4 + 3232*p 5 + 7448*p 6 - 9968*p 7 + 5760*p 8 - 1712*p 9 + 216*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_3_5 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 3 5 =
      1661904*p 1 - 7325712*p 2 + 13516144*p 3 - 13526592*p 4 + 7120000*p 5 - 2105056*p 6 + 1159680*p 7 + 2031264*p 8 - 9545528*p 9 + 14286936*p 10 - 11747576*p 11 + 5993968*p 12 - 2052024*p 13 + 535832*p 14 - 112600*p 15 + 12896*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (28) * (- 10708*p 1 + 4596*p 2 + 1204*p 3 - 3232*p 4 + 4000*p 5 - 6312*p 6 + 8000*p 7 - 6528*p 8 + 2808*p 9 + 1328*p 10 - 3800*p 11 + 3232*p 12 - 1404*p 13 + 388*p 14 - 100*p 15 + 16*p 16) + ((-222) * (2496*p 1 + 3680*p 2 - 6496*p 3 + 928*p 4 + 4000*p 5 - 4000*p 7 - 944*p 8 + 6596*p 9 - 4036*p 10 - 1292*p 11 + 2504*p 12 - 1204*p 13 + 356*p 14 - 100*p 15 + 16*p 16) + ((-40) * (- 2596*p 1 + 4036*p 2 - 2708*p 3 - 3448*p 4 + 7800*p 5 - 4392*p 6 - 1192*p 7 + 2488*p 8 - 1204*p 9 + 356*p 10 - 100*p 11 + 16*p 12) + ((1000) * (2412*p 1 - 6476*p 2 + 11932*p 3 - 13368*p 4 + 8208*p 5 - 2104*p 6 + 2104*p 8 - 8208*p 9 + 13368*p 10 - 11932*p 11 + 6460*p 12 - 2280*p 13 + 604*p 14 - 132*p 15 + 16*p 16) + ((0) * (14212*p 1 - 13972*p 2 + 8340*p 3 - 2120*p 4 + 2104*p 6 - 8208*p 7 + 13368*p 8 - 11932*p 9 + 6460*p 10 - 2280*p 11 + 604*p 12 - 132*p 13 + 16*p 14) + ((0) * (20140*p 1 - 8564*p 2 + 2280*p 3 + 1500*p 4 - 8076*p 5 + 13352*p 6 - 11932*p 7 + 6460*p 8 - 2280*p 9 + 604*p 10 - 132*p 11 + 16*p 12) + ((0) * (8208*p 1 - 11264*p 2 + 3724*p 3 + 6908*p 4 - 9652*p 5 + 5856*p 6 - 2148*p 7 + 588*p 8 - 132*p 9 + 16*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_3_6 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 3 6 =
      152128*p 1 + 226580*p 2 + 1932760*p 3 - 9071740*p 4 + 16020648*p 5 - 12307784*p 6 - 2019416*p 7 + 13435128*p 8 - 13381016*p 9 + 7202912*p 10 - 2508712*p 11 + 692892*p 12 - 185944*p 13 + 46292*p 14 - 10448*p 15 + 1612*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (28) * (- 3672*p 1 + 7766*p 2 - 7884*p 3 - 468*p 4 + 9708*p 5 - 11598*p 6 + 7416*p 7 - 944*p 8 - 3736*p 9 + 3798*p 10 - 1692*p 11 + 468*p 12 - 132*p 13 + 34*p 14 - 8*p 15 + 2*p 16) + ((-222) * (1568*p 1 - 2986*p 2 + 724*p 3 + 7258*p 4 - 10292*p 5 + 10292*p 7 - 7260*p 8 - 716*p 9 + 2956*p 10 - 1452*p 11 + 406*p 12 - 116*p 13 + 30*p 14 - 8*p 15 + 2*p 16) + ((-40) * (- 9576*p 1 - 2956*p 2 + 11744*p 3 - 7666*p 4 - 600*p 5 + 2926*p 6 - 1444*p 7 + 404*p 8 - 116*p 9 + 30*p 10 - 8*p 11 + 2*p 12) + ((1000) * (220*p 1 - 772*p 2 + 2784*p 3 - 7754*p 4 + 13440*p 5 - 11866*p 6 + 11866*p 8 - 13440*p 9 + 7754*p 10 - 2784*p 11 + 770*p 12 - 208*p 13 + 52*p 14 - 12*p 15 + 2*p 16) + ((0) * (2992*p 1 - 7806*p 2 + 13452*p 3 - 11868*p 4 + 11866*p 6 - 13440*p 7 + 7754*p 8 - 2784*p 9 + 770*p 10 - 208*p 11 + 52*p 12 - 12*p 13 + 2*p 14) + ((0) * (16224*p 1 - 12636*p 2 + 208*p 3 + 11814*p 4 - 13428*p 5 + 7752*p 6 - 2784*p 7 + 770*p 8 - 208*p 9 + 52*p 10 - 12*p 11 + 2*p 12) + ((0) * (13440*p 1 + 4112*p 2 - 10656*p 3 + 6984*p 4 - 2576*p 5 + 718*p 6 - 196*p 7 + 50*p 8 - 12*p 9 + 2*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_4_0 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 4 0 =
      - 6720000*p 1 + 2336000*p 2 + 1440000*p 3 - 1792000*p 4 + 1296000*p 6 - 4448000*p 8 + 8000000*p 9 - 6832000*p 10 + 2560000*p 11 + 1792000*p 12 - 4000000*p 13 + 3200000*p 14 - 1280000*p 15 + 216000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-72) * (8000*p 4 + 8000*p 8 - 8000*p 12 + 2000*p 16) + ((-140) * (- 4000*p 2 + 2000*p 4 - 4000*p 8 + 8000*p 10 - 2000*p 12 - 4000*p 14 + 2000*p 16) + ((108) * (- 8000*p 2 - 2000*p 4 + 12000*p 6 - 4000*p 8 - 4000*p 10 + 2000*p 12) + ((320) * (4000*p 1 + 2000*p 2 - 8000*p 3 + 4000*p 4 - 4000*p 10 + 8000*p 11 - 4000*p 12 + 2000*p 14 - 4000*p 15 + 2000*p 16) + ((1000) * (- 8000*p 1 + 2000*p 2 + 4000*p 3 - 2000*p 4 - 4000*p 8 + 8000*p 9 - 4000*p 10 + 2000*p 12 - 4000*p 13 + 2000*p 14) + ((0) * (- 8000*p 1 + 4000*p 2 - 2000*p 4 + 4000*p 5 - 6000*p 6 + 8000*p 7 - 4000*p 8 + 2000*p 10 - 4000*p 11 + 2000*p 12) + ((0) * (4000*p 2 - 8000*p 3 + 8000*p 5 - 6000*p 6 + 4000*p 7 - 4000*p 9 + 2000*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_4_1 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 4 1 =
      - 4104000*p 1 - 1496800*p 2 + 5028000*p 3 - 2990400*p 4 - 226800*p 6 + 3866400*p 8 - 5400000*p 9 - 484400*p 10 + 6272000*p 11 - 4273600*p 12 - 740000*p 13 + 2208000*p 14 - 1056000*p 15 + 178200*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-72) * (- 4000*p 2 + 600*p 4 - 5400*p 8 + 8000*p 10 - 600*p 12 - 4000*p 14 + 1650*p 16) + ((-140) * (16700*p 2 - 4350*p 4 + 2700*p 8 - 9400*p 10 + 12350*p 12 - 7300*p 14 + 1650*p 16) + ((108) * (9400*p 2 - 9650*p 4 - 2100*p 6 + 10700*p 8 - 7300*p 10 + 1650*p 12) + ((320) * (- 4700*p 1 - 350*p 2 + 5400*p 3 - 2700*p 4 + 2700*p 10 - 5400*p 11 - 1300*p 12 + 8000*p 13 - 2350*p 14 - 3300*p 15 + 1650*p 16) + ((1000) * (- 2600*p 1 - 350*p 2 + 3300*p 3 - 1650*p 4 + 2700*p 8 - 5400*p 9 - 1300*p 10 + 8000*p 11 - 2350*p 12 - 3300*p 13 + 1650*p 14) + ((0) * (5400*p 1 + 1300*p 2 - 8000*p 3 + 2350*p 4 + 3300*p 5 + 1050*p 6 - 5400*p 7 - 1300*p 8 + 8000*p 9 - 2350*p 10 - 3300*p 11 + 1650*p 12) + ((0) * (- 2700*p 2 + 5400*p 3 + 4000*p 4 - 13400*p 5 + 1050*p 6 + 11300*p 7 - 4000*p 8 - 3300*p 9 + 1650*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_4_2 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 4 2 =
      3676000*p 1 + 649568*p 2 - 5028480*p 3 + 6220264*p 4 - 2560000*p 5 - 4783664*p 6 + 8000000*p 7 - 1816560*p 8 - 5076000*p 9 + 3880608*p 10 + 684480*p 11 - 1796488*p 12 + 472960*p 13 + 253488*p 14 - 168960*p 15 + 28512*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-72) * (- 9564*p 2 - 3290*p 4 + 12000*p 6 - 7636*p 8 - 872*p 10 + 3290*p 12 - 1564*p 14 + 264*p 16) + ((-140) * (15292*p 2 - 12082*p 4 + 11818*p 8 - 13200*p 10 + 7210*p 12 - 2092*p 14 + 264*p 16) + ((108) * (13200*p 2 + 4608*p 4 - 11108*p 6 + 6946*p 8 - 2092*p 10 + 264*p 12) + ((320) * (- 2600*p 1 - 2518*p 2 + 7636*p 3 + 182*p 4 - 8000*p 5 + 4000*p 6 - 4000*p 8 + 8000*p 9 - 182*p 10 - 7636*p 11 + 2254*p 12 + 3128*p 13 - 1300*p 14 - 528*p 15 + 264*p 16) + ((1000) * (4508*p 1 + 1482*p 2 - 7472*p 3 + 3736*p 4 - 4000*p 6 + 8000*p 7 - 182*p 8 - 7636*p 9 + 2254*p 10 + 3128*p 11 - 1300*p 12 - 528*p 13 + 264*p 14) + ((0) * (- 364*p 1 + 1746*p 2 - 3128*p 3 - 2700*p 4 + 8528*p 5 - 446*p 6 - 7636*p 7 + 2254*p 8 + 3128*p 9 - 1300*p 10 - 528*p 11 + 264*p 12) + ((0) * (- 8000*p 1 - 3818*p 2 + 15636*p 3 - 2436*p 4 - 10764*p 5 + 3554*p 6 + 3656*p 7 - 1564*p 8 - 528*p 9 + 264*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_4_3 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 4 3 =
      14216000*p 1 - 13400256*p 2 + 7584960*p 3 - 1390608*p 4 - 761600*p 5 + 646208*p 6 - 320000*p 7 - 1075040*p 8 + 2033600*p 9 + 1862944*p 10 - 9816960*p 11 + 14344656*p 12 - 11472320*p 13 + 5451104*p 14 - 1463680*p 15 + 174096*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-72) * (4000*p 1 + 3208*p 2 - 8000*p 3 + 3860*p 4 - 480*p 6 + 1272*p 8 - 5616*p 10 + 8000*p 11 - 3860*p 12 + 2888*p 14 - 4000*p 15 + 1612*p 16) + ((-140) * (- 4000*p 1 - 3984*p 2 + 4000*p 3 - 656*p 4 - 956*p 8 + 4320*p 10 - 4000*p 11 - 4800*p 12 + 8000*p 13 - 336*p 14 - 4000*p 15 + 1612*p 16) + ((108) * (- 4320*p 2 + 4000*p 3 + 3844*p 4 - 8000*p 5 + 4656*p 6 - 6412*p 8 + 8000*p 9 - 336*p 10 - 4000*p 11 + 1612*p 12) + ((320) * (17000*p 1 - 3864*p 2 - 1272*p 3 + 476*p 4 + 320*p 5 - 160*p 6 + 160*p 8 - 320*p 9 - 476*p 10 + 1272*p 11 + 2252*p 12 - 9776*p 13 + 12500*p 14 - 7224*p 15 + 1612*p 16) + ((1000) * (8504*p 1 - 12024*p 2 + 7544*p 3 - 1772*p 4 + 160*p 6 - 320*p 7 - 476*p 8 + 1272*p 9 + 2252*p 10 - 9776*p 11 + 12500*p 12 - 7224*p 13 + 1612*p 14) + ((0) * (- 952*p 1 - 2412*p 2 + 9776*p 3 - 12340*p 4 + 6904*p 5 - 2088*p 6 + 1272*p 7 + 2252*p 8 - 9776*p 9 + 12500*p 10 - 7224*p 11 + 1612*p 12) + ((0) * (320*p 1 + 636*p 2 - 1592*p 3 - 2728*p 4 + 11048*p 5 - 10248*p 6 - 2552*p 7 + 10888*p 8 - 7224*p 9 + 1612*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_4_4 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 4 4 =
      26068480*p 1 - 11967232*p 2 + 1982720*p 3 + 995328*p 4 - 552960*p 5 - 867456*p 6 + 1728000*p 7 + 1090688*p 8 - 8343040*p 9 + 15023488*p 10 - 15646720*p 11 + 10720384*p 12 - 4960000*p 13 + 1510400*p 14 - 276480*p 15 + 23328*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-72) * (- 6720*p 1 + 2336*p 2 + 1440*p 3 - 1792*p 4 + 1296*p 6 - 4448*p 8 + 8000*p 9 - 6832*p 10 + 2560*p 11 + 1792*p 12 - 4000*p 13 + 3200*p 14 - 1280*p 15 + 216*p 16) + ((-140) * (- 5280*p 1 - 1088*p 2 + 5280*p 3 - 3304*p 4 + 3088*p 8 - 4000*p 9 - 1680*p 10 + 6720*p 11 - 3960*p 12 - 1440*p 13 + 2768*p 14 - 1280*p 15 + 216*p 16) + ((108) * (4000*p 1 + 1680*p 2 - 6720*p 3 + 7048*p 4 - 2560*p 5 - 4448*p 6 + 8000*p 7 - 4176*p 8 - 1440*p 9 + 2768*p 10 - 1280*p 11 + 216*p 12) + ((320) * (13392*p 1 - 13640*p 2 + 8448*p 3 - 1792*p 4 - 864*p 5 + 432*p 6 - 432*p 8 + 864*p 9 + 1792*p 10 - 8448*p 11 + 13424*p 12 - 11680*p 13 + 5976*p 14 - 1712*p 15 + 216*p 16) + ((1000) * (20128*p 1 - 7768*p 2 + 848*p 3 + 216*p 4 - 432*p 6 + 864*p 7 + 1792*p 8 - 8448*p 9 + 13424*p 10 - 11680*p 11 + 5976*p 12 - 1712*p 13 + 216*p 14) + ((0) * (7584*p 1 - 12992*p 2 + 11680*p 3 - 6408*p 4 + 2576*p 5 + 1576*p 6 - 8448*p 7 + 13424*p 8 - 11680*p 9 + 5976*p 10 - 1712*p 11 + 216*p 12) + ((0) * (- 864*p 1 - 2224*p 2 + 9312*p 3 - 11632*p 4 + 3232*p 5 + 7448*p 6 - 9968*p 7 + 5760*p 8 - 1712*p 9 + 216*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_4_5 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 4 5 =
      15125008*p 1 - 16454544*p 2 + 12688528*p 3 - 6667360*p 4 + 2620960*p 5 + 1410848*p 6 - 8352736*p 7 + 14912160*p 8 - 15814208*p 9 + 11245632*p 10 - 5654560*p 11 + 2089664*p 12 - 591952*p 13 + 131504*p 14 - 21040*p 15 + 1728*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-72) * (- 10708*p 1 + 4596*p 2 + 1204*p 3 - 3232*p 4 + 4000*p 5 - 6312*p 6 + 8000*p 7 - 6528*p 8 + 2808*p 9 + 1328*p 10 - 3800*p 11 + 3232*p 12 - 1404*p 13 + 388*p 14 - 100*p 15 + 16*p 16) + ((-140) * (2496*p 1 + 3680*p 2 - 6496*p 3 + 928*p 4 + 4000*p 5 - 4000*p 7 - 944*p 8 + 6596*p 9 - 4036*p 10 - 1292*p 11 + 2504*p 12 - 1204*p 13 + 356*p 14 - 100*p 15 + 16*p 16) + ((108) * (- 2596*p 1 + 4036*p 2 - 2708*p 3 - 3448*p 4 + 7800*p 5 - 4392*p 6 - 1192*p 7 + 2488*p 8 - 1204*p 9 + 356*p 10 - 100*p 11 + 16*p 12) + ((320) * (2412*p 1 - 6476*p 2 + 11932*p 3 - 13368*p 4 + 8208*p 5 - 2104*p 6 + 2104*p 8 - 8208*p 9 + 13368*p 10 - 11932*p 11 + 6460*p 12 - 2280*p 13 + 604*p 14 - 132*p 15 + 16*p 16) + ((1000) * (14212*p 1 - 13972*p 2 + 8340*p 3 - 2120*p 4 + 2104*p 6 - 8208*p 7 + 13368*p 8 - 11932*p 9 + 6460*p 10 - 2280*p 11 + 604*p 12 - 132*p 13 + 16*p 14) + ((0) * (20140*p 1 - 8564*p 2 + 2280*p 3 + 1500*p 4 - 8076*p 5 + 13352*p 6 - 11932*p 7 + 6460*p 8 - 2280*p 9 + 604*p 10 - 132*p 11 + 16*p 12) + ((0) * (8208*p 1 - 11264*p 2 + 3724*p 3 + 6908*p 4 - 9652*p 5 + 5856*p 6 - 2148*p 7 + 588*p 8 - 132*p 9 + 16*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_4_6 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 4 6 =
      2073056*p 1 - 8513400*p 2 + 16077520*p 3 - 16159632*p 4 + 4977904*p 5 + 9219944*p 6 - 15570784*p 7 + 12679120*p 8 - 6728096*p 9 + 2567224*p 10 - 774640*p 11 + 208080*p 12 - 52816*p 13 + 11992*p 14 - 2144*p 15 + 216*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-72) * (- 3672*p 1 + 7766*p 2 - 7884*p 3 - 468*p 4 + 9708*p 5 - 11598*p 6 + 7416*p 7 - 944*p 8 - 3736*p 9 + 3798*p 10 - 1692*p 11 + 468*p 12 - 132*p 13 + 34*p 14 - 8*p 15 + 2*p 16) + ((-140) * (1568*p 1 - 2986*p 2 + 724*p 3 + 7258*p 4 - 10292*p 5 + 10292*p 7 - 7260*p 8 - 716*p 9 + 2956*p 10 - 1452*p 11 + 406*p 12 - 116*p 13 + 30*p 14 - 8*p 15 + 2*p 16) + ((108) * (- 9576*p 1 - 2956*p 2 + 11744*p 3 - 7666*p 4 - 600*p 5 + 2926*p 6 - 1444*p 7 + 404*p 8 - 116*p 9 + 30*p 10 - 8*p 11 + 2*p 12) + ((320) * (220*p 1 - 772*p 2 + 2784*p 3 - 7754*p 4 + 13440*p 5 - 11866*p 6 + 11866*p 8 - 13440*p 9 + 7754*p 10 - 2784*p 11 + 770*p 12 - 208*p 13 + 52*p 14 - 12*p 15 + 2*p 16) + ((1000) * (2992*p 1 - 7806*p 2 + 13452*p 3 - 11868*p 4 + 11866*p 6 - 13440*p 7 + 7754*p 8 - 2784*p 9 + 770*p 10 - 208*p 11 + 52*p 12 - 12*p 13 + 2*p 14) + ((0) * (16224*p 1 - 12636*p 2 + 208*p 3 + 11814*p 4 - 13428*p 5 + 7752*p 6 - 2784*p 7 + 770*p 8 - 208*p 9 + 52*p 10 - 12*p 11 + 2*p 12) + ((0) * (13440*p 1 + 4112*p 2 - 10656*p 3 + 6984*p 4 - 2576*p 5 + 718*p 6 - 196*p 7 + 50*p 8 - 12*p 9 + 2*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_5_0 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 5 0 =
      - 10708000*p 1 + 4596000*p 2 + 1204000*p 3 - 3232000*p 4 + 4000000*p 5 - 6312000*p 6 + 8000000*p 7 - 6528000*p 8 + 2808000*p 9 + 1328000*p 10 - 3800000*p 11 + 3232000*p 12 - 1404000*p 13 + 388000*p 14 - 100000*p 15 + 16000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-108) * (8000*p 4 + 8000*p 8 - 8000*p 12 + 2000*p 16) + ((91) * (- 4000*p 2 + 2000*p 4 - 4000*p 8 + 8000*p 10 - 2000*p 12 - 4000*p 14 + 2000*p 16) + ((-26) * (- 8000*p 2 - 2000*p 4 + 12000*p 6 - 4000*p 8 - 4000*p 10 + 2000*p 12) + ((25) * (4000*p 1 + 2000*p 2 - 8000*p 3 + 4000*p 4 - 4000*p 10 + 8000*p 11 - 4000*p 12 + 2000*p 14 - 4000*p 15 + 2000*p 16) + ((351) * (- 8000*p 1 + 2000*p 2 + 4000*p 3 - 2000*p 4 - 4000*p 8 + 8000*p 9 - 4000*p 10 + 2000*p 12 - 4000*p 13 + 2000*p 14) + ((1000) * (- 8000*p 1 + 4000*p 2 - 2000*p 4 + 4000*p 5 - 6000*p 6 + 8000*p 7 - 4000*p 8 + 2000*p 10 - 4000*p 11 + 2000*p 12) + ((0) * (4000*p 2 - 8000*p 3 + 8000*p 5 - 6000*p 6 + 4000*p 7 - 4000*p 9 + 2000*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_5_1 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 5 1 =
      4369900*p 1 + 2875700*p 2 - 6706700*p 3 + 1493600*p 4 + 3300000*p 5 + 1104600*p 6 - 5400000*p 7 + 198400*p 8 + 6104600*p 9 - 4268400*p 10 - 627000*p 11 + 1938400*p 12 - 958300*p 13 + 288100*p 14 - 82500*p 15 + 13200*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-108) * (- 4000*p 2 + 600*p 4 - 5400*p 8 + 8000*p 10 - 600*p 12 - 4000*p 14 + 1650*p 16) + ((91) * (16700*p 2 - 4350*p 4 + 2700*p 8 - 9400*p 10 + 12350*p 12 - 7300*p 14 + 1650*p 16) + ((-26) * (9400*p 2 - 9650*p 4 - 2100*p 6 + 10700*p 8 - 7300*p 10 + 1650*p 12) + ((25) * (- 4700*p 1 - 350*p 2 + 5400*p 3 - 2700*p 4 + 2700*p 10 - 5400*p 11 - 1300*p 12 + 8000*p 13 - 2350*p 14 - 3300*p 15 + 1650*p 16) + ((351) * (- 2600*p 1 - 350*p 2 + 3300*p 3 - 1650*p 4 + 2700*p 8 - 5400*p 9 - 1300*p 10 + 8000*p 11 - 2350*p 12 - 3300*p 13 + 1650*p 14) + ((1000) * (5400*p 1 + 1300*p 2 - 8000*p 3 + 2350*p 4 + 3300*p 5 + 1050*p 6 - 5400*p 7 - 1300*p 8 + 8000*p 9 - 2350*p 10 - 3300*p 11 + 1650*p 12) + ((0) * (- 2700*p 2 + 5400*p 3 + 4000*p 4 - 13400*p 5 + 1050*p 6 + 11300*p 7 - 4000*p 8 - 3300*p 9 + 1650*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_5_2 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 5 2 =
      1153308*p 1 + 4284516*p 2 - 5559772*p 3 - 2248064*p 4 + 8328000*p 5 - 2757192*p 6 - 4828000*p 7 + 3809648*p 8 + 647764*p 9 - 1566028*p 10 + 379028*p 11 + 157976*p 12 - 107128*p 13 + 38704*p 14 - 13200*p 15 + 2112*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-108) * (- 9564*p 2 - 3290*p 4 + 12000*p 6 - 7636*p 8 - 872*p 10 + 3290*p 12 - 1564*p 14 + 264*p 16) + ((91) * (15292*p 2 - 12082*p 4 + 11818*p 8 - 13200*p 10 + 7210*p 12 - 2092*p 14 + 264*p 16) + ((-26) * (13200*p 2 + 4608*p 4 - 11108*p 6 + 6946*p 8 - 2092*p 10 + 264*p 12) + ((25) * (- 2600*p 1 - 2518*p 2 + 7636*p 3 + 182*p 4 - 8000*p 5 + 4000*p 6 - 4000*p 8 + 8000*p 9 - 182*p 10 - 7636*p 11 + 2254*p 12 + 3128*p 13 - 1300*p 14 - 528*p 15 + 264*p 16) + ((351) * (4508*p 1 + 1482*p 2 - 7472*p 3 + 3736*p 4 - 4000*p 6 + 8000*p 7 - 182*p 8 - 7636*p 9 + 2254*p 10 + 3128*p 11 - 1300*p 12 - 528*p 13 + 264*p 14) + ((1000) * (- 364*p 1 + 1746*p 2 - 3128*p 3 - 2700*p 4 + 8528*p 5 - 446*p 6 - 7636*p 7 + 2254*p 8 + 3128*p 9 - 1300*p 10 - 528*p 11 + 264*p 12) + ((0) * (- 8000*p 1 - 3818*p 2 + 15636*p 3 - 2436*p 4 - 10764*p 5 + 3554*p 6 + 3656*p 7 - 1564*p 8 - 528*p 9 + 264*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_5_3 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 5 3 =
      1661904*p 1 - 7325712*p 2 + 13516144*p 3 - 13526592*p 4 + 7120000*p 5 - 2105056*p 6 + 1159680*p 7 + 2031264*p 8 - 9545528*p 9 + 14286936*p 10 - 11747576*p 11 + 5993968*p 12 - 2052024*p 13 + 535832*p 14 - 112600*p 15 + 12896*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-108) * (4000*p 1 + 3208*p 2 - 8000*p 3 + 3860*p 4 - 480*p 6 + 1272*p 8 - 5616*p 10 + 8000*p 11 - 3860*p 12 + 2888*p 14 - 4000*p 15 + 1612*p 16) + ((91) * (- 4000*p 1 - 3984*p 2 + 4000*p 3 - 656*p 4 - 956*p 8 + 4320*p 10 - 4000*p 11 - 4800*p 12 + 8000*p 13 - 336*p 14 - 4000*p 15 + 1612*p 16) + ((-26) * (- 4320*p 2 + 4000*p 3 + 3844*p 4 - 8000*p 5 + 4656*p 6 - 6412*p 8 + 8000*p 9 - 336*p 10 - 4000*p 11 + 1612*p 12) + ((25) * (17000*p 1 - 3864*p 2 - 1272*p 3 + 476*p 4 + 320*p 5 - 160*p 6 + 160*p 8 - 320*p 9 - 476*p 10 + 1272*p 11 + 2252*p 12 - 9776*p 13 + 12500*p 14 - 7224*p 15 + 1612*p 16) + ((351) * (8504*p 1 - 12024*p 2 + 7544*p 3 - 1772*p 4 + 160*p 6 - 320*p 7 - 476*p 8 + 1272*p 9 + 2252*p 10 - 9776*p 11 + 12500*p 12 - 7224*p 13 + 1612*p 14) + ((1000) * (- 952*p 1 - 2412*p 2 + 9776*p 3 - 12340*p 4 + 6904*p 5 - 2088*p 6 + 1272*p 7 + 2252*p 8 - 9776*p 9 + 12500*p 10 - 7224*p 11 + 1612*p 12) + ((0) * (320*p 1 + 636*p 2 - 1592*p 3 - 2728*p 4 + 11048*p 5 - 10248*p 6 - 2552*p 7 + 10888*p 8 - 7224*p 9 + 1612*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_5_4 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 5 4 =
      15125008*p 1 - 16454544*p 2 + 12688528*p 3 - 6667360*p 4 + 2620960*p 5 + 1410848*p 6 - 8352736*p 7 + 14912160*p 8 - 15814208*p 9 + 11245632*p 10 - 5654560*p 11 + 2089664*p 12 - 591952*p 13 + 131504*p 14 - 21040*p 15 + 1728*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-108) * (- 6720*p 1 + 2336*p 2 + 1440*p 3 - 1792*p 4 + 1296*p 6 - 4448*p 8 + 8000*p 9 - 6832*p 10 + 2560*p 11 + 1792*p 12 - 4000*p 13 + 3200*p 14 - 1280*p 15 + 216*p 16) + ((91) * (- 5280*p 1 - 1088*p 2 + 5280*p 3 - 3304*p 4 + 3088*p 8 - 4000*p 9 - 1680*p 10 + 6720*p 11 - 3960*p 12 - 1440*p 13 + 2768*p 14 - 1280*p 15 + 216*p 16) + ((-26) * (4000*p 1 + 1680*p 2 - 6720*p 3 + 7048*p 4 - 2560*p 5 - 4448*p 6 + 8000*p 7 - 4176*p 8 - 1440*p 9 + 2768*p 10 - 1280*p 11 + 216*p 12) + ((25) * (13392*p 1 - 13640*p 2 + 8448*p 3 - 1792*p 4 - 864*p 5 + 432*p 6 - 432*p 8 + 864*p 9 + 1792*p 10 - 8448*p 11 + 13424*p 12 - 11680*p 13 + 5976*p 14 - 1712*p 15 + 216*p 16) + ((351) * (20128*p 1 - 7768*p 2 + 848*p 3 + 216*p 4 - 432*p 6 + 864*p 7 + 1792*p 8 - 8448*p 9 + 13424*p 10 - 11680*p 11 + 5976*p 12 - 1712*p 13 + 216*p 14) + ((1000) * (7584*p 1 - 12992*p 2 + 11680*p 3 - 6408*p 4 + 2576*p 5 + 1576*p 6 - 8448*p 7 + 13424*p 8 - 11680*p 9 + 5976*p 10 - 1712*p 11 + 216*p 12) + ((0) * (- 864*p 1 - 2224*p 2 + 9312*p 3 - 11632*p 4 + 3232*p 5 + 7448*p 6 - 9968*p 7 + 5760*p 8 - 1712*p 9 + 216*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_5_5 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 5 5 =
      26639808*p 1 - 13896496*p 2 + 4854880*p 3 + 944832*p 4 - 8141600*p 5 + 14833792*p 6 - 16010016*p 7 + 11759200*p 8 - 6345056*p 9 + 2685704*p 10 - 935152*p 11 + 267896*p 12 - 61264*p 13 + 11208*p 14 - 1600*p 15 + 128*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-108) * (- 10708*p 1 + 4596*p 2 + 1204*p 3 - 3232*p 4 + 4000*p 5 - 6312*p 6 + 8000*p 7 - 6528*p 8 + 2808*p 9 + 1328*p 10 - 3800*p 11 + 3232*p 12 - 1404*p 13 + 388*p 14 - 100*p 15 + 16*p 16) + ((91) * (2496*p 1 + 3680*p 2 - 6496*p 3 + 928*p 4 + 4000*p 5 - 4000*p 7 - 944*p 8 + 6596*p 9 - 4036*p 10 - 1292*p 11 + 2504*p 12 - 1204*p 13 + 356*p 14 - 100*p 15 + 16*p 16) + ((-26) * (- 2596*p 1 + 4036*p 2 - 2708*p 3 - 3448*p 4 + 7800*p 5 - 4392*p 6 - 1192*p 7 + 2488*p 8 - 1204*p 9 + 356*p 10 - 100*p 11 + 16*p 12) + ((25) * (2412*p 1 - 6476*p 2 + 11932*p 3 - 13368*p 4 + 8208*p 5 - 2104*p 6 + 2104*p 8 - 8208*p 9 + 13368*p 10 - 11932*p 11 + 6460*p 12 - 2280*p 13 + 604*p 14 - 132*p 15 + 16*p 16) + ((351) * (14212*p 1 - 13972*p 2 + 8340*p 3 - 2120*p 4 + 2104*p 6 - 8208*p 7 + 13368*p 8 - 11932*p 9 + 6460*p 10 - 2280*p 11 + 604*p 12 - 132*p 13 + 16*p 14) + ((1000) * (20140*p 1 - 8564*p 2 + 2280*p 3 + 1500*p 4 - 8076*p 5 + 13352*p 6 - 11932*p 7 + 6460*p 8 - 2280*p 9 + 604*p 10 - 132*p 11 + 16*p 12) + ((0) * (8208*p 1 - 11264*p 2 + 3724*p 3 + 6908*p 4 - 9652*p 5 + 5856*p 6 - 2148*p 7 + 588*p 8 - 132*p 9 + 16*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_5_6 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 5 6 =
      18067932*p 1 - 16428804*p 2 + 5611264*p 3 + 8364820*p 4 - 15061436*p 5 + 12796824*p 6 - 7328252*p 7 + 3219092*p 8 - 1179836*p 9 + 374152*p 10 - 103796*p 11 + 25852*p 12 - 5712*p 13 + 1060*p 14 - 164*p 15 + 16*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-108) * (- 3672*p 1 + 7766*p 2 - 7884*p 3 - 468*p 4 + 9708*p 5 - 11598*p 6 + 7416*p 7 - 944*p 8 - 3736*p 9 + 3798*p 10 - 1692*p 11 + 468*p 12 - 132*p 13 + 34*p 14 - 8*p 15 + 2*p 16) + ((91) * (1568*p 1 - 2986*p 2 + 724*p 3 + 7258*p 4 - 10292*p 5 + 10292*p 7 - 7260*p 8 - 716*p 9 + 2956*p 10 - 1452*p 11 + 406*p 12 - 116*p 13 + 30*p 14 - 8*p 15 + 2*p 16) + ((-26) * (- 9576*p 1 - 2956*p 2 + 11744*p 3 - 7666*p 4 - 600*p 5 + 2926*p 6 - 1444*p 7 + 404*p 8 - 116*p 9 + 30*p 10 - 8*p 11 + 2*p 12) + ((25) * (220*p 1 - 772*p 2 + 2784*p 3 - 7754*p 4 + 13440*p 5 - 11866*p 6 + 11866*p 8 - 13440*p 9 + 7754*p 10 - 2784*p 11 + 770*p 12 - 208*p 13 + 52*p 14 - 12*p 15 + 2*p 16) + ((351) * (2992*p 1 - 7806*p 2 + 13452*p 3 - 11868*p 4 + 11866*p 6 - 13440*p 7 + 7754*p 8 - 2784*p 9 + 770*p 10 - 208*p 11 + 52*p 12 - 12*p 13 + 2*p 14) + ((1000) * (16224*p 1 - 12636*p 2 + 208*p 3 + 11814*p 4 - 13428*p 5 + 7752*p 6 - 2784*p 7 + 770*p 8 - 208*p 9 + 52*p 10 - 12*p 11 + 2*p 12) + ((0) * (13440*p 1 + 4112*p 2 - 10656*p 3 + 6984*p 4 - 2576*p 5 + 718*p 6 - 196*p 7 + 50*p 8 - 12*p 9 + 2*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_6_0 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 6 0 =
      - 3672000*p 1 + 7766000*p 2 - 7884000*p 3 - 468000*p 4 + 9708000*p 5 - 11598000*p 6 + 7416000*p 7 - 944000*p 8 - 3736000*p 9 + 3798000*p 10 - 1692000*p 11 + 468000*p 12 - 132000*p 13 + 34000*p 14 - 8000*p 15 + 2000*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-10) * (8000*p 4 + 8000*p 8 - 8000*p 12 + 2000*p 16) + ((9) * (- 4000*p 2 + 2000*p 4 - 4000*p 8 + 8000*p 10 - 2000*p 12 - 4000*p 14 + 2000*p 16) + ((-253) * (- 8000*p 2 - 2000*p 4 + 12000*p 6 - 4000*p 8 - 4000*p 10 + 2000*p 12) + ((2) * (4000*p 1 + 2000*p 2 - 8000*p 3 + 4000*p 4 - 4000*p 10 + 8000*p 11 - 4000*p 12 + 2000*p 14 - 4000*p 15 + 2000*p 16) + ((33) * (- 8000*p 1 + 2000*p 2 + 4000*p 3 - 2000*p 4 - 4000*p 8 + 8000*p 9 - 4000*p 10 + 2000*p 12 - 4000*p 13 + 2000*p 14) + ((427) * (- 8000*p 1 + 4000*p 2 - 2000*p 4 + 4000*p 5 - 6000*p 6 + 8000*p 7 - 4000*p 8 + 2000*p 10 - 4000*p 11 + 2000*p 12) + ((1000) * (4000*p 2 - 8000*p 3 + 8000*p 5 - 6000*p 6 + 4000*p 7 - 4000*p 9 + 2000*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_6_1 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 6 1 =
      2210600*p 1 - 4345050*p 2 + 2103700*p 3 + 7339900*p 4 - 11990900*p 5 + 2029650*p 6 + 8994200*p 7 - 7094800*p 8 - 62200*p 9 + 2291350*p 10 - 1155900*p 11 + 324100*p 12 - 92900*p 13 + 24050*p 14 - 6600*p 15 + 1650*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-10) * (- 4000*p 2 + 600*p 4 - 5400*p 8 + 8000*p 10 - 600*p 12 - 4000*p 14 + 1650*p 16) + ((9) * (16700*p 2 - 4350*p 4 + 2700*p 8 - 9400*p 10 + 12350*p 12 - 7300*p 14 + 1650*p 16) + ((-253) * (9400*p 2 - 9650*p 4 - 2100*p 6 + 10700*p 8 - 7300*p 10 + 1650*p 12) + ((2) * (- 4700*p 1 - 350*p 2 + 5400*p 3 - 2700*p 4 + 2700*p 10 - 5400*p 11 - 1300*p 12 + 8000*p 13 - 2350*p 14 - 3300*p 15 + 1650*p 16) + ((33) * (- 2600*p 1 - 350*p 2 + 3300*p 3 - 1650*p 4 + 2700*p 8 - 5400*p 9 - 1300*p 10 + 8000*p 11 - 2350*p 12 - 3300*p 13 + 1650*p 14) + ((427) * (5400*p 1 + 1300*p 2 - 8000*p 3 + 2350*p 4 + 3300*p 5 + 1050*p 6 - 5400*p 7 - 1300*p 8 + 8000*p 9 - 2350*p 10 - 3300*p 11 + 1650*p 12) + ((1000) * (- 2700*p 2 + 5400*p 3 + 4000*p 4 - 13400*p 5 + 1050*p 6 + 11300*p 7 - 4000*p 8 - 3300*p 9 + 1650*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_6_2 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 6 2 =
      - 8011864*p 1 - 6134920*p 2 + 14069040*p 3 - 4706910*p 4 - 7138544*p 5 + 5929882*p 6 + 659428*p 7 - 2190164*p 8 + 571668*p 9 + 202114*p 10 - 137504*p 11 + 39534*p 12 - 11168*p 13 + 2924*p 14 - 1056*p 15 + 264*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-10) * (- 9564*p 2 - 3290*p 4 + 12000*p 6 - 7636*p 8 - 872*p 10 + 3290*p 12 - 1564*p 14 + 264*p 16) + ((9) * (15292*p 2 - 12082*p 4 + 11818*p 8 - 13200*p 10 + 7210*p 12 - 2092*p 14 + 264*p 16) + ((-253) * (13200*p 2 + 4608*p 4 - 11108*p 6 + 6946*p 8 - 2092*p 10 + 264*p 12) + ((2) * (- 2600*p 1 - 2518*p 2 + 7636*p 3 + 182*p 4 - 8000*p 5 + 4000*p 6 - 4000*p 8 + 8000*p 9 - 182*p 10 - 7636*p 11 + 2254*p 12 + 3128*p 13 - 1300*p 14 - 528*p 15 + 264*p 16) + ((33) * (4508*p 1 + 1482*p 2 - 7472*p 3 + 3736*p 4 - 4000*p 6 + 8000*p 7 - 182*p 8 - 7636*p 9 + 2254*p 10 + 3128*p 11 - 1300*p 12 - 528*p 13 + 264*p 14) + ((427) * (- 364*p 1 + 1746*p 2 - 3128*p 3 - 2700*p 4 + 8528*p 5 - 446*p 6 - 7636*p 7 + 2254*p 8 + 3128*p 9 - 1300*p 10 - 528*p 11 + 264*p 12) + ((1000) * (- 8000*p 1 - 3818*p 2 + 15636*p 3 - 2436*p 4 - 10764*p 5 + 3554*p 6 + 3656*p 7 - 1564*p 8 - 528*p 9 + 264*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_6_3 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 6 3 =
      152128*p 1 + 226580*p 2 + 1932760*p 3 - 9071740*p 4 + 16020648*p 5 - 12307784*p 6 - 2019416*p 7 + 13435128*p 8 - 13381016*p 9 + 7202912*p 10 - 2508712*p 11 + 692892*p 12 - 185944*p 13 + 46292*p 14 - 10448*p 15 + 1612*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-10) * (4000*p 1 + 3208*p 2 - 8000*p 3 + 3860*p 4 - 480*p 6 + 1272*p 8 - 5616*p 10 + 8000*p 11 - 3860*p 12 + 2888*p 14 - 4000*p 15 + 1612*p 16) + ((9) * (- 4000*p 1 - 3984*p 2 + 4000*p 3 - 656*p 4 - 956*p 8 + 4320*p 10 - 4000*p 11 - 4800*p 12 + 8000*p 13 - 336*p 14 - 4000*p 15 + 1612*p 16) + ((-253) * (- 4320*p 2 + 4000*p 3 + 3844*p 4 - 8000*p 5 + 4656*p 6 - 6412*p 8 + 8000*p 9 - 336*p 10 - 4000*p 11 + 1612*p 12) + ((2) * (17000*p 1 - 3864*p 2 - 1272*p 3 + 476*p 4 + 320*p 5 - 160*p 6 + 160*p 8 - 320*p 9 - 476*p 10 + 1272*p 11 + 2252*p 12 - 9776*p 13 + 12500*p 14 - 7224*p 15 + 1612*p 16) + ((33) * (8504*p 1 - 12024*p 2 + 7544*p 3 - 1772*p 4 + 160*p 6 - 320*p 7 - 476*p 8 + 1272*p 9 + 2252*p 10 - 9776*p 11 + 12500*p 12 - 7224*p 13 + 1612*p 14) + ((427) * (- 952*p 1 - 2412*p 2 + 9776*p 3 - 12340*p 4 + 6904*p 5 - 2088*p 6 + 1272*p 7 + 2252*p 8 - 9776*p 9 + 12500*p 10 - 7224*p 11 + 1612*p 12) + ((1000) * (320*p 1 + 636*p 2 - 1592*p 3 - 2728*p 4 + 11048*p 5 - 10248*p 6 - 2552*p 7 + 10888*p 8 - 7224*p 9 + 1612*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_6_4 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 6 4 =
      2073056*p 1 - 8513400*p 2 + 16077520*p 3 - 16159632*p 4 + 4977904*p 5 + 9219944*p 6 - 15570784*p 7 + 12679120*p 8 - 6728096*p 9 + 2567224*p 10 - 774640*p 11 + 208080*p 12 - 52816*p 13 + 11992*p 14 - 2144*p 15 + 216*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-10) * (- 6720*p 1 + 2336*p 2 + 1440*p 3 - 1792*p 4 + 1296*p 6 - 4448*p 8 + 8000*p 9 - 6832*p 10 + 2560*p 11 + 1792*p 12 - 4000*p 13 + 3200*p 14 - 1280*p 15 + 216*p 16) + ((9) * (- 5280*p 1 - 1088*p 2 + 5280*p 3 - 3304*p 4 + 3088*p 8 - 4000*p 9 - 1680*p 10 + 6720*p 11 - 3960*p 12 - 1440*p 13 + 2768*p 14 - 1280*p 15 + 216*p 16) + ((-253) * (4000*p 1 + 1680*p 2 - 6720*p 3 + 7048*p 4 - 2560*p 5 - 4448*p 6 + 8000*p 7 - 4176*p 8 - 1440*p 9 + 2768*p 10 - 1280*p 11 + 216*p 12) + ((2) * (13392*p 1 - 13640*p 2 + 8448*p 3 - 1792*p 4 - 864*p 5 + 432*p 6 - 432*p 8 + 864*p 9 + 1792*p 10 - 8448*p 11 + 13424*p 12 - 11680*p 13 + 5976*p 14 - 1712*p 15 + 216*p 16) + ((33) * (20128*p 1 - 7768*p 2 + 848*p 3 + 216*p 4 - 432*p 6 + 864*p 7 + 1792*p 8 - 8448*p 9 + 13424*p 10 - 11680*p 11 + 5976*p 12 - 1712*p 13 + 216*p 14) + ((427) * (7584*p 1 - 12992*p 2 + 11680*p 3 - 6408*p 4 + 2576*p 5 + 1576*p 6 - 8448*p 7 + 13424*p 8 - 11680*p 9 + 5976*p 10 - 1712*p 11 + 216*p 12) + ((1000) * (- 864*p 1 - 2224*p 2 + 9312*p 3 - 11632*p 4 + 3232*p 5 + 7448*p 6 - 9968*p 7 + 5760*p 8 - 1712*p 9 + 216*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_6_5 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 6 5 =
      18067932*p 1 - 16428804*p 2 + 5611264*p 3 + 8364820*p 4 - 15061436*p 5 + 12796824*p 6 - 7328252*p 7 + 3219092*p 8 - 1179836*p 9 + 374152*p 10 - 103796*p 11 + 25852*p 12 - 5712*p 13 + 1060*p 14 - 164*p 15 + 16*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-10) * (- 10708*p 1 + 4596*p 2 + 1204*p 3 - 3232*p 4 + 4000*p 5 - 6312*p 6 + 8000*p 7 - 6528*p 8 + 2808*p 9 + 1328*p 10 - 3800*p 11 + 3232*p 12 - 1404*p 13 + 388*p 14 - 100*p 15 + 16*p 16) + ((9) * (2496*p 1 + 3680*p 2 - 6496*p 3 + 928*p 4 + 4000*p 5 - 4000*p 7 - 944*p 8 + 6596*p 9 - 4036*p 10 - 1292*p 11 + 2504*p 12 - 1204*p 13 + 356*p 14 - 100*p 15 + 16*p 16) + ((-253) * (- 2596*p 1 + 4036*p 2 - 2708*p 3 - 3448*p 4 + 7800*p 5 - 4392*p 6 - 1192*p 7 + 2488*p 8 - 1204*p 9 + 356*p 10 - 100*p 11 + 16*p 12) + ((2) * (2412*p 1 - 6476*p 2 + 11932*p 3 - 13368*p 4 + 8208*p 5 - 2104*p 6 + 2104*p 8 - 8208*p 9 + 13368*p 10 - 11932*p 11 + 6460*p 12 - 2280*p 13 + 604*p 14 - 132*p 15 + 16*p 16) + ((33) * (14212*p 1 - 13972*p 2 + 8340*p 3 - 2120*p 4 + 2104*p 6 - 8208*p 7 + 13368*p 8 - 11932*p 9 + 6460*p 10 - 2280*p 11 + 604*p 12 - 132*p 13 + 16*p 14) + ((427) * (20140*p 1 - 8564*p 2 + 2280*p 3 + 1500*p 4 - 8076*p 5 + 13352*p 6 - 11932*p 7 + 6460*p 8 - 2280*p 9 + 604*p 10 - 132*p 11 + 16*p 12) + ((1000) * (8208*p 1 - 11264*p 2 + 3724*p 3 + 6908*p 4 - 9652*p 5 + 5856*p 6 - 2148*p 7 + 588*p 8 - 132*p 9 + 16*p 10) + (0))))))) = _
  ring

theorem fourthLevelEvenCongruenceEntry_6_6 (p : Fin 17 → ℝ) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 6 6 =
      22940384*p 1 - 899380*p 2 - 13003576*p 3 + 13630926*p 4 - 8320784*p 5 + 3771652*p 6 - 1444488*p 7 + 500292*p 8 - 159304*p 9 + 46156*p 10 - 11680*p 11 + 2578*p 12 - 536*p 13 + 100*p 14 - 16*p 15 + 2*p 16 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.transpose_apply]
  change (-10) * (- 3672*p 1 + 7766*p 2 - 7884*p 3 - 468*p 4 + 9708*p 5 - 11598*p 6 + 7416*p 7 - 944*p 8 - 3736*p 9 + 3798*p 10 - 1692*p 11 + 468*p 12 - 132*p 13 + 34*p 14 - 8*p 15 + 2*p 16) + ((9) * (1568*p 1 - 2986*p 2 + 724*p 3 + 7258*p 4 - 10292*p 5 + 10292*p 7 - 7260*p 8 - 716*p 9 + 2956*p 10 - 1452*p 11 + 406*p 12 - 116*p 13 + 30*p 14 - 8*p 15 + 2*p 16) + ((-253) * (- 9576*p 1 - 2956*p 2 + 11744*p 3 - 7666*p 4 - 600*p 5 + 2926*p 6 - 1444*p 7 + 404*p 8 - 116*p 9 + 30*p 10 - 8*p 11 + 2*p 12) + ((2) * (220*p 1 - 772*p 2 + 2784*p 3 - 7754*p 4 + 13440*p 5 - 11866*p 6 + 11866*p 8 - 13440*p 9 + 7754*p 10 - 2784*p 11 + 770*p 12 - 208*p 13 + 52*p 14 - 12*p 15 + 2*p 16) + ((33) * (2992*p 1 - 7806*p 2 + 13452*p 3 - 11868*p 4 + 11866*p 6 - 13440*p 7 + 7754*p 8 - 2784*p 9 + 770*p 10 - 208*p 11 + 52*p 12 - 12*p 13 + 2*p 14) + ((427) * (16224*p 1 - 12636*p 2 + 208*p 3 + 11814*p 4 - 13428*p 5 + 7752*p 6 - 2784*p 7 + 770*p 8 - 208*p 9 + 52*p 10 - 12*p 11 + 2*p 12) + ((1000) * (13440*p 1 + 4112*p 2 - 10656*p 3 + 6984*p 4 - 2576*p 5 + 718*p 6 - 196*p 7 + 50*p 8 - 12*p 9 + 2*p 10) + (0))))))) = _
  ring

def fourthLevelEvenCongruencePolynomial (p : Fin 17 → ℝ) : Matrix (Fin 7) (Fin 7) ℝ :=
  ![![8000000*p 4 + 8000000*p 8 - 8000000*p 12 + 2000000*p 16,
    - 4000000*p 2 + 600000*p 4 - 5400000*p 8 + 8000000*p 10 - 600000*p 12 - 4000000*p 14 + 1650000*p 16,
    - 9564000*p 2 - 3290000*p 4 + 12000000*p 6 - 7636000*p 8 - 872000*p 10 + 3290000*p 12 - 1564000*p 14 + 264000*p 16,
    4000000*p 1 + 3208000*p 2 - 8000000*p 3 + 3860000*p 4 - 480000*p 6 + 1272000*p 8 - 5616000*p 10 + 8000000*p 11 - 3860000*p 12 + 2888000*p 14 - 4000000*p 15 + 1612000*p 16,
    - 6720000*p 1 + 2336000*p 2 + 1440000*p 3 - 1792000*p 4 + 1296000*p 6 - 4448000*p 8 + 8000000*p 9 - 6832000*p 10 + 2560000*p 11 + 1792000*p 12 - 4000000*p 13 + 3200000*p 14 - 1280000*p 15 + 216000*p 16,
    - 10708000*p 1 + 4596000*p 2 + 1204000*p 3 - 3232000*p 4 + 4000000*p 5 - 6312000*p 6 + 8000000*p 7 - 6528000*p 8 + 2808000*p 9 + 1328000*p 10 - 3800000*p 11 + 3232000*p 12 - 1404000*p 13 + 388000*p 14 - 100000*p 15 + 16000*p 16,
    - 3672000*p 1 + 7766000*p 2 - 7884000*p 3 - 468000*p 4 + 9708000*p 5 - 11598000*p 6 + 7416000*p 7 - 944000*p 8 - 3736000*p 9 + 3798000*p 10 - 1692000*p 11 + 468000*p 12 - 132000*p 13 + 34000*p 14 - 8000*p 15 + 2000*p 16],
  ![- 4000000*p 2 + 600000*p 4 - 5400000*p 8 + 8000000*p 10 - 600000*p 12 - 4000000*p 14 + 1650000*p 16,
    17400000*p 2 - 4455000*p 4 + 3645000*p 8 - 10800000*p 10 + 12455000*p 12 - 6600000*p 14 + 1361250*p 16,
    16965700*p 2 - 11506250*p 4 - 2100000*p 6 + 13154300*p 8 - 13047400*p 10 + 6634250*p 12 - 1818300*p 14 + 217800*p 16,
    - 4700000*p 1 - 4545400*p 2 + 5400000*p 3 - 1331500*p 4 + 84000*p 6 - 1178600*p 8 + 5302800*p 10 - 5400000*p 11 - 4124500*p 12 + 8000000*p 13 - 841400*p 14 - 3300000*p 15 + 1329900*p 16,
    - 4104000*p 1 - 1496800*p 2 + 5028000*p 3 - 2990400*p 4 - 226800*p 6 + 3866400*p 8 - 5400000*p 9 - 484400*p 10 + 6272000*p 11 - 4273600*p 12 - 740000*p 13 + 2208000*p 14 - 1056000*p 15 + 178200*p 16,
    4369900*p 1 + 2875700*p 2 - 6706700*p 3 + 1493600*p 4 + 3300000*p 5 + 1104600*p 6 - 5400000*p 7 + 198400*p 8 + 6104600*p 9 - 4268400*p 10 - 627000*p 11 + 1938400*p 12 - 958300*p 13 + 288100*p 14 - 82500*p 15 + 13200*p 16,
    2210600*p 1 - 4345050*p 2 + 2103700*p 3 + 7339900*p 4 - 11990900*p 5 + 2029650*p 6 + 8994200*p 7 - 7094800*p 8 - 62200*p 9 + 2291350*p 10 - 1155900*p 11 + 324100*p 12 - 92900*p 13 + 24050*p 14 - 6600*p 15 + 1650*p 16],
  ![- 9564000*p 2 - 3290000*p 4 + 12000000*p 6 - 7636000*p 8 - 872000*p 10 + 3290000*p 12 - 1564000*p 14 + 264000*p 16,
    16965700*p 2 - 11506250*p 4 - 2100000*p 6 + 13154300*p 8 - 13047400*p 10 + 6634250*p 12 - 1818300*p 14 + 217800*p 16,
    21656248*p 2 + 736048*p 4 - 14216000*p 6 + 13544562*p 8 - 7027352*p 10 + 2231000*p 12 - 412896*p 14 + 34848*p 16,
    - 2600000*p 1 - 6708616*p 2 + 7636000*p 3 + 2587764*p 4 - 8000000*p 5 + 4780320*p 6 - 7115244*p 8 + 8000000*p 9 + 2807664*p 10 - 7636000*p 11 + 734940*p 12 + 3128000*p 13 - 879368*p 14 - 528000*p 15 + 212784*p 16,
    3676000*p 1 + 649568*p 2 - 5028480*p 3 + 6220264*p 4 - 2560000*p 5 - 4783664*p 6 + 8000000*p 7 - 1816560*p 8 - 5076000*p 9 + 3880608*p 10 + 684480*p 11 - 1796488*p 12 + 472960*p 13 + 253488*p 14 - 168960*p 15 + 28512*p 16,
    1153308*p 1 + 4284516*p 2 - 5559772*p 3 - 2248064*p 4 + 8328000*p 5 - 2757192*p 6 - 4828000*p 7 + 3809648*p 8 + 647764*p 9 - 1566028*p 10 + 379028*p 11 + 157976*p 12 - 107128*p 13 + 38704*p 14 - 13200*p 15 + 2112*p 16,
    - 8011864*p 1 - 6134920*p 2 + 14069040*p 3 - 4706910*p 4 - 7138544*p 5 + 5929882*p 6 + 659428*p 7 - 2190164*p 8 + 571668*p 9 + 202114*p 10 - 137504*p 11 + 39534*p 12 - 11168*p 13 + 2924*p 14 - 1056*p 15 + 264*p 16],
  ![4000000*p 1 + 3208000*p 2 - 8000000*p 3 + 3860000*p 4 - 480000*p 6 + 1272000*p 8 - 5616000*p 10 + 8000000*p 11 - 3860000*p 12 + 2888000*p 14 - 4000000*p 15 + 1612000*p 16,
    - 4700000*p 1 - 4545400*p 2 + 5400000*p 3 - 1331500*p 4 + 84000*p 6 - 1178600*p 8 + 5302800*p 10 - 5400000*p 11 - 4124500*p 12 + 8000000*p 13 - 841400*p 14 - 3300000*p 15 + 1329900*p 16,
    - 2600000*p 1 - 6708616*p 2 + 7636000*p 3 + 2587764*p 4 - 8000000*p 5 + 4780320*p 6 - 7115244*p 8 + 8000000*p 9 + 2807664*p 10 - 7636000*p 11 + 734940*p 12 + 3128000*p 13 - 879368*p 14 - 528000*p 15 + 212784*p 16,
    18000000*p 1 - 2716928*p 2 - 2544000*p 3 + 575952*p 4 + 640000*p 5 - 359680*p 6 + 664328*p 8 - 640000*p 9 - 1578848*p 10 + 2544000*p 11 + 3145040*p 12 - 11552000*p 13 + 12655456*p 14 - 6448000*p 15 + 1299272*p 16,
    14216000*p 1 - 13400256*p 2 + 7584960*p 3 - 1390608*p 4 - 761600*p 5 + 646208*p 6 - 320000*p 7 - 1075040*p 8 + 2033600*p 9 + 1862944*p 10 - 9816960*p 11 + 14344656*p 12 - 11472320*p 13 + 5451104*p 14 - 1463680*p 15 + 174096*p 16,
    1661904*p 1 - 7325712*p 2 + 13516144*p 3 - 13526592*p 4 + 7120000*p 5 - 2105056*p 6 + 1159680*p 7 + 2031264*p 8 - 9545528*p 9 + 14286936*p 10 - 11747576*p 11 + 5993968*p 12 - 2052024*p 13 + 535832*p 14 - 112600*p 15 + 12896*p 16,
    152128*p 1 + 226580*p 2 + 1932760*p 3 - 9071740*p 4 + 16020648*p 5 - 12307784*p 6 - 2019416*p 7 + 13435128*p 8 - 13381016*p 9 + 7202912*p 10 - 2508712*p 11 + 692892*p 12 - 185944*p 13 + 46292*p 14 - 10448*p 15 + 1612*p 16],
  ![- 6720000*p 1 + 2336000*p 2 + 1440000*p 3 - 1792000*p 4 + 1296000*p 6 - 4448000*p 8 + 8000000*p 9 - 6832000*p 10 + 2560000*p 11 + 1792000*p 12 - 4000000*p 13 + 3200000*p 14 - 1280000*p 15 + 216000*p 16,
    - 4104000*p 1 - 1496800*p 2 + 5028000*p 3 - 2990400*p 4 - 226800*p 6 + 3866400*p 8 - 5400000*p 9 - 484400*p 10 + 6272000*p 11 - 4273600*p 12 - 740000*p 13 + 2208000*p 14 - 1056000*p 15 + 178200*p 16,
    3676000*p 1 + 649568*p 2 - 5028480*p 3 + 6220264*p 4 - 2560000*p 5 - 4783664*p 6 + 8000000*p 7 - 1816560*p 8 - 5076000*p 9 + 3880608*p 10 + 684480*p 11 - 1796488*p 12 + 472960*p 13 + 253488*p 14 - 168960*p 15 + 28512*p 16,
    14216000*p 1 - 13400256*p 2 + 7584960*p 3 - 1390608*p 4 - 761600*p 5 + 646208*p 6 - 320000*p 7 - 1075040*p 8 + 2033600*p 9 + 1862944*p 10 - 9816960*p 11 + 14344656*p 12 - 11472320*p 13 + 5451104*p 14 - 1463680*p 15 + 174096*p 16,
    26068480*p 1 - 11967232*p 2 + 1982720*p 3 + 995328*p 4 - 552960*p 5 - 867456*p 6 + 1728000*p 7 + 1090688*p 8 - 8343040*p 9 + 15023488*p 10 - 15646720*p 11 + 10720384*p 12 - 4960000*p 13 + 1510400*p 14 - 276480*p 15 + 23328*p 16,
    15125008*p 1 - 16454544*p 2 + 12688528*p 3 - 6667360*p 4 + 2620960*p 5 + 1410848*p 6 - 8352736*p 7 + 14912160*p 8 - 15814208*p 9 + 11245632*p 10 - 5654560*p 11 + 2089664*p 12 - 591952*p 13 + 131504*p 14 - 21040*p 15 + 1728*p 16,
    2073056*p 1 - 8513400*p 2 + 16077520*p 3 - 16159632*p 4 + 4977904*p 5 + 9219944*p 6 - 15570784*p 7 + 12679120*p 8 - 6728096*p 9 + 2567224*p 10 - 774640*p 11 + 208080*p 12 - 52816*p 13 + 11992*p 14 - 2144*p 15 + 216*p 16],
  ![- 10708000*p 1 + 4596000*p 2 + 1204000*p 3 - 3232000*p 4 + 4000000*p 5 - 6312000*p 6 + 8000000*p 7 - 6528000*p 8 + 2808000*p 9 + 1328000*p 10 - 3800000*p 11 + 3232000*p 12 - 1404000*p 13 + 388000*p 14 - 100000*p 15 + 16000*p 16,
    4369900*p 1 + 2875700*p 2 - 6706700*p 3 + 1493600*p 4 + 3300000*p 5 + 1104600*p 6 - 5400000*p 7 + 198400*p 8 + 6104600*p 9 - 4268400*p 10 - 627000*p 11 + 1938400*p 12 - 958300*p 13 + 288100*p 14 - 82500*p 15 + 13200*p 16,
    1153308*p 1 + 4284516*p 2 - 5559772*p 3 - 2248064*p 4 + 8328000*p 5 - 2757192*p 6 - 4828000*p 7 + 3809648*p 8 + 647764*p 9 - 1566028*p 10 + 379028*p 11 + 157976*p 12 - 107128*p 13 + 38704*p 14 - 13200*p 15 + 2112*p 16,
    1661904*p 1 - 7325712*p 2 + 13516144*p 3 - 13526592*p 4 + 7120000*p 5 - 2105056*p 6 + 1159680*p 7 + 2031264*p 8 - 9545528*p 9 + 14286936*p 10 - 11747576*p 11 + 5993968*p 12 - 2052024*p 13 + 535832*p 14 - 112600*p 15 + 12896*p 16,
    15125008*p 1 - 16454544*p 2 + 12688528*p 3 - 6667360*p 4 + 2620960*p 5 + 1410848*p 6 - 8352736*p 7 + 14912160*p 8 - 15814208*p 9 + 11245632*p 10 - 5654560*p 11 + 2089664*p 12 - 591952*p 13 + 131504*p 14 - 21040*p 15 + 1728*p 16,
    26639808*p 1 - 13896496*p 2 + 4854880*p 3 + 944832*p 4 - 8141600*p 5 + 14833792*p 6 - 16010016*p 7 + 11759200*p 8 - 6345056*p 9 + 2685704*p 10 - 935152*p 11 + 267896*p 12 - 61264*p 13 + 11208*p 14 - 1600*p 15 + 128*p 16,
    18067932*p 1 - 16428804*p 2 + 5611264*p 3 + 8364820*p 4 - 15061436*p 5 + 12796824*p 6 - 7328252*p 7 + 3219092*p 8 - 1179836*p 9 + 374152*p 10 - 103796*p 11 + 25852*p 12 - 5712*p 13 + 1060*p 14 - 164*p 15 + 16*p 16],
  ![- 3672000*p 1 + 7766000*p 2 - 7884000*p 3 - 468000*p 4 + 9708000*p 5 - 11598000*p 6 + 7416000*p 7 - 944000*p 8 - 3736000*p 9 + 3798000*p 10 - 1692000*p 11 + 468000*p 12 - 132000*p 13 + 34000*p 14 - 8000*p 15 + 2000*p 16,
    2210600*p 1 - 4345050*p 2 + 2103700*p 3 + 7339900*p 4 - 11990900*p 5 + 2029650*p 6 + 8994200*p 7 - 7094800*p 8 - 62200*p 9 + 2291350*p 10 - 1155900*p 11 + 324100*p 12 - 92900*p 13 + 24050*p 14 - 6600*p 15 + 1650*p 16,
    - 8011864*p 1 - 6134920*p 2 + 14069040*p 3 - 4706910*p 4 - 7138544*p 5 + 5929882*p 6 + 659428*p 7 - 2190164*p 8 + 571668*p 9 + 202114*p 10 - 137504*p 11 + 39534*p 12 - 11168*p 13 + 2924*p 14 - 1056*p 15 + 264*p 16,
    152128*p 1 + 226580*p 2 + 1932760*p 3 - 9071740*p 4 + 16020648*p 5 - 12307784*p 6 - 2019416*p 7 + 13435128*p 8 - 13381016*p 9 + 7202912*p 10 - 2508712*p 11 + 692892*p 12 - 185944*p 13 + 46292*p 14 - 10448*p 15 + 1612*p 16,
    2073056*p 1 - 8513400*p 2 + 16077520*p 3 - 16159632*p 4 + 4977904*p 5 + 9219944*p 6 - 15570784*p 7 + 12679120*p 8 - 6728096*p 9 + 2567224*p 10 - 774640*p 11 + 208080*p 12 - 52816*p 13 + 11992*p 14 - 2144*p 15 + 216*p 16,
    18067932*p 1 - 16428804*p 2 + 5611264*p 3 + 8364820*p 4 - 15061436*p 5 + 12796824*p 6 - 7328252*p 7 + 3219092*p 8 - 1179836*p 9 + 374152*p 10 - 103796*p 11 + 25852*p 12 - 5712*p 13 + 1060*p 14 - 164*p 15 + 16*p 16,
    22940384*p 1 - 899380*p 2 - 13003576*p 3 + 13630926*p 4 - 8320784*p 5 + 3771652*p 6 - 1444488*p 7 + 500292*p 8 - 159304*p 9 + 46156*p 10 - 11680*p 11 + 2578*p 12 - 536*p 13 + 100*p 14 - 16*p 15 + 2*p 16]]

theorem fourthLevelEvenCongruence_row0 (p : Fin 17 → ℝ) (j : Fin 7) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 0 j =
      fourthLevelEvenCongruencePolynomial p 0 j := by
  fin_cases j
  · exact fourthLevelEvenCongruenceEntry_0_0 p
  · exact fourthLevelEvenCongruenceEntry_0_1 p
  · exact fourthLevelEvenCongruenceEntry_0_2 p
  · exact fourthLevelEvenCongruenceEntry_0_3 p
  · exact fourthLevelEvenCongruenceEntry_0_4 p
  · exact fourthLevelEvenCongruenceEntry_0_5 p
  · exact fourthLevelEvenCongruenceEntry_0_6 p

theorem fourthLevelEvenCongruence_row1 (p : Fin 17 → ℝ) (j : Fin 7) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 1 j =
      fourthLevelEvenCongruencePolynomial p 1 j := by
  fin_cases j
  · exact fourthLevelEvenCongruenceEntry_1_0 p
  · exact fourthLevelEvenCongruenceEntry_1_1 p
  · exact fourthLevelEvenCongruenceEntry_1_2 p
  · exact fourthLevelEvenCongruenceEntry_1_3 p
  · exact fourthLevelEvenCongruenceEntry_1_4 p
  · exact fourthLevelEvenCongruenceEntry_1_5 p
  · exact fourthLevelEvenCongruenceEntry_1_6 p

theorem fourthLevelEvenCongruence_row2 (p : Fin 17 → ℝ) (j : Fin 7) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 2 j =
      fourthLevelEvenCongruencePolynomial p 2 j := by
  fin_cases j
  · exact fourthLevelEvenCongruenceEntry_2_0 p
  · exact fourthLevelEvenCongruenceEntry_2_1 p
  · exact fourthLevelEvenCongruenceEntry_2_2 p
  · exact fourthLevelEvenCongruenceEntry_2_3 p
  · exact fourthLevelEvenCongruenceEntry_2_4 p
  · exact fourthLevelEvenCongruenceEntry_2_5 p
  · exact fourthLevelEvenCongruenceEntry_2_6 p

theorem fourthLevelEvenCongruence_row3 (p : Fin 17 → ℝ) (j : Fin 7) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 3 j =
      fourthLevelEvenCongruencePolynomial p 3 j := by
  fin_cases j
  · exact fourthLevelEvenCongruenceEntry_3_0 p
  · exact fourthLevelEvenCongruenceEntry_3_1 p
  · exact fourthLevelEvenCongruenceEntry_3_2 p
  · exact fourthLevelEvenCongruenceEntry_3_3 p
  · exact fourthLevelEvenCongruenceEntry_3_4 p
  · exact fourthLevelEvenCongruenceEntry_3_5 p
  · exact fourthLevelEvenCongruenceEntry_3_6 p

theorem fourthLevelEvenCongruence_row4 (p : Fin 17 → ℝ) (j : Fin 7) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 4 j =
      fourthLevelEvenCongruencePolynomial p 4 j := by
  fin_cases j
  · exact fourthLevelEvenCongruenceEntry_4_0 p
  · exact fourthLevelEvenCongruenceEntry_4_1 p
  · exact fourthLevelEvenCongruenceEntry_4_2 p
  · exact fourthLevelEvenCongruenceEntry_4_3 p
  · exact fourthLevelEvenCongruenceEntry_4_4 p
  · exact fourthLevelEvenCongruenceEntry_4_5 p
  · exact fourthLevelEvenCongruenceEntry_4_6 p

theorem fourthLevelEvenCongruence_row5 (p : Fin 17 → ℝ) (j : Fin 7) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 5 j =
      fourthLevelEvenCongruencePolynomial p 5 j := by
  fin_cases j
  · exact fourthLevelEvenCongruenceEntry_5_0 p
  · exact fourthLevelEvenCongruenceEntry_5_1 p
  · exact fourthLevelEvenCongruenceEntry_5_2 p
  · exact fourthLevelEvenCongruenceEntry_5_3 p
  · exact fourthLevelEvenCongruenceEntry_5_4 p
  · exact fourthLevelEvenCongruenceEntry_5_5 p
  · exact fourthLevelEvenCongruenceEntry_5_6 p

theorem fourthLevelEvenCongruence_row6 (p : Fin 17 → ℝ) (j : Fin 7) :
    (fourthLevelEvenShearNumerator.transpose * fourthLevelEvenRightPolynomial p) 6 j =
      fourthLevelEvenCongruencePolynomial p 6 j := by
  fin_cases j
  · exact fourthLevelEvenCongruenceEntry_6_0 p
  · exact fourthLevelEvenCongruenceEntry_6_1 p
  · exact fourthLevelEvenCongruenceEntry_6_2 p
  · exact fourthLevelEvenCongruenceEntry_6_3 p
  · exact fourthLevelEvenCongruenceEntry_6_4 p
  · exact fourthLevelEvenCongruenceEntry_6_5 p
  · exact fourthLevelEvenCongruenceEntry_6_6 p

theorem fourthLevelEvenCongruence_eq (p : Fin 17 → ℝ) :
    fourthLevelEvenShearNumerator.transpose * fourthLevelEvenPolynomial p *
        fourthLevelEvenShearNumerator =
      fourthLevelEvenCongruencePolynomial p := by
  rw [Matrix.mul_assoc, fourthLevelEvenRight_eq]
  ext i j
  fin_cases i
  · exact fourthLevelEvenCongruence_row0 p j
  · exact fourthLevelEvenCongruence_row1 p j
  · exact fourthLevelEvenCongruence_row2 p j
  · exact fourthLevelEvenCongruence_row3 p j
  · exact fourthLevelEvenCongruence_row4 p j
  · exact fourthLevelEvenCongruence_row5 p j
  · exact fourthLevelEvenCongruence_row6 p j


theorem realMatrix_congruence_quadratic {n m : Type*} [Fintype n] [Fintype m]
    (S : Matrix n m ℝ) (B : Matrix n n ℝ) (w : m → ℝ) :
    dotProduct w ((S.transpose * B * S).mulVec w) =
      dotProduct (S.mulVec w) (B.mulVec (S.mulVec w)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  congr 1
  ext i
  simp [Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]

theorem realMatrix_congruence_isHermitian {n m : Type*} [Fintype n] [Fintype m]
    (S : Matrix n m ℝ) {B : Matrix n n ℝ} (hB : B.IsHermitian) :
    (S.transpose * B * S).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  have hs := Matrix.isHermitian_iff_isSymm.mp hB
  change B.transpose = B at hs
  change (S.transpose * B * S).transpose = _
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hs, Matrix.mul_assoc]

theorem realMatrix_scaled_shift_congruence {n : Type*} [Fintype n]
    (N B D : Matrix n n ℝ) :
    ((1/1000 : ℝ) • N).transpose * (B-(1/1000000000 : ℝ) • D) *
        ((1/1000 : ℝ) • N) =
      (1/1000000 : ℝ) • (N.transpose * B * N) -
        (1/1000000000000000 : ℝ) • (N.transpose * D * N) := by
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.mul_sub, Matrix.sub_mul, smul_sub]
  norm_num
def fourthLevelOddGramWeight (i : Fin 8) : ℝ := if i = 0 then 1 else 2

def fourthLevelOddGramNumerator : Matrix (Fin 8) (Fin 8) ℝ :=
  ![![1000000,-250000,82000,-146000,11000,-5000,19000,-74000],
  ![-250000,2062500,-450500,18500,63250,-132750,-250750,154500],
  ![82000,-450500,2099174,473898,-417288,-247600,230448,-25308],
  ![-146000,18500,473898,2137640,-187564,183420,-136144,1990],
  ![11000,63250,-417288,-187564,2087779,684363,12371,4094],
  ![-5000,-132750,-247600,183420,684363,2285211,663483,29282],
  ![19000,-250750,230448,-136144,12371,663483,2292943,515244],
  ![-74000,154500,-25308,1990,4094,29282,515244,2149788]]

theorem fourthLevelOddGramEntry_0_0 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 0 0 = 1000000 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (1000) * (1) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_0_1 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 0 1 = -250000 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (1000) * (1) * (-250) + ((0) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_0_2 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 0 2 = 82000 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (1000) * (1) * (82) + ((0) * (2) * (-215) + ((0) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_0_3 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 0 3 = -146000 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (1000) * (1) * (-146) + ((0) * (2) * (-9) + ((0) * (2) * (241) + ((0) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_0_4 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 0 4 = 11000 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (1000) * (1) * (11) + ((0) * (2) * (33) + ((0) * (2) * (-202) + ((0) * (2) * (-44) + ((0) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_0_5 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 0 5 = -5000 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (1000) * (1) * (-5) + ((0) * (2) * (-67) + ((0) * (2) * (-138) + ((0) * (2) * (124) + ((0) * (2) * (322) + ((0) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_0_6 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 0 6 = 19000 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (1000) * (1) * (19) + ((0) * (2) * (-123) + ((0) * (2) * (88) + ((0) * (2) * (-89) + ((0) * (2) * (24) + ((0) * (2) * (339) + ((0) * (2) * (1000) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_0_7 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 0 7 = -74000 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (1000) * (1) * (-74) + ((0) * (2) * (68) + ((0) * (2) * (5) + ((0) * (2) * (-5) + ((0) * (2) * (1) + ((0) * (2) * (20) + ((0) * (2) * (259) + ((0) * (2) * (1000) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_1_0 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 1 0 = -250000 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-250) * (1) * (1000) + ((1000) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_1_1 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 1 1 = 2062500 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-250) * (1) * (-250) + ((1000) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_1_2 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 1 2 = -450500 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-250) * (1) * (82) + ((1000) * (2) * (-215) + ((0) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_1_3 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 1 3 = 18500 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-250) * (1) * (-146) + ((1000) * (2) * (-9) + ((0) * (2) * (241) + ((0) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_1_4 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 1 4 = 63250 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-250) * (1) * (11) + ((1000) * (2) * (33) + ((0) * (2) * (-202) + ((0) * (2) * (-44) + ((0) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_1_5 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 1 5 = -132750 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-250) * (1) * (-5) + ((1000) * (2) * (-67) + ((0) * (2) * (-138) + ((0) * (2) * (124) + ((0) * (2) * (322) + ((0) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_1_6 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 1 6 = -250750 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-250) * (1) * (19) + ((1000) * (2) * (-123) + ((0) * (2) * (88) + ((0) * (2) * (-89) + ((0) * (2) * (24) + ((0) * (2) * (339) + ((0) * (2) * (1000) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_1_7 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 1 7 = 154500 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-250) * (1) * (-74) + ((1000) * (2) * (68) + ((0) * (2) * (5) + ((0) * (2) * (-5) + ((0) * (2) * (1) + ((0) * (2) * (20) + ((0) * (2) * (259) + ((0) * (2) * (1000) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_2_0 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 2 0 = 82000 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (82) * (1) * (1000) + ((-215) * (2) * (0) + ((1000) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_2_1 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 2 1 = -450500 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (82) * (1) * (-250) + ((-215) * (2) * (1000) + ((1000) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_2_2 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 2 2 = 2099174 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (82) * (1) * (82) + ((-215) * (2) * (-215) + ((1000) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_2_3 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 2 3 = 473898 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (82) * (1) * (-146) + ((-215) * (2) * (-9) + ((1000) * (2) * (241) + ((0) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_2_4 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 2 4 = -417288 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (82) * (1) * (11) + ((-215) * (2) * (33) + ((1000) * (2) * (-202) + ((0) * (2) * (-44) + ((0) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_2_5 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 2 5 = -247600 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (82) * (1) * (-5) + ((-215) * (2) * (-67) + ((1000) * (2) * (-138) + ((0) * (2) * (124) + ((0) * (2) * (322) + ((0) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_2_6 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 2 6 = 230448 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (82) * (1) * (19) + ((-215) * (2) * (-123) + ((1000) * (2) * (88) + ((0) * (2) * (-89) + ((0) * (2) * (24) + ((0) * (2) * (339) + ((0) * (2) * (1000) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_2_7 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 2 7 = -25308 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (82) * (1) * (-74) + ((-215) * (2) * (68) + ((1000) * (2) * (5) + ((0) * (2) * (-5) + ((0) * (2) * (1) + ((0) * (2) * (20) + ((0) * (2) * (259) + ((0) * (2) * (1000) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_3_0 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 3 0 = -146000 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-146) * (1) * (1000) + ((-9) * (2) * (0) + ((241) * (2) * (0) + ((1000) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_3_1 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 3 1 = 18500 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-146) * (1) * (-250) + ((-9) * (2) * (1000) + ((241) * (2) * (0) + ((1000) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_3_2 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 3 2 = 473898 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-146) * (1) * (82) + ((-9) * (2) * (-215) + ((241) * (2) * (1000) + ((1000) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_3_3 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 3 3 = 2137640 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-146) * (1) * (-146) + ((-9) * (2) * (-9) + ((241) * (2) * (241) + ((1000) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_3_4 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 3 4 = -187564 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-146) * (1) * (11) + ((-9) * (2) * (33) + ((241) * (2) * (-202) + ((1000) * (2) * (-44) + ((0) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_3_5 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 3 5 = 183420 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-146) * (1) * (-5) + ((-9) * (2) * (-67) + ((241) * (2) * (-138) + ((1000) * (2) * (124) + ((0) * (2) * (322) + ((0) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_3_6 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 3 6 = -136144 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-146) * (1) * (19) + ((-9) * (2) * (-123) + ((241) * (2) * (88) + ((1000) * (2) * (-89) + ((0) * (2) * (24) + ((0) * (2) * (339) + ((0) * (2) * (1000) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_3_7 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 3 7 = 1990 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-146) * (1) * (-74) + ((-9) * (2) * (68) + ((241) * (2) * (5) + ((1000) * (2) * (-5) + ((0) * (2) * (1) + ((0) * (2) * (20) + ((0) * (2) * (259) + ((0) * (2) * (1000) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_4_0 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 4 0 = 11000 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (11) * (1) * (1000) + ((33) * (2) * (0) + ((-202) * (2) * (0) + ((-44) * (2) * (0) + ((1000) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_4_1 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 4 1 = 63250 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (11) * (1) * (-250) + ((33) * (2) * (1000) + ((-202) * (2) * (0) + ((-44) * (2) * (0) + ((1000) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_4_2 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 4 2 = -417288 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (11) * (1) * (82) + ((33) * (2) * (-215) + ((-202) * (2) * (1000) + ((-44) * (2) * (0) + ((1000) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_4_3 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 4 3 = -187564 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (11) * (1) * (-146) + ((33) * (2) * (-9) + ((-202) * (2) * (241) + ((-44) * (2) * (1000) + ((1000) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_4_4 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 4 4 = 2087779 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (11) * (1) * (11) + ((33) * (2) * (33) + ((-202) * (2) * (-202) + ((-44) * (2) * (-44) + ((1000) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_4_5 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 4 5 = 684363 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (11) * (1) * (-5) + ((33) * (2) * (-67) + ((-202) * (2) * (-138) + ((-44) * (2) * (124) + ((1000) * (2) * (322) + ((0) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_4_6 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 4 6 = 12371 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (11) * (1) * (19) + ((33) * (2) * (-123) + ((-202) * (2) * (88) + ((-44) * (2) * (-89) + ((1000) * (2) * (24) + ((0) * (2) * (339) + ((0) * (2) * (1000) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_4_7 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 4 7 = 4094 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (11) * (1) * (-74) + ((33) * (2) * (68) + ((-202) * (2) * (5) + ((-44) * (2) * (-5) + ((1000) * (2) * (1) + ((0) * (2) * (20) + ((0) * (2) * (259) + ((0) * (2) * (1000) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_5_0 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 5 0 = -5000 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-5) * (1) * (1000) + ((-67) * (2) * (0) + ((-138) * (2) * (0) + ((124) * (2) * (0) + ((322) * (2) * (0) + ((1000) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_5_1 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 5 1 = -132750 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-5) * (1) * (-250) + ((-67) * (2) * (1000) + ((-138) * (2) * (0) + ((124) * (2) * (0) + ((322) * (2) * (0) + ((1000) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_5_2 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 5 2 = -247600 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-5) * (1) * (82) + ((-67) * (2) * (-215) + ((-138) * (2) * (1000) + ((124) * (2) * (0) + ((322) * (2) * (0) + ((1000) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_5_3 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 5 3 = 183420 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-5) * (1) * (-146) + ((-67) * (2) * (-9) + ((-138) * (2) * (241) + ((124) * (2) * (1000) + ((322) * (2) * (0) + ((1000) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_5_4 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 5 4 = 684363 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-5) * (1) * (11) + ((-67) * (2) * (33) + ((-138) * (2) * (-202) + ((124) * (2) * (-44) + ((322) * (2) * (1000) + ((1000) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_5_5 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 5 5 = 2285211 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-5) * (1) * (-5) + ((-67) * (2) * (-67) + ((-138) * (2) * (-138) + ((124) * (2) * (124) + ((322) * (2) * (322) + ((1000) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_5_6 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 5 6 = 663483 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-5) * (1) * (19) + ((-67) * (2) * (-123) + ((-138) * (2) * (88) + ((124) * (2) * (-89) + ((322) * (2) * (24) + ((1000) * (2) * (339) + ((0) * (2) * (1000) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_5_7 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 5 7 = 29282 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-5) * (1) * (-74) + ((-67) * (2) * (68) + ((-138) * (2) * (5) + ((124) * (2) * (-5) + ((322) * (2) * (1) + ((1000) * (2) * (20) + ((0) * (2) * (259) + ((0) * (2) * (1000) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_6_0 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 6 0 = 19000 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (19) * (1) * (1000) + ((-123) * (2) * (0) + ((88) * (2) * (0) + ((-89) * (2) * (0) + ((24) * (2) * (0) + ((339) * (2) * (0) + ((1000) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_6_1 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 6 1 = -250750 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (19) * (1) * (-250) + ((-123) * (2) * (1000) + ((88) * (2) * (0) + ((-89) * (2) * (0) + ((24) * (2) * (0) + ((339) * (2) * (0) + ((1000) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_6_2 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 6 2 = 230448 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (19) * (1) * (82) + ((-123) * (2) * (-215) + ((88) * (2) * (1000) + ((-89) * (2) * (0) + ((24) * (2) * (0) + ((339) * (2) * (0) + ((1000) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_6_3 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 6 3 = -136144 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (19) * (1) * (-146) + ((-123) * (2) * (-9) + ((88) * (2) * (241) + ((-89) * (2) * (1000) + ((24) * (2) * (0) + ((339) * (2) * (0) + ((1000) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_6_4 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 6 4 = 12371 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (19) * (1) * (11) + ((-123) * (2) * (33) + ((88) * (2) * (-202) + ((-89) * (2) * (-44) + ((24) * (2) * (1000) + ((339) * (2) * (0) + ((1000) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_6_5 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 6 5 = 663483 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (19) * (1) * (-5) + ((-123) * (2) * (-67) + ((88) * (2) * (-138) + ((-89) * (2) * (124) + ((24) * (2) * (322) + ((339) * (2) * (1000) + ((1000) * (2) * (0) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_6_6 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 6 6 = 2292943 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (19) * (1) * (19) + ((-123) * (2) * (-123) + ((88) * (2) * (88) + ((-89) * (2) * (-89) + ((24) * (2) * (24) + ((339) * (2) * (339) + ((1000) * (2) * (1000) + ((0) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_6_7 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 6 7 = 515244 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (19) * (1) * (-74) + ((-123) * (2) * (68) + ((88) * (2) * (5) + ((-89) * (2) * (-5) + ((24) * (2) * (1) + ((339) * (2) * (20) + ((1000) * (2) * (259) + ((0) * (2) * (1000) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_7_0 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 7 0 = -74000 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-74) * (1) * (1000) + ((68) * (2) * (0) + ((5) * (2) * (0) + ((-5) * (2) * (0) + ((1) * (2) * (0) + ((20) * (2) * (0) + ((259) * (2) * (0) + ((1000) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_7_1 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 7 1 = 154500 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-74) * (1) * (-250) + ((68) * (2) * (1000) + ((5) * (2) * (0) + ((-5) * (2) * (0) + ((1) * (2) * (0) + ((20) * (2) * (0) + ((259) * (2) * (0) + ((1000) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_7_2 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 7 2 = -25308 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-74) * (1) * (82) + ((68) * (2) * (-215) + ((5) * (2) * (1000) + ((-5) * (2) * (0) + ((1) * (2) * (0) + ((20) * (2) * (0) + ((259) * (2) * (0) + ((1000) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_7_3 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 7 3 = 1990 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-74) * (1) * (-146) + ((68) * (2) * (-9) + ((5) * (2) * (241) + ((-5) * (2) * (1000) + ((1) * (2) * (0) + ((20) * (2) * (0) + ((259) * (2) * (0) + ((1000) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_7_4 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 7 4 = 4094 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-74) * (1) * (11) + ((68) * (2) * (33) + ((5) * (2) * (-202) + ((-5) * (2) * (-44) + ((1) * (2) * (1000) + ((20) * (2) * (0) + ((259) * (2) * (0) + ((1000) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_7_5 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 7 5 = 29282 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-74) * (1) * (-5) + ((68) * (2) * (-67) + ((5) * (2) * (-138) + ((-5) * (2) * (124) + ((1) * (2) * (322) + ((20) * (2) * (1000) + ((259) * (2) * (0) + ((1000) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_7_6 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 7 6 = 515244 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-74) * (1) * (19) + ((68) * (2) * (-123) + ((5) * (2) * (88) + ((-5) * (2) * (-89) + ((1) * (2) * (24) + ((20) * (2) * (339) + ((259) * (2) * (1000) + ((1000) * (2) * (0) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGramEntry_7_7 :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 7 7 = 2149788 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-74) * (1) * (-74) + ((68) * (2) * (68) + ((5) * (2) * (5) + ((-5) * (2) * (-5) + ((1) * (2) * (1) + ((20) * (2) * (20) + ((259) * (2) * (259) + ((1000) * (2) * (1000) + (0)))))))) = _
  norm_num

theorem fourthLevelOddGram_row0 (j : Fin 8) :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 0 j = fourthLevelOddGramNumerator 0 j := by
  fin_cases j
  · exact fourthLevelOddGramEntry_0_0
  · exact fourthLevelOddGramEntry_0_1
  · exact fourthLevelOddGramEntry_0_2
  · exact fourthLevelOddGramEntry_0_3
  · exact fourthLevelOddGramEntry_0_4
  · exact fourthLevelOddGramEntry_0_5
  · exact fourthLevelOddGramEntry_0_6
  · exact fourthLevelOddGramEntry_0_7

theorem fourthLevelOddGram_row1 (j : Fin 8) :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 1 j = fourthLevelOddGramNumerator 1 j := by
  fin_cases j
  · exact fourthLevelOddGramEntry_1_0
  · exact fourthLevelOddGramEntry_1_1
  · exact fourthLevelOddGramEntry_1_2
  · exact fourthLevelOddGramEntry_1_3
  · exact fourthLevelOddGramEntry_1_4
  · exact fourthLevelOddGramEntry_1_5
  · exact fourthLevelOddGramEntry_1_6
  · exact fourthLevelOddGramEntry_1_7

theorem fourthLevelOddGram_row2 (j : Fin 8) :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 2 j = fourthLevelOddGramNumerator 2 j := by
  fin_cases j
  · exact fourthLevelOddGramEntry_2_0
  · exact fourthLevelOddGramEntry_2_1
  · exact fourthLevelOddGramEntry_2_2
  · exact fourthLevelOddGramEntry_2_3
  · exact fourthLevelOddGramEntry_2_4
  · exact fourthLevelOddGramEntry_2_5
  · exact fourthLevelOddGramEntry_2_6
  · exact fourthLevelOddGramEntry_2_7

theorem fourthLevelOddGram_row3 (j : Fin 8) :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 3 j = fourthLevelOddGramNumerator 3 j := by
  fin_cases j
  · exact fourthLevelOddGramEntry_3_0
  · exact fourthLevelOddGramEntry_3_1
  · exact fourthLevelOddGramEntry_3_2
  · exact fourthLevelOddGramEntry_3_3
  · exact fourthLevelOddGramEntry_3_4
  · exact fourthLevelOddGramEntry_3_5
  · exact fourthLevelOddGramEntry_3_6
  · exact fourthLevelOddGramEntry_3_7

theorem fourthLevelOddGram_row4 (j : Fin 8) :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 4 j = fourthLevelOddGramNumerator 4 j := by
  fin_cases j
  · exact fourthLevelOddGramEntry_4_0
  · exact fourthLevelOddGramEntry_4_1
  · exact fourthLevelOddGramEntry_4_2
  · exact fourthLevelOddGramEntry_4_3
  · exact fourthLevelOddGramEntry_4_4
  · exact fourthLevelOddGramEntry_4_5
  · exact fourthLevelOddGramEntry_4_6
  · exact fourthLevelOddGramEntry_4_7

theorem fourthLevelOddGram_row5 (j : Fin 8) :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 5 j = fourthLevelOddGramNumerator 5 j := by
  fin_cases j
  · exact fourthLevelOddGramEntry_5_0
  · exact fourthLevelOddGramEntry_5_1
  · exact fourthLevelOddGramEntry_5_2
  · exact fourthLevelOddGramEntry_5_3
  · exact fourthLevelOddGramEntry_5_4
  · exact fourthLevelOddGramEntry_5_5
  · exact fourthLevelOddGramEntry_5_6
  · exact fourthLevelOddGramEntry_5_7

theorem fourthLevelOddGram_row6 (j : Fin 8) :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 6 j = fourthLevelOddGramNumerator 6 j := by
  fin_cases j
  · exact fourthLevelOddGramEntry_6_0
  · exact fourthLevelOddGramEntry_6_1
  · exact fourthLevelOddGramEntry_6_2
  · exact fourthLevelOddGramEntry_6_3
  · exact fourthLevelOddGramEntry_6_4
  · exact fourthLevelOddGramEntry_6_5
  · exact fourthLevelOddGramEntry_6_6
  · exact fourthLevelOddGramEntry_6_7

theorem fourthLevelOddGram_row7 (j : Fin 8) :
    (fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator) 7 j = fourthLevelOddGramNumerator 7 j := by
  fin_cases j
  · exact fourthLevelOddGramEntry_7_0
  · exact fourthLevelOddGramEntry_7_1
  · exact fourthLevelOddGramEntry_7_2
  · exact fourthLevelOddGramEntry_7_3
  · exact fourthLevelOddGramEntry_7_4
  · exact fourthLevelOddGramEntry_7_5
  · exact fourthLevelOddGramEntry_7_6
  · exact fourthLevelOddGramEntry_7_7

theorem fourthLevelOddGram_eq :
    fourthLevelOddShearNumerator.transpose * Matrix.diagonal fourthLevelOddGramWeight *
      fourthLevelOddShearNumerator = fourthLevelOddGramNumerator := by
  ext i j
  fin_cases i
  · exact fourthLevelOddGram_row0 j
  · exact fourthLevelOddGram_row1 j
  · exact fourthLevelOddGram_row2 j
  · exact fourthLevelOddGram_row3 j
  · exact fourthLevelOddGram_row4 j
  · exact fourthLevelOddGram_row5 j
  · exact fourthLevelOddGram_row6 j
  · exact fourthLevelOddGram_row7 j

def fourthLevelOddShear : Matrix (Fin 8) (Fin 8) ℝ :=
  (1/1000 : ℝ) • fourthLevelOddShearNumerator

def fourthLevelOddSheared (p : Fin 17 → ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  fourthLevelOddShear.transpose *
    (fourthLevelOddPolynomial p -
      (1/1000000000 : ℝ) • Matrix.diagonal fourthLevelOddGramWeight) *
    fourthLevelOddShear

theorem fourthLevelOddSheared_eq (p : Fin 17 → ℝ) :
    fourthLevelOddSheared p =
      (1/1000000 : ℝ) • fourthLevelOddCongruencePolynomial p -
        (1/1000000000000000 : ℝ) • fourthLevelOddGramNumerator := by
  rw [fourthLevelOddSheared, fourthLevelOddShear,
    realMatrix_scaled_shift_congruence, fourthLevelOddCongruence_eq, fourthLevelOddGram_eq]

theorem fourthLevelOddSheared_apply (p : Fin 17 → ℝ) (i j : Fin 8) :
    fourthLevelOddSheared p i j =
      fourthLevelOddCongruencePolynomial p i j / 1000000 -
        fourthLevelOddGramNumerator i j / 1000000000000000 := by
  rw [fourthLevelOddSheared_eq]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem fourthLevelOddPolynomial_isHermitian (p : Fin 17 → ℝ) :
    (fourthLevelOddPolynomial p).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem fourthLevelOddSheared_isHermitian (p : Fin 17 → ℝ) :
    (fourthLevelOddSheared p).IsHermitian := by
  apply realMatrix_congruence_isHermitian
  exact (fourthLevelOddPolynomial_isHermitian p).sub
    ((Matrix.isHermitian_diagonal fourthLevelOddGramWeight).smul (by simp [IsSelfAdjoint]))

def fourthLevelEvenGramWeight (i : Fin 7) : ℝ := 2

def fourthLevelEvenGramNumerator : Matrix (Fin 7) (Fin 7) ℝ :=
  ![![2000000,-350000,-518000,56000,-144000,-216000,-20000],
  ![-350000,2061250,872650,-453800,-254800,219800,21500],
  ![-518000,872650,2439924,-268108,143816,75106,-493782],
  ![56000,-453800,-268108,2103336,689488,5628,19684],
  ![-144000,-254800,143816,689488,2277696,702456,11552],
  ![-216000,219800,75106,5628,702456,2288894,894220],
  ![-20000,21500,-493782,19684,11552,894220,2495224]]

theorem fourthLevelEvenGramEntry_0_0 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 0 0 = 2000000 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (1000) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_0_1 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 0 1 = -350000 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (1000) * (2) * (-175) + ((0) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_0_2 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 0 2 = -518000 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (1000) * (2) * (-259) + ((0) * (2) * (391) + ((0) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_0_3 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 0 3 = 56000 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (1000) * (2) * (28) + ((0) * (2) * (-222) + ((0) * (2) * (-40) + ((0) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_0_4 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 0 4 = -144000 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (1000) * (2) * (-72) + ((0) * (2) * (-140) + ((0) * (2) * (108) + ((0) * (2) * (320) + ((0) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_0_5 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 0 5 = -216000 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (1000) * (2) * (-108) + ((0) * (2) * (91) + ((0) * (2) * (-26) + ((0) * (2) * (25) + ((0) * (2) * (351) + ((0) * (2) * (1000) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_0_6 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 0 6 = -20000 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (1000) * (2) * (-10) + ((0) * (2) * (9) + ((0) * (2) * (-253) + ((0) * (2) * (2) + ((0) * (2) * (33) + ((0) * (2) * (427) + ((0) * (2) * (1000) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_1_0 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 1 0 = -350000 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-175) * (2) * (1000) + ((1000) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_1_1 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 1 1 = 2061250 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-175) * (2) * (-175) + ((1000) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_1_2 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 1 2 = 872650 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-175) * (2) * (-259) + ((1000) * (2) * (391) + ((0) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_1_3 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 1 3 = -453800 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-175) * (2) * (28) + ((1000) * (2) * (-222) + ((0) * (2) * (-40) + ((0) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_1_4 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 1 4 = -254800 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-175) * (2) * (-72) + ((1000) * (2) * (-140) + ((0) * (2) * (108) + ((0) * (2) * (320) + ((0) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_1_5 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 1 5 = 219800 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-175) * (2) * (-108) + ((1000) * (2) * (91) + ((0) * (2) * (-26) + ((0) * (2) * (25) + ((0) * (2) * (351) + ((0) * (2) * (1000) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_1_6 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 1 6 = 21500 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-175) * (2) * (-10) + ((1000) * (2) * (9) + ((0) * (2) * (-253) + ((0) * (2) * (2) + ((0) * (2) * (33) + ((0) * (2) * (427) + ((0) * (2) * (1000) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_2_0 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 2 0 = -518000 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-259) * (2) * (1000) + ((391) * (2) * (0) + ((1000) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_2_1 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 2 1 = 872650 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-259) * (2) * (-175) + ((391) * (2) * (1000) + ((1000) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_2_2 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 2 2 = 2439924 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-259) * (2) * (-259) + ((391) * (2) * (391) + ((1000) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_2_3 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 2 3 = -268108 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-259) * (2) * (28) + ((391) * (2) * (-222) + ((1000) * (2) * (-40) + ((0) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_2_4 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 2 4 = 143816 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-259) * (2) * (-72) + ((391) * (2) * (-140) + ((1000) * (2) * (108) + ((0) * (2) * (320) + ((0) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_2_5 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 2 5 = 75106 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-259) * (2) * (-108) + ((391) * (2) * (91) + ((1000) * (2) * (-26) + ((0) * (2) * (25) + ((0) * (2) * (351) + ((0) * (2) * (1000) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_2_6 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 2 6 = -493782 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-259) * (2) * (-10) + ((391) * (2) * (9) + ((1000) * (2) * (-253) + ((0) * (2) * (2) + ((0) * (2) * (33) + ((0) * (2) * (427) + ((0) * (2) * (1000) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_3_0 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 3 0 = 56000 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (28) * (2) * (1000) + ((-222) * (2) * (0) + ((-40) * (2) * (0) + ((1000) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_3_1 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 3 1 = -453800 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (28) * (2) * (-175) + ((-222) * (2) * (1000) + ((-40) * (2) * (0) + ((1000) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_3_2 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 3 2 = -268108 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (28) * (2) * (-259) + ((-222) * (2) * (391) + ((-40) * (2) * (1000) + ((1000) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_3_3 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 3 3 = 2103336 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (28) * (2) * (28) + ((-222) * (2) * (-222) + ((-40) * (2) * (-40) + ((1000) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_3_4 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 3 4 = 689488 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (28) * (2) * (-72) + ((-222) * (2) * (-140) + ((-40) * (2) * (108) + ((1000) * (2) * (320) + ((0) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_3_5 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 3 5 = 5628 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (28) * (2) * (-108) + ((-222) * (2) * (91) + ((-40) * (2) * (-26) + ((1000) * (2) * (25) + ((0) * (2) * (351) + ((0) * (2) * (1000) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_3_6 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 3 6 = 19684 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (28) * (2) * (-10) + ((-222) * (2) * (9) + ((-40) * (2) * (-253) + ((1000) * (2) * (2) + ((0) * (2) * (33) + ((0) * (2) * (427) + ((0) * (2) * (1000) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_4_0 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 4 0 = -144000 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-72) * (2) * (1000) + ((-140) * (2) * (0) + ((108) * (2) * (0) + ((320) * (2) * (0) + ((1000) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_4_1 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 4 1 = -254800 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-72) * (2) * (-175) + ((-140) * (2) * (1000) + ((108) * (2) * (0) + ((320) * (2) * (0) + ((1000) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_4_2 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 4 2 = 143816 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-72) * (2) * (-259) + ((-140) * (2) * (391) + ((108) * (2) * (1000) + ((320) * (2) * (0) + ((1000) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_4_3 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 4 3 = 689488 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-72) * (2) * (28) + ((-140) * (2) * (-222) + ((108) * (2) * (-40) + ((320) * (2) * (1000) + ((1000) * (2) * (0) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_4_4 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 4 4 = 2277696 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-72) * (2) * (-72) + ((-140) * (2) * (-140) + ((108) * (2) * (108) + ((320) * (2) * (320) + ((1000) * (2) * (1000) + ((0) * (2) * (0) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_4_5 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 4 5 = 702456 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-72) * (2) * (-108) + ((-140) * (2) * (91) + ((108) * (2) * (-26) + ((320) * (2) * (25) + ((1000) * (2) * (351) + ((0) * (2) * (1000) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_4_6 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 4 6 = 11552 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-72) * (2) * (-10) + ((-140) * (2) * (9) + ((108) * (2) * (-253) + ((320) * (2) * (2) + ((1000) * (2) * (33) + ((0) * (2) * (427) + ((0) * (2) * (1000) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_5_0 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 5 0 = -216000 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-108) * (2) * (1000) + ((91) * (2) * (0) + ((-26) * (2) * (0) + ((25) * (2) * (0) + ((351) * (2) * (0) + ((1000) * (2) * (0) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_5_1 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 5 1 = 219800 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-108) * (2) * (-175) + ((91) * (2) * (1000) + ((-26) * (2) * (0) + ((25) * (2) * (0) + ((351) * (2) * (0) + ((1000) * (2) * (0) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_5_2 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 5 2 = 75106 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-108) * (2) * (-259) + ((91) * (2) * (391) + ((-26) * (2) * (1000) + ((25) * (2) * (0) + ((351) * (2) * (0) + ((1000) * (2) * (0) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_5_3 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 5 3 = 5628 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-108) * (2) * (28) + ((91) * (2) * (-222) + ((-26) * (2) * (-40) + ((25) * (2) * (1000) + ((351) * (2) * (0) + ((1000) * (2) * (0) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_5_4 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 5 4 = 702456 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-108) * (2) * (-72) + ((91) * (2) * (-140) + ((-26) * (2) * (108) + ((25) * (2) * (320) + ((351) * (2) * (1000) + ((1000) * (2) * (0) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_5_5 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 5 5 = 2288894 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-108) * (2) * (-108) + ((91) * (2) * (91) + ((-26) * (2) * (-26) + ((25) * (2) * (25) + ((351) * (2) * (351) + ((1000) * (2) * (1000) + ((0) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_5_6 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 5 6 = 894220 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-108) * (2) * (-10) + ((91) * (2) * (9) + ((-26) * (2) * (-253) + ((25) * (2) * (2) + ((351) * (2) * (33) + ((1000) * (2) * (427) + ((0) * (2) * (1000) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_6_0 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 6 0 = -20000 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-10) * (2) * (1000) + ((9) * (2) * (0) + ((-253) * (2) * (0) + ((2) * (2) * (0) + ((33) * (2) * (0) + ((427) * (2) * (0) + ((1000) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_6_1 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 6 1 = 21500 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-10) * (2) * (-175) + ((9) * (2) * (1000) + ((-253) * (2) * (0) + ((2) * (2) * (0) + ((33) * (2) * (0) + ((427) * (2) * (0) + ((1000) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_6_2 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 6 2 = -493782 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-10) * (2) * (-259) + ((9) * (2) * (391) + ((-253) * (2) * (1000) + ((2) * (2) * (0) + ((33) * (2) * (0) + ((427) * (2) * (0) + ((1000) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_6_3 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 6 3 = 19684 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-10) * (2) * (28) + ((9) * (2) * (-222) + ((-253) * (2) * (-40) + ((2) * (2) * (1000) + ((33) * (2) * (0) + ((427) * (2) * (0) + ((1000) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_6_4 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 6 4 = 11552 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-10) * (2) * (-72) + ((9) * (2) * (-140) + ((-253) * (2) * (108) + ((2) * (2) * (320) + ((33) * (2) * (1000) + ((427) * (2) * (0) + ((1000) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_6_5 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 6 5 = 894220 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-10) * (2) * (-108) + ((9) * (2) * (91) + ((-253) * (2) * (-26) + ((2) * (2) * (25) + ((33) * (2) * (351) + ((427) * (2) * (1000) + ((1000) * (2) * (0) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGramEntry_6_6 :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 6 6 = 2495224 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-10) * (2) * (-10) + ((9) * (2) * (9) + ((-253) * (2) * (-253) + ((2) * (2) * (2) + ((33) * (2) * (33) + ((427) * (2) * (427) + ((1000) * (2) * (1000) + (0))))))) = _
  norm_num

theorem fourthLevelEvenGram_row0 (j : Fin 7) :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 0 j = fourthLevelEvenGramNumerator 0 j := by
  fin_cases j
  · exact fourthLevelEvenGramEntry_0_0
  · exact fourthLevelEvenGramEntry_0_1
  · exact fourthLevelEvenGramEntry_0_2
  · exact fourthLevelEvenGramEntry_0_3
  · exact fourthLevelEvenGramEntry_0_4
  · exact fourthLevelEvenGramEntry_0_5
  · exact fourthLevelEvenGramEntry_0_6

theorem fourthLevelEvenGram_row1 (j : Fin 7) :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 1 j = fourthLevelEvenGramNumerator 1 j := by
  fin_cases j
  · exact fourthLevelEvenGramEntry_1_0
  · exact fourthLevelEvenGramEntry_1_1
  · exact fourthLevelEvenGramEntry_1_2
  · exact fourthLevelEvenGramEntry_1_3
  · exact fourthLevelEvenGramEntry_1_4
  · exact fourthLevelEvenGramEntry_1_5
  · exact fourthLevelEvenGramEntry_1_6

theorem fourthLevelEvenGram_row2 (j : Fin 7) :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 2 j = fourthLevelEvenGramNumerator 2 j := by
  fin_cases j
  · exact fourthLevelEvenGramEntry_2_0
  · exact fourthLevelEvenGramEntry_2_1
  · exact fourthLevelEvenGramEntry_2_2
  · exact fourthLevelEvenGramEntry_2_3
  · exact fourthLevelEvenGramEntry_2_4
  · exact fourthLevelEvenGramEntry_2_5
  · exact fourthLevelEvenGramEntry_2_6

theorem fourthLevelEvenGram_row3 (j : Fin 7) :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 3 j = fourthLevelEvenGramNumerator 3 j := by
  fin_cases j
  · exact fourthLevelEvenGramEntry_3_0
  · exact fourthLevelEvenGramEntry_3_1
  · exact fourthLevelEvenGramEntry_3_2
  · exact fourthLevelEvenGramEntry_3_3
  · exact fourthLevelEvenGramEntry_3_4
  · exact fourthLevelEvenGramEntry_3_5
  · exact fourthLevelEvenGramEntry_3_6

theorem fourthLevelEvenGram_row4 (j : Fin 7) :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 4 j = fourthLevelEvenGramNumerator 4 j := by
  fin_cases j
  · exact fourthLevelEvenGramEntry_4_0
  · exact fourthLevelEvenGramEntry_4_1
  · exact fourthLevelEvenGramEntry_4_2
  · exact fourthLevelEvenGramEntry_4_3
  · exact fourthLevelEvenGramEntry_4_4
  · exact fourthLevelEvenGramEntry_4_5
  · exact fourthLevelEvenGramEntry_4_6

theorem fourthLevelEvenGram_row5 (j : Fin 7) :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 5 j = fourthLevelEvenGramNumerator 5 j := by
  fin_cases j
  · exact fourthLevelEvenGramEntry_5_0
  · exact fourthLevelEvenGramEntry_5_1
  · exact fourthLevelEvenGramEntry_5_2
  · exact fourthLevelEvenGramEntry_5_3
  · exact fourthLevelEvenGramEntry_5_4
  · exact fourthLevelEvenGramEntry_5_5
  · exact fourthLevelEvenGramEntry_5_6

theorem fourthLevelEvenGram_row6 (j : Fin 7) :
    (fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator) 6 j = fourthLevelEvenGramNumerator 6 j := by
  fin_cases j
  · exact fourthLevelEvenGramEntry_6_0
  · exact fourthLevelEvenGramEntry_6_1
  · exact fourthLevelEvenGramEntry_6_2
  · exact fourthLevelEvenGramEntry_6_3
  · exact fourthLevelEvenGramEntry_6_4
  · exact fourthLevelEvenGramEntry_6_5
  · exact fourthLevelEvenGramEntry_6_6

theorem fourthLevelEvenGram_eq :
    fourthLevelEvenShearNumerator.transpose * Matrix.diagonal fourthLevelEvenGramWeight *
      fourthLevelEvenShearNumerator = fourthLevelEvenGramNumerator := by
  ext i j
  fin_cases i
  · exact fourthLevelEvenGram_row0 j
  · exact fourthLevelEvenGram_row1 j
  · exact fourthLevelEvenGram_row2 j
  · exact fourthLevelEvenGram_row3 j
  · exact fourthLevelEvenGram_row4 j
  · exact fourthLevelEvenGram_row5 j
  · exact fourthLevelEvenGram_row6 j

def fourthLevelEvenShear : Matrix (Fin 7) (Fin 7) ℝ :=
  (1/1000 : ℝ) • fourthLevelEvenShearNumerator

def fourthLevelEvenSheared (p : Fin 17 → ℝ) : Matrix (Fin 7) (Fin 7) ℝ :=
  fourthLevelEvenShear.transpose *
    (fourthLevelEvenPolynomial p -
      (1/1000000000 : ℝ) • Matrix.diagonal fourthLevelEvenGramWeight) *
    fourthLevelEvenShear

theorem fourthLevelEvenSheared_eq (p : Fin 17 → ℝ) :
    fourthLevelEvenSheared p =
      (1/1000000 : ℝ) • fourthLevelEvenCongruencePolynomial p -
        (1/1000000000000000 : ℝ) • fourthLevelEvenGramNumerator := by
  rw [fourthLevelEvenSheared, fourthLevelEvenShear,
    realMatrix_scaled_shift_congruence, fourthLevelEvenCongruence_eq, fourthLevelEvenGram_eq]

theorem fourthLevelEvenSheared_apply (p : Fin 17 → ℝ) (i j : Fin 7) :
    fourthLevelEvenSheared p i j =
      fourthLevelEvenCongruencePolynomial p i j / 1000000 -
        fourthLevelEvenGramNumerator i j / 1000000000000000 := by
  rw [fourthLevelEvenSheared_eq]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem fourthLevelEvenPolynomial_isHermitian (p : Fin 17 → ℝ) :
    (fourthLevelEvenPolynomial p).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem fourthLevelEvenSheared_isHermitian (p : Fin 17 → ℝ) :
    (fourthLevelEvenSheared p).IsHermitian := by
  apply realMatrix_congruence_isHermitian
  exact (fourthLevelEvenPolynomial_isHermitian p).sub
    ((Matrix.isHermitian_diagonal fourthLevelEvenGramWeight).smul (by simp [IsSelfAdjoint]))

def fourthLevelSamples : Fin 17 → ℝ :=
  fun i => fourthLevelPrimitive (5373/2000) (i.val/128)

theorem fourthLevelSamples_zero : fourthLevelSamples 0 = 0 := by
  simpa [fourthLevelSamples] using fourthLevelPrimitive_zero (5373/2000)

theorem fourthLevelSamples_1_bounds :
    (-16007754766/1000000000000000000 : ℝ) ≤ fourthLevelSamples 1 ∧
      fourthLevelSamples 1 ≤ (-16007754765/1000000000000000000 : ℝ) := by
  simpa [fourthLevelSamples] using fourthLevelPrimitive_sixteenth_1_bounds

theorem fourthLevelSamples_2_bounds :
    (-124465267437/1000000000000000000 : ℝ) ≤ fourthLevelSamples 2 ∧
      fourthLevelSamples 2 ≤ (-124465267436/1000000000000000000 : ℝ) := by
  simpa [fourthLevelSamples] using fourthLevelPrimitive_sixteenth_2_bounds

theorem fourthLevelSamples_3_bounds :
    (-408211913058/1000000000000000000 : ℝ) ≤ fourthLevelSamples 3 ∧
      fourthLevelSamples 3 ≤ (-408211913057/1000000000000000000 : ℝ) := by
  simpa [fourthLevelSamples] using fourthLevelPrimitive_sixteenth_3_bounds

theorem fourthLevelSamples_4_bounds :
    (-940154374694/1000000000000000000 : ℝ) ≤ fourthLevelSamples 4 ∧
      fourthLevelSamples 4 ≤ (-940154374693/1000000000000000000 : ℝ) := by
  simpa [fourthLevelSamples] using fourthLevelPrimitive_sixteenth_4_bounds

theorem fourthLevelSamples_5_bounds :
    (-1783847058417/1000000000000000000 : ℝ) ≤ fourthLevelSamples 5 ∧
      fourthLevelSamples 5 ≤ (-1783847058416/1000000000000000000 : ℝ) := by
  simpa [fourthLevelSamples] using fourthLevelPrimitive_sixteenth_5_bounds

theorem fourthLevelSamples_6_bounds :
    (-2994045351101/1000000000000000000 : ℝ) ≤ fourthLevelSamples 6 ∧
      fourthLevelSamples 6 ≤ (-2994045351100/1000000000000000000 : ℝ) := by
  simpa [fourthLevelSamples] using fourthLevelPrimitive_sixteenth_6_bounds

theorem fourthLevelSamples_7_bounds :
    (-4617233164834/1000000000000000000 : ℝ) ≤ fourthLevelSamples 7 ∧
      fourthLevelSamples 7 ≤ (-4617233164833/1000000000000000000 : ℝ) := by
  simpa [fourthLevelSamples] using fourthLevelPrimitive_sixteenth_7_bounds

theorem fourthLevelSamples_8_bounds :
    (-6692126130458/1000000000000000000 : ℝ) ≤ fourthLevelSamples 8 ∧
      fourthLevelSamples 8 ≤ (-6692126130457/1000000000000000000 : ℝ) := by
  simpa [fourthLevelSamples] using fourthLevelPrimitive_sixteenth_8_bounds

theorem fourthLevelSamples_9_bounds :
    (-9250151726173/1000000000000000000 : ℝ) ≤ fourthLevelSamples 9 ∧
      fourthLevelSamples 9 ≤ (-9250151726172/1000000000000000000 : ℝ) := by
  simpa [fourthLevelSamples] using fourthLevelPrimitive_sixteenth_9_bounds

theorem fourthLevelSamples_10_bounds :
    (-12315907555091/1000000000000000000 : ℝ) ≤ fourthLevelSamples 10 ∧
      fourthLevelSamples 10 ≤ (-12315907555090/1000000000000000000 : ℝ) := by
  simpa [fourthLevelSamples] using fourthLevelPrimitive_sixteenth_10_bounds

theorem fourthLevelSamples_11_bounds :
    (-15907598917710/1000000000000000000 : ℝ) ≤ fourthLevelSamples 11 ∧
      fourthLevelSamples 11 ≤ (-15907598917709/1000000000000000000 : ℝ) := by
  simpa [fourthLevelSamples] using fourthLevelPrimitive_sixteenth_11_bounds

theorem fourthLevelSamples_12_bounds :
    (-20037456761388/1000000000000000000 : ℝ) ≤ fourthLevelSamples 12 ∧
      fourthLevelSamples 12 ≤ (-20037456761387/1000000000000000000 : ℝ) := by
  simpa [fourthLevelSamples] using fourthLevelPrimitive_sixteenth_12_bounds

theorem fourthLevelSamples_13_bounds :
    (-24712137028672/1000000000000000000 : ℝ) ≤ fourthLevelSamples 13 ∧
      fourthLevelSamples 13 ≤ (-24712137028671/1000000000000000000 : ℝ) := by
  simpa [fourthLevelSamples] using fourthLevelPrimitive_sixteenth_13_bounds

theorem fourthLevelSamples_14_bounds :
    (-29933102369600/1000000000000000000 : ℝ) ≤ fourthLevelSamples 14 ∧
      fourthLevelSamples 14 ≤ (-29933102369599/1000000000000000000 : ℝ) := by
  simpa [fourthLevelSamples] using fourthLevelPrimitive_sixteenth_14_bounds

theorem fourthLevelSamples_15_bounds :
    (-35696987129701/1000000000000000000 : ℝ) ≤ fourthLevelSamples 15 ∧
      fourthLevelSamples 15 ≤ (-35696987129700/1000000000000000000 : ℝ) := by
  simpa [fourthLevelSamples] using fourthLevelPrimitive_sixteenth_15_bounds

theorem fourthLevelSamples_16_bounds :
    (-41995946475046/1000000000000000000 : ℝ) ≤ fourthLevelSamples 16 ∧
      fourthLevelSamples 16 ≤ (-41995946475045/1000000000000000000 : ℝ) := by
  simpa [fourthLevelSamples] using fourthLevelPrimitive_sixteenth_16_bounds

theorem fourthLevelOddSheared_bounds_0_0 :
    (30453883906/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 0 0 ∧
      fourthLevelOddSheared fourthLevelSamples 0 0 ≤ (30453883907/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (8000000*fourthLevelSamples 8 - 2000000*fourthLevelSamples 16) / 1000000 - (1000000) / 1000000000000000 ∧ (8000000*fourthLevelSamples 8 - 2000000*fourthLevelSamples 16) / 1000000 - (1000000) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_8_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_8_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_0_1 :
    (-10787574/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 0 1 ∧
      fourthLevelOddSheared fourthLevelSamples 0 1 ≤ (-10787573/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (- 4000000*fourthLevelSamples 4 - 2000000*fourthLevelSamples 8 + 4000000*fourthLevelSamples 12 - 1500000*fourthLevelSamples 16) / 1000000 - (-250000) / 1000000000000000 ∧ (- 4000000*fourthLevelSamples 4 - 2000000*fourthLevelSamples 8 + 4000000*fourthLevelSamples 12 - 1500000*fourthLevelSamples 16) / 1000000 - (-250000) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_4_bounds).2, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_4_bounds).1, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_0_2 :
    (2727010/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 0 2 ∧
      fourthLevelOddSheared fourthLevelSamples 0 2 ≤ (2727011/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (4000000*fourthLevelSamples 2 + 2860000*fourthLevelSamples 4 - 8000000*fourthLevelSamples 6 + 4656000*fourthLevelSamples 8 - 2860000*fourthLevelSamples 12 + 4000000*fourthLevelSamples 14 - 1734000*fourthLevelSamples 16) / 1000000 - (82000) / 1000000000000000 ∧ (4000000*fourthLevelSamples 2 + 2860000*fourthLevelSamples 4 - 8000000*fourthLevelSamples 6 + 4656000*fourthLevelSamples 8 - 2860000*fourthLevelSamples 12 + 4000000*fourthLevelSamples 14 - 1734000*fourthLevelSamples 16) / 1000000 - (82000) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_2_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_2_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_0_3 :
    (-2910795/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 0 3 ∧
      fourthLevelOddSheared fourthLevelSamples 0 3 ≤ (-2910794/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (- 7036000*fourthLevelSamples 2 + 2518000*fourthLevelSamples 4 + 2072000*fourthLevelSamples 6 - 4204000*fourthLevelSamples 8 + 4000000*fourthLevelSamples 10 - 2518000*fourthLevelSamples 12 + 964000*fourthLevelSamples 14 - 172000*fourthLevelSamples 16) / 1000000 - (-146000) / 1000000000000000 ∧ (- 7036000*fourthLevelSamples 2 + 2518000*fourthLevelSamples 4 + 2072000*fourthLevelSamples 6 - 4204000*fourthLevelSamples 8 + 4000000*fourthLevelSamples 10 - 2518000*fourthLevelSamples 12 + 964000*fourthLevelSamples 14 - 172000*fourthLevelSamples 16) / 1000000 - (-146000) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_2_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_2_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_0_4 :
    (175218/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 0 4 ∧
      fourthLevelOddSheared fourthLevelSamples 0 4 ≤ (175220/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (4000000*fourthLevelSamples 1 - 2456000*fourthLevelSamples 2 - 624000*fourthLevelSamples 4 + 5440000*fourthLevelSamples 6 - 8000000*fourthLevelSamples 7 + 3456000*fourthLevelSamples 8 - 176000*fourthLevelSamples 10 + 624000*fourthLevelSamples 12 - 2808000*fourthLevelSamples 14 + 4000000*fourthLevelSamples 15 - 1684000*fourthLevelSamples 16) / 1000000 - (11000) / 1000000000000000 ∧ (4000000*fourthLevelSamples 1 - 2456000*fourthLevelSamples 2 - 624000*fourthLevelSamples 4 + 5440000*fourthLevelSamples 6 - 8000000*fourthLevelSamples 7 + 3456000*fourthLevelSamples 8 - 176000*fourthLevelSamples 10 + 624000*fourthLevelSamples 12 - 2808000*fourthLevelSamples 14 + 4000000*fourthLevelSamples 15 - 1684000*fourthLevelSamples 16) / 1000000 - (11000) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_0_5 :
    (-12553761/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 0 5 ∧
      fourthLevelOddSheared fourthLevelSamples 0 5 ≤ (-12553760/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (1288000*fourthLevelSamples 1 - 4188000*fourthLevelSamples 2 + 4000000*fourthLevelSamples 3 + 2240000*fourthLevelSamples 4 - 8000000*fourthLevelSamples 5 + 6888000*fourthLevelSamples 6 - 2576000*fourthLevelSamples 7 + 200000*fourthLevelSamples 8 + 496000*fourthLevelSamples 10 - 2240000*fourthLevelSamples 12 + 4000000*fourthLevelSamples 13 - 3196000*fourthLevelSamples 14 + 1288000*fourthLevelSamples 15 - 224000*fourthLevelSamples 16) / 1000000 - (-5000) / 1000000000000000 ∧ (1288000*fourthLevelSamples 1 - 4188000*fourthLevelSamples 2 + 4000000*fourthLevelSamples 3 + 2240000*fourthLevelSamples 4 - 8000000*fourthLevelSamples 5 + 6888000*fourthLevelSamples 6 - 2576000*fourthLevelSamples 7 + 200000*fourthLevelSamples 8 + 496000*fourthLevelSamples 10 - 2240000*fourthLevelSamples 12 + 4000000*fourthLevelSamples 13 - 3196000*fourthLevelSamples 14 + 1288000*fourthLevelSamples 15 - 224000*fourthLevelSamples 16) / 1000000 - (-5000) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_0_6 :
    (-7176680/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 0 6 ∧
      fourthLevelOddSheared fourthLevelSamples 0 6 ≤ (-7176679/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (96000*fourthLevelSamples 1 + 4338000*fourthLevelSamples 2 - 6644000*fourthLevelSamples 3 + 3168000*fourthLevelSamples 4 + 1288000*fourthLevelSamples 5 - 1608000*fourthLevelSamples 6 - 192000*fourthLevelSamples 7 + 956000*fourthLevelSamples 8 - 2356000*fourthLevelSamples 10 + 4000000*fourthLevelSamples 11 - 3168000*fourthLevelSamples 12 + 1356000*fourthLevelSamples 13 - 374000*fourthLevelSamples 14 + 96000*fourthLevelSamples 15 - 16000*fourthLevelSamples 16) / 1000000 - (19000) / 1000000000000000 ∧ (96000*fourthLevelSamples 1 + 4338000*fourthLevelSamples 2 - 6644000*fourthLevelSamples 3 + 3168000*fourthLevelSamples 4 + 1288000*fourthLevelSamples 5 - 1608000*fourthLevelSamples 6 - 192000*fourthLevelSamples 7 + 956000*fourthLevelSamples 8 - 2356000*fourthLevelSamples 10 + 4000000*fourthLevelSamples 11 - 3168000*fourthLevelSamples 12 + 1356000*fourthLevelSamples 13 - 374000*fourthLevelSamples 14 + 96000*fourthLevelSamples 15 - 16000*fourthLevelSamples 16) / 1000000 - (19000) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_0_7 :
    (-2031579/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 0 7 ∧
      fourthLevelOddSheared fourthLevelSamples 0 7 ≤ (-2031578/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (- 7996000*fourthLevelSamples 1 + 5054000*fourthLevelSamples 2 - 1992000*fourthLevelSamples 3 + 286000*fourthLevelSamples 4 + 876000*fourthLevelSamples 5 - 2494000*fourthLevelSamples 6 + 3992000*fourthLevelSamples 7 - 4548000*fourthLevelSamples 8 + 4000000*fourthLevelSamples 9 - 2538000*fourthLevelSamples 10 + 1036000*fourthLevelSamples 11 - 286000*fourthLevelSamples 12 + 80000*fourthLevelSamples 13 - 22000*fourthLevelSamples 14 + 4000*fourthLevelSamples 15) / 1000000 - (-74000) / 1000000000000000 ∧ (- 7996000*fourthLevelSamples 1 + 5054000*fourthLevelSamples 2 - 1992000*fourthLevelSamples 3 + 286000*fourthLevelSamples 4 + 876000*fourthLevelSamples 5 - 2494000*fourthLevelSamples 6 + 3992000*fourthLevelSamples 7 - 4548000*fourthLevelSamples 8 + 4000000*fourthLevelSamples 9 - 2538000*fourthLevelSamples 10 + 1036000*fourthLevelSamples 11 - 286000*fourthLevelSamples 12 + 80000*fourthLevelSamples 13 - 22000*fourthLevelSamples 14 + 4000*fourthLevelSamples 15) / 1000000 - (-74000) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2]

theorem fourthLevelOddSheared_bounds_1_0 :
    (-10787574/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 1 0 ∧
      fourthLevelOddSheared fourthLevelSamples 1 0 ≤ (-10787573/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (- 4000000*fourthLevelSamples 4 - 2000000*fourthLevelSamples 8 + 4000000*fourthLevelSamples 12 - 1500000*fourthLevelSamples 16) / 1000000 - (-250000) / 1000000000000000 ∧ (- 4000000*fourthLevelSamples 4 - 2000000*fourthLevelSamples 8 + 4000000*fourthLevelSamples 12 - 1500000*fourthLevelSamples 16) / 1000000 - (-250000) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_4_bounds).2, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_4_bounds).1, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_1_1 :
    (6302577996/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 1 1 ∧
      fourthLevelOddSheared fourthLevelSamples 1 1 ≤ (6302577997/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (26000000*fourthLevelSamples 4 - 15500000*fourthLevelSamples 8 + 6000000*fourthLevelSamples 12 - 1125000*fourthLevelSamples 16) / 1000000 - (2062500) / 1000000000000000 ∧ (26000000*fourthLevelSamples 4 - 15500000*fourthLevelSamples 8 + 6000000*fourthLevelSamples 12 - 1125000*fourthLevelSamples 16) / 1000000 - (2062500) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_4_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_4_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_1_2 :
    (-2742984/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 1 2 ∧
      fourthLevelOddSheared fourthLevelSamples 1 2 ≤ (-2742983/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (- 5000000*fourthLevelSamples 2 - 8203000*fourthLevelSamples 4 + 10000000*fourthLevelSamples 6 + 2276000*fourthLevelSamples 8 - 8000000*fourthLevelSamples 10 + 1323000*fourthLevelSamples 12 + 3000000*fourthLevelSamples 14 - 1300500*fourthLevelSamples 16) / 1000000 - (-450500) / 1000000000000000 ∧ (- 5000000*fourthLevelSamples 2 - 8203000*fourthLevelSamples 4 + 10000000*fourthLevelSamples 6 + 2276000*fourthLevelSamples 8 - 8000000*fourthLevelSamples 10 + 1323000*fourthLevelSamples 12 + 3000000*fourthLevelSamples 14 - 1300500*fourthLevelSamples 16) / 1000000 - (-450500) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_2_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_2_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_1_3 :
    (-1742475/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 1 3 ∧
      fourthLevelOddSheared fourthLevelSamples 1 3 ≤ (-1742474/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (795000*fourthLevelSamples 2 + 1256500*fourthLevelSamples 4 - 2590000*fourthLevelSamples 6 + 1195000*fourthLevelSamples 8 + 1072000*fourthLevelSamples 10 - 1544500*fourthLevelSamples 12 + 723000*fourthLevelSamples 14 - 129000*fourthLevelSamples 16) / 1000000 - (18500) / 1000000000000000 ∧ (795000*fourthLevelSamples 2 + 1256500*fourthLevelSamples 4 - 2590000*fourthLevelSamples 6 + 1195000*fourthLevelSamples 8 + 1072000*fourthLevelSamples 10 - 1544500*fourthLevelSamples 12 + 723000*fourthLevelSamples 14 - 129000*fourthLevelSamples 16) / 1000000 - (18500) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_2_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_2_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_1_4 :
    (906415/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 1 4 ∧
      fourthLevelOddSheared fourthLevelSamples 1 4 ≤ (906416/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (3000000*fourthLevelSamples 1 + 3422000*fourthLevelSamples 2 - 8000000*fourthLevelSamples 3 + 5220000*fourthLevelSamples 4 - 6800000*fourthLevelSamples 6 + 10000000*fourthLevelSamples 7 - 5392000*fourthLevelSamples 8 + 5484000*fourthLevelSamples 10 - 8000000*fourthLevelSamples 11 + 3836000*fourthLevelSamples 12 - 2106000*fourthLevelSamples 14 + 3000000*fourthLevelSamples 15 - 1263000*fourthLevelSamples 16) / 1000000 - (63250) / 1000000000000000 ∧ (3000000*fourthLevelSamples 1 + 3422000*fourthLevelSamples 2 - 8000000*fourthLevelSamples 3 + 5220000*fourthLevelSamples 4 - 6800000*fourthLevelSamples 6 + 10000000*fourthLevelSamples 7 - 5392000*fourthLevelSamples 8 + 5484000*fourthLevelSamples 10 - 8000000*fourthLevelSamples 11 + 3836000*fourthLevelSamples 12 - 2106000*fourthLevelSamples 14 + 3000000*fourthLevelSamples 15 - 1263000*fourthLevelSamples 16) / 1000000 - (63250) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_1_5 :
    (-1467056/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 1 5 ∧
      fourthLevelOddSheared fourthLevelSamples 1 5 ≤ (-1467055/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (- 7034000*fourthLevelSamples 1 + 4243000*fourthLevelSamples 2 + 424000*fourthLevelSamples 3 - 6336000*fourthLevelSamples 4 + 10000000*fourthLevelSamples 5 - 8610000*fourthLevelSamples 6 + 3220000*fourthLevelSamples 7 + 3734000*fourthLevelSamples 8 - 8000000*fourthLevelSamples 9 + 6764000*fourthLevelSamples 10 - 2576000*fourthLevelSamples 11 - 1232000*fourthLevelSamples 12 + 3000000*fourthLevelSamples 13 - 2397000*fourthLevelSamples 14 + 966000*fourthLevelSamples 15 - 168000*fourthLevelSamples 16) / 1000000 - (-132750) / 1000000000000000 ∧ (- 7034000*fourthLevelSamples 1 + 4243000*fourthLevelSamples 2 + 424000*fourthLevelSamples 3 - 6336000*fourthLevelSamples 4 + 10000000*fourthLevelSamples 5 - 8610000*fourthLevelSamples 6 + 3220000*fourthLevelSamples 7 + 3734000*fourthLevelSamples 8 - 8000000*fourthLevelSamples 9 + 6764000*fourthLevelSamples 10 - 2576000*fourthLevelSamples 11 - 1232000*fourthLevelSamples 12 + 3000000*fourthLevelSamples 13 - 2397000*fourthLevelSamples 14 + 966000*fourthLevelSamples 15 - 168000*fourthLevelSamples 16) / 1000000 - (-132750) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_1_6 :
    (2249943/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 1 6 ∧
      fourthLevelOddSheared fourthLevelSamples 1 6 ≤ (2249944/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (- 10640000*fourthLevelSamples 1 - 710500*fourthLevelSamples 2 + 10825000*fourthLevelSamples 3 - 12112000*fourthLevelSamples 4 + 6390000*fourthLevelSamples 5 + 2010000*fourthLevelSamples 6 - 7760000*fourthLevelSamples 7 + 6989000*fourthLevelSamples 8 - 2712000*fourthLevelSamples 9 - 1019000*fourthLevelSamples 10 + 2808000*fourthLevelSamples 11 - 2344000*fourthLevelSamples 12 + 1017000*fourthLevelSamples 13 - 280500*fourthLevelSamples 14 + 72000*fourthLevelSamples 15 - 12000*fourthLevelSamples 16) / 1000000 - (-250750) / 1000000000000000 ∧ (- 10640000*fourthLevelSamples 1 - 710500*fourthLevelSamples 2 + 10825000*fourthLevelSamples 3 - 12112000*fourthLevelSamples 4 + 6390000*fourthLevelSamples 5 + 2010000*fourthLevelSamples 6 - 7760000*fourthLevelSamples 7 + 6989000*fourthLevelSamples 8 - 2712000*fourthLevelSamples 9 - 1019000*fourthLevelSamples 10 + 2808000*fourthLevelSamples 11 - 2344000*fourthLevelSamples 12 + 1017000*fourthLevelSamples 13 - 280500*fourthLevelSamples 14 + 72000*fourthLevelSamples 15 - 12000*fourthLevelSamples 16) / 1000000 - (-250750) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_1_7 :
    (1571591/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 1 7 ∧
      fourthLevelOddSheared fourthLevelSamples 1 7 ≤ (1571592/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (7771000*fourthLevelSamples 1 - 1241500*fourthLevelSamples 2 - 5358000*fourthLevelSamples 3 + 8166500*fourthLevelSamples 4 - 7023000*fourthLevelSamples 5 + 3117500*fourthLevelSamples 6 + 938000*fourthLevelSamples 7 - 2839000*fourthLevelSamples 8 + 2840000*fourthLevelSamples 9 - 1859500*fourthLevelSamples 10 + 769000*fourthLevelSamples 11 - 214500*fourthLevelSamples 12 + 60000*fourthLevelSamples 13 - 16500*fourthLevelSamples 14 + 3000*fourthLevelSamples 15) / 1000000 - (154500) / 1000000000000000 ∧ (7771000*fourthLevelSamples 1 - 1241500*fourthLevelSamples 2 - 5358000*fourthLevelSamples 3 + 8166500*fourthLevelSamples 4 - 7023000*fourthLevelSamples 5 + 3117500*fourthLevelSamples 6 + 938000*fourthLevelSamples 7 - 2839000*fourthLevelSamples 8 + 2840000*fourthLevelSamples 9 - 1859500*fourthLevelSamples 10 + 769000*fourthLevelSamples 11 - 214500*fourthLevelSamples 12 + 60000*fourthLevelSamples 13 - 16500*fourthLevelSamples 14 + 3000*fourthLevelSamples 15) / 1000000 - (154500) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2]

theorem fourthLevelOddSheared_bounds_2_0 :
    (2727010/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 2 0 ∧
      fourthLevelOddSheared fourthLevelSamples 2 0 ≤ (2727011/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (4000000*fourthLevelSamples 2 + 2860000*fourthLevelSamples 4 - 8000000*fourthLevelSamples 6 + 4656000*fourthLevelSamples 8 - 2860000*fourthLevelSamples 12 + 4000000*fourthLevelSamples 14 - 1734000*fourthLevelSamples 16) / 1000000 - (82000) / 1000000000000000 ∧ (4000000*fourthLevelSamples 2 + 2860000*fourthLevelSamples 4 - 8000000*fourthLevelSamples 6 + 4656000*fourthLevelSamples 8 - 2860000*fourthLevelSamples 12 + 4000000*fourthLevelSamples 14 - 1734000*fourthLevelSamples 16) / 1000000 - (82000) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_2_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_2_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_2_1 :
    (-2742984/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 2 1 ∧
      fourthLevelOddSheared fourthLevelSamples 2 1 ≤ (-2742983/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (- 5000000*fourthLevelSamples 2 - 8203000*fourthLevelSamples 4 + 10000000*fourthLevelSamples 6 + 2276000*fourthLevelSamples 8 - 8000000*fourthLevelSamples 10 + 1323000*fourthLevelSamples 12 + 3000000*fourthLevelSamples 14 - 1300500*fourthLevelSamples 16) / 1000000 - (-450500) / 1000000000000000 ∧ (- 5000000*fourthLevelSamples 2 - 8203000*fourthLevelSamples 4 + 10000000*fourthLevelSamples 6 + 2276000*fourthLevelSamples 8 - 8000000*fourthLevelSamples 10 + 1323000*fourthLevelSamples 12 + 3000000*fourthLevelSamples 14 - 1300500*fourthLevelSamples 16) / 1000000 - (-450500) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_2_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_2_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_2_2 :
    (1286281916/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 2 2 ∧
      fourthLevelOddSheared fourthLevelSamples 2 2 ≤ (1286281917/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (18376000*fourthLevelSamples 2 - 1561560*fourthLevelSamples 4 - 4752000*fourthLevelSamples 6 - 2029808*fourthLevelSamples 8 + 11440000*fourthLevelSamples 10 - 12959240*fourthLevelSamples 12 + 6936000*fourthLevelSamples 14 - 1503378*fourthLevelSamples 16) / 1000000 - (2099174) / 1000000000000000 ∧ (18376000*fourthLevelSamples 2 - 1561560*fourthLevelSamples 4 - 4752000*fourthLevelSamples 6 - 2029808*fourthLevelSamples 8 + 11440000*fourthLevelSamples 10 - 12959240*fourthLevelSamples 12 + 6936000*fourthLevelSamples 14 - 1503378*fourthLevelSamples 16) / 1000000 - (2099174) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_2_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_2_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_2_3 :
    (507146/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 2 3 ∧
      fourthLevelOddSheared fourthLevelSamples 2 3 ≤ (507147/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (10938308*fourthLevelSamples 2 - 15437014*fourthLevelSamples 4 + 17711384*fourthLevelSamples 6 - 15441688*fourthLevelSamples 8 + 9882520*fourthLevelSamples 10 - 4357066*fourthLevelSamples 12 + 1179788*fourthLevelSamples 14 - 149124*fourthLevelSamples 16) / 1000000 - (473898) / 1000000000000000 ∧ (10938308*fourthLevelSamples 2 - 15437014*fourthLevelSamples 4 + 17711384*fourthLevelSamples 6 - 15441688*fourthLevelSamples 8 + 9882520*fourthLevelSamples 10 - 4357066*fourthLevelSamples 12 + 1179788*fourthLevelSamples 14 - 149124*fourthLevelSamples 16) / 1000000 - (473898) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_2_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_2_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_2_4 :
    (-580301/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 2 4 ∧
      fourthLevelOddSheared fourthLevelSamples 2 4 ≤ (-580300/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (- 4532000*fourthLevelSamples 1 - 4477112*fourthLevelSamples 2 + 5720000*fourthLevelSamples 3 - 1759928*fourthLevelSamples 4 + 1087680*fourthLevelSamples 6 - 2376000*fourthLevelSamples 7 + 2320912*fourthLevelSamples 8 - 5416032*fourthLevelSamples 10 + 5720000*fourthLevelSamples 11 + 3748888*fourthLevelSamples 12 - 8000000*fourthLevelSamples 13 + 933464*fourthLevelSamples 14 + 3468000*fourthLevelSamples 15 - 1460028*fourthLevelSamples 16) / 1000000 - (-417288) / 1000000000000000 ∧ (- 4532000*fourthLevelSamples 1 - 4477112*fourthLevelSamples 2 + 5720000*fourthLevelSamples 3 - 1759928*fourthLevelSamples 4 + 1087680*fourthLevelSamples 6 - 2376000*fourthLevelSamples 7 + 2320912*fourthLevelSamples 8 - 5416032*fourthLevelSamples 10 + 5720000*fourthLevelSamples 11 + 3748888*fourthLevelSamples 12 - 8000000*fourthLevelSamples 13 + 933464*fourthLevelSamples 14 + 3468000*fourthLevelSamples 15 - 1460028*fourthLevelSamples 16) / 1000000 - (-417288) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_2_5 :
    (-258988/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 2 5 ∧
      fourthLevelOddSheared fourthLevelSamples 2 5 ≤ (-258987/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (- 3739304*fourthLevelSamples 1 - 1998556*fourthLevelSamples 2 + 5309840*fourthLevelSamples 3 - 2278480*fourthLevelSamples 4 - 2376000*fourthLevelSamples 5 + 3533736*fourthLevelSamples 6 - 765072*fourthLevelSamples 7 - 4277160*fourthLevelSamples 8 + 5720000*fourthLevelSamples 9 + 339752*fourthLevelSamples 10 - 6158160*fourthLevelSamples 11 + 4129600*fourthLevelSamples 12 + 892000*fourthLevelSamples 13 - 2322932*fourthLevelSamples 14 + 1116696*fourthLevelSamples 15 - 194208*fourthLevelSamples 16) / 1000000 - (-247600) / 1000000000000000 ∧ (- 3739304*fourthLevelSamples 1 - 1998556*fourthLevelSamples 2 + 5309840*fourthLevelSamples 3 - 2278480*fourthLevelSamples 4 - 2376000*fourthLevelSamples 5 + 3533736*fourthLevelSamples 6 - 765072*fourthLevelSamples 7 - 4277160*fourthLevelSamples 8 + 5720000*fourthLevelSamples 9 + 339752*fourthLevelSamples 10 - 6158160*fourthLevelSamples 11 + 4129600*fourthLevelSamples 12 + 892000*fourthLevelSamples 13 - 2322932*fourthLevelSamples 14 + 1116696*fourthLevelSamples 15 - 194208*fourthLevelSamples 16) / 1000000 - (-247600) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_2_6 :
    (-551390/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 2 6 ∧
      fourthLevelOddSheared fourthLevelSamples 2 6 ≤ (-551389/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (4838312*fourthLevelSamples 1 + 3539306*fourthLevelSamples 2 - 9063068*fourthLevelSamples 3 + 5145576*fourthLevelSamples 4 + 2662536*fourthLevelSamples 5 - 7037576*fourthLevelSamples 6 + 5662976*fourthLevelSamples 7 + 992372*fourthLevelSamples 8 - 6060920*fourthLevelSamples 9 + 3758528*fourthLevelSamples 10 + 893280*fourthLevelSamples 11 - 2021536*fourthLevelSamples 12 + 983652*fourthLevelSamples 13 - 292258*fourthLevelSamples 14 + 83232*fourthLevelSamples 15 - 13872*fourthLevelSamples 16) / 1000000 - (230448) / 1000000000000000 ∧ (4838312*fourthLevelSamples 1 + 3539306*fourthLevelSamples 2 - 9063068*fourthLevelSamples 3 + 5145576*fourthLevelSamples 4 + 2662536*fourthLevelSamples 5 - 7037576*fourthLevelSamples 6 + 5662976*fourthLevelSamples 7 + 992372*fourthLevelSamples 8 - 6060920*fourthLevelSamples 9 + 3758528*fourthLevelSamples 10 + 893280*fourthLevelSamples 11 - 2021536*fourthLevelSamples 12 + 983652*fourthLevelSamples 13 - 292258*fourthLevelSamples 14 + 83232*fourthLevelSamples 15 - 13872*fourthLevelSamples 16) / 1000000 - (230448) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_2_7 :
    (-500781/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 2 7 ∧
      fourthLevelOddSheared fourthLevelSamples 2 7 ≤ (-500780/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (- 944652*fourthLevelSamples 1 - 1600302*fourthLevelSamples 2 + 3107696*fourthLevelSamples 3 - 1505718*fourthLevelSamples 4 - 1429308*fourthLevelSamples 5 + 3279282*fourthLevelSamples 6 - 3052896*fourthLevelSamples 7 + 723904*fourthLevelSamples 8 + 1510400*fourthLevelSamples 9 - 1659906*fourthLevelSamples 10 + 743932*fourthLevelSamples 11 - 203962*fourthLevelSamples 12 + 61360*fourthLevelSamples 13 - 19074*fourthLevelSamples 14 + 3468*fourthLevelSamples 15) / 1000000 - (-25308) / 1000000000000000 ∧ (- 944652*fourthLevelSamples 1 - 1600302*fourthLevelSamples 2 + 3107696*fourthLevelSamples 3 - 1505718*fourthLevelSamples 4 - 1429308*fourthLevelSamples 5 + 3279282*fourthLevelSamples 6 - 3052896*fourthLevelSamples 7 + 723904*fourthLevelSamples 8 + 1510400*fourthLevelSamples 9 - 1659906*fourthLevelSamples 10 + 743932*fourthLevelSamples 11 - 203962*fourthLevelSamples 12 + 61360*fourthLevelSamples 13 - 19074*fourthLevelSamples 14 + 3468*fourthLevelSamples 15) / 1000000 - (-25308) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2]

theorem fourthLevelOddSheared_bounds_3_0 :
    (-2910795/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 3 0 ∧
      fourthLevelOddSheared fourthLevelSamples 3 0 ≤ (-2910794/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (- 7036000*fourthLevelSamples 2 + 2518000*fourthLevelSamples 4 + 2072000*fourthLevelSamples 6 - 4204000*fourthLevelSamples 8 + 4000000*fourthLevelSamples 10 - 2518000*fourthLevelSamples 12 + 964000*fourthLevelSamples 14 - 172000*fourthLevelSamples 16) / 1000000 - (-146000) / 1000000000000000 ∧ (- 7036000*fourthLevelSamples 2 + 2518000*fourthLevelSamples 4 + 2072000*fourthLevelSamples 6 - 4204000*fourthLevelSamples 8 + 4000000*fourthLevelSamples 10 - 2518000*fourthLevelSamples 12 + 964000*fourthLevelSamples 14 - 172000*fourthLevelSamples 16) / 1000000 - (-146000) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_2_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_2_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_3_1 :
    (-1742475/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 3 1 ∧
      fourthLevelOddSheared fourthLevelSamples 3 1 ≤ (-1742474/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (795000*fourthLevelSamples 2 + 1256500*fourthLevelSamples 4 - 2590000*fourthLevelSamples 6 + 1195000*fourthLevelSamples 8 + 1072000*fourthLevelSamples 10 - 1544500*fourthLevelSamples 12 + 723000*fourthLevelSamples 14 - 129000*fourthLevelSamples 16) / 1000000 - (18500) / 1000000000000000 ∧ (795000*fourthLevelSamples 2 + 1256500*fourthLevelSamples 4 - 2590000*fourthLevelSamples 6 + 1195000*fourthLevelSamples 8 + 1072000*fourthLevelSamples 10 - 1544500*fourthLevelSamples 12 + 723000*fourthLevelSamples 14 - 129000*fourthLevelSamples 16) / 1000000 - (18500) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_2_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_2_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_3_2 :
    (507146/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 3 2 ∧
      fourthLevelOddSheared fourthLevelSamples 3 2 ≤ (507147/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (10938308*fourthLevelSamples 2 - 15437014*fourthLevelSamples 4 + 17711384*fourthLevelSamples 6 - 15441688*fourthLevelSamples 8 + 9882520*fourthLevelSamples 10 - 4357066*fourthLevelSamples 12 + 1179788*fourthLevelSamples 14 - 149124*fourthLevelSamples 16) / 1000000 - (473898) / 1000000000000000 ∧ (10938308*fourthLevelSamples 2 - 15437014*fourthLevelSamples 4 + 17711384*fourthLevelSamples 6 - 15441688*fourthLevelSamples 8 + 9882520*fourthLevelSamples 10 - 4357066*fourthLevelSamples 12 + 1179788*fourthLevelSamples 14 - 149124*fourthLevelSamples 16) / 1000000 - (473898) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_2_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_2_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_3_3 :
    (667841601/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 3 3 ∧
      fourthLevelOddSheared fourthLevelSamples 3 3 ≤ (667841602/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (30857160*fourthLevelSamples 2 - 23740960*fourthLevelSamples 4 + 15144272*fourthLevelSamples 6 - 7808418*fourthLevelSamples 8 + 3115352*fourthLevelSamples 10 - 897744*fourthLevelSamples 12 + 165808*fourthLevelSamples 14 - 14792*fourthLevelSamples 16) / 1000000 - (2137640) / 1000000000000000 ∧ (30857160*fourthLevelSamples 2 - 23740960*fourthLevelSamples 4 + 15144272*fourthLevelSamples 6 - 7808418*fourthLevelSamples 8 + 3115352*fourthLevelSamples 10 - 897744*fourthLevelSamples 12 + 165808*fourthLevelSamples 14 - 14792*fourthLevelSamples 16) / 1000000 - (2137640) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_2_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_2_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_3_4 :
    (145746/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 3 4 ∧
      fourthLevelOddSheared fourthLevelSamples 3 4 ≤ (145747/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (- 1584000*fourthLevelSamples 1 - 5311648*fourthLevelSamples 2 + 5036000*fourthLevelSamples 3 + 5516108*fourthLevelSamples 4 - 8000000*fourthLevelSamples 5 - 4544528*fourthLevelSamples 6 + 9096000*fourthLevelSamples 7 + 2664600*fourthLevelSamples 8 - 8000000*fourthLevelSamples 9 - 483176*fourthLevelSamples 10 + 5036000*fourthLevelSamples 11 - 713036*fourthLevelSamples 12 - 1928000*fourthLevelSamples 13 + 570200*fourthLevelSamples 14 + 344000*fourthLevelSamples 15 - 144824*fourthLevelSamples 16) / 1000000 - (-187564) / 1000000000000000 ∧ (- 1584000*fourthLevelSamples 1 - 5311648*fourthLevelSamples 2 + 5036000*fourthLevelSamples 3 + 5516108*fourthLevelSamples 4 - 8000000*fourthLevelSamples 5 - 4544528*fourthLevelSamples 6 + 9096000*fourthLevelSamples 7 + 2664600*fourthLevelSamples 8 - 8000000*fourthLevelSamples 9 - 483176*fourthLevelSamples 10 + 5036000*fourthLevelSamples 11 - 713036*fourthLevelSamples 12 - 1928000*fourthLevelSamples 13 + 570200*fourthLevelSamples 14 + 344000*fourthLevelSamples 15 - 144824*fourthLevelSamples 16) / 1000000 - (-187564) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_3_5 :
    (-293211/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 3 5 ∧
      fourthLevelOddSheared fourthLevelSamples 3 5 ≤ (-293210/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (2597952*fourthLevelSamples 1 + 3617396*fourthLevelSamples 2 - 6034408*fourthLevelSamples 3 - 719720*fourthLevelSamples 4 + 6520000*fourthLevelSamples 5 - 1553048*fourthLevelSamples 6 - 5071088*fourthLevelSamples 7 + 2802064*fourthLevelSamples 8 + 2460000*fourthLevelSamples 9 - 2453428*fourthLevelSamples 10 - 306408*fourthLevelSamples 11 + 1065816*fourthLevelSamples 12 - 276816*fourthLevelSamples 13 - 166888*fourthLevelSamples 14 + 110768*fourthLevelSamples 15 - 19264*fourthLevelSamples 16) / 1000000 - (183420) / 1000000000000000 ∧ (2597952*fourthLevelSamples 1 + 3617396*fourthLevelSamples 2 - 6034408*fourthLevelSamples 3 - 719720*fourthLevelSamples 4 + 6520000*fourthLevelSamples 5 - 1553048*fourthLevelSamples 6 - 5071088*fourthLevelSamples 7 + 2802064*fourthLevelSamples 8 + 2460000*fourthLevelSamples 9 - 2453428*fourthLevelSamples 10 - 306408*fourthLevelSamples 11 + 1065816*fourthLevelSamples 12 - 276816*fourthLevelSamples 13 - 166888*fourthLevelSamples 14 + 110768*fourthLevelSamples 15 - 19264*fourthLevelSamples 16) / 1000000 - (183420) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_3_6 :
    (190902/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 3 6 ∧
      fourthLevelOddSheared fourthLevelSamples 3 6 ≤ (190903/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (- 1948404*fourthLevelSamples 1 - 2804090*fourthLevelSamples 2 + 4693480*fourthLevelSamples 3 + 262284*fourthLevelSamples 4 - 4764456*fourthLevelSamples 5 + 1903336*fourthLevelSamples 6 + 2542304*fourthLevelSamples 7 - 2061840*fourthLevelSamples 8 - 412796*fourthLevelSamples 9 + 885494*fourthLevelSamples 10 - 188728*fourthLevelSamples 11 - 112324*fourthLevelSamples 12 + 70344*fourthLevelSamples 13 - 24452*fourthLevelSamples 14 + 8256*fourthLevelSamples 15 - 1376*fourthLevelSamples 16) / 1000000 - (-136144) / 1000000000000000 ∧ (- 1948404*fourthLevelSamples 1 - 2804090*fourthLevelSamples 2 + 4693480*fourthLevelSamples 3 + 262284*fourthLevelSamples 4 - 4764456*fourthLevelSamples 5 + 1903336*fourthLevelSamples 6 + 2542304*fourthLevelSamples 7 - 2061840*fourthLevelSamples 8 - 412796*fourthLevelSamples 9 + 885494*fourthLevelSamples 10 - 188728*fourthLevelSamples 11 - 112324*fourthLevelSamples 12 + 70344*fourthLevelSamples 13 - 24452*fourthLevelSamples 14 + 8256*fourthLevelSamples 15 - 1376*fourthLevelSamples 16) / 1000000 - (-136144) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_3_7 :
    (173555/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 3 7 ∧
      fourthLevelOddSheared fourthLevelSamples 3 7 ≤ (173556/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (388900*fourthLevelSamples 1 + 809508*fourthLevelSamples 2 - 1255572*fourthLevelSamples 3 - 57576*fourthLevelSamples 4 + 1299016*fourthLevelSamples 5 - 699502*fourthLevelSamples 6 - 430580*fourthLevelSamples 7 + 516114*fourthLevelSamples 8 - 62632*fourthLevelSamples 9 - 108114*fourthLevelSamples 10 + 55572*fourthLevelSamples 11 - 13992*fourthLevelSamples 12 + 4952*fourthLevelSamples 13 - 1892*fourthLevelSamples 14 + 344*fourthLevelSamples 15) / 1000000 - (1990) / 1000000000000000 ∧ (388900*fourthLevelSamples 1 + 809508*fourthLevelSamples 2 - 1255572*fourthLevelSamples 3 - 57576*fourthLevelSamples 4 + 1299016*fourthLevelSamples 5 - 699502*fourthLevelSamples 6 - 430580*fourthLevelSamples 7 + 516114*fourthLevelSamples 8 - 62632*fourthLevelSamples 9 - 108114*fourthLevelSamples 10 + 55572*fourthLevelSamples 11 - 13992*fourthLevelSamples 12 + 4952*fourthLevelSamples 13 - 1892*fourthLevelSamples 14 + 344*fourthLevelSamples 15) / 1000000 - (1990) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2]

theorem fourthLevelOddSheared_bounds_4_0 :
    (175218/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 4 0 ∧
      fourthLevelOddSheared fourthLevelSamples 4 0 ≤ (175220/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (4000000*fourthLevelSamples 1 - 2456000*fourthLevelSamples 2 - 624000*fourthLevelSamples 4 + 5440000*fourthLevelSamples 6 - 8000000*fourthLevelSamples 7 + 3456000*fourthLevelSamples 8 - 176000*fourthLevelSamples 10 + 624000*fourthLevelSamples 12 - 2808000*fourthLevelSamples 14 + 4000000*fourthLevelSamples 15 - 1684000*fourthLevelSamples 16) / 1000000 - (11000) / 1000000000000000 ∧ (4000000*fourthLevelSamples 1 - 2456000*fourthLevelSamples 2 - 624000*fourthLevelSamples 4 + 5440000*fourthLevelSamples 6 - 8000000*fourthLevelSamples 7 + 3456000*fourthLevelSamples 8 - 176000*fourthLevelSamples 10 + 624000*fourthLevelSamples 12 - 2808000*fourthLevelSamples 14 + 4000000*fourthLevelSamples 15 - 1684000*fourthLevelSamples 16) / 1000000 - (11000) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_4_1 :
    (906415/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 4 1 ∧
      fourthLevelOddSheared fourthLevelSamples 4 1 ≤ (906416/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (3000000*fourthLevelSamples 1 + 3422000*fourthLevelSamples 2 - 8000000*fourthLevelSamples 3 + 5220000*fourthLevelSamples 4 - 6800000*fourthLevelSamples 6 + 10000000*fourthLevelSamples 7 - 5392000*fourthLevelSamples 8 + 5484000*fourthLevelSamples 10 - 8000000*fourthLevelSamples 11 + 3836000*fourthLevelSamples 12 - 2106000*fourthLevelSamples 14 + 3000000*fourthLevelSamples 15 - 1263000*fourthLevelSamples 16) / 1000000 - (63250) / 1000000000000000 ∧ (3000000*fourthLevelSamples 1 + 3422000*fourthLevelSamples 2 - 8000000*fourthLevelSamples 3 + 5220000*fourthLevelSamples 4 - 6800000*fourthLevelSamples 6 + 10000000*fourthLevelSamples 7 - 5392000*fourthLevelSamples 8 + 5484000*fourthLevelSamples 10 - 8000000*fourthLevelSamples 11 + 3836000*fourthLevelSamples 12 - 2106000*fourthLevelSamples 14 + 3000000*fourthLevelSamples 15 - 1263000*fourthLevelSamples 16) / 1000000 - (63250) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_4_2 :
    (-580301/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 4 2 ∧
      fourthLevelOddSheared fourthLevelSamples 4 2 ≤ (-580300/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (- 4532000*fourthLevelSamples 1 - 4477112*fourthLevelSamples 2 + 5720000*fourthLevelSamples 3 - 1759928*fourthLevelSamples 4 + 1087680*fourthLevelSamples 6 - 2376000*fourthLevelSamples 7 + 2320912*fourthLevelSamples 8 - 5416032*fourthLevelSamples 10 + 5720000*fourthLevelSamples 11 + 3748888*fourthLevelSamples 12 - 8000000*fourthLevelSamples 13 + 933464*fourthLevelSamples 14 + 3468000*fourthLevelSamples 15 - 1460028*fourthLevelSamples 16) / 1000000 - (-417288) / 1000000000000000 ∧ (- 4532000*fourthLevelSamples 1 - 4477112*fourthLevelSamples 2 + 5720000*fourthLevelSamples 3 - 1759928*fourthLevelSamples 4 + 1087680*fourthLevelSamples 6 - 2376000*fourthLevelSamples 7 + 2320912*fourthLevelSamples 8 - 5416032*fourthLevelSamples 10 + 5720000*fourthLevelSamples 11 + 3748888*fourthLevelSamples 12 - 8000000*fourthLevelSamples 13 + 933464*fourthLevelSamples 14 + 3468000*fourthLevelSamples 15 - 1460028*fourthLevelSamples 16) / 1000000 - (-417288) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_4_3 :
    (145746/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 4 3 ∧
      fourthLevelOddSheared fourthLevelSamples 4 3 ≤ (145747/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (- 1584000*fourthLevelSamples 1 - 5311648*fourthLevelSamples 2 + 5036000*fourthLevelSamples 3 + 5516108*fourthLevelSamples 4 - 8000000*fourthLevelSamples 5 - 4544528*fourthLevelSamples 6 + 9096000*fourthLevelSamples 7 + 2664600*fourthLevelSamples 8 - 8000000*fourthLevelSamples 9 - 483176*fourthLevelSamples 10 + 5036000*fourthLevelSamples 11 - 713036*fourthLevelSamples 12 - 1928000*fourthLevelSamples 13 + 570200*fourthLevelSamples 14 + 344000*fourthLevelSamples 15 - 144824*fourthLevelSamples 16) / 1000000 - (-187564) / 1000000000000000 ∧ (- 1584000*fourthLevelSamples 1 - 5311648*fourthLevelSamples 2 + 5036000*fourthLevelSamples 3 + 5516108*fourthLevelSamples 4 - 8000000*fourthLevelSamples 5 - 4544528*fourthLevelSamples 6 + 9096000*fourthLevelSamples 7 + 2664600*fourthLevelSamples 8 - 8000000*fourthLevelSamples 9 - 483176*fourthLevelSamples 10 + 5036000*fourthLevelSamples 11 - 713036*fourthLevelSamples 12 - 1928000*fourthLevelSamples 13 + 570200*fourthLevelSamples 14 + 344000*fourthLevelSamples 15 - 144824*fourthLevelSamples 16) / 1000000 - (-187564) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_4_4 :
    (172104152/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 4 4 ∧
      fourthLevelOddSheared fourthLevelSamples 4 4 ≤ (172104153/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (17968000*fourthLevelSamples 1 - 2851168*fourthLevelSamples 2 - 2496000*fourthLevelSamples 3 + 486208*fourthLevelSamples 4 + 704000*fourthLevelSamples 5 + 60544*fourthLevelSamples 6 - 352000*fourthLevelSamples 7 - 540704*fourthLevelSamples 8 + 704000*fourthLevelSamples 9 + 1455808*fourthLevelSamples 10 - 2496000*fourthLevelSamples 11 - 2891616*fourthLevelSamples 12 + 11232000*fourthLevelSamples 13 - 12728672*fourthLevelSamples 14 + 6736000*fourthLevelSamples 15 - 1417928*fourthLevelSamples 16) / 1000000 - (2087779) / 1000000000000000 ∧ (17968000*fourthLevelSamples 1 - 2851168*fourthLevelSamples 2 - 2496000*fourthLevelSamples 3 + 486208*fourthLevelSamples 4 + 704000*fourthLevelSamples 5 + 60544*fourthLevelSamples 6 - 352000*fourthLevelSamples 7 - 540704*fourthLevelSamples 8 + 704000*fourthLevelSamples 9 + 1455808*fourthLevelSamples 10 - 2496000*fourthLevelSamples 11 - 2891616*fourthLevelSamples 12 + 11232000*fourthLevelSamples 13 - 12728672*fourthLevelSamples 14 + 6736000*fourthLevelSamples 15 - 1417928*fourthLevelSamples 16) / 1000000 - (2087779) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_4_5 :
    (56364/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 4 5 ∧
      fourthLevelOddSheared fourthLevelSamples 4 5 ≤ (56365/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (14100848*fourthLevelSamples 1 - 13548856*fourthLevelSamples 2 + 7798144*fourthLevelSamples 3 - 1181472*fourthLevelSamples 4 - 1054656*fourthLevelSamples 5 - 161520*fourthLevelSamples 6 + 791328*fourthLevelSamples 7 + 915056*fourthLevelSamples 8 - 2126656*fourthLevelSamples 9 - 1749888*fourthLevelSamples 10 + 9694144*fourthLevelSamples 11 - 14303376*fourthLevelSamples 12 + 11568352*fourthLevelSamples 13 - 5581528*fourthLevelSamples 14 + 1532496*fourthLevelSamples 15 - 188608*fourthLevelSamples 16) / 1000000 - (684363) / 1000000000000000 ∧ (14100848*fourthLevelSamples 1 - 13548856*fourthLevelSamples 2 + 7798144*fourthLevelSamples 3 - 1181472*fourthLevelSamples 4 - 1054656*fourthLevelSamples 5 - 161520*fourthLevelSamples 6 + 791328*fourthLevelSamples 7 + 915056*fourthLevelSamples 8 - 2126656*fourthLevelSamples 9 - 1749888*fourthLevelSamples 10 + 9694144*fourthLevelSamples 11 - 14303376*fourthLevelSamples 12 + 11568352*fourthLevelSamples 13 - 5581528*fourthLevelSamples 14 + 1532496*fourthLevelSamples 15 - 188608*fourthLevelSamples 16) / 1000000 - (684363) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_4_6 :
    (-61226/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 4 6 ∧
      fourthLevelOddSheared fourthLevelSamples 4 6 ≤ (-61225/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (1580368*fourthLevelSamples 1 - 6739292*fourthLevelSamples 2 + 13007128*fourthLevelSamples 3 - 14359424*fourthLevelSamples 4 + 8380784*fourthLevelSamples 5 - 215120*fourthLevelSamples 6 - 2980896*fourthLevelSamples 7 - 1573608*fourthLevelSamples 8 + 9913376*fourthLevelSamples 9 - 14316344*fourthLevelSamples 10 + 11577872*fourthLevelSamples 11 - 5899560*fourthLevelSamples 12 + 2024536*fourthLevelSamples 13 - 529372*fourthLevelSamples 14 + 112832*fourthLevelSamples 15 - 13472*fourthLevelSamples 16) / 1000000 - (12371) / 1000000000000000 ∧ (1580368*fourthLevelSamples 1 - 6739292*fourthLevelSamples 2 + 13007128*fourthLevelSamples 3 - 14359424*fourthLevelSamples 4 + 8380784*fourthLevelSamples 5 - 215120*fourthLevelSamples 6 - 2980896*fourthLevelSamples 7 - 1573608*fourthLevelSamples 8 + 9913376*fourthLevelSamples 9 - 14316344*fourthLevelSamples 10 + 11577872*fourthLevelSamples 11 - 5899560*fourthLevelSamples 12 + 2024536*fourthLevelSamples 13 - 529372*fourthLevelSamples 14 + 112832*fourthLevelSamples 15 - 13472*fourthLevelSamples 16) / 1000000 - (12371) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_4_7 :
    (-86391/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 4 7 ∧
      fourthLevelOddSheared fourthLevelSamples 4 7 ≤ (-86390/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (84280*fourthLevelSamples 1 - 95068*fourthLevelSamples 2 + 1158112*fourthLevelSamples 3 - 4669884*fourthLevelSamples 4 + 10404312*fourthLevelSamples 5 - 15754732*fourthLevelSamples 6 + 17763632*fourthLevelSamples 7 - 15305472*fourthLevelSamples 8 + 9873936*fourthLevelSamples 9 - 4603676*fourthLevelSamples 10 + 1555384*fourthLevelSamples 11 - 431700*fourthLevelSamples 12 + 116976*fourthLevelSamples 13 - 26524*fourthLevelSamples 14 + 3368*fourthLevelSamples 15) / 1000000 - (4094) / 1000000000000000 ∧ (84280*fourthLevelSamples 1 - 95068*fourthLevelSamples 2 + 1158112*fourthLevelSamples 3 - 4669884*fourthLevelSamples 4 + 10404312*fourthLevelSamples 5 - 15754732*fourthLevelSamples 6 + 17763632*fourthLevelSamples 7 - 15305472*fourthLevelSamples 8 + 9873936*fourthLevelSamples 9 - 4603676*fourthLevelSamples 10 + 1555384*fourthLevelSamples 11 - 431700*fourthLevelSamples 12 + 116976*fourthLevelSamples 13 - 26524*fourthLevelSamples 14 + 3368*fourthLevelSamples 15) / 1000000 - (4094) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2]

theorem fourthLevelOddSheared_bounds_5_0 :
    (-12553761/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 5 0 ∧
      fourthLevelOddSheared fourthLevelSamples 5 0 ≤ (-12553760/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (1288000*fourthLevelSamples 1 - 4188000*fourthLevelSamples 2 + 4000000*fourthLevelSamples 3 + 2240000*fourthLevelSamples 4 - 8000000*fourthLevelSamples 5 + 6888000*fourthLevelSamples 6 - 2576000*fourthLevelSamples 7 + 200000*fourthLevelSamples 8 + 496000*fourthLevelSamples 10 - 2240000*fourthLevelSamples 12 + 4000000*fourthLevelSamples 13 - 3196000*fourthLevelSamples 14 + 1288000*fourthLevelSamples 15 - 224000*fourthLevelSamples 16) / 1000000 - (-5000) / 1000000000000000 ∧ (1288000*fourthLevelSamples 1 - 4188000*fourthLevelSamples 2 + 4000000*fourthLevelSamples 3 + 2240000*fourthLevelSamples 4 - 8000000*fourthLevelSamples 5 + 6888000*fourthLevelSamples 6 - 2576000*fourthLevelSamples 7 + 200000*fourthLevelSamples 8 + 496000*fourthLevelSamples 10 - 2240000*fourthLevelSamples 12 + 4000000*fourthLevelSamples 13 - 3196000*fourthLevelSamples 14 + 1288000*fourthLevelSamples 15 - 224000*fourthLevelSamples 16) / 1000000 - (-5000) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_5_1 :
    (-1467056/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 5 1 ∧
      fourthLevelOddSheared fourthLevelSamples 5 1 ≤ (-1467055/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (- 7034000*fourthLevelSamples 1 + 4243000*fourthLevelSamples 2 + 424000*fourthLevelSamples 3 - 6336000*fourthLevelSamples 4 + 10000000*fourthLevelSamples 5 - 8610000*fourthLevelSamples 6 + 3220000*fourthLevelSamples 7 + 3734000*fourthLevelSamples 8 - 8000000*fourthLevelSamples 9 + 6764000*fourthLevelSamples 10 - 2576000*fourthLevelSamples 11 - 1232000*fourthLevelSamples 12 + 3000000*fourthLevelSamples 13 - 2397000*fourthLevelSamples 14 + 966000*fourthLevelSamples 15 - 168000*fourthLevelSamples 16) / 1000000 - (-132750) / 1000000000000000 ∧ (- 7034000*fourthLevelSamples 1 + 4243000*fourthLevelSamples 2 + 424000*fourthLevelSamples 3 - 6336000*fourthLevelSamples 4 + 10000000*fourthLevelSamples 5 - 8610000*fourthLevelSamples 6 + 3220000*fourthLevelSamples 7 + 3734000*fourthLevelSamples 8 - 8000000*fourthLevelSamples 9 + 6764000*fourthLevelSamples 10 - 2576000*fourthLevelSamples 11 - 1232000*fourthLevelSamples 12 + 3000000*fourthLevelSamples 13 - 2397000*fourthLevelSamples 14 + 966000*fourthLevelSamples 15 - 168000*fourthLevelSamples 16) / 1000000 - (-132750) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_5_2 :
    (-258988/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 5 2 ∧
      fourthLevelOddSheared fourthLevelSamples 5 2 ≤ (-258987/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (- 3739304*fourthLevelSamples 1 - 1998556*fourthLevelSamples 2 + 5309840*fourthLevelSamples 3 - 2278480*fourthLevelSamples 4 - 2376000*fourthLevelSamples 5 + 3533736*fourthLevelSamples 6 - 765072*fourthLevelSamples 7 - 4277160*fourthLevelSamples 8 + 5720000*fourthLevelSamples 9 + 339752*fourthLevelSamples 10 - 6158160*fourthLevelSamples 11 + 4129600*fourthLevelSamples 12 + 892000*fourthLevelSamples 13 - 2322932*fourthLevelSamples 14 + 1116696*fourthLevelSamples 15 - 194208*fourthLevelSamples 16) / 1000000 - (-247600) / 1000000000000000 ∧ (- 3739304*fourthLevelSamples 1 - 1998556*fourthLevelSamples 2 + 5309840*fourthLevelSamples 3 - 2278480*fourthLevelSamples 4 - 2376000*fourthLevelSamples 5 + 3533736*fourthLevelSamples 6 - 765072*fourthLevelSamples 7 - 4277160*fourthLevelSamples 8 + 5720000*fourthLevelSamples 9 + 339752*fourthLevelSamples 10 - 6158160*fourthLevelSamples 11 + 4129600*fourthLevelSamples 12 + 892000*fourthLevelSamples 13 - 2322932*fourthLevelSamples 14 + 1116696*fourthLevelSamples 15 - 194208*fourthLevelSamples 16) / 1000000 - (-247600) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_5_3 :
    (-293211/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 5 3 ∧
      fourthLevelOddSheared fourthLevelSamples 5 3 ≤ (-293210/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (2597952*fourthLevelSamples 1 + 3617396*fourthLevelSamples 2 - 6034408*fourthLevelSamples 3 - 719720*fourthLevelSamples 4 + 6520000*fourthLevelSamples 5 - 1553048*fourthLevelSamples 6 - 5071088*fourthLevelSamples 7 + 2802064*fourthLevelSamples 8 + 2460000*fourthLevelSamples 9 - 2453428*fourthLevelSamples 10 - 306408*fourthLevelSamples 11 + 1065816*fourthLevelSamples 12 - 276816*fourthLevelSamples 13 - 166888*fourthLevelSamples 14 + 110768*fourthLevelSamples 15 - 19264*fourthLevelSamples 16) / 1000000 - (183420) / 1000000000000000 ∧ (2597952*fourthLevelSamples 1 + 3617396*fourthLevelSamples 2 - 6034408*fourthLevelSamples 3 - 719720*fourthLevelSamples 4 + 6520000*fourthLevelSamples 5 - 1553048*fourthLevelSamples 6 - 5071088*fourthLevelSamples 7 + 2802064*fourthLevelSamples 8 + 2460000*fourthLevelSamples 9 - 2453428*fourthLevelSamples 10 - 306408*fourthLevelSamples 11 + 1065816*fourthLevelSamples 12 - 276816*fourthLevelSamples 13 - 166888*fourthLevelSamples 14 + 110768*fourthLevelSamples 15 - 19264*fourthLevelSamples 16) / 1000000 - (183420) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_5_4 :
    (56364/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 5 4 ∧
      fourthLevelOddSheared fourthLevelSamples 5 4 ≤ (56365/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (14100848*fourthLevelSamples 1 - 13548856*fourthLevelSamples 2 + 7798144*fourthLevelSamples 3 - 1181472*fourthLevelSamples 4 - 1054656*fourthLevelSamples 5 - 161520*fourthLevelSamples 6 + 791328*fourthLevelSamples 7 + 915056*fourthLevelSamples 8 - 2126656*fourthLevelSamples 9 - 1749888*fourthLevelSamples 10 + 9694144*fourthLevelSamples 11 - 14303376*fourthLevelSamples 12 + 11568352*fourthLevelSamples 13 - 5581528*fourthLevelSamples 14 + 1532496*fourthLevelSamples 15 - 188608*fourthLevelSamples 16) / 1000000 - (684363) / 1000000000000000 ∧ (14100848*fourthLevelSamples 1 - 13548856*fourthLevelSamples 2 + 7798144*fourthLevelSamples 3 - 1181472*fourthLevelSamples 4 - 1054656*fourthLevelSamples 5 - 161520*fourthLevelSamples 6 + 791328*fourthLevelSamples 7 + 915056*fourthLevelSamples 8 - 2126656*fourthLevelSamples 9 - 1749888*fourthLevelSamples 10 + 9694144*fourthLevelSamples 11 - 14303376*fourthLevelSamples 12 + 11568352*fourthLevelSamples 13 - 5581528*fourthLevelSamples 14 + 1532496*fourthLevelSamples 15 - 188608*fourthLevelSamples 16) / 1000000 - (684363) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_5_5 :
    (120457812/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 5 5 ∧
      fourthLevelOddSheared fourthLevelSamples 5 5 ≤ (120457813/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (26148960*fourthLevelSamples 1 - 11792896*fourthLevelSamples 2 + 1797120*fourthLevelSamples 3 + 404928*fourthLevelSamples 4 + 353152*fourthLevelSamples 5 + 429536*fourthLevelSamples 6 - 1664576*fourthLevelSamples 7 - 979136*fourthLevelSamples 8 + 8321152*fourthLevelSamples 9 - 15047936*fourthLevelSamples 10 + 15669120*fourthLevelSamples 11 - 10760968*fourthLevelSamples 12 + 5012448*fourthLevelSamples 13 - 1545376*fourthLevelSamples 14 + 288512*fourthLevelSamples 15 - 25088*fourthLevelSamples 16) / 1000000 - (2285211) / 1000000000000000 ∧ (26148960*fourthLevelSamples 1 - 11792896*fourthLevelSamples 2 + 1797120*fourthLevelSamples 3 + 404928*fourthLevelSamples 4 + 353152*fourthLevelSamples 5 + 429536*fourthLevelSamples 6 - 1664576*fourthLevelSamples 7 - 979136*fourthLevelSamples 8 + 8321152*fourthLevelSamples 9 - 15047936*fourthLevelSamples 10 + 15669120*fourthLevelSamples 11 - 10760968*fourthLevelSamples 12 + 5012448*fourthLevelSamples 13 - 1545376*fourthLevelSamples 14 + 288512*fourthLevelSamples 15 - 25088*fourthLevelSamples 16) / 1000000 - (2285211) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_5_6 :
    (44527/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 5 6 ∧
      fourthLevelOddSheared fourthLevelSamples 5 6 ≤ (44528/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (14672928*fourthLevelSamples 1 - 16988416*fourthLevelSamples 2 + 13595296*fourthLevelSamples 3 - 5394536*fourthLevelSamples 4 - 730400*fourthLevelSamples 5 - 682784*fourthLevelSamples 6 + 8272560*fourthLevelSamples 7 - 15118792*fourthLevelSamples 8 + 15740176*fourthLevelSamples 9 - 11029248*fourthLevelSamples 10 + 5510600*fourthLevelSamples 11 - 2035652*fourthLevelSamples 12 + 578136*fourthLevelSamples 13 - 129280*fourthLevelSamples 14 + 21056*fourthLevelSamples 15 - 1792*fourthLevelSamples 16) / 1000000 - (663483) / 1000000000000000 ∧ (14672928*fourthLevelSamples 1 - 16988416*fourthLevelSamples 2 + 13595296*fourthLevelSamples 3 - 5394536*fourthLevelSamples 4 - 730400*fourthLevelSamples 5 - 682784*fourthLevelSamples 6 + 8272560*fourthLevelSamples 7 - 15118792*fourthLevelSamples 8 + 15740176*fourthLevelSamples 9 - 11029248*fourthLevelSamples 10 + 5510600*fourthLevelSamples 11 - 2035652*fourthLevelSamples 12 + 578136*fourthLevelSamples 13 - 129280*fourthLevelSamples 14 + 21056*fourthLevelSamples 15 - 1792*fourthLevelSamples 16) / 1000000 - (663483) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_5_7 :
    (3247/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 5 7 ∧
      fourthLevelOddSheared fourthLevelSamples 5 7 ≤ (3248/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (1261840*fourthLevelSamples 1 - 4574092*fourthLevelSamples 2 + 10525776*fourthLevelSamples 3 - 17249284*fourthLevelSamples 4 + 21470504*fourthLevelSamples 5 - 20902320*fourthLevelSamples 6 + 15985888*fourthLevelSamples 7 - 9527964*fourthLevelSamples 8 + 4398608*fourthLevelSamples 9 - 1593108*fourthLevelSamples 10 + 476536*fourthLevelSamples 11 - 126708*fourthLevelSamples 12 + 29520*fourthLevelSamples 13 - 5040*fourthLevelSamples 14 + 448*fourthLevelSamples 15) / 1000000 - (29282) / 1000000000000000 ∧ (1261840*fourthLevelSamples 1 - 4574092*fourthLevelSamples 2 + 10525776*fourthLevelSamples 3 - 17249284*fourthLevelSamples 4 + 21470504*fourthLevelSamples 5 - 20902320*fourthLevelSamples 6 + 15985888*fourthLevelSamples 7 - 9527964*fourthLevelSamples 8 + 4398608*fourthLevelSamples 9 - 1593108*fourthLevelSamples 10 + 476536*fourthLevelSamples 11 - 126708*fourthLevelSamples 12 + 29520*fourthLevelSamples 13 - 5040*fourthLevelSamples 14 + 448*fourthLevelSamples 15) / 1000000 - (29282) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2]

theorem fourthLevelOddSheared_bounds_6_0 :
    (-7176680/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 6 0 ∧
      fourthLevelOddSheared fourthLevelSamples 6 0 ≤ (-7176679/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (96000*fourthLevelSamples 1 + 4338000*fourthLevelSamples 2 - 6644000*fourthLevelSamples 3 + 3168000*fourthLevelSamples 4 + 1288000*fourthLevelSamples 5 - 1608000*fourthLevelSamples 6 - 192000*fourthLevelSamples 7 + 956000*fourthLevelSamples 8 - 2356000*fourthLevelSamples 10 + 4000000*fourthLevelSamples 11 - 3168000*fourthLevelSamples 12 + 1356000*fourthLevelSamples 13 - 374000*fourthLevelSamples 14 + 96000*fourthLevelSamples 15 - 16000*fourthLevelSamples 16) / 1000000 - (19000) / 1000000000000000 ∧ (96000*fourthLevelSamples 1 + 4338000*fourthLevelSamples 2 - 6644000*fourthLevelSamples 3 + 3168000*fourthLevelSamples 4 + 1288000*fourthLevelSamples 5 - 1608000*fourthLevelSamples 6 - 192000*fourthLevelSamples 7 + 956000*fourthLevelSamples 8 - 2356000*fourthLevelSamples 10 + 4000000*fourthLevelSamples 11 - 3168000*fourthLevelSamples 12 + 1356000*fourthLevelSamples 13 - 374000*fourthLevelSamples 14 + 96000*fourthLevelSamples 15 - 16000*fourthLevelSamples 16) / 1000000 - (19000) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_6_1 :
    (2249943/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 6 1 ∧
      fourthLevelOddSheared fourthLevelSamples 6 1 ≤ (2249944/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (- 10640000*fourthLevelSamples 1 - 710500*fourthLevelSamples 2 + 10825000*fourthLevelSamples 3 - 12112000*fourthLevelSamples 4 + 6390000*fourthLevelSamples 5 + 2010000*fourthLevelSamples 6 - 7760000*fourthLevelSamples 7 + 6989000*fourthLevelSamples 8 - 2712000*fourthLevelSamples 9 - 1019000*fourthLevelSamples 10 + 2808000*fourthLevelSamples 11 - 2344000*fourthLevelSamples 12 + 1017000*fourthLevelSamples 13 - 280500*fourthLevelSamples 14 + 72000*fourthLevelSamples 15 - 12000*fourthLevelSamples 16) / 1000000 - (-250750) / 1000000000000000 ∧ (- 10640000*fourthLevelSamples 1 - 710500*fourthLevelSamples 2 + 10825000*fourthLevelSamples 3 - 12112000*fourthLevelSamples 4 + 6390000*fourthLevelSamples 5 + 2010000*fourthLevelSamples 6 - 7760000*fourthLevelSamples 7 + 6989000*fourthLevelSamples 8 - 2712000*fourthLevelSamples 9 - 1019000*fourthLevelSamples 10 + 2808000*fourthLevelSamples 11 - 2344000*fourthLevelSamples 12 + 1017000*fourthLevelSamples 13 - 280500*fourthLevelSamples 14 + 72000*fourthLevelSamples 15 - 12000*fourthLevelSamples 16) / 1000000 - (-250750) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_6_2 :
    (-551390/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 6 2 ∧
      fourthLevelOddSheared fourthLevelSamples 6 2 ≤ (-551389/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (4838312*fourthLevelSamples 1 + 3539306*fourthLevelSamples 2 - 9063068*fourthLevelSamples 3 + 5145576*fourthLevelSamples 4 + 2662536*fourthLevelSamples 5 - 7037576*fourthLevelSamples 6 + 5662976*fourthLevelSamples 7 + 992372*fourthLevelSamples 8 - 6060920*fourthLevelSamples 9 + 3758528*fourthLevelSamples 10 + 893280*fourthLevelSamples 11 - 2021536*fourthLevelSamples 12 + 983652*fourthLevelSamples 13 - 292258*fourthLevelSamples 14 + 83232*fourthLevelSamples 15 - 13872*fourthLevelSamples 16) / 1000000 - (230448) / 1000000000000000 ∧ (4838312*fourthLevelSamples 1 + 3539306*fourthLevelSamples 2 - 9063068*fourthLevelSamples 3 + 5145576*fourthLevelSamples 4 + 2662536*fourthLevelSamples 5 - 7037576*fourthLevelSamples 6 + 5662976*fourthLevelSamples 7 + 992372*fourthLevelSamples 8 - 6060920*fourthLevelSamples 9 + 3758528*fourthLevelSamples 10 + 893280*fourthLevelSamples 11 - 2021536*fourthLevelSamples 12 + 983652*fourthLevelSamples 13 - 292258*fourthLevelSamples 14 + 83232*fourthLevelSamples 15 - 13872*fourthLevelSamples 16) / 1000000 - (230448) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_6_3 :
    (190902/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 6 3 ∧
      fourthLevelOddSheared fourthLevelSamples 6 3 ≤ (190903/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (- 1948404*fourthLevelSamples 1 - 2804090*fourthLevelSamples 2 + 4693480*fourthLevelSamples 3 + 262284*fourthLevelSamples 4 - 4764456*fourthLevelSamples 5 + 1903336*fourthLevelSamples 6 + 2542304*fourthLevelSamples 7 - 2061840*fourthLevelSamples 8 - 412796*fourthLevelSamples 9 + 885494*fourthLevelSamples 10 - 188728*fourthLevelSamples 11 - 112324*fourthLevelSamples 12 + 70344*fourthLevelSamples 13 - 24452*fourthLevelSamples 14 + 8256*fourthLevelSamples 15 - 1376*fourthLevelSamples 16) / 1000000 - (-136144) / 1000000000000000 ∧ (- 1948404*fourthLevelSamples 1 - 2804090*fourthLevelSamples 2 + 4693480*fourthLevelSamples 3 + 262284*fourthLevelSamples 4 - 4764456*fourthLevelSamples 5 + 1903336*fourthLevelSamples 6 + 2542304*fourthLevelSamples 7 - 2061840*fourthLevelSamples 8 - 412796*fourthLevelSamples 9 + 885494*fourthLevelSamples 10 - 188728*fourthLevelSamples 11 - 112324*fourthLevelSamples 12 + 70344*fourthLevelSamples 13 - 24452*fourthLevelSamples 14 + 8256*fourthLevelSamples 15 - 1376*fourthLevelSamples 16) / 1000000 - (-136144) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_6_4 :
    (-61226/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 6 4 ∧
      fourthLevelOddSheared fourthLevelSamples 6 4 ≤ (-61225/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (1580368*fourthLevelSamples 1 - 6739292*fourthLevelSamples 2 + 13007128*fourthLevelSamples 3 - 14359424*fourthLevelSamples 4 + 8380784*fourthLevelSamples 5 - 215120*fourthLevelSamples 6 - 2980896*fourthLevelSamples 7 - 1573608*fourthLevelSamples 8 + 9913376*fourthLevelSamples 9 - 14316344*fourthLevelSamples 10 + 11577872*fourthLevelSamples 11 - 5899560*fourthLevelSamples 12 + 2024536*fourthLevelSamples 13 - 529372*fourthLevelSamples 14 + 112832*fourthLevelSamples 15 - 13472*fourthLevelSamples 16) / 1000000 - (12371) / 1000000000000000 ∧ (1580368*fourthLevelSamples 1 - 6739292*fourthLevelSamples 2 + 13007128*fourthLevelSamples 3 - 14359424*fourthLevelSamples 4 + 8380784*fourthLevelSamples 5 - 215120*fourthLevelSamples 6 - 2980896*fourthLevelSamples 7 - 1573608*fourthLevelSamples 8 + 9913376*fourthLevelSamples 9 - 14316344*fourthLevelSamples 10 + 11577872*fourthLevelSamples 11 - 5899560*fourthLevelSamples 12 + 2024536*fourthLevelSamples 13 - 529372*fourthLevelSamples 14 + 112832*fourthLevelSamples 15 - 13472*fourthLevelSamples 16) / 1000000 - (12371) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_6_5 :
    (44527/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 6 5 ∧
      fourthLevelOddSheared fourthLevelSamples 6 5 ≤ (44528/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (14672928*fourthLevelSamples 1 - 16988416*fourthLevelSamples 2 + 13595296*fourthLevelSamples 3 - 5394536*fourthLevelSamples 4 - 730400*fourthLevelSamples 5 - 682784*fourthLevelSamples 6 + 8272560*fourthLevelSamples 7 - 15118792*fourthLevelSamples 8 + 15740176*fourthLevelSamples 9 - 11029248*fourthLevelSamples 10 + 5510600*fourthLevelSamples 11 - 2035652*fourthLevelSamples 12 + 578136*fourthLevelSamples 13 - 129280*fourthLevelSamples 14 + 21056*fourthLevelSamples 15 - 1792*fourthLevelSamples 16) / 1000000 - (663483) / 1000000000000000 ∧ (14672928*fourthLevelSamples 1 - 16988416*fourthLevelSamples 2 + 13595296*fourthLevelSamples 3 - 5394536*fourthLevelSamples 4 - 730400*fourthLevelSamples 5 - 682784*fourthLevelSamples 6 + 8272560*fourthLevelSamples 7 - 15118792*fourthLevelSamples 8 + 15740176*fourthLevelSamples 9 - 11029248*fourthLevelSamples 10 + 5510600*fourthLevelSamples 11 - 2035652*fourthLevelSamples 12 + 578136*fourthLevelSamples 13 - 129280*fourthLevelSamples 14 + 21056*fourthLevelSamples 15 - 1792*fourthLevelSamples 16) / 1000000 - (663483) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_6_6 :
    (117737745/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 6 6 ∧
      fourthLevelOddSheared fourthLevelSamples 6 6 ≤ (117737746/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (26936392*fourthLevelSamples 1 - 12031856*fourthLevelSamples 2 + 1320560*fourthLevelSamples 3 - 1163968*fourthLevelSamples 4 + 8461232*fourthLevelSamples 5 - 15155928*fourthLevelSamples 6 + 15778032*fourthLevelSamples 7 - 11308472*fourthLevelSamples 8 + 6017984*fourthLevelSamples 9 - 2525896*fourthLevelSamples 10 + 875272*fourthLevelSamples 11 - 250802*fourthLevelSamples 12 + 57600*fourthLevelSamples 13 - 10592*fourthLevelSamples 14 + 1536*fourthLevelSamples 15 - 128*fourthLevelSamples 16) / 1000000 - (2292943) / 1000000000000000 ∧ (26936392*fourthLevelSamples 1 - 12031856*fourthLevelSamples 2 + 1320560*fourthLevelSamples 3 - 1163968*fourthLevelSamples 4 + 8461232*fourthLevelSamples 5 - 15155928*fourthLevelSamples 6 + 15778032*fourthLevelSamples 7 - 11308472*fourthLevelSamples 8 + 6017984*fourthLevelSamples 9 - 2525896*fourthLevelSamples 10 + 875272*fourthLevelSamples 11 - 250802*fourthLevelSamples 12 + 57600*fourthLevelSamples 13 - 10592*fourthLevelSamples 14 + 1536*fourthLevelSamples 15 - 128*fourthLevelSamples 16) / 1000000 - (2292943) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]

theorem fourthLevelOddSheared_bounds_6_7 :
    (17143/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 6 7 ∧
      fourthLevelOddSheared fourthLevelSamples 6 7 ≤ (17144/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (11725772*fourthLevelSamples 1 - 17499554*fourthLevelSamples 2 + 21738808*fourthLevelSamples 3 - 21334202*fourthLevelSamples 4 + 16561816*fourthLevelSamples 5 - 10193716*fourthLevelSamples 6 + 5024484*fourthLevelSamples 7 - 2044338*fourthLevelSamples 8 + 716896*fourthLevelSamples 9 - 220602*fourthLevelSamples 10 + 58228*fourthLevelSamples 11 - 12954*fourthLevelSamples 12 + 2444*fourthLevelSamples 13 - 368*fourthLevelSamples 14 + 32*fourthLevelSamples 15) / 1000000 - (515244) / 1000000000000000 ∧ (11725772*fourthLevelSamples 1 - 17499554*fourthLevelSamples 2 + 21738808*fourthLevelSamples 3 - 21334202*fourthLevelSamples 4 + 16561816*fourthLevelSamples 5 - 10193716*fourthLevelSamples 6 + 5024484*fourthLevelSamples 7 - 2044338*fourthLevelSamples 8 + 716896*fourthLevelSamples 9 - 220602*fourthLevelSamples 10 + 58228*fourthLevelSamples 11 - 12954*fourthLevelSamples 12 + 2444*fourthLevelSamples 13 - 368*fourthLevelSamples 14 + 32*fourthLevelSamples 15) / 1000000 - (515244) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2]

theorem fourthLevelOddSheared_bounds_7_0 :
    (-2031579/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 7 0 ∧
      fourthLevelOddSheared fourthLevelSamples 7 0 ≤ (-2031578/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (- 7996000*fourthLevelSamples 1 + 5054000*fourthLevelSamples 2 - 1992000*fourthLevelSamples 3 + 286000*fourthLevelSamples 4 + 876000*fourthLevelSamples 5 - 2494000*fourthLevelSamples 6 + 3992000*fourthLevelSamples 7 - 4548000*fourthLevelSamples 8 + 4000000*fourthLevelSamples 9 - 2538000*fourthLevelSamples 10 + 1036000*fourthLevelSamples 11 - 286000*fourthLevelSamples 12 + 80000*fourthLevelSamples 13 - 22000*fourthLevelSamples 14 + 4000*fourthLevelSamples 15) / 1000000 - (-74000) / 1000000000000000 ∧ (- 7996000*fourthLevelSamples 1 + 5054000*fourthLevelSamples 2 - 1992000*fourthLevelSamples 3 + 286000*fourthLevelSamples 4 + 876000*fourthLevelSamples 5 - 2494000*fourthLevelSamples 6 + 3992000*fourthLevelSamples 7 - 4548000*fourthLevelSamples 8 + 4000000*fourthLevelSamples 9 - 2538000*fourthLevelSamples 10 + 1036000*fourthLevelSamples 11 - 286000*fourthLevelSamples 12 + 80000*fourthLevelSamples 13 - 22000*fourthLevelSamples 14 + 4000*fourthLevelSamples 15) / 1000000 - (-74000) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2]

theorem fourthLevelOddSheared_bounds_7_1 :
    (1571591/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 7 1 ∧
      fourthLevelOddSheared fourthLevelSamples 7 1 ≤ (1571592/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (7771000*fourthLevelSamples 1 - 1241500*fourthLevelSamples 2 - 5358000*fourthLevelSamples 3 + 8166500*fourthLevelSamples 4 - 7023000*fourthLevelSamples 5 + 3117500*fourthLevelSamples 6 + 938000*fourthLevelSamples 7 - 2839000*fourthLevelSamples 8 + 2840000*fourthLevelSamples 9 - 1859500*fourthLevelSamples 10 + 769000*fourthLevelSamples 11 - 214500*fourthLevelSamples 12 + 60000*fourthLevelSamples 13 - 16500*fourthLevelSamples 14 + 3000*fourthLevelSamples 15) / 1000000 - (154500) / 1000000000000000 ∧ (7771000*fourthLevelSamples 1 - 1241500*fourthLevelSamples 2 - 5358000*fourthLevelSamples 3 + 8166500*fourthLevelSamples 4 - 7023000*fourthLevelSamples 5 + 3117500*fourthLevelSamples 6 + 938000*fourthLevelSamples 7 - 2839000*fourthLevelSamples 8 + 2840000*fourthLevelSamples 9 - 1859500*fourthLevelSamples 10 + 769000*fourthLevelSamples 11 - 214500*fourthLevelSamples 12 + 60000*fourthLevelSamples 13 - 16500*fourthLevelSamples 14 + 3000*fourthLevelSamples 15) / 1000000 - (154500) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2]

theorem fourthLevelOddSheared_bounds_7_2 :
    (-500781/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 7 2 ∧
      fourthLevelOddSheared fourthLevelSamples 7 2 ≤ (-500780/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (- 944652*fourthLevelSamples 1 - 1600302*fourthLevelSamples 2 + 3107696*fourthLevelSamples 3 - 1505718*fourthLevelSamples 4 - 1429308*fourthLevelSamples 5 + 3279282*fourthLevelSamples 6 - 3052896*fourthLevelSamples 7 + 723904*fourthLevelSamples 8 + 1510400*fourthLevelSamples 9 - 1659906*fourthLevelSamples 10 + 743932*fourthLevelSamples 11 - 203962*fourthLevelSamples 12 + 61360*fourthLevelSamples 13 - 19074*fourthLevelSamples 14 + 3468*fourthLevelSamples 15) / 1000000 - (-25308) / 1000000000000000 ∧ (- 944652*fourthLevelSamples 1 - 1600302*fourthLevelSamples 2 + 3107696*fourthLevelSamples 3 - 1505718*fourthLevelSamples 4 - 1429308*fourthLevelSamples 5 + 3279282*fourthLevelSamples 6 - 3052896*fourthLevelSamples 7 + 723904*fourthLevelSamples 8 + 1510400*fourthLevelSamples 9 - 1659906*fourthLevelSamples 10 + 743932*fourthLevelSamples 11 - 203962*fourthLevelSamples 12 + 61360*fourthLevelSamples 13 - 19074*fourthLevelSamples 14 + 3468*fourthLevelSamples 15) / 1000000 - (-25308) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2]

theorem fourthLevelOddSheared_bounds_7_3 :
    (173555/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 7 3 ∧
      fourthLevelOddSheared fourthLevelSamples 7 3 ≤ (173556/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (388900*fourthLevelSamples 1 + 809508*fourthLevelSamples 2 - 1255572*fourthLevelSamples 3 - 57576*fourthLevelSamples 4 + 1299016*fourthLevelSamples 5 - 699502*fourthLevelSamples 6 - 430580*fourthLevelSamples 7 + 516114*fourthLevelSamples 8 - 62632*fourthLevelSamples 9 - 108114*fourthLevelSamples 10 + 55572*fourthLevelSamples 11 - 13992*fourthLevelSamples 12 + 4952*fourthLevelSamples 13 - 1892*fourthLevelSamples 14 + 344*fourthLevelSamples 15) / 1000000 - (1990) / 1000000000000000 ∧ (388900*fourthLevelSamples 1 + 809508*fourthLevelSamples 2 - 1255572*fourthLevelSamples 3 - 57576*fourthLevelSamples 4 + 1299016*fourthLevelSamples 5 - 699502*fourthLevelSamples 6 - 430580*fourthLevelSamples 7 + 516114*fourthLevelSamples 8 - 62632*fourthLevelSamples 9 - 108114*fourthLevelSamples 10 + 55572*fourthLevelSamples 11 - 13992*fourthLevelSamples 12 + 4952*fourthLevelSamples 13 - 1892*fourthLevelSamples 14 + 344*fourthLevelSamples 15) / 1000000 - (1990) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2]

theorem fourthLevelOddSheared_bounds_7_4 :
    (-86391/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 7 4 ∧
      fourthLevelOddSheared fourthLevelSamples 7 4 ≤ (-86390/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (84280*fourthLevelSamples 1 - 95068*fourthLevelSamples 2 + 1158112*fourthLevelSamples 3 - 4669884*fourthLevelSamples 4 + 10404312*fourthLevelSamples 5 - 15754732*fourthLevelSamples 6 + 17763632*fourthLevelSamples 7 - 15305472*fourthLevelSamples 8 + 9873936*fourthLevelSamples 9 - 4603676*fourthLevelSamples 10 + 1555384*fourthLevelSamples 11 - 431700*fourthLevelSamples 12 + 116976*fourthLevelSamples 13 - 26524*fourthLevelSamples 14 + 3368*fourthLevelSamples 15) / 1000000 - (4094) / 1000000000000000 ∧ (84280*fourthLevelSamples 1 - 95068*fourthLevelSamples 2 + 1158112*fourthLevelSamples 3 - 4669884*fourthLevelSamples 4 + 10404312*fourthLevelSamples 5 - 15754732*fourthLevelSamples 6 + 17763632*fourthLevelSamples 7 - 15305472*fourthLevelSamples 8 + 9873936*fourthLevelSamples 9 - 4603676*fourthLevelSamples 10 + 1555384*fourthLevelSamples 11 - 431700*fourthLevelSamples 12 + 116976*fourthLevelSamples 13 - 26524*fourthLevelSamples 14 + 3368*fourthLevelSamples 15) / 1000000 - (4094) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2]

theorem fourthLevelOddSheared_bounds_7_5 :
    (3247/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 7 5 ∧
      fourthLevelOddSheared fourthLevelSamples 7 5 ≤ (3248/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (1261840*fourthLevelSamples 1 - 4574092*fourthLevelSamples 2 + 10525776*fourthLevelSamples 3 - 17249284*fourthLevelSamples 4 + 21470504*fourthLevelSamples 5 - 20902320*fourthLevelSamples 6 + 15985888*fourthLevelSamples 7 - 9527964*fourthLevelSamples 8 + 4398608*fourthLevelSamples 9 - 1593108*fourthLevelSamples 10 + 476536*fourthLevelSamples 11 - 126708*fourthLevelSamples 12 + 29520*fourthLevelSamples 13 - 5040*fourthLevelSamples 14 + 448*fourthLevelSamples 15) / 1000000 - (29282) / 1000000000000000 ∧ (1261840*fourthLevelSamples 1 - 4574092*fourthLevelSamples 2 + 10525776*fourthLevelSamples 3 - 17249284*fourthLevelSamples 4 + 21470504*fourthLevelSamples 5 - 20902320*fourthLevelSamples 6 + 15985888*fourthLevelSamples 7 - 9527964*fourthLevelSamples 8 + 4398608*fourthLevelSamples 9 - 1593108*fourthLevelSamples 10 + 476536*fourthLevelSamples 11 - 126708*fourthLevelSamples 12 + 29520*fourthLevelSamples 13 - 5040*fourthLevelSamples 14 + 448*fourthLevelSamples 15) / 1000000 - (29282) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2]

theorem fourthLevelOddSheared_bounds_7_6 :
    (17143/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 7 6 ∧
      fourthLevelOddSheared fourthLevelSamples 7 6 ≤ (17144/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (11725772*fourthLevelSamples 1 - 17499554*fourthLevelSamples 2 + 21738808*fourthLevelSamples 3 - 21334202*fourthLevelSamples 4 + 16561816*fourthLevelSamples 5 - 10193716*fourthLevelSamples 6 + 5024484*fourthLevelSamples 7 - 2044338*fourthLevelSamples 8 + 716896*fourthLevelSamples 9 - 220602*fourthLevelSamples 10 + 58228*fourthLevelSamples 11 - 12954*fourthLevelSamples 12 + 2444*fourthLevelSamples 13 - 368*fourthLevelSamples 14 + 32*fourthLevelSamples 15) / 1000000 - (515244) / 1000000000000000 ∧ (11725772*fourthLevelSamples 1 - 17499554*fourthLevelSamples 2 + 21738808*fourthLevelSamples 3 - 21334202*fourthLevelSamples 4 + 16561816*fourthLevelSamples 5 - 10193716*fourthLevelSamples 6 + 5024484*fourthLevelSamples 7 - 2044338*fourthLevelSamples 8 + 716896*fourthLevelSamples 9 - 220602*fourthLevelSamples 10 + 58228*fourthLevelSamples 11 - 12954*fourthLevelSamples 12 + 2444*fourthLevelSamples 13 - 368*fourthLevelSamples 14 + 32*fourthLevelSamples 15) / 1000000 - (515244) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2]

theorem fourthLevelOddSheared_bounds_7_7 :
    (81735296/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples 7 7 ∧
      fourthLevelOddSheared fourthLevelSamples 7 7 ≤ (81735297/1000000000000000 : ℝ) := by
  rw [fourthLevelOddSheared_apply]
  change _ ≤ (31294392*fourthLevelSamples 1 - 24502184*fourthLevelSamples 2 + 16234704*fourthLevelSamples 3 - 9045430*fourthLevelSamples 4 + 4235360*fourthLevelSamples 5 - 1698572*fourthLevelSamples 6 + 605528*fourthLevelSamples 7 - 195614*fourthLevelSamples 8 + 55824*fourthLevelSamples 9 - 13636*fourthLevelSamples 10 + 2904*fourthLevelSamples 11 - 562*fourthLevelSamples 12 + 88*fourthLevelSamples 13 - 8*fourthLevelSamples 14) / 1000000 - (2149788) / 1000000000000000 ∧ (31294392*fourthLevelSamples 1 - 24502184*fourthLevelSamples 2 + 16234704*fourthLevelSamples 3 - 9045430*fourthLevelSamples 4 + 4235360*fourthLevelSamples 5 - 1698572*fourthLevelSamples 6 + 605528*fourthLevelSamples 7 - 195614*fourthLevelSamples 8 + 55824*fourthLevelSamples 9 - 13636*fourthLevelSamples 10 + 2904*fourthLevelSamples 11 - 562*fourthLevelSamples 12 + 88*fourthLevelSamples 13 - 8*fourthLevelSamples 14) / 1000000 - (2149788) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1]

def fourthLevelOddLower : Matrix (Fin 8) (Fin 8) ℝ :=
  ![![30453883906,-10787574,2727010,-2910795,175218,-12553761,-7176680,-2031579],
  ![-10787574,6302577996,-2742984,-1742475,906415,-1467056,2249943,1571591],
  ![2727010,-2742984,1286281916,507146,-580301,-258988,-551390,-500781],
  ![-2910795,-1742475,507146,667841601,145746,-293211,190902,173555],
  ![175218,906415,-580301,145746,172104152,56364,-61226,-86391],
  ![-12553761,-1467056,-258988,-293211,56364,120457812,44527,3247],
  ![-7176680,2249943,-551390,190902,-61226,44527,117737745,17143],
  ![-2031579,1571591,-500781,173555,-86391,3247,17143,81735296]]

def fourthLevelOddUpper : Matrix (Fin 8) (Fin 8) ℝ :=
  ![![30453883907,-10787573,2727011,-2910794,175220,-12553760,-7176679,-2031578],
  ![-10787573,6302577997,-2742983,-1742474,906416,-1467055,2249944,1571592],
  ![2727011,-2742983,1286281917,507147,-580300,-258987,-551389,-500780],
  ![-2910794,-1742474,507147,667841602,145747,-293210,190903,173556],
  ![175220,906416,-580300,145747,172104153,56365,-61225,-86390],
  ![-12553760,-1467055,-258987,-293210,56365,120457813,44528,3248],
  ![-7176679,2249944,-551389,190903,-61225,44528,117737746,17144],
  ![-2031578,1571592,-500780,173556,-86390,3248,17144,81735297]]

theorem fourthLevelOddSheared_bounds_row0 (j : Fin 8) :
    fourthLevelOddLower 0 j / 1000000000000000 ≤ fourthLevelOddSheared fourthLevelSamples 0 j ∧
      fourthLevelOddSheared fourthLevelSamples 0 j ≤ fourthLevelOddUpper 0 j / 1000000000000000 := by
  fin_cases j
  · exact fourthLevelOddSheared_bounds_0_0
  · exact fourthLevelOddSheared_bounds_0_1
  · exact fourthLevelOddSheared_bounds_0_2
  · exact fourthLevelOddSheared_bounds_0_3
  · exact fourthLevelOddSheared_bounds_0_4
  · exact fourthLevelOddSheared_bounds_0_5
  · exact fourthLevelOddSheared_bounds_0_6
  · exact fourthLevelOddSheared_bounds_0_7

theorem fourthLevelOddSheared_bounds_row1 (j : Fin 8) :
    fourthLevelOddLower 1 j / 1000000000000000 ≤ fourthLevelOddSheared fourthLevelSamples 1 j ∧
      fourthLevelOddSheared fourthLevelSamples 1 j ≤ fourthLevelOddUpper 1 j / 1000000000000000 := by
  fin_cases j
  · exact fourthLevelOddSheared_bounds_1_0
  · exact fourthLevelOddSheared_bounds_1_1
  · exact fourthLevelOddSheared_bounds_1_2
  · exact fourthLevelOddSheared_bounds_1_3
  · exact fourthLevelOddSheared_bounds_1_4
  · exact fourthLevelOddSheared_bounds_1_5
  · exact fourthLevelOddSheared_bounds_1_6
  · exact fourthLevelOddSheared_bounds_1_7

theorem fourthLevelOddSheared_bounds_row2 (j : Fin 8) :
    fourthLevelOddLower 2 j / 1000000000000000 ≤ fourthLevelOddSheared fourthLevelSamples 2 j ∧
      fourthLevelOddSheared fourthLevelSamples 2 j ≤ fourthLevelOddUpper 2 j / 1000000000000000 := by
  fin_cases j
  · exact fourthLevelOddSheared_bounds_2_0
  · exact fourthLevelOddSheared_bounds_2_1
  · exact fourthLevelOddSheared_bounds_2_2
  · exact fourthLevelOddSheared_bounds_2_3
  · exact fourthLevelOddSheared_bounds_2_4
  · exact fourthLevelOddSheared_bounds_2_5
  · exact fourthLevelOddSheared_bounds_2_6
  · exact fourthLevelOddSheared_bounds_2_7

theorem fourthLevelOddSheared_bounds_row3 (j : Fin 8) :
    fourthLevelOddLower 3 j / 1000000000000000 ≤ fourthLevelOddSheared fourthLevelSamples 3 j ∧
      fourthLevelOddSheared fourthLevelSamples 3 j ≤ fourthLevelOddUpper 3 j / 1000000000000000 := by
  fin_cases j
  · exact fourthLevelOddSheared_bounds_3_0
  · exact fourthLevelOddSheared_bounds_3_1
  · exact fourthLevelOddSheared_bounds_3_2
  · exact fourthLevelOddSheared_bounds_3_3
  · exact fourthLevelOddSheared_bounds_3_4
  · exact fourthLevelOddSheared_bounds_3_5
  · exact fourthLevelOddSheared_bounds_3_6
  · exact fourthLevelOddSheared_bounds_3_7

theorem fourthLevelOddSheared_bounds_row4 (j : Fin 8) :
    fourthLevelOddLower 4 j / 1000000000000000 ≤ fourthLevelOddSheared fourthLevelSamples 4 j ∧
      fourthLevelOddSheared fourthLevelSamples 4 j ≤ fourthLevelOddUpper 4 j / 1000000000000000 := by
  fin_cases j
  · exact fourthLevelOddSheared_bounds_4_0
  · exact fourthLevelOddSheared_bounds_4_1
  · exact fourthLevelOddSheared_bounds_4_2
  · exact fourthLevelOddSheared_bounds_4_3
  · exact fourthLevelOddSheared_bounds_4_4
  · exact fourthLevelOddSheared_bounds_4_5
  · exact fourthLevelOddSheared_bounds_4_6
  · exact fourthLevelOddSheared_bounds_4_7

theorem fourthLevelOddSheared_bounds_row5 (j : Fin 8) :
    fourthLevelOddLower 5 j / 1000000000000000 ≤ fourthLevelOddSheared fourthLevelSamples 5 j ∧
      fourthLevelOddSheared fourthLevelSamples 5 j ≤ fourthLevelOddUpper 5 j / 1000000000000000 := by
  fin_cases j
  · exact fourthLevelOddSheared_bounds_5_0
  · exact fourthLevelOddSheared_bounds_5_1
  · exact fourthLevelOddSheared_bounds_5_2
  · exact fourthLevelOddSheared_bounds_5_3
  · exact fourthLevelOddSheared_bounds_5_4
  · exact fourthLevelOddSheared_bounds_5_5
  · exact fourthLevelOddSheared_bounds_5_6
  · exact fourthLevelOddSheared_bounds_5_7

theorem fourthLevelOddSheared_bounds_row6 (j : Fin 8) :
    fourthLevelOddLower 6 j / 1000000000000000 ≤ fourthLevelOddSheared fourthLevelSamples 6 j ∧
      fourthLevelOddSheared fourthLevelSamples 6 j ≤ fourthLevelOddUpper 6 j / 1000000000000000 := by
  fin_cases j
  · exact fourthLevelOddSheared_bounds_6_0
  · exact fourthLevelOddSheared_bounds_6_1
  · exact fourthLevelOddSheared_bounds_6_2
  · exact fourthLevelOddSheared_bounds_6_3
  · exact fourthLevelOddSheared_bounds_6_4
  · exact fourthLevelOddSheared_bounds_6_5
  · exact fourthLevelOddSheared_bounds_6_6
  · exact fourthLevelOddSheared_bounds_6_7

theorem fourthLevelOddSheared_bounds_row7 (j : Fin 8) :
    fourthLevelOddLower 7 j / 1000000000000000 ≤ fourthLevelOddSheared fourthLevelSamples 7 j ∧
      fourthLevelOddSheared fourthLevelSamples 7 j ≤ fourthLevelOddUpper 7 j / 1000000000000000 := by
  fin_cases j
  · exact fourthLevelOddSheared_bounds_7_0
  · exact fourthLevelOddSheared_bounds_7_1
  · exact fourthLevelOddSheared_bounds_7_2
  · exact fourthLevelOddSheared_bounds_7_3
  · exact fourthLevelOddSheared_bounds_7_4
  · exact fourthLevelOddSheared_bounds_7_5
  · exact fourthLevelOddSheared_bounds_7_6
  · exact fourthLevelOddSheared_bounds_7_7

theorem fourthLevelOddSheared_bounds (i j : Fin 8) :
    fourthLevelOddLower i j / 1000000000000000 ≤ fourthLevelOddSheared fourthLevelSamples i j ∧
      fourthLevelOddSheared fourthLevelSamples i j ≤ fourthLevelOddUpper i j / 1000000000000000 := by
  fin_cases i
  · exact fourthLevelOddSheared_bounds_row0 j
  · exact fourthLevelOddSheared_bounds_row1 j
  · exact fourthLevelOddSheared_bounds_row2 j
  · exact fourthLevelOddSheared_bounds_row3 j
  · exact fourthLevelOddSheared_bounds_row4 j
  · exact fourthLevelOddSheared_bounds_row5 j
  · exact fourthLevelOddSheared_bounds_row6 j
  · exact fourthLevelOddSheared_bounds_row7 j

theorem fourthLevelEvenSheared_bounds_0_0 :
    (15247517099/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 0 0 ∧
      fourthLevelEvenSheared fourthLevelSamples 0 0 ≤ (15247517100/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (8000000*fourthLevelSamples 4 + 8000000*fourthLevelSamples 8 - 8000000*fourthLevelSamples 12 + 2000000*fourthLevelSamples 16) / 1000000 - (2000000) / 1000000000000000 ∧ (8000000*fourthLevelSamples 4 + 8000000*fourthLevelSamples 8 - 8000000*fourthLevelSamples 12 + 2000000*fourthLevelSamples 16) / 1000000 - (2000000) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_4_bounds).1, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_4_bounds).2, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_0_1 :
    (5910960/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 0 1 ∧
      fourthLevelEvenSheared fourthLevelSamples 0 1 ≤ (5910961/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (- 4000000*fourthLevelSamples 2 + 600000*fourthLevelSamples 4 - 5400000*fourthLevelSamples 8 + 8000000*fourthLevelSamples 10 - 600000*fourthLevelSamples 12 - 4000000*fourthLevelSamples 14 + 1650000*fourthLevelSamples 16) / 1000000 - (-350000) / 1000000000000000 ∧ (- 4000000*fourthLevelSamples 2 + 600000*fourthLevelSamples 4 - 5400000*fourthLevelSamples 8 + 8000000*fourthLevelSamples 10 - 600000*fourthLevelSamples 12 - 4000000*fourthLevelSamples 14 + 1650000*fourthLevelSamples 16) / 1000000 - (-350000) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_2_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_2_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_0_2 :
    (1223509/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 0 2 ∧
      fourthLevelEvenSheared fourthLevelSamples 0 2 ≤ (1223510/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (- 9564000*fourthLevelSamples 2 - 3290000*fourthLevelSamples 4 + 12000000*fourthLevelSamples 6 - 7636000*fourthLevelSamples 8 - 872000*fourthLevelSamples 10 + 3290000*fourthLevelSamples 12 - 1564000*fourthLevelSamples 14 + 264000*fourthLevelSamples 16) / 1000000 - (-518000) / 1000000000000000 ∧ (- 9564000*fourthLevelSamples 2 - 3290000*fourthLevelSamples 4 + 12000000*fourthLevelSamples 6 - 7636000*fourthLevelSamples 8 - 872000*fourthLevelSamples 10 + 3290000*fourthLevelSamples 12 - 1564000*fourthLevelSamples 14 + 264000*fourthLevelSamples 16) / 1000000 - (-518000) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_2_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_2_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_0_3 :
    (-8303104/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 0 3 ∧
      fourthLevelEvenSheared fourthLevelSamples 0 3 ≤ (-8303103/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (4000000*fourthLevelSamples 1 + 3208000*fourthLevelSamples 2 - 8000000*fourthLevelSamples 3 + 3860000*fourthLevelSamples 4 - 480000*fourthLevelSamples 6 + 1272000*fourthLevelSamples 8 - 5616000*fourthLevelSamples 10 + 8000000*fourthLevelSamples 11 - 3860000*fourthLevelSamples 12 + 2888000*fourthLevelSamples 14 - 4000000*fourthLevelSamples 15 + 1612000*fourthLevelSamples 16) / 1000000 - (56000) / 1000000000000000 ∧ (4000000*fourthLevelSamples 1 + 3208000*fourthLevelSamples 2 - 8000000*fourthLevelSamples 3 + 3860000*fourthLevelSamples 4 - 480000*fourthLevelSamples 6 + 1272000*fourthLevelSamples 8 - 5616000*fourthLevelSamples 10 + 8000000*fourthLevelSamples 11 - 3860000*fourthLevelSamples 12 + 2888000*fourthLevelSamples 14 - 4000000*fourthLevelSamples 15 + 1612000*fourthLevelSamples 16) / 1000000 - (56000) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_0_4 :
    (-5678535/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 0 4 ∧
      fourthLevelEvenSheared fourthLevelSamples 0 4 ≤ (-5678534/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (- 6720000*fourthLevelSamples 1 + 2336000*fourthLevelSamples 2 + 1440000*fourthLevelSamples 3 - 1792000*fourthLevelSamples 4 + 1296000*fourthLevelSamples 6 - 4448000*fourthLevelSamples 8 + 8000000*fourthLevelSamples 9 - 6832000*fourthLevelSamples 10 + 2560000*fourthLevelSamples 11 + 1792000*fourthLevelSamples 12 - 4000000*fourthLevelSamples 13 + 3200000*fourthLevelSamples 14 - 1280000*fourthLevelSamples 15 + 216000*fourthLevelSamples 16) / 1000000 - (-144000) / 1000000000000000 ∧ (- 6720000*fourthLevelSamples 1 + 2336000*fourthLevelSamples 2 + 1440000*fourthLevelSamples 3 - 1792000*fourthLevelSamples 4 + 1296000*fourthLevelSamples 6 - 4448000*fourthLevelSamples 8 + 8000000*fourthLevelSamples 9 - 6832000*fourthLevelSamples 10 + 2560000*fourthLevelSamples 11 + 1792000*fourthLevelSamples 12 - 4000000*fourthLevelSamples 13 + 3200000*fourthLevelSamples 14 - 1280000*fourthLevelSamples 15 + 216000*fourthLevelSamples 16) / 1000000 - (-144000) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_0_5 :
    (-4538860/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 0 5 ∧
      fourthLevelEvenSheared fourthLevelSamples 0 5 ≤ (-4538859/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (- 10708000*fourthLevelSamples 1 + 4596000*fourthLevelSamples 2 + 1204000*fourthLevelSamples 3 - 3232000*fourthLevelSamples 4 + 4000000*fourthLevelSamples 5 - 6312000*fourthLevelSamples 6 + 8000000*fourthLevelSamples 7 - 6528000*fourthLevelSamples 8 + 2808000*fourthLevelSamples 9 + 1328000*fourthLevelSamples 10 - 3800000*fourthLevelSamples 11 + 3232000*fourthLevelSamples 12 - 1404000*fourthLevelSamples 13 + 388000*fourthLevelSamples 14 - 100000*fourthLevelSamples 15 + 16000*fourthLevelSamples 16) / 1000000 - (-216000) / 1000000000000000 ∧ (- 10708000*fourthLevelSamples 1 + 4596000*fourthLevelSamples 2 + 1204000*fourthLevelSamples 3 - 3232000*fourthLevelSamples 4 + 4000000*fourthLevelSamples 5 - 6312000*fourthLevelSamples 6 + 8000000*fourthLevelSamples 7 - 6528000*fourthLevelSamples 8 + 2808000*fourthLevelSamples 9 + 1328000*fourthLevelSamples 10 - 3800000*fourthLevelSamples 11 + 3232000*fourthLevelSamples 12 - 1404000*fourthLevelSamples 13 + 388000*fourthLevelSamples 14 - 100000*fourthLevelSamples 15 + 16000*fourthLevelSamples 16) / 1000000 - (-216000) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_0_6 :
    (593004/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 0 6 ∧
      fourthLevelEvenSheared fourthLevelSamples 0 6 ≤ (593005/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (- 3672000*fourthLevelSamples 1 + 7766000*fourthLevelSamples 2 - 7884000*fourthLevelSamples 3 - 468000*fourthLevelSamples 4 + 9708000*fourthLevelSamples 5 - 11598000*fourthLevelSamples 6 + 7416000*fourthLevelSamples 7 - 944000*fourthLevelSamples 8 - 3736000*fourthLevelSamples 9 + 3798000*fourthLevelSamples 10 - 1692000*fourthLevelSamples 11 + 468000*fourthLevelSamples 12 - 132000*fourthLevelSamples 13 + 34000*fourthLevelSamples 14 - 8000*fourthLevelSamples 15 + 2000*fourthLevelSamples 16) / 1000000 - (-20000) / 1000000000000000 ∧ (- 3672000*fourthLevelSamples 1 + 7766000*fourthLevelSamples 2 - 7884000*fourthLevelSamples 3 - 468000*fourthLevelSamples 4 + 9708000*fourthLevelSamples 5 - 11598000*fourthLevelSamples 6 + 7416000*fourthLevelSamples 7 - 944000*fourthLevelSamples 8 - 3736000*fourthLevelSamples 9 + 3798000*fourthLevelSamples 10 - 1692000*fourthLevelSamples 11 + 468000*fourthLevelSamples 12 - 132000*fourthLevelSamples 13 + 34000*fourthLevelSamples 14 - 8000*fourthLevelSamples 15 + 2000*fourthLevelSamples 16) / 1000000 - (-20000) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_1_0 :
    (5910960/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 1 0 ∧
      fourthLevelEvenSheared fourthLevelSamples 1 0 ≤ (5910961/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (- 4000000*fourthLevelSamples 2 + 600000*fourthLevelSamples 4 - 5400000*fourthLevelSamples 8 + 8000000*fourthLevelSamples 10 - 600000*fourthLevelSamples 12 - 4000000*fourthLevelSamples 14 + 1650000*fourthLevelSamples 16) / 1000000 - (-350000) / 1000000000000000 ∧ (- 4000000*fourthLevelSamples 2 + 600000*fourthLevelSamples 4 - 5400000*fourthLevelSamples 8 + 8000000*fourthLevelSamples 10 - 600000*fourthLevelSamples 12 - 4000000*fourthLevelSamples 14 + 1650000*fourthLevelSamples 16) / 1000000 - (-350000) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_2_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_2_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_1_1 :
    (1464602222/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 1 1 ∧
      fourthLevelEvenSheared fourthLevelSamples 1 1 ≤ (1464602223/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (17400000*fourthLevelSamples 2 - 4455000*fourthLevelSamples 4 + 3645000*fourthLevelSamples 8 - 10800000*fourthLevelSamples 10 + 12455000*fourthLevelSamples 12 - 6600000*fourthLevelSamples 14 + 1361250*fourthLevelSamples 16) / 1000000 - (2061250) / 1000000000000000 ∧ (17400000*fourthLevelSamples 2 - 4455000*fourthLevelSamples 4 + 3645000*fourthLevelSamples 8 - 10800000*fourthLevelSamples 10 + 12455000*fourthLevelSamples 12 - 6600000*fourthLevelSamples 14 + 1361250*fourthLevelSamples 16) / 1000000 - (2061250) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_2_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_2_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_1_2 :
    (116326/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 1 2 ∧
      fourthLevelEvenSheared fourthLevelSamples 1 2 ≤ (116327/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (16965700*fourthLevelSamples 2 - 11506250*fourthLevelSamples 4 - 2100000*fourthLevelSamples 6 + 13154300*fourthLevelSamples 8 - 13047400*fourthLevelSamples 10 + 6634250*fourthLevelSamples 12 - 1818300*fourthLevelSamples 14 + 217800*fourthLevelSamples 16) / 1000000 - (872650) / 1000000000000000 ∧ (16965700*fourthLevelSamples 2 - 11506250*fourthLevelSamples 4 - 2100000*fourthLevelSamples 6 + 13154300*fourthLevelSamples 8 - 13047400*fourthLevelSamples 10 + 6634250*fourthLevelSamples 12 - 1818300*fourthLevelSamples 14 + 217800*fourthLevelSamples 16) / 1000000 - (872650) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_2_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_2_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_1_3 :
    (-259659/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 1 3 ∧
      fourthLevelEvenSheared fourthLevelSamples 1 3 ≤ (-259658/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (- 4700000*fourthLevelSamples 1 - 4545400*fourthLevelSamples 2 + 5400000*fourthLevelSamples 3 - 1331500*fourthLevelSamples 4 + 84000*fourthLevelSamples 6 - 1178600*fourthLevelSamples 8 + 5302800*fourthLevelSamples 10 - 5400000*fourthLevelSamples 11 - 4124500*fourthLevelSamples 12 + 8000000*fourthLevelSamples 13 - 841400*fourthLevelSamples 14 - 3300000*fourthLevelSamples 15 + 1329900*fourthLevelSamples 16) / 1000000 - (-453800) / 1000000000000000 ∧ (- 4700000*fourthLevelSamples 1 - 4545400*fourthLevelSamples 2 + 5400000*fourthLevelSamples 3 - 1331500*fourthLevelSamples 4 + 84000*fourthLevelSamples 6 - 1178600*fourthLevelSamples 8 + 5302800*fourthLevelSamples 10 - 5400000*fourthLevelSamples 11 - 4124500*fourthLevelSamples 12 + 8000000*fourthLevelSamples 13 - 841400*fourthLevelSamples 14 - 3300000*fourthLevelSamples 15 + 1329900*fourthLevelSamples 16) / 1000000 - (-453800) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_1_4 :
    (-896744/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 1 4 ∧
      fourthLevelEvenSheared fourthLevelSamples 1 4 ≤ (-896743/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (- 4104000*fourthLevelSamples 1 - 1496800*fourthLevelSamples 2 + 5028000*fourthLevelSamples 3 - 2990400*fourthLevelSamples 4 - 226800*fourthLevelSamples 6 + 3866400*fourthLevelSamples 8 - 5400000*fourthLevelSamples 9 - 484400*fourthLevelSamples 10 + 6272000*fourthLevelSamples 11 - 4273600*fourthLevelSamples 12 - 740000*fourthLevelSamples 13 + 2208000*fourthLevelSamples 14 - 1056000*fourthLevelSamples 15 + 178200*fourthLevelSamples 16) / 1000000 - (-254800) / 1000000000000000 ∧ (- 4104000*fourthLevelSamples 1 - 1496800*fourthLevelSamples 2 + 5028000*fourthLevelSamples 3 - 2990400*fourthLevelSamples 4 - 226800*fourthLevelSamples 6 + 3866400*fourthLevelSamples 8 - 5400000*fourthLevelSamples 9 - 484400*fourthLevelSamples 10 + 6272000*fourthLevelSamples 11 - 4273600*fourthLevelSamples 12 - 740000*fourthLevelSamples 13 + 2208000*fourthLevelSamples 14 - 1056000*fourthLevelSamples 15 + 178200*fourthLevelSamples 16) / 1000000 - (-254800) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_1_5 :
    (-362134/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 1 5 ∧
      fourthLevelEvenSheared fourthLevelSamples 1 5 ≤ (-362133/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (4369900*fourthLevelSamples 1 + 2875700*fourthLevelSamples 2 - 6706700*fourthLevelSamples 3 + 1493600*fourthLevelSamples 4 + 3300000*fourthLevelSamples 5 + 1104600*fourthLevelSamples 6 - 5400000*fourthLevelSamples 7 + 198400*fourthLevelSamples 8 + 6104600*fourthLevelSamples 9 - 4268400*fourthLevelSamples 10 - 627000*fourthLevelSamples 11 + 1938400*fourthLevelSamples 12 - 958300*fourthLevelSamples 13 + 288100*fourthLevelSamples 14 - 82500*fourthLevelSamples 15 + 13200*fourthLevelSamples 16) / 1000000 - (219800) / 1000000000000000 ∧ (4369900*fourthLevelSamples 1 + 2875700*fourthLevelSamples 2 - 6706700*fourthLevelSamples 3 + 1493600*fourthLevelSamples 4 + 3300000*fourthLevelSamples 5 + 1104600*fourthLevelSamples 6 - 5400000*fourthLevelSamples 7 + 198400*fourthLevelSamples 8 + 6104600*fourthLevelSamples 9 - 4268400*fourthLevelSamples 10 - 627000*fourthLevelSamples 11 + 1938400*fourthLevelSamples 12 - 958300*fourthLevelSamples 13 + 288100*fourthLevelSamples 14 - 82500*fourthLevelSamples 15 + 13200*fourthLevelSamples 16) / 1000000 - (219800) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_1_6 :
    (982291/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 1 6 ∧
      fourthLevelEvenSheared fourthLevelSamples 1 6 ≤ (982292/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (2210600*fourthLevelSamples 1 - 4345050*fourthLevelSamples 2 + 2103700*fourthLevelSamples 3 + 7339900*fourthLevelSamples 4 - 11990900*fourthLevelSamples 5 + 2029650*fourthLevelSamples 6 + 8994200*fourthLevelSamples 7 - 7094800*fourthLevelSamples 8 - 62200*fourthLevelSamples 9 + 2291350*fourthLevelSamples 10 - 1155900*fourthLevelSamples 11 + 324100*fourthLevelSamples 12 - 92900*fourthLevelSamples 13 + 24050*fourthLevelSamples 14 - 6600*fourthLevelSamples 15 + 1650*fourthLevelSamples 16) / 1000000 - (21500) / 1000000000000000 ∧ (2210600*fourthLevelSamples 1 - 4345050*fourthLevelSamples 2 + 2103700*fourthLevelSamples 3 + 7339900*fourthLevelSamples 4 - 11990900*fourthLevelSamples 5 + 2029650*fourthLevelSamples 6 + 8994200*fourthLevelSamples 7 - 7094800*fourthLevelSamples 8 - 62200*fourthLevelSamples 9 + 2291350*fourthLevelSamples 10 - 1155900*fourthLevelSamples 11 + 324100*fourthLevelSamples 12 - 92900*fourthLevelSamples 13 + 24050*fourthLevelSamples 14 - 6600*fourthLevelSamples 15 + 1650*fourthLevelSamples 16) / 1000000 - (21500) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_2_0 :
    (1223509/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 2 0 ∧
      fourthLevelEvenSheared fourthLevelSamples 2 0 ≤ (1223510/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (- 9564000*fourthLevelSamples 2 - 3290000*fourthLevelSamples 4 + 12000000*fourthLevelSamples 6 - 7636000*fourthLevelSamples 8 - 872000*fourthLevelSamples 10 + 3290000*fourthLevelSamples 12 - 1564000*fourthLevelSamples 14 + 264000*fourthLevelSamples 16) / 1000000 - (-518000) / 1000000000000000 ∧ (- 9564000*fourthLevelSamples 2 - 3290000*fourthLevelSamples 4 + 12000000*fourthLevelSamples 6 - 7636000*fourthLevelSamples 8 - 872000*fourthLevelSamples 10 + 3290000*fourthLevelSamples 12 - 1564000*fourthLevelSamples 14 + 264000*fourthLevelSamples 16) / 1000000 - (-518000) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_2_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_2_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_2_1 :
    (116326/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 2 1 ∧
      fourthLevelEvenSheared fourthLevelSamples 2 1 ≤ (116327/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (16965700*fourthLevelSamples 2 - 11506250*fourthLevelSamples 4 - 2100000*fourthLevelSamples 6 + 13154300*fourthLevelSamples 8 - 13047400*fourthLevelSamples 10 + 6634250*fourthLevelSamples 12 - 1818300*fourthLevelSamples 14 + 217800*fourthLevelSamples 16) / 1000000 - (872650) / 1000000000000000 ∧ (16965700*fourthLevelSamples 2 - 11506250*fourthLevelSamples 4 - 2100000*fourthLevelSamples 6 + 13154300*fourthLevelSamples 8 - 13047400*fourthLevelSamples 10 + 6634250*fourthLevelSamples 12 - 1818300*fourthLevelSamples 14 + 217800*fourthLevelSamples 16) / 1000000 - (872650) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_2_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_2_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_2_2 :
    (1271977102/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 2 2 ∧
      fourthLevelEvenSheared fourthLevelSamples 2 2 ≤ (1271977103/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (21656248*fourthLevelSamples 2 + 736048*fourthLevelSamples 4 - 14216000*fourthLevelSamples 6 + 13544562*fourthLevelSamples 8 - 7027352*fourthLevelSamples 10 + 2231000*fourthLevelSamples 12 - 412896*fourthLevelSamples 14 + 34848*fourthLevelSamples 16) / 1000000 - (2439924) / 1000000000000000 ∧ (21656248*fourthLevelSamples 2 + 736048*fourthLevelSamples 4 - 14216000*fourthLevelSamples 6 + 13544562*fourthLevelSamples 8 - 7027352*fourthLevelSamples 10 + 2231000*fourthLevelSamples 12 - 412896*fourthLevelSamples 14 + 34848*fourthLevelSamples 16) / 1000000 - (2439924) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_2_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_2_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_2_3 :
    (-189715/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 2 3 ∧
      fourthLevelEvenSheared fourthLevelSamples 2 3 ≤ (-189713/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (- 2600000*fourthLevelSamples 1 - 6708616*fourthLevelSamples 2 + 7636000*fourthLevelSamples 3 + 2587764*fourthLevelSamples 4 - 8000000*fourthLevelSamples 5 + 4780320*fourthLevelSamples 6 - 7115244*fourthLevelSamples 8 + 8000000*fourthLevelSamples 9 + 2807664*fourthLevelSamples 10 - 7636000*fourthLevelSamples 11 + 734940*fourthLevelSamples 12 + 3128000*fourthLevelSamples 13 - 879368*fourthLevelSamples 14 - 528000*fourthLevelSamples 15 + 212784*fourthLevelSamples 16) / 1000000 - (-268108) / 1000000000000000 ∧ (- 2600000*fourthLevelSamples 1 - 6708616*fourthLevelSamples 2 + 7636000*fourthLevelSamples 3 + 2587764*fourthLevelSamples 4 - 8000000*fourthLevelSamples 5 + 4780320*fourthLevelSamples 6 - 7115244*fourthLevelSamples 8 + 8000000*fourthLevelSamples 9 + 2807664*fourthLevelSamples 10 - 7636000*fourthLevelSamples 11 + 734940*fourthLevelSamples 12 + 3128000*fourthLevelSamples 13 - 879368*fourthLevelSamples 14 - 528000*fourthLevelSamples 15 + 212784*fourthLevelSamples 16) / 1000000 - (-268108) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_2_4 :
    (396835/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 2 4 ∧
      fourthLevelEvenSheared fourthLevelSamples 2 4 ≤ (396836/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (3676000*fourthLevelSamples 1 + 649568*fourthLevelSamples 2 - 5028480*fourthLevelSamples 3 + 6220264*fourthLevelSamples 4 - 2560000*fourthLevelSamples 5 - 4783664*fourthLevelSamples 6 + 8000000*fourthLevelSamples 7 - 1816560*fourthLevelSamples 8 - 5076000*fourthLevelSamples 9 + 3880608*fourthLevelSamples 10 + 684480*fourthLevelSamples 11 - 1796488*fourthLevelSamples 12 + 472960*fourthLevelSamples 13 + 253488*fourthLevelSamples 14 - 168960*fourthLevelSamples 15 + 28512*fourthLevelSamples 16) / 1000000 - (143816) / 1000000000000000 ∧ (3676000*fourthLevelSamples 1 + 649568*fourthLevelSamples 2 - 5028480*fourthLevelSamples 3 + 6220264*fourthLevelSamples 4 - 2560000*fourthLevelSamples 5 - 4783664*fourthLevelSamples 6 + 8000000*fourthLevelSamples 7 - 1816560*fourthLevelSamples 8 - 5076000*fourthLevelSamples 9 + 3880608*fourthLevelSamples 10 + 684480*fourthLevelSamples 11 - 1796488*fourthLevelSamples 12 + 472960*fourthLevelSamples 13 + 253488*fourthLevelSamples 14 - 168960*fourthLevelSamples 15 + 28512*fourthLevelSamples 16) / 1000000 - (143816) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_2_5 :
    (-467726/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 2 5 ∧
      fourthLevelEvenSheared fourthLevelSamples 2 5 ≤ (-467725/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (1153308*fourthLevelSamples 1 + 4284516*fourthLevelSamples 2 - 5559772*fourthLevelSamples 3 - 2248064*fourthLevelSamples 4 + 8328000*fourthLevelSamples 5 - 2757192*fourthLevelSamples 6 - 4828000*fourthLevelSamples 7 + 3809648*fourthLevelSamples 8 + 647764*fourthLevelSamples 9 - 1566028*fourthLevelSamples 10 + 379028*fourthLevelSamples 11 + 157976*fourthLevelSamples 12 - 107128*fourthLevelSamples 13 + 38704*fourthLevelSamples 14 - 13200*fourthLevelSamples 15 + 2112*fourthLevelSamples 16) / 1000000 - (75106) / 1000000000000000 ∧ (1153308*fourthLevelSamples 1 + 4284516*fourthLevelSamples 2 - 5559772*fourthLevelSamples 3 - 2248064*fourthLevelSamples 4 + 8328000*fourthLevelSamples 5 - 2757192*fourthLevelSamples 6 - 4828000*fourthLevelSamples 7 + 3809648*fourthLevelSamples 8 + 647764*fourthLevelSamples 9 - 1566028*fourthLevelSamples 10 + 379028*fourthLevelSamples 11 + 157976*fourthLevelSamples 12 - 107128*fourthLevelSamples 13 + 38704*fourthLevelSamples 14 - 13200*fourthLevelSamples 15 + 2112*fourthLevelSamples 16) / 1000000 - (75106) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_2_6 :
    (-707094/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 2 6 ∧
      fourthLevelEvenSheared fourthLevelSamples 2 6 ≤ (-707093/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (- 8011864*fourthLevelSamples 1 - 6134920*fourthLevelSamples 2 + 14069040*fourthLevelSamples 3 - 4706910*fourthLevelSamples 4 - 7138544*fourthLevelSamples 5 + 5929882*fourthLevelSamples 6 + 659428*fourthLevelSamples 7 - 2190164*fourthLevelSamples 8 + 571668*fourthLevelSamples 9 + 202114*fourthLevelSamples 10 - 137504*fourthLevelSamples 11 + 39534*fourthLevelSamples 12 - 11168*fourthLevelSamples 13 + 2924*fourthLevelSamples 14 - 1056*fourthLevelSamples 15 + 264*fourthLevelSamples 16) / 1000000 - (-493782) / 1000000000000000 ∧ (- 8011864*fourthLevelSamples 1 - 6134920*fourthLevelSamples 2 + 14069040*fourthLevelSamples 3 - 4706910*fourthLevelSamples 4 - 7138544*fourthLevelSamples 5 + 5929882*fourthLevelSamples 6 + 659428*fourthLevelSamples 7 - 2190164*fourthLevelSamples 8 + 571668*fourthLevelSamples 9 + 202114*fourthLevelSamples 10 - 137504*fourthLevelSamples 11 + 39534*fourthLevelSamples 12 - 11168*fourthLevelSamples 13 + 2924*fourthLevelSamples 14 - 1056*fourthLevelSamples 15 + 264*fourthLevelSamples 16) / 1000000 - (-493782) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_3_0 :
    (-8303104/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 3 0 ∧
      fourthLevelEvenSheared fourthLevelSamples 3 0 ≤ (-8303103/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (4000000*fourthLevelSamples 1 + 3208000*fourthLevelSamples 2 - 8000000*fourthLevelSamples 3 + 3860000*fourthLevelSamples 4 - 480000*fourthLevelSamples 6 + 1272000*fourthLevelSamples 8 - 5616000*fourthLevelSamples 10 + 8000000*fourthLevelSamples 11 - 3860000*fourthLevelSamples 12 + 2888000*fourthLevelSamples 14 - 4000000*fourthLevelSamples 15 + 1612000*fourthLevelSamples 16) / 1000000 - (56000) / 1000000000000000 ∧ (4000000*fourthLevelSamples 1 + 3208000*fourthLevelSamples 2 - 8000000*fourthLevelSamples 3 + 3860000*fourthLevelSamples 4 - 480000*fourthLevelSamples 6 + 1272000*fourthLevelSamples 8 - 5616000*fourthLevelSamples 10 + 8000000*fourthLevelSamples 11 - 3860000*fourthLevelSamples 12 + 2888000*fourthLevelSamples 14 - 4000000*fourthLevelSamples 15 + 1612000*fourthLevelSamples 16) / 1000000 - (56000) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_3_1 :
    (-259659/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 3 1 ∧
      fourthLevelEvenSheared fourthLevelSamples 3 1 ≤ (-259658/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (- 4700000*fourthLevelSamples 1 - 4545400*fourthLevelSamples 2 + 5400000*fourthLevelSamples 3 - 1331500*fourthLevelSamples 4 + 84000*fourthLevelSamples 6 - 1178600*fourthLevelSamples 8 + 5302800*fourthLevelSamples 10 - 5400000*fourthLevelSamples 11 - 4124500*fourthLevelSamples 12 + 8000000*fourthLevelSamples 13 - 841400*fourthLevelSamples 14 - 3300000*fourthLevelSamples 15 + 1329900*fourthLevelSamples 16) / 1000000 - (-453800) / 1000000000000000 ∧ (- 4700000*fourthLevelSamples 1 - 4545400*fourthLevelSamples 2 + 5400000*fourthLevelSamples 3 - 1331500*fourthLevelSamples 4 + 84000*fourthLevelSamples 6 - 1178600*fourthLevelSamples 8 + 5302800*fourthLevelSamples 10 - 5400000*fourthLevelSamples 11 - 4124500*fourthLevelSamples 12 + 8000000*fourthLevelSamples 13 - 841400*fourthLevelSamples 14 - 3300000*fourthLevelSamples 15 + 1329900*fourthLevelSamples 16) / 1000000 - (-453800) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_3_2 :
    (-189715/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 3 2 ∧
      fourthLevelEvenSheared fourthLevelSamples 3 2 ≤ (-189713/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (- 2600000*fourthLevelSamples 1 - 6708616*fourthLevelSamples 2 + 7636000*fourthLevelSamples 3 + 2587764*fourthLevelSamples 4 - 8000000*fourthLevelSamples 5 + 4780320*fourthLevelSamples 6 - 7115244*fourthLevelSamples 8 + 8000000*fourthLevelSamples 9 + 2807664*fourthLevelSamples 10 - 7636000*fourthLevelSamples 11 + 734940*fourthLevelSamples 12 + 3128000*fourthLevelSamples 13 - 879368*fourthLevelSamples 14 - 528000*fourthLevelSamples 15 + 212784*fourthLevelSamples 16) / 1000000 - (-268108) / 1000000000000000 ∧ (- 2600000*fourthLevelSamples 1 - 6708616*fourthLevelSamples 2 + 7636000*fourthLevelSamples 3 + 2587764*fourthLevelSamples 4 - 8000000*fourthLevelSamples 5 + 4780320*fourthLevelSamples 6 - 7115244*fourthLevelSamples 8 + 8000000*fourthLevelSamples 9 + 2807664*fourthLevelSamples 10 - 7636000*fourthLevelSamples 11 + 734940*fourthLevelSamples 12 + 3128000*fourthLevelSamples 13 - 879368*fourthLevelSamples 14 - 528000*fourthLevelSamples 15 + 212784*fourthLevelSamples 16) / 1000000 - (-268108) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_3_3 :
    (179467983/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 3 3 ∧
      fourthLevelEvenSheared fourthLevelSamples 3 3 ≤ (179467984/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (18000000*fourthLevelSamples 1 - 2716928*fourthLevelSamples 2 - 2544000*fourthLevelSamples 3 + 575952*fourthLevelSamples 4 + 640000*fourthLevelSamples 5 - 359680*fourthLevelSamples 6 + 664328*fourthLevelSamples 8 - 640000*fourthLevelSamples 9 - 1578848*fourthLevelSamples 10 + 2544000*fourthLevelSamples 11 + 3145040*fourthLevelSamples 12 - 11552000*fourthLevelSamples 13 + 12655456*fourthLevelSamples 14 - 6448000*fourthLevelSamples 15 + 1299272*fourthLevelSamples 16) / 1000000 - (2103336) / 1000000000000000 ∧ (18000000*fourthLevelSamples 1 - 2716928*fourthLevelSamples 2 - 2544000*fourthLevelSamples 3 + 575952*fourthLevelSamples 4 + 640000*fourthLevelSamples 5 - 359680*fourthLevelSamples 6 + 664328*fourthLevelSamples 8 - 640000*fourthLevelSamples 9 - 1578848*fourthLevelSamples 10 + 2544000*fourthLevelSamples 11 + 3145040*fourthLevelSamples 12 - 11552000*fourthLevelSamples 13 + 12655456*fourthLevelSamples 14 - 6448000*fourthLevelSamples 15 + 1299272*fourthLevelSamples 16) / 1000000 - (2103336) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_3_4 :
    (-41450/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 3 4 ∧
      fourthLevelEvenSheared fourthLevelSamples 3 4 ≤ (-41449/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (14216000*fourthLevelSamples 1 - 13400256*fourthLevelSamples 2 + 7584960*fourthLevelSamples 3 - 1390608*fourthLevelSamples 4 - 761600*fourthLevelSamples 5 + 646208*fourthLevelSamples 6 - 320000*fourthLevelSamples 7 - 1075040*fourthLevelSamples 8 + 2033600*fourthLevelSamples 9 + 1862944*fourthLevelSamples 10 - 9816960*fourthLevelSamples 11 + 14344656*fourthLevelSamples 12 - 11472320*fourthLevelSamples 13 + 5451104*fourthLevelSamples 14 - 1463680*fourthLevelSamples 15 + 174096*fourthLevelSamples 16) / 1000000 - (689488) / 1000000000000000 ∧ (14216000*fourthLevelSamples 1 - 13400256*fourthLevelSamples 2 + 7584960*fourthLevelSamples 3 - 1390608*fourthLevelSamples 4 - 761600*fourthLevelSamples 5 + 646208*fourthLevelSamples 6 - 320000*fourthLevelSamples 7 - 1075040*fourthLevelSamples 8 + 2033600*fourthLevelSamples 9 + 1862944*fourthLevelSamples 10 - 9816960*fourthLevelSamples 11 + 14344656*fourthLevelSamples 12 - 11472320*fourthLevelSamples 13 + 5451104*fourthLevelSamples 14 - 1463680*fourthLevelSamples 15 + 174096*fourthLevelSamples 16) / 1000000 - (689488) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_3_5 :
    (12702/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 3 5 ∧
      fourthLevelEvenSheared fourthLevelSamples 3 5 ≤ (12703/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (1661904*fourthLevelSamples 1 - 7325712*fourthLevelSamples 2 + 13516144*fourthLevelSamples 3 - 13526592*fourthLevelSamples 4 + 7120000*fourthLevelSamples 5 - 2105056*fourthLevelSamples 6 + 1159680*fourthLevelSamples 7 + 2031264*fourthLevelSamples 8 - 9545528*fourthLevelSamples 9 + 14286936*fourthLevelSamples 10 - 11747576*fourthLevelSamples 11 + 5993968*fourthLevelSamples 12 - 2052024*fourthLevelSamples 13 + 535832*fourthLevelSamples 14 - 112600*fourthLevelSamples 15 + 12896*fourthLevelSamples 16) / 1000000 - (5628) / 1000000000000000 ∧ (1661904*fourthLevelSamples 1 - 7325712*fourthLevelSamples 2 + 13516144*fourthLevelSamples 3 - 13526592*fourthLevelSamples 4 + 7120000*fourthLevelSamples 5 - 2105056*fourthLevelSamples 6 + 1159680*fourthLevelSamples 7 + 2031264*fourthLevelSamples 8 - 9545528*fourthLevelSamples 9 + 14286936*fourthLevelSamples 10 - 11747576*fourthLevelSamples 11 + 5993968*fourthLevelSamples 12 - 2052024*fourthLevelSamples 13 + 535832*fourthLevelSamples 14 - 112600*fourthLevelSamples 15 + 12896*fourthLevelSamples 16) / 1000000 - (5628) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_3_6 :
    (-79005/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 3 6 ∧
      fourthLevelEvenSheared fourthLevelSamples 3 6 ≤ (-79003/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (152128*fourthLevelSamples 1 + 226580*fourthLevelSamples 2 + 1932760*fourthLevelSamples 3 - 9071740*fourthLevelSamples 4 + 16020648*fourthLevelSamples 5 - 12307784*fourthLevelSamples 6 - 2019416*fourthLevelSamples 7 + 13435128*fourthLevelSamples 8 - 13381016*fourthLevelSamples 9 + 7202912*fourthLevelSamples 10 - 2508712*fourthLevelSamples 11 + 692892*fourthLevelSamples 12 - 185944*fourthLevelSamples 13 + 46292*fourthLevelSamples 14 - 10448*fourthLevelSamples 15 + 1612*fourthLevelSamples 16) / 1000000 - (19684) / 1000000000000000 ∧ (152128*fourthLevelSamples 1 + 226580*fourthLevelSamples 2 + 1932760*fourthLevelSamples 3 - 9071740*fourthLevelSamples 4 + 16020648*fourthLevelSamples 5 - 12307784*fourthLevelSamples 6 - 2019416*fourthLevelSamples 7 + 13435128*fourthLevelSamples 8 - 13381016*fourthLevelSamples 9 + 7202912*fourthLevelSamples 10 - 2508712*fourthLevelSamples 11 + 692892*fourthLevelSamples 12 - 185944*fourthLevelSamples 13 + 46292*fourthLevelSamples 14 - 10448*fourthLevelSamples 15 + 1612*fourthLevelSamples 16) / 1000000 - (19684) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_4_0 :
    (-5678535/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 4 0 ∧
      fourthLevelEvenSheared fourthLevelSamples 4 0 ≤ (-5678534/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (- 6720000*fourthLevelSamples 1 + 2336000*fourthLevelSamples 2 + 1440000*fourthLevelSamples 3 - 1792000*fourthLevelSamples 4 + 1296000*fourthLevelSamples 6 - 4448000*fourthLevelSamples 8 + 8000000*fourthLevelSamples 9 - 6832000*fourthLevelSamples 10 + 2560000*fourthLevelSamples 11 + 1792000*fourthLevelSamples 12 - 4000000*fourthLevelSamples 13 + 3200000*fourthLevelSamples 14 - 1280000*fourthLevelSamples 15 + 216000*fourthLevelSamples 16) / 1000000 - (-144000) / 1000000000000000 ∧ (- 6720000*fourthLevelSamples 1 + 2336000*fourthLevelSamples 2 + 1440000*fourthLevelSamples 3 - 1792000*fourthLevelSamples 4 + 1296000*fourthLevelSamples 6 - 4448000*fourthLevelSamples 8 + 8000000*fourthLevelSamples 9 - 6832000*fourthLevelSamples 10 + 2560000*fourthLevelSamples 11 + 1792000*fourthLevelSamples 12 - 4000000*fourthLevelSamples 13 + 3200000*fourthLevelSamples 14 - 1280000*fourthLevelSamples 15 + 216000*fourthLevelSamples 16) / 1000000 - (-144000) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_4_1 :
    (-896744/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 4 1 ∧
      fourthLevelEvenSheared fourthLevelSamples 4 1 ≤ (-896743/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (- 4104000*fourthLevelSamples 1 - 1496800*fourthLevelSamples 2 + 5028000*fourthLevelSamples 3 - 2990400*fourthLevelSamples 4 - 226800*fourthLevelSamples 6 + 3866400*fourthLevelSamples 8 - 5400000*fourthLevelSamples 9 - 484400*fourthLevelSamples 10 + 6272000*fourthLevelSamples 11 - 4273600*fourthLevelSamples 12 - 740000*fourthLevelSamples 13 + 2208000*fourthLevelSamples 14 - 1056000*fourthLevelSamples 15 + 178200*fourthLevelSamples 16) / 1000000 - (-254800) / 1000000000000000 ∧ (- 4104000*fourthLevelSamples 1 - 1496800*fourthLevelSamples 2 + 5028000*fourthLevelSamples 3 - 2990400*fourthLevelSamples 4 - 226800*fourthLevelSamples 6 + 3866400*fourthLevelSamples 8 - 5400000*fourthLevelSamples 9 - 484400*fourthLevelSamples 10 + 6272000*fourthLevelSamples 11 - 4273600*fourthLevelSamples 12 - 740000*fourthLevelSamples 13 + 2208000*fourthLevelSamples 14 - 1056000*fourthLevelSamples 15 + 178200*fourthLevelSamples 16) / 1000000 - (-254800) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_4_2 :
    (396835/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 4 2 ∧
      fourthLevelEvenSheared fourthLevelSamples 4 2 ≤ (396836/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (3676000*fourthLevelSamples 1 + 649568*fourthLevelSamples 2 - 5028480*fourthLevelSamples 3 + 6220264*fourthLevelSamples 4 - 2560000*fourthLevelSamples 5 - 4783664*fourthLevelSamples 6 + 8000000*fourthLevelSamples 7 - 1816560*fourthLevelSamples 8 - 5076000*fourthLevelSamples 9 + 3880608*fourthLevelSamples 10 + 684480*fourthLevelSamples 11 - 1796488*fourthLevelSamples 12 + 472960*fourthLevelSamples 13 + 253488*fourthLevelSamples 14 - 168960*fourthLevelSamples 15 + 28512*fourthLevelSamples 16) / 1000000 - (143816) / 1000000000000000 ∧ (3676000*fourthLevelSamples 1 + 649568*fourthLevelSamples 2 - 5028480*fourthLevelSamples 3 + 6220264*fourthLevelSamples 4 - 2560000*fourthLevelSamples 5 - 4783664*fourthLevelSamples 6 + 8000000*fourthLevelSamples 7 - 1816560*fourthLevelSamples 8 - 5076000*fourthLevelSamples 9 + 3880608*fourthLevelSamples 10 + 684480*fourthLevelSamples 11 - 1796488*fourthLevelSamples 12 + 472960*fourthLevelSamples 13 + 253488*fourthLevelSamples 14 - 168960*fourthLevelSamples 15 + 28512*fourthLevelSamples 16) / 1000000 - (143816) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_4_3 :
    (-41450/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 4 3 ∧
      fourthLevelEvenSheared fourthLevelSamples 4 3 ≤ (-41449/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (14216000*fourthLevelSamples 1 - 13400256*fourthLevelSamples 2 + 7584960*fourthLevelSamples 3 - 1390608*fourthLevelSamples 4 - 761600*fourthLevelSamples 5 + 646208*fourthLevelSamples 6 - 320000*fourthLevelSamples 7 - 1075040*fourthLevelSamples 8 + 2033600*fourthLevelSamples 9 + 1862944*fourthLevelSamples 10 - 9816960*fourthLevelSamples 11 + 14344656*fourthLevelSamples 12 - 11472320*fourthLevelSamples 13 + 5451104*fourthLevelSamples 14 - 1463680*fourthLevelSamples 15 + 174096*fourthLevelSamples 16) / 1000000 - (689488) / 1000000000000000 ∧ (14216000*fourthLevelSamples 1 - 13400256*fourthLevelSamples 2 + 7584960*fourthLevelSamples 3 - 1390608*fourthLevelSamples 4 - 761600*fourthLevelSamples 5 + 646208*fourthLevelSamples 6 - 320000*fourthLevelSamples 7 - 1075040*fourthLevelSamples 8 + 2033600*fourthLevelSamples 9 + 1862944*fourthLevelSamples 10 - 9816960*fourthLevelSamples 11 + 14344656*fourthLevelSamples 12 - 11472320*fourthLevelSamples 13 + 5451104*fourthLevelSamples 14 - 1463680*fourthLevelSamples 15 + 174096*fourthLevelSamples 16) / 1000000 - (689488) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_4_4 :
    (120870574/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 4 4 ∧
      fourthLevelEvenSheared fourthLevelSamples 4 4 ≤ (120870575/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (26068480*fourthLevelSamples 1 - 11967232*fourthLevelSamples 2 + 1982720*fourthLevelSamples 3 + 995328*fourthLevelSamples 4 - 552960*fourthLevelSamples 5 - 867456*fourthLevelSamples 6 + 1728000*fourthLevelSamples 7 + 1090688*fourthLevelSamples 8 - 8343040*fourthLevelSamples 9 + 15023488*fourthLevelSamples 10 - 15646720*fourthLevelSamples 11 + 10720384*fourthLevelSamples 12 - 4960000*fourthLevelSamples 13 + 1510400*fourthLevelSamples 14 - 276480*fourthLevelSamples 15 + 23328*fourthLevelSamples 16) / 1000000 - (2277696) / 1000000000000000 ∧ (26068480*fourthLevelSamples 1 - 11967232*fourthLevelSamples 2 + 1982720*fourthLevelSamples 3 + 995328*fourthLevelSamples 4 - 552960*fourthLevelSamples 5 - 867456*fourthLevelSamples 6 + 1728000*fourthLevelSamples 7 + 1090688*fourthLevelSamples 8 - 8343040*fourthLevelSamples 9 + 15023488*fourthLevelSamples 10 - 15646720*fourthLevelSamples 11 + 10720384*fourthLevelSamples 12 - 4960000*fourthLevelSamples 13 + 1510400*fourthLevelSamples 14 - 276480*fourthLevelSamples 15 + 23328*fourthLevelSamples 16) / 1000000 - (2277696) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_4_5 :
    (29791/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 4 5 ∧
      fourthLevelEvenSheared fourthLevelSamples 4 5 ≤ (29792/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (15125008*fourthLevelSamples 1 - 16454544*fourthLevelSamples 2 + 12688528*fourthLevelSamples 3 - 6667360*fourthLevelSamples 4 + 2620960*fourthLevelSamples 5 + 1410848*fourthLevelSamples 6 - 8352736*fourthLevelSamples 7 + 14912160*fourthLevelSamples 8 - 15814208*fourthLevelSamples 9 + 11245632*fourthLevelSamples 10 - 5654560*fourthLevelSamples 11 + 2089664*fourthLevelSamples 12 - 591952*fourthLevelSamples 13 + 131504*fourthLevelSamples 14 - 21040*fourthLevelSamples 15 + 1728*fourthLevelSamples 16) / 1000000 - (702456) / 1000000000000000 ∧ (15125008*fourthLevelSamples 1 - 16454544*fourthLevelSamples 2 + 12688528*fourthLevelSamples 3 - 6667360*fourthLevelSamples 4 + 2620960*fourthLevelSamples 5 + 1410848*fourthLevelSamples 6 - 8352736*fourthLevelSamples 7 + 14912160*fourthLevelSamples 8 - 15814208*fourthLevelSamples 9 + 11245632*fourthLevelSamples 10 - 5654560*fourthLevelSamples 11 + 2089664*fourthLevelSamples 12 - 591952*fourthLevelSamples 13 + 131504*fourthLevelSamples 14 - 21040*fourthLevelSamples 15 + 1728*fourthLevelSamples 16) / 1000000 - (702456) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_4_6 :
    (45226/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 4 6 ∧
      fourthLevelEvenSheared fourthLevelSamples 4 6 ≤ (45227/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (2073056*fourthLevelSamples 1 - 8513400*fourthLevelSamples 2 + 16077520*fourthLevelSamples 3 - 16159632*fourthLevelSamples 4 + 4977904*fourthLevelSamples 5 + 9219944*fourthLevelSamples 6 - 15570784*fourthLevelSamples 7 + 12679120*fourthLevelSamples 8 - 6728096*fourthLevelSamples 9 + 2567224*fourthLevelSamples 10 - 774640*fourthLevelSamples 11 + 208080*fourthLevelSamples 12 - 52816*fourthLevelSamples 13 + 11992*fourthLevelSamples 14 - 2144*fourthLevelSamples 15 + 216*fourthLevelSamples 16) / 1000000 - (11552) / 1000000000000000 ∧ (2073056*fourthLevelSamples 1 - 8513400*fourthLevelSamples 2 + 16077520*fourthLevelSamples 3 - 16159632*fourthLevelSamples 4 + 4977904*fourthLevelSamples 5 + 9219944*fourthLevelSamples 6 - 15570784*fourthLevelSamples 7 + 12679120*fourthLevelSamples 8 - 6728096*fourthLevelSamples 9 + 2567224*fourthLevelSamples 10 - 774640*fourthLevelSamples 11 + 208080*fourthLevelSamples 12 - 52816*fourthLevelSamples 13 + 11992*fourthLevelSamples 14 - 2144*fourthLevelSamples 15 + 216*fourthLevelSamples 16) / 1000000 - (11552) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_5_0 :
    (-4538860/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 5 0 ∧
      fourthLevelEvenSheared fourthLevelSamples 5 0 ≤ (-4538859/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (- 10708000*fourthLevelSamples 1 + 4596000*fourthLevelSamples 2 + 1204000*fourthLevelSamples 3 - 3232000*fourthLevelSamples 4 + 4000000*fourthLevelSamples 5 - 6312000*fourthLevelSamples 6 + 8000000*fourthLevelSamples 7 - 6528000*fourthLevelSamples 8 + 2808000*fourthLevelSamples 9 + 1328000*fourthLevelSamples 10 - 3800000*fourthLevelSamples 11 + 3232000*fourthLevelSamples 12 - 1404000*fourthLevelSamples 13 + 388000*fourthLevelSamples 14 - 100000*fourthLevelSamples 15 + 16000*fourthLevelSamples 16) / 1000000 - (-216000) / 1000000000000000 ∧ (- 10708000*fourthLevelSamples 1 + 4596000*fourthLevelSamples 2 + 1204000*fourthLevelSamples 3 - 3232000*fourthLevelSamples 4 + 4000000*fourthLevelSamples 5 - 6312000*fourthLevelSamples 6 + 8000000*fourthLevelSamples 7 - 6528000*fourthLevelSamples 8 + 2808000*fourthLevelSamples 9 + 1328000*fourthLevelSamples 10 - 3800000*fourthLevelSamples 11 + 3232000*fourthLevelSamples 12 - 1404000*fourthLevelSamples 13 + 388000*fourthLevelSamples 14 - 100000*fourthLevelSamples 15 + 16000*fourthLevelSamples 16) / 1000000 - (-216000) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_5_1 :
    (-362134/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 5 1 ∧
      fourthLevelEvenSheared fourthLevelSamples 5 1 ≤ (-362133/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (4369900*fourthLevelSamples 1 + 2875700*fourthLevelSamples 2 - 6706700*fourthLevelSamples 3 + 1493600*fourthLevelSamples 4 + 3300000*fourthLevelSamples 5 + 1104600*fourthLevelSamples 6 - 5400000*fourthLevelSamples 7 + 198400*fourthLevelSamples 8 + 6104600*fourthLevelSamples 9 - 4268400*fourthLevelSamples 10 - 627000*fourthLevelSamples 11 + 1938400*fourthLevelSamples 12 - 958300*fourthLevelSamples 13 + 288100*fourthLevelSamples 14 - 82500*fourthLevelSamples 15 + 13200*fourthLevelSamples 16) / 1000000 - (219800) / 1000000000000000 ∧ (4369900*fourthLevelSamples 1 + 2875700*fourthLevelSamples 2 - 6706700*fourthLevelSamples 3 + 1493600*fourthLevelSamples 4 + 3300000*fourthLevelSamples 5 + 1104600*fourthLevelSamples 6 - 5400000*fourthLevelSamples 7 + 198400*fourthLevelSamples 8 + 6104600*fourthLevelSamples 9 - 4268400*fourthLevelSamples 10 - 627000*fourthLevelSamples 11 + 1938400*fourthLevelSamples 12 - 958300*fourthLevelSamples 13 + 288100*fourthLevelSamples 14 - 82500*fourthLevelSamples 15 + 13200*fourthLevelSamples 16) / 1000000 - (219800) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_5_2 :
    (-467726/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 5 2 ∧
      fourthLevelEvenSheared fourthLevelSamples 5 2 ≤ (-467725/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (1153308*fourthLevelSamples 1 + 4284516*fourthLevelSamples 2 - 5559772*fourthLevelSamples 3 - 2248064*fourthLevelSamples 4 + 8328000*fourthLevelSamples 5 - 2757192*fourthLevelSamples 6 - 4828000*fourthLevelSamples 7 + 3809648*fourthLevelSamples 8 + 647764*fourthLevelSamples 9 - 1566028*fourthLevelSamples 10 + 379028*fourthLevelSamples 11 + 157976*fourthLevelSamples 12 - 107128*fourthLevelSamples 13 + 38704*fourthLevelSamples 14 - 13200*fourthLevelSamples 15 + 2112*fourthLevelSamples 16) / 1000000 - (75106) / 1000000000000000 ∧ (1153308*fourthLevelSamples 1 + 4284516*fourthLevelSamples 2 - 5559772*fourthLevelSamples 3 - 2248064*fourthLevelSamples 4 + 8328000*fourthLevelSamples 5 - 2757192*fourthLevelSamples 6 - 4828000*fourthLevelSamples 7 + 3809648*fourthLevelSamples 8 + 647764*fourthLevelSamples 9 - 1566028*fourthLevelSamples 10 + 379028*fourthLevelSamples 11 + 157976*fourthLevelSamples 12 - 107128*fourthLevelSamples 13 + 38704*fourthLevelSamples 14 - 13200*fourthLevelSamples 15 + 2112*fourthLevelSamples 16) / 1000000 - (75106) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_5_3 :
    (12702/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 5 3 ∧
      fourthLevelEvenSheared fourthLevelSamples 5 3 ≤ (12703/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (1661904*fourthLevelSamples 1 - 7325712*fourthLevelSamples 2 + 13516144*fourthLevelSamples 3 - 13526592*fourthLevelSamples 4 + 7120000*fourthLevelSamples 5 - 2105056*fourthLevelSamples 6 + 1159680*fourthLevelSamples 7 + 2031264*fourthLevelSamples 8 - 9545528*fourthLevelSamples 9 + 14286936*fourthLevelSamples 10 - 11747576*fourthLevelSamples 11 + 5993968*fourthLevelSamples 12 - 2052024*fourthLevelSamples 13 + 535832*fourthLevelSamples 14 - 112600*fourthLevelSamples 15 + 12896*fourthLevelSamples 16) / 1000000 - (5628) / 1000000000000000 ∧ (1661904*fourthLevelSamples 1 - 7325712*fourthLevelSamples 2 + 13516144*fourthLevelSamples 3 - 13526592*fourthLevelSamples 4 + 7120000*fourthLevelSamples 5 - 2105056*fourthLevelSamples 6 + 1159680*fourthLevelSamples 7 + 2031264*fourthLevelSamples 8 - 9545528*fourthLevelSamples 9 + 14286936*fourthLevelSamples 10 - 11747576*fourthLevelSamples 11 + 5993968*fourthLevelSamples 12 - 2052024*fourthLevelSamples 13 + 535832*fourthLevelSamples 14 - 112600*fourthLevelSamples 15 + 12896*fourthLevelSamples 16) / 1000000 - (5628) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_5_4 :
    (29791/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 5 4 ∧
      fourthLevelEvenSheared fourthLevelSamples 5 4 ≤ (29792/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (15125008*fourthLevelSamples 1 - 16454544*fourthLevelSamples 2 + 12688528*fourthLevelSamples 3 - 6667360*fourthLevelSamples 4 + 2620960*fourthLevelSamples 5 + 1410848*fourthLevelSamples 6 - 8352736*fourthLevelSamples 7 + 14912160*fourthLevelSamples 8 - 15814208*fourthLevelSamples 9 + 11245632*fourthLevelSamples 10 - 5654560*fourthLevelSamples 11 + 2089664*fourthLevelSamples 12 - 591952*fourthLevelSamples 13 + 131504*fourthLevelSamples 14 - 21040*fourthLevelSamples 15 + 1728*fourthLevelSamples 16) / 1000000 - (702456) / 1000000000000000 ∧ (15125008*fourthLevelSamples 1 - 16454544*fourthLevelSamples 2 + 12688528*fourthLevelSamples 3 - 6667360*fourthLevelSamples 4 + 2620960*fourthLevelSamples 5 + 1410848*fourthLevelSamples 6 - 8352736*fourthLevelSamples 7 + 14912160*fourthLevelSamples 8 - 15814208*fourthLevelSamples 9 + 11245632*fourthLevelSamples 10 - 5654560*fourthLevelSamples 11 + 2089664*fourthLevelSamples 12 - 591952*fourthLevelSamples 13 + 131504*fourthLevelSamples 14 - 21040*fourthLevelSamples 15 + 1728*fourthLevelSamples 16) / 1000000 - (702456) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_5_5 :
    (123172181/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 5 5 ∧
      fourthLevelEvenSheared fourthLevelSamples 5 5 ≤ (123172182/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (26639808*fourthLevelSamples 1 - 13896496*fourthLevelSamples 2 + 4854880*fourthLevelSamples 3 + 944832*fourthLevelSamples 4 - 8141600*fourthLevelSamples 5 + 14833792*fourthLevelSamples 6 - 16010016*fourthLevelSamples 7 + 11759200*fourthLevelSamples 8 - 6345056*fourthLevelSamples 9 + 2685704*fourthLevelSamples 10 - 935152*fourthLevelSamples 11 + 267896*fourthLevelSamples 12 - 61264*fourthLevelSamples 13 + 11208*fourthLevelSamples 14 - 1600*fourthLevelSamples 15 + 128*fourthLevelSamples 16) / 1000000 - (2288894) / 1000000000000000 ∧ (26639808*fourthLevelSamples 1 - 13896496*fourthLevelSamples 2 + 4854880*fourthLevelSamples 3 + 944832*fourthLevelSamples 4 - 8141600*fourthLevelSamples 5 + 14833792*fourthLevelSamples 6 - 16010016*fourthLevelSamples 7 + 11759200*fourthLevelSamples 8 - 6345056*fourthLevelSamples 9 + 2685704*fourthLevelSamples 10 - 935152*fourthLevelSamples 11 + 267896*fourthLevelSamples 12 - 61264*fourthLevelSamples 13 + 11208*fourthLevelSamples 14 - 1600*fourthLevelSamples 15 + 128*fourthLevelSamples 16) / 1000000 - (2288894) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_5_6 :
    (-20925/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 5 6 ∧
      fourthLevelEvenSheared fourthLevelSamples 5 6 ≤ (-20923/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (18067932*fourthLevelSamples 1 - 16428804*fourthLevelSamples 2 + 5611264*fourthLevelSamples 3 + 8364820*fourthLevelSamples 4 - 15061436*fourthLevelSamples 5 + 12796824*fourthLevelSamples 6 - 7328252*fourthLevelSamples 7 + 3219092*fourthLevelSamples 8 - 1179836*fourthLevelSamples 9 + 374152*fourthLevelSamples 10 - 103796*fourthLevelSamples 11 + 25852*fourthLevelSamples 12 - 5712*fourthLevelSamples 13 + 1060*fourthLevelSamples 14 - 164*fourthLevelSamples 15 + 16*fourthLevelSamples 16) / 1000000 - (894220) / 1000000000000000 ∧ (18067932*fourthLevelSamples 1 - 16428804*fourthLevelSamples 2 + 5611264*fourthLevelSamples 3 + 8364820*fourthLevelSamples 4 - 15061436*fourthLevelSamples 5 + 12796824*fourthLevelSamples 6 - 7328252*fourthLevelSamples 7 + 3219092*fourthLevelSamples 8 - 1179836*fourthLevelSamples 9 + 374152*fourthLevelSamples 10 - 103796*fourthLevelSamples 11 + 25852*fourthLevelSamples 12 - 5712*fourthLevelSamples 13 + 1060*fourthLevelSamples 14 - 164*fourthLevelSamples 15 + 16*fourthLevelSamples 16) / 1000000 - (894220) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_6_0 :
    (593004/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 6 0 ∧
      fourthLevelEvenSheared fourthLevelSamples 6 0 ≤ (593005/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (- 3672000*fourthLevelSamples 1 + 7766000*fourthLevelSamples 2 - 7884000*fourthLevelSamples 3 - 468000*fourthLevelSamples 4 + 9708000*fourthLevelSamples 5 - 11598000*fourthLevelSamples 6 + 7416000*fourthLevelSamples 7 - 944000*fourthLevelSamples 8 - 3736000*fourthLevelSamples 9 + 3798000*fourthLevelSamples 10 - 1692000*fourthLevelSamples 11 + 468000*fourthLevelSamples 12 - 132000*fourthLevelSamples 13 + 34000*fourthLevelSamples 14 - 8000*fourthLevelSamples 15 + 2000*fourthLevelSamples 16) / 1000000 - (-20000) / 1000000000000000 ∧ (- 3672000*fourthLevelSamples 1 + 7766000*fourthLevelSamples 2 - 7884000*fourthLevelSamples 3 - 468000*fourthLevelSamples 4 + 9708000*fourthLevelSamples 5 - 11598000*fourthLevelSamples 6 + 7416000*fourthLevelSamples 7 - 944000*fourthLevelSamples 8 - 3736000*fourthLevelSamples 9 + 3798000*fourthLevelSamples 10 - 1692000*fourthLevelSamples 11 + 468000*fourthLevelSamples 12 - 132000*fourthLevelSamples 13 + 34000*fourthLevelSamples 14 - 8000*fourthLevelSamples 15 + 2000*fourthLevelSamples 16) / 1000000 - (-20000) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_6_1 :
    (982291/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 6 1 ∧
      fourthLevelEvenSheared fourthLevelSamples 6 1 ≤ (982292/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (2210600*fourthLevelSamples 1 - 4345050*fourthLevelSamples 2 + 2103700*fourthLevelSamples 3 + 7339900*fourthLevelSamples 4 - 11990900*fourthLevelSamples 5 + 2029650*fourthLevelSamples 6 + 8994200*fourthLevelSamples 7 - 7094800*fourthLevelSamples 8 - 62200*fourthLevelSamples 9 + 2291350*fourthLevelSamples 10 - 1155900*fourthLevelSamples 11 + 324100*fourthLevelSamples 12 - 92900*fourthLevelSamples 13 + 24050*fourthLevelSamples 14 - 6600*fourthLevelSamples 15 + 1650*fourthLevelSamples 16) / 1000000 - (21500) / 1000000000000000 ∧ (2210600*fourthLevelSamples 1 - 4345050*fourthLevelSamples 2 + 2103700*fourthLevelSamples 3 + 7339900*fourthLevelSamples 4 - 11990900*fourthLevelSamples 5 + 2029650*fourthLevelSamples 6 + 8994200*fourthLevelSamples 7 - 7094800*fourthLevelSamples 8 - 62200*fourthLevelSamples 9 + 2291350*fourthLevelSamples 10 - 1155900*fourthLevelSamples 11 + 324100*fourthLevelSamples 12 - 92900*fourthLevelSamples 13 + 24050*fourthLevelSamples 14 - 6600*fourthLevelSamples 15 + 1650*fourthLevelSamples 16) / 1000000 - (21500) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_6_2 :
    (-707094/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 6 2 ∧
      fourthLevelEvenSheared fourthLevelSamples 6 2 ≤ (-707093/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (- 8011864*fourthLevelSamples 1 - 6134920*fourthLevelSamples 2 + 14069040*fourthLevelSamples 3 - 4706910*fourthLevelSamples 4 - 7138544*fourthLevelSamples 5 + 5929882*fourthLevelSamples 6 + 659428*fourthLevelSamples 7 - 2190164*fourthLevelSamples 8 + 571668*fourthLevelSamples 9 + 202114*fourthLevelSamples 10 - 137504*fourthLevelSamples 11 + 39534*fourthLevelSamples 12 - 11168*fourthLevelSamples 13 + 2924*fourthLevelSamples 14 - 1056*fourthLevelSamples 15 + 264*fourthLevelSamples 16) / 1000000 - (-493782) / 1000000000000000 ∧ (- 8011864*fourthLevelSamples 1 - 6134920*fourthLevelSamples 2 + 14069040*fourthLevelSamples 3 - 4706910*fourthLevelSamples 4 - 7138544*fourthLevelSamples 5 + 5929882*fourthLevelSamples 6 + 659428*fourthLevelSamples 7 - 2190164*fourthLevelSamples 8 + 571668*fourthLevelSamples 9 + 202114*fourthLevelSamples 10 - 137504*fourthLevelSamples 11 + 39534*fourthLevelSamples 12 - 11168*fourthLevelSamples 13 + 2924*fourthLevelSamples 14 - 1056*fourthLevelSamples 15 + 264*fourthLevelSamples 16) / 1000000 - (-493782) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_6_3 :
    (-79005/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 6 3 ∧
      fourthLevelEvenSheared fourthLevelSamples 6 3 ≤ (-79003/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (152128*fourthLevelSamples 1 + 226580*fourthLevelSamples 2 + 1932760*fourthLevelSamples 3 - 9071740*fourthLevelSamples 4 + 16020648*fourthLevelSamples 5 - 12307784*fourthLevelSamples 6 - 2019416*fourthLevelSamples 7 + 13435128*fourthLevelSamples 8 - 13381016*fourthLevelSamples 9 + 7202912*fourthLevelSamples 10 - 2508712*fourthLevelSamples 11 + 692892*fourthLevelSamples 12 - 185944*fourthLevelSamples 13 + 46292*fourthLevelSamples 14 - 10448*fourthLevelSamples 15 + 1612*fourthLevelSamples 16) / 1000000 - (19684) / 1000000000000000 ∧ (152128*fourthLevelSamples 1 + 226580*fourthLevelSamples 2 + 1932760*fourthLevelSamples 3 - 9071740*fourthLevelSamples 4 + 16020648*fourthLevelSamples 5 - 12307784*fourthLevelSamples 6 - 2019416*fourthLevelSamples 7 + 13435128*fourthLevelSamples 8 - 13381016*fourthLevelSamples 9 + 7202912*fourthLevelSamples 10 - 2508712*fourthLevelSamples 11 + 692892*fourthLevelSamples 12 - 185944*fourthLevelSamples 13 + 46292*fourthLevelSamples 14 - 10448*fourthLevelSamples 15 + 1612*fourthLevelSamples 16) / 1000000 - (19684) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_6_4 :
    (45226/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 6 4 ∧
      fourthLevelEvenSheared fourthLevelSamples 6 4 ≤ (45227/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (2073056*fourthLevelSamples 1 - 8513400*fourthLevelSamples 2 + 16077520*fourthLevelSamples 3 - 16159632*fourthLevelSamples 4 + 4977904*fourthLevelSamples 5 + 9219944*fourthLevelSamples 6 - 15570784*fourthLevelSamples 7 + 12679120*fourthLevelSamples 8 - 6728096*fourthLevelSamples 9 + 2567224*fourthLevelSamples 10 - 774640*fourthLevelSamples 11 + 208080*fourthLevelSamples 12 - 52816*fourthLevelSamples 13 + 11992*fourthLevelSamples 14 - 2144*fourthLevelSamples 15 + 216*fourthLevelSamples 16) / 1000000 - (11552) / 1000000000000000 ∧ (2073056*fourthLevelSamples 1 - 8513400*fourthLevelSamples 2 + 16077520*fourthLevelSamples 3 - 16159632*fourthLevelSamples 4 + 4977904*fourthLevelSamples 5 + 9219944*fourthLevelSamples 6 - 15570784*fourthLevelSamples 7 + 12679120*fourthLevelSamples 8 - 6728096*fourthLevelSamples 9 + 2567224*fourthLevelSamples 10 - 774640*fourthLevelSamples 11 + 208080*fourthLevelSamples 12 - 52816*fourthLevelSamples 13 + 11992*fourthLevelSamples 14 - 2144*fourthLevelSamples 15 + 216*fourthLevelSamples 16) / 1000000 - (11552) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_6_5 :
    (-20925/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 6 5 ∧
      fourthLevelEvenSheared fourthLevelSamples 6 5 ≤ (-20923/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (18067932*fourthLevelSamples 1 - 16428804*fourthLevelSamples 2 + 5611264*fourthLevelSamples 3 + 8364820*fourthLevelSamples 4 - 15061436*fourthLevelSamples 5 + 12796824*fourthLevelSamples 6 - 7328252*fourthLevelSamples 7 + 3219092*fourthLevelSamples 8 - 1179836*fourthLevelSamples 9 + 374152*fourthLevelSamples 10 - 103796*fourthLevelSamples 11 + 25852*fourthLevelSamples 12 - 5712*fourthLevelSamples 13 + 1060*fourthLevelSamples 14 - 164*fourthLevelSamples 15 + 16*fourthLevelSamples 16) / 1000000 - (894220) / 1000000000000000 ∧ (18067932*fourthLevelSamples 1 - 16428804*fourthLevelSamples 2 + 5611264*fourthLevelSamples 3 + 8364820*fourthLevelSamples 4 - 15061436*fourthLevelSamples 5 + 12796824*fourthLevelSamples 6 - 7328252*fourthLevelSamples 7 + 3219092*fourthLevelSamples 8 - 1179836*fourthLevelSamples 9 + 374152*fourthLevelSamples 10 - 103796*fourthLevelSamples 11 + 25852*fourthLevelSamples 12 - 5712*fourthLevelSamples 13 + 1060*fourthLevelSamples 14 - 164*fourthLevelSamples 15 + 16*fourthLevelSamples 16) / 1000000 - (894220) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

theorem fourthLevelEvenSheared_bounds_6_6 :
    (157308780/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples 6 6 ∧
      fourthLevelEvenSheared fourthLevelSamples 6 6 ≤ (157308781/1000000000000000 : ℝ) := by
  rw [fourthLevelEvenSheared_apply]
  change _ ≤ (22940384*fourthLevelSamples 1 - 899380*fourthLevelSamples 2 - 13003576*fourthLevelSamples 3 + 13630926*fourthLevelSamples 4 - 8320784*fourthLevelSamples 5 + 3771652*fourthLevelSamples 6 - 1444488*fourthLevelSamples 7 + 500292*fourthLevelSamples 8 - 159304*fourthLevelSamples 9 + 46156*fourthLevelSamples 10 - 11680*fourthLevelSamples 11 + 2578*fourthLevelSamples 12 - 536*fourthLevelSamples 13 + 100*fourthLevelSamples 14 - 16*fourthLevelSamples 15 + 2*fourthLevelSamples 16) / 1000000 - (2495224) / 1000000000000000 ∧ (22940384*fourthLevelSamples 1 - 899380*fourthLevelSamples 2 - 13003576*fourthLevelSamples 3 + 13630926*fourthLevelSamples 4 - 8320784*fourthLevelSamples 5 + 3771652*fourthLevelSamples 6 - 1444488*fourthLevelSamples 7 + 500292*fourthLevelSamples 8 - 159304*fourthLevelSamples 9 + 46156*fourthLevelSamples 10 - 11680*fourthLevelSamples 11 + 2578*fourthLevelSamples 12 - 536*fourthLevelSamples 13 + 100*fourthLevelSamples 14 - 16*fourthLevelSamples 15 + 2*fourthLevelSamples 16) / 1000000 - (2495224) / 1000000000000000 ≤ _
  constructor
  · linarith only [(fourthLevelSamples_1_bounds).1, (fourthLevelSamples_2_bounds).2, (fourthLevelSamples_3_bounds).2, (fourthLevelSamples_4_bounds).1, (fourthLevelSamples_5_bounds).2, (fourthLevelSamples_6_bounds).1, (fourthLevelSamples_7_bounds).2, (fourthLevelSamples_8_bounds).1, (fourthLevelSamples_9_bounds).2, (fourthLevelSamples_10_bounds).1, (fourthLevelSamples_11_bounds).2, (fourthLevelSamples_12_bounds).1, (fourthLevelSamples_13_bounds).2, (fourthLevelSamples_14_bounds).1, (fourthLevelSamples_15_bounds).2, (fourthLevelSamples_16_bounds).1]
  · linarith only [(fourthLevelSamples_1_bounds).2, (fourthLevelSamples_2_bounds).1, (fourthLevelSamples_3_bounds).1, (fourthLevelSamples_4_bounds).2, (fourthLevelSamples_5_bounds).1, (fourthLevelSamples_6_bounds).2, (fourthLevelSamples_7_bounds).1, (fourthLevelSamples_8_bounds).2, (fourthLevelSamples_9_bounds).1, (fourthLevelSamples_10_bounds).2, (fourthLevelSamples_11_bounds).1, (fourthLevelSamples_12_bounds).2, (fourthLevelSamples_13_bounds).1, (fourthLevelSamples_14_bounds).2, (fourthLevelSamples_15_bounds).1, (fourthLevelSamples_16_bounds).2]

def fourthLevelEvenLower : Matrix (Fin 7) (Fin 7) ℝ :=
  ![![15247517099,5910960,1223509,-8303104,-5678535,-4538860,593004],
  ![5910960,1464602222,116326,-259659,-896744,-362134,982291],
  ![1223509,116326,1271977102,-189715,396835,-467726,-707094],
  ![-8303104,-259659,-189715,179467983,-41450,12702,-79005],
  ![-5678535,-896744,396835,-41450,120870574,29791,45226],
  ![-4538860,-362134,-467726,12702,29791,123172181,-20925],
  ![593004,982291,-707094,-79005,45226,-20925,157308780]]

def fourthLevelEvenUpper : Matrix (Fin 7) (Fin 7) ℝ :=
  ![![15247517100,5910961,1223510,-8303103,-5678534,-4538859,593005],
  ![5910961,1464602223,116327,-259658,-896743,-362133,982292],
  ![1223510,116327,1271977103,-189713,396836,-467725,-707093],
  ![-8303103,-259658,-189713,179467984,-41449,12703,-79003],
  ![-5678534,-896743,396836,-41449,120870575,29792,45227],
  ![-4538859,-362133,-467725,12703,29792,123172182,-20923],
  ![593005,982292,-707093,-79003,45227,-20923,157308781]]

theorem fourthLevelEvenSheared_bounds_row0 (j : Fin 7) :
    fourthLevelEvenLower 0 j / 1000000000000000 ≤ fourthLevelEvenSheared fourthLevelSamples 0 j ∧
      fourthLevelEvenSheared fourthLevelSamples 0 j ≤ fourthLevelEvenUpper 0 j / 1000000000000000 := by
  fin_cases j
  · exact fourthLevelEvenSheared_bounds_0_0
  · exact fourthLevelEvenSheared_bounds_0_1
  · exact fourthLevelEvenSheared_bounds_0_2
  · exact fourthLevelEvenSheared_bounds_0_3
  · exact fourthLevelEvenSheared_bounds_0_4
  · exact fourthLevelEvenSheared_bounds_0_5
  · exact fourthLevelEvenSheared_bounds_0_6

theorem fourthLevelEvenSheared_bounds_row1 (j : Fin 7) :
    fourthLevelEvenLower 1 j / 1000000000000000 ≤ fourthLevelEvenSheared fourthLevelSamples 1 j ∧
      fourthLevelEvenSheared fourthLevelSamples 1 j ≤ fourthLevelEvenUpper 1 j / 1000000000000000 := by
  fin_cases j
  · exact fourthLevelEvenSheared_bounds_1_0
  · exact fourthLevelEvenSheared_bounds_1_1
  · exact fourthLevelEvenSheared_bounds_1_2
  · exact fourthLevelEvenSheared_bounds_1_3
  · exact fourthLevelEvenSheared_bounds_1_4
  · exact fourthLevelEvenSheared_bounds_1_5
  · exact fourthLevelEvenSheared_bounds_1_6

theorem fourthLevelEvenSheared_bounds_row2 (j : Fin 7) :
    fourthLevelEvenLower 2 j / 1000000000000000 ≤ fourthLevelEvenSheared fourthLevelSamples 2 j ∧
      fourthLevelEvenSheared fourthLevelSamples 2 j ≤ fourthLevelEvenUpper 2 j / 1000000000000000 := by
  fin_cases j
  · exact fourthLevelEvenSheared_bounds_2_0
  · exact fourthLevelEvenSheared_bounds_2_1
  · exact fourthLevelEvenSheared_bounds_2_2
  · exact fourthLevelEvenSheared_bounds_2_3
  · exact fourthLevelEvenSheared_bounds_2_4
  · exact fourthLevelEvenSheared_bounds_2_5
  · exact fourthLevelEvenSheared_bounds_2_6

theorem fourthLevelEvenSheared_bounds_row3 (j : Fin 7) :
    fourthLevelEvenLower 3 j / 1000000000000000 ≤ fourthLevelEvenSheared fourthLevelSamples 3 j ∧
      fourthLevelEvenSheared fourthLevelSamples 3 j ≤ fourthLevelEvenUpper 3 j / 1000000000000000 := by
  fin_cases j
  · exact fourthLevelEvenSheared_bounds_3_0
  · exact fourthLevelEvenSheared_bounds_3_1
  · exact fourthLevelEvenSheared_bounds_3_2
  · exact fourthLevelEvenSheared_bounds_3_3
  · exact fourthLevelEvenSheared_bounds_3_4
  · exact fourthLevelEvenSheared_bounds_3_5
  · exact fourthLevelEvenSheared_bounds_3_6

theorem fourthLevelEvenSheared_bounds_row4 (j : Fin 7) :
    fourthLevelEvenLower 4 j / 1000000000000000 ≤ fourthLevelEvenSheared fourthLevelSamples 4 j ∧
      fourthLevelEvenSheared fourthLevelSamples 4 j ≤ fourthLevelEvenUpper 4 j / 1000000000000000 := by
  fin_cases j
  · exact fourthLevelEvenSheared_bounds_4_0
  · exact fourthLevelEvenSheared_bounds_4_1
  · exact fourthLevelEvenSheared_bounds_4_2
  · exact fourthLevelEvenSheared_bounds_4_3
  · exact fourthLevelEvenSheared_bounds_4_4
  · exact fourthLevelEvenSheared_bounds_4_5
  · exact fourthLevelEvenSheared_bounds_4_6

theorem fourthLevelEvenSheared_bounds_row5 (j : Fin 7) :
    fourthLevelEvenLower 5 j / 1000000000000000 ≤ fourthLevelEvenSheared fourthLevelSamples 5 j ∧
      fourthLevelEvenSheared fourthLevelSamples 5 j ≤ fourthLevelEvenUpper 5 j / 1000000000000000 := by
  fin_cases j
  · exact fourthLevelEvenSheared_bounds_5_0
  · exact fourthLevelEvenSheared_bounds_5_1
  · exact fourthLevelEvenSheared_bounds_5_2
  · exact fourthLevelEvenSheared_bounds_5_3
  · exact fourthLevelEvenSheared_bounds_5_4
  · exact fourthLevelEvenSheared_bounds_5_5
  · exact fourthLevelEvenSheared_bounds_5_6

theorem fourthLevelEvenSheared_bounds_row6 (j : Fin 7) :
    fourthLevelEvenLower 6 j / 1000000000000000 ≤ fourthLevelEvenSheared fourthLevelSamples 6 j ∧
      fourthLevelEvenSheared fourthLevelSamples 6 j ≤ fourthLevelEvenUpper 6 j / 1000000000000000 := by
  fin_cases j
  · exact fourthLevelEvenSheared_bounds_6_0
  · exact fourthLevelEvenSheared_bounds_6_1
  · exact fourthLevelEvenSheared_bounds_6_2
  · exact fourthLevelEvenSheared_bounds_6_3
  · exact fourthLevelEvenSheared_bounds_6_4
  · exact fourthLevelEvenSheared_bounds_6_5
  · exact fourthLevelEvenSheared_bounds_6_6

theorem fourthLevelEvenSheared_bounds (i j : Fin 7) :
    fourthLevelEvenLower i j / 1000000000000000 ≤ fourthLevelEvenSheared fourthLevelSamples i j ∧
      fourthLevelEvenSheared fourthLevelSamples i j ≤ fourthLevelEvenUpper i j / 1000000000000000 := by
  fin_cases i
  · exact fourthLevelEvenSheared_bounds_row0 j
  · exact fourthLevelEvenSheared_bounds_row1 j
  · exact fourthLevelEvenSheared_bounds_row2 j
  · exact fourthLevelEvenSheared_bounds_row3 j
  · exact fourthLevelEvenSheared_bounds_row4 j
  · exact fourthLevelEvenSheared_bounds_row5 j
  · exact fourthLevelEvenSheared_bounds_row6 j


theorem abs_le_max_abs_of_bounds {l x u : ℝ} (h : l ≤ x ∧ x ≤ u) :
    |x| ≤ max |l| |u| := by
  apply abs_le.mpr
  constructor
  · have hl : -|l| ≤ l := neg_abs_le l
    have hm : |l| ≤ max |l| |u| := le_max_left _ _
    linarith [h.1]
  · exact h.2.trans ((le_abs_self u).trans (le_max_right _ _))
def fourthLevelOddAbsUpper (i j : Fin 8) : ℝ :=
  max |fourthLevelOddLower i j / 1000000000000000|
    |fourthLevelOddUpper i j / 1000000000000000|

def fourthLevelEvenAbsUpper (i j : Fin 7) : ℝ :=
  max |fourthLevelEvenLower i j / 1000000000000000|
    |fourthLevelEvenUpper i j / 1000000000000000|

theorem fourthLevelOddRowMargin_0 :
    (∑ j ∈ Finset.univ.erase (0 : Fin 8), fourthLevelOddAbsUpper 0 j) +
      (77351005/1000000000000000 : ℝ) ≤ fourthLevelOddLower 0 0 / 1000000000000000 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (max |(30453883906 : ℝ) / 1000000000000000| |(30453883907 : ℝ) / 1000000000000000| + (max |(-10787574 : ℝ) / 1000000000000000| |(-10787573 : ℝ) / 1000000000000000| + (max |(2727010 : ℝ) / 1000000000000000| |(2727011 : ℝ) / 1000000000000000| + (max |(-2910795 : ℝ) / 1000000000000000| |(-2910794 : ℝ) / 1000000000000000| + (max |(175218 : ℝ) / 1000000000000000| |(175220 : ℝ) / 1000000000000000| + (max |(-12553761 : ℝ) / 1000000000000000| |(-12553760 : ℝ) / 1000000000000000| + (max |(-7176680 : ℝ) / 1000000000000000| |(-7176679 : ℝ) / 1000000000000000| + (max |(-2031579 : ℝ) / 1000000000000000| |(-2031578 : ℝ) / 1000000000000000| + (0))))))))) - (max |(30453883906 : ℝ) / 1000000000000000| |(30453883907 : ℝ) / 1000000000000000|) + _ ≤ (30453883906 : ℝ) / 1000000000000000
  norm_num

theorem fourthLevelOddRowMargin_1 :
    (∑ j ∈ Finset.univ.erase (1 : Fin 8), fourthLevelOddAbsUpper 1 j) +
      (77351005/1000000000000000 : ℝ) ≤ fourthLevelOddLower 1 1 / 1000000000000000 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (max |(-10787574 : ℝ) / 1000000000000000| |(-10787573 : ℝ) / 1000000000000000| + (max |(6302577996 : ℝ) / 1000000000000000| |(6302577997 : ℝ) / 1000000000000000| + (max |(-2742984 : ℝ) / 1000000000000000| |(-2742983 : ℝ) / 1000000000000000| + (max |(-1742475 : ℝ) / 1000000000000000| |(-1742474 : ℝ) / 1000000000000000| + (max |(906415 : ℝ) / 1000000000000000| |(906416 : ℝ) / 1000000000000000| + (max |(-1467056 : ℝ) / 1000000000000000| |(-1467055 : ℝ) / 1000000000000000| + (max |(2249943 : ℝ) / 1000000000000000| |(2249944 : ℝ) / 1000000000000000| + (max |(1571591 : ℝ) / 1000000000000000| |(1571592 : ℝ) / 1000000000000000| + (0))))))))) - (max |(6302577996 : ℝ) / 1000000000000000| |(6302577997 : ℝ) / 1000000000000000|) + _ ≤ (6302577996 : ℝ) / 1000000000000000
  norm_num

theorem fourthLevelOddRowMargin_2 :
    (∑ j ∈ Finset.univ.erase (2 : Fin 8), fourthLevelOddAbsUpper 2 j) +
      (77351005/1000000000000000 : ℝ) ≤ fourthLevelOddLower 2 2 / 1000000000000000 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (max |(2727010 : ℝ) / 1000000000000000| |(2727011 : ℝ) / 1000000000000000| + (max |(-2742984 : ℝ) / 1000000000000000| |(-2742983 : ℝ) / 1000000000000000| + (max |(1286281916 : ℝ) / 1000000000000000| |(1286281917 : ℝ) / 1000000000000000| + (max |(507146 : ℝ) / 1000000000000000| |(507147 : ℝ) / 1000000000000000| + (max |(-580301 : ℝ) / 1000000000000000| |(-580300 : ℝ) / 1000000000000000| + (max |(-258988 : ℝ) / 1000000000000000| |(-258987 : ℝ) / 1000000000000000| + (max |(-551390 : ℝ) / 1000000000000000| |(-551389 : ℝ) / 1000000000000000| + (max |(-500781 : ℝ) / 1000000000000000| |(-500780 : ℝ) / 1000000000000000| + (0))))))))) - (max |(1286281916 : ℝ) / 1000000000000000| |(1286281917 : ℝ) / 1000000000000000|) + _ ≤ (1286281916 : ℝ) / 1000000000000000
  norm_num

theorem fourthLevelOddRowMargin_3 :
    (∑ j ∈ Finset.univ.erase (3 : Fin 8), fourthLevelOddAbsUpper 3 j) +
      (77351005/1000000000000000 : ℝ) ≤ fourthLevelOddLower 3 3 / 1000000000000000 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (max |(-2910795 : ℝ) / 1000000000000000| |(-2910794 : ℝ) / 1000000000000000| + (max |(-1742475 : ℝ) / 1000000000000000| |(-1742474 : ℝ) / 1000000000000000| + (max |(507146 : ℝ) / 1000000000000000| |(507147 : ℝ) / 1000000000000000| + (max |(667841601 : ℝ) / 1000000000000000| |(667841602 : ℝ) / 1000000000000000| + (max |(145746 : ℝ) / 1000000000000000| |(145747 : ℝ) / 1000000000000000| + (max |(-293211 : ℝ) / 1000000000000000| |(-293210 : ℝ) / 1000000000000000| + (max |(190902 : ℝ) / 1000000000000000| |(190903 : ℝ) / 1000000000000000| + (max |(173555 : ℝ) / 1000000000000000| |(173556 : ℝ) / 1000000000000000| + (0))))))))) - (max |(667841601 : ℝ) / 1000000000000000| |(667841602 : ℝ) / 1000000000000000|) + _ ≤ (667841601 : ℝ) / 1000000000000000
  norm_num

theorem fourthLevelOddRowMargin_4 :
    (∑ j ∈ Finset.univ.erase (4 : Fin 8), fourthLevelOddAbsUpper 4 j) +
      (77351005/1000000000000000 : ℝ) ≤ fourthLevelOddLower 4 4 / 1000000000000000 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (max |(175218 : ℝ) / 1000000000000000| |(175220 : ℝ) / 1000000000000000| + (max |(906415 : ℝ) / 1000000000000000| |(906416 : ℝ) / 1000000000000000| + (max |(-580301 : ℝ) / 1000000000000000| |(-580300 : ℝ) / 1000000000000000| + (max |(145746 : ℝ) / 1000000000000000| |(145747 : ℝ) / 1000000000000000| + (max |(172104152 : ℝ) / 1000000000000000| |(172104153 : ℝ) / 1000000000000000| + (max |(56364 : ℝ) / 1000000000000000| |(56365 : ℝ) / 1000000000000000| + (max |(-61226 : ℝ) / 1000000000000000| |(-61225 : ℝ) / 1000000000000000| + (max |(-86391 : ℝ) / 1000000000000000| |(-86390 : ℝ) / 1000000000000000| + (0))))))))) - (max |(172104152 : ℝ) / 1000000000000000| |(172104153 : ℝ) / 1000000000000000|) + _ ≤ (172104152 : ℝ) / 1000000000000000
  norm_num

theorem fourthLevelOddRowMargin_5 :
    (∑ j ∈ Finset.univ.erase (5 : Fin 8), fourthLevelOddAbsUpper 5 j) +
      (77351005/1000000000000000 : ℝ) ≤ fourthLevelOddLower 5 5 / 1000000000000000 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (max |(-12553761 : ℝ) / 1000000000000000| |(-12553760 : ℝ) / 1000000000000000| + (max |(-1467056 : ℝ) / 1000000000000000| |(-1467055 : ℝ) / 1000000000000000| + (max |(-258988 : ℝ) / 1000000000000000| |(-258987 : ℝ) / 1000000000000000| + (max |(-293211 : ℝ) / 1000000000000000| |(-293210 : ℝ) / 1000000000000000| + (max |(56364 : ℝ) / 1000000000000000| |(56365 : ℝ) / 1000000000000000| + (max |(120457812 : ℝ) / 1000000000000000| |(120457813 : ℝ) / 1000000000000000| + (max |(44527 : ℝ) / 1000000000000000| |(44528 : ℝ) / 1000000000000000| + (max |(3247 : ℝ) / 1000000000000000| |(3248 : ℝ) / 1000000000000000| + (0))))))))) - (max |(120457812 : ℝ) / 1000000000000000| |(120457813 : ℝ) / 1000000000000000|) + _ ≤ (120457812 : ℝ) / 1000000000000000
  norm_num

theorem fourthLevelOddRowMargin_6 :
    (∑ j ∈ Finset.univ.erase (6 : Fin 8), fourthLevelOddAbsUpper 6 j) +
      (77351005/1000000000000000 : ℝ) ≤ fourthLevelOddLower 6 6 / 1000000000000000 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (max |(-7176680 : ℝ) / 1000000000000000| |(-7176679 : ℝ) / 1000000000000000| + (max |(2249943 : ℝ) / 1000000000000000| |(2249944 : ℝ) / 1000000000000000| + (max |(-551390 : ℝ) / 1000000000000000| |(-551389 : ℝ) / 1000000000000000| + (max |(190902 : ℝ) / 1000000000000000| |(190903 : ℝ) / 1000000000000000| + (max |(-61226 : ℝ) / 1000000000000000| |(-61225 : ℝ) / 1000000000000000| + (max |(44527 : ℝ) / 1000000000000000| |(44528 : ℝ) / 1000000000000000| + (max |(117737745 : ℝ) / 1000000000000000| |(117737746 : ℝ) / 1000000000000000| + (max |(17143 : ℝ) / 1000000000000000| |(17144 : ℝ) / 1000000000000000| + (0))))))))) - (max |(117737745 : ℝ) / 1000000000000000| |(117737746 : ℝ) / 1000000000000000|) + _ ≤ (117737745 : ℝ) / 1000000000000000
  norm_num

theorem fourthLevelOddRowMargin_7 :
    (∑ j ∈ Finset.univ.erase (7 : Fin 8), fourthLevelOddAbsUpper 7 j) +
      (77351005/1000000000000000 : ℝ) ≤ fourthLevelOddLower 7 7 / 1000000000000000 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (max |(-2031579 : ℝ) / 1000000000000000| |(-2031578 : ℝ) / 1000000000000000| + (max |(1571591 : ℝ) / 1000000000000000| |(1571592 : ℝ) / 1000000000000000| + (max |(-500781 : ℝ) / 1000000000000000| |(-500780 : ℝ) / 1000000000000000| + (max |(173555 : ℝ) / 1000000000000000| |(173556 : ℝ) / 1000000000000000| + (max |(-86391 : ℝ) / 1000000000000000| |(-86390 : ℝ) / 1000000000000000| + (max |(3247 : ℝ) / 1000000000000000| |(3248 : ℝ) / 1000000000000000| + (max |(17143 : ℝ) / 1000000000000000| |(17144 : ℝ) / 1000000000000000| + (max |(81735296 : ℝ) / 1000000000000000| |(81735297 : ℝ) / 1000000000000000| + (0))))))))) - (max |(81735296 : ℝ) / 1000000000000000| |(81735297 : ℝ) / 1000000000000000|) + _ ≤ (81735296 : ℝ) / 1000000000000000
  norm_num

theorem fourthLevelEvenRowMargin_0 :
    (∑ j ∈ Finset.univ.erase (0 : Fin 7), fourthLevelEvenAbsUpper 0 j) +
      (113781990/1000000000000000 : ℝ) ≤ fourthLevelEvenLower 0 0 / 1000000000000000 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (max |(15247517099 : ℝ) / 1000000000000000| |(15247517100 : ℝ) / 1000000000000000| + (max |(5910960 : ℝ) / 1000000000000000| |(5910961 : ℝ) / 1000000000000000| + (max |(1223509 : ℝ) / 1000000000000000| |(1223510 : ℝ) / 1000000000000000| + (max |(-8303104 : ℝ) / 1000000000000000| |(-8303103 : ℝ) / 1000000000000000| + (max |(-5678535 : ℝ) / 1000000000000000| |(-5678534 : ℝ) / 1000000000000000| + (max |(-4538860 : ℝ) / 1000000000000000| |(-4538859 : ℝ) / 1000000000000000| + (max |(593004 : ℝ) / 1000000000000000| |(593005 : ℝ) / 1000000000000000| + (0)))))))) - (max |(15247517099 : ℝ) / 1000000000000000| |(15247517100 : ℝ) / 1000000000000000|) + _ ≤ (15247517099 : ℝ) / 1000000000000000
  norm_num

theorem fourthLevelEvenRowMargin_1 :
    (∑ j ∈ Finset.univ.erase (1 : Fin 7), fourthLevelEvenAbsUpper 1 j) +
      (113781990/1000000000000000 : ℝ) ≤ fourthLevelEvenLower 1 1 / 1000000000000000 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (max |(5910960 : ℝ) / 1000000000000000| |(5910961 : ℝ) / 1000000000000000| + (max |(1464602222 : ℝ) / 1000000000000000| |(1464602223 : ℝ) / 1000000000000000| + (max |(116326 : ℝ) / 1000000000000000| |(116327 : ℝ) / 1000000000000000| + (max |(-259659 : ℝ) / 1000000000000000| |(-259658 : ℝ) / 1000000000000000| + (max |(-896744 : ℝ) / 1000000000000000| |(-896743 : ℝ) / 1000000000000000| + (max |(-362134 : ℝ) / 1000000000000000| |(-362133 : ℝ) / 1000000000000000| + (max |(982291 : ℝ) / 1000000000000000| |(982292 : ℝ) / 1000000000000000| + (0)))))))) - (max |(1464602222 : ℝ) / 1000000000000000| |(1464602223 : ℝ) / 1000000000000000|) + _ ≤ (1464602222 : ℝ) / 1000000000000000
  norm_num

theorem fourthLevelEvenRowMargin_2 :
    (∑ j ∈ Finset.univ.erase (2 : Fin 7), fourthLevelEvenAbsUpper 2 j) +
      (113781990/1000000000000000 : ℝ) ≤ fourthLevelEvenLower 2 2 / 1000000000000000 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (max |(1223509 : ℝ) / 1000000000000000| |(1223510 : ℝ) / 1000000000000000| + (max |(116326 : ℝ) / 1000000000000000| |(116327 : ℝ) / 1000000000000000| + (max |(1271977102 : ℝ) / 1000000000000000| |(1271977103 : ℝ) / 1000000000000000| + (max |(-189715 : ℝ) / 1000000000000000| |(-189713 : ℝ) / 1000000000000000| + (max |(396835 : ℝ) / 1000000000000000| |(396836 : ℝ) / 1000000000000000| + (max |(-467726 : ℝ) / 1000000000000000| |(-467725 : ℝ) / 1000000000000000| + (max |(-707094 : ℝ) / 1000000000000000| |(-707093 : ℝ) / 1000000000000000| + (0)))))))) - (max |(1271977102 : ℝ) / 1000000000000000| |(1271977103 : ℝ) / 1000000000000000|) + _ ≤ (1271977102 : ℝ) / 1000000000000000
  norm_num

theorem fourthLevelEvenRowMargin_3 :
    (∑ j ∈ Finset.univ.erase (3 : Fin 7), fourthLevelEvenAbsUpper 3 j) +
      (113781990/1000000000000000 : ℝ) ≤ fourthLevelEvenLower 3 3 / 1000000000000000 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (max |(-8303104 : ℝ) / 1000000000000000| |(-8303103 : ℝ) / 1000000000000000| + (max |(-259659 : ℝ) / 1000000000000000| |(-259658 : ℝ) / 1000000000000000| + (max |(-189715 : ℝ) / 1000000000000000| |(-189713 : ℝ) / 1000000000000000| + (max |(179467983 : ℝ) / 1000000000000000| |(179467984 : ℝ) / 1000000000000000| + (max |(-41450 : ℝ) / 1000000000000000| |(-41449 : ℝ) / 1000000000000000| + (max |(12702 : ℝ) / 1000000000000000| |(12703 : ℝ) / 1000000000000000| + (max |(-79005 : ℝ) / 1000000000000000| |(-79003 : ℝ) / 1000000000000000| + (0)))))))) - (max |(179467983 : ℝ) / 1000000000000000| |(179467984 : ℝ) / 1000000000000000|) + _ ≤ (179467983 : ℝ) / 1000000000000000
  norm_num

theorem fourthLevelEvenRowMargin_4 :
    (∑ j ∈ Finset.univ.erase (4 : Fin 7), fourthLevelEvenAbsUpper 4 j) +
      (113781990/1000000000000000 : ℝ) ≤ fourthLevelEvenLower 4 4 / 1000000000000000 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (max |(-5678535 : ℝ) / 1000000000000000| |(-5678534 : ℝ) / 1000000000000000| + (max |(-896744 : ℝ) / 1000000000000000| |(-896743 : ℝ) / 1000000000000000| + (max |(396835 : ℝ) / 1000000000000000| |(396836 : ℝ) / 1000000000000000| + (max |(-41450 : ℝ) / 1000000000000000| |(-41449 : ℝ) / 1000000000000000| + (max |(120870574 : ℝ) / 1000000000000000| |(120870575 : ℝ) / 1000000000000000| + (max |(29791 : ℝ) / 1000000000000000| |(29792 : ℝ) / 1000000000000000| + (max |(45226 : ℝ) / 1000000000000000| |(45227 : ℝ) / 1000000000000000| + (0)))))))) - (max |(120870574 : ℝ) / 1000000000000000| |(120870575 : ℝ) / 1000000000000000|) + _ ≤ (120870574 : ℝ) / 1000000000000000
  norm_num

theorem fourthLevelEvenRowMargin_5 :
    (∑ j ∈ Finset.univ.erase (5 : Fin 7), fourthLevelEvenAbsUpper 5 j) +
      (113781990/1000000000000000 : ℝ) ≤ fourthLevelEvenLower 5 5 / 1000000000000000 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (max |(-4538860 : ℝ) / 1000000000000000| |(-4538859 : ℝ) / 1000000000000000| + (max |(-362134 : ℝ) / 1000000000000000| |(-362133 : ℝ) / 1000000000000000| + (max |(-467726 : ℝ) / 1000000000000000| |(-467725 : ℝ) / 1000000000000000| + (max |(12702 : ℝ) / 1000000000000000| |(12703 : ℝ) / 1000000000000000| + (max |(29791 : ℝ) / 1000000000000000| |(29792 : ℝ) / 1000000000000000| + (max |(123172181 : ℝ) / 1000000000000000| |(123172182 : ℝ) / 1000000000000000| + (max |(-20925 : ℝ) / 1000000000000000| |(-20923 : ℝ) / 1000000000000000| + (0)))))))) - (max |(123172181 : ℝ) / 1000000000000000| |(123172182 : ℝ) / 1000000000000000|) + _ ≤ (123172181 : ℝ) / 1000000000000000
  norm_num

theorem fourthLevelEvenRowMargin_6 :
    (∑ j ∈ Finset.univ.erase (6 : Fin 7), fourthLevelEvenAbsUpper 6 j) +
      (113781990/1000000000000000 : ℝ) ≤ fourthLevelEvenLower 6 6 / 1000000000000000 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (max |(593004 : ℝ) / 1000000000000000| |(593005 : ℝ) / 1000000000000000| + (max |(982291 : ℝ) / 1000000000000000| |(982292 : ℝ) / 1000000000000000| + (max |(-707094 : ℝ) / 1000000000000000| |(-707093 : ℝ) / 1000000000000000| + (max |(-79005 : ℝ) / 1000000000000000| |(-79003 : ℝ) / 1000000000000000| + (max |(45226 : ℝ) / 1000000000000000| |(45227 : ℝ) / 1000000000000000| + (max |(-20925 : ℝ) / 1000000000000000| |(-20923 : ℝ) / 1000000000000000| + (max |(157308780 : ℝ) / 1000000000000000| |(157308781 : ℝ) / 1000000000000000| + (0)))))))) - (max |(157308780 : ℝ) / 1000000000000000| |(157308781 : ℝ) / 1000000000000000|) + _ ≤ (157308780 : ℝ) / 1000000000000000
  norm_num

theorem fourthLevelOddRowMargin (i : Fin 8) :
    (∑ j ∈ Finset.univ.erase i, fourthLevelOddAbsUpper i j) +
      (77351005/1000000000000000 : ℝ) ≤ fourthLevelOddLower i i / 1000000000000000 := by
  fin_cases i
  · exact fourthLevelOddRowMargin_0
  · exact fourthLevelOddRowMargin_1
  · exact fourthLevelOddRowMargin_2
  · exact fourthLevelOddRowMargin_3
  · exact fourthLevelOddRowMargin_4
  · exact fourthLevelOddRowMargin_5
  · exact fourthLevelOddRowMargin_6
  · exact fourthLevelOddRowMargin_7

theorem fourthLevelOddSheared_abs_le (i j : Fin 8) :
    ‖fourthLevelOddSheared fourthLevelSamples i j‖ ≤ fourthLevelOddAbsUpper i j := by
  rw [Real.norm_eq_abs]
  exact abs_le_max_abs_of_bounds (fourthLevelOddSheared_bounds i j)

theorem fourthLevelOddSheared_rowMargin (i : Fin 8) :
    StrictDiagonalDominance.offDiagonalRowSum (fourthLevelOddSheared fourthLevelSamples) i +
      (77351005/1000000000000000 : ℝ) ≤ fourthLevelOddSheared fourthLevelSamples i i := by
  have hr : StrictDiagonalDominance.offDiagonalRowSum (fourthLevelOddSheared fourthLevelSamples) i ≤
      ∑ j ∈ Finset.univ.erase i, fourthLevelOddAbsUpper i j := by
    apply Finset.sum_le_sum
    intro j hj
    exact fourthLevelOddSheared_abs_le i j
  have hc := fourthLevelOddRowMargin i
  have hd := (fourthLevelOddSheared_bounds i i).1
  linarith only [hr,hc,hd]

theorem fourthLevelOddSheared_posDef :
    (fourthLevelOddSheared fourthLevelSamples).PosDef := by
  apply StrictDiagonalDominance.posDef_of_strictlyRowDiagonallyDominant
    (fourthLevelOddSheared_isHermitian _)
  intro i
  have h := fourthLevelOddSheared_rowMargin i
  linarith only [h]

theorem fourthLevelEvenRowMargin (i : Fin 7) :
    (∑ j ∈ Finset.univ.erase i, fourthLevelEvenAbsUpper i j) +
      (113781990/1000000000000000 : ℝ) ≤ fourthLevelEvenLower i i / 1000000000000000 := by
  fin_cases i
  · exact fourthLevelEvenRowMargin_0
  · exact fourthLevelEvenRowMargin_1
  · exact fourthLevelEvenRowMargin_2
  · exact fourthLevelEvenRowMargin_3
  · exact fourthLevelEvenRowMargin_4
  · exact fourthLevelEvenRowMargin_5
  · exact fourthLevelEvenRowMargin_6

theorem fourthLevelEvenSheared_abs_le (i j : Fin 7) :
    ‖fourthLevelEvenSheared fourthLevelSamples i j‖ ≤ fourthLevelEvenAbsUpper i j := by
  rw [Real.norm_eq_abs]
  exact abs_le_max_abs_of_bounds (fourthLevelEvenSheared_bounds i j)

theorem fourthLevelEvenSheared_rowMargin (i : Fin 7) :
    StrictDiagonalDominance.offDiagonalRowSum (fourthLevelEvenSheared fourthLevelSamples) i +
      (113781990/1000000000000000 : ℝ) ≤ fourthLevelEvenSheared fourthLevelSamples i i := by
  have hr : StrictDiagonalDominance.offDiagonalRowSum (fourthLevelEvenSheared fourthLevelSamples) i ≤
      ∑ j ∈ Finset.univ.erase i, fourthLevelEvenAbsUpper i j := by
    apply Finset.sum_le_sum
    intro j hj
    exact fourthLevelEvenSheared_abs_le i j
  have hc := fourthLevelEvenRowMargin i
  have hd := (fourthLevelEvenSheared_bounds i i).1
  linarith only [hr,hc,hd]

theorem fourthLevelEvenSheared_posDef :
    (fourthLevelEvenSheared fourthLevelSamples).PosDef := by
  apply StrictDiagonalDominance.posDef_of_strictlyRowDiagonallyDominant
    (fourthLevelEvenSheared_isHermitian _)
  intro i
  have h := fourthLevelEvenSheared_rowMargin i
  linarith only [h]

theorem fourthLevelOddShear_upperTriangular :
    fourthLevelOddShear.IsUpperTriangular := by
  intro i j hij
  change j < i at hij
  simp only [fourthLevelOddShear, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;>
    norm_num [fourthLevelOddShearNumerator, Fin.lt_def] at *

theorem fourthLevelOddShear_diagonal (i : Fin 8) : fourthLevelOddShear i i = 1 := by
  simp only [fourthLevelOddShear, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> norm_num [fourthLevelOddShearNumerator]

theorem fourthLevelOddShear_det : fourthLevelOddShear.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular fourthLevelOddShear_upperTriangular]
  simp only [fourthLevelOddShear_diagonal, Finset.prod_const_one]

theorem fourthLevelOddShear_isUnit : IsUnit fourthLevelOddShear := by
  rw [Matrix.isUnit_iff_isUnit_det, fourthLevelOddShear_det]
  exact isUnit_one

theorem fourthLevelEvenShear_upperTriangular :
    fourthLevelEvenShear.IsUpperTriangular := by
  intro i j hij
  change j < i at hij
  simp only [fourthLevelEvenShear, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;>
    norm_num [fourthLevelEvenShearNumerator, Fin.lt_def] at *

theorem fourthLevelEvenShear_diagonal (i : Fin 7) : fourthLevelEvenShear i i = 1 := by
  simp only [fourthLevelEvenShear, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> norm_num [fourthLevelEvenShearNumerator]

theorem fourthLevelEvenShear_det : fourthLevelEvenShear.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular fourthLevelEvenShear_upperTriangular]
  simp only [fourthLevelEvenShear_diagonal, Finset.prod_const_one]

theorem fourthLevelEvenShear_isUnit : IsUnit fourthLevelEvenShear := by
  rw [Matrix.isUnit_iff_isUnit_det, fourthLevelEvenShear_det]
  exact isUnit_one


theorem realMatrix_lower_of_shear {n : Type*} [Fintype n] [DecidableEq n]
    (S B D : Matrix n n ℝ) (ε : ℝ) (hS : IsUnit S)
    (h : (S.transpose * (B-ε • D) * S).PosSemidef) (v : n → ℝ) :
    ε * dotProduct v (D.mulVec v) ≤ dotProduct v (B.mulVec v) := by
  obtain ⟨w,hw⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hS) v
  have hv := (Matrix.posSemidef_iff_dotProduct_mulVec.mp h).2 w
  simp only [star_trivial, realMatrix_congruence_quadratic, hw,
    Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at hv
  exact sub_nonneg.mp hv

theorem realMatrix_blockDiagonal_quadratic {n m : Type*} [Fintype n] [Fintype m]
    (O : Matrix n n ℝ) (E : Matrix m m ℝ) (v : n ⊕ m → ℝ) :
    dotProduct v ((Matrix.fromBlocks O 0 0 E).mulVec v) =
      dotProduct (v ∘ Sum.inl) (O.mulVec (v ∘ Sum.inl)) +
        dotProduct (v ∘ Sum.inr) (E.mulVec (v ∘ Sum.inr)) := by
  simp only [Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, add_zero, zero_add,
    dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply]

theorem realMatrix_norm_eq_quadratic {n : Type*} [Fintype n] [DecidableEq n] (v : n → ℝ) :
    (∑ i, (v i)^2) = dotProduct v ((1 : Matrix n n ℝ).mulVec v) := by
  simp [Matrix.one_mulVec, dotProduct, pow_two]
theorem fourthLevelOddPolynomial_lower (v : Fin 8 → ℝ) :
    (1/1000000000 : ℝ) * dotProduct v ((Matrix.diagonal fourthLevelOddGramWeight).mulVec v) ≤
      dotProduct v ((fourthLevelOddPolynomial fourthLevelSamples).mulVec v) :=
  realMatrix_lower_of_shear fourthLevelOddShear _ _ _
    fourthLevelOddShear_isUnit fourthLevelOddSheared_posDef.posSemidef v

theorem fourthLevelEvenPolynomial_lower (v : Fin 7 → ℝ) :
    (1/1000000000 : ℝ) * dotProduct v ((Matrix.diagonal fourthLevelEvenGramWeight).mulVec v) ≤
      dotProduct v ((fourthLevelEvenPolynomial fourthLevelSamples).mulVec v) :=
  realMatrix_lower_of_shear fourthLevelEvenShear _ _ _
    fourthLevelEvenShear_isUnit fourthLevelEvenSheared_posDef.posSemidef v


/-- Auxiliary lower bound in all fifteen original unnormalized Haar coordinates. -/
theorem fourthLevelJumpHaar_sixteenth_lower (c : Fin 15 → ℝ) :
    (1/1000000000 : ℝ) * (∑ i, (c i)^2) ≤
      dotProduct c ((fourthLevelJumpHaar (5373/2000) (1/16)).mulVec c) := by
  let v := fourthLevelReflectionCoordinates c
  have hv : fourthLevelReflection.mulVec v = c :=
    fourthLevelReflection_mulVec_coordinates c
  have hp : fourthLevelJumpHaar (5373/2000) (1/16) = fourthLevelValueHaar fourthLevelSamples :=
    fourthLevelJumpHaar_sixteenth _
  have hb := fourthLevelJumpHaar_reflection_congruence (5373/2000) (1/16)
  rw [hp, fourthLevelOddBlock_eq_polynomial _ fourthLevelSamples_zero,
    fourthLevelEvenBlock_eq_polynomial _ fourthLevelSamples_zero] at hb
  have hc := realMatrix_congruence_quadratic fourthLevelReflection
    (fourthLevelValueHaar fourthLevelSamples) v
  rw [hb, realMatrix_blockDiagonal_quadratic, hv] at hc
  have hn := realMatrix_congruence_quadratic fourthLevelReflection
    (1 : Matrix (Fin 15) (Fin 15) ℝ) v
  rw [Matrix.mul_one, fourthLevelReflection_gram, realMatrix_blockDiagonal_quadratic, hv] at hn
  have ho := fourthLevelOddPolynomial_lower (v ∘ Sum.inl)
  have he := fourthLevelEvenPolynomial_lower (v ∘ Sum.inr)
  change dotProduct (v ∘ Sum.inl) ((Matrix.diagonal fourthLevelOddGramWeight).mulVec (v ∘ Sum.inl)) +
    dotProduct (v ∘ Sum.inr) ((Matrix.diagonal fourthLevelEvenGramWeight).mulVec (v ∘ Sum.inr)) =
      dotProduct c ((1 : Matrix (Fin 15) (Fin 15) ℝ).mulVec c) at hn
  rw [hp]
  have hnorm := realMatrix_norm_eq_quadratic c
  linarith only [ho,he,hc,hn,hnorm]

theorem fourthLevel_reindex_quadratic
    (M : Matrix (FiniteDyadicHaarIndex 4) (FiniteDyadicHaarIndex 4) ℝ)
    (c : FiniteDyadicHaarIndex 4 → ℝ) :
    dotProduct c (M.mulVec c) =
      dotProduct (c ∘ fourthLevelIndex)
        (Matrix.mulVec (fun i j : Fin 15 => M (fourthLevelIndex i) (fourthLevelIndex j))
          (c ∘ fourthLevelIndex)) := by
  unfold Matrix.mulVec dotProduct
  rw [← fourthLevelIndexEquiv.sum_comp (fun i => c i * ∑ j, M i j * c j)]
  apply Finset.sum_congr rfl
  intro i hi
  change c (fourthLevelIndex i) * (∑ j, M (fourthLevelIndex i) j * c j) = _
  rw [← fourthLevelIndexEquiv.sum_comp
    (fun j => M (fourthLevelIndex i) j * c j)]
  rfl

theorem fourthLevelHaarModel_quadratic (C R : ℝ)
    (c : FiniteDyadicHaarIndex 4 → ℝ) :
    dotProduct c ((fourthLevelHaarModel C R).mulVec c) =
      dotProduct (c ∘ fourthLevelIndex)
        ((fourthLevelJumpHaar C R).mulVec (c ∘ fourthLevelIndex)) := by
  rw [fourthLevel_reindex_quadratic, fourthLevelHaarModel_reindex]

theorem fourthLevelHaarModel_sixteenth_lower (c : FiniteDyadicHaarIndex 4 → ℝ) :
    (1/1000000000 : ℝ) * (∑ i, (c i)^2) ≤
      dotProduct c ((fourthLevelHaarModel (5373/2000) (1/16)).mulVec c) := by
  have h := fourthLevelJumpHaar_sixteenth_lower (c ∘ fourthLevelIndex)
  have he : (∑ i : Fin 15, ((c ∘ fourthLevelIndex) i)^2) = ∑ i, (c i)^2 :=
    fourthLevelIndexEquiv.sum_comp (fun i => (c i)^2)
  rw [he, ← fourthLevelHaarModel_quadratic] at h
  exact h

/-- Genuine arithmetic approximation, only at R=1/16, m=4, N=2, J=5. -/
theorem arithmeticScrewApproxHaarMatrix_sixteenth_level_four_lower
    (c : FiniteDyadicHaarIndex 4 → ℝ) :
    (1/1000000000 : ℝ) * (∑ i, (c i)^2) ≤
      dotProduct c ((arithmeticScrewApproxHaarMatrix (1/16) 4 2 5).mulVec c) :=
  (fourthLevelHaarModel_sixteenth_lower c).trans
    (fourthLevelHaarModel_auxiliary_le_finite (by norm_num) c)

/-- Native positive-semidefiniteness of the fixed finite arithmetic approximation. -/
theorem arithmeticScrewApproxHaarMatrix_sixteenth_level_four_posSemidef :
    (arithmeticScrewApproxHaarMatrix (1/16) 4 2 5).PosSemidef := by
  rw [arithmeticScrewApproxHaarMatrix_posSemidef_iff]
  intro c
  exact le_trans (by positivity)
    (arithmeticScrewApproxHaarMatrix_sixteenth_level_four_lower c)

/-- The admissible signed tail comparison transfers precisely the same lower bound. -/
theorem arithmeticScrewHaarMatrix_sixteenth_four_lower
    (c : FiniteDyadicHaarIndex 4 → ℝ) :
    (1/1000000000 : ℝ) * (∑ i, (c i)^2) ≤
      dotProduct c ((arithmeticScrewHaarMatrix (1/16) 4).mulVec c) :=
  (arithmeticScrewApproxHaarMatrix_sixteenth_level_four_lower c).trans
    (arithmeticScrewApproxHaarMatrix_four_sixteenth_le_actual c)

/-- Native actual arithmetic PSD at this fixed window and level only.
This is not all-level or all-window positivity, completed-Weil positivity, or RH. -/
theorem arithmeticScrewHaarMatrix_sixteenth_four_posSemidef :
    (arithmeticScrewHaarMatrix (1/16) 4).PosSemidef :=
  arithmeticScrewHaarMatrix_posSemidef_of_approx_posSemidef
    (by norm_num) 4 2 5 arithmeticScrewApprox_sixteenth_cutoff
    arithmeticScrewApproxHaarMatrix_sixteenth_level_four_posSemidef
end
end RiemannResearch.RH
