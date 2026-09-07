/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.ArithmeticFiniteFourthLevelCertificate

/-!
# Reusable exact finite arithmetic certificate infrastructure

This module supplies sign-aware finite interval evaluation, an interval/shear
strict-diagonal-dominance checker, and the literal finite arithmetic model with
an arbitrary linear coefficient, dyadic level, and finite cutoffs. The latter
is compared in the correct signed quadratic-form direction to the native
finite and actual arithmetic Haar matrices. No interval or positivity datum
from numerical reconnaissance is assumed to have been verified.

Source: user-provided RH continuation program and FifthLevel_Paper_Recon_v47.md.
The sources support the certificate architecture and proposed m=5 consumer.
This infrastructure alone proves no new arithmetic positive-semidefinite
matrix, all-level positivity, completed-Weil agreement, or RH.
-/

open scoped BigOperators
namespace RiemannResearch.RH
open RiemannResearch.Analysis RiemannResearch.RH.PrimeGapCurvature
noncomputable section

/-- Outward lower endpoint for a signed scalar product. -/
def signedIntervalLower (w l u : ℝ) : ℝ := if 0 ≤ w then w*l else w*u

/-- Outward upper endpoint for a signed scalar product. -/
def signedIntervalUpper (w l u : ℝ) : ℝ := if 0 ≤ w then w*u else w*l

theorem signedInterval_mul_bounds {l p u : ℝ} (w : ℝ)
    (hl : l ≤ p) (hu : p ≤ u) :
    signedIntervalLower w l u ≤ w*p ∧ w*p ≤ signedIntervalUpper w l u := by
  by_cases hw : 0 ≤ w
  · simp only [signedIntervalLower, signedIntervalUpper, if_pos hw]
    exact ⟨mul_le_mul_of_nonneg_left hl hw, mul_le_mul_of_nonneg_left hu hw⟩
  · simp only [signedIntervalLower, signedIntervalUpper, if_neg hw]
    exact ⟨mul_le_mul_of_nonpos_left hu (le_of_not_ge hw),
      mul_le_mul_of_nonpos_left hl (le_of_not_ge hw)⟩

/-- A data-driven enclosure for an arbitrary finite linear form. -/
theorem signedInterval_finset_sum_bounds {κ : Type*} (s : Finset κ)
    (w l p u : κ → ℝ) (hl : ∀ k ∈ s, l k ≤ p k) (hu : ∀ k ∈ s, p k ≤ u k) :
    (∑ k ∈ s, signedIntervalLower (w k) (l k) (u k)) ≤ ∑ k ∈ s, w k*p k ∧
    (∑ k ∈ s, w k*p k) ≤ ∑ k ∈ s, signedIntervalUpper (w k) (l k) (u k) := by
  constructor
  · exact Finset.sum_le_sum (fun k hk => (signedInterval_mul_bounds (w k) (hl k hk) (hu k hk)).1)
  · exact Finset.sum_le_sum (fun k hk => (signedInterval_mul_bounds (w k) (hl k hk) (hu k hk)).2)

/-- Positivity from full entry intervals and exact rational row margins. -/
theorem realMatrix_posDef_of_intervals {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (lo hi : Matrix n n ℝ) (hA : A.IsHermitian)
    (hlo : ∀ i j, lo i j ≤ A i j) (hhi : ∀ i j, A i j ≤ hi i j)
    (hdd : ∀ i, (∑ j ∈ Finset.univ.erase i, max |lo i j| |hi i j|) < lo i i) :
    A.PosDef := by
  apply StrictDiagonalDominance.posDef_of_entrywise_interval_certificate hA lo
    (fun i j => max |lo i j| |hi i j|) (fun i => hlo i i) ?_ hdd
  intro i j _
  simpa only [Real.norm_eq_abs] using abs_le_max_abs_of_bounds ⟨hlo i j, hhi i j⟩

/-- The interval/shear checker uses the supplied coefficient Gram literally. -/
theorem realMatrix_lower_of_interval_shear {n : Type*} [Fintype n] [DecidableEq n]
    (K G S lo hi : Matrix n n ℝ) (ε : ℝ)
    (hK : K.IsHermitian) (hG : G.IsHermitian) (hS : IsUnit S)
    (hlo : ∀ i j, lo i j ≤ (S.transpose * (K - ε • G) * S) i j)
    (hhi : ∀ i j, (S.transpose * (K - ε • G) * S) i j ≤ hi i j)
    (hdd : ∀ i, (∑ j ∈ Finset.univ.erase i, max |lo i j| |hi i j|) < lo i i)
    (c : n → ℝ) :
    ε * dotProduct c (G.mulVec c) ≤ dotProduct c (K.mulVec c) := by
  apply realMatrix_lower_of_shear S K G ε hS
  exact (realMatrix_posDef_of_intervals lo hi
    (realMatrix_congruence_isHermitian S (hK.sub (hG.smul (by simp [IsSelfAdjoint]))))
    hlo hhi hdd).posSemidef

/-- Literal signed finite rectangle with only its linear coefficient exposed. -/
def arithmeticFiniteCellModel (C : ℝ) (N J : ℕ) (b₁ d₁ b₂ d₂ : ℝ) : ℝ :=
  screwPolarCell b₁ d₁ b₂ d₂ +
    (∑ n ∈ Finset.range N, primePowerHingeCell n b₁ d₁ b₂ d₂) +
    C * absCell b₁ d₁ b₂ d₂ -
    ∑ k ∈ Finset.range J, archimedeanScrewCell k b₁ d₁ b₂ d₂

def arithmeticFiniteCellMatrix (C R : ℝ) (m N J : ℕ) :
    Matrix (Fin (2^m)) (Fin (2^m)) ℝ :=
  fun i j => arithmeticFiniteCellModel C N J
    (dyadicCellLeft R m i) (dyadicCellRight R m i)
    (dyadicCellLeft R m j) (dyadicCellRight R m j)

def arithmeticFiniteHaarModel (C R : ℝ) (m N J : ℕ) :
    Matrix (FiniteDyadicHaarIndex m) (FiniteDyadicHaarIndex m) ℝ :=
  finiteDyadicHaarCompression m (arithmeticFiniteCellMatrix C R m N J)

theorem arithmeticScrewApproxHaarMatrix_eq_finiteModel (R : ℝ) (m N J : ℕ) :
    arithmeticScrewApproxHaarMatrix R m N J =
      arithmeticFiniteHaarModel screwLinearCoefficient R m N J := by
  unfold arithmeticFiniteHaarModel arithmeticScrewApproxHaarMatrix
  congr 1
  ext i j
  exact integral_integral_arithmeticScrewApprox N J
    (dyadicCellLeft R m i) (dyadicCellRight R m i)
    (dyadicCellLeft R m j) (dyadicCellRight R m j)

theorem arithmeticFiniteCellMatrix_coefficient_difference (C C0 R : ℝ) (m N J : ℕ) :
    arithmeticFiniteCellMatrix C R m N J - arithmeticFiniteCellMatrix C0 R m N J =
      (C-C0) • dyadicCellKernel R m (fun x y => |x-y|) := by
  ext i j
  change arithmeticFiniteCellModel C N J _ _ _ _ - arithmeticFiniteCellModel C0 N J _ _ _ _ =
    (C-C0) * (∫ x in dyadicCellLeft R m i..dyadicCellRight R m i,
      ∫ y in dyadicCellLeft R m j..dyadicCellRight R m j, |x-y|)
  rw [integral_integral_abs_sub]
  unfold arithmeticFiniteCellModel
  ring

theorem arithmeticFiniteHaarModel_coefficient_difference (C C0 R : ℝ) (m N J : ℕ) :
    arithmeticFiniteHaarModel C R m N J - arithmeticFiniteHaarModel C0 R m N J =
      (C-C0) • finiteDyadicHaarCompression m
        (dyadicCellKernel R m (fun x y => |x-y|)) := by
  unfold arithmeticFiniteHaarModel finiteDyadicHaarCompression
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, arithmeticFiniteCellMatrix_coefficient_difference]
  simp only [Matrix.mul_smul, Matrix.smul_mul]

/-- Exact negative-absolute-kernel comparison at every dyadic level and cutoff. -/
theorem arithmeticFiniteHaarModel_quadratic_coefficient_difference
    (C C0 : ℝ) {R : ℝ} (hR : 0 ≤ R) (m N J : ℕ) (c : FiniteDyadicHaarIndex m → ℝ) :
    dotProduct c ((arithmeticFiniteHaarModel C R m N J).mulVec c) -
      dotProduct c ((arithmeticFiniteHaarModel C0 R m N J).mulVec c) =
      2*(C0-C)*(∫ t, (∫ x in Set.Iic t, dyadicHaarStep R m c x)^2) := by
  rw [← dotProduct_sub, ← Matrix.sub_mulVec, arithmeticFiniteHaarModel_coefficient_difference,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    ← dyadicHaarStep_quadratic_reconstruction hR m
      (fun x y => |x-y|) ((continuous_fst.sub continuous_snd).abs),
    dyadicHaarStep_absKernel_integral_eq hR m c]
  ring

theorem arithmeticFiniteHaarModel_antitone {C C0 R : ℝ}
    (hC : C ≤ C0) (hR : 0 ≤ R) (m N J : ℕ) (c : FiniteDyadicHaarIndex m → ℝ) :
    dotProduct c ((arithmeticFiniteHaarModel C0 R m N J).mulVec c) ≤
      dotProduct c ((arithmeticFiniteHaarModel C R m N J).mulVec c) := by
  apply sub_nonneg.mp
  rw [arithmeticFiniteHaarModel_quadratic_coefficient_difference C C0 hR]
  exact mul_nonneg (by positivity)
    (MeasureTheory.integral_nonneg (fun _ => sq_nonneg _))

theorem arithmeticFiniteHaarModel_auxiliary_le_finite
    {R : ℝ} (hR : 0 ≤ R) (m N J : ℕ) (c : FiniteDyadicHaarIndex m → ℝ) :
    dotProduct c ((arithmeticFiniteHaarModel (5373/2000) R m N J).mulVec c) ≤
      dotProduct c ((arithmeticScrewApproxHaarMatrix R m N J).mulVec c) := by
  rw [arithmeticScrewApproxHaarMatrix_eq_finiteModel]
  exact arithmeticFiniteHaarModel_antitone screwLinearCoefficient_le_5373_div_2000 hR m N J c

/-- The fixed admissible cutoff works uniformly in the dyadic level and mode count. -/
theorem arithmeticScrewApproxHaarMatrix_sixteenth_le_actual (m J : ℕ)
    (c : FiniteDyadicHaarIndex m → ℝ) :
    dotProduct c ((arithmeticScrewApproxHaarMatrix (1/16) m 2 J).mulVec c) ≤
      dotProduct c ((arithmeticScrewHaarMatrix (1/16) m).mulVec c) :=
  arithmeticScrewApproxHaarMatrix_quadratic_le (by norm_num) m 2 J
    arithmeticScrewApprox_sixteenth_cutoff c

/-- Incidence evaluation, including both boundary rows, without dimension casts. -/
theorem cellEndpointIncidence_mul_apply {κ : Type*} [Fintype κ] {n : ℕ}
    (H : Matrix (Fin n) κ ℝ) (r : Fin (n+1)) (j : κ) :
    (cellEndpointIncidence n * H) r j =
      (if h : r.val < n then H ⟨r.val,h⟩ j else 0) -
      (if h : 0 < r.val then H ⟨r.val-1,by omega⟩ j else 0) := by
  simp only [Matrix.mul_apply, cellEndpointIncidence, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · split_ifs with h
    · have hr : r = (⟨r.val,h⟩ : Fin n).castSucc := Fin.ext rfl
      conv_lhs => rw [hr]
      simp only [Fin.castSucc_inj, ite_mul, one_mul, zero_mul]
      simp
    · apply Finset.sum_eq_zero
      intro i _
      have hr : r ≠ i.castSucc := by
        intro he
        have hv := congrArg Fin.val he
        simp only [Fin.val_castSucc] at hv
        omega
      simp [hr]
  · split_ifs with h
    · have hr : r = (⟨r.val-1,by omega⟩ : Fin n).succ := Fin.ext (by simp; omega)
      conv_lhs => rw [hr]
      simp only [Fin.succ_inj, ite_mul, one_mul, zero_mul]
      simp
    · apply Finset.sum_eq_zero
      intro i _
      have hr : r ≠ i.succ := by intro he; have := congrArg Fin.val he; simp at this; omega
      simp [hr]

/-- Discrete integration by parts for one unnormalized interval indicator. -/
theorem cellEndpointIncidence_interval {n : ℕ} (a b : Fin (n+1)) (hab : a.val ≤ b.val)
    (r : Fin (n+1)) :
    (cellEndpointIncidence n).mulVec
      (fun i => if a.val ≤ i.val ∧ i.val < b.val then (1:ℝ) else 0) r =
        (if r = a then 1 else 0) - (if r = b then 1 else 0) := by
  let H : Matrix (Fin n) Unit ℝ :=
    fun i _ => if a.val ≤ i.val ∧ i.val < b.val then 1 else 0
  change (cellEndpointIncidence n * H) r () = _
  rw [cellEndpointIncidence_mul_apply]
  simp only [H, Fin.ext_iff]
  split_ifs <;> norm_num <;> omega

/-- Native dyadic half-block endpoints lie inside the full endpoint grid. -/
theorem finiteDyadicHaarEndpoint_bound (m : ℕ) (i : FiniteDyadicHaarIndex m) :
    2*i.2.val*2^(m-i.1.val-1) + 2*2^(m-i.1.val-1) ≤ 2^m := by
  have hf : 2^i.1.val * (2*2^(m-i.1.val-1)) = 2^m := by
    rw [← pow_succ', ← pow_add]
    congr 1
    have := i.1.isLt
    omega
  have h := Nat.mul_le_mul_right (2*2^(m-i.1.val-1)) i.2.isLt
  rw [hf] at h
  nlinarith

def finiteDyadicHaarLeftEndpoint (m : ℕ) (i : FiniteDyadicHaarIndex m) : Fin (2^m+1) :=
  ⟨2*i.2.val*2^(m-i.1.val-1), by have := finiteDyadicHaarEndpoint_bound m i; omega⟩

def finiteDyadicHaarMidEndpoint (m : ℕ) (i : FiniteDyadicHaarIndex m) : Fin (2^m+1) :=
  ⟨2*i.2.val*2^(m-i.1.val-1)+2^(m-i.1.val-1),
    by have := finiteDyadicHaarEndpoint_bound m i; omega⟩

def finiteDyadicHaarRightEndpoint (m : ℕ) (i : FiniteDyadicHaarIndex m) : Fin (2^m+1) :=
  ⟨2*i.2.val*2^(m-i.1.val-1)+2*2^(m-i.1.val-1),
    by have := finiteDyadicHaarEndpoint_bound m i; omega⟩

/-- The native endpoint jumps, with the exact unnormalized weights `1,-2,1`. -/
def finiteDyadicHaarEndpointJumps (m : ℕ) :
    Matrix (Fin (2^m+1)) (FiniteDyadicHaarIndex m) ℝ :=
  threePointJumps (finiteDyadicHaarLeftEndpoint m)
    (finiteDyadicHaarMidEndpoint m) (finiteDyadicHaarRightEndpoint m)

/-- Literal native Haar atoms yield the same three-point endpoint columns at every level. -/
theorem finiteDyadicHaarMatrix_endpointJumps (m : ℕ) :
    cellEndpointIncidence (2^m) * finiteDyadicHaarMatrix m =
      finiteDyadicHaarEndpointJumps m := by
  ext r i
  have h₁ := cellEndpointIncidence_interval
    (finiteDyadicHaarLeftEndpoint m i) (finiteDyadicHaarMidEndpoint m i)
    (Nat.le_add_right _ _) r
  have h₂ := cellEndpointIncidence_interval
    (finiteDyadicHaarMidEndpoint m i) (finiteDyadicHaarRightEndpoint m i)
    (by dsimp only [finiteDyadicHaarMidEndpoint, finiteDyadicHaarRightEndpoint]; omega) r
  change ((cellEndpointIncidence (2^m)).mulVec
    (finiteDyadicHaarAtom m i.1.val i.2)) r = _
  unfold finiteDyadicHaarAtom
  change ((cellEndpointIncidence (2^m)).mulVec
    ((fun j => if (finiteDyadicHaarLeftEndpoint m i).val ≤ j.val ∧
       j.val < (finiteDyadicHaarMidEndpoint m i).val then 1 else 0) -
     (fun j => if (finiteDyadicHaarMidEndpoint m i).val ≤ j.val ∧
       j.val < (finiteDyadicHaarRightEndpoint m i).val then 1 else 0))) r = _
  rw [Matrix.mulVec_sub, Pi.sub_apply, h₁, h₂]
  simp only [finiteDyadicHaarEndpointJumps, threePointJumps]
  ring

/-- Generic native endpoint congruence against any literal second-primitive cell matrix. -/
theorem finiteDyadicHaarCompression_primitive (m : ℕ) (P : ℝ → ℝ)
    (x : Fin (2^m+1) → ℝ) :
    finiteDyadicHaarCompression m
      (fun i j => secondPrimitiveCell P (x i.castSucc) (x i.succ)
        (x j.castSucc) (x j.succ)) =
      -((finiteDyadicHaarEndpointJumps m).transpose * endpointPrimitiveMatrix P x *
        finiteDyadicHaarEndpointJumps m) := by
  rw [secondPrimitiveCell_incidence]
  unfold finiteDyadicHaarCompression
  rw [cellHaar_jump_congruence, finiteDyadicHaarMatrix_endpointJumps]

def finiteDyadicGridEndpoint (R : ℝ) (m : ℕ) (i : Fin (2^m+1)) : ℝ :=
  -R + dyadicCellWidth R m * i.val

/-- The existing five-mode primitive is valid on every dyadic grid. -/
theorem arithmeticFiniteCellMatrix_fiveModes_primitive (C R : ℝ) (m : ℕ) :
    arithmeticFiniteCellMatrix C R m 2 5 =
      (fun i j => secondPrimitiveCell (fun t => fourthLevelPrimitive C |t|)
        (finiteDyadicGridEndpoint R m i.castSucc) (finiteDyadicGridEndpoint R m i.succ)
        (finiteDyadicGridEndpoint R m j.castSucc) (finiteDyadicGridEndpoint R m j.succ)) := by
  ext i j
  change fourthLevelArithmeticCell C _ _ _ _ = _
  rw [fourthLevelArithmeticCell_eq_primitive]
  congr 1 <;>
    simp only [finiteDyadicGridEndpoint, dyadicCellLeft, dyadicCellRight,
      Fin.val_succ, Nat.cast_add, Nat.cast_one] <;> ring

/-- Complete arbitrary-level J=5 native Haar reconstruction by endpoint jumps. -/
theorem arithmeticFiniteHaarModel_fiveModes_jumps (C R : ℝ) (m : ℕ) :
    arithmeticFiniteHaarModel C R m 2 5 =
      -((finiteDyadicHaarEndpointJumps m).transpose *
        endpointPrimitiveMatrix (fun t => fourthLevelPrimitive C |t|)
          (finiteDyadicGridEndpoint R m) * finiteDyadicHaarEndpointJumps m) := by
  unfold arithmeticFiniteHaarModel
  rw [arithmeticFiniteCellMatrix_fiveModes_primitive, finiteDyadicHaarCompression_primitive]

/-- Signed integer-distance Toeplitz value; no modular index arithmetic occurs. -/
def finiteDyadicPrimitiveToeplitz (P : ℝ → ℝ) (h : ℝ) (k : ℤ) : ℝ :=
  P ((k+1)*h) - 2*P (k*h) + P ((k-1)*h)

theorem secondPrimitiveCell_uniform_toeplitz (P : ℝ → ℝ) (a h : ℝ) (i j : ℤ) :
    secondPrimitiveCell P (a+i*h) (a+(i+1)*h) (a+j*h) (a+(j+1)*h) =
      finiteDyadicPrimitiveToeplitz P h (i-j) := by
  unfold secondPrimitiveCell finiteDyadicPrimitiveToeplitz
  push_cast
  congr 1 <;> ring

/-- Reflection of a native Haar coefficient stays at its literal scale. -/
def finiteDyadicHaarReflect (m : ℕ) (i : FiniteDyadicHaarIndex m) : FiniteDyadicHaarIndex m :=
  ⟨i.1, i.2.rev⟩

theorem finiteDyadicHaarReflect_involutive (m : ℕ) :
    Function.Involutive (finiteDyadicHaarReflect m) := by
  intro i
  simp [finiteDyadicHaarReflect]

theorem finiteDyadicHaarReflect_left (m : ℕ) (i : FiniteDyadicHaarIndex m) :
    finiteDyadicHaarLeftEndpoint m (finiteDyadicHaarReflect m i) =
      (finiteDyadicHaarRightEndpoint m i).rev := by
  apply Fin.ext
  have hf : 2^i.1.val * (2*2^(m-i.1.val-1)) = 2^m := by
    rw [← pow_succ', ← pow_add]
    congr 1
    have := i.1.isLt
    omega
  have hq : i.2.val ≤ 2^i.1.val-1 := by have := i.2.isLt; omega
  have hsum : (2^i.1.val-(i.2.val+1))+i.2.val+1 = 2^i.1.val := by omega
  dsimp [finiteDyadicHaarLeftEndpoint, finiteDyadicHaarRightEndpoint,
    finiteDyadicHaarReflect, Fin.rev]
  have hb := finiteDyadicHaarEndpoint_bound m i
  have ht := Nat.sub_add_cancel (show
    2*i.2.val*2^(m-i.1.val-1)+2*2^(m-i.1.val-1)+1 ≤ 2^m+1 by omega)
  have hm := congrArg (fun k : ℕ => k * (2*2^(m-i.1.val-1))) hsum
  nlinarith

theorem finiteDyadicHaarReflect_right (m : ℕ) (i : FiniteDyadicHaarIndex m) :
    finiteDyadicHaarRightEndpoint m (finiteDyadicHaarReflect m i) =
      (finiteDyadicHaarLeftEndpoint m i).rev := by
  have h := finiteDyadicHaarReflect_left m (finiteDyadicHaarReflect m i)
  rw [finiteDyadicHaarReflect_involutive m i] at h
  simpa using congrArg Fin.rev h.symm

theorem finiteDyadicHaarReflect_mid (m : ℕ) (i : FiniteDyadicHaarIndex m) :
    finiteDyadicHaarMidEndpoint m (finiteDyadicHaarReflect m i) =
      (finiteDyadicHaarMidEndpoint m i).rev := by
  have h := congrArg Fin.val (finiteDyadicHaarReflect_left m i)
  have hb := finiteDyadicHaarEndpoint_bound m i
  dsimp [finiteDyadicHaarLeftEndpoint, finiteDyadicHaarRightEndpoint,
    finiteDyadicHaarReflect, Fin.rev] at h
  apply Fin.ext
  dsimp [finiteDyadicHaarMidEndpoint, finiteDyadicHaarReflect, Fin.rev]
  omega

/-- Every even translation primitive is invariant under the full-grid reflection. -/
theorem endpointPrimitiveMatrix_grid_reflect (R : ℝ) (m : ℕ) (P : ℝ → ℝ)
    (hP : ∀ t, P (-t) = P t) (i j : Fin (2^m+1)) :
    endpointPrimitiveMatrix P (finiteDyadicGridEndpoint R m) i.rev j.rev =
      endpointPrimitiveMatrix P (finiteDyadicGridEndpoint R m) i j := by
  unfold endpointPrimitiveMatrix finiteDyadicGridEndpoint
  have hi : (i.rev.val : ℝ) = (2^m : ℕ) - (i.val : ℝ) := by
    rw [Fin.val_rev]
    norm_num
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hj : (j.rev.val : ℝ) = (2^m : ℕ) - (j.val : ℝ) := by
    rw [Fin.val_rev]
    norm_num
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hi, hj, show -R+dyadicCellWidth R m*((2^m:ℕ)-(i.val:ℝ))-
      (-R+dyadicCellWidth R m*((2^m:ℕ)-(j.val:ℝ))) =
      -((-R+dyadicCellWidth R m*i.val)-(-R+dyadicCellWidth R m*j.val)) by ring, hP]

/-- Reflection symmetry transfers exactly to the native, unnormalized jump compression. -/
theorem finiteDyadicHaarEndpointJumps_congruence_reflect (m : ℕ)
    (F : Matrix (Fin (2^m+1)) (Fin (2^m+1)) ℝ)
    (hF : ∀ r s, F r.rev s.rev = F r s) (i j : FiniteDyadicHaarIndex m) :
    ((finiteDyadicHaarEndpointJumps m).transpose * F * finiteDyadicHaarEndpointJumps m)
        (finiteDyadicHaarReflect m i) (finiteDyadicHaarReflect m j) =
      ((finiteDyadicHaarEndpointJumps m).transpose * F * finiteDyadicHaarEndpointJumps m) i j := by
  unfold finiteDyadicHaarEndpointJumps
  simp only [threePointJumps_congruence, finiteDyadicHaarReflect_left,
    finiteDyadicHaarReflect_mid, finiteDyadicHaarReflect_right, hF]
  ring

theorem arithmeticFiniteHaarModel_fiveModes_reflect (C R : ℝ) (m : ℕ)
    (i j : FiniteDyadicHaarIndex m) :
    arithmeticFiniteHaarModel C R m 2 5 (finiteDyadicHaarReflect m i)
      (finiteDyadicHaarReflect m j) = arithmeticFiniteHaarModel C R m 2 5 i j := by
  rw [arithmeticFiniteHaarModel_fiveModes_jumps]
  simp only [Matrix.neg_apply]
  congr 1
  apply finiteDyadicHaarEndpointJumps_congruence_reflect
  exact endpointPrimitiveMatrix_grid_reflect R m (fun t => fourthLevelPrimitive C |t|)
    (fun t => by rw [abs_neg])

/-- Reflection columns for an arbitrary involution and arbitrary chosen representatives. -/
def involutionReflectionColumns {n o e : Type*} [DecidableEq n]
    (r : n → n) (a : o → n) (b : e → n) (w : o → ℝ) : Matrix n (o ⊕ e) ℝ :=
  twoPointColumns (Sum.elim a b) (r ∘ Sum.elim a b)
    (Sum.elim w (fun _ => 1)) (Sum.elim w (fun _ => -1))

def involutionOddBlock {n o : Type*} (r : n → n) (a : o → n) (w : o → ℝ)
    (K : Matrix n n ℝ) : Matrix o o ℝ :=
  fun i j => 2*w i*w j*(K (a i) (a j)+K (a i) (r (a j)))

def involutionEvenBlock {n e : Type*} (r : n → n) (b : e → n)
    (K : Matrix n n ℝ) : Matrix e e ℝ :=
  fun i j => 2*(K (b i) (b j)-K (b i) (r (b j)))

/-- Exact even-Toeplitz reflection congruence; no positive-definiteness premise is used. -/
theorem involutionReflectionColumns_congruence
    {n o e : Type*} [Fintype n] [Fintype o] [Fintype e] [DecidableEq n]
    (r : n → n) (hr : Function.Involutive r)
    (a : o → n) (b : e → n) (w : o → ℝ) (K : Matrix n n ℝ)
    (hK : ∀ i j, K (r i) (r j) = K i j) :
    (involutionReflectionColumns r a b w).transpose * K * involutionReflectionColumns r a b w =
      Matrix.fromBlocks (involutionOddBlock r a w K) 0 0 (involutionEvenBlock r b K) := by
  have hcross (i j : n) : K (r i) j = K i (r j) := by
    simpa only [hr j] using hK i (r j)
  ext i j
  simp only [involutionReflectionColumns, twoPointColumns_congruence]
  cases i <;> cases j <;>
    simp only [Sum.elim_inl, Sum.elim_inr, Function.comp_apply,
      Matrix.fromBlocks, Matrix.of_apply, Matrix.zero_apply,
      involutionOddBlock, involutionEvenBlock, hK, hcross] <;> ring

/-- A complete finite collection of one fixed point and distinct reflection pairs. -/
structure ReflectionOrbitSystem (n κ : Type*) where
  reflect : n → n
  involutive : Function.Involutive reflect
  pick : Option κ → n
  pick_injective : Function.Injective pick
  root_fixed : reflect (pick none) = pick none
  pairs_disjoint : ∀ i j, pick (some i) ≠ reflect (pick (some j))
  exhaustive : ∀ i, (∃ j, i = pick j) ∨ (∃ j, i = reflect (pick (some j)))

def reflectionOrbitWeight {κ : Type*} : Option κ → ℝ
  | none => 1/2
  | some _ => 1

def ReflectionOrbitSystem.columns {n κ : Type*} [DecidableEq n]
    (s : ReflectionOrbitSystem n κ) : Matrix n (Option κ ⊕ κ) ℝ :=
  involutionReflectionColumns s.reflect s.pick (fun i => s.pick (some i)) reflectionOrbitWeight

theorem ReflectionOrbitSystem.pick_reflect_eq {n κ : Type*}
    (s : ReflectionOrbitSystem n κ) (i j : Option κ) :
    s.pick i = s.reflect (s.pick j) ↔ i = none ∧ j = none := by
  cases i with
  | none =>
    cases j with
    | none => simp [s.root_fixed]
    | some j =>
      simp only [Option.some_ne_none, and_false, iff_false]
      intro h
      have h' := congrArg s.reflect h
      rw [s.root_fixed, s.involutive] at h'
      have := s.pick_injective h'
      cases this
  | some i =>
    cases j with
    | none =>
      rw [s.root_fixed]
      simp only [Option.some_ne_none, false_and, iff_false]
      intro h
      have := s.pick_injective h
      cases this
    | some j => simp [s.pairs_disjoint]

/-- Exact native-coefficient Gram: root weight one, pair weights two. -/
theorem ReflectionOrbitSystem.columns_gram {n κ : Type*}
    [Fintype n] [Fintype κ] [DecidableEq n] [DecidableEq κ]
    (s : ReflectionOrbitSystem n κ) :
    s.columns.transpose * s.columns =
      Matrix.fromBlocks (Matrix.diagonal (fun i : Option κ => if i = none then 1 else 2))
        0 0 (Matrix.diagonal (fun _ : κ => 2)) := by
  have h := involutionReflectionColumns_congruence s.reflect s.involutive s.pick
    (fun i => s.pick (some i)) reflectionOrbitWeight (1 : Matrix n n ℝ)
    (by intro i j; simp only [Matrix.one_apply, s.involutive.injective.eq_iff])
  have ho : involutionOddBlock s.reflect s.pick reflectionOrbitWeight (1 : Matrix n n ℝ) =
      Matrix.diagonal (fun i : Option κ => if i = none then 1 else 2) := by
    ext i j
    simp only [involutionOddBlock, Matrix.one_apply, s.pick_injective.eq_iff,
      s.pick_reflect_eq, Matrix.diagonal_apply]
    cases i <;> cases j <;> simp [reflectionOrbitWeight]
    norm_num
  have he : involutionEvenBlock s.reflect (fun i => s.pick (some i)) (1 : Matrix n n ℝ) =
      Matrix.diagonal (fun _ : κ => 2) := by
    ext i j
    simp only [involutionEvenBlock, Matrix.one_apply, s.pick_injective.eq_iff,
      s.pick_reflect_eq, Matrix.diagonal_apply, Option.some.injEq,
      Option.some_ne_none, false_and, if_false, sub_zero]
    split_ifs <;> norm_num
  simpa only [ReflectionOrbitSystem.columns, Matrix.mul_one, ho, he] using h

def ReflectionOrbitSystem.coordinates {n κ : Type*} (s : ReflectionOrbitSystem n κ)
    (c : n → ℝ) : Option κ ⊕ κ → ℝ :=
  Sum.elim
    (fun i => match i with
      | none => c (s.pick none)
      | some j => (c (s.pick (some j)) + c (s.reflect (s.pick (some j))))/2)
    (fun j => (c (s.pick (some j))-c (s.reflect (s.pick (some j))))/2)

theorem ReflectionOrbitSystem.columns_mulVec_coordinates {n κ : Type*}
    [Fintype n] [Fintype κ] [DecidableEq n] [DecidableEq κ]
    (s : ReflectionOrbitSystem n κ) (c : n → ℝ) :
    s.columns.mulVec (s.coordinates c) = c := by
  funext i
  rcases s.exhaustive i with ⟨j,rfl⟩ | ⟨j,rfl⟩
  · cases j <;>
      simp [ReflectionOrbitSystem.columns, involutionReflectionColumns, twoPointColumns,
        Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_option,
        s.pick_injective.eq_iff, s.pick_reflect_eq, reflectionOrbitWeight,
        ReflectionOrbitSystem.coordinates] <;> ring
  · have h₁ (k : Option κ) :
        s.reflect (s.pick (some j)) = s.pick k ↔ k = none ∧ (some j : Option κ) = none := by
      rw [eq_comm, s.pick_reflect_eq]
    simp [ReflectionOrbitSystem.columns, involutionReflectionColumns, twoPointColumns,
      Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      s.involutive.injective.eq_iff, s.pick_injective.eq_iff, h₁,
      reflectionOrbitWeight, ReflectionOrbitSystem.coordinates]
    ring

theorem finiteDyadicHaarIndex_ext {m : ℕ} {i j : FiniteDyadicHaarIndex m}
    (hl : i.1.val = j.1.val) (hq : i.2.val = j.2.val) : i = j := by
  rcases i with ⟨l,q⟩
  rcases j with ⟨k,r⟩
  have h : l = k := Fin.ext hl
  subst k
  have h : q = r := Fin.ext hq
  subst r
  rfl

/-- Root plus the left member of every native reflection pair. -/
def finiteDyadicHaarReflectionPick (m : ℕ) :
    Option (FiniteDyadicHaarIndex m) → FiniteDyadicHaarIndex (m+1)
  | none => ⟨⟨0,by omega⟩,⟨0,by norm_num⟩⟩
  | some i => ⟨⟨i.1.val+1,by have := i.1.isLt; omega⟩,
      ⟨i.2.val,by have := i.2.isLt; simp only [pow_succ]; omega⟩⟩

theorem finiteDyadicHaarReflectionPick_injective (m : ℕ) :
    Function.Injective (finiteDyadicHaarReflectionPick m) := by
  intro i j h
  have hl := congrArg (fun x : FiniteDyadicHaarIndex (m+1) => x.1.val) h
  have hq := congrArg (fun x : FiniteDyadicHaarIndex (m+1) => x.2.val) h
  cases i <;> cases j
  · rfl
  · simp [finiteDyadicHaarReflectionPick] at hl
  · simp [finiteDyadicHaarReflectionPick] at hl
  · simp only [finiteDyadicHaarReflectionPick, Nat.add_right_cancel_iff] at hl hq
    congr 1
    exact finiteDyadicHaarIndex_ext hl hq

theorem finiteDyadicHaarReflectionPick_root (m : ℕ) :
    finiteDyadicHaarReflect (m+1) (finiteDyadicHaarReflectionPick m none) =
      finiteDyadicHaarReflectionPick m none := by
  apply finiteDyadicHaarIndex_ext <;> rfl

theorem finiteDyadicHaarReflectionPick_disjoint (m : ℕ)
    (i j : FiniteDyadicHaarIndex m) :
    finiteDyadicHaarReflectionPick m (some i) ≠
      finiteDyadicHaarReflect (m+1) (finiteDyadicHaarReflectionPick m (some j)) := by
  intro h
  have hl := congrArg (fun x : FiniteDyadicHaarIndex (m+1) => x.1.val) h
  have hq := congrArg (fun x : FiniteDyadicHaarIndex (m+1) => x.2.val) h
  dsimp [finiteDyadicHaarReflectionPick, finiteDyadicHaarReflect, Fin.rev] at hl hq
  have hl' : i.1.val = j.1.val := by omega
  have hi := i.2.isLt
  have hj := j.2.isLt
  rw [pow_succ] at hq
  have hp := congrArg (fun k : ℕ => 2^k) hl'
  omega

theorem finiteDyadicHaarReflectionPick_exhaustive (m : ℕ)
    (i : FiniteDyadicHaarIndex (m+1)) :
    (∃ j, i = finiteDyadicHaarReflectionPick m j) ∨
      (∃ j, i = finiteDyadicHaarReflect (m+1) (finiteDyadicHaarReflectionPick m (some j))) := by
  by_cases hl : i.1.val = 0
  · left
    refine ⟨none, finiteDyadicHaarIndex_ext hl ?_⟩
    have hq := i.2.isLt
    have hp : 2^i.1.val = 1 := by rw [hl]; norm_num
    change i.2.val = 0
    omega
  · have hm : i.1.val-1 < m := by have := i.1.isLt; omega
    have he : i.1.val-1+1 = i.1.val := by omega
    have hp : 2^i.1.val = 2^(i.1.val-1)*2 := by rw [← pow_succ, he]
    by_cases hq : i.2.val < 2^(i.1.val-1)
    · left
      refine ⟨some ⟨⟨i.1.val-1,hm⟩,⟨i.2.val,hq⟩⟩, ?_⟩
      apply finiteDyadicHaarIndex_ext
      · exact he.symm
      · rfl
    · right
      have hv : 2^i.1.val-(i.2.val+1) < 2^(i.1.val-1) := by
        have := i.2.isLt
        omega
      refine ⟨⟨⟨i.1.val-1,hm⟩,⟨2^i.1.val-(i.2.val+1),hv⟩⟩, ?_⟩
      apply finiteDyadicHaarIndex_ext
      · exact he.symm
      · dsimp [finiteDyadicHaarReflect, finiteDyadicHaarReflectionPick, Fin.rev]
        rw [he]
        have := i.2.isLt
        omega

/-- Complete native reflection coordinates for every positive dyadic level. -/
def finiteDyadicHaarReflectionOrbits (m : ℕ) :
    ReflectionOrbitSystem (FiniteDyadicHaarIndex (m+1)) (FiniteDyadicHaarIndex m) where
  reflect := finiteDyadicHaarReflect (m+1)
  involutive := finiteDyadicHaarReflect_involutive (m+1)
  pick := finiteDyadicHaarReflectionPick m
  pick_injective := finiteDyadicHaarReflectionPick_injective m
  root_fixed := finiteDyadicHaarReflectionPick_root m
  pairs_disjoint := finiteDyadicHaarReflectionPick_disjoint m
  exhaustive := finiteDyadicHaarReflectionPick_exhaustive m

/-- Pull block lower bounds back through the exact unnormalized reflection Gram. -/
theorem ReflectionOrbitSystem.lower_of_blocks {n κ : Type*}
    [Fintype n] [Fintype κ] [DecidableEq n] [DecidableEq κ]
    (s : ReflectionOrbitSystem n κ) (K : Matrix n n ℝ) (ε : ℝ)
    (hK : ∀ i j, K (s.reflect i) (s.reflect j) = K i j)
    (hodd : ∀ v : Option κ → ℝ,
      ε * dotProduct v ((Matrix.diagonal (fun i : Option κ => if i = none then 1 else 2)).mulVec v) ≤
        dotProduct v ((involutionOddBlock s.reflect s.pick reflectionOrbitWeight K).mulVec v))
    (heven : ∀ v : κ → ℝ,
      ε * dotProduct v ((Matrix.diagonal (fun _ : κ => 2)).mulVec v) ≤
        dotProduct v ((involutionEvenBlock s.reflect (fun i => s.pick (some i)) K).mulVec v))
    (c : n → ℝ) : ε * (∑ i, (c i)^2) ≤ dotProduct c (K.mulVec c) := by
  let v := s.coordinates c
  have hv : s.columns.mulVec v = c := s.columns_mulVec_coordinates c
  have hnorm := realMatrix_congruence_quadratic s.columns (1 : Matrix n n ℝ) v
  rw [Matrix.mul_one, s.columns_gram, hv, ← realMatrix_norm_eq_quadratic] at hnorm
  have hquad := realMatrix_congruence_quadratic s.columns K v
  have hc := involutionReflectionColumns_congruence s.reflect s.involutive s.pick
    (fun i => s.pick (some i)) reflectionOrbitWeight K hK
  change s.columns.transpose * K * s.columns = _ at hc
  rw [hc, hv] at hquad
  rw [← hnorm, ← hquad, realMatrix_blockDiagonal_quadratic, realMatrix_blockDiagonal_quadratic,
    mul_add]
  exact add_le_add (hodd (v ∘ Sum.inl)) (heven (v ∘ Sum.inr))

/-- Rational scalar interval endpoints are executable exact certificate data. -/
def rationalIntervalLower (w l u : ℚ) : ℚ := if 0 ≤ w then w*l else w*u
def rationalIntervalUpper (w l u : ℚ) : ℚ := if 0 ≤ w then w*u else w*l

theorem rationalInterval_cast (w l u : ℚ) :
    ((rationalIntervalLower w l u : ℚ) : ℝ) = signedIntervalLower w l u ∧
    ((rationalIntervalUpper w l u : ℚ) : ℝ) = signedIntervalUpper w l u := by
  by_cases hw : 0 ≤ w
  · have hw' : (0:ℝ) ≤ w := by exact_mod_cast hw
    simp [rationalIntervalLower, rationalIntervalUpper, signedIntervalLower,
      signedIntervalUpper, hw, hw']
  · have hw' : ¬(0:ℝ) ≤ w := by exact_mod_cast hw
    simp [rationalIntervalLower, rationalIntervalUpper, signedIntervalLower,
      signedIntervalUpper, hw, hw']

def rationalAffineLower {κ : Type*} [Fintype κ] (d : ℚ) (w l u : κ → ℚ) : ℚ :=
  d + ∑ k, rationalIntervalLower (w k) (l k) (u k)

def rationalAffineUpper {κ : Type*} [Fintype κ] (d : ℚ) (w l u : κ → ℚ) : ℚ :=
  d + ∑ k, rationalIntervalUpper (w k) (l k) (u k)

/-- A single sign-aware theorem validates every rational affine matrix entry. -/
theorem rationalAffine_bounds {κ : Type*} [Fintype κ] (d : ℚ) (w l u : κ → ℚ)
    (p : κ → ℝ) (hl : ∀ k, (l k : ℝ) ≤ p k) (hu : ∀ k, p k ≤ (u k : ℝ)) :
    (rationalAffineLower d w l u : ℝ) ≤ (d : ℝ)+∑ k, (w k : ℝ)*p k ∧
    (d : ℝ)+∑ k, (w k : ℝ)*p k ≤ (rationalAffineUpper d w l u : ℝ) := by
  have h := signedInterval_finset_sum_bounds Finset.univ (fun k => (w k : ℝ))
    (fun k => (l k : ℝ)) p (fun k => (u k : ℝ)) (fun k _ => hl k) (fun k _ => hu k)
  simp only [rationalAffineLower, rationalAffineUpper, Rat.cast_add, Rat.cast_sum]
  simp_rw [(rationalInterval_cast _ _ _).1, (rationalInterval_cast _ _ _).2]
  exact ⟨add_le_add (le_refl (d:ℝ)) h.1, add_le_add (le_refl (d:ℝ)) h.2⟩

/-- Executable rational row conditions certify a real affine matrix as positive definite. -/
theorem realMatrix_posDef_of_rationalAffine_certificate
    {n κ : Type*} [Fintype n] [Fintype κ] [DecidableEq n]
    (A : Matrix n n ℝ) (d : Matrix n n ℚ) (w : n → n → κ → ℚ)
    (l u : κ → ℚ) (p : κ → ℝ) (hA : A.IsHermitian)
    (hp : ∀ k, (l k : ℝ) ≤ p k ∧ p k ≤ (u k : ℝ))
    (hentry : ∀ i j, A i j = (d i j : ℝ) + ∑ k, (w i j k : ℝ)*p k)
    (hdd : ∀ i, (∑ j ∈ Finset.univ.erase i,
      max |rationalAffineLower (d i j) (w i j) l u|
        |rationalAffineUpper (d i j) (w i j) l u|) <
          rationalAffineLower (d i i) (w i i) l u) : A.PosDef := by
  apply realMatrix_posDef_of_intervals
    (fun i j => (rationalAffineLower (d i j) (w i j) l u : ℝ))
    (fun i j => (rationalAffineUpper (d i j) (w i j) l u : ℝ)) hA
  · intro i j
    rw [hentry]
    exact (rationalAffine_bounds (d i j) (w i j) l u p (fun k => (hp k).1) (fun k => (hp k).2)).1
  · intro i j
    rw [hentry]
    exact (rationalAffine_bounds (d i j) (w i j) l u p (fun k => (hp k).1) (fun k => (hp k).2)).2
  · intro i
    exact_mod_cast hdd i

/-- A rational unit-upper shear is certified without determinant expansion. -/
theorem realMatrix_isUnit_of_unit_upper {n : Type*} [Fintype n] [DecidableEq n]
    [LinearOrder n] (S : Matrix n n ℝ) (hupper : S.IsUpperTriangular)
    (hdiag : ∀ i, S i i = 1) : IsUnit S := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isUpperTriangular hupper]
  simp [hdiag]

/-- End-to-end data-driven affine interval/shear certificate with rational row tests. -/
theorem realMatrix_lower_of_rationalAffine_shear
    {n κ : Type*} [Fintype n] [Fintype κ] [DecidableEq n]
    (K G S : Matrix n n ℝ) (ε : ℝ)
    (d : Matrix n n ℚ) (w : n → n → κ → ℚ) (l u : κ → ℚ) (p : κ → ℝ)
    (hK : K.IsHermitian) (hG : G.IsHermitian) (hS : IsUnit S)
    (hp : ∀ k, (l k : ℝ) ≤ p k ∧ p k ≤ (u k : ℝ))
    (hentry : ∀ i j, (S.transpose * (K-ε • G) * S) i j =
      (d i j : ℝ) + ∑ k, (w i j k : ℝ)*p k)
    (hdd : ∀ i, (∑ j ∈ Finset.univ.erase i,
      max |rationalAffineLower (d i j) (w i j) l u|
        |rationalAffineUpper (d i j) (w i j) l u|) <
          rationalAffineLower (d i i) (w i i) l u)
    (c : n → ℝ) : ε * dotProduct c (G.mulVec c) ≤ dotProduct c (K.mulVec c) := by
  apply realMatrix_lower_of_shear S K G ε hS
  exact (realMatrix_posDef_of_rationalAffine_certificate _ d w l u p
    (realMatrix_congruence_isHermitian S (hK.sub (hG.smul (by simp [IsSelfAdjoint]))))
    hp hentry hdd).posSemidef

/-- Conditional finite and actual transfer; the sole numerical premise is an auxiliary lower bound. -/
theorem arithmeticFiniteHaarModel_sixteenth_lower_transfer (m J : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε)
    (haux : ∀ c : FiniteDyadicHaarIndex m → ℝ,
      ε * (∑ i, (c i)^2) ≤
        dotProduct c ((arithmeticFiniteHaarModel (5373/2000) (1/16) m 2 J).mulVec c)) :
    (∀ c : FiniteDyadicHaarIndex m → ℝ,
      ε * (∑ i, (c i)^2) ≤ dotProduct c ((arithmeticScrewApproxHaarMatrix (1/16) m 2 J).mulVec c)) ∧
    (arithmeticScrewApproxHaarMatrix (1/16) m 2 J).PosSemidef ∧
    (∀ c : FiniteDyadicHaarIndex m → ℝ,
      ε * (∑ i, (c i)^2) ≤ dotProduct c ((arithmeticScrewHaarMatrix (1/16) m).mulVec c)) ∧
    (arithmeticScrewHaarMatrix (1/16) m).PosSemidef := by
  have hf (c : FiniteDyadicHaarIndex m → ℝ) := (haux c).trans
    (arithmeticFiniteHaarModel_auxiliary_le_finite (by norm_num) m 2 J c)
  have ha (c : FiniteDyadicHaarIndex m → ℝ) :=
    (hf c).trans (arithmeticScrewApproxHaarMatrix_sixteenth_le_actual m J c)
  refine ⟨hf, ?_, ha, ?_⟩
  · apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    refine ⟨arithmeticScrewApproxHaarMatrix_isHermitian _ _ _ _, fun c => ?_⟩
    simpa only [star_trivial] using
      (mul_nonneg hε (Finset.sum_nonneg (fun i _ => sq_nonneg (c i)))).trans (hf c)
  · apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    refine ⟨arithmeticScrewHaarMatrix_isHermitian _ _, fun c => ?_⟩
    simpa only [star_trivial] using
      (mul_nonneg hε (Finset.sum_nonneg (fun i _ => sq_nonneg (c i)))).trans (ha c)

/-- The literal signed J=5 cell matrix is an even Toeplitz matrix at every level. -/
theorem arithmeticFiniteCellMatrix_fiveModes_toeplitz (C R : ℝ) (m : ℕ)
    (i j : Fin (2^m)) :
    arithmeticFiniteCellMatrix C R m 2 5 i j =
      finiteDyadicPrimitiveToeplitz (fun t => fourthLevelPrimitive C |t|)
        (dyadicCellWidth R m) ((i.val:ℤ)-j.val) := by
  rw [arithmeticFiniteCellMatrix_fiveModes_primitive]
  simpa only [finiteDyadicGridEndpoint, Fin.val_castSucc, Fin.val_succ,
    Nat.cast_add, Nat.cast_one, Int.cast_natCast, mul_comm] using
      secondPrimitiveCell_uniform_toeplitz (fun t => fourthLevelPrimitive C |t|)
        (-R) (dyadicCellWidth R m) (i.val:ℤ) (j.val:ℤ)

def arithmeticFiniteOddBlock (C R : ℝ) (m : ℕ) :
    Matrix (Option (FiniteDyadicHaarIndex m)) (Option (FiniteDyadicHaarIndex m)) ℝ :=
  involutionOddBlock (finiteDyadicHaarReflect (m+1)) (finiteDyadicHaarReflectionPick m)
    reflectionOrbitWeight (arithmeticFiniteHaarModel C R (m+1) 2 5)

def arithmeticFiniteEvenBlock (C R : ℝ) (m : ℕ) :
    Matrix (FiniteDyadicHaarIndex m) (FiniteDyadicHaarIndex m) ℝ :=
  involutionEvenBlock (finiteDyadicHaarReflect (m+1))
    (fun i => finiteDyadicHaarReflectionPick m (some i))
    (arithmeticFiniteHaarModel C R (m+1) 2 5)

/-- Native quantitative lower bound from the two reflection blocks at any level. -/
theorem arithmeticFiniteHaarModel_fiveModes_lower_of_blocks (C R ε : ℝ) (m : ℕ)
    (hodd : ∀ v : Option (FiniteDyadicHaarIndex m) → ℝ,
      ε * dotProduct v ((Matrix.diagonal (fun i => if i = none then 1 else 2)).mulVec v) ≤
        dotProduct v ((arithmeticFiniteOddBlock C R m).mulVec v))
    (heven : ∀ v : FiniteDyadicHaarIndex m → ℝ,
      ε * dotProduct v ((Matrix.diagonal (fun _ => 2)).mulVec v) ≤
        dotProduct v ((arithmeticFiniteEvenBlock C R m).mulVec v))
    (c : FiniteDyadicHaarIndex (m+1) → ℝ) :
    ε * (∑ i, (c i)^2) ≤ dotProduct c ((arithmeticFiniteHaarModel C R (m+1) 2 5).mulVec c) :=
  (finiteDyadicHaarReflectionOrbits m).lower_of_blocks _ ε
    (arithmeticFiniteHaarModel_fiveModes_reflect C R (m+1)) hodd heven c

/-- Entrywise congruence as a finite linear form in the original entries. -/
theorem realMatrix_congruence_apply {n m : Type*} [Fintype n] [Fintype m]
    (S : Matrix n m ℝ) (B : Matrix n n ℝ) (i j : m) :
    (S.transpose * B * S) i j = ∑ a, ∑ b, (S a i*S b j)*B a b := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

def rationalCongruenceLower {n m : Type*} [Fintype n]
    (S : Matrix n m ℚ) (L U : Matrix n n ℚ) (i j : m) : ℚ :=
  ∑ a, ∑ b, rationalIntervalLower (S a i*S b j) (L a b) (U a b)

def rationalCongruenceUpper {n m : Type*} [Fintype n]
    (S : Matrix n m ℚ) (L U : Matrix n n ℚ) (i j : m) : ℚ :=
  ∑ a, ∑ b, rationalIntervalUpper (S a i*S b j) (L a b) (U a b)

/-- Exact interval propagation through any rational rectangular congruence. -/
theorem rationalCongruence_bounds {n m : Type*} [Fintype n] [Fintype m]
    (S : Matrix n m ℚ) (L U : Matrix n n ℚ) (B : Matrix n n ℝ)
    (hB : ∀ a b, (L a b : ℝ) ≤ B a b ∧ B a b ≤ (U a b : ℝ)) (i j : m) :
    (rationalCongruenceLower S L U i j : ℝ) ≤
      ((S.map (fun q : ℚ => (q:ℝ))).transpose * B * S.map (fun q : ℚ => (q:ℝ))) i j ∧
    ((S.map (fun q : ℚ => (q:ℝ))).transpose * B * S.map (fun q : ℚ => (q:ℝ))) i j ≤
      (rationalCongruenceUpper S L U i j : ℝ) := by
  rw [realMatrix_congruence_apply]
  have h := rationalAffine_bounds (0:ℚ)
    (fun ab : n×n => S ab.1 i*S ab.2 j)
    (fun ab : n×n => L ab.1 ab.2) (fun ab : n×n => U ab.1 ab.2)
    (fun ab : n×n => B ab.1 ab.2)
    (fun ab => (hB ab.1 ab.2).1) (fun ab => (hB ab.1 ab.2).2)
  simpa only [rationalAffineLower, rationalAffineUpper, rationalCongruenceLower,
    rationalCongruenceUpper, Fintype.sum_prod_type, Rat.cast_zero, zero_add, Rat.cast_mul,
    Matrix.map_apply] using h

/-- Matrix intervals followed by rational shear margins give the native Gram lower bound. -/
theorem realMatrix_lower_of_rational_interval_shear
    {n : Type*} [Fintype n] [DecidableEq n]
    (K G : Matrix n n ℝ) (S L U : Matrix n n ℚ) (ε : ℝ)
    (hK : K.IsHermitian) (hG : G.IsHermitian)
    (hS : IsUnit (S.map (fun q : ℚ => (q:ℝ))))
    (hB : ∀ i j, (L i j : ℝ) ≤ (K-ε • G) i j ∧ (K-ε • G) i j ≤ (U i j : ℝ))
    (hdd : ∀ i, (∑ j ∈ Finset.univ.erase i,
      max |rationalCongruenceLower S L U i j| |rationalCongruenceUpper S L U i j|) <
        rationalCongruenceLower S L U i i)
    (c : n → ℝ) : ε * dotProduct c (G.mulVec c) ≤ dotProduct c (K.mulVec c) := by
  apply realMatrix_lower_of_interval_shear K G (S.map (fun q : ℚ => (q:ℝ)))
    (fun i j => (rationalCongruenceLower S L U i j : ℝ))
    (fun i j => (rationalCongruenceUpper S L U i j : ℝ)) ε hK hG hS
  · intro i j
    exact (rationalCongruence_bounds S L U (K-ε • G) hB i j).1
  · intro i j
    exact (rationalCongruence_bounds S L U (K-ε • G) hB i j).2
  · intro i
    exact_mod_cast hdd i

end
end RiemannResearch.RH
