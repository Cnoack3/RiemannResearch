/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.FiniteEndpointProfile
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The finite Dirichlet Green matrix

This module gives a closed formula for the endpoint-zero profile produced by
unit-grid finite curvature data. Its columns are the responses to standard
curvature vectors, and its interior restriction is a symmetric, entrywise
nonpositive matrix. The sign is negative because this project uses the
positive second-difference convention for finite curvature.

Source: user-provided argument,
RH_Proof_First_Continuation_2026-09-04.md, Section 5. The source supports the
finite coordinate and gauge strategy. This finite-dimensional inverse does
not identify a Weil form, establish dyadic density, or prove RH.
-/

namespace RiemannResearch.RH.PrimeGapCurvature

noncomputable section

open scoped BigOperators

/-- The standard coordinate vector in finite curvature space. -/
def finStandardBasis (n : ℕ) (i : Fin n) : Fin n → ℝ :=
  fun j => if j = i then 1 else 0

/-- The endpoint-zero Green response at profile node `k` to unit curvature
at `i`. -/
def finiteDirichletGreenKernel (n : ℕ)
    (k : Fin (n + 2)) (i : Fin n) : ℝ :=
  if k.val ≤ i.val + 1 then
    -((k.val : ℝ) * ((n - i.val : ℕ) : ℝ) /
      ((n + 1 : ℕ) : ℝ))
  else
    -((((i.val + 1 : ℕ) : ℝ) *
      (((n + 1 - k.val : ℕ) : ℝ))) /
      ((n + 1 : ℕ) : ℝ))

/-- The Green matrix obtained by restricting the kernel to interior nodes. -/
def finiteDirichletGreenMatrix (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun r i => finiteDirichletGreenKernel n r.succ.castSucc i

@[simp] theorem finiteDirichletGreenKernel_zero
    (n : ℕ) (i : Fin n) :
    finiteDirichletGreenKernel n (0 : Fin (n + 2)) i = 0 := by
  simp [finiteDirichletGreenKernel]

@[simp] theorem finiteDirichletGreenKernel_last
    (n : ℕ) (i : Fin n) :
    finiteDirichletGreenKernel n (Fin.last (n + 1)) i = 0 := by
  simp [finiteDirichletGreenKernel]

/-- Every Green-kernel entry is nonpositive. -/
theorem finiteDirichletGreenKernel_nonpos
    (n : ℕ) (k : Fin (n + 2)) (i : Fin n) :
    finiteDirichletGreenKernel n k i ≤ 0 := by
  unfold finiteDirichletGreenKernel
  split
  · apply neg_nonpos.mpr
    positivity
  · apply neg_nonpos.mpr
    positivity

/-- A Green column has Kronecker-delta unit-grid curvature. -/
theorem finiteCurvature_finiteDirichletGreenKernel
    (n : ℕ) (i j : Fin n) :
    finiteCurvature (unitFiniteGap n)
      (fun k => finiteDirichletGreenKernel n k i) j =
      if j = i then 1 else 0 := by
  unfold finiteCurvature finiteAdjacentSlope
  simp only [unitFiniteGap_apply, div_one]
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rcases lt_trichotomy j.val i.val with hlt | heq | hgt
  · have hji : j ≠ i := by
      intro h
      simp [h] at hlt
    rw [if_neg hji]
    simp only [finiteDirichletGreenKernel,
      if_pos (show j.succ.succ.val ≤ i.val + 1 by simp; omega),
      if_pos (show j.succ.castSucc.val ≤ i.val + 1 by simp; omega),
      if_pos (show j.castSucc.succ.val ≤ i.val + 1 by simp; omega),
      if_pos (show j.castSucc.castSucc.val ≤ i.val + 1 by simp; omega)]
    simp
    field_simp [hn]
    ring
  · have hji : j = i := Fin.ext heq
    subst j
    rw [if_pos rfl]
    simp only [finiteDirichletGreenKernel,
      if_neg (show ¬ i.succ.succ.val ≤ i.val + 1 by simp),
      if_pos (show i.succ.castSucc.val ≤ i.val + 1 by simp),
      if_pos (show i.castSucc.succ.val ≤ i.val + 1 by simp),
      if_pos (show i.castSucc.castSucc.val ≤ i.val + 1 by simp)]
    simp
    field_simp [hn]
    ring
  · have hji : j ≠ i := by
      intro h
      simp [h] at hgt
    rw [if_neg hji]
    by_cases hadj : j.val = i.val + 1
    · have hcast : (j.val : ℝ) = (i.val : ℝ) + 1 := by
        exact_mod_cast hadj
      simp only [finiteDirichletGreenKernel,
        if_neg (show ¬ j.succ.succ.val ≤ i.val + 1 by simp; omega),
        if_neg (show ¬ j.succ.castSucc.val ≤ i.val + 1 by simp; omega),
        if_neg (show ¬ j.castSucc.succ.val ≤ i.val + 1 by simp; omega),
        if_pos (show j.castSucc.castSucc.val ≤ i.val + 1 by simp; omega)]
      simp only [Nat.cast_add, Nat.cast_one, Fin.val_succ,
        Nat.reduceSubDiff, Order.add_one_le_iff, Fin.is_lt, Nat.cast_sub,
        Fin.castSucc_succ, Fin.val_castSucc, Fin.is_le', sub_neg_eq_add]
      rw [hcast]
      field_simp [hn]
      ring
    · have hle : j.val ≤ n + 1 := by omega
      have hsub : (((n + 1 - j.val : ℕ) : ℝ)) =
          ((n + 1 : ℕ) : ℝ) - (j.val : ℝ) :=
        Nat.cast_sub hle
      simp only [finiteDirichletGreenKernel,
        if_neg (show ¬ j.succ.succ.val ≤ i.val + 1 by simp; omega),
        if_neg (show ¬ j.succ.castSucc.val ≤ i.val + 1 by simp; omega),
        if_neg (show ¬ j.castSucc.succ.val ≤ i.val + 1 by simp; omega),
        if_neg (show ¬ j.castSucc.castSucc.val ≤ i.val + 1 by simp; omega)]
      simp only [Nat.cast_add, Nat.cast_one, Fin.val_succ,
        Nat.reduceSubDiff, Order.add_one_le_iff, Fin.is_lt, Nat.cast_sub,
        Fin.castSucc_succ, Fin.val_castSucc, Fin.is_le', sub_neg_eq_add]
      rw [hsub]
      push_cast
      field_simp [hn]
      ring

/-- A standard curvature vector is sent to the corresponding Green column. -/
theorem centeredProfileSection_standardBasis
    (n : ℕ) (i : Fin n) :
    centeredProfileSectionLinearMap n (finStandardBasis n i) =
      fun k => finiteDirichletGreenKernel n k i := by
  let z : Fin (n + 2) → ℝ :=
    fun k => finiteDirichletGreenKernel n k i
  have hcurv : finiteCurvature (unitFiniteGap n) z =
      finStandardBasis n i := by
    funext j
    exact finiteCurvature_finiteDirichletGreenKernel n i j
  rw [← hcurv]
  exact centeredProfileSection_finiteCurvature_of_endpoints_zero
    n z (finiteDirichletGreenKernel_zero n i)
      (finiteDirichletGreenKernel_last n i)

/-- Every centered endpoint-zero profile is the Green superposition of its
curvature coordinates. -/
theorem centeredProfileSection_eq_green_sum
    (n : ℕ) (c : Fin n → ℝ) (k : Fin (n + 2)) :
    centeredProfileSectionLinearMap n c k =
      ∑ i, c i * finiteDirichletGreenKernel n k i := by
  have hdecomp :
      (∑ i, c i • finStandardBasis n i) = c := by
    funext j
    simp [finStandardBasis, Pi.smul_apply, smul_eq_mul]
  calc
    centeredProfileSectionLinearMap n c k =
        centeredProfileSectionLinearMap n
          (∑ i, c i • finStandardBasis n i) k := by
      exact congrArg
        (fun d => centeredProfileSectionLinearMap n d k)
        hdecomp.symm
    _ = ∑ i, c i * finiteDirichletGreenKernel n k i := by
      simp only [map_sum, Finset.sum_apply, map_smul, Pi.smul_apply,
        smul_eq_mul]
      simp_rw [centeredProfileSection_standardBasis]

/-- Matrix multiplication evaluates the Green profile at interior nodes. -/
theorem finiteDirichletGreenMatrix_mulVec
    (n : ℕ) (c : Fin n → ℝ) (r : Fin n) :
    (finiteDirichletGreenMatrix n).mulVec c r =
      centeredProfileSectionLinearMap n c r.succ.castSucc := by
  rw [centeredProfileSection_eq_green_sum]
  rw [Matrix.mulVec_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [finiteDirichletGreenMatrix]
  ring

/-- The interior Green matrix is symmetric, pointwise. -/
theorem finiteDirichletGreenMatrix_apply_comm
    (n : ℕ) (r i : Fin n) :
    finiteDirichletGreenMatrix n r i =
      finiteDirichletGreenMatrix n i r := by
  rcases lt_trichotomy r.val i.val with hlt | heq | hgt
  · have hsub : n + 1 - (i.val + 1) = n - i.val := by omega
    simp only [finiteDirichletGreenMatrix, finiteDirichletGreenKernel,
      if_pos (show r.succ.castSucc.val ≤ i.val + 1 by simp; omega),
      if_neg (show ¬ i.succ.castSucc.val ≤ r.val + 1 by simp; omega)]
    simp [hsub]
  · have hri : r = i := Fin.ext heq
    subst r
    rfl
  · have hsub : n + 1 - (r.val + 1) = n - r.val := by omega
    simp only [finiteDirichletGreenMatrix, finiteDirichletGreenKernel,
      if_neg (show ¬ r.succ.castSucc.val ≤ i.val + 1 by simp; omega),
      if_pos (show i.succ.castSucc.val ≤ r.val + 1 by simp; omega)]
    simp [hsub]

/-- The interior Green matrix equals its transpose. -/
theorem finiteDirichletGreenMatrix_symm (n : ℕ) :
    Matrix.IsSymm (finiteDirichletGreenMatrix n) := by
  apply Matrix.IsSymm.ext
  intro r i
  exact finiteDirichletGreenMatrix_apply_comm n i r

/-- The Green superposition has exactly the prescribed unit-grid curvature. -/
theorem finiteCurvature_green_sum
    (n : ℕ) (c : Fin n → ℝ) :
    finiteCurvature (unitFiniteGap n)
      (fun k => ∑ i, c i * finiteDirichletGreenKernel n k i) = c := by
  have hprofile :
      (fun k => ∑ i, c i * finiteDirichletGreenKernel n k i) =
        centeredProfileSectionLinearMap n c := by
    funext k
    exact (centeredProfileSection_eq_green_sum n c k).symm
  rw [hprofile]
  exact finiteCurvature_centeredProfileSection n c

end

end RiemannResearch.RH.PrimeGapCurvature
