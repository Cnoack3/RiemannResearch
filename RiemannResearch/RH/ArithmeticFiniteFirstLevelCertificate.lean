/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.ArithmeticFiniteFirstLevel

/-!
# A positive first-level arithmetic certificate

This module evaluates the exact unnormalized level-one Haar entry with prime
cutoff two. It proves, by rational Taylor bounds, that the nonzero finite
approximation at `R = 1/16`, `N = 2`, and `J = 4` has a strictly
positive diagonal and is positive semidefinite. The previously proved signed
tail comparison then transfers nonnegativity to the actual arithmetic Haar
matrix at this single window and level.

The complete `Finset.range 2` von Mangoldt sum is retained and proved zero;
the polar, linear/pole, and four archimedean contributions keep their original
signs and the Haar atom remains unnormalized. This fixed-level certificate is
not all-level arithmetic positivity, completed-Weil positivity, or RH.

Source: user-provided RH continuation and
RH_Local_to_Global_Trace_Attack_Plan_2026-09-05.pdf support the exact
finite-cell strategy. The rational enclosures are proved from Mathlib bounds.
-/

set_option maxRecDepth 4096

open scoped BigOperators
open RiemannResearch.Analysis RiemannResearch.RH.PrimeGapCurvature

namespace RiemannResearch.RH
noncomputable section

/-- The first positive-window certificate uses a genuinely admissible prime
cutoff. -/
theorem arithmeticScrewApprox_sixteenth_cutoff :
    Real.exp (2 * (1/16 : ℝ)) < (2 : ℕ) := by
  have h := Real.exp_bound' (x := (1/8 : ℝ)) (by norm_num) (by norm_num)
    (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

/-- The signed contribution of subtracting one archimedean cell kernel from
the unnormalized level-one Haar form. -/
theorem archimedeanScrewCell_one_contribution
    {R : ℝ} (hR : 0 ≤ R) (k : ℕ) :
    -archimedeanScrewCell k (-R) 0 (-R) 0 +
      archimedeanScrewCell k (-R) 0 0 R +
      archimedeanScrewCell k 0 R (-R) 0 -
      archimedeanScrewCell k 0 R 0 R =
    4 * archimedeanWeight k *
      (4*R / archimedeanRate k +
       (-6 + 8*Real.exp (-archimedeanRate k*R) -
         2*Real.exp (-2*archimedeanRate k*R)) /
           (archimedeanRate k)^2) := by
  unfold archimedeanScrewCell exponentialAbsCell
    exponentialAbsSecondPrimitive
  have h2R : 0 ≤ 2*R := by positivity
  simp only [sub_neg_eq_add, zero_add, add_zero, sub_zero, sub_self, zero_sub,
    abs_neg, abs_of_nonneg hR, abs_zero, mul_zero, Real.exp_zero]
  rw [show R+R=2*R by ring, show -R-R=-(2*R) by ring]
  simp only [abs_neg, abs_of_nonneg h2R]
  have ha := ne_of_gt (archimedeanRate_pos k)
  rw [show -archimedeanRate k*(2*R)=-2*archimedeanRate k*R by ring]
  field_simp
  ring

/-- Exact scalar contribution of the subtracted `k`th archimedean term to
the unnormalized level-one Haar entry. -/
def firstLevelArchimedeanContribution (R : ℝ) (k : ℕ) : ℝ :=
  4 * archimedeanWeight k *
    (4*R / archimedeanRate k +
      (-6 + 8*Real.exp (-archimedeanRate k*R) -
        2*Real.exp (-2*archimedeanRate k*R)) /
          (archimedeanRate k)^2)

/-- Exact level-one entry for prime cutoff two and arbitrary archimedean
cutoff. The full range-two von Mangoldt sum is retained in the proof and
vanishes because its weights at zero and one are zero. -/
theorem arithmeticScrewApproxHaarMatrix_one_two_entry
    {R : ℝ} (hR : 0 ≤ R) (J : ℕ) :
    arithmeticScrewApproxHaarMatrix R 1 2 J
        finiteDyadicHaarIndexOne finiteDyadicHaarIndexOne =
      32*(Real.exp (R/2)+Real.exp (-R/2)-2)^2 -
        4/3*screwLinearCoefficient*R^3 +
          ∑ k ∈ Finset.range J, firstLevelArchimedeanContribution R k := by
  have harch := Finset.sum_congr (s₁ := Finset.range J) rfl
    (fun k _ => archimedeanScrewCell_one_contribution hR k)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib] at harch
  have hprime (a b c d : ℝ) :
      (∑ n ∈ Finset.range 2, primePowerHingeCell n a b c d) = 0 := by
    norm_num [Finset.sum_range_succ, primePowerHingeCell, primePowerWeight]
  rw [arithmeticScrewApproxHaarMatrix_one_entry]
  simp only [arithmeticScrewApproxCell, hprime, add_zero]
  unfold firstLevelArchimedeanContribution
  rw [← harch]
  have h2R : 0 ≤ 2*R := by positivity
  simp only [screwPolarCell, exponentialCell, secondPrimitiveCell,
    absCell, hingeKernelSecondPrimitive]
  norm_num
  have hp : Real.exp R = Real.exp (R/2)^2 := by
    calc
      Real.exp R = Real.exp (R/2+R/2) := congrArg Real.exp (by ring)
      _ = _ := by rw [Real.exp_add, pow_two]
  have hn : Real.exp (-R) = Real.exp (-R/2)^2 := by
    calc
      Real.exp (-R) = Real.exp (-R/2+(-R/2)) :=
        congrArg Real.exp (by ring)
      _ = _ := by rw [Real.exp_add, pow_two]
  have hprod : Real.exp (R/2)*Real.exp (-R/2) = 1 := by
    rw [← Real.exp_add]
    simp [show R/2+-R/2 = 0 by ring]
  ring_nf at hp hn hprod ⊢
  simp only [max_eq_left hR, max_eq_right (show -R ≤ 0 by linarith),
    max_eq_left (show 0 ≤ R*2 by positivity),
    max_eq_right (show -(R*2) ≤ 0 by linarith),
    zero_pow (by decide : 3 ≠ 0), mul_zero]
  rw [hp, hn]
  nlinarith only [hprod]

/-- Rational lower bound for the polar contribution at `R = 1/16`. -/
theorem sixteenth_polar_lower :
    (3/100000 : ℝ) ≤
      32*(Real.exp (1/32 : ℝ)+Real.exp (-1/32 : ℝ)-2)^2 := by
  have hp := Real.exp_bound (x := (1/32 : ℝ)) (by norm_num)
    (n := 4) (by norm_num)
  have hn := Real.exp_bound (x := (-1/32 : ℝ)) (by norm_num)
    (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ] at hp hn
  have hl : (97/100000 : ℝ) ≤
      Real.exp (1/32 : ℝ)+Real.exp (-1/32 : ℝ)-2 := by
    linarith [(abs_le.mp hp).1, (abs_le.mp hn).1]
  nlinarith [sq_nonneg
    (Real.exp (1/32 : ℝ)+Real.exp (-1/32 : ℝ)-2 - 97/100000)]

set_option maxHeartbeats 1000000 in
-- The eight twelfth-order exponential enclosures need extra elaboration time.
/-- Rational lower bound for the first four archimedean contributions at
`R = 1/16`. -/
theorem sixteenth_archimedean_lower :
    (84824/100000000 : ℝ) ≤
      ∑ k ∈ Finset.range 4, firstLevelArchimedeanContribution (1/16) k := by
  have h0 := Real.exp_bound (x := (-1/32 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h1 := Real.exp_bound (x := (-2/32 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h2 := Real.exp_bound (x := (-5/32 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h3 := Real.exp_bound (x := (-10/32 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h4 := Real.exp_bound (x := (-9/32 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h5 := Real.exp_bound (x := (-18/32 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h6 := Real.exp_bound (x := (-13/32 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  have h7 := Real.exp_bound (x := (-26/32 : ℝ))
    (by norm_num) (n := 12) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4 h5 h6 h7
  norm_num [Finset.sum_range_succ, firstLevelArchimedeanContribution,
    archimedeanWeight, archimedeanRate]
  linarith [(abs_le.mp h0).1, (abs_le.mp h1).2,
    (abs_le.mp h2).1, (abs_le.mp h3).2,
    (abs_le.mp h4).1, (abs_le.mp h5).2,
    (abs_le.mp h6).1, (abs_le.mp h7).2]

/-- Exact rational upper bound for Euler's constant used by the certificate. -/
theorem eulerMascheroniConstant_le_291_div_500 :
    Real.eulerMascheroniConstant ≤ (291/500 : ℝ) := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 128
  have hH : (harmonic 128 : ℝ) < 2717/500 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hlog := Real.log_two_gt_d9
  have hlog128 : Real.log (128 : ℝ) = 7 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 7 using 1 <;> norm_num
  norm_num [Real.eulerMascheroniSeq'] at h
  rw [hlog128] at h
  linarith

/-- Exact rational upper bound for `log π` used by the certificate. -/
theorem log_pi_le_229_div_200 :
    Real.log Real.pi ≤ (229/200 : ℝ) := by
  have hπ := Real.pi_lt_d4
  have he := Real.exp_one_gt_d9
  have hx := Real.exp_bound (x := (29/200 : ℝ))
    (by norm_num) (n := 5) (by norm_num)
  norm_num [Finset.sum_range_succ] at hx
  have hlower := (abs_le.mp hx).1
  have hxpos := Real.exp_pos (29/200 : ℝ)
  apply (Real.log_le_iff_le_exp Real.pi_pos).mpr
  have heq :
      Real.exp (229/200 : ℝ) =
        Real.exp 1 * Real.exp (29/200 : ℝ) := by
    rw [← Real.exp_add]
    congr 1
    norm_num
  rw [heq]
  nlinarith

/-- The live linear/pole coefficient is bounded sharply enough for the first
positive certificate. -/
theorem screwLinearCoefficient_le_269_div_100 :
    screwLinearCoefficient ≤ (269/100 : ℝ) := by
  have hg := eulerMascheroniConstant_le_291_div_500
  have hl := log_pi_le_229_div_200
  have h2 := Real.log_two_lt_d9
  have hπ := Real.pi_lt_d4
  unfold screwLinearCoefficient
  linarith

/-- Exact scalar expression for the certified finite entry. -/
theorem arithmeticScrewApproxHaarMatrix_sixteenth_two_four_entry :
    arithmeticScrewApproxHaarMatrix (1/16) 1 2 4
        finiteDyadicHaarIndexOne finiteDyadicHaarIndexOne =
      32 * (Real.exp (1/32) + Real.exp (-1/32) - 2)^2 -
        screwLinearCoefficient/3072 +
        ∑ k ∈ Finset.range 4,
          firstLevelArchimedeanContribution (1/16) k := by
  rw [arithmeticScrewApproxHaarMatrix_one_two_entry
    (by norm_num : (0 : ℝ) ≤ 1/16)]
  norm_num
  ring

/-- The unique entry has a strict, exact rational positive margin. -/
theorem arithmeticScrewApproxHaarMatrix_sixteenth_two_four_diag_gt :
    (1/500000 : ℝ) <
      arithmeticScrewApproxHaarMatrix (1/16) 1 2 4
        finiteDyadicHaarIndexOne finiteDyadicHaarIndexOne := by
  rw [arithmeticScrewApproxHaarMatrix_sixteenth_two_four_entry]
  linarith [sixteenth_polar_lower, sixteenth_archimedean_lower,
    screwLinearCoefficient_le_269_div_100]

/-- The first nonempty, nonzero-window Lean-certified finite arithmetic
approximation is positive semidefinite. -/
theorem arithmeticScrewApproxHaarMatrix_sixteenth_two_four_posSemidef :
    (arithmeticScrewApproxHaarMatrix (1/16) 1 2 4).PosSemidef := by
  rw [arithmeticScrewApproxHaarMatrix_one_posSemidef_iff]
  linarith
    [arithmeticScrewApproxHaarMatrix_sixteenth_two_four_diag_gt]

/-- The actual arithmetic Haar matrix is Hermitian at every window and finite
level. -/
theorem arithmeticScrewHaarMatrix_isHermitian (R : ℝ) (m : ℕ) :
    (arithmeticScrewHaarMatrix R m).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  unfold arithmeticScrewHaarMatrix
  apply finiteDyadicHaarCompression_symm
  apply dyadicCellKernel_symm R m
    (fun x y => arithmeticScrewFunction (x-y))
    (continuous_arithmeticScrewFunction.comp
      (continuous_fst.sub continuous_snd))
  intro x y
  rw [show x-y=-(y-x) by ring, arithmeticScrewFunction_neg]

/-- Native fixed-level PSD transfer from one admissible finite PSD
approximation to the actual arithmetic Haar matrix. -/
theorem arithmeticScrewHaarMatrix_posSemidef_of_approx_posSemidef
    {R : ℝ} (hR : 0 ≤ R) (m N J : ℕ)
    (hN : Real.exp (2 * R) < N)
    (hpos : (arithmeticScrewApproxHaarMatrix R m N J).PosSemidef) :
    (arithmeticScrewHaarMatrix R m).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨arithmeticScrewHaarMatrix_isHermitian R m, ?_⟩
  simpa only [star_trivial] using
    arithmeticScrewHaarMatrix_nonneg_of_approx_posSemidef
      hR m N J hN hpos

/-- The first certified finite approximation transfers to native PSD of the
actual arithmetic Haar matrix at this same window and level only. -/
theorem arithmeticScrewHaarMatrix_sixteenth_one_posSemidef :
    (arithmeticScrewHaarMatrix (1/16) 1).PosSemidef :=
  arithmeticScrewHaarMatrix_posSemidef_of_approx_posSemidef
    (by norm_num) 1 2 4 arithmeticScrewApprox_sixteenth_cutoff
    arithmeticScrewApproxHaarMatrix_sixteenth_two_four_posSemidef

end
end RiemannResearch.RH
