/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.Analysis.TranslationKernelCellIntegral
import RiemannResearch.RH.ArithmeticFiniteApproxPositivity

/-!
# Exact finite entries of the arithmetic screw approximation

This module evaluates every finite arithmetic approximation cell as the literal
signed sum of its polar, full von Mangoldt prime-power, linear, and truncated
archimedean pieces, then expands the existing unnormalized Haar compression
entry by entry. It proves exact finite algebra only: no finite PSD certificate,
completed-Weil identification, arithmetic positivity, or RH conclusion.

Source: the exact-cell and signed arithmetic assembly in the user-provided
RH_Local_to_Global_Trace_Attack_Plan_2026-09-05.pdf support the statements and
proof strategy.
-/

open MeasureTheory Set
open scoped BigOperators

namespace RiemannResearch.RH
open RiemannResearch.Analysis RiemannResearch.RH.PrimeGapCurvature
noncomputable section

def screwPolarCell (b₁ d₁ b₂ d₂ : ℝ) : ℝ :=
  -4 * (exponentialCell (1/2) b₁ d₁ b₂ d₂ +
    exponentialCell (-1/2) b₁ d₁ b₂ d₂ - 2*(d₁-b₁)*(d₂-b₂))

theorem integral_integral_screwPolarPart (b₁ d₁ b₂ d₂ : ℝ) :
    (∫ x in b₁..d₁, ∫ y in b₂..d₂, screwPolarPart (x-y)) =
      screwPolarCell b₁ d₁ b₂ d₂ := by
  have hp : Continuous (Function.uncurry
      (fun x y : ℝ => Real.exp ((1/2)*(x-y)))) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_fst.sub continuous_snd))
  have hn : Continuous (Function.uncurry
      (fun x y : ℝ => Real.exp ((-1/2)*(x-y)))) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_fst.sub continuous_snd))
  have he (t : ℝ) : screwPolarPart t =
      -4 * (Real.exp ((1/2)*t) + Real.exp ((-1/2)*t) - 2) := by
    simp only [screwPolarPart,
      show (1/2 : ℝ)*t = t/2 by ring,
      show (-1/2 : ℝ)*t = -t/2 by ring]
  simp_rw [he, intervalIntegral.integral_const_mul]
  rw [← RiemannResearch.Analysis.integral_integral_sub
    (k := fun x y => Real.exp ((1/2)*(x-y)) + Real.exp ((-1/2)*(x-y)))
    (l := fun _ _ => 2) (hp.add hn) continuous_const,
    RiemannResearch.Analysis.integral_integral_add hp hn,
    integral_integral_exp_mul_sub (by norm_num : (1/2 : ℝ) ≠ 0),
    integral_integral_exp_mul_sub (by norm_num : (-1/2 : ℝ) ≠ 0)]
  simp [screwPolarCell, intervalIntegral.integral_const, smul_eq_mul]
  ring

def archimedeanScrewCell (k : ℕ) (b₁ d₁ b₂ d₂ : ℝ) : ℝ :=
  4 * ((d₁-b₁)*(d₂-b₂) -
    exponentialAbsCell (archimedeanRate k) b₁ d₁ b₂ d₂) * archimedeanWeight k

theorem integral_integral_archimedeanScrewTerm (k : ℕ) (b₁ d₁ b₂ d₂ : ℝ) :
    (∫ x in b₁..d₁, ∫ y in b₂..d₂, archimedeanScrewTerm k (x-y)) =
      archimedeanScrewCell k b₁ d₁ b₂ d₂ := by
  have he : Continuous (Function.uncurry
      (fun x y : ℝ => Real.exp (-archimedeanRate k * |x-y|))) :=
    Real.continuous_exp.comp
      (continuous_const.mul ((continuous_fst.sub continuous_snd).abs))
  simp_rw [archimedeanScrewTerm, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_const_mul]
  rw [← RiemannResearch.Analysis.integral_integral_sub
    (k := fun _ _ => 1) (l := fun x y => Real.exp (-archimedeanRate k * |x-y|))
    continuous_const he, integral_integral_exp_neg_mul_abs (ne_of_gt (archimedeanRate_pos k))]
  simp only [archimedeanScrewCell, intervalIntegral.integral_const, smul_eq_mul, mul_one]

theorem integral_integral_sum_archimedeanScrewTerm (J : ℕ) (b₁ d₁ b₂ d₂ : ℝ) :
    (∫ x in b₁..d₁, ∫ y in b₂..d₂,
      ∑ k ∈ Finset.range J, archimedeanScrewTerm k (x-y)) =
      ∑ k ∈ Finset.range J, archimedeanScrewCell k b₁ d₁ b₂ d₂ := by
  rw [RiemannResearch.Analysis.integral_integral_finsetSum (Finset.range J)
    (fun k x y => archimedeanScrewTerm k (x-y))
    (fun k _ => (continuous_archimedeanScrewTerm k).comp
      (continuous_fst.sub continuous_snd))]
  simp_rw [integral_integral_archimedeanScrewTerm]

/-- Exact signed finite arithmetic rectangle; no positivity is asserted. -/
def arithmeticScrewApproxCell (N J : ℕ) (b₁ d₁ b₂ d₂ : ℝ) : ℝ :=
  screwPolarCell b₁ d₁ b₂ d₂ +
    (∑ n ∈ Finset.range N, primePowerHingeCell n b₁ d₁ b₂ d₂) +
    screwLinearCoefficient * absCell b₁ d₁ b₂ d₂ -
    ∑ k ∈ Finset.range J, archimedeanScrewCell k b₁ d₁ b₂ d₂

theorem integral_integral_arithmeticScrewApprox (N J : ℕ) (b₁ d₁ b₂ d₂ : ℝ) :
    (∫ x in b₁..d₁, ∫ y in b₂..d₂, arithmeticScrewApprox N J (x-y)) =
      arithmeticScrewApproxCell N J b₁ d₁ b₂ d₂ := by
  have hp : Continuous (Function.uncurry (fun x y : ℝ => screwPolarPart (x-y))) :=
    continuous_screwPolarPart.comp (continuous_fst.sub continuous_snd)
  have hq : Continuous (Function.uncurry
      (fun x y : ℝ => ∑ n ∈ Finset.range N, primePowerHingeTerm n (x-y))) :=
    (continuous_finsetSum _ (fun n _ => continuous_primePowerHingeTerm n)).comp
      (continuous_fst.sub continuous_snd)
  have hl : Continuous (Function.uncurry
      (fun x y : ℝ => screwLinearCoefficient * |x-y|)) :=
    continuous_const.mul ((continuous_fst.sub continuous_snd).abs)
  have ha : Continuous (Function.uncurry
      (fun x y : ℝ => ∑ k ∈ Finset.range J, archimedeanScrewTerm k (x-y))) :=
    (continuous_finsetSum _ (fun k _ => continuous_archimedeanScrewTerm k)).comp
      (continuous_fst.sub continuous_snd)
  unfold arithmeticScrewApprox
  rw [← RiemannResearch.Analysis.integral_integral_sub
    (k := fun x y => screwPolarPart (x-y) +
      (∑ n ∈ Finset.range N, primePowerHingeTerm n (x-y)) +
      screwLinearCoefficient * |x-y|)
    (l := fun x y => ∑ k ∈ Finset.range J, archimedeanScrewTerm k (x-y))
    ((hp.add hq).add hl) ha,
    RiemannResearch.Analysis.integral_integral_add
      (k := fun x y => screwPolarPart (x-y) +
        ∑ n ∈ Finset.range N, primePowerHingeTerm n (x-y))
      (l := fun x y => screwLinearCoefficient * |x-y|) (hp.add hq) hl,
    RiemannResearch.Analysis.integral_integral_add hp hq,
    integral_integral_screwPolarPart, integral_integral_sum_primePowerHingeTerm,
    integral_integral_sum_archimedeanScrewTerm]
  simp_rw [intervalIntegral.integral_const_mul]
  rw [integral_integral_abs_sub]
  rfl

/-- Every dyadic approximation cell, with the literal signed finite pieces. -/
theorem dyadicCell_arithmeticScrewApprox_eq_finite (R : ℝ) (m N J : ℕ)
    (i j : Fin (2 ^ m)) :
    dyadicCellKernel R m (fun x y => arithmeticScrewApprox N J (x-y)) i j =
      screwPolarCell (dyadicCellLeft R m i) (dyadicCellRight R m i)
        (dyadicCellLeft R m j) (dyadicCellRight R m j) +
      (∑ n ∈ Finset.range N, primePowerHingeCell n
        (dyadicCellLeft R m i) (dyadicCellRight R m i)
        (dyadicCellLeft R m j) (dyadicCellRight R m j)) +
      screwLinearCoefficient * absCell
        (dyadicCellLeft R m i) (dyadicCellRight R m i)
        (dyadicCellLeft R m j) (dyadicCellRight R m j) -
      ∑ k ∈ Finset.range J, archimedeanScrewCell k
        (dyadicCellLeft R m i) (dyadicCellRight R m i)
        (dyadicCellLeft R m j) (dyadicCellRight R m j) :=
  integral_integral_arithmeticScrewApprox N J
    (dyadicCellLeft R m i) (dyadicCellRight R m i)
    (dyadicCellLeft R m j) (dyadicCellRight R m j)

/-- Exact unnormalized Hᵀ K H entries. All endpoint orientations are allowed. -/
theorem arithmeticScrewApproxHaarMatrix_entry (R : ℝ) (m N J : ℕ)
    (a b : FiniteDyadicHaarIndex m) :
    arithmeticScrewApproxHaarMatrix R m N J a b =
      ∑ i : Fin (2 ^ m), ∑ j : Fin (2 ^ m),
        finiteDyadicHaarAtom m a.1.val a.2 i *
        (screwPolarCell (dyadicCellLeft R m i) (dyadicCellRight R m i)
          (dyadicCellLeft R m j) (dyadicCellRight R m j) +
        (∑ n ∈ Finset.range N, primePowerHingeCell n
          (dyadicCellLeft R m i) (dyadicCellRight R m i)
          (dyadicCellLeft R m j) (dyadicCellRight R m j)) +
        screwLinearCoefficient * absCell
          (dyadicCellLeft R m i) (dyadicCellRight R m i)
          (dyadicCellLeft R m j) (dyadicCellRight R m j) -
        ∑ k ∈ Finset.range J, archimedeanScrewCell k
          (dyadicCellLeft R m i) (dyadicCellRight R m i)
          (dyadicCellLeft R m j) (dyadicCellRight R m j)) *
        finiteDyadicHaarAtom m b.1.val b.2 j := by
  unfold arithmeticScrewApproxHaarMatrix
  rw [finiteDyadicHaarCompression_apply]
  simp_rw [Matrix.mulVec, dotProduct, Finset.mul_sum,
    dyadicCell_arithmeticScrewApprox_eq_finite, mul_assoc]

end
end RiemannResearch.RH
