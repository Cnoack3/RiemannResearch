import RiemannResearch.RH.ParetoMellinFiniteGram
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Optimal finite Mellin certificates in Ramanujan coordinates

Source: user-requested second ten-transfer program, 23 October 2026.
The Cauchy-Gram completion extends the original lower bound to an exact
variational identity. Normal equations suffice even for singular or repeated
zero families. The explicit inverse branch retains nonsingularity as a named
hypothesis. Full Mellin remainders and packet competitor excesses are preserved.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto
variable {ι : Type*} [Fintype ι]

def mellinGramPairing (s c d : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (c i) * d j * mellinCauchyGram s i j

def mellinCharge (s b c : ι → ℂ) : ℝ :=
  2 * (∑ i, starRingEnd ℂ (c i) * b i).re - (mellinGramQuadratic s c).re

omit [Fintype ι] in
theorem mellinCauchyGram_conj (s : ι → ℂ) (i j : ι) :
    starRingEnd ℂ (mellinCauchyGram s i j) = mellinCauchyGram s j i := by
  have hconj (z : ℂ) : starRingEnd ℂ (starRingEnd ℂ z) = z := by
    change star (star z) = z
    exact star_star z
  simp only [mellinCauchyGram, map_div₀, map_one, map_sub, map_add, hconj]
  congr 1
  ring

theorem mellinGramPairing_conj (s c d : ι → ℂ) :
    starRingEnd ℂ (mellinGramPairing s c d) = mellinGramPairing s d c := by
  classical
  have hconj (z : ℂ) : starRingEnd ℂ (starRingEnd ℂ z) = z := by
    change star (star z) = z
    exact star_star z
  simp only [mellinGramPairing, map_sum, map_mul, hconj, mellinCauchyGram_conj]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem mellinGramPairing_re_symm (s c d : ι → ℂ) :
    (mellinGramPairing s c d).re = (mellinGramPairing s d c).re := by
  have h := congrArg Complex.re (mellinGramPairing_conj s c d)
  simpa only [Complex.conj_re] using h

theorem mellinGramPairing_eq_of_normal (s c d b : ι → ℂ)
    (hn : ∀ i, ∑ j, mellinCauchyGram s i j * d j = b i) :
    mellinGramPairing s c d = ∑ i, starRingEnd ℂ (c i) * b i := by
  classical
  unfold mellinGramPairing
  apply Finset.sum_congr rfl
  intro i _
  rw [← hn i, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem mellinGramQuadratic_sub (s c d : ι → ℂ) :
    mellinGramQuadratic s (c - d) =
      mellinGramQuadratic s c + mellinGramQuadratic s d -
        mellinGramPairing s c d - mellinGramPairing s d c := by
  classical
  simp only [mellinGramQuadratic, mellinGramPairing, Pi.sub_apply,
    map_sub, sub_mul, mul_sub, Finset.sum_sub_distrib]
  ring

/-- Exact maximization of the signed charge; a normal solution suffices. -/
theorem mellinCharge_completion (s b c d : ι → ℂ)
    (hn : ∀ i, ∑ j, mellinCauchyGram s i j * d j = b i) :
    mellinCharge s b d = mellinCharge s b c +
      (mellinGramQuadratic s (c - d)).re := by
  have hs := congrArg Complex.re (mellinGramQuadratic_sub s c d)
  have hc := congrArg Complex.re (mellinGramPairing_eq_of_normal s c d b hn)
  have hd := congrArg Complex.re (mellinGramQuadratic_eq_of_normal s d b hn)
  have hsym := mellinGramPairing_re_symm s c d
  simp only [Complex.add_re, Complex.sub_re] at hs
  unfold mellinCharge
  linarith

theorem mellinCharge_le_normal (s b c d : ι → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hn : ∀ i, ∑ j, mellinCauchyGram s i j * d j = b i) :
    mellinCharge s b c ≤ mellinCharge s b d := by
  have hnonneg : 0 ≤ (mellinGramQuadratic s (c - d)).re := by
    rw [← finiteMellinKernel_energy s (c - d) hs]
    exact integral_nonneg (fun _ => sq_nonneg _)
  linarith [mellinCharge_completion s b c d hn]

theorem mellinCharge_eq_normal_iff (s b c d : ι → ℂ)
    (hn : ∀ i, ∑ j, mellinCauchyGram s i j * d j = b i) :
    mellinCharge s b c = mellinCharge s b d ↔
      (mellinGramQuadratic s (c - d)).re = 0 := by
  have h := mellinCharge_completion s b c d hn
  constructor <;> intro he <;> linarith

/-- Strengthening the original normal lower bound to its full exact remainder. -/
theorem finiteMellinKernel_normal_completion (f : ThresholdHilbert) (s c : ι → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hn : ∀ i, ∑ j, mellinCauchyGram s i j * c j = paretoMellin f (s i)) :
    ‖f‖ ^ 2 = (∑ i, starRingEnd ℂ (c i) * paretoMellin f (s i)).re +
      ∫ x in Ioi (1 : ℝ),
        ‖mellinWeightedStep f x - starRingEnd ℂ (finiteMellinKernel s c x)‖ ^ 2 := by
  have h := finiteMellinKernel_remainder f s c hs
  rw [mellinGramQuadratic_eq_of_normal s c _ hn] at h
  linarith

def mellinInverseCoefficients [DecidableEq ι] (s b : ι → ℂ) : ι → ℂ :=
  (mellinCauchyGram s)⁻¹.mulVec b

def mellinInverseCapacity [DecidableEq ι] (s b : ι → ℂ) : ℝ :=
  (∑ i, starRingEnd ℂ (mellinInverseCoefficients s b i) * b i).re

theorem mellinInverseCoefficients_normal [DecidableEq ι] (s b : ι → ℂ)
    (hdet : (mellinCauchyGram s).det ≠ 0) :
    ∀ i, ∑ j, mellinCauchyGram s i j * mellinInverseCoefficients s b j = b i := by
  have he : (mellinCauchyGram s).mulVec (mellinInverseCoefficients s b) = b := by
    unfold mellinInverseCoefficients
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
  intro i
  exact congrFun he i

theorem mellinCharge_inverse [DecidableEq ι] (s b : ι → ℂ)
    (hdet : (mellinCauchyGram s).det ≠ 0) :
    mellinCharge s b (mellinInverseCoefficients s b) = mellinInverseCapacity s b := by
  have h := congrArg Complex.re (mellinGramQuadratic_eq_of_normal s
    (mellinInverseCoefficients s b) b (mellinInverseCoefficients_normal s b hdet))
  unfold mellinCharge mellinInverseCapacity
  linarith

/-- The optimized capacity is exactly the energy of its complete Mellin kernel. -/
theorem mellinInverseCapacity_eq_kernel_energy [DecidableEq ι] (s b : ι → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hdet : (mellinCauchyGram s).det ≠ 0) :
    mellinInverseCapacity s b =
      ∫ x in Ioi (1 : ℝ),
        ‖finiteMellinKernel s (mellinInverseCoefficients s b) x‖ ^ 2 := by
  rw [finiteMellinKernel_energy s (mellinInverseCoefficients s b) hs]
  have h := congrArg Complex.re (mellinGramQuadratic_eq_of_normal s
    (mellinInverseCoefficients s b) b (mellinInverseCoefficients_normal s b hdet))
  exact h.symm

theorem mellinInverseCapacity_nonneg [DecidableEq ι] (s b : ι → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hdet : (mellinCauchyGram s).det ≠ 0) :
    0 ≤ mellinInverseCapacity s b := by
  rw [mellinInverseCapacity_eq_kernel_energy s b hs hdet]
  exact integral_nonneg (fun _ => sq_nonneg _)

theorem finiteMellinKernel_inverse_completion [DecidableEq ι]
    (f : ThresholdHilbert) (s : ι → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hdet : (mellinCauchyGram s).det ≠ 0) :
    ‖f‖ ^ 2 = mellinInverseCapacity s (fun i => paretoMellin f (s i)) +
      ∫ x in Ioi (1 : ℝ),
        ‖mellinWeightedStep f x - starRingEnd ℂ (finiteMellinKernel s
          (mellinInverseCoefficients s (fun i => paretoMellin f (s i))) x)‖ ^ 2 :=
  finiteMellinKernel_normal_completion f s _ hs
    (mellinInverseCoefficients_normal s _ hdet)

end RiemannResearch.RH.Pareto
