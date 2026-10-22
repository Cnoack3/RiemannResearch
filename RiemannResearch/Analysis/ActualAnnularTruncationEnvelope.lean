import RiemannResearch.Analysis.ActualAnnularTruncationMembership
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# An explicit unconditional finite annular norm envelope

Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

The exact finite cutoff and actual von Mangoldt coefficients are retained.
The sharp global arithmetic-weight bound 0 <= W <= 7/24 bounds the
nonnegative prime sum. Centering bounds the signed signal by the maximum
of this prime-sum bound and the nonnegative centering term. Multiplying
this sharper B(X)^2 by the exact weighted cutoff mass then bounds the
actual finite weighted Mellin energy.

This is a finite bound for every real a and X. It supplies no asymptotic
cancellation bound, infinite-vector membership, prime-pair estimate, or RH.
The weighted cutoff mass is an actual integral, not a symbolic placeholder.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.WeightedMellinTopology
open MeasureTheory.WeightedMellin
open RiemannResearch.RH
open RiemannResearch.RH.AnnularPrimePair

/-- Explicit finite amplitude bound, retaining all prime powers and the
sign of the nonnegative prime sum before centering. -/
def finiteCutoffAmplitude (X : ℝ) : ℝ :=
  max ((7 / 24 : ℝ) * (∑ n ∈ indices X, ArithmeticFunction.vonMangoldt n))
    ((7 / 64 : ℝ) * max (1 : ℝ) X)

theorem finiteCutoffAmplitude_nonneg (X : ℝ) :
    0 ≤ finiteCutoffAmplitude X := by
  have hs : 0 ≤ (∑ n ∈ indices X, ArithmeticFunction.vonMangoldt n) :=
    Finset.sum_nonneg (fun n _ => ArithmeticFunction.vonMangoldt_nonneg)
  unfold finiteCutoffAmplitude
  exact (mul_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 24) hs).trans (le_max_left _ _)

/-- Pointwise control of the actual centered arithmetic signal on [1,X]. -/
theorem actualAnnularVector_norm_le_finiteCutoffAmplitude {x X : ℝ}
    (hx : x ∈ Icc (1 : ℝ) X) :
    ‖actualAnnularVector x‖ ≤ finiteCutoffAmplitude X := by
  have hs0 : 0 ≤ (∑ n ∈ indices X,
      ArithmeticFunction.vonMangoldt n * annularArithmeticWeight ((n : ℝ) / x)) :=
    Finset.sum_nonneg (fun n _ => mul_nonneg
      ArithmeticFunction.vonMangoldt_nonneg (annularArithmeticWeight_nonnegative _))
  have hs : (∑ n ∈ indices X,
      ArithmeticFunction.vonMangoldt n * annularArithmeticWeight ((n : ℝ) / x)) ≤
      (7 / 24 : ℝ) * (∑ n ∈ indices X, ArithmeticFunction.vonMangoldt n) := by
    calc
      _ ≤ ∑ n ∈ indices X, ArithmeticFunction.vonMangoldt n * (7 / 24 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        exact mul_le_mul_of_nonneg_left
          (annularArithmeticWeight_le_seven_twentyfourths _)
          ArithmeticFunction.vonMangoldt_nonneg
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        ring
  have hx0 : 0 ≤ x := zero_le_one.trans hx.1
  have hxm : x ≤ max (1 : ℝ) X := hx.2.trans (le_max_right 1 X)
  have hcenter0 : 0 ≤ (7 / 64 : ℝ) * x := mul_nonneg (by norm_num) hx0
  have hcenter : (7 / 64 : ℝ) * x ≤ (7 / 64 : ℝ) * max (1 : ℝ) X :=
    mul_le_mul_of_nonneg_left hxm (by norm_num)
  have hleft := le_max_left
    ((7 / 24 : ℝ) * (∑ n ∈ indices X, ArithmeticFunction.vonMangoldt n))
    ((7 / 64 : ℝ) * max (1 : ℝ) X)
  have hright := le_max_right
    ((7 / 24 : ℝ) * (∑ n ∈ indices X, ArithmeticFunction.vonMangoldt n))
    ((7 / 64 : ℝ) * max (1 : ℝ) X)
  change ‖(actualPrimeSignal x : ℂ)‖ ≤ finiteCutoffAmplitude X
  rw [Complex.norm_real, Real.norm_eq_abs,
    actualPrimeSignal_eq_fixed_cutoff hx.1 hx.2]
  unfold annularPrimeFinite finiteCutoffAmplitude
  apply abs_le.mpr
  constructor <;> linarith

/-- The real density of the exact weighted cutoff mass. -/
def weightedCutoffDensity (a X : ℝ) : ℝ → ℝ :=
  (Icc (1 : ℝ) X).indicator (fun x : ℝ => x ^ (-(2 * a) - 1))

/-- Exact finite mass in the H_a measure. -/
def weightedCutoffMass (a X : ℝ) : ℝ :=
  ∫ x in Ioi (1 : ℝ), weightedCutoffDensity a X x

theorem weightedCutoffDensity_integrable (a X : ℝ) :
    Integrable (weightedCutoffDensity a X) := by
  have hw : ContinuousOn (fun x : ℝ => x ^ (-(2 * a) - 1)) (Icc (1 : ℝ) X) := by
    apply continuousOn_id.rpow_const
    intro x hx
    exact Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1))
  exact hw.integrableOn_Icc.integrable_indicator measurableSet_Icc

theorem weightedCutoffDensity_nonneg (a X x : ℝ) :
    0 ≤ weightedCutoffDensity a X x := by
  unfold weightedCutoffDensity
  by_cases hx : x ∈ Icc (1 : ℝ) X
  · rw [indicator_of_mem hx]
    exact Real.rpow_nonneg (zero_le_one.trans hx.1) _
  · simp only [indicator_of_notMem hx, le_refl]

theorem weightedCutoffMass_nonneg (a X : ℝ) :
    0 ≤ weightedCutoffMass a X := by
  unfold weightedCutoffMass
  exact integral_nonneg_of_ae
    (Filter.Eventually.of_forall (weightedCutoffDensity_nonneg a X))

/-- The integrand domination is pointwise; no exceptional arithmetic values
or zero ordinates are discarded. -/
theorem actualAnnularTruncation_density_le (a X x : ℝ) :
    ‖actualAnnularTruncation X x‖ ^ 2 * x ^ (-(2 * a) - 1) ≤
      finiteCutoffAmplitude X ^ 2 * weightedCutoffDensity a X x := by
  by_cases hx : x ∈ Icc (1 : ℝ) X
  · have hn := actualAnnularVector_norm_le_finiteCutoffAmplitude hx
    have hB := finiteCutoffAmplitude_nonneg X
    have hsq : ‖actualAnnularVector x‖ ^ 2 ≤ finiteCutoffAmplitude X ^ 2 := by
      have hp : 0 ≤ (finiteCutoffAmplitude X - ‖actualAnnularVector x‖) *
          (finiteCutoffAmplitude X + ‖actualAnnularVector x‖) :=
        mul_nonneg (sub_nonneg.mpr hn)
          (add_nonneg hB (norm_nonneg (actualAnnularVector x)))
      nlinarith
    simp only [actualAnnularTruncation, weightedCutoffDensity, indicator_of_mem hx]
    exact mul_le_mul_of_nonneg_right hsq
      (Real.rpow_nonneg (zero_le_one.trans hx.1) _)
  · simp only [actualAnnularTruncation, weightedCutoffDensity, indicator_of_notMem hx,
      norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, le_refl]

/-- Explicit finite energy envelope for the actual centered arithmetic vector.
The statement also covers X<1, when the cutoff is empty. -/
theorem actualAnnularTruncation_normSquared_le (a X : ℝ) :
    normSquared a (actualAnnularTruncation X) ≤
      finiteCutoffAmplitude X ^ 2 * weightedCutoffMass a X := by
  have hmem := actualAnnularTruncation_Ha a X
  have hmajor : IntegrableOn
      (fun x : ℝ => finiteCutoffAmplitude X ^ 2 * weightedCutoffDensity a X x)
      (Ioi (1 : ℝ)) :=
    ((weightedCutoffDensity_integrable a X).const_mul _).integrableOn
  unfold normSquared energy
  calc
    _ ≤ ∫ x in Ioi (1 : ℝ),
        finiteCutoffAmplitude X ^ 2 * weightedCutoffDensity a X x :=
      integral_mono_ae hmem.2 hmajor
        (Filter.Eventually.of_forall (actualAnnularTruncation_density_le a X))
    _ = _ := by
      rw [integral_const_mul]
      rfl

/-- This discharges an actual finite norm-envelope proposition rather than
assuming a provider of prime cancellation. -/
theorem actualTruncationExplicitEnvelope (a : ℝ) :
    ActualTruncationEnvelope a
      (fun X => finiteCutoffAmplitude X ^ 2 * weightedCutoffMass a X) := by
  intro X hX
  exact actualAnnularTruncation_normSquared_le a X

/-- Every admissible full-zero evaluation of the actual finite vector has
an unconditional explicit finite bound. -/
theorem actualTruncation_explicit_fullZero_evaluation_bound
    {ι : Type*} (D : RiemannResearch.RH.AnnularZeroSpectral.FullZeroData ι) (i : ι)
    {a X : ℝ} (ha : a < (D.rho i).re) :
    ‖transform (actualAnnularTruncation X) (D.rho i)‖ ^ 2 ≤
      (finiteCutoffAmplitude X ^ 2 * weightedCutoffMass a X) /
        (2 * ((D.rho i).re - a)) := by
  exact actualTruncation_fullZero_evaluation_bound D i
    (N := fun Y => finiteCutoffAmplitude Y ^ 2 * weightedCutoffMass a Y)
    (actualAnnularTruncation_Ha a X)
    (actualAnnularTruncation_normSquared_le a X) ha

end RiemannResearch.Analysis.WeightedMellinTopology
