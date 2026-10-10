import RiemannResearch.Analysis.SignedLatticeEnergy
import RiemannResearch.RH.ActualAnnularKernel
import RiemannResearch.RH.AnnularLatticeBounds

/-!
# Complete signed critical-energy transfer for actual annular signals

Actual arithmetic growth uses only vonMangoldt_le_log.  The sharp actual
lattice estimate proves the previously open ActualLatticeDecay provider.
The energy difference is uniformly bounded by 1105/5832 at every real
cutoff, converges to its absolutely convergent signed integral, and transfers
logarithmic energy bounds in both directions.  The RH energy criterion and
actual signed-residual bound remain independent analytic obligations.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.AnnularCriticalEnergy
open RiemannResearch.RH.AnnularPrimePair
open RiemannResearch.Analysis.SignedLatticeEnergy

theorem actualCentered_growth {x : ℝ} (hx : 1 ≤ x) :
    |actualCentered x| ≤ (7 / 24 : ℝ) * x * (1 + Real.log x) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hcard : ((indices x).card : ℝ) ≤ x := by
    simpa [indices, Nat.card_Icc] using (Nat.floor_le hx0.le)
  unfold actualCentered annularCenteredFinite
  calc
    _ ≤ ∑ n ∈ indices x,
        |(ArithmeticFunction.vonMangoldt n - 1) * annularArithmeticWeight (n / x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ indices x, (7 / 24 : ℝ) * (1 + Real.log x) := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hn1, hnf⟩ := Finset.mem_Icc.mp hn
      have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
      have hnx : (n : ℝ) ≤ x :=
        (by exact_mod_cast hnf : (n : ℝ) ≤ (Nat.floor x : ℝ)).trans (Nat.floor_le hx0.le)
      have hΛ0 : 0 ≤ ArithmeticFunction.vonMangoldt n :=
        ArithmeticFunction.vonMangoldt_nonneg
      have hΛx : ArithmeticFunction.vonMangoldt n ≤ Real.log x :=
        ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hn0 hnx)
      have hΛabs : |ArithmeticFunction.vonMangoldt n - 1| ≤ 1 + Real.log x := by
        have hn := norm_sub_le (ArithmeticFunction.vonMangoldt n) (1 : ℝ)
        simp only [Real.norm_eq_abs, abs_of_nonneg hΛ0, abs_one] at hn
        linarith
      rw [abs_mul, abs_of_nonneg (annularArithmeticWeight_nonnegative _)]
      have hw := annularArithmeticWeight_le_seven_twentyfourths (n / x)
      calc
        _ ≤ (1 + Real.log x) * (7 / 24 : ℝ) :=
          mul_le_mul hΛabs hw (annularArithmeticWeight_nonnegative _)
            (by positivity)
        _ = _ := by ring
    _ = ((indices x).card : ℝ) * ((7 / 24 : ℝ) * (1 + Real.log x)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ x * ((7 / 24 : ℝ) * (1 + Real.log x)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

theorem actualCentered_continuousOn_Ioi :
    ContinuousOn actualCentered (Ioi (1 : ℝ)) :=
  continuousOn_Ioi_of_continuousOn_Icc actualCentered_continuousOn

theorem actualCentered_correction_integrableOn {δ : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hδcont : ∀ X : ℝ, ContinuousOn δ (Icc (1 : ℝ) X))
    (hδ : ∀ x : ℝ, 1 ≤ x → |δ x| ≤ C / x ^ 2) :
    IntegrableOn (signedCorrectionDensity actualCentered δ) (Ioi (1 : ℝ)) :=
  signedCorrectionDensity_integrableOn (by norm_num) hC
    actualCentered_continuousOn_Ioi (continuousOn_Ioi_of_continuousOn_Icc hδcont)
    (fun x hx => actualCentered_growth hx) hδ

theorem actualCentered_correction_uniform_bound {δ : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hδcont : ∀ X : ℝ, ContinuousOn δ (Icc (1 : ℝ) X))
    (hδ : ∀ x : ℝ, 1 ≤ x → |δ x| ≤ C / x ^ 2) (X : ℝ) :
    |signedCorrectionCutoff actualCentered δ X| ≤ (7 / 16 : ℝ) * C + C ^ 2 / 5 := by
  have hf := actualCentered_correction_integrableOn hC hδcont hδ
  have h := signedCorrectionCutoff_uniform_bound (by norm_num : (0 : ℝ) ≤ 7 / 24)
    hC hf (fun x hx => actualCentered_growth hx) hδ X
  convert h using 1
  ring

theorem actualCentered_correction_tendsto {δ : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hδcont : ∀ X : ℝ, ContinuousOn δ (Icc (1 : ℝ) X))
    (hδ : ∀ x : ℝ, 1 ≤ x → |δ x| ≤ C / x ^ 2) :
    Tendsto (signedCorrectionCutoff actualCentered δ) atTop
      (𝓝 (∫ x in Ioi (1 : ℝ), signedCorrectionDensity actualCentered δ x)) :=
  signedCorrectionCutoff_tendsto (actualCentered_correction_integrableOn hC hδcont hδ)

/-- Exact support replacement for the full actual lattice correction. -/

theorem actualLatticeCorrection_eq_fixed_cutoff {x X : ℝ}
    (hx : 1 ≤ x) (hX : x ≤ X) :
    actualLatticeCorrection x = annularLatticeFinite (indices X) x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  unfold actualLatticeCorrection annularLatticeFinite
  congr 1
  apply Finset.sum_subset (indices_mono hX)
  intro n hn hnnot
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnf : Nat.floor x < n := by
    by_contra h
    exact hnnot (Finset.mem_Icc.mpr ⟨hn1, le_of_not_gt h⟩)
  have hxn : x < (n : ℝ) := Nat.lt_of_floor_lt hnf
  have hr : 1 ≤ (n : ℝ) / x := (le_div_iff₀ hx0).mpr (by simpa using hxn.le)
  exact annularArithmeticWeight_eq_zero_of_one_le hr

theorem actualLatticeCorrection_continuousOn (X : ℝ) :
    ContinuousOn actualLatticeCorrection (Icc (1 : ℝ) X) := by
  have hc : ContinuousOn (annularLatticeFinite (indices X)) (Icc (1 : ℝ) X) := by
    unfold annularLatticeFinite
    apply ContinuousOn.sub
    · exact continuousOn_finsetSum (indices X) (fun n _ => continuousOn_annularScaled n X)
    · exact continuousOn_const.mul continuousOn_id
  apply hc.congr
  intro x hx
  exact actualLatticeCorrection_eq_fixed_cutoff hx.1 hx.2

theorem actualLatticeCorrection_abs_le {x : ℝ} (hx : 1 ≤ x) :
    |actualLatticeCorrection x| ≤ (10 / 27 : ℝ) / x ^ 2 := by
  change |annularLatticeFinite (Finset.Icc 1 (Nat.floor x)) x| ≤ (10 / 27 : ℝ) / x ^ 2
  rw [div_div]
  exact annularLatticeFinite_abs_le (zero_lt_one.trans_le hx)

/-- The previously open lattice provider is discharged unconditionally. -/

theorem actualLatticeDecay : ActualLatticeDecay :=
  ⟨10 / 27, fun _ hx => actualLatticeCorrection_abs_le hx⟩

theorem actual_signedCorrection_integrableOn :
    IntegrableOn (signedCorrectionDensity actualCentered actualLatticeCorrection)
      (Ioi (1 : ℝ)) :=
  actualCentered_correction_integrableOn (by norm_num)
    actualLatticeCorrection_continuousOn (fun _ hx => actualLatticeCorrection_abs_le hx)

theorem actualPrimeSignal_energy_eq_signedCorrection (X : ℝ) :
    criticalEnergy actualPrimeSignal X = actualIntegralEnergy X +
      signedCorrectionCutoff actualCentered actualLatticeCorrection X := by
  have he : actualPrimeSignal = fun x => actualCentered x + actualLatticeCorrection x :=
    funext actualPrimeSignal_eq_centered_add_lattice
  rw [he, criticalEnergy_add_eq_energy_add_signedCorrection X
    (actualCentered_continuousOn X) (actualLatticeCorrection_continuousOn X)]
  rfl

/-- Complete all-cutoff transfer: the signed cross term and lattice square
are contained in the exact correction, with an unconditional uniform bound. -/

theorem actualPrimeSignal_energy_difference_abs_le (X : ℝ) :
    |criticalEnergy actualPrimeSignal X - actualIntegralEnergy X| ≤ 1105 / 5832 := by
  rw [actualPrimeSignal_energy_eq_signedCorrection, add_sub_cancel_left]
  have h := actualCentered_correction_uniform_bound (by norm_num : (0 : ℝ) ≤ 10 / 27)
    actualLatticeCorrection_continuousOn (fun _ hx => actualLatticeCorrection_abs_le hx) X
  norm_num at h ⊢
  exact h

/-- The limiting offset is the actual absolutely convergent signed integral;
it is not asserted to vanish or to have a particular sign. -/

theorem actualPrimeSignal_energy_difference_tendsto :
    Tendsto (fun X : ℝ => criticalEnergy actualPrimeSignal X - actualIntegralEnergy X)
      atTop (𝓝 (∫ x in Ioi (1 : ℝ),
        signedCorrectionDensity actualCentered actualLatticeCorrection x)) := by
  have he : (fun X : ℝ => criticalEnergy actualPrimeSignal X - actualIntegralEnergy X) =
      signedCorrectionCutoff actualCentered actualLatticeCorrection := by
    funext X
    rw [actualPrimeSignal_energy_eq_signedCorrection, add_sub_cancel_left]
  rw [he]
  exact signedCorrectionCutoff_tendsto actual_signedCorrection_integrableOn

/-- The logarithmic critical-energy target for the actual prime-centered
signal A.  This is a proposition to estimate, not an assumed arithmetic
bound or a new RH criterion. -/

def ActualPrimeEnergyUpperBound : Prop :=
  ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X → criticalEnergy actualPrimeSignal X ≤ C * Real.log X

private theorem correctionConstant_le_logAllowance {X : ℝ} (hX : 2 ≤ X) :
    (1105 / 5832 : ℝ) ≤
      ((1105 / 5832 : ℝ) / Real.log 2) * Real.log X := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX
  have hallow : 0 ≤ (1105 / 5832 : ℝ) / Real.log 2 :=
    div_nonneg (by norm_num) hlog2.le
  have h := mul_le_mul_of_nonneg_left hlog hallow
  rw [div_mul_cancel₀ _ hlog2.ne'] at h
  exact h

/-- The exact all-cutoff bounded correction removes the lattice obstacle
from logarithmic critical-energy estimates, in both directions. -/

theorem actualPrimeEnergyUpperBound_iff_actualEnergyUpperBound :
    ActualPrimeEnergyUpperBound ↔ ActualEnergyUpperBound := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + (1105 / 5832 : ℝ) / Real.log 2, ?_⟩
    intro X hX
    have hd := actualPrimeSignal_energy_difference_abs_le X
    rw [actualIntegralEnergy_eq_quadratic] at hd
    have hleft := (abs_le.mp hd).1
    calc
      actualQuadraticEnergy X ≤ criticalEnergy actualPrimeSignal X + 1105 / 5832 :=
        by linarith
      _ ≤ C * Real.log X + ((1105 / 5832 : ℝ) / Real.log 2) * Real.log X :=
        add_le_add (hC X hX) (correctionConstant_le_logAllowance hX)
      _ = _ := by ring
  · rintro ⟨C, hC⟩
    refine ⟨C + (1105 / 5832 : ℝ) / Real.log 2, ?_⟩
    intro X hX
    have hd := actualPrimeSignal_energy_difference_abs_le X
    rw [actualIntegralEnergy_eq_quadratic] at hd
    have hright := (abs_le.mp hd).2
    calc
      criticalEnergy actualPrimeSignal X ≤ actualQuadraticEnergy X + 1105 / 5832 :=
        by linarith
      _ ≤ C * Real.log X + ((1105 / 5832 : ℝ) / Real.log 2) * Real.log X :=
        add_le_add (hC X hX) (correctionConstant_le_logAllowance hX)
      _ = _ := by ring

/-- The model estimate remains an explicit arithmetic premise. -/

theorem actualPrimeEnergyUpperBound_iff_signedResidualUpperBound
    (hmodel : ActualModelLogBound) :
    ActualPrimeEnergyUpperBound ↔ ActualSignedResidualUpperBound :=
  actualPrimeEnergyUpperBound_iff_actualEnergyUpperBound.trans
    (actualEnergyUpperBound_iff_signedResidualUpperBound hmodel)

/-- This transports the existing conditional analytic criterion.  The
criterion itself and the logarithmic arithmetic estimate remain open. -/

theorem riemannHypothesis_iff_actualPrimeEnergyUpperBound
    (hcriterion : ActualRHEnergyCriterion) :
    _root_.RiemannHypothesis ↔ ActualPrimeEnergyUpperBound :=
  hcriterion.trans actualPrimeEnergyUpperBound_iff_actualEnergyUpperBound.symm

end RiemannResearch.RH.AnnularCriticalEnergy
