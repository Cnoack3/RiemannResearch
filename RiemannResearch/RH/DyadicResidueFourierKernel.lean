import RiemannResearch.RH.DyadicTentFourierSamples
import RiemannResearch.RH.DyadicResidueStepApproximation
import RiemannResearch.RH.ParetoResidueMean
import RiemannResearch.RH.DyadicTentLogMajorant
import RiemannResearch.Analysis.ScalarFourierLimit
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Actual signed residue Fourier cutoff kernels

Source: independently developed from the actual residue jump expansion in
the user-provided FourierTentContinuationVerification20260910(1).md.
The finite Abel identity retains the conductor reset before any estimate.
No zeta identification or cutoff-independent majorant is asserted here.
-/

open scoped BigOperators

namespace RiemannResearch.Analysis
noncomputable section

/-- Finite complex Abel summation for the jumps of a real sequence. -/
theorem complex_weighted_jump_sum_abel
    (r : ℕ → ℝ) (w : ℕ → ℂ) (K : ℕ) :
    (∑ j ∈ Finset.range K, ((r (j+1) - r j : ℝ) : ℂ) * w (j+1)) =
      (r K : ℂ) * w (K+1) - (r 0 : ℂ) * w 1 +
        ∑ j ∈ Finset.range K, (r (j+1) : ℂ) * (w (j+1) - w (j+2)) := by
  induction K with
  | zero => simp
  | succ K ih =>
      simp only [Finset.sum_range_succ]
      rw [ih]
      push_cast
      have hidx : K + 1 + 1 = K + 2 := by omega
      rw [hidx]
      ring

end
end RiemannResearch.Analysis

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis
noncomputable section

/-- The actual positive integer logarithmic Fourier phase. -/
def dyadicIntegerFourierPhase (h : ℤ) (n : ℕ) : ℂ :=
  fourier h ((Real.log (n : ℝ) / Real.log 2 : ℝ) : UnitAddCircle)

/-- The harmonic Fourier weight occurring in a signed residue jump packet. -/
def dyadicHarmonicFourierWeight (h : ℤ) (n : ℕ) : ℂ :=
  dyadicIntegerFourierPhase h n / (n : ℂ)

/-- The actual signed reset kernel at a finite physical cutoff. -/
def dyadicResidueFourierKernel (a K : ℕ) (h : ℤ) : ℂ :=
  ∑ j ∈ Finset.range K,
    (((1 - if a ∣ j+1 then (a : ℝ) else 0) / (j+1 : ℝ) : ℝ) : ℂ) *
      dyadicIntegerFourierPhase h (j+1)

/-- The finite residue packet has the exact tent Fourier expansion. -/
theorem hilbertResidue_stepJumpPrefix_hasSum_fourier
    (a : ℕ) (ha : 0 < a) (K i : ℕ) :
    HasSum (fun h : ℤ => dyadicTentMellinCoefficient i h *
        dyadicResidueFourierKernel a K h)
      (dyadicBoundaryCoordinate
        (hilbertStepJumpPrefix (hilbertResidue a ha) K) i : ℂ) := by
  have hs := dyadicBoundaryCoordinate_finite_signed_packet_hasSum_fourier
    i (Finset.range K)
    (fun j => (1 - if a ∣ j+1 then (a : ℝ) else 0) / (j+1 : ℝ))
  rw [hilbertResidue_stepJumpPrefix_signed_boundary a ha K i]
  simpa only [dyadicResidueFourierKernel, dyadicIntegerFourierPhase,
    Complex.ofReal_sum, Complex.ofReal_mul] using hs

/-- The genuine signed reset is the jump of the bounded modular prefix. -/
theorem dyadicResidueFourierKernel_eq_modular_jumps
    (a : ℕ) (ha : 0 < a) (K : ℕ) (h : ℤ) :
    dyadicResidueFourierKernel a K h =
      ∑ j ∈ Finset.range K,
        (((((j+1) % a : ℕ) : ℝ) - ((j % a : ℕ) : ℝ) : ℝ) : ℂ) *
          dyadicHarmonicFourierWeight h (j+1) := by
  unfold dyadicResidueFourierKernel
  apply Finset.sum_congr rfl
  intro j hj
  rw [natResidue_cast_jump a j ha]
  unfold dyadicHarmonicFourierWeight
  push_cast
  ring

/-- Exact signed Abel identity for the actual Fourier kernel. The bounded
modular prefix and the full terminal weight remain explicit. -/
theorem dyadicResidueFourierKernel_eq_modular_abel
    (a : ℕ) (ha : 0 < a) (K : ℕ) (h : ℤ) :
    dyadicResidueFourierKernel a K h =
      ((K % a : ℕ) : ℂ) * dyadicHarmonicFourierWeight h (K+1) +
        ∑ j ∈ Finset.range K, (((j+1) % a : ℕ) : ℂ) *
          (dyadicHarmonicFourierWeight h (j+1) -
            dyadicHarmonicFourierWeight h (j+2)) := by
  rw [dyadicResidueFourierKernel_eq_modular_jumps a ha K h]
  simpa only [Nat.zero_mod, Nat.cast_zero, Complex.ofReal_zero, Complex.ofReal_natCast,
    zero_mul, sub_zero] using
      complex_weighted_jump_sum_abel
        (fun n => ((n % a : ℕ) : ℝ)) (dyadicHarmonicFourierWeight h) K

/-- The exact zero-frequency kernel includes the vanishing finite endpoint. -/
theorem dyadicResidueFourierKernel_zero_eq_pareto
    (a : ℕ) (ha : 0 < a) (K : ℕ) :
    dyadicResidueFourierKernel a K 0 =
      ((∑ k ∈ Finset.range (K+1), positiveWeight k * residue a k) +
        residue a K / (K+1 : ℝ) : ℝ) := by
  rw [dyadicResidueFourierKernel_eq_modular_abel a ha K 0]
  have hw (n : ℕ) : dyadicHarmonicFourierWeight 0 n = 1 / (n : ℂ) := by
    simp [dyadicHarmonicFourierWeight, dyadicIntegerFourierPhase]
  simp only [hw]
  have hp : (∑ k ∈ Finset.range (K+1), positiveWeight k * residue a k) =
      ∑ j ∈ Finset.range K, positiveWeight (j+1) * residue a (j+1) := by
    rw [Finset.sum_range_succ']
    simp only [residue, Nat.zero_mod, Nat.cast_zero, mul_zero, add_zero]
  rw [hp]
  push_cast
  have he : (∑ j ∈ Finset.range K, (((j+1) % a : ℕ) : ℂ) *
      (1 / ((j+1 : ℕ) : ℂ) - 1 / ((j+2 : ℕ) : ℂ))) =
      ∑ j ∈ Finset.range K, (positiveWeight (j+1) : ℂ) * (residue a (j+1) : ℂ) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [positiveWeight, residue]
    push_cast
    have h1 : (j : ℂ) + 1 ≠ 0 := by exact_mod_cast (show (j : ℝ)+1 ≠ 0 by positivity)
    have h2 : (j : ℂ) + 1 + 1 ≠ 0 := by exact_mod_cast (show (j : ℝ)+1+1 ≠ 0 by positivity)
    have h3 : (j : ℂ) + 2 ≠ 0 := by exact_mod_cast (show (j : ℝ)+2 ≠ 0 by positivity)
    field_simp [h1, h2, h3]
    ring
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at he
  rw [he]
  simp only [residue]
  push_cast
  ring

/-- The actual endpoint vanishes at every conductor, with its dependence
on that conductor explicit. -/
theorem residue_harmonic_endpoint_tendsto_zero (a : ℕ) (ha : 0 < a) :
    Filter.Tendsto (fun K : ℕ => residue a K / (K+1 : ℝ))
      Filter.atTop (nhds 0) := by
  have hupper : Filter.Tendsto (fun K : ℕ => (a : ℝ) / (K+1 : ℝ))
      Filter.atTop (nhds 0) := by
    simpa only [mul_one_div, mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (a : ℝ)
  apply squeeze_zero (fun K => div_nonneg (by unfold residue; positivity)
      (by positivity)) (fun K => ?_) hupper
  apply div_le_div_of_nonneg_right _ (by positivity)
  unfold residue
  exact_mod_cast (Nat.mod_lt K ha).le

/-- The zero mode of the actual signed residue kernel converges to log a.
This is a proved endpoint, not a summability hypothesis or default tsum. -/
theorem dyadicResidueFourierKernel_zero_tendsto (a : ℕ) (ha : 0 < a) :
    Filter.Tendsto (fun K : ℕ => dyadicResidueFourierKernel a K 0)
      Filter.atTop (nhds (Real.log a : ℂ)) := by
  have hb : ∀ k, |residue a k| ≤ (a : ℝ) := by
    intro k
    unfold residue
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast (Nat.mod_lt k ha).le
  have hs := (weighted_summable_of_bounded hb).hasSum.tendsto_sum_nat
  have hnext : Filter.Tendsto (fun K : ℕ => K+1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun K => Nat.le_succ K) Filter.tendsto_id
  have hpart := hs.comp hnext
  have hsum := hpart.add (residue_harmonic_endpoint_tendsto_zero a ha)
  change Filter.Tendsto (fun K : ℕ =>
      (∑ k ∈ Finset.range (K+1), positiveWeight k * residue a k) +
        residue a K / (K+1 : ℝ)) Filter.atTop (nhds (paretoMean (residue a) + 0)) at hsum
  rw [paretoMean_residue a ha, add_zero] at hsum
  simpa only [dyadicResidueFourierKernel_zero_eq_pareto a ha, Function.comp_def] using
    Complex.continuous_ofReal.continuousAt.tendsto.comp hsum

/-- The physical side of the residue cutoff converges independently of any
Fourier-kernel estimate. -/
theorem hilbertResidue_stepJumpPrefix_boundaryCoordinate_tendsto
    (a : ℕ) (ha : 0 < a) (i : ℕ) :
    Filter.Tendsto (fun K : ℕ =>
      (dyadicBoundaryCoordinate (hilbertStepJumpPrefix (hilbertResidue a ha) K) i : ℂ))
      Filter.atTop (nhds (dyadicBoundaryCoordinate (hilbertResidue a ha) i : ℂ)) := by
  have ht := (innerSL ℝ (dyadicBoundaryVector i)).continuous.continuousAt.tendsto.comp
    (hilbertResidue_stepJumpPrefix_tendsto a ha)
  have ht' := ht.const_mul 4
  exact Complex.continuous_ofReal.continuousAt.tendsto.comp ht'

/-- The signed residue symbol, with its finite zero-frequency value kept
separate from the nonzero zeta expression. Identifying nonzero cutoff limits
with this symbol remains an explicit analytic hypothesis below. -/
def dyadicResidueFourierSymbol (a : ℕ) (h : ℤ) : ℂ :=
  if h = 0 then (Real.log a : ℂ) else
    (1 - dyadicIntegerFourierPhase h a) *
      riemannZeta (1 - Complex.I * (dyadicLogFrequency h : ℂ))

/-- Conditional research reduction for the actual fixed-conductor residue
Fourier bridge. Only the logarithmic cutoff bound and the nonzero-frequency
zeta limit are assumptions. The finite signed identity, physical convergence,
zero-frequency limit and summable Fourier majorant have proved providers. -/
theorem dyadicBoundaryCoordinate_residue_hasSum_fourier_of_logarithmic_kernel
    (a : ℕ) (ha : 0 < a) (i : ℕ) (C : ℝ)
    (hD : ∀ K h, ‖dyadicResidueFourierKernel a K h‖ ≤
      C * (1 + Real.log (2 + |(h : ℝ)|)))
    (hd : ∀ h : ℤ, h ≠ 0 →
      Filter.Tendsto (fun K => dyadicResidueFourierKernel a K h)
        Filter.atTop (nhds ((1 - dyadicIntegerFourierPhase h a) *
          riemannZeta (1 - Complex.I * (dyadicLogFrequency h : ℂ))))) :
    HasSum (fun h => dyadicTentMellinCoefficient i h * dyadicResidueFourierSymbol a h)
      (dyadicBoundaryCoordinate (hilbertResidue a ha) i : ℂ) := by
  have hB : Summable (fun h : ℤ => ‖dyadicTentMellinCoefficient i h‖ *
      (C * (1 + Real.log (2 + |(h : ℝ)|)))) := by
    apply ((summable_norm_dyadicTentMellinCoefficient_mul_one_add_log i).mul_left C).congr
    intro h
    ring
  have hlimit : ∀ h, Filter.Tendsto (fun K => dyadicResidueFourierKernel a K h)
      Filter.atTop (nhds (dyadicResidueFourierSymbol a h)) := by
    intro h
    by_cases hh : h = 0
    · subst h
      simpa [dyadicResidueFourierSymbol] using
        dyadicResidueFourierKernel_zero_tendsto a ha
    · simpa only [dyadicResidueFourierSymbol, if_neg hh] using hd h hh
  exact hasSum_fourier_kernel_limit_of_actual_approximation
    (dyadicTentMellinCoefficient i) (dyadicResidueFourierKernel a)
    (dyadicResidueFourierSymbol a)
    (fun h => C * (1 + Real.log (2 + |(h : ℝ)|))) hB hD hlimit
    (fun K => (dyadicBoundaryCoordinate (hilbertStepJumpPrefix (hilbertResidue a ha) K) i : ℂ))
    (dyadicBoundaryCoordinate (hilbertResidue a ha) i : ℂ)
    (fun K => (hilbertResidue_stepJumpPrefix_hasSum_fourier a ha K i).tsum_eq.symm)
    (hilbertResidue_stepJumpPrefix_boundaryCoordinate_tendsto a ha i)


end
end RiemannResearch.RH.Pareto
