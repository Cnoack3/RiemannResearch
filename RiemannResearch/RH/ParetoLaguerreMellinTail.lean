import RiemannResearch.Analysis.LaguerreKernelTail
import RiemannResearch.Analysis.LaguerreComplexLaplace
import RiemannResearch.RH.ParetoLaguerreCoordinates
import RiemannResearch.RH.ParetoMellinFunctional
import RiemannResearch.RH.ParetoExponentialRealization
import RiemannResearch.Analysis.LaguerreMeasure
import Mathlib.Tactic.LinearCombination

/-!
# Mellin evaluation after matching Laguerre coordinates

Subtracting the matched Laguerre modes from the real and imaginary parts of the
Mellin kernel yields an exact geometric residual energy. The resulting bound
uses the complete Pareto norm.
-/

noncomputable section
open Filter MeasureTheory Set
namespace RiemannResearch.RH.Pareto.RamanujanLaguerre
open RiemannResearch.Analysis

private theorem laguerreMeasure_complex_integral (g : ℝ → ℂ) :
    (∫ t, g t ∂laguerreMeasure) =
      ∫ t in Ici (0 : ℝ), (Real.exp (-t) : ℂ) * g t := by
  rw [laguerreMeasure, integral_withDensity_eq_integral_toReal_smul
    laguerreDensity_measurable (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _), Complex.real_smul]

private theorem mellin_pareto_exp_factor (s : ℂ) (t : ℝ) :
    (Real.exp t : ℂ) * (Real.exp t : ℂ) ^ (-s - 1) =
      (Real.exp (-t) : ℂ) * Complex.exp ((1 - s) * (t : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t)),
    ← Complex.ofReal_log (Real.exp_nonneg t), Real.log_exp,
    Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Under the change of variables `x = exp t`, the complete Pareto Mellin
transform is the pairing of the exponential step profile with the scalar
kernel `exp ((1-s)t)` for the Laguerre probability measure. -/
theorem paretoMellin_eq_laguerre_pairing (f : ThresholdHilbert) (s : ℂ) :
    paretoMellin f s = ∫ t : ℝ,
      (exponentialLift (hilbertSequence f) t : ℂ) * Complex.exp ((1 - s) * (t : ℂ))
        ∂laguerreMeasure := by
  rw [paretoMellin_eq_step_integral, laguerreMeasure_complex_integral, integral_Ici_eq_integral_Ioi]
  calc
    _ = ∫ t in Ioi (0 : ℝ), Real.exp t •
        ((hilbertSequence f ⌊Real.exp t⌋₊ : ℂ) * (Real.exp t : ℂ) ^ (-s - 1)) := by
          simpa only [Real.exp_zero] using (integral_comp_exp_Ioi
            (fun x : ℝ => (hilbertSequence f ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1)) 0).symm
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      simp only [Complex.real_smul, exponentialLift]
      linear_combination (hilbertSequence f ⌊Real.exp t⌋₊ : ℂ) * mellin_pareto_exp_factor s t

end RiemannResearch.RH.Pareto.RamanujanLaguerre

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.RamanujanLaguerre
open RiemannResearch.Analysis RiemannResearch.Analysis.LaguerreKernelTail

private def geometricProbe (s : ℂ) (t : ℝ) : ℂ := Complex.exp ((1-s)*(t:ℂ))

private theorem geometricProbe_memLp (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    MemLp (geometricProbe s) 2 laguerreMeasure := by
  apply (memLp_exp_mul_laguerreMeasure (s := 1-s.re) (by linarith)).mono' (by unfold geometricProbe; fun_prop)
  exact Filter.Eventually.of_forall (fun t => by
    simp [geometricProbe, Complex.norm_exp, Complex.mul_re])

private def realProbe (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) : LaguerreL2 :=
  ((geometricProbe_memLp s hs).continuousLinearMap_comp Complex.reCLM).toLp _
private def imaginaryProbe (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) : LaguerreL2 :=
  ((geometricProbe_memLp s hs).continuousLinearMap_comp Complex.imCLM).toLp _
private def geometricPairing (s : ℂ) (f : LaguerreL2) : ℂ :=
  ∫ t : ℝ, (f t : ℂ) * geometricProbe s t ∂laguerreMeasure

private theorem geometricPairing_parts (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (f : LaguerreL2) :
    (geometricPairing s f).re = inner ℝ f (realProbe s hs) ∧
    (geometricPairing s f).im = inner ℝ f (imaginaryProbe s hs) := by
  have hi : Integrable (fun t => (f t : ℂ) * geometricProbe s t) laguerreMeasure :=
    (Lp.memLp f).ofReal.integrable_mul (geometricProbe_memLp s hs)
  constructor
  · have h := integral_re hi
    change (∫ t : ℝ, ((f t : ℂ) * geometricProbe s t).re ∂laguerreMeasure) = (geometricPairing s f).re at h
    rw [← h, L2.inner_def]
    apply integral_congr_ae
    have hcoe : (realProbe s hs : ℝ → ℝ) =ᵐ[laguerreMeasure] fun t => (geometricProbe s t).re :=
      ((geometricProbe_memLp s hs).continuousLinearMap_comp Complex.reCLM).coeFn_toLp
    filter_upwards [hcoe] with t ht
    simp [ht, Complex.mul_re, mul_comm]
  · have h := integral_im hi
    change (∫ t : ℝ, ((f t : ℂ) * geometricProbe s t).im ∂laguerreMeasure) = (geometricPairing s f).im at h
    rw [← h, L2.inner_def]
    apply integral_congr_ae
    have hcoe : (imaginaryProbe s hs : ℝ → ℝ) =ᵐ[laguerreMeasure] fun t => (geometricProbe s t).im :=
      ((geometricProbe_memLp s hs).continuousLinearMap_comp Complex.imCLM).coeFn_toLp
    filter_upwards [hcoe] with t ht
    simp [ht, Complex.mul_im, mul_comm]

private theorem squared_pairing (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (f : LaguerreL2) :
    (inner ℝ f (realProbe s hs)) ^ 2 + (inner ℝ f (imaginaryProbe s hs)) ^ 2 =
      ‖geometricPairing s f‖ ^ 2 := by
  rw [← (geometricPairing_parts s hs f).1, ← (geometricPairing_parts s hs f).2,
    Complex.sq_norm, Complex.normSq_apply]
  ring

private theorem geometricPairing_realization (s : ℂ) (f : ThresholdHilbert) :
    geometricPairing s (laguerreRealization f) = paretoMellin f s := by
  rw [paretoMellin_eq_laguerre_pairing]
  apply integral_congr_ae
  filter_upwards [laguerreRealization_ae f] with t ht
  simp only [ht, geometricProbe]

private theorem geometricPairing_laguerre (s : ℂ) (hs : 0 < s.re) (j : ℕ) :
    geometricPairing s (laguerreVector j) = (s-1)^j / s^(j+1) := by
  calc
    _ = ∫ t : ℝ, (laguerreValue j t : ℂ) * geometricProbe s t ∂laguerreMeasure := by
      apply integral_congr_ae
      filter_upwards [laguerreVector_coe j] with t ht
      rw [ht]
    _ = _ := by
      rw [laguerreMeasure_complex_integral, ← laguerreValue_complex_laplace j hs]
      apply setIntegral_congr_fun measurableSet_Ici
      intro t _
      dsimp only [geometricProbe]
      rw [Complex.ofReal_exp, Complex.ofReal_neg]
      have h : Complex.exp (-(t:ℂ)) * Complex.exp ((1-s)*(t:ℂ)) = Complex.exp (-s*(t:ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        ring
      linear_combination (laguerreValue j t : ℂ) * h

/-- Matching the first `K` real Laguerre modes removes the corresponding
geometric coefficients of every continuous Mellin evaluation. -/
theorem paretoMellin_norm_sq_le_of_laguerre_matching (f : ThresholdHilbert) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (K : ℕ) (hf : ∀ j < K, laguerreReadout j f = 0) :
    ‖paretoMellin f s‖ ^ 2 ≤ ‖f‖ ^ 2 / (2*s.re-1) * (‖s-1‖/‖s‖)^(2*K) := by
  let x := realProbe s hs
  let y := imaginaryProbe s hs
  let r := (‖s-1‖/‖s‖)^2
  let c := (‖s‖^2)⁻¹
  have hspos : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := fun h => by simpa [h] using hspos
  have hn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hA : 0 < 2*s.re-1 := by linarith
  have hsq : ‖s‖^2 - ‖s-1‖^2 = 2*s.re-1 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im, sub_zero]
    ring
  have hratio : 1-r = (2*s.re-1)/‖s‖^2 := by
    dsimp only [r]
    calc
      1 - (‖s-1‖/‖s‖)^2 = (‖s‖^2-‖s-1‖^2)/‖s‖^2 := by
        rw [div_pow, sub_div, div_self (pow_ne_zero _ hn.ne')]
      _ = _ := congrArg (fun t : ℝ => t / ‖s‖^2) hsq
  have hrpos : 0 ≤ r := sq_nonneg _
  have hr : r < 1 := by
    have hh : 0 < 1-r := by rw [hratio]; exact div_pos hA (sq_pos_of_pos hn)
    linarith
  have hcoeff (j : ℕ) : (inner ℝ (laguerreVector j) x)^2 + (inner ℝ (laguerreVector j) y)^2 = c*r^j := by
    rw [squared_pairing s hs, geometricPairing_laguerre s hspos]
    have he : (s-1)^j / s^(j+1) = ((s-1)/s)^j / s := by
      rw [div_pow, div_div, pow_succ]
    have hp : ((‖s-1‖/‖s‖)^j)^2 = r^j := by
      dsimp only [r]
      rw [← pow_mul (‖s-1‖/‖s‖) j 2, ← pow_mul (‖s-1‖/‖s‖) 2 j, Nat.mul_comm j 2]
    rw [he, norm_div, norm_pow, norm_div, div_pow, hp]
    simp only [c, div_eq_mul_inv, mul_comm]
  have hcoeff' (j : ℕ) : (inner ℝ x (laguerreVector j))^2 + (inner ℝ y (laguerreVector j))^2 = c*r^j := by
    simpa only [real_inner_comm x (laguerreVector j), real_inner_comm y (laguerreVector j)]
      using hcoeff j
  have hsum : HasSum (fun j : ℕ => c*r^j) (‖x‖^2+‖y‖^2) := by
    simpa only [Pi.add_apply, hcoeff'] using (hasSum_laguerre_inner_sq x).add (hasSum_laguerre_inner_sq y)
  have hB : ‖x‖^2 + ‖y‖^2 = c*(1-r)⁻¹ := by
    apply hsum.unique
    simpa only [one_div] using (hasSum_geometric_of_lt_one hrpos hr).mul_left c
  have hfinite (n : ℕ) : c*(1-r)⁻¹ - (∑ i ∈ Finset.range n, c*r^i) = c*(1-r)⁻¹*r^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have ht : (1-r)⁻¹ * (1-r) = 1 := inv_mul_cancel₀ (sub_pos.mpr hr).ne'
      linear_combination ih + c * r^n * ht
  have hpre (j : ℕ) (hj : j ∈ Finset.range K) : inner ℝ (laguerreRealization f) (laguerreVector j) = 0 :=
    (real_inner_comm (laguerreVector j) (laguerreRealization f)).trans (hf j (Finset.mem_range.mp hj))
  have h := matched_complex_kernel_sq_le laguerreVector laguerreVector_orthonormal K (laguerreRealization f) x y hpre
  rw [squared_pairing s hs, geometricPairing_realization, laguerreRealization.norm_map, hB] at h
  simp_rw [hcoeff] at h
  rw [hfinite, hratio] at h
  have hconst : c * (((2*s.re-1)/‖s‖^2)⁻¹) = (2*s.re-1)⁻¹ := by
    dsimp only [c]
    field_simp [hn.ne', hA.ne']
  rw [hconst] at h
  simpa only [r, pow_mul, div_eq_mul_inv, mul_assoc] using h

/--
info: 'RiemannResearch.RH.Pareto.RamanujanLaguerre.paretoMellin_norm_sq_le_of_laguerre_matching' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms paretoMellin_norm_sq_le_of_laguerre_matching

end RiemannResearch.RH.Pareto.RamanujanLaguerre
