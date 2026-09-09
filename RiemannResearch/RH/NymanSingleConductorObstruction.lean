import RiemannResearch.RH.NymanActualTailEnergy
import RiemannResearch.Analysis.CompactLaplaceInterpolation
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The actual single-conductor tail obstruction

Source: user-provided argument, Section 10.4, equation (10.5), of
`RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md`.
The note supplies the artificial-zero obstruction. This module derives the
signature and the linear-in-M energy floor for the actual arithmetic tails.
No Riemann hypothesis or assertion about the zeros of zeta is assumed.
-/

open MeasureTheory MeasureTheory.BilateralLaplace
open RiemannResearch.Analysis
open Filter
open scoped Topology

namespace RiemannResearch.RH

open ArithmeticConductorCommonZeros ZetaConductorRegularization

/-- The obstruction applies to every compact smooth potential for this conductor,
not only to the particular truncated inverse used to construct a feasible tail. -/
theorem singleConductorCompletion_energy_lower_bound
    (n : ℕ) (hn : 2 ≤ n) {u f : ℝ → ℂ} {a b : ℝ}
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (ha : ∀ x < a, u x = 0) (hb : ∀ x > b, u x = 0)
    (hf : SmoothSuperexponentialDecay f) (Y : ℝ)
    (hhead : ∀ x < Y, poleCancellationOperator (nymanFullReturn n u) x = f x)
    {s : ℂ} (hs : s ≠ 1) (hP : conductorSymbol n s = 0) :
    Real.exp Y * ‖centeredTransform f s‖ ^ 2 ≤
      RemoteLaplaceTail.energy (poleCancellationOperator (nymanFullReturn n u) - f) := by
  letI : NeZero n := ⟨by omega⟩
  have hG := (smoothSuperexponentialDecay_nymanFullReturn hu ha hb n).poleCancellationOperator
  have hτ := hG.sub hf
  have hLp : MemLp (poleCancellationOperator (nymanFullReturn n u) - f) 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm hτ.1.continuous.aestronglyMeasurable).2
    have hi := (hτ.decay.integrable_crossCorrelation hτ.decay
      hτ.1.continuous hτ.1.continuous 0).norm
    simpa only [add_zero, norm_mul, norm_star, pow_two] using hi
  have hsig : centeredTransform (poleCancellationOperator (nymanFullReturn n u) - f) s =
      -centeredTransform f s := by
    rw [centeredTransform_sub (hG.decay.hasExponentialMoments hG.1.continuous)
      (hf.decay.hasExponentialMoments hf.1.continuous),
      centeredTransform_poleCancellation_nymanFullReturn n hu ha hb s,
      conductorZeta_of_ne_one n hs, hP, mul_zero, mul_zero, zero_mul, zero_sub]
  have hre := conductorSymbol_zero_re n (by omega) s hP
  have h := RemoteLaplaceTail.supported_signature_energy_lower_bound
    (poleCancellationOperator (nymanFullReturn n u) - f) s
    (by rw [hre]; norm_num) Y hLp
    (fun x hx => sub_eq_zero.mpr (hhead x hx)) (centeredTransform f s) hsig
  simpa only [hre, mul_one, show (2 : ℝ) - 1 = 1 by norm_num, one_mul] using h

/-- The compact interpolation seed supplies the precise pole-cancelled signature. -/
theorem centeredTransform_poleCancellation_compactLaplaceSeed (s : ℂ) :
    centeredTransform (poleCancellationOperator (compactLaplaceSeed s)) s = s * (s - 1) := by
  rw [centeredTransform_poleCancellation_of_smoothSuperexponential
    (smoothSuperexponentialDecay_of_compact_interval (compactLaplaceSeed_contDiff s)
      (compactLaplaceSeed_zero_below s) (compactLaplaceSeed_zero_above s)) s,
    centeredTransform_compactLaplaceSeed, mul_one]

/-- Every nonremovable conductor zero annihilates the actual completed test. -/
theorem centeredTransform_nymanCompletedTest_of_symbol_zero
    (n M : ℕ) (hn : 2 ≤ n) {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0)
    {s : ℂ} (hs : s ≠ 1) (hP : conductorSymbol n s = 0) :
    centeredTransform (nymanCompletedTest n M hn v) s = 0 := by
  rw [centeredTransform_nymanCompletedTest n M hn hv ha hb s,
    conductorZeta_of_ne_one n hs, hP, mul_zero, mul_zero, zero_mul]

/-- The artificial-zero signature follows from the concrete arithmetic construction. -/
theorem centeredTransform_nymanCompletionTail_of_symbol_zero
    (n M : ℕ) (hn : 2 ≤ n) {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0)
    {s : ℂ} (hs : s ≠ 1) (hP : conductorSymbol n s = 0) :
    centeredTransform (nymanCompletionTail n M hn v) s =
      -centeredTransform (poleCancellationOperator v) s := by
  rw [centeredTransform_nymanCompletionTail_sub n M hn hv ha hb s,
    centeredTransform_nymanCompletedTest_of_symbol_zero n M hn hv ha hb hs hP,
    zero_sub]

/-- Equation (10.5), with support and L2 hypotheses discharged by the actual tail. -/
theorem nymanCompletionTail_artificial_zero_energy_lower_bound
    (n M : ℕ) (hn : 2 ≤ n) {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0)
    {s : ℂ} (hs : s ≠ 1) (hP : conductorSymbol n s = 0) :
    Real.exp (a + Real.log (M + 1 : ℕ)) *
        ‖centeredTransform (poleCancellationOperator v) s‖ ^ 2 ≤
      RemoteLaplaceTail.energy (nymanCompletionTail n M hn v) := by
  have hre := conductorSymbol_zero_re n (by omega) s hP
  have h := RemoteLaplaceTail.supported_signature_energy_lower_bound
    (nymanCompletionTail n M hn v) s (by rw [hre]; norm_num)
    (a + Real.log (M + 1 : ℕ))
    (memLp_two_nymanCompletionTail n M hn hv ha hb)
    (fun y hy => nymanCompletionTail_zero_below n M hn ha hy)
    (centeredTransform (poleCancellationOperator v) s)
    (centeredTransform_nymanCompletionTail_of_symbol_zero n M hn hv ha hb hs hP)
  simpa only [hre, mul_one, show (2 : ℝ) - 1 = 1 by norm_num, one_mul] using h

/-- The exact exponential support factor is linear in the truncation parameter. -/
theorem nymanCompletionTail_artificial_zero_linear_lower_bound
    (n M : ℕ) (hn : 2 ≤ n) {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0)
    {s : ℂ} (hs : s ≠ 1) (hP : conductorSymbol n s = 0) :
    (Real.exp a * ‖centeredTransform (poleCancellationOperator v) s‖ ^ 2) *
        ((M : ℝ) + 1) ≤
      RemoteLaplaceTail.energy (nymanCompletionTail n M hn v) := by
  have h := nymanCompletionTail_artificial_zero_energy_lower_bound n M hn hv ha hb hs hP
  rw [Real.exp_add, Real.exp_log (by positivity : (0 : ℝ) < (M + 1 : ℕ))] at h
  convert h using 1 <;> push_cast <;> ring

/-- A literal artificial zero, with the removable point excluded by k != 0. -/
theorem nymanCompletionTail_explicit_artificial_zero_lower_bound
    (n M : ℕ) (hn : 2 ≤ n) {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0)
    (k : ℤ) (hk : k ≠ 0) :
    (Real.exp a * ‖centeredTransform (poleCancellationOperator v)
      (1 + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) / (Real.log n : ℂ))‖ ^ 2) *
        ((M : ℝ) + 1) ≤
      RemoteLaplaceTail.energy (nymanCompletionTail n M hn v) :=
  nymanCompletionTail_artificial_zero_linear_lower_bound n M hn hv ha hb
    (conductorSymbol_extra_zero_ne_one n (by omega) k hk)
    (conductorSymbol_explicit_zero n (by omega) k)

/-- A nonzero artificial signature forces energy beyond every fixed bound. -/
theorem nymanCompletionTail_energy_unbounded_of_artificial_signature
    (n : ℕ) (hn : 2 ≤ n) {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0)
    {s : ℂ} (hs : s ≠ 1) (hP : conductorSymbol n s = 0)
    (hsig : centeredTransform (poleCancellationOperator v) s ≠ 0) :
    ∀ B : ℝ, ∃ M : ℕ, B < RemoteLaplaceTail.energy (nymanCompletionTail n M hn v) := by
  intro B
  let c := Real.exp a * ‖centeredTransform (poleCancellationOperator v) s‖ ^ 2
  have hc : 0 < c := mul_pos (Real.exp_pos _) (pow_pos (norm_pos_iff.mpr hsig) 2)
  obtain ⟨M, hM⟩ := exists_nat_gt (B / c)
  refine ⟨M, lt_of_lt_of_le ?_
    (nymanCompletionTail_artificial_zero_linear_lower_bound n M hn hv ha hb hs hP)⟩
  change B < c * ((M : ℝ) + 1)
  have hBM : B < (M : ℝ) * c := (div_lt_iff₀ hc).mp hM
  nlinarith

/-- In particular, the actual energies cannot be o(M+1) for such a seed. -/
theorem nymanCompletionTail_normalized_energy_not_tendsto_zero
    (n : ℕ) (hn : 2 ≤ n) {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0)
    {s : ℂ} (hs : s ≠ 1) (hP : conductorSymbol n s = 0)
    (hsig : centeredTransform (poleCancellationOperator v) s ≠ 0) :
    ¬ Tendsto (fun M : ℕ => RemoteLaplaceTail.energy (nymanCompletionTail n M hn v) /
      ((M : ℝ) + 1)) atTop (𝓝 0) := by
  intro hlim
  have hc : 0 < Real.exp a * ‖centeredTransform (poleCancellationOperator v) s‖ ^ 2 :=
    mul_pos (Real.exp_pos _) (pow_pos (norm_pos_iff.mpr hsig) 2)
  have hle : Real.exp a * ‖centeredTransform (poleCancellationOperator v) s‖ ^ 2 ≤ 0 := by
    apply ge_of_tendsto hlim
    exact Filter.Eventually.of_forall fun M =>
      (le_div_iff₀ (by positivity : (0 : ℝ) < (M : ℝ) + 1)).mpr
        (nymanCompletionTail_artificial_zero_linear_lower_bound n M hn hv ha hb hs hP)
  exact (not_le_of_gt hc) hle

/-- For every artificial zero there is a concrete compact seed with a strictly
positive, explicit energy slope, valid for every truncation parameter. -/
theorem nymanCompletionTail_compactLaplaceSeed_linear_lower_bound
    (n M : ℕ) (hn : 2 ≤ n) {s : ℂ}
    (hs : s ≠ 1) (hP : conductorSymbol n s = 0) :
    (Real.exp (-2) * ‖s * (s - 1)‖ ^ 2) * ((M : ℝ) + 1) ≤
      RemoteLaplaceTail.energy (nymanCompletionTail n M hn (compactLaplaceSeed s)) := by
  simpa only [centeredTransform_poleCancellation_compactLaplaceSeed] using
    nymanCompletionTail_artificial_zero_linear_lower_bound n M hn
      (compactLaplaceSeed_contDiff s) (compactLaplaceSeed_zero_below s)
      (compactLaplaceSeed_zero_above s) hs hP

/-- Every conductor n>=2 has an actual compact smooth seed whose tail energy
fails to be sublinear. The nonzero-signature condition is constructed here. -/
theorem exists_nymanCompletionTail_normalized_energy_not_tendsto_zero
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ v : ℝ → ℂ,
      ContDiff ℝ (↑(⊤ : ℕ∞)) v ∧
      (∀ x < (-2 : ℝ), v x = 0) ∧ (∀ x > (2 : ℝ), v x = 0) ∧
      ¬ Tendsto (fun M : ℕ => RemoteLaplaceTail.energy (nymanCompletionTail n M hn v) /
        ((M : ℝ) + 1)) atTop (𝓝 0) := by
  let s : ℂ := 1 + (1 : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) / (Real.log n : ℂ)
  have hs : s ≠ 1 := by
    simpa [s] using conductorSymbol_extra_zero_ne_one n (by omega) 1 (by norm_num)
  have hP : conductorSymbol n s = 0 := by
    simpa [s] using conductorSymbol_explicit_zero n (by omega) 1
  have hs0 : s ≠ 0 := by
    intro heq
    have hre := conductorSymbol_zero_re n (by omega) s hP
    simp [heq] at hre
  refine ⟨compactLaplaceSeed s, compactLaplaceSeed_contDiff s,
    compactLaplaceSeed_zero_below s, compactLaplaceSeed_zero_above s, ?_⟩
  apply nymanCompletionTail_normalized_energy_not_tendsto_zero n hn
    (compactLaplaceSeed_contDiff s) (compactLaplaceSeed_zero_below s)
    (compactLaplaceSeed_zero_above s) hs hP
  rw [centeredTransform_poleCancellation_compactLaplaceSeed]
  exact mul_ne_zero hs0 (sub_ne_zero.mpr hs)

end RiemannResearch.RH
