import RiemannResearch.Analysis.MontgomeryPrimeProbeEnergy
import RiemannResearch.Analysis.MontgomeryPrimeProbe
import RiemannResearch.Analysis.MontgomeryIntervalIdentity

/-! # Finite rational logarithmic frequencies of the signed comparison

Expanding the squared prime probe retains all prime-power pairs and the
continuous sinc value on the diagonal.
-/

noncomputable section
namespace RiemannResearch.Analysis.MontgomeryPrimeTrace
open Filter MeasureTheory Set
open scoped Topology BigOperators
open MontgomeryFormFactor ZeroOrdinate

private theorem cosineWindow_zero_sinc (q f : ℝ) :
    cosineWindow 0 q f = q * Real.sinc (q*f) := by
  by_cases hf : f = 0
  · simp [hf, cosineWindow]
  by_cases hq : q = 0
  · simp [hq, cosineWindow, hf]
  rw [cosineWindow, if_neg hf, Real.sinc_of_ne_zero (mul_ne_zero hq hf)]
  simp only [zero_mul, Real.sin_zero, sub_zero]
  field_simp [hq, hf]

private theorem probeKernel_energy_sinc {κ : Type*} [Fintype κ]
    (f w : κ → ℝ) (q : ℝ) :
    (∫ u in (0:ℝ)..q, ‖probeKernel f w u‖^2) =
      ∑ i, ∑ j, w i * w j * (q * Real.sinc (q * (f i-f j))) := by
  have hp (u v : ℝ) : (phase v u).re = Real.cos (u*v) := by
    calc
      (phase v u).re = Real.cos (v*u) := Complex.exp_ofReal_mul_I_re _
      _ = _ := by rw [mul_comm v u]
  have he (u : ℝ) : ‖probeKernel f w u‖^2 =
      ∑ i, ∑ j, (w i*w j) * Real.cos (u*(f i-f j)) := by
    have h := congrArg Complex.re (probe_energy_expansion f w u)
    rw [Complex.ofReal_re] at h
    simpa [Complex.mul_re, hp] using h
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [intervalIntegral.integral_const_mul, integral_cosineWindow, cosineWindow_zero_sinc]
    · intro j _
      exact (by fun_prop : Continuous (fun u : ℝ =>
        w i*w j * Real.cos (u*(f i-f j)))).intervalIntegrable 0 q
  · intro i _
    exact (by fun_prop : Continuous (fun u : ℝ =>
      ∑ j, w i*w j * Real.cos (u*(f i-f j)))).intervalIntegrable 0 q

/-- The finite comparison is an exact sinc sum over rational log-frequencies.
The diagonal terms use sinc(0)=1, including the endpoints of the height cutoff. -/
theorem primeProbeEnergy_eq_double_sinc (T q : ℝ) :
    primeProbeEnergy T q = (q / (Real.log T)^2) *
      ∑ n ∈ Finset.Ioc 0 ⌊T⌋₊, ∑ m ∈ Finset.Ioc 0 ⌊T⌋₊,
        (ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt m /
          ((n : ℝ)*(m : ℝ))) *
          Real.sinc (2 * Real.pi * q * Real.log ((n : ℝ) / (m : ℝ)) / Real.log T) := by
  classical
  let s := Finset.Ioc 0 ⌊T⌋₊
  let w (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n / (n : ℝ) / Real.log T
  let f (n : ℕ) : ℝ := 2 * Real.pi * Real.log n / Real.log T
  have hprobe (u : ℝ) : primeFourierProbe T u =
      probeKernel (fun n : s => f n) (fun n : s => w n) u := by
    rw [probeKernel, Finset.sum_coe_sort s (fun n : ℕ => (w n : ℂ) * phase (f n) u)]
    unfold primeFourierProbe
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    unfold phase
    congr 1
    dsimp [f]
    push_cast
    ring
  unfold primeProbeEnergy
  simp_rw [hprobe]
  rw [probeKernel_energy_sinc]
  have hs : (∑ i : s, ∑ j : s, w i * w j * (q * Real.sinc (q * (f i-f j)))) =
      ∑ i ∈ s, ∑ j ∈ s, w i * w j * (q * Real.sinc (q * (f i-f j))) := by
    let term (i j : ℕ) := w i * w j * (q * Real.sinc (q * (f i - f j)))
    calc
      _ = ∑ i : s, ∑ j ∈ s, term i j :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_coe_sort s (fun j : ℕ => term i j))
      _ = _ := Finset.sum_coe_sort s (fun i : ℕ => ∑ j ∈ s, term i j)
  rw [hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hn' : 0 < (n:ℝ) := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
  have hm' : 0 < (m:ℝ) := by exact_mod_cast (Finset.mem_Ioc.mp hm).1
  rw [Real.log_div hn'.ne' hm'.ne']
  have he : q*(f n-f m) = 2 * Real.pi * q * (Real.log n-Real.log m) / Real.log T := by
    dsimp [f]
    ring
  rw [he]
  dsimp [w]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
  ring

/--
info: 'RiemannResearch.Analysis.MontgomeryPrimeTrace.primeProbeEnergy_eq_double_sinc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms primeProbeEnergy_eq_double_sinc

end RiemannResearch.Analysis.MontgomeryPrimeTrace
