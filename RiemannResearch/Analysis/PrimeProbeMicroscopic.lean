import RiemannResearch.Analysis.MontgomeryPrimeProbe
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Frequency variance and the microscopic limit of prime probes

Source: user-provided V_vector_space_RH.pdf, Sections 2--5, for the prime-power
gauge orbit and the distinction between fixed and moving frequency supports.
The exact finite probe expansion is inherited from MontgomeryPrimeProbe
(Montgomery, 1973, https://websites.umich.edu/~hlm/paircor1.pdf).
The characteristic-function variance estimate below is an elementary deduction;
no mathematical novelty is asserted.

For nonnegative weights of total mass one, 1-|H(d)|^2 is the determinant of
the two-site unit-diagonal Gram matrix. An actual discrete DPP also needs its
full kernel to be a positive contraction: this determinant alone does not
construct that law. Dividing a finite sample Gram by its trace is one way to
obtain a contraction.

The exact signed cosine identity precedes the estimate. The final theorem
allows the finite index type itself to vary with height. At scale log T,
frequency variance o((log T)^2) forces the two-site determinant to vanish.
It therefore cannot supply nonzero sine-kernel repulsion at that scale.
No assertion about actual zeta pair correlations is used or concluded.
-/

noncomputable section
open Filter
open scoped BigOperators ComplexConjugate Topology
namespace RiemannResearch.Analysis.MontgomeryFormFactor
open ZeroOrdinate
variable {κ : Type*} [Fintype κ]

def spectralVariance (q b : κ → ℝ) : ℝ :=
  (∑ p, ∑ r, b p * b r * (q p - q r)^2) / 2

def probeRepulsion (q b : κ → ℝ) (d : ℝ) : ℝ :=
  1 - ‖probeKernel q b d‖^2

theorem probe_energy_cos (q b : κ → ℝ) (d : ℝ) :
    ‖probeKernel q b d‖^2 =
      ∑ p, ∑ r, b p * b r * Real.cos ((q p - q r) * d) := by
  have h := congrArg Complex.re (probe_energy_expansion q b d)
  simp only [Complex.ofReal_re] at h
  simpa [phase, Complex.exp_re] using h

theorem probeRepulsion_exact (q b : κ → ℝ) (hb : ∑ p, b p = 1) (d : ℝ) :
    probeRepulsion q b d =
      ∑ p, ∑ r, b p * b r * (1 - Real.cos ((q p - q r) * d)) := by
  have hmass : (∑ p, ∑ r, b p * b r) = 1 := by
    simp_rw [← Finset.mul_sum]
    rw [hb]
    simpa using hb
  simp only [probeRepulsion, probe_energy_cos, mul_sub, mul_one,
    Finset.sum_sub_distrib]
  rw [hmass]

theorem probeRepulsion_nonneg (q b : κ → ℝ)
    (hb0 : ∀ p, 0 ≤ b p) (hb : ∑ p, b p = 1) (d : ℝ) :
    0 ≤ probeRepulsion q b d := by
  rw [probeRepulsion_exact q b hb]
  exact Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun r _ =>
    mul_nonneg (mul_nonneg (hb0 p) (hb0 r)) (sub_nonneg.mpr (Real.cos_le_one _))))

private theorem one_sub_cos_le_half_sq (x : ℝ) :
    1 - Real.cos x ≤ x^2 / 2 := by
  have h : |Real.sin (x / 2)| ≤ |x / 2| := Real.abs_sin_le_abs
  have hsq := mul_self_le_mul_self (abs_nonneg (Real.sin (x/2))) h
  rw [← sq, ← sq, sq_abs, sq_abs] at hsq
  have hc := Real.cos_two_mul (x / 2)
  have hs := Real.sin_sq_add_cos_sq (x / 2)
  rw [show 2 * (x/2) = x by ring] at hc
  nlinarith

theorem probeRepulsion_le_variance (q b : κ → ℝ)
    (hb0 : ∀ p, 0 ≤ b p) (hb : ∑ p, b p = 1) (d : ℝ) :
    probeRepulsion q b d ≤ d^2 * spectralVariance q b := by
  rw [probeRepulsion_exact q b hb]
  calc
    _ ≤ ∑ p, ∑ r, b p * b r * (((q p - q r) * d)^2 / 2) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_left (one_sub_cos_le_half_sq _)
        (mul_nonneg (hb0 p) (hb0 r))
    _ = _ := by
      unfold spectralVariance
      simp only [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro r hr
      ring

theorem spectralVariance_eq_centered (q b : κ → ℝ)
    (hb : ∑ p, b p = 1) :
    spectralVariance q b = ∑ p, b p * (q p - ∑ r, b r * q r)^2 := by
  have hvar : spectralVariance q b =
      (∑ p, b p * q p ^ 2) - (∑ p, b p * q p)^2 := by
    have he (p r : κ) : b p * b r * (q p - q r)^2 =
        (b p * q p ^ 2) * b r + b p * (b r * q r ^ 2) -
          ((b p * q p) * 2) * (b r * q r) := by ring
    unfold spectralVariance
    simp_rw [he, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hb, mul_one, ← Finset.sum_mul, hb, one_mul]
    ring
  rw [hvar]
  have he (p : κ) : b p * (q p - ∑ r, b r * q r)^2 =
      b p * q p ^ 2 - ((b p * q p) * 2) * (∑ r, b r * q r) +
        b p * (∑ r, b r * q r)^2 := by ring
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, hb, one_mul]
  ring

theorem microscopic_repulsion_tendsto_zero
    {α : Type*} {l : Filter α} (I : α → Type*) [∀ a, Fintype (I a)]
    (q b : ∀ a, I a → ℝ) (scale : α → ℝ)
    (hb0 : ∀ a p, 0 ≤ b a p) (hb : ∀ a, ∑ p, b a p = 1)
    (hsmall : Tendsto (fun a => spectralVariance (q a) (b a) / scale a ^ 2)
      l (𝓝 0)) (u : ℝ) :
    Tendsto (fun a => probeRepulsion (q a) (b a) (u / scale a)) l (𝓝 0) := by
  have hlim := hsmall.const_mul (u^2)
  simp only [mul_zero] at hlim
  apply squeeze_zero (fun a => probeRepulsion_nonneg _ _ (hb0 a) (hb a) _) _ hlim
  intro a
  calc
    _ ≤ (u / scale a)^2 * spectralVariance (q a) (b a) :=
      probeRepulsion_le_variance _ _ (hb0 a) (hb a) _
    _ = _ := by ring

end RiemannResearch.Analysis.MontgomeryFormFactor
