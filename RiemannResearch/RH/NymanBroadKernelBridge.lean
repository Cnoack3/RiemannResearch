import RiemannResearch.RH.NymanReturnAbel
import RiemannResearch.RH.NymanReturnKernelMoments
import RiemannResearch.RH.ArithmeticCompletionDifferential
import RiemannResearch.Analysis.BroadKernelProfile
import RiemannResearch.Analysis.BroadProfileRegularity
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# The actual normalized Nyman broad family is the cumulative-kernel profile

The input is u_R(y)=R^(-1/2)φ(y/R). The actual arithmetic return and the
actual operator D²−1/4 give exactly the four-term profile used in the broad
limit estimates. Derivative arrays are the actual derivatives of one smooth
compact φ; no output-family identity is an assumption.
-/

open MeasureTheory Set
open scoped Topology
namespace RiemannResearch.RH
open RiemannResearch.Analysis

noncomputable def nymanBroadPotential (φ : ℝ → ℝ) (R y : ℝ) : ℂ :=
  ((Real.sqrt R)⁻¹ : ℝ) • (φ (y / R) : ℂ)

noncomputable def nymanBroadTest (n : ℕ) (φ : ℝ → ℝ) (R : ℝ) : ℝ → ℂ :=
  poleCancellationOperator (nymanFullReturn n (nymanBroadPotential φ R))

theorem contDiff_nymanBroadPotential {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ) (R : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (nymanBroadPotential φ R) := by
  exact (contDiff_const : ContDiff ℝ (↑(⊤ : ℕ∞))
    (fun _ : ℝ => (Real.sqrt R)⁻¹)).smul
    (Complex.ofRealCLM.contDiff.comp (hφ.comp (contDiff_id.div_const R)))

theorem nymanBroadPotential_zero_below {φ : ℝ → ℝ} {a R : ℝ}
    (ha : ∀ x < a, φ x = 0) (hR : 0 < R) :
    ∀ y < a * R, nymanBroadPotential φ R y = 0 := by
  intro y hy
  have hy' : y / R < a := (div_lt_iff₀ hR).mpr hy
  simp [nymanBroadPotential, ha _ hy']

theorem nymanBroadPotential_zero_above {φ : ℝ → ℝ} {b R : ℝ}
    (hb : ∀ x > b, φ x = 0) (hR : 0 < R) :
    ∀ y > b * R, nymanBroadPotential φ R y = 0 := by
  intro y hy
  have hy' : b < y / R := (lt_div_iff₀ hR).mpr hy
  simp [nymanBroadPotential, hb _ hy']

/-- Exact derivative scaling, including the half-density amplitude. -/
theorem iteratedDeriv_nymanBroadPotential {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ) (R : ℝ) (j : ℕ) (y : ℝ) :
    iteratedDeriv j (nymanBroadPotential φ R) y =
      (((Real.sqrt R)⁻¹ * (R⁻¹) ^ j : ℝ) : ℂ) *
        ((iteratedDeriv (F := ℝ) j φ (y / R) : ℝ) : ℂ) := by
  have hj : (j : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) :=
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl j).le
  have hc : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (φ x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hφ
  have hscale : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun x : ℝ => (φ (R⁻¹ * x) : ℂ)) := hc.comp (contDiff_const.mul contDiff_id)
  have hdef : nymanBroadPotential φ R =
      (Real.sqrt R)⁻¹ • (fun x : ℝ => (φ (R⁻¹ * x) : ℂ)) := by
    funext x
    simp only [nymanBroadPotential, Pi.smul_apply, div_eq_mul_inv, mul_comm]
  rw [hdef, iteratedDeriv_const_smul ((hscale.of_le hj).contDiffAt),
    iteratedDeriv_comp_const_smul (hc.of_le hj), iteratedDeriv_real_to_complex hφ]
  simp only [Pi.smul_apply, smul_smul, Complex.real_smul, Complex.ofReal_mul,
    div_eq_mul_inv, mul_comm, mul_assoc]

private theorem smooth_iterated_nymanBroadPotential {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ) (R : ℝ) (j : ℕ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (iteratedDeriv j (nymanBroadPotential φ R)) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv j (contDiff_nymanBroadPotential hφ R)

/-- Integral representation of each actual differentiated arithmetic return.
The only profile data here are actual derivative continuity and boundedness;
the final endpoint below supplies both from compact smooth φ. -/
theorem nymanFullReturn_iteratedBroadPotential_eq (n : ℕ) (hn : 0 < n)
    {φ : ℝ → ℝ} {a b R : ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x < a, φ x = 0) (hb : ∀ x > b, φ x = 0) (hR : 0 < R)
    (hM : ∀ j : ℕ, ∃ M : ℝ, ∀ x : ℝ, |iteratedDeriv j φ x| ≤ M)
    (j : ℕ) (x : ℝ) :
    nymanFullReturn n (iteratedDeriv j (nymanBroadPotential φ R)) (R * x) =
      (((Real.sqrt R)⁻¹ *
        ((R⁻¹) ^ (j + 1) * scaledKernelConvolution (nymanReturnKernel n)
            (iteratedDeriv (j + 1) φ) R x +
          (R⁻¹) ^ j / 2 * scaledKernelConvolution (nymanReturnKernel n)
            (iteratedDeriv j φ) R x) : ℝ) : ℂ) := by
  have hU := contDiff_nymanBroadPotential hφ R
  have hUa := nymanBroadPotential_zero_below ha hR
  have hUb := nymanBroadPotential_zero_above hb hR
  have hkc (k : ℕ) : Continuous (iteratedDeriv k φ) :=
    ContDiff.continuous_iteratedDeriv' k
      (hφ.of_le (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k).le)
  have hi (k : ℕ) : Integrable (fun t : ℝ => nymanReturnKernel n t *
      iteratedDeriv k φ (x - t / R)) := by
    obtain ⟨M, hM⟩ := hM k
    exact integrable_scaledKernel_integrand _ _ (integrable_nymanReturnKernel hn)
      (hkc k) M hM R x
  rw [nymanFullReturn_eq_kernel_convolution n
    ((smooth_iterated_nymanBroadPotential hφ R j).of_le (by simp))
    (iteratedDeriv_zero_below_of_zero_below hUa j)
    (iteratedDeriv_zero_above_of_zero_above hUb j)]
  have harg (t : ℝ) : (R * x - t) / R = x - t / R := by
    field_simp [hR.ne']
  have heq :
      (fun t : ℝ => (nymanReturnKernel n t : ℂ) *
        (deriv (iteratedDeriv j (nymanBroadPotential φ R)) (R * x - t) +
          (1 / 2 : ℂ) * iteratedDeriv j (nymanBroadPotential φ R) (R * x - t))) =
      fun t : ℝ => (((Real.sqrt R)⁻¹ *
        ((R⁻¹) ^ (j + 1) * (nymanReturnKernel n t * iteratedDeriv (j + 1) φ (x - t / R)) +
          (R⁻¹) ^ j / 2 * (nymanReturnKernel n t * iteratedDeriv j φ (x - t / R))) : ℝ) : ℂ) := by
    funext t
    rw [← iteratedDeriv_succ, iteratedDeriv_nymanBroadPotential hφ,
      iteratedDeriv_nymanBroadPotential hφ, harg]
    push_cast
    ring
  rw [heq, integral_complex_ofReal, integral_const_mul,
    integral_add ((hi (j + 1)).const_mul _) ((hi j).const_mul _),
    integral_const_mul, integral_const_mul]
  rfl

/-- The normalized actual pole-cancelled arithmetic return has exactly the
four coefficients in the broad differential kernel profile. -/
theorem nymanBroadTest_scaled_eq_of_bounds (n : ℕ) (hn : 0 < n)
    {φ : ℝ → ℝ} {a b R : ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x < a, φ x = 0) (hb : ∀ x > b, φ x = 0) (hR : 0 < R)
    (hM : ∀ j : ℕ, ∃ M : ℝ, ∀ x : ℝ, |iteratedDeriv j φ x| ≤ M)
    (x : ℝ) :
    (Real.sqrt R : ℂ) * nymanBroadTest n φ R (R * x) =
      (differentialBroadKernelProfile (nymanReturnKernel n) φ R x : ℂ) := by
  have hU := contDiff_nymanBroadPotential hφ R
  have hUa := nymanBroadPotential_zero_below ha hR
  have h2 := nymanFullReturn_iteratedBroadPotential_eq n hn hφ ha hb hR hM 2 x
  have h0 := nymanFullReturn_iteratedBroadPotential_eq n hn hφ ha hb hR hM 0 x
  simp only [iteratedDeriv_zero, pow_zero, zero_add] at h0
  have hcomm := congrFun (nymanFullReturn_iteratedDeriv n hU hUa 2) (R * x)
  have hD : deriv (deriv (nymanFullReturn n (nymanBroadPotential φ R))) (R * x) =
      nymanFullReturn n (iteratedDeriv 2 (nymanBroadPotential φ R)) (R * x) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hcomm
  change (Real.sqrt R : ℂ) *
    (deriv (deriv (nymanFullReturn n (nymanBroadPotential φ R))) (R * x) -
      (1 / 4 : ℝ) • nymanFullReturn n (nymanBroadPotential φ R) (R * x)) = _
  rw [hD, h2, h0]
  have hs : (Real.sqrt R : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hR).ne'
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  unfold differentialBroadKernelProfile broadKernelProfile
  simp only [Complex.real_smul, iteratedDeriv_zero]
  push_cast
  field_simp [hs, hRc] <;> ring

/-- Complete actual-family bridge: all derivative bounds used in the proof
come from the input's smoothness and compact support. -/
theorem nymanBroadTest_scaled_eq (n : ℕ) (hn : 0 < n)
    {φ : ℝ → ℝ} {a b R : ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x < a, φ x = 0) (hb : ∀ x > b, φ x = 0) (hR : 0 < R)
    (x : ℝ) :
    (Real.sqrt R : ℂ) * nymanBroadTest n φ R (R * x) =
      (differentialBroadKernelProfile (nymanReturnKernel n) φ R x : ℂ) := by
  apply nymanBroadTest_scaled_eq_of_bounds n hn hφ ha hb hR _ x
  intro j
  obtain ⟨M, _, hM⟩ := broadProfile_exists_derivative_bound hφ
    (broadProfile_hasCompactSupport_of_bounds ha hb) j
  exact ⟨M, hM⟩

end RiemannResearch.RH
