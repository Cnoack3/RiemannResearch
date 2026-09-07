import RiemannResearch.RH.ArithmeticReturnPoisson
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Compact logarithmic tests give genuine positive Schwartz kernels

Source: §4 of the user-provided Nyman--Weil note. This is the actual
transformation g(t)=t^(-1/2)u(-log t), extended by zero for nonpositive t.
Lean's total square root automatically makes the nonpositive values zero.
The proof supplies compact support and smoothness, including at t=0.
-/

noncomputable section
open scoped Topology SchwartzMap

namespace RiemannResearch.RH

/-- Actual logarithmic kernel, zero on the nonpositive half-line. -/
def inverseLogarithmicHalfDensity (u : ℝ → ℂ) (t : ℝ) : ℂ :=
  (Real.sqrt t)⁻¹ • u (-Real.log t)

theorem inverseLogarithmicHalfDensity_zero_nonpos (u : ℝ → ℂ)
    {t : ℝ} (ht : t ≤ 0) : inverseLogarithmicHalfDensity u t = 0 := by
  simp [inverseLogarithmicHalfDensity, Real.sqrt_eq_zero_of_nonpos ht]

theorem inverseLogarithmicHalfDensity_zero_below {u : ℝ → ℂ} {b t : ℝ}
    (hb : ∀ y > b, u y = 0) (ht : t < Real.exp (-b)) :
    inverseLogarithmicHalfDensity u t = 0 := by
  by_cases htp : 0 < t
  · have hl : Real.log t < -b := (Real.log_lt_iff_lt_exp htp).mpr ht
    simp [inverseLogarithmicHalfDensity, hb (-Real.log t) (by linarith)]
  · exact inverseLogarithmicHalfDensity_zero_nonpos u (le_of_not_gt htp)

theorem inverseLogarithmicHalfDensity_zero_above {u : ℝ → ℂ} {a t : ℝ}
    (ha : ∀ y < a, u y = 0) (ht : Real.exp (-a) < t) :
    inverseLogarithmicHalfDensity u t = 0 := by
  have htp : 0 < t := lt_trans (Real.exp_pos _) ht
  have hl : -a < Real.log t := (Real.lt_log_iff_exp_lt htp).mpr ht
  simp [inverseLogarithmicHalfDensity, ha (-Real.log t) (by linarith)]

/-- The apparent singularity at zero is absent because the kernel is exactly
zero on the full interval `(-∞, exp(-b))`. -/
theorem inverseLogarithmicHalfDensity_contDiff {u : ℝ → ℂ} {b : ℝ}
    {r : WithTop ℕ∞} (hu : ContDiff ℝ r u) (hb : ∀ y > b, u y = 0) :
    ContDiff ℝ r (inverseLogarithmicHalfDensity u) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : 0 < t
  · change ContDiffAt ℝ r (fun x : ℝ => (Real.sqrt x)⁻¹ • u (-Real.log x)) t
    fun_prop (disch := positivity)
  · have hte : t < Real.exp (-b) := lt_of_le_of_lt (le_of_not_gt ht) (Real.exp_pos _)
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hte] with x hx
    exact inverseLogarithmicHalfDensity_zero_below hb hx

/-- The transformed kernel has a concrete compact support interval bounded
strictly away from zero. -/
theorem inverseLogarithmicHalfDensity_tsupport {u : ℝ → ℂ} {a b : ℝ}
    (ha : ∀ y < a, u y = 0) (hb : ∀ y > b, u y = 0) :
    tsupport (inverseLogarithmicHalfDensity u) ⊆
      Set.Icc (Real.exp (-b)) (Real.exp (-a)) := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  constructor
  · by_contra h
    exact ht (inverseLogarithmicHalfDensity_zero_below hb (lt_of_not_ge h))
  · by_contra h
    exact ht (inverseLogarithmicHalfDensity_zero_above ha (lt_of_not_ge h))

theorem inverseLogarithmicHalfDensity_hasCompactSupport {u : ℝ → ℂ} {a b : ℝ}
    (ha : ∀ y < a, u y = 0) (hb : ∀ y > b, u y = 0) :
    HasCompactSupport (inverseLogarithmicHalfDensity u) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure
    (inverseLogarithmicHalfDensity_tsupport ha hb)

/-- The actual positive Schwartz kernel associated with a compact smooth u. -/
def logarithmicSchwartzKernel {u : ℝ → ℂ} {a b : ℝ}
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (ha : ∀ y < a, u y = 0) (hb : ∀ y > b, u y = 0) : SchwartzMap ℝ ℂ :=
  (inverseLogarithmicHalfDensity_hasCompactSupport ha hb).toSchwartzMap
    (inverseLogarithmicHalfDensity_contDiff hu hb)

@[simp] theorem logarithmicSchwartzKernel_apply {u : ℝ → ℂ} {a b : ℝ}
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (ha : ∀ y < a, u y = 0) (hb : ∀ y > b, u y = 0) (t : ℝ) :
    logarithmicSchwartzKernel hu ha hb t = inverseLogarithmicHalfDensity u t := rfl

/-- The two half-density substitutions are exact inverses on logarithmic space. -/
theorem logarithmicHalfDensity_inverse (u : ℝ → ℂ) :
    logarithmicHalfDensity (inverseLogarithmicHalfDensity u) = u := by
  funext y
  have hs : Real.sqrt (Real.exp (-y)) = Real.exp (-y / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  simp [logarithmicHalfDensity, inverseLogarithmicHalfDensity, hs,
    smul_smul, Real.exp_ne_zero]

/-- Poisson-kernel identification for every genuinely compact smooth input,
with the actual Schwartz regularity and support hypotheses discharged. -/
theorem nymanFullReturn_eq_actual_poisson_kernel {u : ℝ → ℂ} {a b : ℝ}
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (ha : ∀ y < a, u y = 0) (hb : ∀ y > b, u y = 0)
    (n : ℕ) [NeZero n] (y : ℝ) :
    nymanFullReturn n u y = Real.exp (-y / 2) •
      RiemannResearch.Analysis.conductorLatticeDiscrepancy
        (logarithmicSchwartzKernel hu ha hb) (n : ℝ) (Real.exp (-y)) := by
  have hkernel : ∀ t ≤ 0, logarithmicSchwartzKernel hu ha hb t = 0 := by
    intro t ht
    exact inverseLogarithmicHalfDensity_zero_nonpos u ht
  have he := nymanFullReturn_logarithmicHalfDensity
    (logarithmicSchwartzKernel hu ha hb) hkernel n y
  have hi : logarithmicHalfDensity (logarithmicSchwartzKernel hu ha hb) = u :=
    logarithmicHalfDensity_inverse u
  rwa [hi] at he

end RiemannResearch.RH
