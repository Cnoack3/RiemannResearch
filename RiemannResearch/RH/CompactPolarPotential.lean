import RiemannResearch.RH.ArithmeticCompletionDifferential
import RiemannResearch.Analysis.BilateralLaplaceDifferential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Order.Compact

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Compact smooth potentials for actual pole-annihilating tests

The Green formula solves (D²−1/4)v=f. The two actual polar Laplace moments
remove its two outer exponential tails, preserving the support interval.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open MeasureTheory.BilateralLaplace

namespace RiemannResearch.RH

private def polarPrimitive (c : ℂ) (l : ℝ) (f : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∫ t in l..y, f t * kernel c t

private theorem polarKernel_contDiff (c : ℂ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (kernel c) := by
  have hlin : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y : ℝ => -c * (y : ℂ)) :=
    contDiff_const.mul Complex.ofRealCLM.contDiff
  exact hlin.cexp

private theorem hasDerivAt_polarPrimitive {f : ℝ → ℂ} (hf : Continuous f)
    (c : ℂ) (l y : ℝ) :
    HasDerivAt (polarPrimitive c l f) (f y * kernel c y) y := by
  have hc := hf.mul (polarKernel_contDiff c).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable l y)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

private theorem polarPrimitive_contDiff {f : ℝ → ℂ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (c : ℂ) (l : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (polarPrimitive c l f) := by
  have hd : deriv (polarPrimitive c l f) = fun y => f y * kernel c y := by
    funext y
    exact (hasDerivAt_polarPrimitive hf.continuous c l y).deriv
  apply contDiff_infty_iff_deriv.mpr
  constructor
  · intro y
    exact (hasDerivAt_polarPrimitive hf.continuous c l y).differentiableAt
  · rw [hd]
    exact hf.mul (polarKernel_contDiff c)

private def polarResolvent (c : ℂ) (l : ℝ) (f : ℝ → ℂ) (y : ℝ) : ℂ :=
  kernel (-c) y * polarPrimitive c l f y

private theorem polarResolvent_contDiff {f : ℝ → ℂ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (c : ℂ) (l : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (polarResolvent c l f) :=
  (polarKernel_contDiff (-c)).mul (polarPrimitive_contDiff hf c l)

private theorem kernel_neg_mul (c : ℂ) (y : ℝ) : kernel (-c) y * kernel c y = 1 := by
  simp only [kernel, neg_neg]
  rw [← Complex.exp_add,
    show c * (y : ℂ) + -c * (y : ℂ) = 0 by ring, Complex.exp_zero]

private theorem hasDerivAt_polarResolvent {f : ℝ → ℂ} (hf : Continuous f)
    (c : ℂ) (l y : ℝ) :
    HasDerivAt (polarResolvent c l f) (c * polarResolvent c l f y + f y) y := by
  have h := (hasDerivAt_kernel_spatial (-c) y).mul
    (hasDerivAt_polarPrimitive hf c l y)
  convert h using 1 <;> first | rfl | skip
  simp only [polarResolvent, neg_neg]
  have he := kernel_neg_mul c y
  calc
    c * (kernel (-c) y * polarPrimitive c l f y) + f y =
      c * (kernel (-c) y * polarPrimitive c l f y) +
        f y * (kernel (-c) y * kernel c y) := by rw [he, mul_one]
    _ = _ := by ring

/-- An explicit compact potential; the anchor lies strictly below both endpoints. -/
def compactPolarPotential (a b : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  polarResolvent (1/2) (min a b - 1) f -
    polarResolvent (-1/2) (min a b - 1) f

theorem compactPolarPotential_contDiff {f : ℝ → ℂ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (compactPolarPotential a b f) :=
  (polarResolvent_contDiff hf _ _).sub (polarResolvent_contDiff hf _ _)

private def compactPolarPotentialFirst (a b : ℝ) (f : ℝ → ℂ) (y : ℝ) : ℂ :=
  (1/2 : ℂ) * (polarResolvent (1/2) (min a b - 1) f y +
    polarResolvent (-1/2) (min a b - 1) f y)

private theorem hasDerivAt_compactPolarPotential {f : ℝ → ℂ} (hf : Continuous f)
    (a b y : ℝ) : HasDerivAt (compactPolarPotential a b f)
      (compactPolarPotentialFirst a b f y) y := by
  have h := (hasDerivAt_polarResolvent hf (1/2) (min a b-1) y).sub
    (hasDerivAt_polarResolvent hf (-1/2) (min a b-1) y)
  convert h using 1 <;> first | rfl | skip
  unfold compactPolarPotentialFirst
  ring

private theorem hasDerivAt_compactPolarPotentialFirst {f : ℝ → ℂ} (hf : Continuous f)
    (a b y : ℝ) : HasDerivAt (compactPolarPotentialFirst a b f)
      ((1/4 : ℂ) * compactPolarPotential a b f y + f y) y := by
  have h := ((hasDerivAt_polarResolvent hf (1/2) (min a b-1) y).add
    (hasDerivAt_polarResolvent hf (-1/2) (min a b-1) y)).const_mul (1/2 : ℂ)
  convert h using 1 <;> first | rfl | skip
  simp only [compactPolarPotential, Pi.sub_apply]
  ring

/-- The actual differential equation follows from both FTC derivatives. -/
theorem poleCancellationOperator_compactPolarPotential {f : ℝ → ℂ}
    (hf : Continuous f) (a b : ℝ) :
    poleCancellationOperator (compactPolarPotential a b f) = f := by
  have hd : deriv (compactPolarPotential a b f) = compactPolarPotentialFirst a b f := by
    funext y
    exact (hasDerivAt_compactPolarPotential hf a b y).deriv
  funext y
  unfold poleCancellationOperator
  rw [hd, (hasDerivAt_compactPolarPotentialFirst hf a b y).deriv]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

private theorem polarPrimitive_zero_below {f : ℝ → ℂ} {a l y : ℝ}
    (ha : ∀ t < a, f t = 0) (hl : l < a) (hy : y < a) (c : ℂ) :
    polarPrimitive c l f y = 0 := by
  unfold polarPrimitive
  calc
    (∫ t in l..y, f t * kernel c t) = ∫ _ in l..y, (0 : ℂ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ≤ max l y := ht.2
      change f t * kernel c t = 0
      rw [ha t (lt_of_le_of_lt ht' (max_lt_iff.mpr ⟨hl, hy⟩)), zero_mul]
    _ = 0 := by simp

private theorem polarPrimitive_eq_full_transform {f : ℝ → ℂ} {a b l y : ℝ}
    (ha : ∀ t < a, f t = 0) (hb : ∀ t > b, f t = 0)
    (hla : l < a) (hlb : l ≤ b) (hy : b < y) (c : ℂ) :
    polarPrimitive c l f y = transform f c := by
  unfold polarPrimitive transform
  rw [intervalIntegral.integral_of_le (le_trans hlb hy.le)]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  by_cases htl : l < t
  · have hyt : y < t := by
      by_contra h
      exact ht ⟨htl, le_of_not_gt h⟩
    rw [hb t (lt_trans hy hyt), zero_mul]
  · rw [ha t (lt_of_le_of_lt (le_of_not_gt htl) hla), zero_mul]

theorem compactPolarPotential_zero_below {f : ℝ → ℂ} {a b y : ℝ}
    (ha : ∀ t < a, f t = 0) (hy : y < a) :
    compactPolarPotential a b f y = 0 := by
  have hl : min a b - 1 < a := by linarith [min_le_left a b]
  simp only [compactPolarPotential, Pi.sub_apply, polarResolvent,
    polarPrimitive_zero_below ha hl hy, mul_zero, sub_self]

theorem compactPolarPotential_zero_above {f : ℝ → ℂ} {a b y : ℝ}
    (ha : ∀ t < a, f t = 0) (hb : ∀ t > b, f t = 0)
    (h0 : centeredTransform f 0 = 0) (h1 : centeredTransform f 1 = 0)
    (hy : b < y) : compactPolarPotential a b f y = 0 := by
  have hla : min a b - 1 < a := by linarith [min_le_left a b]
  have hlb : min a b - 1 ≤ b := by linarith [min_le_right a b]
  have hp : transform f (1/2) = 0 := by
    simpa only [centeredTransform, show (1 : ℂ) - 1/2 = 1/2 by norm_num] using h1
  have hm : transform f (-1/2) = 0 := by
    simpa only [centeredTransform, zero_sub, neg_div] using h0
  simp only [compactPolarPotential, Pi.sub_apply, polarResolvent,
    polarPrimitive_eq_full_transform ha hb hla hlb hy, hp, hm, mul_zero, sub_self]

/-- The potential has the original test's support interval. -/
theorem compactPolarPotential_tsupport {f : ℝ → ℂ} {a b : ℝ}
    (ha : ∀ t < a, f t = 0) (hb : ∀ t > b, f t = 0)
    (h0 : centeredTransform f 0 = 0) (h1 : centeredTransform f 1 = 0) :
    tsupport (compactPolarPotential a b f) ⊆ Set.Icc a b := by
  apply closure_minimal _ isClosed_Icc
  intro y hy
  constructor
  · by_contra h
    exact hy (compactPolarPotential_zero_below ha (lt_of_not_ge h))
  · by_contra h
    exact hy (compactPolarPotential_zero_above ha hb h0 h1 (lt_of_not_ge h))

/-- Every compact smooth polar-annihilating test has an actual compact smooth
potential, with no assumed differential inverse or support-transfer axiom. -/
theorem exists_compact_smooth_polarPotential {f : ℝ → ℂ} {a b : ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (ha : ∀ t < a, f t = 0) (hb : ∀ t > b, f t = 0)
    (h0 : centeredTransform f 0 = 0) (h1 : centeredTransform f 1 = 0) :
    ∃ v : ℝ → ℂ, ContDiff ℝ (↑(⊤ : ℕ∞)) v ∧ HasCompactSupport v ∧
      tsupport v ⊆ Set.Icc a b ∧ poleCancellationOperator v = f := by
  refine ⟨compactPolarPotential a b f, compactPolarPotential_contDiff hf a b, ?_,
    compactPolarPotential_tsupport ha hb h0 h1,
    poleCancellationOperator_compactPolarPotential hf.continuous a b⟩
  exact isCompact_Icc.of_isClosed_subset isClosed_closure
    (compactPolarPotential_tsupport ha hb h0 h1)

end RiemannResearch.RH
