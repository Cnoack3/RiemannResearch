import RiemannResearch.Analysis.WeightedMellinEnergy
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact logarithmic Mellin evaluation kernels

Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

The logarithmic moment identity is proved for every natural order, using
the actual gamma integral and an actual logarithmic change of variables.
The resulting Cauchy--Schwarz inequality controls the integral functional
with the kth logarithmic multiplier. An all-order local dominated
differentiation argument then proves its iterated derivative identity.
The analytic identity and the arithmetic energy membership remain
distinct: no arithmetic energy estimate is established in this module.

Pinned API source: mathlib 51e6992efd06126df61a496bebf8f49482a4e129,
Gamma/Basic.lean, Gaussian/GaussianIntegral.lean and IntegralEqImproper.lean.
Reusable project sources at 443c8a75da168bb561d0f3ca2298a039d69607ee:
Analysis/WeightedMellinEnergy.lean and Analysis/LogarithmicMellinBounds.lean.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace MeasureTheory.WeightedMellin

/-- Exact gamma moments at an arbitrary positive exponential rate. -/
theorem scaled_exp_moment_integrable (j : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun y : ℝ => y ^ j * Real.exp (-(δ * y))) (Ioi 0) := by
  simpa only [Real.rpow_one, Real.rpow_natCast, neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (j : ℝ))
      (b := δ) (by have h := Nat.cast_nonneg (α := ℝ) j; linarith) (by norm_num) hδ)

theorem scaled_exp_moment_integral (j : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (∫ y in Ioi (0 : ℝ), y ^ j * Real.exp (-(δ * y))) =
      (j.factorial : ℝ) / δ ^ (j + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (j : ℝ) + 1) (r := δ) (by positivity) hδ
  have he : (j : ℝ) + 1 - 1 = (j : ℝ) := by ring
  have hc : (j : ℝ) + 1 = ((j + 1 : ℕ) : ℝ) := by push_cast; ring
  simp only [he, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
  simp only [hc, Real.rpow_natCast] at h
  simpa only [div_pow, one_pow, div_eq_mul_inv, mul_comm, mul_one, inv_pow] using h

private theorem log_moment_exp_change (j : ℕ) (δ y : ℝ) :
    Real.exp y • ((Real.log (Real.exp y)) ^ j *
      (Real.exp y) ^ (-δ - 1)) =
        y ^ j * Real.exp (-(δ * y)) := by
  rw [smul_eq_mul, Real.log_exp,
    Real.rpow_def_of_pos (Real.exp_pos y), Real.log_exp]
  calc
    _ = y ^ j * (Real.exp y * Real.exp (y * (-δ - 1))) := by ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 2
      ring

/-- Every logarithmic moment of the Mellin kernel is integrable. -/
theorem log_moment_integrable (j : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun x : ℝ => (Real.log x) ^ j * x ^ (-δ - 1)) (Ioi 1) := by
  have h := (integrableOn_comp_exp_Ioi
    (fun x : ℝ => (Real.log x) ^ j * x ^ (-δ - 1)) 0)
  simp only [Real.exp_zero] at h
  apply h.mp
  convert scaled_exp_moment_integrable j hδ using 1
  funext y
  exact log_moment_exp_change j δ y

/-- Exact logarithmic moments; this quantifies all orders, not sample orders. -/
theorem log_moment_integral (j : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (∫ x in Ioi (1 : ℝ), (Real.log x) ^ j * x ^ (-δ - 1)) =
      (j.factorial : ℝ) / δ ^ (j + 1) := by
  calc
    _ = ∫ y in Ioi (0 : ℝ), y ^ j * Real.exp (-(δ * y)) := by
      have h := integral_comp_exp_Ioi
        (fun x : ℝ => (Real.log x) ^ j * x ^ (-δ - 1)) 0
      simp only [Real.exp_zero] at h
      rw [← h]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y _
      exact log_moment_exp_change j δ y
    _ = _ := scaled_exp_moment_integral j hδ

/-- Kernel for the kth signed logarithmic Mellin integral. -/
def logarithmicKernel (s : ℝ) (z : ℂ) (k : ℕ) (x : ℝ) : ℂ :=
  kernel s z x * (-(Real.log x : ℂ)) ^ k

theorem logarithmicKernel_norm_sq (s : ℝ) (z : ℂ) (k : ℕ)
    {x : ℝ} (hx : 1 < x) :
    ‖logarithmicKernel s z k x‖ ^ 2 =
      (Real.log x) ^ (2 * k) * x ^ (s - 2 * z.re - 1) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  rw [logarithmicKernel, norm_mul, mul_pow, kernel_norm_sq s z hx0,
    norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg hx.le), ← pow_mul]
  rw [Nat.mul_comm k 2]
  ring

theorem logarithmicKernel_memLp (s : ℝ) (z : ℂ) (k : ℕ)
    (hz : s / 2 < z.re) :
    MemLp (logarithmicKernel s z k) 2 (volume.restrict (Ioi (1 : ℝ))) := by
  have hm : Measurable (logarithmicKernel s z k) :=
    (Complex.continuous_ofReal.measurable.pow_const _).mul
      ((Complex.continuous_ofReal.measurable.comp Real.measurable_log).neg.pow_const k)
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2
  apply (log_moment_integrable (2 * k)
    (by linarith : 0 < 2 * z.re - s)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [logarithmicKernel_norm_sq s z k hx]
  congr 2
  ring

/-- The exact squared L2 norm gives the sharp candidate derivative constant. -/
theorem logarithmicKernel_energy (s : ℝ) (z : ℂ) (k : ℕ)
    (hz : s / 2 < z.re) :
    (∫ x in Ioi (1 : ℝ), ‖logarithmicKernel s z k x‖ ^ 2) =
      ((2 * k).factorial : ℝ) / (2 * z.re - s) ^ (2 * k + 1) := by
  calc
    _ = ∫ x in Ioi (1 : ℝ),
        (Real.log x) ^ (2 * k) * x ^ (-(2 * z.re - s) - 1) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [logarithmicKernel_norm_sq s z k hx]
      congr 2
      ring
    _ = _ := log_moment_integral (2 * k) (by linarith)

def logarithmicTransform (f : ℝ → ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  ∫ x in Ioi (1 : ℝ),
    f x * (x : ℂ) ^ (-z - 1) * (-(Real.log x : ℂ)) ^ k

theorem density_mul_logarithmicKernel (f : ℝ → ℂ) (s : ℝ)
    (z : ℂ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    density f s x * logarithmicKernel s z k x =
      f x * (x : ℂ) ^ (-z - 1) * (-(Real.log x : ℂ)) ^ k := by
  rw [logarithmicKernel, ← mul_assoc, density_mul_kernel f s z hx]

theorem logarithmicTransform_integrable {f : ℝ → ℂ} {s : ℝ}
    (hf : FiniteEnergy f s) (k : ℕ) {z : ℂ} (hz : s / 2 < z.re) :
    IntegrableOn (fun x : ℝ =>
      f x * (x : ℂ) ^ (-z - 1) * (-(Real.log x : ℂ)) ^ k) (Ioi 1) := by
  apply ((density_memLp hf).integrable_mul (logarithmicKernel_memLp s z k hz)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact density_mul_logarithmicKernel f s z k (zero_lt_one.trans hx)

theorem logarithmicTransform_sub {f g : ℝ → ℂ} {s : ℝ}
    (hf : FiniteEnergy f s) (hg : FiniteEnergy g s) (k : ℕ)
    {z : ℂ} (hz : s / 2 < z.re) :
    logarithmicTransform (fun x => f x - g x) k z =
      logarithmicTransform f k z - logarithmicTransform g k z := by
  have hfz := logarithmicTransform_integrable hf k hz
  have hgz := logarithmicTransform_integrable hg k hz
  unfold logarithmicTransform
  rw [← integral_sub hfz hgz]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  ring

/-- All orders are controlled as genuine integral functionals, with no
arithmetic or RH premise besides the explicitly given finite energy. -/
theorem logarithmicTransform_norm_sq_le {f : ℝ → ℂ} {s : ℝ}
    (hf : FiniteEnergy f s) (k : ℕ) {z : ℂ} (hz : s / 2 < z.re) :
    ‖logarithmicTransform f k z‖ ^ 2 ≤
      energy f s * ((2 * k).factorial : ℝ) /
        (2 * z.re - s) ^ (2 * k + 1) := by
  have he : logarithmicTransform f k z =
      ∫ x in Ioi (1 : ℝ), density f s x * logarithmicKernel s z k x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact (density_mul_logarithmicKernel f s z k (zero_lt_one.trans hx)).symm
  rw [he]
  simpa only [density_energy, logarithmicKernel_energy s z k hz, mul_div_assoc]
    using RemoteLaplaceTail.norm_integral_mul_sq_le
      (density_memLp hf) (logarithmicKernel_memLp s z k hz)

/-- Differentiation at every logarithmic order. The dominator retains the
kth power of log, and just one additional log is absorbed in the positive
margin of the half-plane. Its integrability was proved above by L2 pairing. -/
theorem logarithmicTransform_hasDerivAt {f : ℝ → ℂ} {s : ℝ}
    (hf : FiniteEnergy f s) (k : ℕ) {z : ℂ} (hz : s / 2 < z.re) :
    HasDerivAt (logarithmicTransform f k) (logarithmicTransform f (k + 1) z) z := by
  let r : ℝ := (z.re - s / 2) / 4
  have hr : 0 < r := by dsimp [r]; linarith
  let a : ℝ := z.re - 2 * r
  have ha : s / 2 < a := by dsimp [a, r]; linarith
  let G : ℂ → ℝ → ℂ := fun w x =>
    f x * (x : ℂ) ^ (-w - 1) * (-(Real.log x : ℂ)) ^ k
  let G' : ℂ → ℝ → ℂ := fun w x =>
    f x * (x : ℂ) ^ (-w - 1) * (-(Real.log x : ℂ)) ^ (k + 1)
  have hmeas (w : ℂ) (j : ℕ) :
      Measurable (fun x : ℝ =>
        f x * (x : ℂ) ^ (-w - 1) * (-(Real.log x : ℂ)) ^ j) :=
    (hf.1.mul (Complex.continuous_ofReal.measurable.pow_const _)).mul
      ((Complex.continuous_ofReal.measurable.comp Real.measurable_log).neg.pow_const j)
  have hbound : ∀ᵐ x ∂volume.restrict (Ioi (1 : ℝ)),
      ∀ w ∈ Metric.ball z r,
        ‖G' w x‖ ≤ (1 / r) * ‖G (a : ℂ) x‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx.le
    have hnorm (v : ℂ) (j : ℕ) :
        ‖f x * (x : ℂ) ^ (-v - 1) * (-(Real.log x : ℂ)) ^ j‖ =
          ‖f x‖ * x ^ (-v.re - 1) * (Real.log x) ^ j := by
      simp only [norm_mul, norm_pow, norm_neg, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hlog]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    intro w hw
    have hwre : z.re - r < w.re := by
      have hb : ‖w - z‖ < r := by simpa [dist_eq_norm] using hw
      have hc := Complex.abs_re_le_norm (w - z)
      simp only [Complex.sub_re] at hc
      have := (abs_le.mp hc).1
      linarith
    have hbase : ‖f x‖ * x ^ (-w.re - 1) * Real.log x ≤
        (1 / r) * ‖f x‖ * x ^ (-a - 1) := by
      calc
        _ ≤ ‖f x‖ * x ^ (-w.re - 1) * (x ^ r / r) :=
          mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hx0.le hr)
            (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hx0.le _))
        _ = (1 / r) * ‖f x‖ * x ^ (-w.re - 1 + r) := by
          rw [Real.rpow_add hx0]
          ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left
          · apply Real.rpow_le_rpow_of_exponent_le hx.le
            dsimp [a]
            linarith
          · positivity
    dsimp [G, G']
    rw [hnorm, hnorm]
    simp only [Complex.ofReal_re]
    calc
      _ = (‖f x‖ * x ^ (-w.re - 1) * Real.log x) * (Real.log x) ^ k := by
        rw [pow_succ]
        ring
      _ ≤ ((1 / r) * ‖f x‖ * x ^ (-a - 1)) * (Real.log x) ^ k :=
        mul_le_mul_of_nonneg_right hbase (pow_nonneg hlog _)
      _ = _ := by ring
  have hdiff : ∀ᵐ x ∂volume.restrict (Ioi (1 : ℝ)),
      ∀ w ∈ Metric.ball z r, HasDerivAt (fun w : ℂ => G w x) (G' w x) w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro w _
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hd := ((((hasDerivAt_id w).neg.sub_const 1).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hx0.ne'))).const_mul (f x)).mul_const
        ((-(Real.log x : ℂ)) ^ k)
    convert! hd using 1
    simp [G', Complex.ofReal_log hx0.le, pow_succ]
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z hr)
    (Filter.Eventually.of_forall fun w => (hmeas w k).aestronglyMeasurable)
    (logarithmicTransform_integrable hf k hz)
    (hmeas z (k + 1)).aestronglyMeasurable hbound
    ((logarithmicTransform_integrable hf k (z := (a : ℂ)) ha).norm.const_mul (1 / r))
    hdiff).2

/-- Actual higher derivative identities on the entire energy half-plane. -/
theorem iteratedDeriv_transform_eq_logarithmicTransform {f : ℝ → ℂ} {s : ℝ}
    (hf : FiniteEnergy f s) (k : ℕ) {z : ℂ} (hz : s / 2 < z.re) :
    iteratedDeriv k (transform f) z = logarithmicTransform f k z := by
  induction k generalizing z with
  | zero => simp [iteratedDeriv_zero, logarithmicTransform, transform]
  | succ k ih =>
    have he : iteratedDeriv k (transform f) =ᶠ[𝓝 z] logarithmicTransform f k := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz]
        with w hw
      exact ih hw
    rw [iteratedDeriv_succ, he.deriv_eq]
    exact (logarithmicTransform_hasDerivAt hf k hz).deriv

/-- The exact all-order derivative estimate, now with its integral identity. -/
theorem iteratedDeriv_transform_norm_sq_le {f : ℝ → ℂ} {s : ℝ}
    (hf : FiniteEnergy f s) (k : ℕ) {z : ℂ} (hz : s / 2 < z.re) :
    ‖iteratedDeriv k (transform f) z‖ ^ 2 ≤
      energy f s * ((2 * k).factorial : ℝ) /
        (2 * z.re - s) ^ (2 * k + 1) := by
  rw [iteratedDeriv_transform_eq_logarithmicTransform hf k hz]
  exact logarithmicTransform_norm_sq_le hf k hz

/-- Uniform jet control on any strictly interior closed half-plane. The
constant is independent of the imaginary part and no zero hypothesis is used. -/
theorem iteratedDeriv_transform_norm_sq_le_of_margin {f : ℝ → ℂ} {s b : ℝ}
    (hf : FiniteEnergy f s) (k : ℕ) (hb : s / 2 < b)
    {z : ℂ} (hz : b ≤ z.re) :
    ‖iteratedDeriv k (transform f) z‖ ^ 2 ≤
      energy f s * ((2 * k).factorial : ℝ) /
        (2 * b - s) ^ (2 * k + 1) := by
  have hb0 : 0 < 2 * b - s := by linarith
  have hz0 : 0 < 2 * z.re - s := by linarith
  have hp : (2 * b - s) ^ (2 * k + 1) ≤
      (2 * z.re - s) ^ (2 * k + 1) := by
    gcongr
  have h := (le_div_iff₀ (pow_pos hz0 _)).mp
    (iteratedDeriv_transform_norm_sq_le hf k (by linarith : s / 2 < z.re))
  apply (le_div_iff₀ (pow_pos hb0 _)).mpr
  exact (mul_le_mul_of_nonneg_left hp (sq_nonneg _)).trans h

/-- The existing differentiated Mellin formula supplies the first derivative. -/
theorem deriv_transform_eq_logarithmicTransform {f : ℝ → ℂ} {s : ℝ}
    (hf : FiniteEnergy f s) {z : ℂ} (hz : s / 2 < z.re) :
    deriv (transform f) z = logarithmicTransform f 1 z := by
  rw [(transform_hasDerivAt hf hz).deriv]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  simp only [logarithmicTransform, pow_one]
  ring

theorem deriv_transform_norm_sq_le {f : ℝ → ℂ} {s : ℝ}
    (hf : FiniteEnergy f s) {z : ℂ} (hz : s / 2 < z.re) :
    ‖deriv (transform f) z‖ ^ 2 ≤ 2 * energy f s / (2 * z.re - s) ^ 3 := by
  rw [deriv_transform_eq_logarithmicTransform hf hz]
  have h := logarithmicTransform_norm_sq_le hf 1 hz
  norm_num at h
  simpa only [mul_comm] using h

end MeasureTheory.WeightedMellin
