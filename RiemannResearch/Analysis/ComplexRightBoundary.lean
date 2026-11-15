import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
/-!
# Signed right-boundary integrals from horizontal exponential decay

Source: the user-provided normalized Littlewood continuation (15 November 2026)
asks for endpoint-independent signed cancellation. This proof uses Mathlib's
Cauchy--Goursat theorem on finite rectangles and horizontal exponential decay.
The exact rectangle identity is retained before passing to the estimate.
The concrete consumer is the actual nonstandard Conrey--Baluyot mollifier.
No Dirichlet-series expansion or interchange with an infinite series is assumed.
-/

open Complex MeasureTheory Set Filter
open scoped Topology
noncomputable section

namespace Complex
/-- Exact exponential majorant integral, with both endpoints. -/
theorem right_decay_integral_exp {a C b R : ℝ} (ha : 0 < a) :
    (∫ x in b..R, C * Real.exp (-a * x)) =
      C / a * (Real.exp (-a * b) - Real.exp (-a * R)) := by
  have hd (x : ℝ) : HasDerivAt (fun u : ℝ => -(C / a) * Real.exp (-a * u))
      (C * Real.exp (-a * x)) x := by
    have h := (((hasDerivAt_id x).const_mul (-a)).exp.const_mul (-(C / a)))
    have he : -(C / a) * (Real.exp (-a * x) * (-a * 1)) = C * Real.exp (-a * x) := by
      field_simp [ha.ne']
    simpa only [id_eq, he] using h
  have hi : IntervalIntegrable (fun x : ℝ => C * Real.exp (-a * x)) volume b R :=
    (by fun_prop : Continuous (fun x : ℝ => C * Real.exp (-a * x))).intervalIntegrable b R
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hi
  rw [h]
  ring

theorem norm_horizontal_integral_le_exp {f : ℂ → ℂ} {a C b R : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C) (hR : b ≤ R)
    (hd : ∀ z : ℂ, b ≤ z.re → DifferentiableAt ℂ f z)
    (hb : ∀ z : ℂ, b ≤ z.re → ‖f z‖ ≤ C * Real.exp (-a * z.re))
    (t : ℝ) :
    ‖∫ x in b..R, f ((x : ℂ) + t * I)‖ ≤ C / a * Real.exp (-a * b) := by
  have hc : ContinuousOn (fun x : ℝ => f ((x : ℂ) + t * I)) (Icc b R) := by
    intro x hx
    exact ((hd _ (by simpa using hx.1)).continuousAt.comp
      (by fun_prop : ContinuousAt (fun x : ℝ => (x : ℂ) + t * I) x)).continuousWithinAt
  calc
    _ ≤ ∫ x in b..R, ‖f ((x : ℂ) + t * I)‖ :=
      intervalIntegral.norm_integral_le_integral_norm hR
    _ ≤ ∫ x in b..R, C * Real.exp (-a * x) := by
      apply intervalIntegral.integral_mono_on hR
        ((show ContinuousOn (fun x : ℝ => ‖f ((x : ℂ) + t * I)‖) (uIcc b R) from by
          simpa only [uIcc_of_le hR] using hc.norm).intervalIntegrable)
        ((by fun_prop : Continuous (fun x : ℝ => C * Real.exp (-a * x))).intervalIntegrable b R)
      intro x hx
      simpa using hb ((x : ℂ) + t * I) (by simpa using hx.1)
    _ = C / a * (Real.exp (-a * b) - Real.exp (-a * R)) :=
      right_decay_integral_exp ha
    _ ≤ C / a * Real.exp (-a * b) := by
      nlinarith [mul_nonneg (div_nonneg hC ha.le) (Real.exp_pos (-a * R)).le]

/-- Exact finite contour shift, retaining the remote vertical remainder. -/
theorem integral_vertical_rectangle_identity {f : ℂ → ℂ} {b R : ℝ}
    (hR : b ≤ R) (hd : ∀ z : ℂ, b ≤ z.re → DifferentiableAt ℂ f z)
    (u v : ℝ) :
    I * (∫ t in u..v, f ((b : ℂ) + t * I)) =
      (∫ x in b..R, f ((x : ℂ) + u * I)) -
      (∫ x in b..R, f ((x : ℂ) + v * I)) +
      I * (∫ t in u..v, f ((R : ℂ) + t * I)) := by
  have hh := integral_boundary_rect_eq_zero_of_differentiableOn f
    ((b : ℂ) + u * I) ((R : ℂ) + v * I) (by
      intro z hz
      apply (hd z ?_).differentiableWithinAt
      have hz' := (mem_reProdIm.mp hz).1
      have hz'' : z.re ∈ uIcc b R := by simpa using hz'
      rw [uIcc_of_le hR] at hz''
      exact hz''.1)
  have hh' : (∫ x in b..R, f ((x : ℂ) + u * I)) -
      (∫ x in b..R, f ((x : ℂ) + v * I)) +
      I * (∫ t in u..v, f ((R : ℂ) + t * I)) -
      I * (∫ t in u..v, f ((b : ℂ) + t * I)) = 0 := by
    simpa [smul_eq_mul] using hh
  exact (sub_eq_zero.mp hh').symm

/-- Horizontal exponential decay and holomorphy imply cancellation on every
finite vertical interval, uniformly in both endpoints and their order. -/
theorem norm_integral_vertical_le_of_exp_decay {f : ℂ → ℂ} {a C b : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C)
    (hd : ∀ z : ℂ, b ≤ z.re → DifferentiableAt ℂ f z)
    (hb : ∀ z : ℂ, b ≤ z.re → ‖f z‖ ≤ C * Real.exp (-a * z.re))
    (u v : ℝ) :
    ‖∫ t in u..v, f ((b : ℂ) + t * I)‖ ≤
      2 * (C / a * Real.exp (-a * b)) := by
  have hfinite (R : ℝ) (hR : b ≤ R) :
      ‖∫ t in u..v, f ((b : ℂ) + t * I)‖ ≤
        2 * (C / a * Real.exp (-a * b)) +
          (C * Real.exp (-a * R)) * |v - u| := by
    have hU := norm_horizontal_integral_le_exp ha hC hR hd hb u
    have hV := norm_horizontal_integral_le_exp ha hC hR hd hb v
    have hright :
        ‖∫ t in u..v, f ((R : ℂ) + t * I)‖ ≤
          (C * Real.exp (-a * R)) * |v - u| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => by
        simpa using hb ((R : ℂ) + t * I) (by simpa using hR))
    have he := congrArg norm (integral_vertical_rectangle_identity hR hd u v)
    simp only [norm_mul, norm_I, one_mul] at he
    rw [he]
    calc
      _ ≤ ‖∫ x in b..R, f ((x : ℂ) + u * I)‖ +
          ‖∫ x in b..R, f ((x : ℂ) + v * I)‖ +
          ‖∫ t in u..v, f ((R : ℂ) + t * I)‖ := by
        exact (norm_add_le _ _).trans (add_le_add
          (norm_sub_le _ _) (by simp))
      _ ≤ _ := by linarith
  have hx : Tendsto (fun R : ℝ => -a * R) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos ha)
  have he : Tendsto (fun R : ℝ => Real.exp (-a * R)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hx
  have hlim : Tendsto (fun R : ℝ => 2 * (C / a * Real.exp (-a * b)) +
      (C * Real.exp (-a * R)) * |v - u|) atTop
      (𝓝 (2 * (C / a * Real.exp (-a * b)))) := by
    simpa using ((he.const_mul C).mul_const |v - u|).const_add
      (2 * (C / a * Real.exp (-a * b)))
  exact ge_of_tendsto hlim (eventually_atTop.2 ⟨b, hfinite⟩)

/-- The principal logarithm is controlled throughout Re z >= 1/2. -/
theorem norm_log_le_two_mul_norm_sub_one {z : ℂ} (hz : 1 / 2 ≤ z.re) :
    ‖log z‖ ≤ 2 * ‖z - 1‖ := by
  let S : Set ℂ := {w | 1 / 2 ≤ w.re}
  have hconv : Convex ℝ S := by
    intro x hx y hy a b ha hb hab
    change 1 / 2 ≤ (a • x + b • y).re
    simp only [add_re]
    simp only [Algebra.smul_def]
    simp
    dsimp [S] at hx hy
    nlinarith
  have hd : ∀ w ∈ S, HasDerivWithinAt log w⁻¹ S w := by
    intro w hw
    exact (hasDerivAt_log (mem_slitPlane_iff.mpr (Or.inl (by
      dsimp [S] at hw; linarith)))).hasDerivWithinAt
  have hn : ∀ w ∈ S, ‖w⁻¹‖ ≤ (2 : ℝ) := by
    intro w hw
    have hnorm : 1 / 2 ≤ ‖w‖ := le_trans hw (re_le_norm w)
    rw [norm_inv, inv_eq_one_div]
    exact (div_le_iff₀ (by linarith : 0 < ‖w‖)).2 (by linarith)
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hn hconv
    (show (1 : ℂ) ∈ S by norm_num [S]) (show z ∈ S from hz)
  simpa using hh


theorem norm_integral_log_vertical_le_of_exp_decay
    {f : ℂ → ℂ} {a C b : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (hd : ∀ z : ℂ, b ≤ z.re → DifferentiableAt ℂ f z)
    (hr : ∀ z : ℂ, b ≤ z.re → 1 / 2 ≤ (f z).re)
    (hb : ∀ z : ℂ, b ≤ z.re → ‖f z - 1‖ ≤ C * Real.exp (-a * z.re))
    (u v : ℝ) :
    ‖∫ t in u..v, log (f ((b : ℂ) + t * I))‖ ≤
      4 * (C / a * Real.exp (-a * b)) := by
  have hdlog : ∀ z : ℂ, b ≤ z.re → DifferentiableAt ℂ (fun z => log (f z)) z := by
    intro z hz
    exact (differentiableAt_log (mem_slitPlane_iff.mpr (Or.inl (by
      have hh := hr z hz; linarith)))).comp z (hd z hz)
  have hbLog : ∀ z : ℂ, b ≤ z.re →
      ‖log (f z)‖ ≤ (2 * C) * Real.exp (-a * z.re) := by
    intro z hz
    calc
      _ ≤ 2 * ‖f z - 1‖ := norm_log_le_two_mul_norm_sub_one (hr z hz)
      _ ≤ 2 * (C * Real.exp (-a * z.re)) := mul_le_mul_of_nonneg_left (hb z hz) (by norm_num)
      _ = _ := by ring
  convert norm_integral_vertical_le_of_exp_decay ha (by positivity : 0 ≤ 2 * C)
    hdlog hbLog u v using 1 <;> ring

theorem abs_integral_log_norm_vertical_le_of_exp_decay
    {f : ℂ → ℂ} {a C b : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (hd : ∀ z : ℂ, b ≤ z.re → DifferentiableAt ℂ f z)
    (hr : ∀ z : ℂ, b ≤ z.re → 1 / 2 ≤ (f z).re)
    (hb : ∀ z : ℂ, b ≤ z.re → ‖f z - 1‖ ≤ C * Real.exp (-a * z.re))
    (u v : ℝ) :
    |∫ t in u..v, Real.log ‖f ((b : ℂ) + t * I)‖| ≤
      4 * (C / a * Real.exp (-a * b)) := by
  have hc : Continuous (fun t : ℝ => log (f ((b : ℂ) + t * I))) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ((differentiableAt_log (mem_slitPlane_iff.mpr (Or.inl (by
      have hh := hr ((b : ℂ) + t * I) (by simp); linarith)))).continuousAt.comp
        (hd _ (by simp)).continuousAt).comp (by fun_prop)
  have he : (∫ t in u..v, Real.log ‖f ((b : ℂ) + t * I)‖) =
      (∫ t in u..v, log (f ((b : ℂ) + t * I))).re := by
    have hh := intervalIntegral.intervalIntegral_re (μ := volume) (hc.intervalIntegrable u v)
    change (∫ t in u..v, (log (f ((b : ℂ) + t * I))).re) =
      (∫ t in u..v, log (f ((b : ℂ) + t * I))).re at hh
    simpa only [Complex.log_re] using hh
  rw [he]
  exact (abs_re_le_norm _).trans
    (norm_integral_log_vertical_le_of_exp_decay ha hC hd hr hb u v)

end Complex
