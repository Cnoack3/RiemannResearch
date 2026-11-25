import RiemannResearch.Analysis.PoissonHaarSpecialization
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Normed.Group.AddCircle

/-!
# Extremal circle potential for the one-zero signed Poisson correction

Ford and Zaharescu, *On the distribution of imaginary parts of zeros of the
Riemann zeta function*, give the signed one-prime density. Here circle Haar
has mass one and the geodesic circle has circumference one. On each half-arc
the density changes sign just once. Subtracting a potential's value at the
crossing proves optimality without differentiating the potential.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace RiemannResearch.Analysis.DyadicZeroWasserstein
open PoissonHaar

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- With radius `r = 1 / √p`, multiply this density by `log p` on the
logarithmically rescaled dyadic probability scale. -/
def oneMinusPoisson (r : ℝ) (z : CircleSpace) : ℝ :=
  1 - (poissonKernel r z).re

private theorem continuous_oneMinusPoisson (r : ℝ) : Continuous (oneMinusPoisson r) :=
  continuous_const.sub (Complex.continuous_re.comp (poissonKernel r).continuous)

private theorem coe_circle_lipschitz : LipschitzWith 1 (fun t : ℝ => (t : CircleSpace)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  change ‖((x - y : ℝ) : CircleSpace)‖ ≤ ‖x - y‖
  exact QuotientAddGroup.norm_mk_le_norm

private theorem pullback_oneMinusPoisson {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    oneMinusPoisson r (t : CircleSpace) =
      (2 * r * (r - Real.cos (2 * Real.pi * t))) /
        (1 - 2 * r * Real.cos (2 * Real.pi * t) + r ^ 2) := by
  have hcos : (fourier 1 (t : CircleSpace)).re = Real.cos (2 * Real.pi * t) := by
    rw [fourier_coe_apply, Complex.exp_re]
    simp [Complex.mul_re, Complex.mul_im]
  have hden : 0 < 1 - 2 * r * Real.cos (2 * Real.pi * t) + r ^ 2 := by
    nlinarith [sq_pos_of_pos (sub_pos.mpr hr1),
      mul_nonneg hr (sub_nonneg.mpr (Real.cos_le_one (2 * Real.pi * t)))]
  rw [oneMinusPoisson, poissonKernel_apply_rational r hr hr1, Complex.ofReal_re, hcos]
  apply (eq_div_iff hden.ne').2
  rw [sub_mul, div_mul_cancel₀ _ hden.ne']
  ring

/-- Integration on the two half-arcs, parametrized by their distance from zero. -/
private theorem haar_eq_two_arcs (F : CircleSpace → ℝ) (hF : Continuous F) :
    (∫ z, F z ∂AddCircle.haarAddCircle) =
      (∫ t in (0 : ℝ)..1/2, F ((-t : ℝ) : CircleSpace)) +
       ∫ t in (0 : ℝ)..1/2, F (t : CircleSpace) := by
  have hc : Continuous (fun t : ℝ => F (t : CircleSpace)) := hF.comp coe_circle_lipschitz.continuous
  rw [AddCircle.integral_haarAddCircle]
  simp only [inv_one, one_smul]
  rw [← AddCircle.intervalIntegral_preimage (1 : ℝ) (-(1/2)) F]
  rw [show -(1 / 2 : ℝ) + 1 = 1/2 by norm_num,
    ← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (-(1/2)) 0) (hc.intervalIntegrable 0 (1/2))]
  congr 1
  simpa only [neg_zero] using
    (intervalIntegral.integral_comp_neg (f := fun t : ℝ => F (t : CircleSpace))
      (a := (0 : ℝ)) (b := (1/2 : ℝ))).symm

private theorem zero_half_mass {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    (∫ t in (0 : ℝ)..1/2, oneMinusPoisson r (t : CircleSpace)) = 0 := by
  have hc := (poissonKernel r).continuous
  have hi : Integrable (poissonKernel r) AddCircle.haarAddCircle := hc.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hz : (∫ z, oneMinusPoisson r z ∂AddCircle.haarAddCircle) = 0 := by
    simp only [oneMinusPoisson]
    have hir : Integrable (fun z : CircleSpace => (poissonKernel r z).re)
        AddCircle.haarAddCircle := hi.re
    have hmean : (∫ z : CircleSpace, (poissonKernel r z).re ∂AddCircle.haarAddCircle) = 1 := by
      calc
        _ = (∫ z : CircleSpace, poissonKernel r z ∂AddCircle.haarAddCircle).re := integral_re hi
        _ = 1 := by rw [poissonKernel_integral_one r hr hr1]; rfl
    rw [integral_sub (integrable_const (1:ℝ)) hir, hmean]
    simp
  have heven (t : ℝ) : oneMinusPoisson r ((-t : ℝ) : CircleSpace) =
      oneMinusPoisson r (t : CircleSpace) := by
    rw [pullback_oneMinusPoisson hr hr1 (-t), pullback_oneMinusPoisson hr hr1 t]
    simp only [mul_neg, Real.cos_neg]
  rw [haar_eq_two_arcs _ (continuous_oneMinusPoisson r)] at hz
  simp_rw [heven] at hz
  linarith

private theorem half_arc_lipschitz_max {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (F : ℝ → ℝ) (hF : LipschitzWith 1 F) :
    (∫ t in (0 : ℝ)..1/2, F t * oneMinusPoisson r (t : CircleSpace)) ≤
      ∫ t in (0 : ℝ)..1/2, t * oneMinusPoisson r (t : CircleSpace) := by
  let a := Real.arccos r / (2 * Real.pi)
  let w := fun t : ℝ => oneMinusPoisson r (t : CircleSpace)
  have hw : Continuous w := (continuous_oneMinusPoisson r).comp coe_circle_lipschitz.continuous
  have hc : 2 * Real.pi * a = Real.arccos r := by
    dsimp [a]
    field_simp [Real.pi_ne_zero]
  have hcos : Real.cos (2 * Real.pi * a) = r := by
    rw [hc, Real.cos_arccos (by linarith) hr1.le]
  have hs (t : ℝ) : |F t - F a| ≤ |t-a| := by
    simpa [Real.dist_eq] using hF.dist_le_mul t a
  have hp {t : ℝ} (ht : t ∈ Icc 0 (1/2 : ℝ)) :
      F t * w t ≤ t * w t + (F a - a) * w t := by
    have hden : 0 ≤ 1 - 2 * r * Real.cos (2 * Real.pi * t) + r^2 := by
      nlinarith [sq_nonneg (1-r),
        mul_nonneg hr (sub_nonneg.mpr (Real.cos_le_one (2 * Real.pi * t)))]
    have hπ := Real.pi_pos
    rcases le_total t a with h | h
    · have hct : r ≤ Real.cos (2 * Real.pi * t) := by
        rw [← hcos]
        apply Real.cos_le_cos_of_nonneg_of_le_pi (by nlinarith [ht.1])
        · rw [hc]
          exact Real.arccos_le_pi _
        · exact mul_le_mul_of_nonneg_left h (by positivity)
      have hwt : w t ≤ 0 := by
        dsimp [w]
        rw [pullback_oneMinusPoisson hr hr1]
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hct)) hden
      have hf := (abs_le.mp (hs t)).1
      rw [abs_of_nonpos (sub_nonpos.mpr h)] at hf
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ (F t - t) - (F a - a) by linarith) hwt]
    · have hct : Real.cos (2 * Real.pi * t) ≤ r := by
        rw [← hcos]
        apply Real.cos_le_cos_of_nonneg_of_le_pi
        · rw [hc]
          exact Real.arccos_nonneg _
        · nlinarith [mul_nonneg hπ.le (sub_nonneg.mpr ht.2)]
        · exact mul_le_mul_of_nonneg_left h (by positivity)
      have hwt : 0 ≤ w t := by
        dsimp [w]
        rw [pullback_oneMinusPoisson hr hr1]
        exact div_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hct)) hden
      have hf := (abs_le.mp (hs t)).2
      rw [abs_of_nonneg (sub_nonneg.mpr h)] at hf
      nlinarith [mul_nonpos_of_nonpos_of_nonneg (show (F t - t) - (F a - a) ≤ 0 by linarith) hwt]
  have hu := intervalIntegral.integral_mono_on (μ := volume) (show (0:ℝ) ≤ 1/2 by norm_num)
    ((hF.continuous.mul hw).intervalIntegrable _ _)
    (((continuous_id.mul hw).add (continuous_const.mul hw)).intervalIntegrable _ _)
    (fun t ht => hp ht)
  have hleft : Continuous (fun t : ℝ => t * w t) := continuous_id.mul hw
  have hright : Continuous (fun t : ℝ => (F a - a) * w t) := continuous_const.mul hw
  change (∫ t in (0 : ℝ)..1/2, F t * w t) ≤
    ∫ t in (0 : ℝ)..1/2, t * w t + (F a-a) * w t at hu
  rw [intervalIntegral.integral_add (hleft.intervalIntegrable _ _)
    (hright.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    show (∫ t in (0:ℝ)..1/2, w t) = 0 from zero_half_mass hr hr1, mul_zero, add_zero] at hu
  exact hu

/-- The periodic tent attains the signed marginal dual norm. -/
theorem abs_poisson_pairing_le_tent {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (f : CircleSpace → ℝ) (hf : LipschitzWith 1 f) :
    |∫ z, f z * oneMinusPoisson r z ∂AddCircle.haarAddCircle| ≤
      ∫ z : CircleSpace, ‖z‖ * oneMinusPoisson r z ∂AddCircle.haarAddCircle := by
  have upper (F : CircleSpace → ℝ) (hF : LipschitzWith 1 F) :
      (∫ z, F z * oneMinusPoisson r z ∂AddCircle.haarAddCircle) ≤
      ∫ z : CircleSpace, ‖z‖ * oneMinusPoisson r z ∂AddCircle.haarAddCircle := by
    have hneg : LipschitzWith 1 (fun t : ℝ => F ((-t : ℝ) : CircleSpace)) := by
      simpa only [one_mul, Function.comp_def] using
        (hF.comp coe_circle_lipschitz).comp (isometry_neg.lipschitz (α := ℝ))
    have hpos : LipschitzWith 1 (fun t : ℝ => F (t : CircleSpace)) := by
      simpa only [one_mul, Function.comp_def] using hF.comp coe_circle_lipschitz
    have heven (t : ℝ) : oneMinusPoisson r ((-t : ℝ) : CircleSpace) =
        oneMinusPoisson r (t : CircleSpace) := by
      rw [pullback_oneMinusPoisson hr hr1 (-t), pullback_oneMinusPoisson hr hr1 t]
      simp only [mul_neg, Real.cos_neg]
    have htent : (∫ t in (0:ℝ)..1/2, ‖(t : CircleSpace)‖ * oneMinusPoisson r (t : CircleSpace)) =
        ∫ t in (0:ℝ)..1/2, t * oneMinusPoisson r (t : CircleSpace) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by norm_num)] at ht
      have hn : ‖(t : CircleSpace)‖ = |t| := (AddCircle.norm_coe_eq_abs_iff 1 one_ne_zero).2
        (by simpa [abs_of_nonneg ht.1] using ht.2)
      dsimp only
      rw [hn, abs_of_nonneg ht.1]
    rw [haar_eq_two_arcs (fun z => F z * oneMinusPoisson r z) (hF.continuous.mul (continuous_oneMinusPoisson r)),
      haar_eq_two_arcs (fun z : CircleSpace => ‖z‖ * oneMinusPoisson r z) (continuous_norm.mul (continuous_oneMinusPoisson r))]
    simp_rw [heven, QuotientAddGroup.mk_neg, norm_neg, htent]
    exact add_le_add (half_arc_lipschitz_max hr hr1 _ hneg) (half_arc_lipschitz_max hr hr1 _ hpos)
  apply abs_le.mpr
  constructor
  · have h := upper (fun z => -f z) (by simpa only [one_mul, Function.comp_def] using isometry_neg.lipschitz.comp hf)
    simp only [neg_mul, integral_neg] at h
    linarith
  · exact upper f hf

end RiemannResearch.Analysis.DyadicZeroWasserstein
