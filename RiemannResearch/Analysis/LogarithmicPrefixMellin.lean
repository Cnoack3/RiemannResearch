import RiemannResearch.Analysis.WeightedMellinEnergy
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Logarithmic critical-energy prefixes give weighted Mellin membership

Source: the classical integration-by-parts argument, independently assembled
from pinned Mathlib finite-interval and improper-integral APIs.

The only arithmetic hypothesis is the explicit all-cutoff logarithmic prefix
bound. The proof converts it to weighted integrability; it does not prove the
prefix bound.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace MeasureTheory.WeightedMellin

private theorem continuousOn_rpow_Ici_one (r : ℝ) :
    ContinuousOn (fun x : ℝ => x ^ r) (Ici 1) := by
  intro x hx
  exact (Real.continuousAt_rpow_const x r
    (Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)))).continuousWithinAt

/-- A power bound on a nonnegative continuous density's primitive gives
integrability against every strictly faster decaying power. -/
theorem integrableOn_density_rpow_of_prefix_power
    (g : ℝ → ℝ) (hg : ContinuousOn g (Ici 1))
    (hg0 : ∀ x ∈ Ici 1, 0 ≤ g x)
    (D ε η : ℝ) (hD : 0 ≤ D) (hη : 0 < η) (hεη : ε < η)
    (hprefix : ∀ X : ℝ, 1 ≤ X →
      (∫ x in (1 : ℝ)..X, g x) ≤ D * X ^ ε) :
    IntegrableOn (fun x : ℝ => g x * x ^ (-η)) (Ioi 1) := by
  let E : ℝ → ℝ := fun X => ∫ x in (1 : ℝ)..X, g x
  have hE1 : E 1 = 0 := by simp [E]
  have hEderiv : ∀ x : ℝ, 1 < x → HasDerivAt E (g x) x := by
    intro x hx
    have hgint : IntervalIntegrable g volume 1 x :=
      ContinuousOn.intervalIntegrable_of_Icc hx.le (hg.mono Icc_subset_Ici_self)
    have hgm : StronglyMeasurableAtFilter g (𝓝 x) :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi
        (hg.mono Ioi_subset_Ici_self) x hx
    have hgc : ContinuousAt g x := hg.continuousAt (Ici_mem_nhds hx)
    exact intervalIntegral.integral_hasDerivAt_right hgint hgm hgc
  have hweightedcont : ContinuousOn (fun x : ℝ => g x * x ^ (-η)) (Ici 1) :=
    hg.mul (continuousOn_rpow_Ici_one (-η))
  have hbound : ∀ X : ℝ, 1 ≤ X →
      (∫ x in (1 : ℝ)..X, g x * x ^ (-η)) ≤ D + η * D / (η - ε) := by
    intro X hX
    have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
    have hden : 0 < η - ε := sub_pos.mpr hεη
    have hgint : IntervalIntegrable g volume 1 X :=
      ContinuousOn.intervalIntegrable_of_Icc hX (hg.mono Icc_subset_Ici_self)
    have hEc : ContinuousOn E [[(1 : ℝ), X]] :=
      intervalIntegral.continuousOn_primitive_interval' hgint left_mem_uIcc
    have hwc : ContinuousOn (fun x : ℝ => x ^ (-η)) [[(1 : ℝ), X]] := by
      rw [uIcc_of_le hX]
      exact (continuousOn_rpow_Ici_one (-η)).mono Icc_subset_Ici_self
    have hwpc : ContinuousOn (fun x : ℝ => -η * x ^ (-η - 1))
        [[(1 : ℝ), X]] := by
      rw [uIcc_of_le hX]
      exact continuousOn_const.mul
        ((continuousOn_rpow_Ici_one (-η - 1)).mono Icc_subset_Ici_self)
    have hwpint : IntervalIntegrable (fun x : ℝ => -η * x ^ (-η - 1))
        volume 1 X := hwpc.intervalIntegrable
    have hgwint : IntervalIntegrable (fun x : ℝ => g x * x ^ (-η))
        volume 1 X := hgint.mul_continuousOn hwc
    have hEwpint : IntervalIntegrable (fun x : ℝ => E x * (-η * x ^ (-η - 1)))
        volume 1 X := (hEc.mul hwpc).intervalIntegrable
    have hparts := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
      hEc hwc
      (fun x hx => hEderiv x (by
        have hx' : x ∈ Ioo (1 : ℝ) X := by
          simpa only [min_eq_left hX, max_eq_right hX] using hx
        exact hx'.1))
      (fun x hx => Real.hasDerivAt_rpow_const
        (p := -η) (Or.inl (ne_of_gt (by
          have hx' : x ∈ Ioo (1 : ℝ) X := by
            simpa only [min_eq_left hX, max_eq_right hX] using hx
          linarith [hx'.1]))))
      hgint hwpint
    rw [intervalIntegral.integral_add hgwint hEwpint, hE1, zero_mul, sub_zero]
      at hparts
    have hrewrite :
        (∫ x in (1 : ℝ)..X, E x * (-η * x ^ (-η - 1))) =
          -η * (∫ x in (1 : ℝ)..X, E x * x ^ (-η - 1)) := by
      rw [show (fun x : ℝ => E x * (-η * x ^ (-η - 1))) =
          (fun x : ℝ => -η * (E x * x ^ (-η - 1))) by
        funext x
        ring]
      exact intervalIntegral.integral_const_mul _ _
    rw [hrewrite] at hparts
    have hidentity :
        (∫ x in (1 : ℝ)..X, g x * x ^ (-η)) =
          E X * X ^ (-η) + η * (∫ x in (1 : ℝ)..X, E x * x ^ (-η - 1)) := by
      linarith
    have hterminal : E X * X ^ (-η) ≤ D := by
      calc
        E X * X ^ (-η) ≤ (D * X ^ ε) * X ^ (-η) :=
          mul_le_mul_of_nonneg_right (hprefix X hX) (Real.rpow_nonneg hXpos.le _)
        _ = D * X ^ (ε - η) := by
          rw [mul_assoc, ← Real.rpow_add hXpos, ← sub_eq_add_neg]
        _ ≤ D * 1 := mul_le_mul_of_nonneg_left
          (Real.rpow_le_one_of_one_le_of_nonpos hX (by linarith)) hD
        _ = D := mul_one D
    have hEpowc : ContinuousOn (fun x : ℝ => E x * x ^ (-η - 1))
        [[(1 : ℝ), X]] := by
      exact hEc.mul (by
        rw [uIcc_of_le hX]
        exact (continuousOn_rpow_Ici_one (-η - 1)).mono Icc_subset_Ici_self)
    have hcompc : ContinuousOn (fun x : ℝ => D * x ^ (ε - η - 1))
        [[(1 : ℝ), X]] := by
      exact continuousOn_const.mul (by
        rw [uIcc_of_le hX]
        exact (continuousOn_rpow_Ici_one (ε - η - 1)).mono Icc_subset_Ici_self)
    have hcompare :
        (∫ x in (1 : ℝ)..X, E x * x ^ (-η - 1)) ≤
          D * (∫ x in (1 : ℝ)..X, x ^ (ε - η - 1)) := by
      calc
        (∫ x in (1 : ℝ)..X, E x * x ^ (-η - 1)) ≤
            ∫ x in (1 : ℝ)..X, D * x ^ (ε - η - 1) := by
          apply intervalIntegral.integral_mono_on hX
            hEpowc.intervalIntegrable hcompc.intervalIntegrable
          intro x hx
          have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
          calc
            E x * x ^ (-η - 1) ≤ (D * x ^ ε) * x ^ (-η - 1) :=
              mul_le_mul_of_nonneg_right (hprefix x hx.1) (Real.rpow_nonneg hxpos.le _)
            _ = D * x ^ (ε - η - 1) := by
              rw [mul_assoc, ← Real.rpow_add hxpos,
                show ε + (-η - 1) = ε - η - 1 by ring]
        _ = D * (∫ x in (1 : ℝ)..X, x ^ (ε - η - 1)) :=
          intervalIntegral.integral_const_mul _ _
    have hpowint :
        (∫ x in (1 : ℝ)..X, x ^ (ε - η - 1)) ≤ 1 / (η - ε) := by
      have hzero : (0 : ℝ) ∉ [[(1 : ℝ), X]] := by
        rw [uIcc_of_le hX]
        simp
      rw [integral_rpow (Or.inr ⟨by linarith, hzero⟩)]
      have hsum : ε - η - 1 + 1 = ε - η := by ring
      rw [hsum, Real.one_rpow]
      have heq : (X ^ (ε - η) - 1) / (ε - η) =
          (1 - X ^ (ε - η)) / (η - ε) := by
        have hq : ε - η ≠ 0 := by linarith
        field_simp [hq, hden.ne']
        ring
      rw [heq]
      apply (div_le_div_iff_of_pos_right hden).2
      linarith [Real.rpow_nonneg hXpos.le (ε - η)]
    have hJ : (∫ x in (1 : ℝ)..X, E x * x ^ (-η - 1)) ≤ D / (η - ε) := by
      exact hcompare.trans (by
        simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hpowint hD)
    rw [hidentity]
    have hJ' := mul_le_mul_of_nonneg_left hJ hη.le
    calc
      E X * X ^ (-η) + η * (∫ x in (1 : ℝ)..X, E x * x ^ (-η - 1)) ≤
          D + η * (D / (η - ε)) := add_le_add hterminal hJ'
      _ = D + η * D / (η - ε) := by ring
  refine MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_bounded
    (b := fun X : ℝ => X) (l := atTop) (D + η * D / (η - ε)) 1
    (fun X => ?_) tendsto_id ?_
  · by_cases hX : 1 ≤ X
    · exact (ContinuousOn.intervalIntegrable_of_Icc hX
        (hweightedcont.mono Icc_subset_Ici_self)).1
    · have hX' : X ≤ 1 := le_of_not_ge hX
      simp [Ioc_eq_empty_of_le hX']
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    have hnorm : (∫ x in (1 : ℝ)..X, ‖g x * x ^ (-η)‖) =
        ∫ x in (1 : ℝ)..X, g x * x ^ (-η) := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [uIcc_of_le hX] at hx
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact mul_nonneg (hg0 x hx.1) (Real.rpow_nonneg (by linarith [hx.1]) _)
    rw [hnorm]
    exact hbound X hX

/-- An explicit all-cutoff critical energy bound supplies every H_a
membership strictly to the right of the critical line. -/
theorem finiteEnergy_of_logarithmic_prefix
    (f : ℝ → ℂ) (hfm : Measurable f) (hfc : ContinuousOn f (Ici 1))
    (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ X : ℝ, 2 ≤ X →
      (∫ x in (1 : ℝ)..X, ‖f x‖ ^ 2 * x ^ (-2 : ℝ)) ≤ C * Real.log X)
    (s : ℝ) (hs : 1 < s) : FiniteEnergy f s := by
  let g : ℝ → ℝ := fun x => ‖f x‖ ^ 2 * x ^ (-2 : ℝ)
  let η : ℝ := s - 1
  let ε : ℝ := η / 2
  let D : ℝ := C * (Real.log 2 + 1 / ε)
  have hη : 0 < η := by dsimp [η]; linarith
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεη : ε < η := by dsimp [ε]; linarith
  have hg : ContinuousOn g (Ici 1) :=
    hfc.norm.pow 2 |>.mul (continuousOn_rpow_Ici_one (-2))
  have hg0 : ∀ x ∈ Ici 1, 0 ≤ g x := by
    intro x hx
    have hx1 : 1 ≤ x := hx
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (zero_le_one.trans hx1) _)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hbound : ∀ X : ℝ, 1 ≤ X → (∫ x in (1 : ℝ)..X, g x) ≤ D * X ^ ε := by
    intro X hX
    have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
    have hlogbound : (∫ x in (1 : ℝ)..X, g x) ≤ C * (Real.log 2 + Real.log X) := by
      by_cases hX2 : 2 ≤ X
      · exact (hprefix X hX2).trans (by nlinarith [mul_nonneg hC hlog2])
      · have hX2' : X ≤ 2 := le_of_not_ge hX2
        have hgint : IntervalIntegrable g volume 1 2 :=
          ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
            (hg.mono Icc_subset_Ici_self)
        have hga : 0 ≤ᵐ[volume.restrict (Ioc (1 : ℝ) 2)] g := by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
          exact hg0 x hx.1.le
        have hmono := intervalIntegral.integral_mono_interval
          (le_refl (1 : ℝ)) hX hX2' hga hgint
        exact (hmono.trans (hprefix 2 (le_refl 2))).trans
          (by nlinarith [mul_nonneg hC hlogX])
    have hone : 1 ≤ X ^ ε := Real.one_le_rpow hX hε.le
    have hlogpow : Real.log X ≤ X ^ ε / ε :=
      Real.log_le_rpow_div (by linarith) hε
    calc
      (∫ x in (1 : ℝ)..X, g x) ≤ C * (Real.log 2 + Real.log X) := hlogbound
      _ ≤ C * (Real.log 2 + X ^ ε / ε) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [add_comm] using add_le_add_right hlogpow (Real.log 2)) hC
      _ ≤ C * ((Real.log 2 + 1 / ε) * X ^ ε) := by
        apply mul_le_mul_of_nonneg_left _ hC
        have haux := mul_le_mul_of_nonneg_left hone hlog2
        simp only [mul_one] at haux
        simp only [div_eq_mul_inv, one_mul]
        nlinarith
      _ = D * X ^ ε := by dsimp [D]; ring
  have hgi := integrableOn_density_rpow_of_prefix_power
    g hg hg0 D ε η hD hη hεη hbound
  refine ⟨hfm, hgi.congr_fun ?_ measurableSet_Ioi⟩
  intro x hx
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  dsimp [g, η]
  rw [mul_assoc, ← Real.rpow_add hxpos]
  rw [show (-2 : ℝ) + -(s - 1) = -s - 1 by ring]

end MeasureTheory.WeightedMellin
