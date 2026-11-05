/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.PrimeTreeFractionalMellin
import RiemannResearch.RH.PrimeTreeScalingEnergy
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Polarization with fixed complex coefficients
This module treats the finite continuum packet in equation (26) of the
prime-tree paper. The identity between its Mellin transform and the product of
the zeta transform with the finite polynomial uses absolute convergence
on the entire open critical strip. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace RiemannResearch.RH.PrimeTreeScalingEnergy
open PrimeTreeMellinLaws ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative
variable {ι : Type*} [Fintype ι]

def packet (a : ι → ℕ) (v : ι → ℂ) (y : ℝ) : ℂ :=
  ∑ j, v j * ((Int.fract (y / (a j : ℝ)) : ℝ) : ℂ)

def packetProfile (a : ι → ℕ) (v : ι → ℂ) (y : ℝ) : ℂ := packet a v y / (y : ℂ)

private theorem dilated_fract_mellin (a : ℕ) (ha : 0 < a) (s : ℂ) :
    mellin (fun y : ℝ => ((Int.fract (y / (a : ℝ)) : ℝ) : ℂ)) (-s) =
      (a : ℂ) ^ (-s) * mellin (fun y : ℝ => ((Int.fract y : ℝ) : ℂ)) (-s) := by
  have har : 0 < (a : ℝ) := by exact_mod_cast ha
  have h := mellin_comp_mul_left (fun y : ℝ => ((Int.fract y : ℝ) : ℂ)) (-s)
    (inv_pos.mpr har)
  rw [neg_neg, smul_eq_mul, Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg har.le,
    Complex.ofReal_natCast, ← Complex.cpow_neg] at h
  simpa only [div_eq_inv_mul] using h

theorem packet_mellin_convergent (a : ι → ℕ) (ha : ∀ j, 0 < a j) (v : ι → ℂ)
    (s : ℂ) (hpos : 0 < s.re) (hlt : s.re < 1) :
    MellinConvergent (packet a v) (-s) := by
  classical
  unfold MellinConvergent packet
  simp only [smul_eq_mul, Finset.mul_sum]
  apply integrable_finsetSum
  intro j _
  have hr : 0 < (a j : ℝ) := by exact_mod_cast ha j
  have hi := (MellinConvergent.comp_mul_left (inv_pos.mpr hr)).mpr
    (fract_mellin_convergent s hpos hlt)
  simpa only [MellinConvergent, IntegrableOn, smul_eq_mul, div_eq_inv_mul] using hi.const_smul (v j)

theorem mellin_packet (a : ι → ℕ) (ha : ∀ j, 0 < a j) (v : ι → ℂ)
    (s : ℂ) (hpos : 0 < s.re) (hlt : s.re < 1) :
    mellin (packet a v) (-s) =
      (-riemannZeta s / s) * ∑ j, v j * (a j : ℂ) ^ (-s) := by
  classical
  let f (j : ι) (y : ℝ) := ((Int.fract (y / (a j : ℝ)) : ℝ) : ℂ)
  have hterm (j : ι) : MellinConvergent (f j) (-s) := by
    have hr : 0 < (a j : ℝ) := by exact_mod_cast ha j
    have h := (MellinConvergent.comp_mul_left (inv_pos.mpr hr)).mpr
      (fract_mellin_convergent s hpos hlt)
    simpa only [f, div_eq_inv_mul] using h
  calc
    _ = ∫ y in Ioi (0 : ℝ), ∑ j, (y : ℂ) ^ (-s - 1) • (v j • f j y) := by
      simp only [mellin, packet, f, smul_eq_mul, Finset.mul_sum]
    _ = ∑ j, mellin (fun y => v j • f j y) (-s) := by
      exact integral_finsetSum _ (fun j _ => (hterm j).const_smul (v j))
    _ = _ := by
      simp_rw [mellin_const_smul, f, dilated_fract_mellin _ (ha _) s, mellin_fract_zeta s hpos hlt,
        smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem packet_measurable (a : ι → ℕ) (v : ι → ℂ) : Measurable (packet a v) := by
  classical
  unfold packet
  apply Finset.measurable_sum
  intro j _
  exact measurable_const.mul
    (Complex.measurable_ofReal.comp (measurable_fract.comp (measurable_id.div_const _)))

theorem packet_bound (a : ι → ℕ) (ha : ∀ j, 0 < a j) (v : ι → ℂ) {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) :
    ‖packetProfile a v y‖ ≤ (∑ j, ‖v j‖) * envelope x := by
  classical
  have hy := hx.trans_le hxy
  rw [packetProfile, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
  rw [packet, Finset.sum_mul]
  apply (div_le_div_of_nonneg_right (norm_sum_le _ _) hy.le).trans
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro j _
  have hAj : 1 ≤ (a j : ℝ) := by exact_mod_cast ha j
  have hAn := zero_lt_one.trans_le hAj
  have hf0 := Int.fract_nonneg (y / (a j : ℝ))
  have hy0 := div_nonneg hy.le hAn.le
  have hfl : (0 : ℝ) ≤ (⌊y / (a j : ℝ)⌋ : ℝ) := by exact_mod_cast Int.floor_nonneg.mpr hy0
  have hf : Int.fract (y / (a j : ℝ)) / y ≤ envelope x := by
    apply le_min
    · apply (div_le_iff₀ hy).mpr
      have hb : y / (a j : ℝ) ≤ y := div_le_self hy.le hAj
      unfold Int.fract
      linarith
    · exact (div_le_div_of_nonneg_right (Int.fract_lt_one _).le hy.le).trans
        (one_div_le_one_div_of_le hx hxy)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hf0, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hf (norm_nonneg _)

theorem packet_sample_tendsto (a : ι → ℕ) (ha : ∀ j, 0 < a j) (v : ι → ℂ)
    (x : ℝ) (hx : 0 < x) :
    Tendsto (fun D : ℕ => packetProfile a v (sample D x)) atTop (𝓝 (packetProfile a v x)) := by
  classical
  let u (D : ℕ) := sample D x
  have hu := tendsto_sample x
  have hur := tendsto_nhds_of_tendsto_nhdsWithin hu
  have hnum : Tendsto (fun D : ℕ => packet a v (u D)) atTop (𝓝 (packet a v x)) := by
    apply tendsto_finsetSum
    intro j _
    have hAj : 0 < (a j : ℝ) := by exact_mod_cast ha j
    have hw : Tendsto (fun D : ℕ => u D / (a j : ℝ)) atTop (𝓝[≥] (x / (a j : ℝ))) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (hur.div_const _)
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with D hD
      exact div_le_div_of_nonneg_right (sample_bounds D hD x).1 hAj.le
    have hfl := tendsto_pure.mp ((tendsto_floor_right_pure_floor _).comp hw)
    have hcast : Tendsto (fun D : ℕ => (⌊u D / (a j : ℝ)⌋ : ℝ)) atTop
        (𝓝 (⌊x / (a j : ℝ)⌋ : ℝ)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hfl] with D hD
      change ⌊u D / (a j : ℝ)⌋ = ⌊x / (a j : ℝ)⌋ at hD
      rw [hD]
    exact (Complex.continuous_ofReal.continuousAt.tendsto.comp
      ((hur.div_const _).sub hcast)).const_mul _
  exact hnum.div (Complex.continuous_ofReal.continuousAt.tendsto.comp hur)
    (Complex.ofReal_ne_zero.mpr hx.ne')

theorem packetProfile_integrable_sq (a : ι → ℕ) (ha : ∀ j, 0 < a j) (v : ι → ℂ) :
    IntegrableOn (fun x : ℝ => ‖packetProfile a v x‖ ^ 2) (Ioi 0) := by
  apply (integrable_envelope_sq.const_mul ((∑ j, ‖v j‖) ^ 2)).mono'
    (((packet_measurable a v).div Complex.measurable_ofReal).norm.pow_const 2).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_of_nonneg (sq_nonneg _), ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (packet_bound a ha v hx (le_refl _)) _

private theorem packet_sample_bound (D : ℕ) (a : ι → ℕ) (ha : ∀ j, 0 < a j)
    (v : ι → ℂ) (x : ℝ) (hx : 0 < x) :
    ‖packetProfile a v (sample D x)‖ ^ 2 ≤ (∑ j, ‖v j‖) ^ 2 * envelope x ^ 2 := by
  rw [← mul_pow]
  by_cases hd : D = 0
  · subst D
    simp only [sample, Nat.cast_zero, zero_mul, div_zero, packetProfile, Complex.ofReal_zero,
      norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg _
  · exact pow_le_pow_left₀ (norm_nonneg _) (packet_bound a ha v hx
      (sample_bounds D (Nat.pos_of_ne_zero hd) x).1) _

private theorem packet_sample_meas (a : ι → ℕ) (v : ι → ℂ) (D : ℕ) :
    Measurable (fun x => ‖packetProfile a v (sample D x)‖ ^ 2) := by
  have h := (packet_measurable a v).div Complex.measurable_ofReal
  exact ((h.comp (measurable_sample D)).norm).pow_const _

theorem tendsto_packet_sample_energy (a : ι → ℕ) (ha : ∀ j, 0 < a j) (v : ι → ℂ) :
    Tendsto (fun D : ℕ => ∫ x in Ioi (0 : ℝ), ‖packetProfile a v (sample D x)‖ ^ 2)
      atTop (𝓝 (∫ x in Ioi (0 : ℝ), ‖packetProfile a v x‖ ^ 2)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun x : ℝ => (∑ j, ‖v j‖) ^ 2 * envelope x ^ 2)
    (fun D => (packet_sample_meas a v D).aestronglyMeasurable)
    (integrable_envelope_sq.const_mul _)
  · intro D
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact packet_sample_bound D a ha v x hx
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (packet_sample_tendsto a ha v x hx).norm.pow 2

/-- The complete complex Q norm square, in positive site coordinates. -/
def packetQEnergy (D : ℕ) (a : ι → ℕ) (v : ι → ℂ) : ℝ :=
  ∑' n : ℕ, positiveQWeight (n + 1) *
    ‖∑ j, v j * (residueFraction (a j * D) (n + 1) : ℂ)‖ ^ 2

theorem integral_packet_sample (D : ℕ) (hD : 0 < D) (a : ι → ℕ) (ha : ∀ j, 0 < a j)
    (v : ι → ℂ) :
    (∫ x in Ioi (0 : ℝ), ‖packetProfile a v (sample D x)‖ ^ 2) =
      zetaTwo * (D : ℝ) * packetQEnergy D a v := by
  classical
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  let g (u : ℝ) := ‖packetProfile a v ((⌈u⌉ : ℝ) / D)‖ ^ 2
  have hscaled : IntegrableOn (fun x : ℝ => g ((D : ℝ) * x)) (Ioi 0) := by
    apply (integrable_envelope_sq.const_mul ((∑ j, ‖v j‖) ^ 2)).mono'
      (packet_sample_meas a v D).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact packet_sample_bound D a ha v x hx
  have hi : IntegrableOn g (Ioi 0) := by
    simpa only [mul_zero] using (integrableOn_Ioi_comp_mul_left_iff g 0 hDr).mp hscaled
  have hcell (n : ℕ) :
      (∫ x in Ioc (0 + (n : ℝ)) (0 + (n : ℝ) + 1), g x) =
        ((D : ℝ) ^ 2 * zetaTwo) * (positiveQWeight (n + 1) *
          ‖∑ j, v j * (residueFraction (a j * D) (n + 1) : ℂ)‖ ^ 2) := by
    simp only [zero_add]
    calc
      _ = ∫ _x in Ioc (n : ℝ) ((n : ℝ) + 1),
          ‖packetProfile a v (((n + 1 : ℕ) : ℝ) / D)‖ ^ 2 := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x hx
        have he : ⌈x⌉ = ((n + 1 : ℕ) : ℤ) := by
          apply Int.ceil_eq_iff.mpr
          constructor
          · simpa using hx.1
          · simpa using hx.2
        dsimp only [g]
        rw [he, Int.cast_natCast]
      _ = _ := by
        rw [setIntegral_const, Real.volume_real_Ioc_of_le (by linarith), add_sub_cancel_left,
          one_smul, packetProfile, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hDr.le)]
        have hv : packet a v (((n + 1 : ℕ) : ℝ) / D) =
            ∑ j, v j * (residueFraction (a j * D) (n + 1) : ℂ) := by
          apply Finset.sum_congr rfl
          intro j _
          have e : (((n + 1 : ℕ) : ℝ) / D) / (a j : ℝ) =
              ((n + 1 : ℕ) : ℝ) / ((a j * D : ℕ) : ℝ) := by rw [div_div, Nat.cast_mul, mul_comm]
          rw [e, Int.fract_div_natCast_eq_div_natCast_mod]
          rfl
        rw [hv, positiveQWeight, div_pow, div_pow]
        have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp [hDr.ne', zetaTwo_pos.ne', hn]
        <;> ring
  have hcells := (RiemannResearch.Analysis.PositiveNaturalCellIntegral.hasSum_integral_Ioi_cells 0 hi).tsum_eq.symm
  simp_rw [hcell] at hcells
  rw [tsum_mul_left] at hcells
  change (∫ x in Ioi (0 : ℝ), g ((D : ℝ) * x)) = _
  rw [integral_comp_mul_left_Ioi g 0 hDr, mul_zero, smul_eq_mul, hcells, packetQEnergy]
  field_simp [hDr.ne']
  <;> ring

theorem tendsto_packetQEnergy (a : ι → ℕ) (ha : ∀ j, 0 < a j) (v : ι → ℂ) :
    Tendsto (fun D : ℕ => (D : ℝ) * packetQEnergy D a v) atTop
      (𝓝 ((∫ x in Ioi (0 : ℝ), ‖packetProfile a v x‖ ^ 2) / zetaTwo)) := by
  apply ((tendsto_packet_sample_energy a ha v).div_const zetaTwo).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with D hD
  rw [integral_packet_sample D hD a ha v]
  field_simp [zetaTwo_pos.ne']

end RiemannResearch.RH.PrimeTreeScalingEnergy
