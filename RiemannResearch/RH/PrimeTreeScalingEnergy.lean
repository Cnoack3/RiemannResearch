/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.StepCorrectionConstant
import RiemannResearch.RH.QConductorDecay
import RiemannResearch.Analysis.PositiveNaturalCellIntegral
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # The physical conductor scaling limit

The strong limit is the sampled fractional-part profile from Section 6 of
*Prime trees, fractional parts, and zeta zeros*. Its continuum energy is the
classical fractional-part autocorrelation at 1, as in Báez-Duarte,
Balazard, Landreau and Saias, Ramanujan J. 9 (2005), 215–240.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RiemannResearch.RH.PrimeTreeScalingEnergy
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative
open RiemannResearch.Analysis.PositiveNaturalCellIntegral

def sample (D : ℕ) (x : ℝ) : ℝ := (⌈(D : ℝ) * x⌉ : ℝ) / D
def profile (x : ℝ) : ℝ := Int.fract x / x
def envelope (x : ℝ) : ℝ := min 1 (1 / x)

theorem sample_bounds (D : ℕ) (hD : 0 < D) (x : ℝ) :
    x ≤ sample D x ∧ sample D x < x + 1 / (D : ℝ) := by
  have h : 0 < (D : ℝ) := by exact_mod_cast hD
  constructor
  · apply (le_div_iff₀ h).mpr
    simpa only [mul_comm x] using Int.le_ceil ((D : ℝ) * x)
  · apply (div_lt_iff₀ h).mpr
    calc
      _ < (D : ℝ) * x + 1 := Int.ceil_lt_add_one _
      _ = _ := by field_simp [h.ne'] <;> ring

theorem tendsto_sample (x : ℝ) : Tendsto (fun D : ℕ => sample D x) atTop (𝓝[≥] x) := by
  have hlo : ∀ᶠ D : ℕ in atTop, x ≤ sample D x :=
    (eventually_gt_atTop 0).mono fun D hD => (sample_bounds D hD x).1
  have hhi : ∀ᶠ D : ℕ in atTop, sample D x ≤ x + 1 / (D : ℝ) :=
    (eventually_gt_atTop 0).mono fun D hD => (sample_bounds D hD x).2.le
  have hlim : Tendsto (fun D : ℕ => x + 1 / (D : ℝ)) atTop (𝓝 x) := by
    simpa only [add_zero] using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add x
  exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim hlo hhi) hlo

theorem tendsto_sample_profile (x : ℝ) (hx : 0 < x) :
    Tendsto (fun D : ℕ => profile (sample D x)) atTop (𝓝 (profile x)) := by
  have hs := tendsto_sample x
  have hn := tendsto_nhds_of_tendsto_nhdsWithin hs
  have hfloor := tendsto_pure.mp ((tendsto_floor_right_pure_floor x).comp hs)
  have hcast : Tendsto (fun D : ℕ => (⌊sample D x⌋ : ℝ)) atTop (𝓝 (⌊x⌋ : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hfloor] with D hD
    change ⌊sample D x⌋ = ⌊x⌋ at hD
    rw [hD]
  exact (hn.sub hcast).div hn hx.ne'

private theorem measurable_profile : Measurable profile :=
  measurable_fract.div measurable_id

theorem measurable_sample (D : ℕ) : Measurable (sample D) := by
  unfold sample
  fun_prop

private theorem profile_bounds {y x : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    0 ≤ profile y ∧ profile y ≤ envelope x := by
  have hy : 0 < y := hx.trans_le hxy
  have hf : (0 : ℝ) ≤ (⌊y⌋ : ℝ) := by exact_mod_cast Int.floor_nonneg.mpr hy.le
  refine ⟨div_nonneg (Int.fract_nonneg _) hy.le, le_min ?_ ?_⟩
  · apply (div_le_iff₀ hy).mpr
    unfold Int.fract
    linarith
  · exact (div_le_div_of_nonneg_right (Int.fract_lt_one _).le hy.le).trans
      (one_div_le_one_div_of_le hx hxy)

private theorem sample_profile_bounds (D : ℕ) (x : ℝ) (hx : 0 < x) :
    0 ≤ profile (sample D x) ∧ profile (sample D x) ≤ envelope x := by
  by_cases hD : D = 0
  · subst D
    simp [sample, profile, envelope, hx.le]
  · exact profile_bounds hx (sample_bounds D (Nat.pos_of_ne_zero hD) x).1

theorem integrable_envelope_sq :
    IntegrableOn (fun x : ℝ => envelope x ^ 2) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num), integrableOn_union]
  constructor
  · have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (0 : ℝ) 1) :=
      integrableOn_const (by simp [Real.volume_Ioc])
    apply hi.congr_fun _ measurableSet_Ioc
    intro x hx
    have he : (1 : ℝ) ≤ 1 / x := (le_div_iff₀ hx.1).mpr (by simpa using hx.2)
    change 1 = min 1 (1 / x) ^ 2
    rw [min_eq_left he, one_pow]
  · have hi := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) zero_lt_one
    apply hi.congr_fun _ measurableSet_Ioi
    intro x hx
    have he : 1 / x ≤ (1 : ℝ) := (div_le_iff₀ (zero_lt_one.trans hx)).mpr
      (by simpa using (le_of_lt hx))
    change x ^ (-2 : ℝ) = min 1 (1 / x) ^ 2
    rw [min_eq_right he, Real.rpow_neg (zero_lt_one.trans hx).le, Real.rpow_two]
    ring

/-- Mean-square form of the strong convergence in (22), on the full positive ray. -/
theorem tendsto_profile_error_energy :
    Tendsto (fun D : ℕ => ∫ x in Ioi (0 : ℝ), (profile (sample D x) - profile x) ^ 2)
      atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioi (0 : ℝ)))
    (fun x : ℝ => envelope x ^ 2)
    (F := fun D : ℕ => fun x : ℝ => (profile (sample D x) - profile x) ^ 2)
    (f := fun _ : ℝ => (0 : ℝ))
    (fun D => (((measurable_profile.comp (measurable_sample D)).sub
      measurable_profile).pow_const 2).aestronglyMeasurable) integrable_envelope_sq
  suffices ht : Tendsto
      (fun D : ℕ => ∫ x in Ioi (0 : ℝ), (profile (sample D x) - profile x) ^ 2)
      atTop (𝓝 (∫ _x in Ioi (0 : ℝ), (0 : ℝ))) by
    simpa only [integral_zero] using ht
  apply h
  · intro D
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    obtain ⟨hn, hb⟩ := sample_profile_bounds D x hx
    obtain ⟨hn', hb'⟩ := profile_bounds hx (le_refl x)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    apply sq_le_sq' <;> linarith
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simpa using ((tendsto_sample_profile x hx).sub_const (profile x)).pow 2

/-- The actual continuum energy limit from (23), with its evaluated constant. -/
theorem tendsto_sample_energy :
    Tendsto (fun D : ℕ => ∫ x in Ioi (0 : ℝ), (profile (sample D x)) ^ 2)
      atTop (𝓝 (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant)) := by
  have h :=
    tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioi (0 : ℝ)))
      (fun x : ℝ => envelope x ^ 2)
      (F := fun D : ℕ => fun x : ℝ => (profile (sample D x)) ^ 2)
      (f := fun x : ℝ => profile x ^ 2)
      (fun D => ((measurable_profile.comp (measurable_sample D)).pow_const 2).aestronglyMeasurable)
      integrable_envelope_sq
  have he : (∫ x in Ioi (0 : ℝ), profile x ^ 2) =
      Real.log (2 * Real.pi) - Real.eulerMascheroniConstant := by
    simpa only [profile, div_pow] using StepCorrectionNorm.fract_energy_eq_log_two_pi_sub_gamma
  rw [← he]
  apply h
  · intro D
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    obtain ⟨hn, hb⟩ := sample_profile_bounds D x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ hn hb _
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (tendsto_sample_profile x hx).pow 2

/-- The exact partition into scaled physical cells, including the first cell. -/
theorem integral_sample_energy (D : ℕ) (hD : 0 < D) :
    (∫ x in Ioi (0 : ℝ), (profile (sample D x)) ^ 2) =
      zetaTwo * (D : ℝ) * ‖qResidue D‖ ^ 2 := by
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  let g (u : ℝ) := (profile ((⌈u⌉ : ℝ) / D)) ^ 2
  have hscaled : IntegrableOn (fun x : ℝ => g ((D : ℝ) * x)) (Ioi 0) := by
    change IntegrableOn (fun x : ℝ => (profile (sample D x)) ^ 2) (Ioi 0)
    apply integrable_envelope_sq.mono'
      ((measurable_profile.comp (measurable_sample D)).pow_const 2).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    obtain ⟨hn, hb⟩ := sample_profile_bounds D x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ hn hb _
  have hi : IntegrableOn g (Ioi 0) := by
    simpa only [mul_zero] using (integrableOn_Ioi_comp_mul_left_iff g 0 hDr).mp hscaled
  have hcell (n : ℕ) :
      (∫ x in Ioc (0 + (n : ℝ)) (0 + (n : ℝ) + 1), g x) =
        ((D : ℝ) ^ 2 * zetaTwo) *
          (positiveQWeight (n + 1) * (residueFraction D (n + 1)) ^ 2) := by
    simp only [zero_add]
    calc
      _ = ∫ _x in Ioc (n : ℝ) ((n : ℝ) + 1),
          (profile ((((n + 1 : ℕ) : ℝ)) / D)) ^ 2 := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x hx
        have hceil : ⌈x⌉ = ((n + 1 : ℕ) : ℤ) := by
          apply Int.ceil_eq_iff.mpr
          constructor
          · simpa using hx.1
          · simpa using hx.2
        dsimp only [g]
        rw [hceil, Int.cast_natCast]
      _ = _ := by
        rw [setIntegral_const, Real.volume_real_Ioc_of_le (by linarith),
          add_sub_cancel_left, one_smul, profile, Int.fract_div_natCast_eq_div_natCast_mod]
        simp only [positiveQWeight, residueFraction]
        have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp [hDr.ne', zetaTwo_pos.ne', hn]
        <;> ring
  have hq : (∑' n : ℕ, positiveQWeight (n + 1) * (residueFraction D (n + 1)) ^ 2) =
      ‖qResidue D‖ ^ 2 := by
    rw [qNorm_weighted_sq, (qSequence_square_summable (qResidue D)).tsum_eq_zero_add]
    simp only [qSequence_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add,
      qSequence_qResidue]
  have hcells := (hasSum_integral_Ioi_cells 0 hi).tsum_eq.symm
  simp_rw [hcell] at hcells
  rw [tsum_mul_left, hq] at hcells
  change (∫ x in Ioi (0 : ℝ), g ((D : ℝ) * x)) = _
  rw [integral_comp_mul_left_Ioi g 0 hDr, mul_zero, smul_eq_mul, hcells]
  field_simp [hDr.ne']
  <;> ring

/-- The complete discrete limit in (23). No particular sequence of prime
conductors or arithmetic restrictions enters the argument. -/
theorem tendsto_conductor_energy :
    Tendsto (fun D : ℕ => (D : ℝ) * ‖qResidue D‖ ^ 2) atTop
      (𝓝 ((Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / zetaTwo)) := by
  apply (tendsto_sample_energy.div_const zetaTwo).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with D hD
  rw [integral_sample_energy D hD]
  field_simp [zetaTwo_pos.ne']

end RiemannResearch.RH.PrimeTreeScalingEnergy
