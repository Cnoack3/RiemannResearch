import RiemannResearch.Analysis.MontgomeryMacroscopicGapModel
import RiemannResearch.Analysis.MontgomeryScaledHeightTests

/-! # Logarithmic terms of the actual macroscopic positive-gap law -/

noncomputable section
open Filter Set
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryPositiveGap

/-- A single absolute error of order 1/T holds for all macroscopic widths
after subtracting both explicit logarithmic corrections. -/
theorem eventually_macroscopic_gap_quadratic_expansion :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ c ∈ Icc (0:ℝ) 1,
      |positiveGapMass T (c*unfoldedCutoff T)/unfoldedCutoff T -
        ((c-c^2/2)+macroscopicGapSecondCoefficient c/Real.log T +
          macroscopicGapThirdCoefficient c/(Real.log T)^2)| ≤ C/T := by
  obtain ⟨C,hC,hm⟩ := eventually_macroscopic_gap_density_model
  refine ⟨C,hC,?_⟩
  filter_upwards [hm] with T hT c hc
  have h := hT c hc.1
  rwa [macroscopicGapDensityModel_eq_from_second_term hc eventually_macroscopic_gap_density_model
    (macroscopic_gap_second_term hc)] at h

/-- After subtracting the triangular law and its first logarithmic
correction, the actual positive gaps have the second logarithmic coefficient. -/
theorem macroscopic_gap_third_term {c : ℝ} (hc : c ∈ Icc (0:ℝ) 1) :
    Tendsto (fun T : ℝ => (Real.log T)^2*(positiveGapMass T (c*unfoldedCutoff T)/unfoldedCutoff T -
      (c-c^2/2) - macroscopicGapSecondCoefficient c/Real.log T))
      atTop (𝓝 (macroscopicGapThirdCoefficient c)) :=
  macroscopic_gap_third_term_of_density_model hc eventually_macroscopic_gap_density_model
    (macroscopic_gap_second_term hc)

/-- The smooth quadratic density model has a universal logarithmic
correction at every sequence of positive fractions tending to zero. -/
theorem macroscopic_density_model_shrinking_drift {c : ℝ → ℝ}
    (hpos : ∀ᶠ T : ℝ in atTop, 0 < c T) (hc : Tendsto c atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => Real.log T*(macroscopicGapDensityModel (Real.log T) (c T)/c T -
      (1-c T/2))) atTop (𝓝 (-2*(1+Real.log (2*Real.pi)))) := by
  let L := Real.log
  obtain ⟨K,hK,hV⟩ := exists_abs_macroscopicGapThirdCoefficient_le
  have hquad : Tendsto (fun T : ℝ => macroscopicGapThirdCoefficient (c T)/(c T*L T))
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hu := (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul K
    simp only [mul_zero] at hu
    apply squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) _ hu
    filter_upwards [hpos,eventually_gt_atTop (1:ℝ)] with T hcT hT
    have hL := Real.log_pos hT
    rw [Real.norm_eq_abs,abs_div,abs_of_pos (mul_pos hcT hL)]
    apply (div_le_div_of_nonneg_right (hV (c T) hcT.le) (mul_pos hcT hL).le).trans_eq
    dsimp only [Function.comp_def,L]
    field_simp [hL.ne',hcT.ne']
  have h := (macroscopicGapSecondCoefficient_div_tendsto hpos hc).add hquad
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [hpos,hc.eventually_lt_const zero_lt_one,eventually_gt_atTop (1:ℝ)] with T hcT hcT₁ hT
  have hI : c T ∈ Icc (0:ℝ) 1 := ⟨hcT.le,hcT₁.le⟩
  change macroscopicGapSecondCoefficient (c T)/c T + macroscopicGapThirdCoefficient (c T)/(c T*L T) =
    L T*(macroscopicGapDensityModel (L T) (c T)/c T-(1-c T/2))
  rw [macroscopicGapDensityModel_eq_from_second_term hI eventually_macroscopic_gap_density_model
    (macroscopic_gap_second_term hI)]
  have hL : 0 < L T := Real.log_pos hT
  field_simp [hcT.ne',hL.ne'] <;> ring

/-- When the physical width grows faster than log T and remains o(T), the
first logarithmic correction to the proportion of positive gaps is universal
after retaining the exact clipped boundary loss. -/
theorem mesoscopic_gap_logarithmic_correction {c : ℝ → ℝ}
    (hpos : ∀ᶠ T : ℝ in atTop, 0 < c T) (hc : Tendsto c atTop (𝓝 0))
    (hwidth : Tendsto (fun T : ℝ => T*c T/Real.log T) atTop atTop) :
    Tendsto (fun T : ℝ => Real.log T*(positiveGapMass T (c T*unfoldedCutoff T) /
      (c T*unfoldedCutoff T) - (1-c T/2))) atTop (𝓝 (-2*(1+Real.log (2*Real.pi)))) := by
  let L := Real.log
  let D := unfoldedCutoff
  let P := fun T : ℝ => positiveGapMass T (c T*D T)/D T
  let M := fun T : ℝ => macroscopicGapDensityModel (L T) (c T)
  obtain ⟨C,hC,hE⟩ := eventually_macroscopic_gap_density_model
  have hres : Tendsto (fun T : ℝ => (L T/c T)*(P T-M T)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hu := (tendsto_inv_atTop_zero.comp hwidth).const_mul C
    simp only [mul_zero] at hu
    apply squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) _ hu
    filter_upwards [hpos,hE,eventually_gt_atTop (1:ℝ)] with T hcT he hT
    have hL := Real.log_pos hT
    have ht := zero_lt_one.trans hT
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (div_pos hL hcT)]
    apply (mul_le_mul_of_nonneg_left (he (c T) hcT.le) (div_pos hL hcT).le).trans_eq
    dsimp only [Function.comp_def,L]
    field_simp [hL.ne',hcT.ne',ht.ne']
  have h := hres.add (macroscopic_density_model_shrinking_drift hpos hc)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [hpos,eventually_gt_atTop (1:ℝ)] with T hcT hT
  have hD : 0 < D T := div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  change L T / c T * (P T - M T) + L T*(M T/c T-(1-c T/2)) =
    L T*(positiveGapMass T (c T*D T)/(c T*D T)-(1-c T/2))
  dsimp only [P]
  field_simp [hcT.ne',hD.ne'] <;> ring

/-- In unfolded units the logarithmic correction applies whenever the
width exceeds (log T)² by a factor tending to infinity and occupies a
vanishing fraction of the full cutoff. -/
theorem positiveGapMass_mesoscopic_second_term {R : ℝ → ℝ}
    (hR : Tendsto (fun T : ℝ => R T/(Real.log T)^2) atTop atTop)
    (hscale : Tendsto (fun T : ℝ => R T/unfoldedCutoff T) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => Real.log T*(positiveGapMass T (R T)/R T -
      (1-R T/(2*unfoldedCutoff T)))) atTop (𝓝 (-2*(1+Real.log (2*Real.pi)))) := by
  let c := fun T : ℝ => R T/unfoldedCutoff T
  have hpos : ∀ᶠ T : ℝ in atTop, 0 < c T := by
    filter_upwards [hR.eventually_gt_atTop 0,eventually_gt_atTop (1:ℝ)] with T hr hT
    have hL := Real.log_pos hT
    have hD : 0 < unfoldedCutoff T := div_pos (mul_pos (zero_lt_one.trans hT) hL) (by positivity)
    have hR₀ := (lt_div_iff₀ (sq_pos_of_pos hL)).mp hr
    exact div_pos (by simpa only [zero_mul] using hR₀) hD
  have hwidth : Tendsto (fun T : ℝ => T*c T/Real.log T) atTop atTop := by
    apply (hR.const_mul_atTop (show 0 < 2*Real.pi by positivity)).congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
    dsimp only [c,unfoldedCutoff]
    field_simp [Real.pi_ne_zero,(Real.log_pos hT).ne',(zero_lt_one.trans hT).ne'] <;> ring
  apply (mesoscopic_gap_logarithmic_correction hpos hscale hwidth).congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
  have hD : 0 < unfoldedCutoff T := div_pos
    (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  dsimp only [c]
  rw [div_mul_cancel₀ _ hD.ne']
  ring

end RiemannResearch.Analysis.MontgomeryPositiveGap

namespace RiemannResearch.Analysis.MontgomeryPositiveGap

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.positiveGapMass_mesoscopic_second_term' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms positiveGapMass_mesoscopic_second_term

end RiemannResearch.Analysis.MontgomeryPositiveGap

namespace RiemannResearch.Analysis.MontgomeryPositiveGap

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.eventually_macroscopic_gap_quadratic_expansion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_macroscopic_gap_quadratic_expansion

end RiemannResearch.Analysis.MontgomeryPositiveGap
