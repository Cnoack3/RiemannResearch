import RiemannResearch.RH.ParetoBoundedMellinLinearity
import RiemannResearch.Analysis.CriticalBoundaryWitness
/-!
# The actual bounded Mellin integral on the critical line

Source: the user's request to complete the coefficient-mass obstruction,
28 September 2026. This elementary split at exp R uses the exact logarithmic
kernel energy and the bounded physical tail. No zeta zero is assumed here.
-/

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace RiemannResearch.RH.Pareto

theorem criticalMellinKernel_head_energy (s : ℂ) (hs : s.re = 1/2) (R : ℝ) (hR : 0 < R) :
    (∫ x in Ioc 1 (Real.exp R), ‖paretoMellinKernel s x‖^2) = R := by
  calc
    _ = ∫ x in Ioc 1 (Real.exp R), x⁻¹ := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      change ‖paretoMellinKernel s x‖^2 = x⁻¹
      rw [paretoMellinKernel_norm_sq s (zero_lt_one.trans hx.1), hs]
      norm_num [Real.rpow_neg_one]
    _ = R := RiemannResearch.Analysis.CriticalBoundaryWitness.inverse_integral R hR

theorem criticalMellin_head_norm_le (f : ThresholdHilbert) (s : ℂ)
    (hs : s.re = 1/2) (R : ℝ) (hR : 0 < R) :
    ‖∫ x in Ioc 1 (Real.exp R), mellinWeightedStep f x * paretoMellinKernel s x‖ ≤
      ‖f‖ * Real.sqrt R := by
  have hsub : Ioc 1 (Real.exp R) ⊆ Ioi (1 : ℝ) := fun _ hx => hx.1
  have hmeasure := Measure.restrict_mono (μ := volume) hsub le_rfl
  have hf := MemLp.mono_measure hmeasure (mellinWeightedStep_memLp f)
  have he := criticalMellinKernel_head_energy s hs R hR
  have hg : MemLp (paretoMellinKernel s) 2 (volume.restrict (Ioc 1 (Real.exp R))) := by
    have hm : Measurable (paretoMellinKernel s) :=
      Complex.continuous_ofReal.measurable.pow_const (-s)
    apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2
    by_contra hi
    rw [integral_undef hi] at he
    linarith
  have henergy : (∫ x in Ioc 1 (Real.exp R), ‖mellinWeightedStep f x‖^2) ≤ ‖f‖^2 := by
    rw [← mellinWeightedStep_energy f]
    exact integral_mono_measure hmeasure
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      (mellinWeightedStep_memLp f).norm.integrable_sq
  have hcs := RemoteLaplaceTail.norm_integral_mul_sq_le hf hg
  rw [he] at hcs
  have hsq := hcs.trans (mul_le_mul_of_nonneg_right henergy hR.le)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ ‖f‖ * Real.sqrt R)).mp
  rw [mul_pow, Real.sq_sqrt hR.le]
  exact hsq

theorem criticalMellin_tail_norm_le (f : ThresholdHilbert) {C : ℝ}
    (hC : ∀ k, |hilbertSequence f k| ≤ C) (s : ℂ) (hs : s.re = 1/2)
    {b : ℝ} (hb : 1 ≤ b) :
    ‖∫ x in Ioi b, (hilbertSequence f ⌊x⌋₊ : ℂ) * (x:ℂ)^(-s-1)‖ ≤
      2*C*b^(-(1/2:ℝ)) := by
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  have hi := (paretoMellin_step_integrable_of_bounded f hC s
    (by linarith [hs])).mono_set (Ioi_subset_Ioi hb)
  have hj : IntegrableOn (fun x : ℝ => x^(-(1/2:ℝ)-1)) (Ioi b) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hb0
  calc
    _ ≤ ∫ x in Ioi b, ‖(hilbertSequence f ⌊x⌋₊ : ℂ) * (x:ℂ)^(-s-1)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x in Ioi b, C*x^(-(1/2:ℝ)-1) := by
      apply integral_mono_ae hi.norm (hj.const_mul C)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 < x := hb0.trans hx
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re, hs]
      exact mul_le_mul_of_nonneg_right (hC _) (Real.rpow_nonneg hx0.le _)
    _ = _ := by
      rw [integral_const_mul,
        integral_Ioi_rpow_of_lt (by norm_num : -(1/2:ℝ)-1 < -1) hb0]
      norm_num
      <;> ring

/-- Literal critical-line cutoff: bounded physical sequences permit the full
integral, while the finite-head Hilbert cost is exactly sqrt R. -/
theorem paretoMellin_critical_cutoff (f : ThresholdHilbert) {C : ℝ}
    (hC : ∀ k, |hilbertSequence f k| ≤ C) (s : ℂ) (hs : s.re = 1/2)
    (R : ℝ) (hR : 0 < R) :
    ‖paretoMellin f s‖ ≤ ‖f‖ * Real.sqrt R + 2*C*Real.exp (-R/2) := by
  let G : ℝ → ℂ := fun x => (hilbertSequence f ⌊x⌋₊ : ℂ) * (x:ℂ)^(-s-1)
  have hb : 1 ≤ Real.exp R := Real.one_le_exp_iff.mpr hR.le
  have hi : IntegrableOn G (Ioi 1) :=
    paretoMellin_step_integrable_of_bounded f hC s (by linarith [hs])
  have hhsub : Ioc 1 (Real.exp R) ⊆ Ioi (1:ℝ) := fun _ hx => hx.1
  have htsub : Ioi (Real.exp R) ⊆ Ioi (1:ℝ) := Ioi_subset_Ioi hb
  have hdis : Disjoint (Ioc 1 (Real.exp R)) (Ioi (Real.exp R)) := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact (not_lt_of_ge hx.2) hy
  have hu : Ioc 1 (Real.exp R) ∪ Ioi (Real.exp R) = Ioi (1:ℝ) := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact hb.trans_lt h
    · intro hx
      by_cases hxR : x ≤ Real.exp R
      · exact Or.inl ⟨hx,hxR⟩
      · exact Or.inr (lt_of_not_ge hxR)
  have hsplit : (∫ x in Ioi 1, G x) =
      (∫ x in Ioc 1 (Real.exp R), G x) + ∫ x in Ioi (Real.exp R), G x := by
    rw [← hu]
    exact setIntegral_union hdis measurableSet_Ioi (hi.mono_set hhsub) (hi.mono_set htsub)
  have hhead : (∫ x in Ioc 1 (Real.exp R), G x) =
      ∫ x in Ioc 1 (Real.exp R), mellinWeightedStep f x * paretoMellinKernel s x := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    have hx0 : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hx.1).ne'
    dsimp [G,mellinWeightedStep,paretoMellinKernel]
    rw [Complex.cpow_sub (-s) 1 hx0,Complex.cpow_one]
    ring
  rw [paretoMellin_eq_step_integral]
  change ‖∫ x in Ioi 1, G x‖ ≤ _
  rw [hsplit]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · rw [hhead]
    exact criticalMellin_head_norm_le f s hs R hR
  · have htail := criticalMellin_tail_norm_le f hC s hs hb
    rw [Real.rpow_def_of_pos (Real.exp_pos R), Real.log_exp] at htail
    simpa only [show R * (-(1/2:ℝ)) = -R/2 by ring] using htail

end RiemannResearch.RH.Pareto
