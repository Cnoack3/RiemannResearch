import RiemannResearch.RH.ParetoParityAdjointCriterion
import RiemannResearch.RH.ParetoFirstPointHeadObstruction
import RiemannResearch.RH.ParetoMellinDilation
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip

/-! # Exact mean-zero cost of the first Pareto site

The centered representer of evaluation at one has unit norm. Saturation of
the one-site cost by mixed packets places this representer in the legal
closure. Its Mellin symbol detects every zero in the open right half-strip.
-/
noncomputable section
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- Saturating the one-site mean-zero interpolation budget gives the vector with
physical values 1,-1,-1,... in the closed legal span. Its Mellin symbol rules
out every zero in the open right half-strip. -/
theorem riemannHypothesis_of_centered_firstSite_mem
    (hb : hilbertOne - hilbertDilation 2 (by decide) hilbertOne ∈ closedSpace) :
    RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hlt hz
  have hs0 : s ≠ 0 := by
    intro he
    norm_num [he] at hs
  have hs1 : s ≠ 1 := by
    intro he
    norm_num [he] at hlt
  have hv := paretoMellin_zero_on_legalClosure_of_zeta {n : ℕ | 0 < n}
    (fun _ hn => hn) s hs hs1 hz (closedSpace_le_legalClosure hb)
  change paretoMellinContinuous s hs
    (hilbertOne - hilbertDilation 2 (by decide) hilbertOne) = 0 at hv
  rw [map_sub] at hv
  change paretoMellin hilbertOne s -
    paretoMellin (hilbertDilation 2 (by decide) hilbertOne) s = 0 at hv
  rw [paretoMellin_dilation, paretoMellin_one s hs] at hv
  have heq : (1 - (2 : ℂ) ^ (1 - s)) * (1 / s) = 0 := by
    calc
      _ = 1 / s - (2 : ℂ) ^ (1 - s) * (1 / s) := by ring
      _ = 0 := by simpa using hv
  have hpow : (2 : ℂ) ^ (1 - s) = 1 :=
    (sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_right (one_div_ne_zero hs0))).symm
  have hnorm : 1 < ‖(2 : ℂ) ^ (1 - s)‖ := by
    change 1 < ‖((2 : ℝ) : ℂ) ^ (1 - s)‖
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
    simp only [Complex.sub_re, Complex.one_re]
    exact Real.one_lt_rpow (by norm_num) (by linarith)
  rw [hpow, norm_one] at hnorm
  exact (lt_irrefl (1 : ℝ)) hnorm

end RiemannResearch.RH.Pareto.CoefficientStabilization


namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

/-- The centered evaluation representer at physical site one. -/
noncomputable def centeredFirstSite : ThresholdHilbert :=
  (2 : ℝ) • hilbertAtom 1 (by decide) - hilbertOne

theorem centeredFirstSite_inner (x : ThresholdHilbert) :
    inner ℝ centeredFirstSite x = hilbertSequence x 1 - inner ℝ x hilbertOne := by
  rw [centeredFirstSite, inner_sub_left, real_inner_smul_left, hilbertAtom_inner,
    real_inner_comm hilbertOne x]
  norm_num [positiveWeight]
  ring

theorem centeredFirstSite_eq_dilation_sub :
    centeredFirstSite = hilbertOne - hilbertDilation 2 (by decide) hilbertOne := by
  apply hilbertSequence_injective
  rw [centeredFirstSite, hilbertSequence_sub, hilbertSequence_smul,
    hilbertSequence_sub, hilbertDilation_sequence, hilbertOne_sequence, hilbertAtom_sequence]
  funext n
  change 2 * (if n = 1 then 1 else (0 : ℝ)) - (if n = 0 then 0 else 1) =
    (if n = 0 then 0 else 1) - 2 * (if n/2 = 0 then 0 else 1)
  split_ifs <;> norm_num <;> omega

theorem centeredFirstSite_unit_norm_sq : ‖centeredFirstSite‖ ^ 2 = 1 := by
  have hm : inner ℝ centeredFirstSite hilbertOne = 0 := by
    rw [centeredFirstSite_inner, real_inner_self_eq_norm_sq, hilbertOne_norm_sq,
      hilbertOne_sequence]
    norm_num [zeroAnchor]
  rw [← real_inner_self_eq_norm_sq, centeredFirstSite_inner, hm, sub_zero,
    centeredFirstSite, hilbertSequence_sub, hilbertSequence_smul,
    hilbertAtom_sequence, hilbertOne_sequence]
  norm_num [zeroAnchor]

/-- Exact complete cost for a mixed vector with first physical value one. -/
theorem mixed_unit_firstSite_cost {v : ThresholdHilbert} (hv : v ∈ mixedClosure)
    (h1 : hilbertSequence v 1 = 1) :
    ‖v‖ ^ 2 = 1 + ‖v - centeredFirstSite‖ ^ 2 := by
  rw [norm_sub_sq_real, centeredFirstSite_unit_norm_sq,
    real_inner_comm centeredFirstSite v, centeredFirstSite_inner,
    ((mem_mixedClosure_iff_mem_closedSpace_and_mean_zero v).mp hv).2, h1]
  ring

theorem rh_of_sharp_mixed_firstSite_cost
    (h : ∀ ε : ℝ, 0 < ε → ∃ v ∈ mixedClosure,
      hilbertSequence v 1 = 1 ∧ ‖v‖ ^ 2 < 1 + ε ^ 2) : RiemannHypothesis := by
  apply riemannHypothesis_of_centered_firstSite_mem
  rw [← centeredFirstSite_eq_dilation_sub]
  apply mixedClosure_le_closedSpace
  have hc : centeredFirstSite ∈ closure (mixedClosure : Set ThresholdHilbert) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨v, hv, h1, hb⟩ := h ε hε
    refine ⟨v, hv, ?_⟩
    rw [dist_eq_norm, norm_sub_rev]
    have hi := mixed_unit_firstSite_cost hv h1
    nlinarith [norm_nonneg (v - centeredFirstSite)]
  have hclosed : IsClosed (mixedClosure : Set ThresholdHilbert) := by
    exact Submodule.isClosed_topologicalClosure _
  rwa [hclosed.closure_eq] at hc

end RiemannResearch.RH.Pareto.PrimePowerSchur
