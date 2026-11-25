import RiemannResearch.RH.ParetoParityAdjointCriterion
import RiemannResearch.RH.ParetoFirstPointHeadObstruction
import RiemannResearch.RH.LocalizedMellinObstruction
import RiemannResearch.RH.ParetoMellinDilation
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip

/-! # Exact mean-zero cost of the first Pareto site

The centered representer of evaluation at one has unit norm. Saturation of
the one-site cost by mixed packets places this representer in the legal
closure. Its Mellin symbol detects every zero in the open right half-strip.
-/
noncomputable section
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- The Mellin transform of a difference of two normalized threshold steps
is explicit at every point in the continuity half-plane. -/
theorem thresholdContrast_mellin (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    paretoMellin (hilbertDilation m hm hilbertOne - hilbertDilation k hk hilbertOne) s =
      ((m : ℂ) ^ (1-s) - (k : ℂ) ^ (1-s)) / s := by
  change paretoMellinContinuous s hs (_ - _) = _
  rw [map_sub]
  change paretoMellin (hilbertDilation m hm hilbertOne) s -
    paretoMellin (hilbertDilation k hk hilbertOne) s = _
  rw [paretoMellin_dilation, paretoMellin_dilation, paretoMellin_one s hs]
  ring

/-- Each actual zeta zero in the evaluation half-plane gives a complete
power lower bound for every legal fit matching the threshold contrast on
all physical sites strictly below L. -/
theorem thresholdContrast_exact_head_error_lower (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (L : ℕ) (hL : 1 ≤ L) {v : ThresholdHilbert} (hv : v ∈ closedSpace)
    (hhead : ∀ j, 0 < j → j < L → hilbertSequence v j =
      hilbertSequence (hilbertDilation m hm hilbertOne - hilbertDilation k hk hilbertOne) j)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    (2*s.re-1) * ‖((m : ℂ)^(1-s) - (k : ℂ)^(1-s))/s‖^2 * (L : ℝ)^(2*s.re-1) ≤
      ‖hilbertDilation m hm hilbertOne - hilbertDilation k hk hilbertOne - v‖^2 := by
  let z := hilbertDilation m hm hilbertOne - hilbertDilation k hk hilbertOne
  have hvz := paretoMellin_zero_on_legalClosure_of_zeta {a : ℕ | 0 < a}
    (fun _ ha => ha) s hs hs1 hz (closedSpace_le_legalClosure hv)
  have heval : paretoMellin (z-v) s = ((m : ℂ)^(1-s) - (k : ℂ)^(1-s))/s := by
    change paretoMellinContinuous s hs (z-v) = _
    rw [map_sub]
    change paretoMellin z s - paretoMellin v s = _
    rw [hvz, sub_zero]
    exact thresholdContrast_mellin m k hm hk s hs
  have hzero j (hj : 0 < j) (hjL : j < L) : hilbertSequence (z-v) j = 0 := by
    rw [hilbertSequence_sub, Pi.sub_apply, hhead j hj hjL, sub_self]
  simpa only [heval] using mellin_zero_head_lower (z-v) L hL hzero s hs

/-- Distinct positive thresholds have a nonzero difference symbol to the left
of the line Re(s)=1, away from the pole at zero. -/
theorem thresholdContrast_symbol_ne_zero (m k : ℕ) (hm : 0 < m) (hmk : m < k)
    (s : ℂ) (hs0 : s ≠ 0) (hlt : s.re < 1) :
    ((m : ℂ) ^ (1-s) - (k : ℂ) ^ (1-s)) / s ≠ 0 := by
  intro hz
  have he := sub_eq_zero.mp ((div_eq_zero_iff.mp hz).resolve_right hs0)
  have hnorm := congrArg norm he
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  rw [Complex.norm_natCast_cpow_of_pos hm, Complex.norm_natCast_cpow_of_pos (hm.trans hmk)] at hnorm
  exact (ne_of_lt (Real.rpow_lt_rpow hmR.le (by exact_mod_cast hmk)
    (by simpa only [Complex.sub_re, Complex.one_re] using sub_pos.mpr hlt))) hnorm

/-- Every two distinct positive thresholds have a contrast that detects every
point in the open right half-strip. Thus membership of just one such contrast
in the legal closure implies RH. -/
theorem riemannHypothesis_of_thresholdContrast_mem (m k : ℕ) (hm : 0 < m) (hmk : m < k)
    (hb : hilbertDilation m hm hilbertOne -
      hilbertDilation k (hm.trans hmk) hilbertOne ∈ closedSpace) :
    RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hlt hz
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at hlt
  have hv := paretoMellin_zero_on_legalClosure_of_zeta {n : ℕ | 0 < n}
    (fun _ hn => hn) s hs hs1 hz (closedSpace_le_legalClosure hb)
  rw [thresholdContrast_mellin m k hm (hm.trans hmk) s hs] at hv
  exact thresholdContrast_symbol_ne_zero m k hm hmk s hs0 hlt hv

/-- Saturating the one-site mean-zero interpolation budget gives the vector with
physical values 1,-1,-1,... in the closed legal span. Its Mellin symbol rules
out every zero in the open right half-strip. -/
theorem riemannHypothesis_of_centered_firstSite_mem
    (hb : hilbertOne - hilbertDilation 2 (by decide) hilbertOne ∈ closedSpace) :
    RiemannHypothesis :=
  riemannHypothesis_of_thresholdContrast_mem 1 2 (by decide) (by decide)
    (by simpa only [hilbertDilation_one] using hb)

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
