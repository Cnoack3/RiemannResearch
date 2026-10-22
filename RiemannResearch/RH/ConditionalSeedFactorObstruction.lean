/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CRTMeanRepair
import RiemannResearch.RH.ConditionalMeanSubpolynomial
import RiemannResearch.RH.ParetoResidueMellinContinuation
import RiemannResearch.RH.ArithmeticConductorCommonZeros

/-!
# Artificial conductor zeros obstruct pulse-only conditional-energy bounds

Source: user-provided RH_Exact_CRT_Energy_Mean_Repair_2026-09-18,
appendix 9. The generic dual and polynomial proofs are adapted from the
already-verified ConditionalMeanHeadObstruction and ConditionalMeanSubpolynomial
modules, replacing zeta-zero annihilation by actual seed-factor annihilation.

No RH conclusion or unrestricted legal-energy lower bound is claimed.
The final dyadic result applies to the single-seed space legalSeedSpan {2};
delayed pulses belong to that space.
-/

noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto
open Analysis.Cesaro Probability.ConditionalIID ArithmeticCumulative
open RiemannResearch.RH.ArithmeticConductorCommonZeros

/-- The two conventions for the actual conductor factor differ only by a. -/
theorem conductorFactor_eq_mul_symbol (a : ℕ) (ha : 0 < a) (s : ℂ) :
    1 - (a : ℂ) ^ (1 - s) = (a : ℂ) * conductorSymbol a s := by
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  rw [RiemannResearch.RH.conductorSymbol_eq_cpow a ha s]
  rw [show (1 : ℂ) - s = 1 + (-s) by ring,
    Complex.cpow_add _ _ ha0, Complex.cpow_one]
  field_simp

/-- Seed-factor annihilation, without any assumption that zeta itself vanishes. -/
theorem paretoMellin_zero_on_legalClosure_of_seed_factors
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hfac : ∀ a ∈ A, conductorSymbol a s = 0)
    {f : ThresholdHilbert} (hf : f ∈ hilbertLegalClosure A) :
    paretoMellin f s = 0 := by
  let L := paretoMellinContinuous s hs
  have hspan : legalSeedSpan A ≤ L.ker.map hilbertSequenceLinear := by
    apply Submodule.span_le.2
    rintro g ⟨a, ha, m, hm, rfl⟩
    refine ⟨hilbertDilation m hm (digitHilbert a 1 (hA a ha) (by omega)), ?_, ?_⟩
    · change paretoMellin _ s = 0
      rw [paretoMellin_generator_zeta a m (hA a ha) hm s hs hs1,
        conductorFactor_eq_mul_symbol a (hA a ha) s, hfac a ha]
      simp
    · exact hilbertDilation_digit_one_sequence a m (hA a ha) hm
  have hlegal : hilbertLegalSubspace A ≤ L.ker := by
    intro g hg
    obtain ⟨v, hv, hvg⟩ := hspan hg
    have he : v = g := hilbertSequence_injective hvg
    exact he ▸ hv
  have hc := Submodule.topologicalClosure_mono hlegal
  rw [L.isClosed_ker.submodule_topologicalClosure_eq] at hc
  exact hc hf

theorem legal_second_pairing_zero_of_seed_factors (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hfac : ∀ a ∈ A, conductorSymbol a s = 0)
    {g : ℕ → ℝ} (hg : g ∈ legalSeedSpan A) :
    (∑' k : ℕ, mellinSecond s (k + 1) * mean (fun n => (g n : ℂ)) (k + 1)) = 0 := by
  obtain ⟨f, hf, hfg⟩ := legalSeedSpan_exists_hilbert A hA hg
  obtain ⟨B, hB⟩ := legalSeedSpan_bounded A hA hg
  have hb (n : ℕ) (hn : 0 < n) : ‖(hilbertSequence f n : ℂ)‖ ≤ B := by
    rw [hfg]
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hB n
  have hp := cesaro_mellin_pairing f s hs B hb
  rw [hfg] at hp
  have hz' := paretoMellin_zero_on_legalClosure_of_seed_factors A hA s hs hs1 hfac
    ((hilbertLegalSubspace A).le_topologicalClosure hf)
  simpa only [hz', mul_zero] using hp

/-- Exact signed head/tail balance followed by a valid weighted tail estimate. -/
theorem exact_head_dual_obstruction_of_seed_factors (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hfac : ∀ a ∈ A, conductorSymbol a s = 0)
    (N : ℕ) {g : ℕ → ℝ} (hg : g ∈ legalSeedSpan A)
    (hhead : ∀ n, 0 < n → n ≤ N → g n = 1) :
    ‖partialSum (mellinSecond s) N‖ ^ 2 ≤ dualTail s N * conditionalMeanSquare g := by
  obtain ⟨B, hB⟩ := legalSeedSpan_bounded A hA hg
  let F : ℕ → ℂ := fun n => (g n : ℂ)
  have hb (n : ℕ) (hn : 0 < n) : ‖F n‖ ≤ B := by
    simpa only [F, Complex.norm_real, Real.norm_eq_abs] using hB n
  have hsum := bounded_second_pairing_summable s (by linarith) F B hb
  have hsplit := hsum.sum_add_tsum_nat_add N
  have hpref : (∑ k ∈ Finset.range N, mellinSecond s (k + 1) * mean F (k + 1)) =
      partialSum (mellinSecond s) N := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkN := Finset.mem_range.mp hk
    rw [mean_eq_one_of_head F (k + 1) (Nat.succ_pos _) ?_, mul_one]
    intro n hn hnk
    simp only [F, hhead n hn (hnk.trans (by omega)), Complex.ofReal_one]
  rw [hpref, legal_second_pairing_zero_of_seed_factors A hA s hs hs1 hfac hg] at hsplit
  have he : (∑' k : ℕ, mellinSecond s (k + N + 1) * mean F (k + N + 1)) =
      -partialSum (mellinSecond s) N := by linear_combination hsplit
  have henergy := bounded_mean_energy_summable F B hb
  have htail : Summable (fun k : ℕ => conditionalWeight (k + N) *
      ‖mean F (k + N + 1)‖ ^ 2) :=
    henergy.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hbound := Analysis.WeightedPairing.pairing_norm_sq_le
    (fun k => conditionalWeight (k + N)) (fun k => conditionalWeight_pos _)
    (fun k => mellinSecond s (k + N + 1)) (fun k => mean F (k + N + 1))
    (dualTail_summable s hs N) htail
  rw [he, norm_neg] at hbound
  have hEsplit := henergy.sum_add_tsum_nat_add N
  have hEnonneg : 0 ≤ ∑ k ∈ Finset.range N, conditionalWeight k * ‖mean F (k + 1)‖ ^ 2 :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (conditionalWeight_pos k).le (sq_nonneg _))
  have ht : (∑' k : ℕ, conditionalWeight (k + N) * ‖mean F (k + N + 1)‖ ^ 2) ≤
      ∑' k : ℕ, conditionalWeight k * ‖mean F (k + 1)‖ ^ 2 := by linarith
  have hall : (∑' k : ℕ, conditionalWeight k * ‖mean F (k + 1)‖ ^ 2) =
      conditionalMeanSquare g := by
    simp only [F, mean_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs, conditionalMeanSquare]
  rw [hall] at ht
  exact hbound.trans (mul_le_mul_of_nonneg_left ht (dualTail_nonneg s N))

/-- A zero gives a uniform quantitative obstruction for all sufficiently long exact heads. -/
theorem exact_head_scaled_obstruction_of_seed_factors_eventually (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hfac : ∀ a ∈ A, conductorSymbol a s = 0) :
    ∀ᶠ N : ℕ in atTop, ∀ g ∈ legalSeedSpan A,
      (∀ n, 0 < n → n ≤ N → g n = 1) →
      (1 / 4 : ℝ) ≤ (3 * ‖s * (s + 1)‖ ^ 2 / (2 * s.re - 1)) *
        (N : ℝ) ^ (1 - 2 * s.re) * conditionalMeanSquare g := by
  filter_upwards [mellinSecond_prefix_eventually s hs, eventually_ge_atTop 1] with N hp hN
  intro g hg hhead
  have h := hp.trans (exact_head_dual_obstruction_of_seed_factors A hA s hs hs1 hfac N hg hhead)
  exact h.trans (mul_le_mul_of_nonneg_right (dualTail_le s hs N hN)
    (conditionalMeanSquare_nonneg g))


theorem exact_head_polynomial_obstruction_of_seed_factors_eventually (A : Set ℕ)
    (hA : ∀ a ∈ A, 0 < a) (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hs1 : s ≠ 1) (hfac : ∀ a ∈ A, conductorSymbol a s = 0) :
    ∀ᶠ N : ℕ in atTop, ∀ g ∈ legalSeedSpan A,
      (∀ n, 0 < n → n ≤ N → g n = 1) →
      ((2 * s.re - 1) / (12 * ‖s * (s + 1)‖ ^ 2)) *
        (N : ℝ) ^ (2 * s.re - 1) ≤ conditionalMeanSquare g := by
  have hd : 0 < 2 * s.re - 1 := by linarith
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hsadd : s + 1 ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at h
    linarith
  have hB : 0 < ‖s * (s + 1)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (mul_ne_zero hs0 hsadd))
  filter_upwards [exact_head_scaled_obstruction_of_seed_factors_eventually A hA s hs hs1 hfac,
    eventually_ge_atTop 1] with N hob hN
  intro g hg hhead
  have hnR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpow : (N : ℝ) ^ (1 - 2 * s.re) * (N : ℝ) ^ (2 * s.re - 1) = 1 := by
    rw [← Real.rpow_add hnR]
    convert Real.rpow_zero (N : ℝ) using 1
    congr 1
    ring
  have hc : (3 * ‖s * (s + 1)‖ ^ 2 / (2 * s.re - 1)) *
      ((2 * s.re - 1) / (12 * ‖s * (s + 1)‖ ^ 2)) = (1 / 4 : ℝ) := by
    field_simp [ne_of_gt hd, ne_of_gt hB]
    ring
  have he : ((3 * ‖s * (s + 1)‖ ^ 2 / (2 * s.re - 1)) *
      (N : ℝ) ^ (1 - 2 * s.re)) *
      (((2 * s.re - 1) / (12 * ‖s * (s + 1)‖ ^ 2)) *
        (N : ℝ) ^ (2 * s.re - 1)) = (1 / 4 : ℝ) := by
    calc
      _ = ((3 * ‖s * (s + 1)‖ ^ 2 / (2 * s.re - 1)) *
          ((2 * s.re - 1) / (12 * ‖s * (s + 1)‖ ^ 2))) *
          ((N : ℝ) ^ (1 - 2 * s.re) * (N : ℝ) ^ (2 * s.re - 1)) := by ring
      _ = _ := by rw [hc, hpow, mul_one]
  have hcoef : 0 < (3 * ‖s * (s + 1)‖ ^ 2 / (2 * s.re - 1)) *
      (N : ℝ) ^ (1 - 2 * s.re) := by positivity
  by_contra hnot
  have hbad := mul_lt_mul_of_pos_left (lt_of_not_ge hnot) hcoef
  rw [he] at hbad
  exact not_lt_of_ge (hob g hg hhead) hbad


/-- A fixed nonreal dyadic conductor resonance. -/
def dyadicPulseResonance : ℂ :=
  1 + (2 * (Real.pi : ℂ) * Complex.I) / (Real.log 2 : ℂ)

theorem dyadicPulseResonance_symbol :
    conductorSymbol 2 dyadicPulseResonance = 0 := by
  simpa [dyadicPulseResonance] using
    conductorSymbol_explicit_zero 2 (by norm_num) (1 : ℤ)

theorem dyadicPulseResonance_ne_one : dyadicPulseResonance ≠ 1 := by
  simpa [dyadicPulseResonance] using
    conductorSymbol_extra_zero_ne_one 2 (by norm_num) (1 : ℤ) (by norm_num)

theorem dyadicPulseResonance_re : dyadicPulseResonance.re = 1 :=
  conductorSymbol_zero_re 2 (by norm_num) dyadicPulseResonance
    dyadicPulseResonance_symbol

/-- Unconditional linear energy barrier in the one-seed dyadic pulse space. -/
theorem dyadic_pulse_head_linear_obstruction_eventually :
    ∀ᶠ N : ℕ in atTop, ∀ g ∈ legalSeedSpan ({2} : Set ℕ),
      (∀ n, 0 < n → n ≤ N → g n = 1) →
      (1 / (12 * ‖dyadicPulseResonance * (dyadicPulseResonance + 1)‖ ^ 2)) *
        (N : ℝ) ≤ conditionalMeanSquare g := by
  have hA : ∀ a ∈ ({2} : Set ℕ), 0 < a := by
    intro a ha
    rcases Set.mem_singleton_iff.mp ha with rfl
    norm_num
  have hfac : ∀ a ∈ ({2} : Set ℕ), conductorSymbol a dyadicPulseResonance = 0 := by
    intro a ha
    rcases Set.mem_singleton_iff.mp ha with rfl
    exact dyadicPulseResonance_symbol
  have hs : (1 / 2 : ℝ) < dyadicPulseResonance.re := by
    rw [dyadicPulseResonance_re]
    norm_num
  have he : 2 * dyadicPulseResonance.re - 1 = (1 : ℝ) := by
    rw [dyadicPulseResonance_re]
    norm_num
  filter_upwards [exact_head_polynomial_obstruction_of_seed_factors_eventually
    ({2} : Set ℕ) hA dyadicPulseResonance hs dyadicPulseResonance_ne_one hfac]
    with N hN
  intro g hg hhead
  simpa only [he, Real.rpow_one] using hN g hg hhead

theorem dyadic_pulse_head_linear_constant_pos :
    0 < 1 / (12 * ‖dyadicPulseResonance * (dyadicPulseResonance + 1)‖ ^ 2) := by
  have hs0 : dyadicPulseResonance ≠ 0 := by
    intro he
    have hr := dyadicPulseResonance_re
    simp [he] at hr
  have hs1 : dyadicPulseResonance + 1 ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re,
      dyadicPulseResonance_re] at hr
    norm_num at hr
  exact one_div_pos.mpr (mul_pos (by norm_num)
    (sq_pos_of_pos (norm_pos_iff.mpr (mul_ne_zero hs0 hs1))))

/-- The physical delayed pulse is precisely a rescaled all-integer dyadic dilation. -/
theorem meanPulse_eq_scaled_dyadic_dilation (A : ℕ) (hA : 0 < A) :
    CRTBlock.meanPulse A = (1 / (A : ℝ)) • dilation A (residue 2) := by
  have hAR : (A : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hA
  ext n
  rw [Pi.smul_apply, smul_eq_mul, residue_mul_floor]
  simp only [CRTBlock.meanPulse, residueFraction, residue,
    Nat.mul_comm A 2, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hAR]

theorem meanPulse_mem_dyadic_seed_span (A : ℕ) (hA : 0 < A) :
    CRTBlock.meanPulse A ∈ legalSeedSpan ({2} : Set ℕ) := by
  rw [meanPulse_eq_scaled_dyadic_dilation A hA]
  exact (legalSeedSpan ({2} : Set ℕ)).smul_mem _
    (dilation_generator_mem ({2} : Set ℕ) (by simp) hA)


/-- No cofinal exact-head family in the dyadic pulse space has subpolynomial
conditional energy. This is independent of RH. -/
theorem not_subpolynomial_dyadic_heads
    (F : ℕ → ℕ → ℝ) (Y : ℕ → ℕ)
    (hF : ∀ j, F j ∈ legalSeedSpan ({2} : Set ℕ))
    (hhead : ∀ j n, 0 < n → n ≤ Y j → F j n = 1)
    (hY : Tendsto Y atTop atTop) :
    ¬ SubpolynomialConditionalMean F Y := by
  intro hsub
  let c : ℝ := 1/(12*‖dyadicPulseResonance*(dyadicPulseResonance+1)‖^2)
  have hc : 0 < c := dyadic_pulse_head_linear_constant_pos
  obtain ⟨C,hC,hbound⟩ := hsub (1/2) (by norm_num)
  have hyR : Tendsto (fun j => (Y j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hY
  have hdecay := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)).comp hyR).const_mul C
  have hsmall : ∀ᶠ j : ℕ in atTop, C*(Y j : ℝ)^(-(1/2 : ℝ)) < c :=
    hdecay.eventually (gt_mem_nhds (by simpa using hc))
  have hlin := hY.eventually dyadic_pulse_head_linear_obstruction_eventually
  have hpos := hY.eventually (eventually_ge_atTop 1)
  obtain ⟨j,hjlin,hjbound,hjpos,hjsmall⟩ :=
    (hlin.and (hbound.and (hpos.and hsmall))).exists
  have hypos : (0 : ℝ) < Y j := by exact_mod_cast hjpos
  have hpow : (Y j : ℝ)^(-(1/2 : ℝ))*(Y j : ℝ) = (Y j : ℝ)^(1/2 : ℝ) := by
    calc
      _ = (Y j : ℝ)^(-(1/2 : ℝ))*(Y j : ℝ)^(1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hypos]; norm_num
  have hlo : c*(Y j : ℝ) ≤ conditionalMeanSquare (F j) :=
    hjlin (F j) (hF j) (hhead j)
  have hhi := mul_lt_mul_of_pos_right hjsmall hypos
  rw [mul_assoc,hpow] at hhi
  exact not_lt_of_ge (hlo.trans hjbound) hhi

end RiemannResearch.RH.Pareto
