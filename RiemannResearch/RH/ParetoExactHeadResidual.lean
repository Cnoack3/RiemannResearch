import RiemannResearch.RH.ThresholdRiemannHypothesis

/-!
# Exact-head residual amplification and a deterministic RH criterion

Source: user-requested deterministic continuation of the Nyman--Pareto program,
2026-09-17. The proof combines the project's actual legal Mellin annihilation
with its exact continuous tail kernel energy. No novelty claim is made.

A residual vanishing on the first N positive coordinates has its entire Mellin
transform and norm in the tail beyond N+1. At a hypothetical right-half-plane
zeta zero this amplifies the conserved value 1/s into a polynomial lower bound
on the actual residual norm, without an oscillating head factor.

The final RH implication is a conditional research reduction: the existence
of a legal exact-head family with a uniform residual bound remains Open.
Neither finite interpolation nor positivity of a finite Gram matrix supplies it.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto

private theorem step_zero_on_head {f : ThresholdHilbert} {N : ℕ}
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 0)
    {x : ℝ} (hx : x ∈ Ico (1 : ℝ) ((N : ℝ) + 1)) :
    mellinWeightedStep f x = 0 := by
  have hx0 : 0 ≤ x := le_trans zero_le_one hx.1
  have hlow : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).2 (by simpa using hx.1)
  have hhigh : ⌊x⌋₊ < N + 1 := (Nat.floor_lt hx0).2 (by exact_mod_cast hx.2)
  have hk : hilbertSequence f ⌊x⌋₊ = 0 := hhead ⌊x⌋₊ (by omega) (by omega)
  simp [mellinWeightedStep, hk]

theorem paretoMellin_zero_head_tail {f : ThresholdHilbert} {N : ℕ}
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 0)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    (∫ x in Ioi ((N : ℝ) + 1), mellinWeightedStep f x * paretoMellinKernel s x) =
      paretoMellin f s := by
  have hb : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hfull := paretoMellin_integrable f s hs
  have htail := hfull.mono_set (Ioi_subset_Ioi hb)
  have h := intervalIntegral.integral_interval_add_Ioi hfull htail
  have hzero : (∫ x in (1 : ℝ)..((N : ℝ) + 1),
      mellinWeightedStep f x * paretoMellinKernel s x) = 0 := by
    rw [intervalIntegral.integral_of_le hb, ← integral_Ico_eq_integral_Ioc]
    calc
      _ = ∫ x in Ico (1 : ℝ) ((N : ℝ) + 1), (0 : ℂ) := by
        apply setIntegral_congr_fun measurableSet_Ico
        intro x hx
        simp [step_zero_on_head hhead hx]
      _ = 0 := by simp
  rw [hzero, zero_add] at h
  exact h

theorem pareto_zero_head_tail_energy {f : ThresholdHilbert} {N : ℕ}
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 0) :
    (∫ x in Ioi ((N : ℝ) + 1), ‖mellinWeightedStep f x‖ ^ 2) = ‖f‖ ^ 2 := by
  have hb : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hfull : IntegrableOn (fun x => ‖mellinWeightedStep f x‖ ^ 2) (Ioi (1 : ℝ)) :=
    (mellinWeightedStep_memLp f).norm.integrable_sq
  have htail := hfull.mono_set (Ioi_subset_Ioi hb)
  have h := intervalIntegral.integral_interval_add_Ioi hfull htail
  have hzero : (∫ x in (1 : ℝ)..((N : ℝ) + 1),
      ‖mellinWeightedStep f x‖ ^ 2) = 0 := by
    rw [intervalIntegral.integral_of_le hb, ← integral_Ico_eq_integral_Ioc]
    calc
      _ = ∫ x in Ico (1 : ℝ) ((N : ℝ) + 1), (0 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Ico
        intro x hx
        simp [step_zero_on_head hhead hx]
      _ = 0 := by simp
  rw [hzero, zero_add, mellinWeightedStep_energy] at h
  exact h

theorem paretoMellin_zero_head_norm_sq_le {f : ThresholdHilbert} {N : ℕ}
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 0)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    ‖paretoMellin f s‖ ^ 2 ≤
      ‖f‖ ^ 2 * (((N : ℝ) + 1) ^ (1 - 2 * s.re) / (2 * s.re - 1)) := by
  have h := paretoMellin_tail_norm_sq_le f s hs
    (by linarith [Nat.cast_nonneg (α := ℝ) N] : (1 : ℝ) ≤ (N : ℝ) + 1)
  rwa [paretoMellin_zero_head_tail hhead s hs, pareto_zero_head_tail_energy hhead] at h

theorem legal_exact_head_residual_lower_bound
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0)
    {f : ThresholdHilbert} (hf : f ∈ hilbertLegalClosure A) {N : ℕ}
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1) :
    ((2 * s.re - 1) / ‖s‖ ^ 2) * ((N : ℝ) + 1) ^ (2 * s.re - 1) ≤
      ‖hilbertOne - f‖ ^ 2 := by
  have hrhead : ∀ k, 0 < k → k ≤ N → hilbertSequence (hilbertOne - f) k = 0 := by
    intro k hk hkN
    change hilbertSequenceLinear (hilbertOne - f) k = 0
    rw [map_sub]
    change hilbertSequence hilbertOne k - hilbertSequence f k = 0
    rw [hilbertOne_sequence, hhead k hk hkN]
    simp [zeroAnchor, ne_of_gt hk]
  have hm : paretoMellin (hilbertOne - f) s = 1 / s := by
    change paretoMellinContinuous s hs (hilbertOne - f) = _
    rw [map_sub]
    change paretoMellin hilbertOne s - paretoMellin f s = _
    rw [paretoMellin_one s hs,
      paretoMellin_zero_on_legalClosure_of_zeta A hA s hs hs1 hz hf, sub_zero]
  have h := paretoMellin_zero_head_norm_sq_le hrhead s hs
  rw [hm, norm_div, norm_one, div_pow, one_pow] at h
  have hd : 0 < 2 * s.re - 1 := by linarith
  have hb : 0 < (N : ℝ) + 1 := by positivity
  have hp : 0 < ((N : ℝ) + 1) ^ (2 * s.re - 1) :=
    Real.rpow_pos_of_pos hb _
  have he : ((N : ℝ) + 1) ^ (2 * s.re - 1) *
      ((N : ℝ) + 1) ^ (1 - 2 * s.re) = 1 := by
    rw [← Real.rpow_add hb]
    have hexp : 2 * s.re - 1 + (1 - 2 * s.re) = 0 := by ring
    rw [hexp, Real.rpow_zero]
  have hh := mul_le_mul_of_nonneg_left h (mul_nonneg hd.le hp.le)
  have hcancel : (2 * s.re - 1) * ((N : ℝ) + 1) ^ (2 * s.re - 1) *
      (‖hilbertOne - f‖ ^ 2 *
        (((N : ℝ) + 1) ^ (1 - 2 * s.re) / (2 * s.re - 1))) =
      ‖hilbertOne - f‖ ^ 2 := by
    calc
      _ = ‖hilbertOne - f‖ ^ 2 *
          (((N : ℝ) + 1) ^ (2 * s.re - 1) *
            ((N : ℝ) + 1) ^ (1 - 2 * s.re)) := by field_simp [ne_of_gt hd]
      _ = _ := by rw [he, mul_one]
  rw [hcancel] at hh
  calc
    _ = (2 * s.re - 1) * ((N : ℝ) + 1) ^ (2 * s.re - 1) * (1 / ‖s‖ ^ 2) := by ring
    _ ≤ _ := hh


/-- A finite full-norm certificate excludes a zero at the indicated point. -/
theorem zeta_ne_zero_of_exact_head_error_lt
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    {f : ThresholdHilbert} (hf : f ∈ hilbertLegalClosure A) {N : ℕ}
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1)
    (herror : ‖hilbertOne - f‖ ^ 2 <
      ((2 * s.re - 1) / ‖s‖ ^ 2) * ((N : ℝ) + 1) ^ (2 * s.re - 1)) :
    riemannZeta s ≠ 0 := by
  intro hz
  exact not_lt_of_ge (legal_exact_head_residual_lower_bound A hA s hs hs1 hz hf hhead) herror


/-- Uniform boundedness of actual exact-head residuals excludes every right-half-plane zero.
The bounded family is the explicit unresolved arithmetic premise. -/
theorem zeta_ne_zero_of_bounded_exact_head_residuals
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (g : ℕ → ThresholdHilbert) (hg : ∀ N, g N ∈ hilbertLegalClosure A)
    (hhead : ∀ N k, 0 < k → k ≤ N → hilbertSequence (g N) k = 1)
    (C : ℝ) (hbound : ∀ N, ‖hilbertOne - g N‖ ^ 2 ≤ C)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hd : 0 < 2 * s.re - 1 := by linarith
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hc : 0 < (2 * s.re - 1) / ‖s‖ ^ 2 :=
    div_pos hd (sq_pos_of_pos (norm_pos_iff.mpr hs0))
  have hbase : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    have hn : ∀ᶠ N : ℕ in atTop, b ≤ (N : ℝ) :=
      (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually
        (eventually_ge_atTop b)
    filter_upwards [hn] with N hN
    linarith
  have hdecay := ((tendsto_rpow_neg_atTop hd).comp hbase).const_mul C
  have hsmall : ∀ᶠ N : ℕ in atTop,
      C * ((N : ℝ) + 1) ^ (-(2 * s.re - 1)) < (2 * s.re - 1) / ‖s‖ ^ 2 :=
    hdecay.eventually (gt_mem_nhds (by simpa only [mul_zero] using hc))
  obtain ⟨N, hN⟩ := hsmall.exists
  have hb : 0 < (N : ℝ) + 1 := by positivity
  have hlo := (legal_exact_head_residual_lower_bound A hA s hs hs1 hz
    (hg N) (hhead N)).trans (hbound N)
  have he : ((N : ℝ) + 1) ^ (2 * s.re - 1) *
      ((N : ℝ) + 1) ^ (-(2 * s.re - 1)) = 1 := by
    rw [← Real.rpow_add hb, add_neg_cancel, Real.rpow_zero]
  have hh := mul_le_mul_of_nonneg_right hlo
    (Real.rpow_nonneg hb.le (-(2 * s.re - 1)))
  rw [mul_assoc, he, mul_one] at hh
  exact not_lt_of_ge hh hN

/-- Conditional research reduction: a uniformly bounded equality-preserving
legal family implies actual Mathlib RH. No such bound is supplied here. -/
theorem riemannHypothesis_of_bounded_exact_head_residuals
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (g : ℕ → ThresholdHilbert) (hg : ∀ N, g N ∈ hilbertLegalClosure A)
    (hhead : ∀ N k, 0 < k → k ≤ N → hilbertSequence (g N) k = 1)
    (C : ℝ) (hbound : ∀ N, ‖hilbertOne - g N‖ ^ 2 ≤ C) :
    RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_strip_zeros_on_line.mpr
  intro ρ hz h0 h1
  have hright (s : ℂ) (hsz : riemannZeta s = 0)
      (_hs0 : 0 < s.re) (hslt : s.re < 1) : s.re ≤ 1 / 2 := by
    by_contra h
    have hs : 1 / 2 < s.re := lt_of_not_ge h
    have hsne : s ≠ 1 := by intro he; simp [he] at hslt
    exact zeta_ne_zero_of_bounded_exact_head_residuals A hA g hg hhead C hbound s hs hsne hsz
  have href := Zeta23.zeta_reflect_zero ρ ⟨hz, h0, h1⟩
  have hr := hright (Zeta23.reflect ρ) href.1 href.2.1 href.2.2
  have hl := hright ρ hz h0 h1
  simp [Zeta23.reflect] at hr
  linarith


end RiemannResearch.RH.Pareto
