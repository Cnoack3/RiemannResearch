/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.LocalizedMellinObstruction
import RiemannResearch.RH.ParetoCompactHead
import RiemannResearch.Analysis.SubpolynomialWindowGrowth
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip

/-!
# Exact retained head signature in the localized Mellin obstruction


Source: the user-provided Green-Pareto-Schur continuation and its requested
improvement, 6 October 2026. No arithmetic signature provider is asserted.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto

/-- Exact localization retains the full complex head signature and the full
head square. It does not replace the head by an absolute-norm estimate. -/
theorem legal_residual_head_signature_power_lower
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    {f : ThresholdHilbert} (hf : f ∈ hilbertLegalClosure A)
    (n : ℕ) (hn : 1 ≤ n)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) :
    (2 * s.re - 1) *
      ‖1 / s - paretoMellin (compactHead (n - 1) (hilbertOne - f)) s‖ ^ 2 *
      (n : ℝ) ^ (2 * s.re - 1) ≤
      ‖hilbertOne - f‖ ^ 2 - ‖compactHead (n - 1) (hilbertOne - f)‖ ^ 2 := by
  let e := hilbertOne - f
  let h := compactHead (n - 1) e
  let t := e - h
  have hfzero := paretoMellin_zero_on_legalClosure_of_zeta A hA s hs hs1 hz hf
  have heval : paretoMellin e s = 1 / s := by
    change paretoMellinContinuous s hs (hilbertOne - f) = _
    rw [map_sub]
    change paretoMellin hilbertOne s - paretoMellin f s = _
    rw [paretoMellin_one s hs, hfzero, sub_zero]
  have htval : paretoMellin t s = 1 / s - paretoMellin h s := by
    change paretoMellinContinuous s hs (e - h) = _
    rw [map_sub]
    change paretoMellin e s - paretoMellin h s = _
    rw [heval]
  have hthead : ∀ k, 0 < k → k < n → hilbertSequence t k = 0 := by
    intro k hk hkn
    change hilbertSequenceLinear (e - compactHead (n - 1) e) k = 0
    rw [map_sub]
    change hilbertSequence e k - hilbertSequence (compactHead (n - 1) e) k = 0
    rw [compactHead_sequence, if_pos (by omega)]
    exact sub_self _
  have hb := mellin_zero_head_lower t n hn hthead s hs
  rw [htval] at hb
  have hpy := compactHead_pythagoras (n - 1) e
  change ‖e‖ ^ 2 = ‖h‖ ^ 2 + ‖t‖ ^ 2 at hpy
  change (2 * s.re - 1) * ‖1 / s - paretoMellin h s‖ ^ 2 *
    (n : ℝ) ^ (2 * s.re - 1) ≤ ‖e‖ ^ 2 - ‖h‖ ^ 2
  linarith

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis.SubpolynomialWindow

/-- Cofinal weighted noncancellation is sufficient. The signature may tend
to zero: at each hypothetical off-line zero its squared localized signature
need only retain some positive polynomial growth on unbounded indices.
No head norm limit is assumed. -/
theorem riemannHypothesis_of_legal_subpolynomial_cofinal_weighted_signature
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (f : ℕ → ThresholdHilbert) (n : ℕ → ℕ) (C : ℕ → ℝ)
    (hn : Tendsto (fun i => (n i : ℝ)) atTop atTop)
    (hf : ∀ i, f i ∈ hilbertLegalClosure A)
    (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i, ‖hilbertOne - f i‖ ^ 2 ≤ C i + 1)
    (hsub : Tendsto (fun i => Real.log (1 + C i) / Real.log (n i : ℝ))
      atTop (𝓝 0))
    (hsignature : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → s.re < 1 →
      riemannZeta s = 0 → ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧
        ∃ᶠ i : ℕ in atTop, c * (n i : ℝ) ^ ε ≤
          ‖1 / s - paretoMellin (compactHead (n i - 1) (hilbertOne - f i)) s‖ ^ 2 *
            (n i : ℝ) ^ (2 * s.re - 1)) : RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hslt hz
  obtain ⟨c, ε, hc, hε, hsig⟩ := hsignature s hs hslt hz
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at hslt
  have hd : 0 < 2 * s.re - 1 := by linarith
  have hn1 : ∀ᶠ i : ℕ in atTop, (1 : ℝ) ≤ (n i : ℝ) :=
    hn.eventually (eventually_ge_atTop 1)
  have hfloor : ∃ᶠ i : ℕ in atTop,
      ((2 * s.re - 1) * c) * (n i : ℝ) ^ ε ≤ C i + 1 := by
    apply (hsig.and_eventually hn1).mono
    rintro i ⟨hsi, hi⟩
    have hiNat : 1 ≤ n i := by exact_mod_cast hi
    have hmul := mul_le_mul_of_nonneg_left hsi hd.le
    have hb := legal_residual_head_signature_power_lower A hA (hf i)
      (n i) hiNat s hs hs1 hz
    have hdrop : ‖hilbertOne - f i‖ ^ 2 -
        ‖compactHead (n i - 1) (hilbertOne - f i)‖ ^ 2 ≤
        ‖hilbertOne - f i‖ ^ 2 := sub_le_self _ (sq_nonneg _)
    have hcombine := ((hmul.trans (by simpa only [mul_assoc] using hb)).trans hdrop).trans (hbound i)
    simpa only [mul_assoc] using hcombine
  exact no_positive_power_floor_frequently (fun i => (n i : ℝ)) C 1
    ((2 * s.re - 1) * c) ε hn hC (by norm_num) (mul_pos hd hc) hε hsub hfloor

/-- The preceding criterion in the simpler cofinal uniformly-separated form.
Separation is required only on unbounded indices, not eventually. -/
theorem riemannHypothesis_of_legal_subpolynomial_cofinal_head_signature
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (f : ℕ → ThresholdHilbert) (n : ℕ → ℕ) (C : ℕ → ℝ)
    (hn : Tendsto (fun i => (n i : ℝ)) atTop atTop)
    (hf : ∀ i, f i ∈ hilbertLegalClosure A)
    (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i, ‖hilbertOne - f i‖ ^ 2 ≤ C i + 1)
    (hsub : Tendsto (fun i => Real.log (1 + C i) / Real.log (n i : ℝ))
      atTop (𝓝 0))
    (hsignature : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → s.re < 1 →
      riemannZeta s = 0 → ∃ c : ℝ, 0 < c ∧
        ∃ᶠ i : ℕ in atTop, c ≤
          ‖1 / s - paretoMellin (compactHead (n i - 1) (hilbertOne - f i)) s‖) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_legal_subpolynomial_cofinal_weighted_signature
    A hA f n C hn hf hC hbound hsub
  intro s hs hslt hz
  obtain ⟨c, hc, hsig⟩ := hsignature s hs hslt hz
  refine ⟨c ^ 2, 2 * s.re - 1, pow_pos hc 2, by linarith, ?_⟩
  have hn1 : ∀ᶠ i : ℕ in atTop, (1 : ℝ) ≤ (n i : ℝ) :=
    hn.eventually (eventually_ge_atTop 1)
  apply (hsig.and_eventually hn1).mono
  rintro i ⟨hsi, hi⟩
  have hsq := (sq_le_sq₀ hc.le (norm_nonneg _)).mpr hsi
  exact mul_le_mul_of_nonneg_right hsq
    (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ n i) _)

end RiemannResearch.RH.Pareto
