/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.VanishingExponentBudget
import RiemannResearch.RH.CRTReciprocalPowerObstruction

/-!
# Subpolynomial exact-head CRT criteria

Source: user-provided bounded-tail goal, 13 October 2026.
These conditional research reductions weaken boundedness to subpolynomial
energy or sparse finite certificates. No arithmetic provider is assumed proved.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto
open ZetaTwoProbability RiemannResearch.Analysis.SubpolynomialWindow

/-- Sparse finite certificates suffice. The head length and period may
depend on both epsilon and eta; no predetermined family is assumed. -/
theorem riemannHypothesis_of_squarefree_crt_power_infimum_zero
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η →
      ∃ (M L : ℕ) (F : ℕ → ℝ), Squarefree L ∧ F ∈ divisorResidueSpan L ∧
        (∀ n, 0 < n → n ≤ M → F n = 1) ∧
        crtTailEnergy M L F < η * ((M : ℝ) + 1) ^ ε) :
    RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hslt hz
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at hslt
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have ha : 0 < 2 * s.re - 1 := by linarith
  have hc : 0 < (2 * s.re - 1) / (zetaTwo * ‖s‖ ^ 2) :=
    div_pos ha (mul_pos zetaTwo_pos (pow_pos (norm_pos_iff.mpr hs0) 2))
  obtain ⟨M, L, F, hL, hF, hhead, henergy⟩ := hsmall _ ha _ hc
  exact (not_lt_of_ge (crtTailEnergy_power_lower_of_zeta_zero M L F
    (Nat.pos_of_ne_zero hL.ne_zero) hF hhead s hs hs1 hz)) henergy

/-- Subpolynomial finite tail energy is enough; uniform boundedness is not required. -/
theorem riemannHypothesis_of_squarefree_crt_subpolynomial_tail
    (M L : ℕ → ℕ) (F : ℕ → ℕ → ℝ)
    (hM : Tendsto M atTop atTop)
    (hL : ∀ j, Squarefree (L j))
    (hF : ∀ j, F j ∈ divisorResidueSpan (L j))
    (hhead : ∀ j n, 0 < n → n ≤ M j → F j n = 1)
    (hsub : Tendsto (fun j =>
      Real.log (1 + crtTailEnergy (M j) (L j) (F j)) /
        Real.log ((M j : ℝ) + 1)) atTop (𝓝 0)) :
    RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hslt hz
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at hslt
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have ha : 0 < 2 * s.re - 1 := by linarith
  have hc : 0 < (2 * s.re - 1) / (zetaTwo * ‖s‖ ^ 2) :=
    div_pos ha (mul_pos zetaTwo_pos (pow_pos (norm_pos_iff.mpr hs0) 2))
  have hx : Tendsto (fun j => (M j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun j => by dsimp; linarith)
      (tendsto_natCast_atTop_atTop.comp hM)
  apply no_positive_power_floor (fun j => (M j : ℝ) + 1)
    (fun j => crtTailEnergy (M j) (L j) (F j)) 1
    ((2 * s.re - 1) / (zetaTwo * ‖s‖ ^ 2)) (2 * s.re - 1)
    hx (fun j => crtTailEnergy_nonneg _ _ _) (by norm_num) hc ha hsub
  exact Eventually.of_forall (fun j =>
    (crtTailEnergy_power_lower_of_zeta_zero (M j) (L j) (F j)
      (Nat.pos_of_ne_zero (hL j).ne_zero) (hF j) (hhead j) s hs hs1 hz).trans
      (by linarith))

/-- A countable collection of single finite certificates suffices. -/
theorem riemannHypothesis_of_squarefree_crt_reciprocal_exponents
    (htrial : ∀ j : ℕ, ∃ (M L : ℕ) (F : ℕ → ℝ),
      j + 1 ≤ M ∧ Squarefree L ∧ F ∈ divisorResidueSpan L ∧
      (∀ n, 0 < n → n ≤ M → F n = 1) ∧
      crtTailEnergy M L F ≤ ((M : ℝ) + 1) ^ (1 / ((j : ℝ) + 1))) :
    RiemannHypothesis := by
  choose M L F hM hL hF hhead henergy using htrial
  have hcofinal : Tendsto M atTop atTop :=
    tendsto_atTop_mono (fun j => by change j ≤ M j; have := hM j; omega) tendsto_id
  apply riemannHypothesis_of_squarefree_crt_subpolynomial_tail
    M L F hcofinal hL hF hhead
  apply relativeLog_tendsto_zero_of_reciprocal_exponent
    (fun j => (M j : ℝ) + 1) (fun j => crtTailEnergy (M j) (L j) (F j))
  · intro j
    have h : (j : ℝ) + 1 ≤ M j := by exact_mod_cast hM j
    linarith
  · intro j
    exact crtTailEnergy_nonneg _ _ _
  · exact henergy

end RiemannResearch.RH.Pareto
