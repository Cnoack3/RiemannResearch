import RiemannResearch.Analysis.MontgomeryResolventWeilTest
import RiemannResearch.Analysis.MontgomeryPrimeCrossIntegral

/-! # The two prime terms and the pole pair of the shifted Weil test -/

noncomputable section
open Complex
open scoped ArithmeticFunction
namespace RiemannResearch.Analysis.MontgomeryResolventPrimeTerms
open MontgomeryFiniteResolventSignal MontgomeryResolventWeilTest MontgomeryPrimeCrossIntegral

/-- The two actual prime weights associated to the nonsmooth Weil test. -/
theorem cutoffTest_prime_terms {u : ℝ} (hu : 0 ≤ u) (t : ℝ) (n : ℕ) :
    (((Λ n / Real.sqrt n : ℝ) : ℂ) *
      (cutoffTest u t (Real.log n) + cutoffTest u t (-Real.log n))) =
    Complex.exp ((t:ℂ)*I*u) *
      ((primeWeight (Real.exp u) n : ℂ) * Complex.exp (-(t:ℂ)*I*Real.log n) +
       (mangoldtThreeHalves n / Real.exp u : ℝ) * Complex.exp ((t:ℂ)*I*Real.log n)) := by
  by_cases hn : n=0
  · subst n; simp [primeWeight,mangoldtThreeHalves]
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have h1 : 1 ≤ (n:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hlog := Real.log_nonneg h1
  have hw : Real.exp (-|Real.log n-u|) = min ((n:ℝ)/Real.exp u) (Real.exp u/(n:ℝ)) := by
    have e1 : Real.exp (Real.log (n:ℝ)-u) = (n:ℝ)/Real.exp u := by rw [Real.exp_sub,Real.exp_log hn0]
    have e2 : Real.exp (-(Real.log (n:ℝ)-u)) = Real.exp u/(n:ℝ) := by
      rw [neg_sub,Real.exp_sub,Real.exp_log hn0]
    by_cases h : 0 ≤ Real.log n-u
    · rw [abs_of_nonneg h,← e1,← e2,min_eq_right ((Real.exp_le_exp).mpr (by linarith))]
    · rw [abs_of_nonpos (by linarith : Real.log n-u ≤ 0),neg_neg,← e1,← e2,
        min_eq_left ((Real.exp_le_exp).mpr (by linarith))]
  have hl : Real.exp (-|-(Real.log n)-u|) = (n:ℝ)⁻¹/(Real.exp u) := by
    rw [abs_of_nonpos (by linarith),neg_neg,Real.exp_sub,Real.exp_neg,Real.exp_log hn0]
  have hp : (n:ℝ)^(3/2:ℝ) = Real.sqrt n*n := by
    rw [show (3/2:ℝ) = 1/2+1 by norm_num,Real.rpow_add hn0,Real.rpow_one,← Real.sqrt_eq_rpow]
  have hp1 : -(t:ℂ)*I*((Real.log n : ℂ)-u) = (t:ℂ)*I*u + (-(t:ℂ)*I*Real.log n) := by ring
  have hp2 : -(t:ℂ)*I*((-Real.log n : ℝ)-u) = (t:ℂ)*I*u + ((t:ℂ)*I*Real.log n) := by push_cast; ring
  simp only [cutoffTest,primeWeight,mangoldtThreeHalves,hw,hl,hp,hp1,hp2,Complex.exp_add]
  push_cast
  ring

/-- Both actual pole evaluations on the right side of the literal Weil formula
have the uniform BGSTB pointwise envelope, including at height zero. -/
theorem norm_cutoffTest_pole_pair_le {u : ℝ} (hu : 0 ≤ u) (t : ℝ) :
    ‖Zeta23.paperFT (cutoffTest u t) (I/2) + Zeta23.paperFT (cutoffTest u t) (-I/2)‖ ≤
      16*Real.exp (u/2)/(1+t^2) := by
  have h0 : Zeta23.gammaOf (0:ℂ) = I/2 := by simp [Zeta23.gammaOf,Complex.div_I]; ring
  have h1 : Zeta23.gammaOf (1:ℂ) = -I/2 := by simp [Zeta23.gammaOf,Complex.div_I]; ring
  have hstrip {p : ℂ} (hp : |(p-1/2 : ℂ).re| ≤ 1/2) (him : p.im = 0) :
      ‖Zeta23.paperFT (cutoffTest u t) (Zeta23.gammaOf p)‖ ≤ Real.exp (u/2)*(8/(1+t^2)) := by
    rw [paperFT_cutoffTest _ _ _ (hp.trans_lt (by norm_num)),norm_mul]
    have he : ‖Complex.exp ((u:ℂ)*(p-1/2))‖ ≤ Real.exp (u/2) := by
      rw [Complex.norm_exp,Complex.re_ofReal_mul]
      apply Real.exp_le_exp.mpr
      exact (mul_le_mul_of_nonneg_left (abs_le.mp hp).2 hu).trans_eq (by ring)
    have hq := norm_rationalTerm_le (p-1/2) hp t
    have hpim : (p-1/2:ℂ).im = 0 := by norm_num [him]
    rw [hpim,zero_sub,neg_sq] at hq
    exact mul_le_mul he hq (norm_nonneg _) (Real.exp_pos _).le
  rw [← h0,← h1]
  apply (norm_add_le _ _).trans
  exact (add_le_add (hstrip (p := 0) (by norm_num) (by simp))
    (hstrip (p := 1) (by norm_num) (by simp))).trans_eq (by ring)

end RiemannResearch.Analysis.MontgomeryResolventPrimeTerms

namespace RiemannResearch.Analysis.MontgomeryResolventPrimeTerms

/--
info: 'RiemannResearch.Analysis.MontgomeryResolventPrimeTerms.cutoffTest_prime_terms' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cutoffTest_prime_terms

end RiemannResearch.Analysis.MontgomeryResolventPrimeTerms

namespace RiemannResearch.Analysis.MontgomeryResolventPrimeTerms

/--
info: 'RiemannResearch.Analysis.MontgomeryResolventPrimeTerms.norm_cutoffTest_pole_pair_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms norm_cutoffTest_pole_pair_le

end RiemannResearch.Analysis.MontgomeryResolventPrimeTerms
