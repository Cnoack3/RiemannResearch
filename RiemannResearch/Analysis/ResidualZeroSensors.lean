import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.RH.ArithmeticZeroProjectionProof
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Tactic

/-!
# Actual residuals: blind zero values, informative derivatives, and energy cost

The zeta function, zero multiplicities, legal coefficients, Mellin integrals,
and approximation energy are the actual project/Mathlib definitions.
No Riemann hypothesis, zero-density estimate, or sampling limit is assumed.
The Mellin and projection results below reuse audited project proofs.
-/

noncomputable section
open Filter MeasureTheory Zeta23
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.ResidualZeroSensors
open RiemannResearch.RH.Pareto

/-- The numerator of the actual Mellin residual. -/
def residualNumerator (A : ℂ → ℂ) (s : ℂ) : ℂ := 1 - riemannZeta s * A s

@[simp] theorem residual_at_zero (A : ℂ → ℂ) (ρ : ℂ) (hρ : riemannZeta ρ = 0) :
    residualNumerator A ρ = 1 := by simp [residualNumerator, hρ]

theorem residual_values_independent (A B : ℂ → ℂ) (ρ : ℂ) (hρ : riemannZeta ρ = 0) :
    residualNumerator A ρ = residualNumerator B ρ := by simp [hρ]

/-- Even arbitrary weighted linear sensors at the full zeros cannot distinguish
legal correction numerators: every sampled value equals one. -/
theorem full_zero_weighted_samples (T : ℝ) (A w : ℂ → ℂ) :
    ActualZeroOrdinate.sum T (fun ρ => residualNumerator A ρ * w ρ) =
      ActualZeroOrdinate.sum T w := by
  unfold ActualZeroOrdinate.sum
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hz := (ActualZeroOrdinate.mem_cutoff.mp hρ).1.1
  simp [residualNumerator, hz]

/-- The complete multiplicity-weighted squared sample energy is N(T). -/
theorem full_zero_sample_energy (T : ℝ) (A : ℂ → ℂ) :
    ActualZeroOrdinate.realSum T (fun ρ => ‖residualNumerator A ρ‖ ^ 2) =
      (Ncount 0 T : ℝ) := by
  rw [← ActualZeroOrdinate.realSum_one T]
  unfold ActualZeroOrdinate.realSum
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hz := (ActualZeroOrdinate.mem_cutoff.mp hρ).1.1
  simp [residualNumerator, hz]

theorem full_zero_normalized_energy (T : ℝ) (hN : Ncount 0 T ≠ 0) (A : ℂ → ℂ) :
    ActualZeroOrdinate.realSum T (fun ρ => ‖residualNumerator A ρ‖ ^ 2) /
      (Ncount 0 T : ℝ) = 1 := by
  rw [full_zero_sample_energy]
  exact div_self (by exact_mod_cast hN)

/-- A general exact jet formula, with its regularity and vanishing assumptions
explicit. These are discharged for zeta zeros in `zeta_residual_jet` below. -/
theorem residual_jet_of_vanishing (f A : ℂ → ℂ) (ρ : ℂ) (m : ℕ)
    (hm : 0 < m) (hf : ContDiffAt ℂ m f ρ) (hA : ContDiffAt ℂ m A ρ)
    (hvan : ∀ j < m, iteratedDeriv j f ρ = 0) :
    iteratedDeriv m (fun s => 1 - f s * A s) ρ =
      -(iteratedDeriv m f ρ) * A ρ := by
  rw [iteratedDeriv_const_sub hm, iteratedDeriv_neg,
    show (fun s => f s * A s) = f * A from rfl, iteratedDeriv_mul hf hA]
  rw [Finset.sum_eq_single m]
  · simp
  · intro j hj hjm
    have hjlt : j < m := by have := Finset.mem_range.mp hj; omega
    simp [hvan j hjlt]
  · simp

/-- All earlier positive-order residual derivatives vanish. -/
theorem residual_lower_jet (f A : ℂ → ℂ) (ρ : ℂ) (j : ℕ)
    (hj : 0 < j) (hf : ContDiffAt ℂ j f ρ) (hA : ContDiffAt ℂ j A ρ)
    (hvan : ∀ i ≤ j, iteratedDeriv i f ρ = 0) :
    iteratedDeriv j (fun s => 1 - f s * A s) ρ = 0 := by
  rw [residual_jet_of_vanishing f A ρ j hj hf hA
    (fun i hi => hvan i (Nat.le_of_lt hi)), hvan j le_rfl]
  simp

lemma zeta_analytic_at_zero (ρ : ℂ) (hρ : IsNontrivialZero ρ) :
    AnalyticAt ℂ riemannZeta ρ :=
  Zeta23.riemannZeta_analyticOnNhd_compl_one ρ (by simpa using hρ.not_trivial.2)

/-- The order used here is the analytic multiplicity, not a postulated integer. -/
theorem zeta_lower_derivatives_zero (ρ : ℂ) (hρ : IsNontrivialZero ρ) :
    ∀ j < zeroMult ρ, iteratedDeriv j riemannZeta ρ = 0 := by
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (zeta_analytic_at_zero ρ hρ)).mp
  exact ENat.natCast_toNat_le_self _

/-- At the first potentially nonzero derivative, the correction A becomes visible. -/
theorem zeta_residual_jet (A : ℂ → ℂ) (ρ : ℂ) (hρ : IsNontrivialZero ρ)
    (hA : AnalyticAt ℂ A ρ) :
    iteratedDeriv (zeroMult ρ) (residualNumerator A) ρ =
      -(iteratedDeriv (zeroMult ρ) riemannZeta ρ) * A ρ := by
  exact residual_jet_of_vanishing riemannZeta A ρ (zeroMult ρ)
    (zetaSeam.one_le_mult ρ hρ) (zeta_analytic_at_zero ρ hρ).contDiffAt
    hA.contDiffAt (zeta_lower_derivatives_zero ρ hρ)

theorem zeta_residual_lower_jets (A : ℂ → ℂ) (ρ : ℂ) (hρ : IsNontrivialZero ρ)
    (hA : AnalyticAt ℂ A ρ) (j : ℕ) (hj : 0 < j) (hjm : j < zeroMult ρ) :
    iteratedDeriv j (residualNumerator A) ρ = 0 := by
  exact residual_lower_jet riemannZeta A ρ j hj (zeta_analytic_at_zero ρ hρ).contDiffAt
    hA.contDiffAt (fun i hi => zeta_lower_derivatives_zero ρ hρ i (lt_of_le_of_lt hi hjm))

/-- Genuine legal Mellin residuals have the fixed interpolation value 1/rho. -/
theorem legal_residual_mellin (c : ArithmeticCoefficients) (hc : ArithmeticCoefficientsLegal c)
    (ρ : ℂ) (hρ : IsNontrivialZero ρ) :
    (∫ x : ℝ in Set.Ioi 1, (1 - arithmeticStep c x) * (x : ℂ) ^ (-ρ - 1)) = 1 / ρ :=
  (arithmeticErrorMellin_at_zero c hc ρ hρ.1 hρ.2.1 hρ.2.2).2

/-- Two genuine legal corrections have identical Mellin residual values at each zero. -/
theorem legal_residual_mellin_independent (c d : ArithmeticCoefficients)
    (hc : ArithmeticCoefficientsLegal c) (hd : ArithmeticCoefficientsLegal d)
    (ρ : ℂ) (hρ : IsNontrivialZero ρ) :
    (∫ x : ℝ in Set.Ioi 1, (1 - arithmeticStep c x) * (x : ℂ) ^ (-ρ - 1)) =
      (∫ x : ℝ in Set.Ioi 1, (1 - arithmeticStep d x) * (x : ℂ) ^ (-ρ - 1)) := by
  rw [legal_residual_mellin c hc ρ hρ, legal_residual_mellin d hd ρ hρ]

/-- This is the exact energy obstruction for actual legal coefficients, obtained
from the project's already-proved signed projection identity. -/
theorem legal_residual_energy_lower_bound (c : ArithmeticCoefficients)
    (hc : ArithmeticCoefficientsLegal c) (ρ : ℂ) (hρ : IsNontrivialZero ρ)
    (hhalf : (1 / 2 : ℝ) < ρ.re) :
    (2 * ρ.re - 1) / ‖ρ‖ ^ 2 ≤ arithmeticFullError c := by
  rw [arithmeticZeroProjectionTarget ρ hρ.1 hhalf hρ.2.2 c hc]
  exact le_add_of_nonneg_right (integral_nonneg (fun x => div_nonneg (sq_nonneg _) (sq_nonneg _)))

/-- If a right-half-strip zero exists, no sequence of actual legal residuals
can have energy tending to zero. The hypothetical zero is an explicit premise. -/
theorem no_legal_energy_decay_at_offline_zero (ρ : ℂ) (hρ : IsNontrivialZero ρ)
    (hhalf : (1 / 2 : ℝ) < ρ.re) (c : ℕ → ArithmeticCoefficients)
    (hc : ∀ n, ArithmeticCoefficientsLegal (c n)) :
    ¬ Tendsto (fun n => arithmeticFullError (c n)) atTop (𝓝 0) := by
  intro hlim
  have hρ0 : ρ ≠ 0 := by intro hz; subst ρ; norm_num at hhalf
  have hpos : 0 < (2 * ρ.re - 1) / ‖ρ‖ ^ 2 :=
    div_pos (by linarith) (pow_pos (norm_pos_iff.mpr hρ0) 2)
  have hle : (2 * ρ.re - 1) / ‖ρ‖ ^ 2 ≤ 0 := ge_of_tendsto hlim
    (Filter.Eventually.of_forall (fun n => legal_residual_energy_lower_bound (c n) (hc n) ρ hρ hhalf))
  exact (not_le_of_gt hpos) hle

/-- At the actual analytic multiplicity, the zeta derivative is nonzero. -/
theorem zeta_multiplicity_derivative_ne_zero (ρ : ℂ) (hρ : IsNontrivialZero ρ) :
    iteratedDeriv (zeroMult ρ) riemannZeta ρ ≠ 0 := by
  intro hz
  have hvan : ∀ j < zeroMult ρ + 1, iteratedDeriv j riemannZeta ρ = 0 := by
    intro j hj
    by_cases hjm : j < zeroMult ρ
    · exact zeta_lower_derivatives_zero ρ hρ j hjm
    · have heq : j = zeroMult ρ := by omega
      simpa only [heq] using hz
  have hle := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (zeta_analytic_at_zero ρ hρ)).mpr hvan
  have hcast : (zeroMult ρ : ℕ∞) = analyticOrderAt riemannZeta ρ :=
    ENat.natCast_toNat (Zeta23.analyticOrderAt_riemannZeta_ne_top hρ.not_trivial.2)
  rw [← hcast] at hle
  have hbad : zeroMult ρ + 1 ≤ zeroMult ρ := by exact_mod_cast hle
  omega

/-- Derivative data, unlike zero values, recover the actual correction value. -/
theorem correction_recovered_from_jet (A : ℂ → ℂ) (ρ : ℂ) (hρ : IsNontrivialZero ρ)
    (hA : AnalyticAt ℂ A ρ) :
    -(iteratedDeriv (zeroMult ρ) (residualNumerator A) ρ) /
      iteratedDeriv (zeroMult ρ) riemannZeta ρ = A ρ := by
  rw [zeta_residual_jet A ρ hρ hA]
  field_simp [zeta_multiplicity_derivative_ne_zero ρ hρ]

lemma nat_cpow_symbol_analytic (n : ℕ) (hn : 0 < n) (ρ : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => (n : ℂ) ^ (1 - s)) ρ := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  simp_rw [Complex.cpow_def_of_ne_zero hn0]
  exact (analyticAt_const.mul (analyticAt_const.sub analyticAt_id)).cexp

/-- The required regularity is proved for the actual finite legal Mellin symbol. -/
theorem arithmetic_symbol_analytic (c : ArithmeticCoefficients)
    (hc : ArithmeticCoefficientsLegal c) (ρ : ℂ) :
    AnalyticAt ℂ (arithmeticMellinSymbol c) ρ := by
  unfold arithmeticMellinSymbol
  apply Finset.analyticAt_fun_sum
  intro p hp
  have hp1 : 0 < p.1 := by
    rcases (hc p hp).1 with h | h <;> simp [h]
  exact (analyticAt_const.mul (nat_cpow_symbol_analytic p.2 (hc p hp).2 ρ)).mul
    (analyticAt_const.sub (nat_cpow_symbol_analytic p.1 hp1 ρ))

/-- No auxiliary analyticity hypothesis remains for actual legal coefficients. -/
theorem legal_correction_recovered_from_jet (c : ArithmeticCoefficients)
    (hc : ArithmeticCoefficientsLegal c) (ρ : ℂ) (hρ : IsNontrivialZero ρ) :
    -(iteratedDeriv (zeroMult ρ) (residualNumerator (arithmeticMellinSymbol c)) ρ) /
      iteratedDeriv (zeroMult ρ) riemannZeta ρ = arithmeticMellinSymbol c ρ :=
  correction_recovered_from_jet _ ρ hρ (arithmetic_symbol_analytic c hc ρ)

end RiemannResearch.Analysis.ResidualZeroSensors
