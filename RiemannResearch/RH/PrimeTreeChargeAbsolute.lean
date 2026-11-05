import RiemannResearch.RH.SquarefreeRadicalDifference
import RiemannResearch.RH.ParetoResidueDuality
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.Analysis.PSeries

/-! # The absolute half-plane of the physical charge series

M. Balazard, *An arithmetical function related to Báez-Duarte’s criterion
for the Riemann hypothesis*, Propositions 8–9, DOI
10.1007/978-3-030-61887-2_3. Cauchy–Schwarz for the Hilbert coordinates,
followed by Möbius convolution, gives absolute convergence for Re(s)>3/2.
-/

noncomputable section
open scoped BigOperators LSeries.notation
namespace RiemannResearch.RH.PrimeTreeChargeAbsolute
open ZetaTwoHilbert Pareto

private theorem absolute_site (f : QHilbert) (σ : ℝ) (hσ : 3 / 2 < σ) :
    Summable (fun n : ℕ => |qSequence f n| / (n : ℝ) ^ σ) := by
  have hs := SquarefreeRadicalDifference.qNormalized_square_summable f
  have ht : Summable (fun n : ℕ => (n : ℝ) ^ (2 * (1 - σ))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ (hs.add ht)
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [qSequence_zero, abs_zero, zero_div, zero_pow (by decide : 2 ≠ 0), zero_add]
    positivity
  have hp : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hpow : (n : ℝ) ^ (2 * (1 - σ)) = ((n : ℝ) ^ (1 - σ)) ^ 2 := by
    rw [mul_comm, Real.rpow_mul hp.le, Real.rpow_two]
  have hmul : |qSequence f n| / (n : ℝ) ^ σ =
      (|qSequence f n| / (n : ℝ)) * (n : ℝ) ^ (1 - σ) := by
    rw [Real.rpow_sub hp, Real.rpow_one]
    field_simp [hp.ne']
  have hsquare : (qSequence f n / (n : ℝ)) ^ 2 =
      (|qSequence f n| / (n : ℝ)) ^ 2 := by rw [div_pow, div_pow, sq_abs]
  rw [hpow, hsquare, hmul]
  nlinarith [sq_nonneg (|qSequence f n| / (n : ℝ) - (n : ℝ) ^ (1 - σ)),
    sq_nonneg (|qSequence f n| / (n : ℝ)), sq_nonneg ((n : ℝ) ^ (1 - σ))]

theorem increments_summable (f : QHilbert) (s : ℂ) (hs : 3 / 2 < s.re) :
    LSeriesSummable (fun n : ℕ => ((qSequence f n - qSequence f (n - 1) : ℝ) : ℂ)) s := by
  let coeff (n : ℕ) : ℂ := ((qSequence f n - qSequence f (n - 1) : ℝ) : ℂ)
  change Summable (LSeries.term coeff s)
  rw [← summable_norm_iff]
  apply (summable_nat_add_iff 1).mp
  have hsite := absolute_site f s.re hs
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (((summable_nat_add_iff 1).mpr hsite).add hsite)
  intro n
  rw [LSeries.norm_term_eq, if_neg (Nat.succ_ne_zero n)]
  simp only [coeff, Nat.add_sub_cancel, Complex.norm_real, Real.norm_eq_abs, Pi.add_apply]
  by_cases hn : n = 0
  · simp [hn]
  have hp : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hpow : (n : ℝ) ^ s.re ≤ ((n + 1 : ℕ) : ℝ) ^ s.re :=
    Real.rpow_le_rpow hp.le (by exact_mod_cast Nat.le_succ n) (by linarith)
  calc
    _ ≤ (|qSequence f (n + 1)| + |qSequence f n|) / ((n + 1 : ℕ) : ℝ) ^ s.re :=
      div_le_div_of_nonneg_right (abs_sub _ _) (by positivity)
    _ ≤ _ := by
      rw [add_div]
      exact add_le_add le_rfl (div_le_div_of_nonneg_left (abs_nonneg _)
        (Real.rpow_pos_of_pos hp _) hpow)

theorem charge_summable_three_halves (f : QHilbert) (s : ℂ) (hs : 3 / 2 < s.re) :
    LSeriesSummable (fun n : ℕ => (mobiusDifference n (qSequence f) : ℂ)) s := by
  let a (n : ℕ) : ℂ := ((qSequence f n - qSequence f (n - 1) : ℝ) : ℂ)
  let b (n : ℕ) : ℂ := (ArithmeticFunction.moebius n : ℂ)
  have hB : LSeriesSummable b s := ArithmeticFunction.LSeriesSummable_moebius_iff.mpr (by linarith)
  have he (n : ℕ) : (a ⍟ b) n = (mobiusDifference n (qSequence f) : ℂ) := by
    rw [LSeries.convolution_def]
    dsimp only
    rw [Nat.sum_divisorsAntidiagonal (fun i j => a i * b j)]
    simp only [a, b, mobiusDifference, Complex.ofReal_sum, Complex.ofReal_mul,
      Complex.ofReal_sub, Complex.ofReal_intCast]
    apply Finset.sum_congr rfl
    intro k _
    ring
  apply (LSeriesSummable_congr s (fun {n} _ => he n)).mp
  exact (increments_summable f s hs).convolution hB

end RiemannResearch.RH.PrimeTreeChargeAbsolute
