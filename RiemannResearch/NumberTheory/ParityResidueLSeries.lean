import RiemannResearch.NumberTheory.ParityResidueConvolution
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Dirichlet series of the parity atom and its convolution square

The absolute-convergence hypothesis `1 < s.re` is retained. This is the ordinary
Dirichlet series, not the jump transform used in the Baez-Duarte/Balazard
closed-span criterion. The proof uses Mathlib's L-series convolution theorem.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.NumberTheory.ParityResidueLSeries
open DirichletExponential ParityResidueConvolution

def paritySeed (n : ℕ) : ℂ :=
  (if n = 1 then (1 / 2 : ℂ) else 0) - (if n = 2 then (1 / 2 : ℂ) else 0)

theorem paritySeed_hasSum (s : ℂ) :
    LSeriesHasSum paritySeed s ((1 / 2 : ℂ) * (1 - (2 : ℂ) ^ (-s))) := by
  have h := (hasSum_ite_eq 1 (1 / 2 : ℂ)).sub
    (hasSum_ite_eq 2 ((1 / 2 : ℂ) * (2 : ℂ) ^ (-s)))
  have he (n : ℕ) : LSeries.term paritySeed s n =
      (if n = 1 then (1 / 2 : ℂ) else 0) -
      (if n = 2 then (1 / 2 : ℂ) * (2 : ℂ) ^ (-s) else 0) := by
    rw [LSeries.term_def₀ (by norm_num [paritySeed])]
    by_cases h1 : n = 1
    · subst n
      simp [paritySeed]
    · by_cases h2 : n = 2
      · subst n
        simp [paritySeed]
      · simp [paritySeed, h1, h2]
  change HasSum _ _
  have hv : (1 / 2 : ℂ) - (1 / 2 : ℂ) * (2 : ℂ) ^ (-s) =
      (1 / 2 : ℂ) * (1 - (2 : ℂ) ^ (-s)) := by ring
  rw [hv] at h
  exact h.congr_fun he

theorem paritySeed_convolution_one :
    LSeries.convolution paritySeed (1 : ℕ → ℂ) = fun n => (residueAF 2 n : ℂ) := by
  funext n
  by_cases hn : n = 0
  · subst n
    simp
  · simp only [LSeries.convolution_def]
    rw [Nat.sum_divisorsAntidiagonal (fun a b => paritySeed a * (1 : ℕ → ℂ) b)]
    simp only [Pi.one_apply, mul_one, paritySeed, Finset.sum_sub_distrib]
    simp [Nat.mem_divisors, hn]
    rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
    · have hd : 2 ∣ n := Nat.dvd_of_mod_eq_zero h0
      simp [h0, hd]
    · have hd : ¬ 2 ∣ n := by
        intro hd
        have := Nat.mod_eq_zero_of_dvd hd
        omega
      simp [h1, hd]

theorem residue_two_hasSum {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n => (residueAF 2 n : ℂ)) s
      ((1 / 2 : ℂ) * (1 - (2 : ℂ) ^ (-s)) * riemannZeta s) := by
  have h := (paritySeed_hasSum s).convolution (LSeriesHasSum_one hs)
  simpa only [paritySeed_convolution_one] using h

theorem paritySquare_convolution_complex :
    LSeries.convolution (fun n => (residueAF 2 n : ℂ))
      (fun n => (residueAF 2 n : ℂ)) = fun n => (paritySquare n : ℂ) := by
  funext n
  rw [LSeries.convolution_def, paritySquare, ArithmeticFunction.mul_apply]
  push_cast
  rfl

theorem paritySquare_hasSum {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n => (paritySquare n : ℂ)) s
      ((1 / 4 : ℂ) * (1 - (2 : ℂ) ^ (-s)) ^ 2 * riemannZeta s ^ 2) := by
  have h := (residue_two_hasSum hs).convolution (residue_two_hasSum hs)
  rw [paritySquare_convolution_complex] at h
  convert h using 1
  ring

end RiemannResearch.NumberTheory.ParityResidueLSeries
