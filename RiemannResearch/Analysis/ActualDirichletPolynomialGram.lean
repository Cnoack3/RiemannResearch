/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.Analysis.FrequencySensitiveGramBounds
import RiemannResearch.Analysis.GrowingPhaseCovarianceAssembly

/-!
# Exact actual-zero Dirichlet Gram forms and conditional moving remainders

Every sample is an actual zeta-zero ordinate with analytic multiplicity.
The polynomial and its exact Gram identity have no analytic hypotheses.
The FMZ-shaped error estimate is an explicit hypothesis: the sharp density
estimate from Ford--Meng--Zaharescu, arXiv:1511.06814, Lemmas 1--2, has not
been formalized by this module. The companion research note proves the paper-level application to
growing Mobius polynomials and records the remaining formalization boundary.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.ActualDirichletPolynomialGram
open ZeroOrdinate ActualZeroOrdinate RiemannResearch.Fourier

def polynomial (s : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ s, a n * phase (Real.log n) t

def gramEntry (T : ℝ) (n m : ℕ) : ℂ :=
  ordinateSum T (Real.log m - Real.log n)

def sampledSquare (T : ℝ) (s : Finset ℕ) (a : ℕ → ℂ) : ℂ :=
  ActualZeroOrdinate.sum T (fun ρ => star (polynomial s a ρ.im) * polynomial s a ρ.im)

/-- Complete finite equality, including every off-diagonal signed summand. -/
theorem sampledSquare_eq_gram (T : ℝ) (s : Finset ℕ) (a : ℕ → ℂ) :
    sampledSquare T s a = finiteGramErrorPairing s a (gramEntry T) := by
  have hp (t : ℝ) : star (polynomial s a t) * polynomial s a t =
      ∑ n ∈ s, ∑ m ∈ s, star (a n) * phase (Real.log m - Real.log n) t * a m := by
    simp only [polynomial, star_sum, star_mul, Finset.sum_mul_sum, phase_sub]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    ring
  simp only [sampledSquare, hp, ActualZeroOrdinate.sum, finiteGramErrorPairing,
    gramEntry, ordinateSum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro ρ hρ
  ring

theorem gramEntry_diag (T : ℝ) (n : ℕ) : gramEntry T n n = (Zeta23.Ncount 0 T : ℂ) := by
  simp [gramEntry, ordinateSum]

/-- The exact diagonal of the actual sampled quadratic form. -/
theorem diagonal_pairing (T : ℝ) (s : Finset ℕ) (a : ℕ → ℂ) :
    finiteGramErrorPairing s a (fun n m => if n = m then (Zeta23.Ncount 0 T : ℂ) else 0) =
      (Zeta23.Ncount 0 T : ℂ) * ∑ n ∈ s, star (a n) * a n := by
  classical
  simp only [finiteGramErrorPairing, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [if_pos hn]
  ring

/-- The arithmetic matrix remains signed. Only the remainder is estimated.
`hR` is a conditional analytic provider, not an established FMZ theorem in Lean. -/
theorem sampledSquare_prime_remainder_bound
    (T : ℝ) (s : Finset ℕ) (a : ℕ → ℂ) (η κ : ℝ)
    (hR : ∀ n ∈ s, ∀ m ∈ s,
      ‖gramEntry T n m - (if n = m then (Zeta23.Ncount 0 T : ℂ) else 0) -
        (T : ℂ) * primePowerCovarianceSignedEntry n m‖ ≤
        η + κ * (Real.log n - Real.log m) ^ 2) :
    ‖sampledSquare T s a -
      (Zeta23.Ncount 0 T : ℂ) * (∑ n ∈ s, star (a n) * a n) -
      finiteGramErrorPairing s a (fun n m => (T : ℂ) * primePowerCovarianceSignedEntry n m)‖ ≤
        η * (∑ n ∈ s, ‖a n‖) ^ 2 +
          κ * weightedFrequencySpread s (fun n => ‖a n‖) (fun n => Real.log n) := by
  classical
  let B : ℕ → ℕ → ℂ := fun n m => (T : ℂ) * primePowerCovarianceSignedEntry n m
  let D : ℕ → ℕ → ℂ := fun n m => if n = m then (Zeta23.Ncount 0 T : ℂ) else 0
  let R : ℕ → ℕ → ℂ := fun n m => gramEntry T n m - D n m - B n m
  have he := finiteGramErrorPairing_three_term_split s a (gramEntry T) D B R
    (fun n hn m hm => by dsimp [R]; ring)
  rw [sampledSquare_eq_gram, he, diagonal_pairing]
  have hc : ∀ x y z : ℂ, x + y + z - x - y = z := by intros; ring
  rw [hc]
  exact finiteGramErrorPairing_norm_le_frequencySpread s a R
    (fun n => Real.log n) η κ hR

end RiemannResearch.Analysis.ActualDirichletPolynomialGram
