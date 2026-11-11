import RiemannResearch.Analysis.BoundedPrimeDegreeEnergy
import RiemannResearch.Analysis.PrimePowerCovarianceConjugation

/-!
Homogeneous prime-factor-degree blocks have identically zero arithmetic
prime-power covariance. This includes their diagonal and uses no squarefreeness.
-/

open scoped BigOperators
namespace RiemannResearch.Fourier

/-- Divisibility cannot change an integer within a fixed positive-degree block. -/
theorem primePowerCovarianceSymmetricEntry_eq_zero_of_primeDegree_eq
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hdeg : primeDegree n = primeDegree m) :
    primePowerCovarianceSymmetricEntry n m = 0 := by
  by_cases hnm : n = m
  · subst m
    exact primePowerCovarianceSymmetricEntry_diag n hn
  · apply primePowerCovarianceSymmetricEntry_eq_zero_of_nondvd
    · intro hd
      exact hnm (eq_of_dvd_of_primeDegree_eq (ne_of_gt hn) (ne_of_gt hm) hd hdeg)
    · intro hd
      exact hnm (eq_of_dvd_of_primeDegree_eq (ne_of_gt hm) (ne_of_gt hn) hd hdeg.symm).symm

/-- The signed quadratic arithmetic correction vanishes, coefficient by coefficient. -/
theorem homogeneous_primePowerCovariance_pairing_eq_zero
    (s : Finset ℕ) (a : ℕ → ℂ) (d : ℕ) (c : ℂ)
    (hs0 : ∀ n ∈ s, 0 < n) (hsd : ∀ n ∈ s, primeDegree n = d) :
    (∑ n ∈ s, ∑ m ∈ s, star (a n) *
      (c * (primePowerCovarianceSymmetricEntry n m : ℂ)) * a m) = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  apply Finset.sum_eq_zero
  intro m hm
  rw [primePowerCovarianceSymmetricEntry_eq_zero_of_primeDegree_eq
    (hs0 n hn) (hs0 m hm) ((hsd n hn).trans (hsd m hm).symm)]
  simp

end RiemannResearch.Fourier
