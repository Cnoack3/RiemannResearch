/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualDirichletPolynomialOffDiagonal
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Squarefree

/-!
# Actual squarefree coefficients in the signed covariance

Source: Signed_Quadratic_Correction_Research_Note.pdf, §§2 and 10.5.
The full arithmetic covariance is retained, including composite conductors.
Squarefree prime-power edges are prime edges. Möbius coefficients alternate
on every such edge, so their correction is positive rather than cancelling.
No assertion about legal projection convergence follows from this identity.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Fourier

theorem squarefree_ratio_prime_of_primePower {n m : ℕ}
    (hm : Squarefree m) (hd : n ∣ m) (hpp : IsPrimePow (m / n)) :
    (m / n).Prime :=
  Nat.squarefree_and_prime_pow_iff_prime.mp
    ⟨hm.squarefree_of_dvd (Nat.div_dvd_of_dvd hd), hpp⟩

theorem squarefree_prime_power_exponent {n p k : ℕ}
    (hn : Squarefree n) (hp : p.Prime) (hk : 0 < k) (hd : p ^ k ∣ n) :
    k = 1 :=
  ((Nat.squarefree_pow_iff hp.ne_one hk.ne').mp (hn.squarefree_of_dvd hd)).2

theorem moebius_squarefree_prime_edge (p n : ℕ) (hp : p.Prime)
    (hs : Squarefree (p * n)) :
    (ArithmeticFunction.moebius n : ℝ) *
      (ArithmeticFunction.moebius (p * n) : ℝ) = -1 := by
  have hpn : ¬ p ∣ n := by
    intro h
    exact (Nat.squarefree_iff_prime_squarefree.mp hs p hp)
      (Nat.mul_dvd_mul_left p h)
  have hmul : ArithmeticFunction.moebius (p * n) =
      -ArithmeticFunction.moebius n := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (hp.coprime_iff_not_dvd.mpr hpn), ArithmeticFunction.moebius_apply_prime hp]
    ring
  have hsq : (ArithmeticFunction.moebius n : ℝ) ^ 2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hs.of_mul_right
  rw [hmul]
  push_cast
  nlinarith

private theorem squarefree_covariance_moebius_of_lt (n m : ℕ)
    (hn : Squarefree n) (hm : Squarefree m) (hlt : n < m) :
    primePowerCovarianceSymmetricEntry n m *
      (ArithmeticFunction.moebius n : ℝ) * (ArithmeticFunction.moebius m : ℝ) =
        -primePowerCovarianceSymmetricEntry n m := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn.ne_zero
  by_cases hd : n ∣ m
  · by_cases hp : (m / n).Prime
    · have heq : m = (m / n) * n := (Nat.div_mul_cancel hd).symm
      have hmu : (ArithmeticFunction.moebius n : ℝ) *
          (ArithmeticFunction.moebius m : ℝ) = -1 := by
        rw [heq]
        apply moebius_squarefree_prime_edge _ _ hp
        simpa only [← heq] using hm
      calc
        _ = primePowerCovarianceSymmetricEntry n m *
            ((ArithmeticFunction.moebius n : ℝ) *
              (ArithmeticFunction.moebius m : ℝ)) := by ring
        _ = _ := by rw [hmu]; ring
    · have hpp : ¬ IsPrimePow (m / n) :=
        fun h => hp (squarefree_ratio_prime_of_primePower hm hd h)
      have hz : primePowerCovarianceSymmetricEntry n m = 0 := by
        rw [primePowerCovarianceSymmetricEntry_eq_of_lt_of_dvd n m hn0 hlt hd,
          ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp, zero_div]
      simp only [hz, zero_mul, neg_zero]
  · have hrev : ¬ m ∣ n := by
      intro h
      have := Nat.le_of_dvd hn0 h
      omega
    rw [primePowerCovarianceSymmetricEntry_eq_zero_of_nondvd n m hd hrev]
    simp

/-- The full covariance is anti-conjugated by Möbius signs on squarefree support. -/
theorem squarefree_covariance_moebius (n m : ℕ)
    (hn : Squarefree n) (hm : Squarefree m) :
    primePowerCovarianceSymmetricEntry n m *
      (ArithmeticFunction.moebius n : ℝ) * (ArithmeticFunction.moebius m : ℝ) =
        -primePowerCovarianceSymmetricEntry n m := by
  rcases lt_trichotomy n m with hlt | heq | hgt
  · exact squarefree_covariance_moebius_of_lt n m hn hm hlt
  · subst m
    rw [primePowerCovarianceSymmetricEntry_diag n (Nat.pos_of_ne_zero hn.ne_zero)]
    simp
  · rw [primePowerCovarianceSymmetricEntry_symm n m
      (Nat.pos_of_ne_zero hn.ne_zero) (Nat.pos_of_ne_zero hm.ne_zero)]
    convert squarefree_covariance_moebius_of_lt m n hm hn hgt using 1 <;> ring

def realSignedCovariance (s : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  -(1 / (2 * Real.pi)) * ∑ n ∈ s, ∑ m ∈ s,
    primePowerCovarianceSymmetricEntry n m * a n * a m

/-- Exact sign identity for arbitrary damped Möbius families, with all boundaries. -/
theorem realSignedCovariance_moebius (s : Finset ℕ) (f : ℕ → ℝ)
    (hs : ∀ n ∈ s, Squarefree n) :
    realSignedCovariance s (fun n => (ArithmeticFunction.moebius n : ℝ) * f n) =
      (1 / (2 * Real.pi)) * ∑ n ∈ s, ∑ m ∈ s,
        primePowerCovarianceSymmetricEntry n m * f n * f m := by
  have hterm (n : ℕ) (hn : n ∈ s) (m : ℕ) (hm : m ∈ s) :
      primePowerCovarianceSymmetricEntry n m *
          ((ArithmeticFunction.moebius n : ℝ) * f n) *
          ((ArithmeticFunction.moebius m : ℝ) * f m) =
        -(primePowerCovarianceSymmetricEntry n m * f n * f m) := by
    calc
      _ = (primePowerCovarianceSymmetricEntry n m *
        (ArithmeticFunction.moebius n : ℝ) * (ArithmeticFunction.moebius m : ℝ)) *
          (f n * f m) := by ring
      _ = _ := by rw [squarefree_covariance_moebius n m (hs n hn) (hs m hm)]; ring
  unfold realSignedCovariance
  have heq : (∑ n ∈ s, ∑ m ∈ s,
      primePowerCovarianceSymmetricEntry n m *
        ((ArithmeticFunction.moebius n : ℝ) * f n) *
        ((ArithmeticFunction.moebius m : ℝ) * f m)) =
      -(∑ n ∈ s, ∑ m ∈ s, primePowerCovarianceSymmetricEntry n m * f n * f m) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun m hm => hterm n hn m hm)
  rw [heq]
  ring

/-- Nonnegative damping gives a nonnegative signed correction on the entire
squarefree dictionary, not merely on its pure-prime vertices. -/
theorem realSignedCovariance_moebius_nonneg (s : Finset ℕ) (f : ℕ → ℝ)
    (hs : ∀ n ∈ s, Squarefree n) (hf : ∀ n ∈ s, 0 ≤ f n) :
    0 ≤ realSignedCovariance s (fun n => (ArithmeticFunction.moebius n : ℝ) * f n) := by
  rw [realSignedCovariance_moebius s f hs]
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro n hn
  apply Finset.sum_nonneg
  intro m hm
  exact mul_nonneg (mul_nonneg (primePowerCovarianceSymmetricEntry_nonneg n m)
    (hf n hn)) (hf m hm)

/-- Compatibility with the actual complex Gram pairing used by the phase consumer. -/
theorem finiteGramErrorPairing_realSignedCovariance (s : Finset ℕ) (a : ℕ → ℝ) :
    finiteGramErrorPairing s (fun n => (a n : ℂ)) primePowerCovarianceSignedEntry =
      (realSignedCovariance s a : ℂ) := by
  have hstar (x : ℝ) : star (x : ℂ) = (x : ℂ) := by simp
  unfold finiteGramErrorPairing primePowerCovarianceSignedEntry realSignedCovariance
  push_cast
  simp only [hstar]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

open RiemannResearch.Analysis.ActualDirichletPolynomialGram in
/-- Actual-zero phase consequence for the full squarefree Möbius family.
The phase provider is precisely the explicit hypothesis hphase. -/
theorem sampledSquare_squarefree_moebius_limit_of_phase
    (s : Finset ℕ) (f : ℕ → ℝ) (hs : ∀ n ∈ s, Squarefree n)
    (hphase : ∀ n ∈ s, ∀ m ∈ s, n ≠ m →
      Filter.Tendsto (fun T : ℝ => gramEntry T n m / (T : ℂ))
        Filter.atTop (nhds (primePowerCovarianceSignedEntry n m))) :
    let a : ℕ → ℂ := fun n => (((ArithmeticFunction.moebius n : ℝ) * f n : ℝ) : ℂ)
    Filter.Tendsto (fun T : ℝ =>
      (sampledSquare T s a -
        (Zeta23.Ncount 0 T : ℂ) * ∑ n ∈ s, star (a n) * a n) / (T : ℂ))
      Filter.atTop (nhds (((1 / (2 * Real.pi)) * ∑ n ∈ s, ∑ m ∈ s,
        primePowerCovarianceSymmetricEntry n m * f n * f m : ℝ) : ℂ)) := by
  have h := sampledSquare_signed_limit_of_phase s
    (fun n => (((ArithmeticFunction.moebius n : ℝ) * f n : ℝ) : ℂ))
    (fun n hn => Nat.pos_of_ne_zero (hs n hn).ne_zero) hphase
  rw [finiteGramErrorPairing_realSignedCovariance,
    realSignedCovariance_moebius s f hs] at h
  exact h

end RiemannResearch.Fourier
