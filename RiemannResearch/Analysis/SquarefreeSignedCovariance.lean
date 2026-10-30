/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualDirichletPolynomialOffDiagonal
import RiemannResearch.Analysis.HermitianQuadraticPerturbation
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.LinearCombination

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

theorem moebius_conjugates_squarefree_signedEntry
    (n m : ℕ) (hn : Squarefree n) (hm : Squarefree m) :
    (ArithmeticFunction.moebius n : ℂ) * (ArithmeticFunction.moebius m : ℂ) *
      primePowerCovarianceSignedEntry n m = -primePowerCovarianceSignedEntry n m := by
  have h := congrArg (fun x : ℝ => (x : ℂ))
    (squarefree_covariance_moebius n m hn hm)
  push_cast at h
  unfold primePowerCovarianceSignedEntry
  calc
    _ = ((-1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((primePowerCovarianceSymmetricEntry n m : ℂ) * (ArithmeticFunction.moebius n : ℂ) *
          (ArithmeticFunction.moebius m : ℂ)) := by ring
    _ = _ := by rw [h]; ring

theorem squarefree_signedPairing_moebius_twist
    (s : Finset ℕ) (hs : ∀ n ∈ s, Squarefree n) (a : ℕ → ℂ) :
    finiteGramErrorPairing s (fun n => (ArithmeticFunction.moebius n : ℂ) * a n)
      primePowerCovarianceSignedEntry =
      -finiteGramErrorPairing s a primePowerCovarianceSignedEntry := by
  unfold finiteGramErrorPairing
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [star_mul, star_intCast]
  calc
    _ = star (a n) * ((ArithmeticFunction.moebius n : ℂ) *
      (ArithmeticFunction.moebius m : ℂ) * primePowerCovarianceSignedEntry n m) * a m := by ring
    _ = _ := by rw [moebius_conjugates_squarefree_signedEntry n m (hs n hn) (hs m hm)]; ring

theorem squarefree_moebius_twist_normSq (s : Finset ℕ)
    (hs : ∀ n ∈ s, Squarefree n) (a : ℕ → ℂ) :
    (∑ n ∈ s, ‖(ArithmeticFunction.moebius n : ℂ) * a n‖ ^ 2) =
      ∑ n ∈ s, ‖a n‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [norm_mul, mul_pow]
  have hmu : ‖(ArithmeticFunction.moebius n : ℂ)‖ ^ 2 = 1 := by
    rw [← norm_pow]
    have hsq : (ArithmeticFunction.moebius n : ℂ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree (hs n hn)
    rw [hsq, norm_one]
  rw [hmu, one_mul]

theorem squarefree_signedEntry_anticommutes (n m : ℕ)
    (hn : Squarefree n) (hm : Squarefree m) :
    primePowerCovarianceSignedEntry n m * (ArithmeticFunction.moebius m : ℂ) =
      -(ArithmeticFunction.moebius n : ℂ) * primePowerCovarianceSignedEntry n m := by
  have h := moebius_conjugates_squarefree_signedEntry n m hn hm
  have hsq : (ArithmeticFunction.moebius n : ℂ) ^ 2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hn
  calc
    _ = (ArithmeticFunction.moebius n : ℂ) *
      ((ArithmeticFunction.moebius n : ℂ) * (ArithmeticFunction.moebius m : ℂ) *
        primePowerCovarianceSignedEntry n m) := by
      linear_combination -(primePowerCovarianceSignedEntry n m *
        (ArithmeticFunction.moebius m : ℂ)) * hsq
    _ = _ := by rw [h]; ring

theorem squarefree_signedAction_moebius_twist (s : Finset ℕ)
    (hs : ∀ n ∈ s, Squarefree n) (a : ℕ → ℂ) (n : ℕ) (hn : n ∈ s) :
    (∑ m ∈ s, primePowerCovarianceSignedEntry n m *
      ((ArithmeticFunction.moebius m : ℂ) * a m)) =
      -(ArithmeticFunction.moebius n : ℂ) *
        ∑ m ∈ s, primePowerCovarianceSignedEntry n m * a m := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← mul_assoc, squarefree_signedEntry_anticommutes n m (hs n hn) (hs m hm)]
  ring

theorem squarefree_signed_eigenvalue_reflection (s : Finset ℕ)
    (hs : ∀ n ∈ s, Squarefree n) (a : ℕ → ℂ) (ev : ℂ)
    (ha : ∀ n ∈ s, ∑ m ∈ s, primePowerCovarianceSignedEntry n m * a m = ev * a n) :
    ∀ n ∈ s, ∑ m ∈ s, primePowerCovarianceSignedEntry n m *
      ((ArithmeticFunction.moebius m : ℂ) * a m) =
      (-ev) * ((ArithmeticFunction.moebius n : ℂ) * a n) := by
  intro n hn
  rw [squarefree_signedAction_moebius_twist s hs a n hn, ha n hn]
  ring


theorem squarefree_moebius_twist_nonzero_iff (s : Finset ℕ)
    (hs : ∀ n ∈ s, Squarefree n) (a : ℕ → ℂ) :
    (∃ n ∈ s, (ArithmeticFunction.moebius n : ℂ) * a n ≠ 0) ↔
      ∃ n ∈ s, a n ≠ 0 := by
  constructor
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, (mul_ne_zero_iff.mp h).2⟩
  · rintro ⟨n, hn, h⟩
    refine ⟨n, hn, mul_ne_zero ?_ h⟩
    exact_mod_cast ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr (hs n hn)

theorem squarefree_signed_upper_iff_lower (s : Finset ℕ)
    (hs : ∀ n ∈ s, Squarefree n) (C : ℝ) :
    (∀ a : ℕ → ℂ,
      (finiteGramErrorPairing s a primePowerCovarianceSignedEntry).re ≤
        C * ∑ n ∈ s, ‖a n‖ ^ 2) ↔
    (∀ a : ℕ → ℂ,
      -(C * ∑ n ∈ s, ‖a n‖ ^ 2) ≤
        (finiteGramErrorPairing s a primePowerCovarianceSignedEntry).re) := by
  constructor
  · intro h a
    have ht := h (fun n => (ArithmeticFunction.moebius n : ℂ) * a n)
    rw [squarefree_signedPairing_moebius_twist s hs,
      squarefree_moebius_twist_normSq s hs, Complex.neg_re] at ht
    linarith
  · intro h a
    have ht := h (fun n => (ArithmeticFunction.moebius n : ℂ) * a n)
    rw [squarefree_signedPairing_moebius_twist s hs,
      squarefree_moebius_twist_normSq s hs, Complex.neg_re] at ht
    linarith


/-- A positive active prime-ratio edge makes a nonnegative Möbius profile strictly positive. -/
theorem realSignedCovariance_moebius_pos_of_edge (s : Finset ℕ)
    (hs : ∀ n ∈ s, Squarefree n) (b : ℕ → ℝ)
    (hb : ∀ n ∈ s, 0 ≤ b n) (n m : ℕ) (hn : n ∈ s) (hm : m ∈ s)
    (hW : 0 < primePowerCovarianceSymmetricEntry n m)
    (hbn : 0 < b n) (hbm : 0 < b m) :
    0 < realSignedCovariance s
      (fun n => (ArithmeticFunction.moebius n : ℝ) * b n) := by
  rw [realSignedCovariance_moebius s b hs]
  apply mul_pos (by positivity)
  have ht (i : ℕ) (hi : i ∈ s) (j : ℕ) (hj : j ∈ s) :
      0 ≤ primePowerCovarianceSymmetricEntry i j * b i * b j :=
    mul_nonneg (mul_nonneg (primePowerCovarianceSymmetricEntry_nonneg i j)
      (hb i hi)) (hb j hj)
  have hterm : 0 < primePowerCovarianceSymmetricEntry n m * b n * b m :=
    mul_pos (mul_pos hW hbn) hbm
  have hrow := Finset.single_le_sum (fun j hj => ht n hn j hj) hm
  have hall := Finset.single_le_sum
    (fun i hi => Finset.sum_nonneg (fun j hj => ht i hi j hj)) hn
  exact lt_of_lt_of_le (lt_of_lt_of_le hterm hrow) hall

/-- The full squarefree covariance retains the action defect and the exact
zero-diagonal quadratic remainder under arbitrary complex perturbations. -/
theorem squarefree_signed_perturbation_bound (s : Finset ℕ)
    (hs : ∀ n ∈ s, Squarefree n) (a h : ℕ → ℂ) (δ : ℕ → ℝ) (η : ℝ)
    (ha : ∀ n ∈ s, ‖∑ m ∈ s, primePowerCovarianceSignedEntry n m * a m‖ ≤ δ n)
    (hR : ∀ n ∈ s, ∀ m ∈ s, n ≠ m → ‖primePowerCovarianceSignedEntry n m‖ ≤ η) :
    |(finiteGramErrorPairing s (fun n => a n + h n) primePowerCovarianceSignedEntry).re -
      (finiteGramErrorPairing s a primePowerCovarianceSignedEntry).re| ≤
      2 * (∑ n ∈ s, ‖h n‖ * δ n) +
        η * ((∑ n ∈ s, ‖h n‖) ^ 2 - ∑ n ∈ s, ‖h n‖ ^ 2) := by
  have hstar (x : ℝ) : star (x : ℂ) = (x : ℂ) := by simp
  have hB : ∀ n ∈ s, ∀ m ∈ s,
      star (primePowerCovarianceSignedEntry n m) = primePowerCovarianceSignedEntry m n := by
    intro n hn m hm
    simp only [primePowerCovarianceSignedEntry, star_mul, hstar]
    rw [primePowerCovarianceSymmetricEntry_symm n m
      (Nat.pos_of_ne_zero (hs n hn).ne_zero) (Nat.pos_of_ne_zero (hs m hm).ne_zero)]
    ring
  have hdiag : ∀ n ∈ s, primePowerCovarianceSignedEntry n n = 0 := by
    intro n hn
    simp [primePowerCovarianceSignedEntry,
      primePowerCovarianceSymmetricEntry_diag n (Nat.pos_of_ne_zero (hs n hn).ne_zero)]
  have hquad : |kernelQuadratic s primePowerCovarianceSignedEntry h| ≤
      η * ((∑ n ∈ s, ‖h n‖) ^ 2 - ∑ n ∈ s, ‖h n‖ ^ 2) :=
    (Complex.abs_re_le_norm _).trans
      (finiteGramErrorPairing_norm_le_offDiagonal_mass s h
        primePowerCovarianceSignedEntry η hdiag hR)
  exact kernelQuadratic_perturbation_abs_bound s primePowerCovarianceSignedEntry
    a h δ _ hB ha hquad

end RiemannResearch.Fourier
