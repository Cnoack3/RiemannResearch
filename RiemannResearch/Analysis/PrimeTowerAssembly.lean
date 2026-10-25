/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.PrimeTowerQuadratic
import RiemannResearch.Analysis.ActualDirichletPolynomialOffDiagonal
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Tactic.NormNum

/-!
# Arithmetic assembly of finite actual-zero prime-tower corrections

Source: user-provided Signed Quadratic Correction Research Note, Section 2.
The finite indexing and covariance assembly are unconditional algebra.
The actual-zero limit explicitly retains its analytic phase provider.
-/

noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiemannResearch.Analysis.PrimeTowerAssembly
open RiemannResearch.Fourier ActualDirichletPolynomialGram

def towerFrequency (i : ℕ × ℕ) : ℕ := i.1 ^ i.2

theorem prime_pow_not_dvd_of_ne (p q k l : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (hk : 0 < k) : ¬ p ^ k ∣ q ^ l := by
  intro hd
  have hpk : p ∣ p ^ k := dvd_pow_self p (Nat.ne_of_gt hk)
  have hpq : p ∣ q := hp.dvd_of_dvd_pow (dvd_trans hpk hd)
  exact hne ((hq.eq_one_or_self_of_dvd p hpq).resolve_left hp.ne_one)

theorem towerFrequency_injective_on (s : Finset (ℕ × ℕ))
    (hs : ∀ i ∈ s, i.1.Prime ∧ 0 < i.2) :
    Set.InjOn towerFrequency (↑s : Set (ℕ × ℕ)) := by
  intro i hi j hj heq
  have hpi := (hs i hi).1
  have hpj := (hs j hj).1
  have hbase : i.1 = j.1 := by
    by_contra hne
    exact prime_pow_not_dvd_of_ne i.1 j.1 i.2 j.2 hpi hpj hne (hs i hi).2
      (dvd_of_eq heq)
  have he : i.1 ^ i.2 = i.1 ^ j.2 := by simpa [towerFrequency, hbase] using heq
  have hexp : i.2 = j.2 := by
    rcases lt_trichotomy i.2 j.2 with h | h | h
    · exact False.elim ((Nat.pow_lt_pow_right hpi.one_lt h).ne he)
    · exact h
    · exact False.elim ((Nat.pow_lt_pow_right hpi.one_lt h).ne he.symm)
  exact Prod.ext hbase hexp

theorem primePowerCovarianceSignedEntry_distinct_towers
    (p q k l : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (hk : 0 < k) (hl : 0 < l) :
    primePowerCovarianceSignedEntry (p ^ k) (q ^ l) = 0 := by
  simp only [primePowerCovarianceSignedEntry,
    primePowerCovarianceSymmetricEntry_eq_zero_of_nondvd _ _
      (prime_pow_not_dvd_of_ne p q k l hp hq hne hk)
      (prime_pow_not_dvd_of_ne q p l k hq hp hne.symm hl),
    Complex.ofReal_zero, mul_zero]

def upperTowerTerm (a : ℕ → ℂ) (i j : ℕ × ℕ) : ℝ :=
  if i.1 = j.1 ∧ i.2 < j.2 then
    (Real.log i.1 / Real.sqrt (i.1 ^ (j.2 - i.2) : ℕ)) *
      (star (a (towerFrequency i)) * a (towerFrequency j)).re
  else 0

private theorem real_pair_swap (z w : ℂ) :
    (star z * w).re = (star w * z).re := by
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

private theorem real_pair_entry (z w : ℂ) (b : ℝ) :
    (star z * (b : ℂ) * w).re = b * (star z * w).re := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem tower_pair_real (a : ℕ → ℂ) (i j : ℕ × ℕ)
    (hi : i.1.Prime ∧ 0 < i.2) (hj : j.1.Prime ∧ 0 < j.2) :
    (star (a (towerFrequency i)) *
      primePowerCovarianceSignedEntry (towerFrequency i) (towerFrequency j) *
        a (towerFrequency j)).re =
      (-1 / (2 * Real.pi)) * (upperTowerTerm a i j + upperTowerTerm a j i) := by
  rcases i with ⟨p, k⟩
  rcases j with ⟨q, l⟩
  change p.Prime ∧ 0 < k at hi
  change q.Prime ∧ 0 < l at hj
  dsimp only [towerFrequency]
  by_cases hp : p = q
  · subst q
    rcases lt_trichotomy k l with h | h | h
    · have hn : ¬ l < k := not_lt_of_ge h.le
      rw [primePowerCovarianceSignedEntry_prime_pow p k l hi.1 h,
        real_pair_entry]
      simp [upperTowerTerm, towerFrequency, h, hn, mul_assoc]
    · subst l
      simp [primePowerCovarianceSignedEntry,
        primePowerCovarianceSymmetricEntry_diag (p ^ k) (pow_pos hi.1.pos k),
        upperTowerTerm, towerFrequency]
    · have hn : ¬ k < l := not_lt_of_ge h.le
      have hsym : primePowerCovarianceSignedEntry (p ^ k) (p ^ l) =
          primePowerCovarianceSignedEntry (p ^ l) (p ^ k) := by
        unfold primePowerCovarianceSignedEntry
        rw [primePowerCovarianceSymmetricEntry_symm (p ^ k) (p ^ l)
          (pow_pos hi.1.pos k) (pow_pos hj.1.pos l)]
      rw [hsym, primePowerCovarianceSignedEntry_prime_pow p l k hi.1 h,
        real_pair_entry, real_pair_swap]
      simp [upperTowerTerm, towerFrequency, h, hn, mul_assoc]
  · have hqp : q ≠ p := Ne.symm hp
    rw [primePowerCovarianceSignedEntry_distinct_towers p q k l
      hi.1 hj.1 hp hi.2 hj.2]
    simp [upperTowerTerm, hp, hqp]

/-- The complete finite correction, including conjugate pairing and the factor two. -/
theorem tower_correction_eq (s : Finset (ℕ × ℕ)) (a : ℕ → ℂ)
    (hs : ∀ i ∈ s, i.1.Prime ∧ 0 < i.2) :
    (finiteGramErrorPairing (s.image towerFrequency) a primePowerCovarianceSignedEntry).re =
      (-1 / Real.pi) * ∑ i ∈ s, ∑ j ∈ s, upperTowerTerm a i j := by
  classical
  have hinj := towerFrequency_injective_on s hs
  have hswap : (∑ i ∈ s, ∑ j ∈ s, upperTowerTerm a j i) =
      ∑ i ∈ s, ∑ j ∈ s, upperTowerTerm a i j := Finset.sum_comm
  simp only [finiteGramErrorPairing, Finset.sum_image hinj, Complex.re_sum]
  calc
    _ = ∑ i ∈ s, ∑ j ∈ s,
        (-1 / (2 * Real.pi)) * (upperTowerTerm a i j + upperTowerTerm a j i) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact tower_pair_real a i j (hs i hi) (hs j hj)
    _ = (-1 / (2 * Real.pi)) *
        ((∑ i ∈ s, ∑ j ∈ s, upperTowerTerm a i j) +
          (∑ i ∈ s, ∑ j ∈ s, upperTowerTerm a j i)) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by rw [hswap]; ring

/-- Actual-zero consumer. The sole analytic premise is the stated phase limit. -/
theorem sampledSquare_tower_signed_limit_of_phase
    (s : Finset (ℕ × ℕ)) (a : ℕ → ℂ)
    (hs : ∀ i ∈ s, i.1.Prime ∧ 0 < i.2)
    (hphase : ∀ n ∈ s.image towerFrequency, ∀ m ∈ s.image towerFrequency, n ≠ m →
      Tendsto (fun T : ℝ => gramEntry T n m / (T : ℂ)) atTop
        (nhds (primePowerCovarianceSignedEntry n m))) :
    Tendsto (fun T : ℝ =>
      ((sampledSquare T (s.image towerFrequency) a -
        (Zeta23.Ncount 0 T : ℂ) *
          ∑ n ∈ s.image towerFrequency, star (a n) * a n) / (T : ℂ)).re)
      atTop (nhds ((-1 / Real.pi) * ∑ i ∈ s, ∑ j ∈ s, upperTowerTerm a i j)) := by
  have hpos : ∀ n ∈ s.image towerFrequency, 0 < n := by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    exact pow_pos (hs i hi).1.pos i.2
  have h := sampledSquare_signed_limit_of_phase (s.image towerFrequency) a hpos hphase
  have hr := (Complex.continuous_re.tendsto _).comp h
  rw [tower_correction_eq s a hs] at hr
  exact hr

end RiemannResearch.Analysis.PrimeTowerAssembly
