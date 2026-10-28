/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import RiemannResearch.NumberTheory.DivisorIncidence

/-!
# Exact finite Selberg mollifier optimization with its support cutoff

Source for the arithmetic optimization strategy: Simonic,
arXiv:1910.08274, Section 4.1, https://arxiv.org/html/1910.08274v2 .
The diagonal identity is also the explicit finite counterpart of the
project's general ProjectionMeanOne completion theorem.

Every squared residual and gcd-kernel off-diagonal term is retained. Mobius
inversion constructs the optimizer, proves its normalization, and preserves
the prescribed support n <= X. The factorial embedding removes the extra
divisors that would occur in a full-divisor-lattice relaxation.

The concrete totient specialization proves an attained minimum for the
ordinary gcd kernel with no unproved analytic premise. Its coefficient is
a_n/n in the classical critical-line mollifier notation. Generalized Jordan
weights and the uniform twisted zeta second moment remain separate work;
this finite theorem is not a zero-density provider.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.SelbergMollifier

/-- The finite reciprocal diagonal mass in Selberg's quadratic minimization. -/
def diagonalMass {ι : Type*} (s : Finset ι) (v μ : ι → ℝ) : ℝ :=
  ∑ i ∈ s, (μ i) ^ 2 / v i

/-- Exact finite diagonal completion, with the entire nonnegative residual.
This is the explicit scalar form needed after divisor diagonalization; the
general Hilbert-space projection identity also exists in ProjectionMeanOne. -/
theorem diagonal_completion {ι : Type*} (s : Finset ι) (v μ y : ι → ℝ)
    (hv : ∀ i ∈ s, v i ≠ 0) (hG : diagonalMass s v μ ≠ 0)
    (hy : ∑ i ∈ s, μ i * y i = 1) :
    (∑ i ∈ s, v i * (y i) ^ 2) =
      1 / diagonalMass s v μ +
        ∑ i ∈ s, v i * (y i - μ i / (v i * diagonalMass s v μ)) ^ 2 := by
  let G := diagonalMass s v μ
  have hterm (i : ι) (hi : i ∈ s) :
      v i * (y i - μ i / (v i * G)) ^ 2 =
        v i * (y i) ^ 2 - (2 / G) * (μ i * y i) +
          (1 / G ^ 2) * ((μ i) ^ 2 / v i) := by
    dsimp only [G]
    field_simp [hv i hi, hG]
    ring
  have hs : (∑ i ∈ s, v i * (y i - μ i / (v i * G)) ^ 2) =
      (∑ i ∈ s, v i * (y i) ^ 2) - 2 / G + 1 / G := by
    calc
      _ = ∑ i ∈ s, (v i * (y i) ^ 2 - (2 / G) * (μ i * y i) +
          (1 / G ^ 2) * ((μ i) ^ 2 / v i)) := Finset.sum_congr rfl hterm
      _ = (∑ i ∈ s, v i * (y i) ^ 2) - (2 / G) * 1 +
          (1 / G ^ 2) * G := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, hy]
        rfl
      _ = _ := by
        have hG' : G ≠ 0 := hG
        field_simp [hG']
  change (∑ i ∈ s, v i * (y i) ^ 2) = 1 / G + _
  rw [hs]
  ring

theorem diagonal_lower_bound {ι : Type*} (s : Finset ι) (v μ y : ι → ℝ)
    (hv : ∀ i ∈ s, 0 < v i) (hG : diagonalMass s v μ ≠ 0)
    (hy : ∑ i ∈ s, μ i * y i = 1) :
    1 / diagonalMass s v μ ≤ ∑ i ∈ s, v i * (y i) ^ 2 := by
  rw [diagonal_completion s v μ y (fun i hi => (hv i hi).ne') hG hy]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i hi =>
    mul_nonneg (hv i hi).le (sq_nonneg _))

/-- The candidate diagonal coordinates satisfy the normalization exactly. -/
theorem diagonal_optimizer_normalized {ι : Type*} (s : Finset ι) (v μ : ι → ℝ)
    (hG : diagonalMass s v μ ≠ 0) :
    (∑ i ∈ s, μ i * (μ i / (v i * diagonalMass s v μ))) = 1 := by
  have ht (i : ι) : μ i * (μ i / (v i * diagonalMass s v μ)) =
      ((μ i) ^ 2 / v i) / diagonalMass s v μ := by ring
  simp_rw [ht, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  simpa only [diagonalMass, div_eq_mul_inv] using (mul_inv_cancel₀ hG)

/-- Divisor coordinates of a finite mollifier supported on divisors of L. -/
def divisorCoordinate (L : ℕ) (coeff : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑ d ∈ L.divisors, if r ∣ d then coeff d else 0

/-- The Möbius normalization follows from the actual incidence inverse. -/
theorem divisorCoordinate_moebius_normalization (L : ℕ) (hL : L ≠ 0)
    (coeff : ℕ → ℝ) :
    (∑ r ∈ L.divisors, (ArithmeticFunction.moebius r : ℝ) *
      divisorCoordinate L coeff r) = coeff 1 := by
  classical
  have h1 : 1 ∈ L.divisors := Nat.mem_divisors.mpr ⟨one_dvd L, hL⟩
  calc
    _ = ∑ d ∈ L.divisors,
        (∑ r ∈ L.divisors,
          (ArithmeticFunction.moebius r : ℝ) * (if r ∣ d then (1 : ℝ) else 0)) * coeff d := by
      unfold divisorCoordinate
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      split_ifs <;> simp
    _ = ∑ d ∈ L.divisors, (if 1 = d then (1 : ℝ) else 0) * coeff d := by
      apply Finset.sum_congr rfl
      intro d hd
      congr 1
      simpa using RiemannResearch.NumberTheory.DivisorIncidence.moebius_left_inverse
        L 1 d h1 hd
    _ = coeff 1 := by simp [h1]

/-- An actual arithmetic divisor-kernel energy: generalized Jordan weights
can be inserted for v, giving the usual gcd-power mollifier kernel once their
divisor-sum identity has been established. -/
def divisorEnergy (L : ℕ) (v coeff : ℕ → ℝ) : ℝ :=
  ∑ r ∈ L.divisors, v r * (divisorCoordinate L coeff r) ^ 2

/-- Exact Selberg completion for divisor coordinates, with all residuals.
This proves the finite optimization step, not a zeta mean-square estimate. -/
theorem divisorEnergy_completion (L : ℕ) (hL : L ≠ 0) (v coeff : ℕ → ℝ)
    (hv : ∀ r ∈ L.divisors, v r ≠ 0)
    (hG : diagonalMass L.divisors v (fun r => (ArithmeticFunction.moebius r : ℝ)) ≠ 0)
    (hcoeff : coeff 1 = 1) :
    divisorEnergy L v coeff =
      1 / diagonalMass L.divisors v (fun r => (ArithmeticFunction.moebius r : ℝ)) +
        ∑ r ∈ L.divisors, v r *
          (divisorCoordinate L coeff r - (ArithmeticFunction.moebius r : ℝ) /
            (v r * diagonalMass L.divisors v
              (fun r => (ArithmeticFunction.moebius r : ℝ)))) ^ 2 := by
  apply diagonal_completion L.divisors v
    (fun r => (ArithmeticFunction.moebius r : ℝ)) (divisorCoordinate L coeff) hv hG
  rw [divisorCoordinate_moebius_normalization L hL coeff, hcoeff]

theorem sum_gcd_divisors_eq (L d e : ℕ) (v : ℕ → ℝ)
    (hd : d ∈ L.divisors) :
    (∑ r ∈ (Nat.gcd d e).divisors, v r) =
      ∑ r ∈ L.divisors, if r ∣ d ∧ r ∣ e then v r else 0 := by
  classical
  have hsets : (Nat.gcd d e).divisors =
      L.divisors.filter (fun r => r ∣ d ∧ r ∣ e) := by
    ext r
    constructor
    · intro hr
      have hrd : r ∣ d := (Nat.dvd_of_mem_divisors hr).trans (Nat.gcd_dvd_left d e)
      have hre : r ∣ e := (Nat.dvd_of_mem_divisors hr).trans (Nat.gcd_dvd_right d e)
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hrd.trans (Nat.dvd_of_mem_divisors hd),
          (Nat.mem_divisors.mp hd).2⟩, hrd, hre⟩
    · intro hr
      obtain ⟨_, hrd, hre⟩ := Finset.mem_filter.mp hr
      exact Nat.mem_divisors.mpr ⟨Nat.dvd_gcd hrd hre,
        (Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left d e) (Nat.pos_of_mem_divisors hd)).ne'⟩
  rw [hsets, Finset.sum_filter]

/-- Exact gcd-kernel diagonalization. No off-diagonal terms are dropped. -/
theorem gcdKernel_energy_eq (L : ℕ) (v coeff : ℕ → ℝ) :
    (∑ d ∈ L.divisors, ∑ e ∈ L.divisors,
      coeff d * coeff e * (∑ r ∈ (Nat.gcd d e).divisors, v r)) =
      divisorEnergy L v coeff := by
  classical
  calc
    _ = ∑ d ∈ L.divisors, ∑ e ∈ L.divisors, ∑ r ∈ L.divisors,
        v r * (if r ∣ d then coeff d else 0) * (if r ∣ e then coeff e else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      rw [sum_gcd_divisors_eq L d e v hd, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hrd : r ∣ d <;> by_cases hre : r ∣ e <;> simp [hrd, hre]
      ring
    _ = ∑ d ∈ L.divisors, ∑ r ∈ L.divisors, ∑ e ∈ L.divisors,
        v r * (if r ∣ d then coeff d else 0) * (if r ∣ e then coeff e else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact Finset.sum_comm
    _ = ∑ r ∈ L.divisors, ∑ d ∈ L.divisors, ∑ e ∈ L.divisors,
        v r * (if r ∣ d then coeff d else 0) * (if r ∣ e then coeff e else 0) :=
      Finset.sum_comm
    _ = divisorEnergy L v coeff := by
      unfold divisorEnergy divisorCoordinate
      apply Finset.sum_congr rfl
      intro r hr
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      rw [← Finset.mul_sum]
      ring


/-- Finite Möbius inversion of arbitrary divisor coordinates. -/
def divisorInverse (L : ℕ) (y : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ r ∈ L.divisors,
    (if d ∣ r then (ArithmeticFunction.moebius (r / d) : ℝ) else 0) * y r

theorem divisorCoordinate_inverse (L : ℕ) (y : ℕ → ℝ) (e : ℕ)
    (he : e ∈ L.divisors) :
    divisorCoordinate L (divisorInverse L y) e = y e := by
  classical
  calc
    _ = ∑ d ∈ L.divisors, ∑ r ∈ L.divisors,
        (if e ∣ d then (1 : ℝ) else 0) *
          (if d ∣ r then (ArithmeticFunction.moebius (r / d) : ℝ) else 0) * y r := by
      unfold divisorCoordinate divisorInverse
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hed : e ∣ d <;> simp [hed]
    _ = ∑ r ∈ L.divisors,
        (∑ d ∈ L.divisors, (if e ∣ d then (1 : ℝ) else 0) *
          (if d ∣ r then (ArithmeticFunction.moebius (r / d) : ℝ) else 0)) * y r := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_mul]
    _ = ∑ r ∈ L.divisors, (if e = r then (1 : ℝ) else 0) * y r := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [RiemannResearch.NumberTheory.DivisorIncidence.moebius_right_inverse L e r he hr]
    _ = y e := by simp [he]

def cutoffSet (L X : ℕ) : Finset ℕ := L.divisors.filter (fun r => r ≤ X)

def cutoffMass (L X : ℕ) (v : ℕ → ℝ) : ℝ :=
  diagonalMass (cutoffSet L X) v (fun r => (ArithmeticFunction.moebius r : ℝ))

def cutoffTarget (L X : ℕ) (v : ℕ → ℝ) (r : ℕ) : ℝ :=
  if r ≤ X then (ArithmeticFunction.moebius r : ℝ) / (v r * cutoffMass L X v) else 0

/-- Möbius inversion preserves the upper support cutoff because a nonzero
term requires d | r with r ≤ X. -/
def cutoffOptimizer (L X : ℕ) (v : ℕ → ℝ) : ℕ → ℝ :=
  divisorInverse L (cutoffTarget L X v)

theorem cutoffOptimizer_eq_zero_above (L X : ℕ) (v : ℕ → ℝ) (d : ℕ)
    (hd : X < d) : cutoffOptimizer L X v d = 0 := by
  classical
  unfold cutoffOptimizer divisorInverse
  apply Finset.sum_eq_zero
  intro r hr
  by_cases hdr : d ∣ r
  · have hXr : X < r := hd.trans_le (Nat.le_of_dvd (Nat.pos_of_mem_divisors hr) hdr)
    simp [cutoffTarget, not_le.mpr hXr]
  · simp [hdr]

theorem cutoffOptimizer_one (L X : ℕ) (v : ℕ → ℝ) (hG : cutoffMass L X v ≠ 0) :
    cutoffOptimizer L X v 1 = 1 := by
  classical
  have h := diagonal_optimizer_normalized (cutoffSet L X) v
    (fun r => (ArithmeticFunction.moebius r : ℝ)) hG
  unfold cutoffOptimizer divisorInverse cutoffTarget
  simp only [one_dvd, if_true, Nat.div_one, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  exact h

theorem divisorCoordinate_eq_zero_above (L X : ℕ) (coeff : ℕ → ℝ)
    (hcoeff : ∀ d, X < d → coeff d = 0) (r : ℕ) (hr : X < r) :
    divisorCoordinate L coeff r = 0 := by
  classical
  unfold divisorCoordinate
  apply Finset.sum_eq_zero
  intro d hd
  by_cases hrd : r ∣ d
  · simp only [if_pos hrd]
    exact hcoeff d (hr.trans_le (Nat.le_of_dvd (Nat.pos_of_mem_divisors hd) hrd))
  · simp [hrd]

/-- The exact energy identity on the prescribed cutoff, not a relaxation to
all divisors of L. Only coordinates r ≤ X remain, since the others vanish. -/
theorem cutoffEnergy_completion (L X : ℕ) (hL : L ≠ 0) (v coeff : ℕ → ℝ)
    (hv : ∀ r ∈ cutoffSet L X, v r ≠ 0) (hG : cutoffMass L X v ≠ 0)
    (hcoeff : ∀ d, X < d → coeff d = 0) (h1 : coeff 1 = 1) :
    divisorEnergy L v coeff = 1 / cutoffMass L X v +
      ∑ r ∈ cutoffSet L X, v r *
        (divisorCoordinate L coeff r -
          (ArithmeticFunction.moebius r : ℝ) / (v r * cutoffMass L X v)) ^ 2 := by
  classical
  have hnorm : (∑ r ∈ cutoffSet L X, (ArithmeticFunction.moebius r : ℝ) *
      divisorCoordinate L coeff r) = 1 := by
    have hfull := divisorCoordinate_moebius_normalization L hL coeff
    rw [h1] at hfull
    calc
      _ = ∑ r ∈ L.divisors, (ArithmeticFunction.moebius r : ℝ) *
          divisorCoordinate L coeff r := by
        rw [cutoffSet, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro r hr
        by_cases hXr : r ≤ X
        · simp [hXr]
        · rw [divisorCoordinate_eq_zero_above L X coeff hcoeff r (lt_of_not_ge hXr)]
          simp
      _ = 1 := hfull
  have henergy : divisorEnergy L v coeff =
      ∑ r ∈ cutoffSet L X, v r * (divisorCoordinate L coeff r) ^ 2 := by
    unfold divisorEnergy cutoffSet
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hXr : r ≤ X
    · simp [hXr]
    · rw [divisorCoordinate_eq_zero_above L X coeff hcoeff r (lt_of_not_ge hXr)]
      simp
  rw [henergy]
  exact diagonal_completion (cutoffSet L X) v
    (fun r => (ArithmeticFunction.moebius r : ℝ)) (divisorCoordinate L coeff) hv hG hnorm

theorem cutoffEnergy_lower_bound (L X : ℕ) (hL : L ≠ 0) (v coeff : ℕ → ℝ)
    (hv : ∀ r ∈ cutoffSet L X, 0 < v r) (hG : cutoffMass L X v ≠ 0)
    (hcoeff : ∀ d, X < d → coeff d = 0) (h1 : coeff 1 = 1) :
    1 / cutoffMass L X v ≤ divisorEnergy L v coeff := by
  rw [cutoffEnergy_completion L X hL v coeff
    (fun r hr => (hv r hr).ne') hG hcoeff h1]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun r hr =>
    mul_nonneg (hv r hr).le (sq_nonneg _))

/-- The cutoff minimum is attained, with support and normalization proved. -/
theorem cutoffEnergy_optimizer (L X : ℕ) (hL : L ≠ 0) (v : ℕ → ℝ)
    (hv : ∀ r ∈ cutoffSet L X, v r ≠ 0) (hG : cutoffMass L X v ≠ 0) :
    divisorEnergy L v (cutoffOptimizer L X v) = 1 / cutoffMass L X v := by
  rw [cutoffEnergy_completion L X hL v (cutoffOptimizer L X v) hv hG
    (cutoffOptimizer_eq_zero_above L X v) (cutoffOptimizer_one L X v hG)]
  suffices hzero : (∑ r ∈ cutoffSet L X, v r *
      (divisorCoordinate L (cutoffOptimizer L X v) r -
        (ArithmeticFunction.moebius r : ℝ) / (v r * cutoffMass L X v)) ^ 2) = 0 by
    rw [hzero, add_zero]
  apply Finset.sum_eq_zero
  intro r hr
  obtain ⟨hrL, hrX⟩ := Finset.mem_filter.mp hr
  rw [cutoffOptimizer, divisorCoordinate_inverse L (cutoffTarget L X v) r hrL]
  simp [cutoffTarget, hrX]

/-- Factorial embedding gives exactly the original cutoff 1 ≤ r ≤ X; extra
divisors of X! are removed by the cutoff mask. -/
theorem cutoffSet_factorial (X : ℕ) :
    cutoffSet (Nat.factorial X) X = Finset.Icc 1 X := by
  ext r
  constructor
  · intro hr
    obtain ⟨hrF, hrX⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hrF, hrX⟩
  · intro hr
    obtain ⟨hr1, hrX⟩ := Finset.mem_Icc.mp hr
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨Nat.dvd_factorial hr1 hrX, (Nat.factorial_pos X).ne'⟩, hrX⟩

/-- Thus the capacity is the conventional sum over the actual cutoff. -/
theorem cutoffMass_factorial (X : ℕ) (v : ℕ → ℝ) :
    cutoffMass (Nat.factorial X) X v =
      ∑ r ∈ Finset.Icc 1 X, (ArithmeticFunction.moebius r : ℝ) ^ 2 / v r := by
  unfold cutoffMass diagonalMass
  rw [cutoffSet_factorial]


/-- The concrete totient weights diagonalize the ordinary gcd kernel. -/
theorem gcd_energy_eq_totient (L : ℕ) (coeff : ℕ → ℝ) :
    (∑ d ∈ L.divisors, ∑ e ∈ L.divisors,
      coeff d * coeff e * (Nat.gcd d e : ℝ)) =
      divisorEnergy L (fun r => (Nat.totient r : ℝ)) coeff := by
  have ht (n : ℕ) : (∑ r ∈ n.divisors, (Nat.totient r : ℝ)) = (n : ℝ) := by
    exact_mod_cast Nat.sum_totient n
  simpa only [ht] using gcdKernel_energy_eq L (fun r => (Nat.totient r : ℝ)) coeff

theorem one_le_totient_cutoffMass (X : ℕ) (hX : 1 ≤ X) :
    1 ≤ cutoffMass (Nat.factorial X) X (fun r => (Nat.totient r : ℝ)) := by
  rw [cutoffMass_factorial]
  have h1 : 1 ∈ Finset.Icc 1 X := Finset.mem_Icc.mpr ⟨le_rfl, hX⟩
  calc
    1 = (ArithmeticFunction.moebius 1 : ℝ) ^ 2 / (Nat.totient 1 : ℝ) := by norm_num
    _ ≤ ∑ r ∈ Finset.Icc 1 X,
        (ArithmeticFunction.moebius r : ℝ) ^ 2 / (Nat.totient r : ℝ) :=
      Finset.single_le_sum
        (f := fun r : ℕ => (ArithmeticFunction.moebius r : ℝ) ^ 2 / (Nat.totient r : ℝ))
        (fun r hr => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) h1

/-- An unconditional actual-cutoff gcd minimizer. This finite theorem does
not estimate an integral involving zeta or imply a zero-density bound. -/
theorem totient_cutoff_optimizer (X : ℕ) (hX : 1 ≤ X) :
    let coeff := cutoffOptimizer (Nat.factorial X) X (fun r => (Nat.totient r : ℝ))
    coeff 1 = 1 ∧ (∀ d, X < d → coeff d = 0) ∧
      (∑ d ∈ (Nat.factorial X).divisors, ∑ e ∈ (Nat.factorial X).divisors,
        coeff d * coeff e * (Nat.gcd d e : ℝ)) =
        1 / (∑ r ∈ Finset.Icc 1 X,
          (ArithmeticFunction.moebius r : ℝ) ^ 2 / (Nat.totient r : ℝ)) := by
  have hG : cutoffMass (Nat.factorial X) X (fun r => (Nat.totient r : ℝ)) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_totient_cutoffMass X hX))
  refine ⟨cutoffOptimizer_one _ _ _ hG, cutoffOptimizer_eq_zero_above _ _ _, ?_⟩
  rw [gcd_energy_eq_totient, cutoffEnergy_optimizer _ _ (Nat.factorial_pos X).ne']
  · rw [cutoffMass_factorial]
  · intro r hr
    have hr0 : 0 < r := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hr).1
    exact_mod_cast (Nat.totient_pos.mpr hr0).ne'
  · exact hG

end RiemannResearch.Analysis.SelbergMollifier

#print axioms RiemannResearch.Analysis.SelbergMollifier.cutoffEnergy_completion
#print axioms RiemannResearch.Analysis.SelbergMollifier.totient_cutoff_optimizer
