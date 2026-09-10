import RiemannResearch.RH.DampedMobiusSeed
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Genuine arithmetic coefficients for the signed Fourier energy

Source: the user-provided argument in
`FourierBridgeUniformSignedEnergy20260910.md`, Section 7.

This file treats the actual Möbius divisor coefficients, not a replacement
sequence. It proves their Euler product and the elementary epsilon-log bound.
The classical quantitative Mertens theorem, its uniform hyperbola consequence,
and the infinite weighted-energy summability are separate analytic obligations.
-/

open scoped BigOperators

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- The exact coefficient of `ζ(s) / ζ(s + ε)`. -/
def dampedDivisorCoefficient (ε : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, dampedMobiusWeight ε d

/-- The genuine signed Möbius weight as an arithmetic function. -/
def dampedMobiusArithmetic (ε : ℝ) : ArithmeticFunction ℝ where
  toFun := dampedMobiusWeight ε
  map_zero' := dampedMobiusWeight_zero ε

@[simp] theorem dampedMobiusArithmetic_apply (ε : ℝ) (n : ℕ) :
    dampedMobiusArithmetic ε n = dampedMobiusWeight ε n := rfl

theorem dampedMobiusArithmetic_multiplicative (ε : ℝ) :
    (dampedMobiusArithmetic ε).IsMultiplicative := by
  constructor
  · simp [dampedMobiusArithmetic, dampedMobiusWeight]
  · intro m n hmn
    simp only [dampedMobiusArithmetic_apply, dampedMobiusWeight]
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn,
      Int.cast_mul, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring

@[simp] theorem dampedDivisorCoefficient_zero (ε : ℝ) :
    dampedDivisorCoefficient ε 0 = 0 := by
  simp [dampedDivisorCoefficient]

@[simp] theorem dampedDivisorCoefficient_one (ε : ℝ) :
    dampedDivisorCoefficient ε 1 = 1 := by
  simp [dampedDivisorCoefficient, dampedMobiusWeight]

/-- Every nontrivial prime power has the same damped divisor coefficient. -/
theorem dampedDivisorCoefficient_prime_pow (ε : ℝ) {p : ℕ}
    (hp : p.Prime) (k : ℕ) :
    dampedDivisorCoefficient ε (p ^ (k + 1)) = 1 - (p : ℝ) ^ (-ε) := by
  have hsum (j : ℕ) :
      (∑ i ∈ Finset.range (j + 2), dampedMobiusWeight ε (p ^ i)) =
        1 - (p : ℝ) ^ (-ε) := by
    induction j with
    | zero =>
      simp [Finset.sum_range_succ, dampedMobiusWeight,
        ArithmeticFunction.moebius_apply_prime hp]
      ring
    | succ j ih =>
      rw [show j + 1 + 2 = (j + 2) + 1 by omega, Finset.sum_range_succ, ih]
      have hj : j + 2 ≠ 0 := by omega
      have hj1 : j + 2 ≠ 1 := by omega
      simp [dampedMobiusWeight, ArithmeticFunction.moebius_apply_prime_pow hp hj, hj1]
  simpa [dampedDivisorCoefficient, Nat.sum_divisors_prime_pow hp] using hsum k

/-- The Möbius convolution equals the Euler product for every positive integer. -/
theorem dampedDivisorCoefficient_eq_prime_product (ε : ℝ) {n : ℕ} (hn : n ≠ 0) :
    dampedDivisorCoefficient ε n =
      ∏ p ∈ n.primeFactors, (1 - (p : ℝ) ^ (-ε)) := by
  let F : ArithmeticFunction ℝ :=
    dampedMobiusArithmetic ε * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
  let G : ArithmeticFunction ℝ :=
    ArithmeticFunction.prodPrimeFactors (fun p => 1 - (p : ℝ) ^ (-ε))
  have hF : F.IsMultiplicative :=
    (dampedMobiusArithmetic_multiplicative ε).mul
      ArithmeticFunction.isMultiplicative_zeta.natCast
  have hG : G.IsMultiplicative :=
    ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  have hFG : F = G := by
    apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers F hF G hG).2
    intro p k hp
    cases k with
    | zero =>
      simpa only [pow_zero] using hF.map_one.trans hG.map_one.symm
    | succ k =>
      rw [show F (p ^ (k + 1)) = dampedDivisorCoefficient ε (p ^ (k + 1)) by
        change (dampedMobiusArithmetic ε *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) (p ^ (k + 1)) = _
        rw [ArithmeticFunction.coe_mul_zeta_apply]
        rfl]
      rw [dampedDivisorCoefficient_prime_pow ε hp k]
      simp [G, ArithmeticFunction.prodPrimeFactors_apply
        (pow_ne_zero (k + 1) hp.ne_zero),
        Nat.primeFactors_prime_pow (by omega : k + 1 ≠ 0) hp]
  calc
    dampedDivisorCoefficient ε n = F n := by
      change _ = (dampedMobiusArithmetic ε *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n
      rw [ArithmeticFunction.coe_mul_zeta_apply]
      rfl
    _ = G n := congrArg (fun f : ArithmeticFunction ℝ => f n) hFG
    _ = _ := ArithmeticFunction.prodPrimeFactors_apply hn

/-- Each Euler factor lies between zero and one for nonnegative damping. -/
theorem dampedPrimeFactor_bounds {ε : ℝ} (hε : 0 ≤ ε) {p : ℕ} (hp : p.Prime) :
    0 ≤ 1 - (p : ℝ) ^ (-ε) ∧ 1 - (p : ℝ) ^ (-ε) ≤ 1 := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  have hpow := Real.rpow_le_one_of_one_le_of_nonpos hp1 (neg_nonpos.mpr hε)
  have hnonneg := Real.rpow_nonneg (Nat.cast_nonneg p) (-ε)
  constructor <;> linarith

/-- Exact signed arithmetic cancellation supplies positivity. -/
theorem dampedDivisorCoefficient_nonneg {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    0 ≤ dampedDivisorCoefficient ε n := by
  by_cases hn : n = 0
  · simp [hn]
  rw [dampedDivisorCoefficient_eq_prime_product ε hn]
  exact Finset.prod_nonneg fun p hp =>
    (dampedPrimeFactor_bounds hε (Nat.prime_of_mem_primeFactors hp)).1

theorem dampedDivisorCoefficient_le_one {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    dampedDivisorCoefficient ε n ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  rw [dampedDivisorCoefficient_eq_prime_product ε hn]
  exact Finset.prod_le_one
    (fun p hp => (dampedPrimeFactor_bounds hε (Nat.prime_of_mem_primeFactors hp)).1)
    (fun p hp => (dampedPrimeFactor_bounds hε (Nat.prime_of_mem_primeFactors hp)).2)

/-- A single prime factor controls the whole nonnegative Euler product. -/
theorem dampedDivisorCoefficient_le_prime_factor {ε : ℝ} (hε : 0 ≤ ε)
    {n p : ℕ} (hp : p ∈ n.primeFactors) :
    dampedDivisorCoefficient ε n ≤ 1 - (p : ℝ) ^ (-ε) := by
  have hn : n ≠ 0 := (Nat.mem_primeFactors.mp hp).2.2
  rw [dampedDivisorCoefficient_eq_prime_product ε hn,
    ← Finset.mul_prod_erase n.primeFactors (fun p => 1 - (p : ℝ) ^ (-ε)) hp]
  have hrest :
      (∏ r ∈ n.primeFactors.erase p, (1 - (r : ℝ) ^ (-ε))) ≤ 1 :=
    Finset.prod_le_one
      (fun r hr => (dampedPrimeFactor_bounds hε
        (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hr))).1)
      (fun r hr => (dampedPrimeFactor_bounds hε
        (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hr))).2)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hrest
    (dampedPrimeFactor_bounds hε (Nat.prime_of_mem_primeFactors hp)).1

/-- The first-order exponential inequality gives the epsilon-log saving. -/
theorem dampedPrimeFactor_le_mul_log (ε : ℝ) {p : ℕ} (hp : p.Prime) :
    1 - (p : ℝ) ^ (-ε) ≤ ε * Real.log p := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  rw [Real.rpow_def_of_pos hp0]
  have h := Real.add_one_le_exp (Real.log (p : ℝ) * -ε)
  nlinarith

/-- The genuine Möbius divisor coefficient has a uniform epsilon-log bound. -/
theorem dampedDivisorCoefficient_le_mul_log {ε : ℝ} (hε : 0 ≤ ε)
    {n : ℕ} (hn : 2 ≤ n) :
    dampedDivisorCoefficient ε n ≤ ε * Real.log n := by
  have hn1 : n ≠ 1 := by omega
  have hn0 : n ≠ 0 := by omega
  let p := n.minFac
  have hp : p.Prime := Nat.minFac_prime hn1
  have hpd : p ∣ n := Nat.minFac_dvd n
  have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, hn0⟩
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpn : (p : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpd
  calc
    dampedDivisorCoefficient ε n ≤ 1 - (p : ℝ) ^ (-ε) :=
      dampedDivisorCoefficient_le_prime_factor hε hmem
    _ ≤ ε * Real.log p := dampedPrimeFactor_le_mul_log ε hp
    _ ≤ ε * Real.log n := mul_le_mul_of_nonneg_left (Real.log_le_log hp0 hpn) hε

/-- The actual coefficient after normalization and subtraction of the atom at one. -/
def normalizedSignedCoefficient (ε N : ℝ) (n : ℕ) : ℝ :=
  N * dampedDivisorCoefficient ε n - if n = 1 then 1 else 0

@[simp] theorem normalizedSignedCoefficient_one (ε N : ℝ) :
    normalizedSignedCoefficient ε N 1 = N - 1 := by
  simp [normalizedSignedCoefficient]

/-- Away from the distinguished atom the full signed coefficient is exactly `N α`. -/
theorem normalizedSignedCoefficient_of_ne_one (ε N : ℝ) {n : ℕ} (hn : n ≠ 1) :
    normalizedSignedCoefficient ε N n = N * dampedDivisorCoefficient ε n := by
  simp [normalizedSignedCoefficient, hn]

/-- The elementary pointwise input for the weighted square-energy bound. -/
theorem abs_normalizedSignedCoefficient_le_mul_log {ε N C : ℝ}
    (hε : 0 ≤ ε) (hN : |N| ≤ C) {n : ℕ} (hn : 2 ≤ n) :
    |normalizedSignedCoefficient ε N n| ≤ C * ε * Real.log n := by
  have hα := dampedDivisorCoefficient_nonneg hε n
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  rw [normalizedSignedCoefficient_of_ne_one ε N (by omega), abs_mul, abs_of_nonneg hα]
  calc
    |N| * dampedDivisorCoefficient ε n ≤
        C * dampedDivisorCoefficient ε n := mul_le_mul_of_nonneg_right hN hα
    _ ≤ C * (ε * Real.log n) := mul_le_mul_of_nonneg_left
      (dampedDivisorCoefficient_le_mul_log hε hn) (le_trans (abs_nonneg N) hN)
    _ = _ := by ring

end
end RiemannResearch.RH.Pareto
