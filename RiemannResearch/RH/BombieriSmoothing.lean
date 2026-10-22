import Mathlib.Tactic.NormNum
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import RiemannResearch.RH.ParetoSmoothing
import RiemannResearch.Analysis.FiniteWeightedVariance
import Mathlib.Tactic.Positivity

/-!
# Bombieri's linear cutoff and its signed arithmetic remainder

Source: L. Báez-Duarte, *A strengthening of the Nyman–Beurling criterion for
 the Riemann hypothesis, 2*, arXiv:math/0205003v1 (2002), equation (3.1).
The paper proposes this taper for damped Möbius coefficients. The results below
specialize the repository's exact residue/divisor identity to that taper.
They retain every signed divisor term; they make no asymptotic or RH claim.
The energy is the finite head of the unnormalised Q energy. Full Q energy also
contains the infinite tail and has an additional factor 1 / zeta(2).
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto.BombieriSmoothing
noncomputable section

/-- Linear cutoff applied to any arithmetic coefficient sequence. -/
def weight (a : ArithmeticFunction ℝ) (N : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => a d * (1 - (d : ℝ) / (N : ℝ)), by simp⟩

/-- Scalar residue slope, including the conductor-one coefficient. -/
def slope (a : ArithmeticFunction ℝ) (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ioc 0 N, weight a N d / (d : ℝ)

/-- A finite legal residue sum. The conductor-one residue is identically zero. -/
def seed (a : ArithmeticFunction ℝ) (N k : ℕ) : ℝ :=
  -∑ d ∈ Finset.Ioc 0 N, weight a N d / (d : ℝ) * residue d k

/-- At cutoff two the linear taper kills the sole nonzero residue atom. -/
theorem seed_two_eq_zero (a : ArithmeticFunction ℝ) (k : ℕ) :
    seed a 2 k = 0 := by
  have hs : Finset.Ioc 0 2 = {1, 2} := by decide
  simp [seed, weight, hs, residue, Nat.mod_one]

/-- Zeroth divisor moment. -/
def divisorSum (a : ArithmeticFunction ℝ) (k : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ioc 0 k, ∑ d ∈ m.divisors, a d

/-- Signed first divisor moment; this must not be discarded in energy estimates. -/
def divisorMoment (a : ArithmeticFunction ℝ) (k : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ioc 0 k, ∑ d ∈ m.divisors, a d * (d : ℝ)

private theorem weight_divisor_sum (a : ArithmeticFunction ℝ) (N m : ℕ) :
    (∑ d ∈ m.divisors, weight a N d) =
      (∑ d ∈ m.divisors, a d) -
        (∑ d ∈ m.divisors, a d * (d : ℝ)) / (N : ℝ) := by
  change (∑ d ∈ m.divisors, a d * (1 - (d : ℝ) / (N : ℝ))) = _
  simp_rw [mul_sub, mul_one, ← mul_div_assoc]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div]

/-- Exact head formula, also valid for arbitrary real damping of Möbius coefficients. -/
theorem seed_head (a : ArithmeticFunction ℝ) (N k : ℕ) (hkN : k ≤ N) :
    seed a N k = divisorSum a k - divisorMoment a k / (N : ℝ) -
      (k : ℝ) * slope a N := by
  unfold seed slope
  rw [finite_residue_divisor_identity _ N k hkN]
  simp_rw [weight_divisor_sum]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div]
  rfl

/-- No support is introduced at a conductor where the underlying coefficient vanishes. -/
theorem weight_eq_zero (a : ArithmeticFunction ℝ) (N d : ℕ) (hd : a d = 0) :
    weight a N d = 0 := by
  change a d * (1 - (d : ℝ) / (N : ℝ)) = 0
  rw [hd, zero_mul]

/-- An arbitrary damping of the actual Möbius coefficients. -/
def dampedMoebius (damping : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun d => (ArithmeticFunction.moebius d : ℝ) * damping d, by simp⟩

/-- Bombieri's damping a^(-epsilon) is a special case of the arithmetic head formula. -/
theorem damped_seed_head (damping : ℕ → ℝ) (N k : ℕ) (hkN : k ≤ N) :
    1 - seed (dampedMoebius damping) N k =
      1 - divisorSum (dampedMoebius damping) k +
        divisorMoment (dampedMoebius damping) k / (N : ℝ) +
          (k : ℝ) * slope (dampedMoebius damping) N := by
  rw [seed_head _ N k hkN]
  ring

/-- Smoothing and damping preserve squarefree support exactly. -/
theorem damped_weight_eq_zero_of_not_squarefree (damping : ℕ → ℝ) (N d : ℕ)
    (hd : ¬ Squarefree d) : weight (dampedMoebius damping) N d = 0 := by
  apply weight_eq_zero
  change (ArithmeticFunction.moebius d : ℝ) * damping d = 0
  simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd]

/-- The undamped Möbius coefficient, still including its conductor-one value. -/
def moebiusCoeff : ArithmeticFunction ℝ := dampedMoebius (fun _ => 1)

private theorem moebiusCoeff_apply (d : ℕ) :
    moebiusCoeff d = (ArithmeticFunction.moebius d : ℝ) := by
  simp [moebiusCoeff, dampedMoebius]

private theorem moebius_divisor_sum (m : ℕ) :
    (∑ d ∈ m.divisors, moebiusCoeff d) = if m = 1 then 1 else 0 := by
  simp_rw [moebiusCoeff_apply]
  have h := congrArg (fun f : ArithmeticFunction ℝ => f m)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simpa only [ArithmeticFunction.intCoe_apply, ArithmeticFunction.one_apply] using h

/-- The zeroth divisor moment collapses to one; the first does not. -/
theorem moebius_divisorSum (k : ℕ) (hk : 0 < k) :
    divisorSum moebiusCoeff k = 1 := by
  unfold divisorSum
  simp_rw [moebius_divisor_sum]
  have hk1 : 1 ≤ k := hk
  simp [Finset.mem_Ioc, hk1]

/-- A negative signed divisor moment, checked with kernel reduction. -/
theorem divisorMoment_three : divisorMoment moebiusCoeff 3 = -2 := by
  have h : (∑ m ∈ Finset.Ioc 0 3, ∑ d ∈ m.divisors,
      ArithmeticFunction.moebius d * (d : ℤ)) = -2 := by decide +kernel
  unfold divisorMoment
  simp_rw [moebiusCoeff_apply]
  exact_mod_cast h

/-- The moment becomes positive, so a uniform nonpositive-sign argument is false. -/
theorem divisorMoment_ninetyFive : divisorMoment moebiusCoeff 95 = 67 := by
  have h : (∑ m ∈ Finset.Ioc 0 95, ∑ d ∈ m.divisors,
      ArithmeticFunction.moebius d * (d : ℤ)) = 67 := by decide +kernel
  unfold divisorMoment
  simp_rw [moebiusCoeff_apply]
  exact_mod_cast h

/-- Exact error of the ordinary Cesàro-tapered Möbius candidate. -/
theorem moebius_seed_error (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N) :
    1 - seed moebiusCoeff N k =
      (k : ℝ) * slope moebiusCoeff N + divisorMoment moebiusCoeff k / (N : ℝ) := by
  rw [seed_head _ N k hkN, moebius_divisorSum k hk]
  ring

/-- The full signed finite-head Q energy. Both the mixed term and the moment square remain. -/
theorem moebius_head_q_energy (N H : ℕ) (hHN : H ≤ N) :
    (∑ k ∈ Finset.Ioc 0 H, (1 - seed moebiusCoeff N k) ^ 2 / (k : ℝ) ^ 2) =
      (H : ℝ) * slope moebiusCoeff N ^ 2 +
        (2 * slope moebiusCoeff N / (N : ℝ)) *
          (∑ k ∈ Finset.Ioc 0 H, divisorMoment moebiusCoeff k / (k : ℝ)) +
        (∑ k ∈ Finset.Ioc 0 H, (divisorMoment moebiusCoeff k / (k : ℝ)) ^ 2) /
          (N : ℝ) ^ 2 := by
  have hpoint (k : ℕ) (hk : k ∈ Finset.Ioc 0 H) :
      (1 - seed moebiusCoeff N k) ^ 2 / (k : ℝ) ^ 2 =
        slope moebiusCoeff N ^ 2 +
          (2 * slope moebiusCoeff N / (N : ℝ)) *
            (divisorMoment moebiusCoeff k / (k : ℝ)) +
          (divisorMoment moebiusCoeff k / (k : ℝ)) ^ 2 / (N : ℝ) ^ 2 := by
    have hkp := (Finset.mem_Ioc.mp hk).1
    have hkN := le_trans (Finset.mem_Ioc.mp hk).2 hHN
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hkp
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (lt_of_lt_of_le hkp hkN)
    rw [moebius_seed_error N k hkp hkN]
    field_simp [hk0, hN0]
    ring
  simp_rw [Finset.sum_congr rfl hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_div]
  simp

/-- The same energy as an exact variance plus a square. This exposes the best possible
scalar slope for the finite head without silently claiming any control of the tail. -/
theorem moebius_head_q_variance (N H : ℕ) (hH : 0 < H) (hHN : H ≤ N) :
    (∑ k ∈ Finset.Ioc 0 H, (1 - seed moebiusCoeff N k) ^ 2 / (k : ℝ) ^ 2) =
      (1 / (N : ℝ)) ^ 2 *
        RiemannResearch.Analysis.FiniteWeightedVariance.variance
          (Finset.Ioc 0 H) (fun _ => 1)
          (fun k => divisorMoment moebiusCoeff k / (k : ℝ)) +
      (H : ℝ) *
        ((1 / (N : ℝ)) *
          RiemannResearch.Analysis.FiniteWeightedVariance.mean
            (Finset.Ioc 0 H) (fun _ => 1)
            (fun k => divisorMoment moebiusCoeff k / (k : ℝ)) +
            slope moebiusCoeff N) ^ 2 := by
  have hmass : RiemannResearch.Analysis.FiniteWeightedVariance.mass
      (Finset.Ioc 0 H) (fun _ => 1) = (H : ℝ) := by
    simp [RiemannResearch.Analysis.FiniteWeightedVariance.mass]
  have hm0 : RiemannResearch.Analysis.FiniteWeightedVariance.mass
      (Finset.Ioc 0 H) (fun _ => 1) ≠ 0 := by
    rw [hmass]
    exact_mod_cast ne_of_gt hH
  calc
    _ = ∑ k ∈ Finset.Ioc 0 H, (1 : ℝ) *
        ((1 / (N : ℝ)) * (divisorMoment moebiusCoeff k / (k : ℝ)) +
          slope moebiusCoeff N) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkp := (Finset.mem_Ioc.mp hk).1
      have hkN := le_trans (Finset.mem_Ioc.mp hk).2 hHN
      have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hkp
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (lt_of_lt_of_le hkp hkN)
      rw [moebius_seed_error N k hkp hkN]
      field_simp [hk0, hN0]
      ring
    _ = _ := by
      simpa only [hmass] using
        RiemannResearch.Analysis.FiniteWeightedVariance.affine_energy
          (Finset.Ioc 0 H) (fun _ => 1)
          (fun k => divisorMoment moebiusCoeff k / (k : ℝ))
          (1 / (N : ℝ)) (slope moebiusCoeff N) hm0

/-- A finite-head obstruction valid independently of the scalar slope. -/
theorem moebius_head_q_variance_lower_bound (N H : ℕ) (hH : 0 < H) (hHN : H ≤ N) :
    (1 / (N : ℝ)) ^ 2 *
        RiemannResearch.Analysis.FiniteWeightedVariance.variance
          (Finset.Ioc 0 H) (fun _ => 1)
          (fun k => divisorMoment moebiusCoeff k / (k : ℝ)) ≤
      ∑ k ∈ Finset.Ioc 0 H, (1 - seed moebiusCoeff N k) ^ 2 / (k : ℝ) ^ 2 := by
  rw [moebius_head_q_variance N H hH hHN]
  exact le_add_of_nonneg_right (by positivity)

/-- Normalized signed arithmetic remainder, including the damping defect. -/
def remainderRatio (a : ArithmeticFunction ℝ) (N k : ℕ) : ℝ :=
  (1 - divisorSum a k + divisorMoment a k / (N : ℝ)) / (k : ℝ)

/-- Exact signed variance decomposition for every damped Bombieri candidate.
For the paper, take a(d)=mu(d)*d^(-epsilon). No damping defect is omitted. -/
theorem head_q_variance (a : ArithmeticFunction ℝ) (N H : ℕ)
    (hH : 0 < H) (hHN : H ≤ N) :
    (∑ k ∈ Finset.Ioc 0 H, (1 - seed a N k) ^ 2 / (k : ℝ) ^ 2) =
      RiemannResearch.Analysis.FiniteWeightedVariance.variance
          (Finset.Ioc 0 H) (fun _ => 1) (remainderRatio a N) +
      (H : ℝ) *
        (RiemannResearch.Analysis.FiniteWeightedVariance.mean
            (Finset.Ioc 0 H) (fun _ => 1) (remainderRatio a N) + slope a N) ^ 2 := by
  have hmass : RiemannResearch.Analysis.FiniteWeightedVariance.mass
      (Finset.Ioc 0 H) (fun _ => 1) = (H : ℝ) := by
    simp [RiemannResearch.Analysis.FiniteWeightedVariance.mass]
  have hm0 : RiemannResearch.Analysis.FiniteWeightedVariance.mass
      (Finset.Ioc 0 H) (fun _ => 1) ≠ 0 := by
    rw [hmass]
    exact_mod_cast ne_of_gt hH
  calc
    _ = ∑ k ∈ Finset.Ioc 0 H, (1 : ℝ) * (remainderRatio a N k + slope a N) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkp := (Finset.mem_Ioc.mp hk).1
      have hkN := le_trans (Finset.mem_Ioc.mp hk).2 hHN
      have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hkp
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (lt_of_lt_of_le hkp hkN)
      rw [seed_head a N k hkN]
      unfold remainderRatio
      field_simp [hk0, hN0]
      ring
    _ = _ := by
      simpa only [hmass] using
        RiemannResearch.Analysis.FiniteWeightedVariance.translation_energy
          (Finset.Ioc 0 H) (fun _ => 1) (remainderRatio a N) (slope a N) hm0

end
end RiemannResearch.RH.Pareto.BombieriSmoothing
