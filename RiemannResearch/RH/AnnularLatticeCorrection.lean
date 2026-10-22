import RiemannResearch.RH.AnnularArithmeticWeight
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp

/-!
# Exact annular lattice correction
The second-Riesz polynomial sum gives the finite Bernoulli remainder exactly.
The annular filter cancels both the constant and reciprocal boundary terms.
Source: independently derived from the annular weight; the Bernoulli-remainder
strategy is classical Euler--Maclaurin summation (NIST DLMF 2.10(i)).
No arithmetic correlation estimate or Riemann Hypothesis is assumed.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH

def annularBernoulliCubic (t : ℝ) : ℝ := t^3 - (3/2:ℝ)*t^2 + t/2

def rieszTwoLattice (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (Nat.floor x), rieszTwoWeight ((n:ℝ)/x)

theorem sum_rieszTwoPolynomial (N : ℕ) (x : ℝ) :
    (∑ n ∈ Finset.Icc 1 N, (1-(n:ℝ)/x)^2) =
      (N:ℝ) - (N:ℝ)*((N:ℝ)+1)/x +
        (N:ℝ)*((N:ℝ)+1)*(2*(N:ℝ)+1)/(6*x^2) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N+1), ih]
    push_cast
    ring

theorem fract_eq_sub_nat_floor {x : ℝ} (hx : 0 ≤ x) :
    Int.fract x = x - (Nat.floor x : ℝ) := by
  have hi : Int.floor x = (Nat.floor x : ℤ) :=
    Int.floor_eq_iff.mpr ⟨by simpa using Nat.floor_le hx,
      by simpa using Nat.lt_floor_add_one x⟩
  simp only [Int.fract, hi, Int.cast_natCast]

/-- The exact finite second-Riesz sum includes the fractional cutoff remainder. -/
theorem rieszTwoLattice_eq_bernoulli {x : ℝ} (hx : 0 < x) :
    rieszTwoLattice x = x/3 - 1/2 + 1/(6*x) -
      annularBernoulliCubic (Int.fract x)/(3*x^2) := by
  unfold rieszTwoLattice
  have he : (∑ n ∈ Finset.Icc 1 (Nat.floor x), rieszTwoWeight ((n:ℝ)/x)) =
      ∑ n ∈ Finset.Icc 1 (Nat.floor x), (1-(n:ℝ)/x)^2 := by
    apply Finset.sum_congr rfl
    intro n hn
    apply rieszTwoWeight_of_le_one
    apply (div_le_iff₀ hx).mpr
    have hnf : (n:ℝ) ≤ (Nat.floor x:ℝ) := by
      exact_mod_cast (Finset.mem_Icc.mp hn).2
    simpa only [one_mul] using hnf.trans (Nat.floor_le hx.le)
  rw [he, sum_rieszTwoPolynomial, fract_eq_sub_nat_floor hx.le]
  unfold annularBernoulliCubic
  field_simp [ne_of_gt hx]
  ring

theorem rieszTwoLattice_eq_fixed_cutoff {y x : ℝ}
    (hy : 0 < y) (hyx : y ≤ x) :
    rieszTwoLattice y =
      ∑ n ∈ Finset.Icc 1 (Nat.floor x), rieszTwoWeight ((n:ℝ)/y) := by
  unfold rieszTwoLattice
  apply Finset.sum_subset
  · intro n hn
    obtain ⟨hn1, hnf⟩ := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨hn1, hnf.trans (Nat.floor_mono hyx)⟩
  · intro n hn hnnot
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnf : Nat.floor y < n := by
      by_contra h
      exact hnnot (Finset.mem_Icc.mpr ⟨hn1, le_of_not_gt h⟩)
    apply rieszTwoWeight_of_one_le
    apply (le_div_iff₀ hy).mpr
    simpa only [one_mul] using (Nat.lt_of_floor_lt hnf).le

theorem annularLatticeSum_eq_scaledRieszTwo {x : ℝ} (hx : 0 < x) :
    (∑ n ∈ Finset.Icc 1 (Nat.floor x), annularArithmeticWeight ((n:ℝ)/x)) =
      rieszTwoLattice x - (7/4:ℝ)*rieszTwoLattice (x/2) +
        (7/8:ℝ)*rieszTwoLattice (x/4) - (1/8:ℝ)*rieszTwoLattice (x/8) := by
  rw [rieszTwoLattice_eq_fixed_cutoff (by positivity : 0 < x/2) (show x/2 ≤ x by linarith),
    rieszTwoLattice_eq_fixed_cutoff (by positivity : 0 < x/4) (show x/4 ≤ x by linarith),
    rieszTwoLattice_eq_fixed_cutoff (by positivity : 0 < x/8) (show x/8 ≤ x by linarith)]
  unfold rieszTwoLattice
  have hscale (n : ℕ) (d : ℝ) : (n:ℝ)/(x/d) = d*((n:ℝ)/x) := by
    rw [div_div_eq_mul_div]
    ring
  simp_rw [hscale]
  simp only [annularArithmeticWeight, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum]

def annularLatticeNumerator (x : ℝ) : ℝ :=
  -annularBernoulliCubic (Int.fract x) +
    7*annularBernoulliCubic (Int.fract (x/2)) -
    14*annularBernoulliCubic (Int.fract (x/4)) +
    8*annularBernoulliCubic (Int.fract (x/8))

/-- Exact all-real-cutoff formula, retaining every endpoint remainder. -/
theorem annularLatticeFinite_eq_bernoulli {x : ℝ} (hx : 0 < x) :
    annularLatticeFinite (Finset.Icc 1 (Nat.floor x)) x =
      annularLatticeNumerator x/(3*x^2) := by
  unfold annularLatticeFinite
  rw [annularLatticeSum_eq_scaledRieszTwo hx,
    rieszTwoLattice_eq_bernoulli hx,
    rieszTwoLattice_eq_bernoulli (by positivity : 0 < x/2),
    rieszTwoLattice_eq_bernoulli (by positivity : 0 < x/4),
    rieszTwoLattice_eq_bernoulli (by positivity : 0 < x/8)]
  unfold annularLatticeNumerator
  field_simp [ne_of_gt hx]
  ring

end RiemannResearch.RH
