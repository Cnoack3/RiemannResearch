import RiemannResearch.Analysis.FiniteProfileEnergy
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual Mobius affine profiles
Source: user - provided "Exact - Head Green Profiles in the Nyman--Beurling Program",
27 July 2026, sections 4 and 7, agenda R5. The finite normal determinant is
strictly positive already at every integer cutoff x >= 2. The signed moment
is reduced exactly to two finite Mobius moments; no PNT is assumed.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.MobiusAffineProfile
open RiemannResearch.Analysis.FiniteProfileEnergy

def weight (d : ℕ) : ℝ := (ArithmeticFunction.moebius d : ℝ) ^ 2 / (d : ℝ)
def signedSum (x : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) * f d

theorem weight_nonneg (d : ℕ) : 0 ≤ weight d := by
  unfold weight
  positivity

theorem moebius_sq_le_one (d : ℕ) : (ArithmeticFunction.moebius d : ℝ) ^ 2 ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;> simp [h]

theorem weight_mul_moebius (d : ℕ) :
    weight d * (ArithmeticFunction.moebius d : ℝ) =
      (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) := by
  rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;> simp [weight, h, div_eq_mul_inv]

theorem pairing_eq_signedSum (x : ℕ) (f : ℕ → ℝ) :
    pairing (Finset.Icc 1 x) weight (fun d => (ArithmeticFunction.moebius d : ℝ)) f =
      signedSum x f := by
  unfold pairing signedSum
  simp_rw [weight_mul_moebius]

theorem profile_error_sq_le (x : ℕ) (b h : ℕ → ℝ) :
    (signedSum x b - signedSum x h) ^ 2 ≤
      mass (Finset.Icc 1 x) weight * energy (Finset.Icc 1 x) weight (fun d => b d - h d) := by
  simpa only [pairing_eq_signedSum] using signed_profile_error_sq_le
    (Finset.Icc 1 x) weight (fun d => (ArithmeticFunction.moebius d : ℝ)) b h
    (fun d _ => weight_nonneg d) (fun d _ => moebius_sq_le_one d)

/-- Strengthens "for all sufficiently large x" to every integer x >= 2. -/
theorem affine_determinant_pos (x : ℕ) (hx : 2 ≤ x) :
    0 < mass (Finset.Icc 1 x) weight *
      energy (Finset.Icc 1 x) weight (fun d => (d : ℝ)/(x : ℝ)) -
      (∑ d ∈ Finset.Icc 1 x, weight d * ((d : ℝ)/(x : ℝ))) ^ 2 := by
  apply RiemannResearch.Analysis.FiniteProfileEnergy.affine_determinant_pos
    (Finset.Icc 1 x) weight (fun d => (d : ℝ)/(x : ℝ))
    (fun d _ => weight_nonneg d) 1 2
  · exact Finset.mem_Icc.mpr ⟨by norm_num, le_trans (by norm_num) hx⟩
  · exact Finset.mem_Icc.mpr ⟨by norm_num, hx⟩
  · norm_num [weight, ArithmeticFunction.moebius_apply_one]
  · norm_num [weight, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  · have hx0 : (x : ℝ) ≠ 0 := by
      have : 0 < x := lt_of_lt_of_le (by norm_num) hx
      exact_mod_cast this.ne'
    intro he
    norm_num at he
    field_simp [hx0] at he
    norm_num at he

theorem affine_signed_moment (x : ℕ) (c0 c1 : ℝ) :
    signedSum x (fun d => c0 + c1 * ((d : ℝ)/(x : ℝ))) =
      c0 * (∑ d ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius d : ℝ)/(d : ℝ)) +
      (c1/(x : ℝ)) * (∑ d ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius d : ℝ)) := by
  unfold signedSum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : (d : ℝ) ≠ 0 := by
    have h := (Finset.mem_Icc.mp hd).1
    exact_mod_cast (show d ≠ 0 by omega)
  field_simp [hd0]


end RiemannResearch.RH.MobiusAffineProfile
