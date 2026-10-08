import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Two radical-invariant backward differences have trivial common kernel

The argument uses the full exact identity at arbitrarily large powers. No
squarefreeness restriction on the base is needed: radical invariance at both
`a` and `a^(k+1)` supplies the required power invariance.

Source: independently developed extension of the user-directed exact
optimizer research continuation, 8 October 2026.

The analytic hypothesis is only `f(n)/n -> 0`; inverse-square summability
provides it. This module is an abstract sequence theorem and makes no claim
that either family separately solves an RH approximation problem.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis.RadicalDifferenceTotality

/-- Backward difference, with the natural predecessor convention at zero. -/
def backwardDifference (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  f n - f (n - 1)

/-- Backward difference after division by the integer index. -/
def quotientDifference (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  f n / (n : ℝ) - f (n - 1) / ((n - 1 : ℕ) : ℝ)

/-- Recover the complete normalized value from the two differences. -/
theorem normalized_value_of_two_differences
    {x y m A B : ℝ} (hm : m ≠ 0) (hm1 : m - 1 ≠ 0)
    (hA : x - y = A) (hB : x / m - y / (m - 1) = B) :
    x / m = A - (m - 1) * B := by
  have hy : y = x - A := by linarith
  rw [hy] at hB
  field_simp [hm, hm1] at hB
  apply (div_eq_iff hm).2
  nlinarith [hB]

/-- Both adjacent normalized values, retaining every affine term. -/
theorem adjacent_values_of_two_differences
    {x y m A B : ℝ} (hm : m ≠ 0) (hm1 : m - 1 ≠ 0)
    (hA : x - y = A) (hB : x / m - y / (m - 1) = B) :
    x / m = A - (m - 1) * B ∧ y / (m - 1) = A - m * B := by
  have hx := normalized_value_of_two_differences hm hm1 hA hB
  exact ⟨hx, by nlinarith [hx, hB]⟩

/-- A decaying sequence cannot be a nonconstant affine function of a
diverging real sequence. The constant part also vanishes. -/
theorem affine_power_amplification
    {q r : ℕ → ℝ} {A B : ℝ}
    (hq : Tendsto q atTop (𝓝 0)) (hr : Tendsto r atTop atTop)
    (h : ∀ k, q k = A - (r k - 1) * B) :
    A = 0 ∧ B = 0 := by
  have hinv : Tendsto (fun k => (r k)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hr
  have hnum : Tendsto (fun k => A + B - q k) atTop (𝓝 (A + B)) := by
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => A + B) atTop
        (𝓝 (A + B))).sub hq
  have hprod : Tendsto (fun k => (A + B - q k) * (r k)⁻¹)
      atTop (𝓝 0) := by
    simpa using hnum.mul hinv
  have heq : (fun k => (A + B - q k) * (r k)⁻¹) =ᶠ[atTop]
      (fun _ => B) := by
    filter_upwards [hr.eventually (eventually_gt_atTop (0 : ℝ))] with k hk
    have hne : r k ≠ 0 := ne_of_gt hk
    have hkform := h k
    field_simp [hne]
    nlinarith [hkform]
  have hB : B = 0 :=
    (tendsto_nhds_unique (hprod.congr' heq) tendsto_const_nhds).symm
  have heqA : q =ᶠ[atTop] (fun _ => A) :=
    Eventually.of_forall (fun k => by simpa [hB] using h k)
  have hA : A = 0 :=
    (tendsto_nhds_unique (hq.congr' heqA) tendsto_const_nhds).symm
  exact ⟨hA, hB⟩

/-- Squared inverse-index summability supplies the only decay input. -/
theorem normalized_tendsto_zero_of_summable
    {f : ℕ → ℝ} (hs : Summable (fun n => (f n / (n : ℝ)) ^ 2)) :
    Tendsto (fun n => f n / (n : ℝ)) atTop (𝓝 0) := by
  have hsq := hs.tendsto_atTop_zero
  have hroot : Tendsto (fun n => Real.sqrt ((f n / (n : ℝ)) ^ 2))
      atTop (𝓝 (Real.sqrt 0)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have hnorm : Tendsto (fun n => ‖f n / (n : ℝ)‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using hroot
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

/-- Power invariance of both differences forces every sequence value to
vanish when the normalized values tend to zero. -/
theorem zero_of_power_invariant_differences
    {f : ℕ → ℝ} (hf0 : f 0 = 0)
    (hf : Tendsto (fun n => f n / (n : ℝ)) atTop (𝓝 0))
    (hpower : ∀ a : ℕ, 2 ≤ a → ∀ k : ℕ,
      backwardDifference f (a ^ (k + 1)) = backwardDifference f a)
    (hqpower : ∀ a : ℕ, 2 ≤ a → ∀ k : ℕ,
      quotientDifference f (a ^ (k + 1)) = quotientDifference f a) :
    ∀ n, f n = 0 := by
  have hdiff : ∀ a : ℕ, 2 ≤ a →
      backwardDifference f a = 0 ∧ quotientDifference f a = 0 := by
    intro a ha
    let m : ℕ → ℕ := fun k => a ^ (k + 1)
    have hm : Tendsto m atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (by omega : 1 < a)).comp
        (tendsto_add_atTop_nat 1)
    have hr : Tendsto (fun k => (m k : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hm
    have hq : Tendsto (fun k => f (m k) / (m k : ℝ)) atTop (𝓝 0) :=
      hf.comp hm
    apply affine_power_amplification hq hr
    intro k
    have hmk : 2 ≤ m k :=
      le_trans ha (le_self_pow (by omega : 1 ≤ a) (Nat.succ_ne_zero k))
    have hmkR : (2 : ℝ) ≤ (m k : ℝ) := by exact_mod_cast hmk
    have hA : f (m k) - f (m k - 1) = backwardDifference f a :=
      hpower a ha k
    have hB : f (m k) / (m k : ℝ) -
        f (m k - 1) / ((m k - 1 : ℕ) : ℝ) = quotientDifference f a :=
      hqpower a ha k
    rw [Nat.cast_sub (by omega : 1 ≤ m k), Nat.cast_one] at hB
    exact normalized_value_of_two_differences (by linarith) (by linarith) hA hB
  have hf1 : f 1 = 0 := by
    have hA := (hdiff 2 (by omega)).1
    have hB := (hdiff 2 (by omega)).2
    norm_num [backwardDifference, quotientDifference] at hA hB
    linarith
  intro n
  induction n with
  | zero => exact hf0
  | succ n ih =>
      by_cases hn : n = 0
      · simpa [hn] using hf1
      · have hA : f (n + 1) - f n = 0 := by
          simpa [backwardDifference] using (hdiff (n + 1) (by omega)).1
        linarith

/-- Concrete radical invariance supplies power invariance exactly. -/
theorem zero_of_radical_invariant_differences
    {f : ℕ → ℝ} (hf0 : f 0 = 0)
    (hf : Tendsto (fun n => f n / (n : ℝ)) atTop (𝓝 0))
    (hrad : ∀ n : ℕ, 2 ≤ n → backwardDifference f n =
      backwardDifference f (UniqueFactorizationMonoid.radical n))
    (hqrad : ∀ n : ℕ, 2 ≤ n → quotientDifference f n =
      quotientDifference f (UniqueFactorizationMonoid.radical n)) :
    ∀ n, f n = 0 := by
  apply zero_of_power_invariant_differences hf0 hf
  · intro a ha k
    have hm : 2 ≤ a ^ (k + 1) :=
      le_trans ha (le_self_pow (by omega : 1 ≤ a) (Nat.succ_ne_zero k))
    calc
      backwardDifference f (a ^ (k + 1)) =
          backwardDifference f (UniqueFactorizationMonoid.radical (a ^ (k + 1))) :=
        hrad _ hm
      _ = backwardDifference f (UniqueFactorizationMonoid.radical a) := by
        rw [UniqueFactorizationMonoid.radical_pow a (Nat.succ_ne_zero k)]
      _ = backwardDifference f a := (hrad a ha).symm
  · intro a ha k
    have hm : 2 ≤ a ^ (k + 1) :=
      le_trans ha (le_self_pow (by omega : 1 ≤ a) (Nat.succ_ne_zero k))
    calc
      quotientDifference f (a ^ (k + 1)) =
          quotientDifference f (UniqueFactorizationMonoid.radical (a ^ (k + 1))) :=
        hqrad _ hm
      _ = quotientDifference f (UniqueFactorizationMonoid.radical a) := by
        rw [UniqueFactorizationMonoid.radical_pow a (Nat.succ_ne_zero k)]
      _ = quotientDifference f a := (hqrad a ha).symm

/-- Inverse-square version of the concrete common-kernel theorem. -/
theorem zero_of_summable_radical_invariant_differences
    {f : ℕ → ℝ} (hf0 : f 0 = 0)
    (hs : Summable (fun n => (f n / (n : ℝ)) ^ 2))
    (hrad : ∀ n : ℕ, 2 ≤ n → backwardDifference f n =
      backwardDifference f (UniqueFactorizationMonoid.radical n))
    (hqrad : ∀ n : ℕ, 2 ≤ n → quotientDifference f n =
      quotientDifference f (UniqueFactorizationMonoid.radical n)) :
    ∀ n, f n = 0 :=
  zero_of_radical_invariant_differences hf0
    (normalized_tendsto_zero_of_summable hs) hrad hqrad

end RiemannResearch.Analysis.RadicalDifferenceTotality
