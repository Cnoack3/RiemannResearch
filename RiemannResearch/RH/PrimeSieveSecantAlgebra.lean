/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Finite algebra for the two-cutoff prime-sieve obstruction

Source: user-directed research continuation, October 7, 2026; see
`IndependentPrimeResearchContinuation20261007.md`, equations (10), (14),
and (15), for the statements and their arithmetic interpretation. These are exact finite identities
and inequalities. The asymptotic Mertens input and the arithmetic
identification of the prime increments are not hypotheses discharged here.

-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.PrimeSieveSecant

theorem two_cutoff_secant_identity
    (a b A B : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    (a * (b * B) - b * (a * A)) / (a - b) =
      (B - A) / (1 / b - 1 / a) := by
  field_simp [ha, hb, sub_ne_zero.mpr hab]

theorem finite_secant_as_weighted_average
    {ι : Type*} (s : Finset ι) (u g : ι → ℝ) :
    (∑ i ∈ s, u i * g i) / (∑ i ∈ s, u i) =
      ∑ i ∈ s, (u i / (∑ j ∈ s, u j)) * g i := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem prime_increment_normalization
    (p a fOld fNew : ℝ) (ha : a ≠ 0) (hp : p ≠ 0)
    (hp1 : p - 1 ≠ 0) :
    fNew / (a * (1 - 1 / p)) - fOld / a =
      (1 / (a * (1 - 1 / p)) - 1 / a) *
        (p * fNew - (p - 1) * fOld) := by
  have hfactor : 1 - 1 / p ≠ 0 := by
    intro h
    have he : p - 1 = 0 := by
      have hm := congrArg (fun x : ℝ => x * p) h
      field_simp [hp] at hm
      linarith
    exact hp1 he
  (field_simp [ha, hp, hp1, hfactor]; ring)

/-- Signed affine combinations pay the full coefficient total variation. -/
theorem affine_mean_deviation_le
    {ι : Type*} (s : Finset ι) (c m : ι → ℝ) (L η : ℝ)
    (hc : (∑ i ∈ s, c i) = 1)
    (hm : ∀ i ∈ s, |m i - L| ≤ η) :
    |(∑ i ∈ s, c i * m i) - L| ≤ η * ∑ i ∈ s, |c i| := by
  have he : (∑ i ∈ s, c i * m i) - L =
      ∑ i ∈ s, c i * (m i - L) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hc]
    ring
  rw [he]
  calc
    _ ≤ ∑ i ∈ s, |c i * (m i - L)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, |c i| * |m i - L| := by simp only [abs_mul]
    _ ≤ ∑ i ∈ s, |c i| * η :=
      Finset.sum_le_sum (fun i hi =>
        mul_le_mul_of_nonneg_left (hm i hi) (abs_nonneg _))
    _ = η * ∑ i ∈ s, |c i| := by rw [← Finset.sum_mul]; ring

/-- A convex average of slopes in an η-band stays in the same band. -/
theorem convex_mean_deviation_le
    {ι : Type*} (s : Finset ι) (w m : ι → ℝ) (L η : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hunit : (∑ i ∈ s, w i) = 1)
    (hm : ∀ i ∈ s, |m i - L| ≤ η) :
    |(∑ i ∈ s, w i * m i) - L| ≤ η := by
  have h := affine_mean_deviation_le s w m L η hunit hm
  have habs : (∑ i ∈ s, |w i|) = 1 := by
    calc
      _ = ∑ i ∈ s, w i := Finset.sum_congr rfl
        (fun i hi => abs_of_nonneg (hw i hi))
      _ = 1 := hunit
  simpa only [habs, mul_one] using h

/-- The mean target one forces cancellation when the local slopes approach L. -/
theorem signed_variation_necessary
    {ι : Type*} (s : Finset ι) (c m : ι → ℝ) (L η τ : ℝ)
    (hc : (∑ i ∈ s, c i) = 1)
    (hm : ∀ i ∈ s, |m i - L| ≤ η)
    (htarget : |1 - ∑ i ∈ s, c i * m i| ≤ τ) :
    |1 - L| ≤ τ + η * ∑ i ∈ s, |c i| := by
  have h := affine_mean_deviation_le s c m L η hc hm
  calc
    _ = |(1 - ∑ i ∈ s, c i * m i) + ((∑ i ∈ s, c i * m i) - L)| := by
      congr 1
      ring
    _ ≤ |1 - ∑ i ∈ s, c i * m i| + |(∑ i ∈ s, c i * m i) - L| := abs_add_le _ _
    _ ≤ _ := add_le_add htarget h

/-! Exact secant subdivision for the moving prime-power sieve investigation,
20 October 2026. Source: independent finite algebra adapting the existing
reciprocal-slope strategy cited above. The asymptotic obstruction remains
an ordinary proof in TwoStageSieveObstructionResearch20261020.md. -/

def intercept (a b x y : ℝ) : ℝ := (a * y - b * x) / (a - b)

theorem intercept_split (a b c x y z : ℝ)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (hb : b ≠ 0) :
    intercept a c x z =
      (c * (a-b) / (b * (a-c))) * intercept a b x y +
      (a * (b-c) / (b * (a-c))) * intercept b c y z := by
  unfold intercept
  field_simp [sub_ne_zero.mpr hab, sub_ne_zero.mpr hbc, sub_ne_zero.mpr hac, hb]
  ring

theorem split_weights_sum (a b c : ℝ) (hac : a ≠ c) (hb : b ≠ 0) :
    c * (a-b) / (b * (a-c)) + a * (b-c) / (b * (a-c)) = 1 := by
  field_simp [sub_ne_zero.mpr hac, hb]
  ring

theorem intercept_abs_le_split (a b c x y z e : ℝ)
    (hc : 0 < c) (hbc : c < b) (hab : b < a)
    (hxy : |intercept a b x y| ≤ e)
    (hyz : |intercept b c y z| ≤ e) :
    |intercept a c x z| ≤ e := by
  have hb : 0 < b := lt_trans hc hbc
  have ha : 0 < a := lt_trans hb hab
  have hac : c < a := lt_trans hbc hab
  let α := c * (a-b) / (b * (a-c))
  let β := a * (b-c) / (b * (a-c))
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hsum : α + β = 1 := split_weights_sum a b c (ne_of_gt hac) (ne_of_gt hb)
  rw [intercept_split a b c x y z (ne_of_gt hab) (ne_of_gt hbc)
    (ne_of_gt hac) (ne_of_gt hb)]
  change |α * intercept a b x y + β * intercept b c y z| ≤ e
  calc
    _ ≤ |α * intercept a b x y| + |β * intercept b c y z| := abs_add_le _ _
    _ = α * |intercept a b x y| + β * |intercept b c y z| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hα, abs_of_nonneg hβ]
    _ ≤ α * e + β * e := add_le_add
      (mul_le_mul_of_nonneg_left hxy hα) (mul_le_mul_of_nonneg_left hyz hβ)
    _ = e := by rw [← add_mul, hsum, one_mul]

theorem intercept_abs_le_of_adjacent (a u : ℕ → ℝ)
    (hpos : ∀ k, 0 < a k) (hanti : StrictAnti a) (i : ℕ) (e : ℝ) :
    ∀ n : ℕ, 0 < n →
      (∀ k, i ≤ k → k < i+n →
        |intercept (a k) (a (k+1)) (u k) (u (k+1))| ≤ e) →
      |intercept (a i) (a (i+n)) (u i) (u (i+n))| ≤ e := by
  intro n
  induction n with
  | zero => intro hn; omega
  | succ n ih =>
    intro hn hadj
    by_cases hn0 : n = 0
    · subst n
      simpa using hadj i (le_refl i) (by omega)
    · have hnpos : 0 < n := by omega
      have hfirst := ih hnpos (fun k hk hl => hadj k hk (by omega))
      have hlast := hadj (i+n) (by omega) (by omega)
      have hr := intercept_abs_le_split (a i) (a (i+n)) (a (i+n+1))
        (u i) (u (i+n)) (u (i+n+1)) e
        (hpos _) (hanti (by omega)) (hanti (by omega)) hfirst hlast
      simpa [Nat.add_assoc] using hr

theorem intercept_euler_step (a t z q r : ℝ) (ha : a ≠ 0) (hq : q ≠ 0) :
    intercept a (a*(1-1/q)) (z*(t-a))
      (z*(t*(1-r)-a*(1-1/q))) = z*t*(1-q*r) := by
  have hd : a - a*(1-1/q) = a/q := by ring
  unfold intercept
  rw [hd]
  field_simp [ha, hq]
  ring


end RiemannResearch.RH.PrimeSieveSecant
