/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.GapKernelQuadratics

/-!
# Bernstein subdivision on the compactified positive ray

Write t = x/(1+x). The right half of the unit interval corresponds to the
substitution x ↦ 1+2x on the physical ray. Reflection t ↦ 1-t reverses the
homogeneous coefficient list. Thus both half-intervals can be checked with
integer Horner arithmetic, without division by binomial coefficients.
This is the subdivision in BoundCertificateReplays20261119.md, expressed
in unnormalized Bernstein coefficients.
-/

namespace RiemannResearch.Analysis.GapKernelPolynomial

private theorem value_append (p q : List ℤ) (x : ℝ) :
    value (p ++ q) x = value p x + x ^ p.length * value q x := by
  induction p with
  | nil => simp [value]
  | cons a p ih =>
    simp only [List.cons_append, value, ih, List.length_cons, pow_succ]
    ring

private theorem reverse_identity (p : List ℤ) {x : ℝ} (hx : 0 < x) :
    x * value p.reverse x = x ^ p.length * value p x⁻¹ := by
  induction p with
  | nil => simp [value]
  | cons a p ih =>
    rw [List.reverse_cons, value_append, List.length_reverse, List.length_cons, pow_succ]
    simp only [value, mul_zero, add_zero]
    rw [mul_add, ih]
    field_simp [hx.ne'] <;> ring

private theorem reverse_positive (p : List ℤ) {x : ℝ} (hx : 0 < x) :
    0 < value p.reverse x ↔ 0 < value p x⁻¹ := by
  rw [← mul_pos_iff_of_pos_left hx, reverse_identity p hx, mul_pos_iff_of_pos_left (pow_pos hx _)]

/-- Homogenized coefficient list on the right dyadic half, in the ray variable. -/
def bernsteinRight : List ℤ → List ℤ
  | [] => []
  | a :: p =>
    let q := bernsteinRight p
    add [a] (add q (0 :: scale 2 q))

theorem value_bernsteinRight (p : List ℤ) (x : ℝ) :
    value (bernsteinRight p) x = value p (1 + 2 * x) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [bernsteinRight, value_add, value_scale, value, Int.cast_zero,
      Int.cast_ofNat, mul_zero, add_zero, zero_add, ih]
    ring

/-- All nonnegative coefficients certify an entire ray. Otherwise bisect in
the compact coordinate. Checking the constant also handles its zero endpoint. -/
def checkBernsteinRay : ℕ → List ℤ → Bool
  | 0, p => checkRay p
  | n + 1, p =>
    checkRay p || (decide (0 < p.headD 0) &&
      (checkBernsteinRay n (bernsteinRight p.reverse).reverse &&
       checkBernsteinRay n (bernsteinRight p)))

theorem checkBernsteinRay_sound (n : ℕ) (p : List ℤ) {x : ℝ}
    (hx : 0 ≤ x) (hc : checkBernsteinRay n p = true) : 0 < value p x := by
  induction n generalizing p x with
  | zero => exact checkRay_sound p hx hc
  | succ n ih =>
    simp only [checkBernsteinRay, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases hc with h | ⟨h₀, hl, hr⟩
    · exact checkRay_sound p hx h
    · rcases eq_or_lt_of_le hx with he | hpos
      · subst x
        rw [value_at_zero]
        exact Int.cast_pos.mpr h₀
      · by_cases hge : 1 ≤ x
        · have h := ih _ (x := (x - 1) / 2) (by linarith) hr
          rwa [value_bernsteinRight, show 1 + 2 * ((x - 1) / 2) = x by ring] at h
        · let v := (x⁻¹ - 1) / 2
          have hv : 0 < v := by
            have h : 1 < 1 / x := (lt_div_iff₀ hpos).mpr (by linarith only [not_le.mp hge])
            dsimp [v]
            rw [one_div] at h
            linarith
          have h := ih _ (inv_pos.mpr hv).le hl
          have h' := (reverse_positive (bernsteinRight p.reverse) (inv_pos.mpr hv)).mp h
          rw [inv_inv, value_bernsteinRight,
            show 1 + 2 * v = x⁻¹ by dsimp [v]; ring] at h'
          simpa only [inv_inv] using (reverse_positive p (inv_pos.mpr hpos)).mp h'

end RiemannResearch.Analysis.GapKernelPolynomial
