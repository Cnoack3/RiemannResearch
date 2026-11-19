/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The optimized sparse-deletion exponent for low-support pair tests

In logarithmic coordinates, the rarity, Conrey–Baluyot and Ingham upper
bounds give affine costs with slopes zero, 8/7 and 4/3. A Fourier support
radius θ subtracts the cost 2θx. The first slope 8/7 is the supremum of
admissible fixed density exponents. The minimum computed here describes
the exponent available with any fixed positive loss in the power of log T.

The analytic ingredients are Lamzouri, arXiv:2611.14486, Lemmas 2.1 and 2.3
and Proposition 3.2, and Chourasiya–Simonič, arXiv:2507.15184, Theorem 1.
The declarations below prove the scalar optimization and its boundaries.
-/

noncomputable section
namespace RiemannResearch.Analysis.SparsePairDensity

/-- The upper envelope of the three decay rates at logarithmic mark height x. -/
def tailEnvelope (p x : ℝ) : ℝ := max p (max (8 / 7 * x) (4 / 3 * x - 2))

/-- The minimum after tilting by c; the application has c = 2θ. -/
def sparseExponent (p c : ℝ) : ℝ :=
  if p ≤ 12 then
    if c ≤ 8 / 7 then p * (1 - 7 * c / 8) else 12 - 21 * c / 2
  else p - 3 * c * (p + 2) / 4

private theorem crossing_minimum {E : ℝ → ℝ} {A B m n c v : ℝ}
    (hv : 0 ≤ v) (hm : m ≤ c) (hn : c ≤ n)
    (hl : ∀ x, A + m * x ≤ E x) (hr : ∀ x, B + n * x ≤ E x)
    (join : A + m * v = B + n * v) (attain : E v = A + m * v) :
    IsLeast ((fun x => E x - c * x) '' Set.Ici 0) (E v - c * v) := by
  refine ⟨⟨v, hv, rfl⟩, ?_⟩
  rintro _ ⟨x, _, rfl⟩
  rcases le_total x v with hx | hx
  · rw [attain]
    nlinarith only [hl x, mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr hx)]
  · rw [attain, join]
    nlinarith only [hr x, mul_nonneg (sub_nonneg.mpr hn) (sub_nonneg.mpr hx)]

private theorem rarity_le (p x : ℝ) : p ≤ tailEnvelope p x := le_max_left _ _

private theorem conrey_le (p x : ℝ) : 8 / 7 * x ≤ tailEnvelope p x :=
  (le_max_left _ _).trans (le_max_right _ _)

private theorem ingham_le (p x : ℝ) : 4 / 3 * x - 2 ≤ tailEnvelope p x :=
  (le_max_right _ _).trans (le_max_right _ _)

/-- The rarity and the Conrey–Baluyot term meet at x = 7p/8. -/
theorem minimum_of_moderate_rarity_low_support {p c : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 12) (hc : 0 ≤ c) (hc' : c ≤ 8 / 7) :
    IsLeast ((fun x => tailEnvelope p x - c * x) '' Set.Ici 0)
      (p * (1 - 7 * c / 8)) := by
  let v := 7 * p / 8
  have hv : 0 ≤ v := by dsimp [v]; linarith
  have he : tailEnvelope p v = p := by
    apply max_eq_left
    apply max_le <;> dsimp [v] <;> linarith
  have h := crossing_minimum (E := tailEnvelope p) (A := p) (B := 0)
    (m := 0) (n := 8 / 7) hv hc hc'
    (fun x => by simpa using rarity_le p x)
    (fun x => by simpa using conrey_le p x)
    (by dsimp [v]; ring) (by simpa using he)
  rw [he] at h
  convert h using 1
  dsimp [v]
  ring

/-- The two density estimates meet at x = 21/2 and share the value 12. -/
theorem minimum_of_moderate_rarity_high_support {p c : ℝ}
    (hp : p ≤ 12) (hc : 8 / 7 ≤ c) (hc' : c ≤ 4 / 3) :
    IsLeast ((fun x => tailEnvelope p x - c * x) '' Set.Ici 0)
      (12 - 21 * c / 2) := by
  have he : tailEnvelope p (21 / 2) = 12 := by
    unfold tailEnvelope
    norm_num
    exact hp
  have h := crossing_minimum (E := tailEnvelope p) (A := 0) (B := -2)
    (m := 8 / 7) (n := 4 / 3) (v := 21 / 2) (by norm_num) hc hc'
    (fun x => by simpa using conrey_le p x)
    (fun x => by simpa only [sub_eq_add_neg, add_comm] using ingham_le p x)
    (by norm_num) (by rw [he]; norm_num)
  rw [he] at h
  convert h using 1 <;> ring

/-- Above rarity 12, the rarity term meets Ingham at x = 3(p+2)/4. -/
theorem minimum_of_high_rarity {p c : ℝ}
    (hp : 12 ≤ p) (hc : 0 ≤ c) (hc' : c ≤ 4 / 3) :
    IsLeast ((fun x => tailEnvelope p x - c * x) '' Set.Ici 0)
      (p - 3 * c * (p + 2) / 4) := by
  let v := 3 * (p + 2) / 4
  have hv : 0 ≤ v := by dsimp [v]; linarith
  have he : tailEnvelope p v = p := by
    apply max_eq_left
    apply max_le <;> dsimp [v] <;> linarith
  have h := crossing_minimum (E := tailEnvelope p) (A := p) (B := -2)
    (m := 0) (n := 4 / 3) hv hc hc'
    (fun x => by simpa using rarity_le p x)
    (fun x => by simpa only [sub_eq_add_neg, add_comm] using ingham_le p x)
    (by dsimp [v]; ring) (by simpa using he)
  rw [he] at h
  convert h using 1
  dsimp [v]
  ring

/-- The whole piecewise result as an attained minimum on the closed half-line. -/
theorem isLeast_tilted_tailEnvelope {p c : ℝ} (hp : 0 ≤ p)
    (hc : 0 ≤ c) (hc' : c ≤ 4 / 3) :
    IsLeast ((fun x => tailEnvelope p x - c * x) '' Set.Ici 0)
      (sparseExponent p c) := by
  by_cases h : p ≤ 12
  · by_cases k : c ≤ 8 / 7
    · simpa [sparseExponent, h, k] using minimum_of_moderate_rarity_low_support hp h hc k
    · simpa [sparseExponent, h, k] using
        minimum_of_moderate_rarity_high_support h (le_of_not_ge k) hc'
  · simpa [sparseExponent, h] using minimum_of_high_rarity (le_of_not_ge h) hc hc'

/-- In the upper support range, positivity is equivalent to a strict rarity threshold. -/
theorem positive_iff_rarity_of_high_support {p θ : ℝ}
    (hθ : 4 / 7 ≤ θ) (hθ' : θ < 2 / 3) :
    0 < sparseExponent p (2 * θ) ↔ 6 * θ / (2 - 3 * θ) < p := by
  have hd : 0 < 2 - 3 * θ := by linarith
  rw [div_lt_iff₀ hd]
  by_cases hp : p ≤ 12
  · have hpr := mul_le_mul_of_nonneg_right hp hd.le
    have hnot : ¬ 6 * θ < p * (2 - 3 * θ) := by linarith
    by_cases hc : 2 * θ ≤ 8 / 7
    · have he : θ = 4 / 7 := by linarith
      subst θ
      norm_num [sparseExponent, hp] at *
      linarith
    · have hleft : ¬ 0 < 12 - 21 * (2 * θ) / 2 := by linarith
      simp only [sparseExponent, if_pos hp, if_neg hc, hleft, hnot]
  · simp only [sparseExponent, if_neg hp]
    constructor <;> intro h <;> nlinarith only [h]

/-- At support 4/7, the positivity threshold in the power of log T is exactly 12. -/
theorem positive_at_conrey_boundary_iff {p : ℝ} :
    0 < sparseExponent p (2 * (4 / 7)) ↔ 12 < p := by
  simpa only [show 6 * (4 / 7 : ℝ) / (2 - 3 * (4 / 7)) = 12 by norm_num] using
    (positive_iff_rarity_of_high_support (p := p) (θ := 4 / 7) le_rfl (by norm_num))

/-- At support 2/3 the two available log-density profiles give exponent -2. -/
theorem sparseExponent_at_ingham_boundary (p : ℝ) : sparseExponent p (2 * (2 / 3)) = -2 := by
  by_cases hp : p ≤ 12 <;> norm_num [sparseExponent, hp]

end RiemannResearch.Analysis.SparsePairDensity
