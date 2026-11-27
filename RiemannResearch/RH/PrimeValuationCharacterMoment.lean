import RiemannResearch.RH.PrimeValuationIndependence
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic

/-! # Character moments of a prime valuation under the inverse-square law

The signed one-prime factor of the packet Gram layer in section 5 of the
CRT packet character note is the covariance of two geometric character modes.
The second character value can be conjugated before applying the bilinear formula.
-/

noncomputable section
namespace RiemannResearch.RH.ZetaTwoProbability

/-- The full transform of one prime exponent, using its actual Q masses. -/
def valuationCharacterMoment (p : ℕ) (z : ℂ) : ℂ :=
  ∑' j : ℕ, ((Q {n : ℕ+ | primeValuation p n = j}).toReal : ℂ) * z ^ j

private def valuationRatio (p : ℕ) : ℝ := 1 / (p : ℝ)^2

private theorem valuationRatio_lt_one {p : ℕ} (hp : p.Prime) : valuationRatio p < 1 := by
  have h : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  unfold valuationRatio
  exact (div_lt_one (by positivity)).2 (by nlinarith)

private theorem valuationRatio_mul_norm_lt {p : ℕ} (hp : p.Prime) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖(valuationRatio p : ℂ) * z‖ < 1 := by
  have h : 0 ≤ valuationRatio p := by unfold valuationRatio; positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h]
  exact (mul_le_mul_of_nonneg_left hz h).trans_lt (by simpa using valuationRatio_lt_one hp)

private theorem denominator_ne {p : ℕ} (hp : p.Prime) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    1 - (valuationRatio p : ℂ) * z ≠ 0 := by
  intro h
  have h' := valuationRatio_mul_norm_lt hp hz
  rw [(sub_eq_zero.mp h).symm, norm_one] at h'
  exact h'.false

theorem valuationCharacterMoment_eq {p : ℕ} (hp : p.Prime) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    valuationCharacterMoment p z =
      (1 - ((1 / (p : ℝ)^2 : ℝ) : ℂ)) / (1 - ((1 / (p : ℝ)^2 : ℝ) : ℂ) * z) := by
  let r := valuationRatio p
  have hr : r ≤ 1 := (valuationRatio_lt_one hp).le
  have hreal (j : ℕ) : (Q {n : ℕ+ | primeValuation p n = j}).toReal = (1-r)*r^j := by
    rw [measure_primeValuation_eq p j hp, ENNReal.toReal_ofReal (by
      apply mul_nonneg
      · exact sub_nonneg.mpr hr
      · positivity)]
    simp [r, valuationRatio, ← pow_mul, Nat.mul_comm j 2]
  unfold valuationCharacterMoment
  simp_rw [hreal, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub,
    Complex.ofReal_one, mul_assoc, ← mul_pow]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (valuationRatio_mul_norm_lt hp hz)]
  rfl

/-- The signed local Euler factor for two character modes of the same exponent. -/
theorem valuationCharacterCovariance_eq {p : ℕ} (hp : p.Prime) {a b : ℂ}
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    let r : ℂ := (1 / (p : ℝ)^2 : ℝ)
    valuationCharacterMoment p (a*b) - valuationCharacterMoment p a * valuationCharacterMoment p b =
      r*(1-r)*(1-a)*(1-b)/((1-r*(a*b))*(1-r*a)*(1-r*b)) := by
  have hab : ‖a*b‖ ≤ 1 := by rw [norm_mul]; nlinarith [norm_nonneg a, norm_nonneg b]
  dsimp only
  rw [valuationCharacterMoment_eq hp hab, valuationCharacterMoment_eq hp ha,
    valuationCharacterMoment_eq hp hb]
  change (1-(valuationRatio p : ℂ))/(1-(valuationRatio p : ℂ)*(a*b)) -
    ((1-(valuationRatio p : ℂ))/(1-(valuationRatio p : ℂ)*a)) *
      ((1-(valuationRatio p : ℂ))/(1-(valuationRatio p : ℂ)*b)) = _
  change _ = (valuationRatio p : ℂ)*(1-(valuationRatio p : ℂ))*(1-a)*(1-b) /
    ((1-(valuationRatio p : ℂ)*(a*b))*(1-(valuationRatio p : ℂ)*a)*(1-(valuationRatio p : ℂ)*b))
  have hprod : 1 - (valuationRatio p : ℂ) * a * b ≠ 0 := by
    simpa only [mul_assoc] using denominator_ne hp hab
  simp only [← mul_assoc]
  field_simp [hprod, denominator_ne hp ha, denominator_ne hp hb]
  <;> ring

/-- A character which is trivial at the newly revealed prime gives exactly zero
local cross term, before taking real parts in the packet expansion. -/
theorem valuationCharacterCovariance_zero_iff {p : ℕ} (hp : p.Prime) {a b : ℂ}
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    valuationCharacterMoment p (a*b) - valuationCharacterMoment p a * valuationCharacterMoment p b = 0
      ↔ a = 1 ∨ b = 1 := by
  have hab : ‖a*b‖ ≤ 1 := by rw [norm_mul]; nlinarith [norm_nonneg a, norm_nonneg b]
  have hpos : 0 < valuationRatio p := by unfold valuationRatio; have := hp.pos; positivity
  have hr : (valuationRatio p : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have ho : (1 : ℂ) - valuationRatio p ≠ 0 := by
    exact_mod_cast (sub_pos.mpr (valuationRatio_lt_one hp)).ne'
  rw [valuationCharacterCovariance_eq hp ha hb]
  change (valuationRatio p : ℂ)*(1-(valuationRatio p : ℂ))*(1-a)*(1-b) /
    ((1-(valuationRatio p : ℂ)*(a*b))*(1-(valuationRatio p : ℂ)*a)*(1-(valuationRatio p : ℂ)*b))
    = 0 ↔ _
  have hd := mul_ne_zero (mul_ne_zero (denominator_ne hp hab) (denominator_ne hp ha)) (denominator_ne hp hb)
  rw [div_eq_zero_iff]
  simp only [hd, or_false, mul_eq_zero, hr, ho, false_or, sub_eq_zero]
  tauto

/-- In a signed real packet Gram entry, passing one prime from the tail Euler
product to the head eliminates the common full product. Only the local
valuation covariance times the two surviving tail means remains. For the
period-six/period-ten cross term, the multiplier includes (15/4)(1+i). -/
theorem realCharacterLayer_step {p : ℕ} (hp : p.Prime) {a b : ℂ}
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (weight head tailA tailB tailAB : ℂ) :
    let m := valuationCharacterMoment p
    let r : ℂ := (1 / (p : ℝ)^2 : ℝ)
    (weight*head*(m (a*b)*tailAB - (m a*tailA)*(m b*tailB))).re -
      (weight*(head*m (a*b))*(tailAB-tailA*tailB)).re =
      (weight*head*tailA*tailB *
        (r*(1-r)*(1-a)*(1-b)/((1-r*(a*b))*(1-r*a)*(1-r*b)))).re := by
  dsimp only
  rw [← Complex.sub_re, ← valuationCharacterCovariance_eq hp ha hb]
  congr 1
  ring

end RiemannResearch.RH.ZetaTwoProbability
