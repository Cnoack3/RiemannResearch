import RiemannResearch.RH.NymanConductorArithmetic
import Mathlib.NumberTheory.LSeries.ZMod
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Entire L-function of the actual periodic Nyman coefficients

Source: equation (4.2) of the user-provided Nyman--Weil note. The construction
uses Mathlib's Hurwitz-zeta continuation of periodic coefficient series.
The vanishing mean is proved for the actual beta coefficients; no analytic
continuation or transform identity is a hypothesis. Identification with the
bilateral integral of `arithmeticReturn` is a separate obligation.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH

/-- The exact normalized conductor coefficients on one complete period. -/
def nymanPeriodicBeta (n : ℕ) (j : ZMod n) : ℂ :=
  1 / (n : ℂ) - if j = 0 then 1 else 0

/-- The periodic model agrees with the actual arithmetic coefficient at every
positive index. The value at zero is immaterial for `LSeries.term`. -/
theorem nymanPeriodicBeta_natCast (n k : ℕ) (hk : k ≠ 0) :
    nymanPeriodicBeta n (k : ZMod n) = (nymanConductorBeta n k : ℂ) := by
  by_cases h : n ∣ k <;>
    simp [nymanPeriodicBeta, nymanConductorBeta_apply hk, ZMod.natCast_eq_zero_iff, h]

/-- Exact zero-frequency cancellation over a complete conductor period. -/
theorem sum_nymanPeriodicBeta (n : ℕ) [NeZero n] :
    (∑ j : ZMod n, nymanPeriodicBeta n j) = 0 := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  simp [nymanPeriodicBeta, Finset.sum_sub_distrib, ZMod.card, hn]

/-- Hurwitz-zeta continuation of the actual periodic beta series. -/
def nymanConductorLFunction (n : ℕ) [NeZero n] : ℂ → ℂ :=
  ZMod.LFunction (nymanPeriodicBeta n)

/-- The conductor L-function is entire; this uses exact arithmetic cancellation. -/
theorem differentiable_nymanConductorLFunction (n : ℕ) [NeZero n] :
    Differentiable ℂ (nymanConductorLFunction n) :=
  ZMod.differentiable_LFunction_of_sum_zero (sum_nymanPeriodicBeta n)

/-- Absolute convergence of the actual beta Dirichlet series on its elementary
half-plane, obtained from the concrete finite-period coefficient function. -/
theorem lSeriesSummable_nymanConductorBeta (n : ℕ) [NeZero n] {s : ℂ}
    (hs : 1 < s.re) :
    LSeriesSummable (fun k => (nymanConductorBeta n k : ℂ)) s := by
  exact (LSeriesSummable_congr s (fun {k} hk =>
    nymanPeriodicBeta_natCast n k hk)).mp
      (ZMod.LSeriesSummable_of_one_lt_re (nymanPeriodicBeta n) hs)

/-- The entire function agrees with the Dirichlet series of the actual arithmetic
return coefficients on `Re s > 1`. No assumed factorization is used. -/
theorem nymanConductorLFunction_eq_LSeries (n : ℕ) [NeZero n] {s : ℂ}
    (hs : 1 < s.re) :
    nymanConductorLFunction n s =
      LSeries (fun k => (nymanConductorBeta n k : ℂ)) s := by
  rw [nymanConductorLFunction, ZMod.LFunction_eq_LSeries _ hs]
  exact LSeries_congr (fun {k} hk => nymanPeriodicBeta_natCast n k hk) s

/-- Explicit absolutely convergent beta series with the zero coefficient removed. -/
theorem nymanConductorLFunction_eq_tsum (n : ℕ) [NeZero n] {s : ℂ}
    (hs : 1 < s.re) :
    nymanConductorLFunction n s =
      ∑' k : ℕ, (nymanConductorBeta n k : ℂ) / (k : ℂ) ^ s := by
  rw [nymanConductorLFunction_eq_LSeries n hs]
  exact LSeries_def₀ (by simp) s

end RiemannResearch.RH

namespace RiemannResearch.RH

/-- Exact sparse reindexing of the divisibility sector. This is the arithmetic
calculation behind `n⁻ˢ ζ(s)`, with no convergence assumptions needed for reindexing. -/
theorem tsum_divisibility_cpow (n : ℕ) [NeZero n] (s : ℂ) :
    (∑' k : ℕ, (if n ∣ k then (1 : ℂ) else 0) / (k : ℂ) ^ s) =
      (n : ℂ) ^ (-s) * ∑' k : ℕ, 1 / (k : ℂ) ^ s := by
  classical
  let f : ℕ → ℂ := fun k => (if n ∣ k then 1 else 0) / (k : ℂ) ^ s
  have hi : Function.Injective (fun k : ℕ => n * k) := by
    intro a b h
    exact Nat.eq_of_mul_eq_mul_left (NeZero.pos n) h
  have hf : Function.support f ⊆ Set.range (fun k : ℕ => n * k) := by
    intro k hk
    have hnk : n ∣ k := by
      by_contra h
      exact hk (by simp [f, h])
    obtain ⟨d, hd⟩ := hnk
    exact ⟨d, hd.symm⟩
  calc
    (∑' k : ℕ, f k) = ∑' k : ℕ, f (n * k) := (hi.tsum_eq hf).symm
    _ = ∑' k : ℕ, (n : ℂ) ^ (-s) * (1 / (k : ℂ) ^ s) := by
      apply tsum_congr
      intro k
      simp [f, Nat.cast_mul, Complex.natCast_mul_natCast_cpow,
        Complex.cpow_neg, one_div, mul_inv_rev, mul_comm]
    _ = _ := tsum_mul_left

private theorem lSeries_const (c : ℂ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun _ : ℕ => c) s = c * riemannZeta s := by
  unfold LSeries
  simp_rw [LSeries.term_of_ne_zero' (Complex.ne_zero_of_one_lt_re hs),
    div_eq_mul_inv]
  rw [tsum_mul_left, zeta_eq_tsum_one_div_nat_cpow hs]
  simp only [one_div]

/-- Exact factorization of the actual periodic coefficient series into zeta and
its conductor factor, on the region where its arithmetic sum converges. -/
theorem nymanConductorLFunction_eq_zeta_cpow (n : ℕ) [NeZero n] {s : ℂ}
    (hs : 1 < s.re) :
    nymanConductorLFunction n s =
      riemannZeta s * (1 / (n : ℂ) - (n : ℂ) ^ (-s)) := by
  classical
  let c : ℕ → ℂ := fun _ => 1 / (n : ℂ)
  let d : ℕ → ℂ := fun k => if n ∣ k then 1 else 0
  have hc : LSeriesSummable c s := by
    exact LSeriesSummable_of_bounded_of_one_lt_re
      (m := ‖1 / (n : ℂ)‖) (fun k _ => le_rfl) hs
  have hd : LSeriesSummable d s := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ hs
    intro k hk
    by_cases h : n ∣ k <;> simp [d, h]
  have hcd : LSeries (fun k => (nymanConductorBeta n k : ℂ)) s =
      LSeries (c - d) s := by
    apply LSeries_congr _ s
    intro k hk
    by_cases h : n ∣ k <;> simp [c, d, nymanConductorBeta_apply hk, h]
  have hdval : LSeries d s = (n : ℂ) ^ (-s) * riemannZeta s := by
    unfold LSeries
    simp_rw [LSeries.term_of_ne_zero' (Complex.ne_zero_of_one_lt_re hs)]
    rw [show (fun k : ℕ => d k / (k : ℂ) ^ s) =
      (fun k : ℕ => (if n ∣ k then (1 : ℂ) else 0) / (k : ℂ) ^ s) from rfl,
      tsum_divisibility_cpow n s, ← zeta_eq_tsum_one_div_nat_cpow hs]
  rw [nymanConductorLFunction_eq_LSeries n hs, hcd, LSeries_sub hc hd,
    hdval, show LSeries c s = (1 / (n : ℂ)) * riemannZeta s from lSeries_const _ hs]
  ring

end RiemannResearch.RH
