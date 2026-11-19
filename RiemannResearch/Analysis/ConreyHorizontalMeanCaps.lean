/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyHorizontalStopLoss

/-! # Certified numerical horizontal mean caps

The strike is v=-(7/2)log t with rational t. Both exponentials in the
one-piece profile become exact powers of t. Positive Taylor lower bounds for
the exponential certify upper bounds for the remaining two logarithms. -/

noncomputable section
open Filter Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.ActualZeroOrdinate

set_option maxHeartbeats 600000

private theorem log_le_of_taylor {x q : ℝ} (hx : 0 < x) (hq : 0 ≤ q)
    (ht : x ≤ ∑ i ∈ Finset.range 15, q^i / (i.factorial : ℝ)) : Real.log x ≤ q :=
  (Real.log_le_iff_le_exp hx).mpr (ht.trans (Real.sum_le_exp_of_nonneg hq 15))

private theorem conrey_mean_cap_at_rational {t p q d B : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hp : Real.log ((1-t^11)/(1-t^4)) ≤ p) (hq : Real.log (t⁻¹) ≤ q)
    (hd : 0 ≤ d) (hupper : p+d*(7/2)*q < B)
    (h : ConreyStopLossHypothesis)
    (hfrac : ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, strictTail T 0 / (Ncount 0 T : ℝ) ≤ d+ε) :
    ∀ᶠ T : ℝ in atTop, microscopicExcess T 0 ≤ B := by
  let v := -(7/2)*Real.log t
  have hlog := Real.log_neg ht ht1
  have hv : 0 < v := by dsimp only [v]; linarith
  have he4 : Real.exp (-(8/7)*v) = t^4 := by
    rw [show -(8/7)*v = (4:ℕ)*Real.log t by dsimp only [v]; norm_num <;> ring,
      Real.exp_nat_mul, Real.exp_log ht]
  have he11 : Real.exp (-(22/7)*v) = t^11 := by
    rw [show -(22/7)*v = (11:ℕ)*Real.log t by dsimp only [v]; norm_num <;> ring,
      Real.exp_nat_mul, Real.exp_log ht]
  have hprof : conreyStopLossProfile v ≤ p := by
    simpa only [conreyStopLossProfile,if_neg hv.ne',he4,he11] using hp
  have hvq : v ≤ (7/2)*q := by
    rw [Real.log_inv] at hq
    dsimp only [v]
    linarith only [hq]
  apply microscopicExcess_asymptotic_cap h (v:=v) le_rfl hv.le hfrac
  rw [sub_zero]
  exact (add_le_add hprof (mul_le_mul_of_nonneg_right hvq hd)).trans_lt
    (by linarith only [hupper])

/-- The repository one-third fraction gives an outward bound on the limiting
mean mark, with the optimized analytic stop-loss statement as hypothesis. -/
theorem microscopicExcess_zero_le_third_numeric (h : ConreyStopLossHypothesis) :
    ∀ᶠ T : ℝ in atTop, microscopicExcess T 0 ≤ 66891266296/100000000000 := by
  refine conrey_mean_cap_at_rational (t:=7202190107/10000000000) (d:=1/3)
    (p:=28601274264/100000000000) (q:=32819993170/100000000000)
    (by norm_num) (by norm_num) ?_ ?_ (by norm_num) (by norm_num) h ?_
  · apply log_le_of_taylor (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · apply log_le_of_taylor (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · intro ε hε
    exact (eventually_normalized_strictTail_le_third ε hε).mono fun _ hT => hT 0 le_rfl

/-- A conditional decimal mean cap with the exact complement of the
ten-point fraction. The input is expressed through the same strict-copy
tail used by the general shift inequality. -/
theorem microscopicExcess_zero_le_tenPoint_numeric (h : ConreyStopLossHypothesis)
    (hfrac : ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, strictTail T 0 / (Ncount 0 T : ℝ) ≤
      32330161312020665580333919999910648931584214094053 /
        99062663304046530894651923264741897583007812500000 + ε) :
    ∀ᶠ T : ℝ in atTop, microscopicExcess T 0 ≤ 66083809238/100000000000 := by
  refine conrey_mean_cap_at_rational (t:=7163736600/10000000000)
    (p:=27983258134/100000000000) (q:=33355337665/100000000000)
    (by norm_num) (by norm_num) ?_ ?_ (by norm_num) (by norm_num) h hfrac
  · apply log_le_of_taylor (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · apply log_le_of_taylor (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial]

end RiemannResearch.Analysis.ActualZeroOrdinate
