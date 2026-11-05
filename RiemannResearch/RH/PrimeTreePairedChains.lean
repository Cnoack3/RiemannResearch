/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.RH.PrimeTreeTwoCarry
import RiemannResearch.RH.QInfiniteRecursiveCarry
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Tactic

/-! # Changing the first lift in an actual infinite chain

Source: C. Noack, *Prime trees, fractional parts, and zeta zeros* (2026),
§§3 and 5.1. The indices of the normalized chain start at zero for the
first edge 2 → 6. The signal is defined by summing the floor carries and
the second chain explicitly replaces (1,-1) by (3,-4) at that edge.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.CRTCarryArithmetic.NormalizedCarryChain
open ArithmeticCumulative PrimeTreeTwoCarry

variable (s : NormalizedCarryChain)

/-- The physical observation of the infinite sum of integer floors. -/
def chainSignal (n : ℕ) : ℂ := ((∑' k, s.carryTerm n k : ℝ) : ℂ)

def chainConductors : ℕ → ℕ
  | 0 => s.D 0
  | k+1 => s.p k

def chainCoefficients : ℕ → ℂ
  | 0 => (s.w 0 : ℂ)
  | k+1 => ((s.w (k+1) * (s.b k : ℝ) : ℝ) : ℂ)

/-- The signal is exactly its prime-atom expansion, even before imposing
the extra uniform coefficient bound required for Mellin interchange. -/
theorem chainSignal_eq_atomSeries :
    s.chainSignal = atomSeries s.chainConductors s.chainCoefficients := by
  funext n
  have hp := (s.infinite_carry_expansion n).1
  have htail : Summable (fun k => s.chainCoefficients (k+1) *
      (residueFraction (s.chainConductors (k+1)) n : ℂ)) := by
    simpa only [chainCoefficients, chainConductors, primeTerm, Complex.ofReal_mul] using
      (Complex.summable_ofReal.mpr hp)
  have hall : Summable (fun k => s.chainCoefficients k *
      (residueFraction (s.chainConductors k) n : ℂ)) := (summable_nat_add_iff 1).mp htail
  unfold chainSignal atomSeries
  rw [hall.tsum_eq_zero_add, (s.infinite_carry_expansion n).2.2,
    Complex.ofReal_add, Complex.ofReal_tsum]
  simp only [chainCoefficients, chainConductors, parentTerm, primeTerm, Complex.ofReal_mul]

/-- For positive inverses at least two from the second edge onward, and each
subsequent radix no larger than its parent conductor, the prime coefficients
have summable absolute values. -/
theorem chainCoefficients_summable (hw : ∀ k, 0 ≤ s.w k)
    (ha : ∀ k, (2 : ℤ) ≤ s.a (k+1)) (hp : ∀ k, s.p (k+1) ≤ s.D (k+1)) :
    Summable (fun k => ‖s.chainCoefficients k‖) := by
  have hg : Summable (fun k : ℕ => (1/2 : ℝ)^k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hdec (k : ℕ) : 2 * s.w (k+1+1) ≤ s.w (k+1) := by
    have h := mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ (s.a (k+1) : ℝ) by exact_mod_cast ha k)
      (hw (k+1+1))
    linarith [s.normalize (k+1)]
  have hpow (k : ℕ) : s.w (k+1) ≤ (1/2 : ℝ)^k := by
    induction k with
    | zero => simpa using (le_abs_self (s.w 1)).trans (s.weight_bound 1)
    | succ k ih =>
      rw [pow_succ]
      linarith [hdec k]
  apply (summable_nat_add_iff 2).mp
  apply Summable.of_norm_bounded hg
  intro k
  let i := k+1
  have hD : 0 < s.D i := (pow_pos (by decide : 0 < (2 : ℕ)) i).trans_le (s.modulus_growth i)
  have hDr : (0 : ℝ) < s.D i := by exact_mod_cast hD
  have hpr : (s.p i : ℝ) ≤ (s.D i : ℝ) := by exact_mod_cast hp k
  have hpr2 : (2 : ℝ) ≤ (s.p i : ℝ) := by exact_mod_cast s.radix_ge i
  have he : (s.w (i+1) * (s.b i : ℝ)) * (s.D i : ℝ) =
      s.w (i+1) - s.w i * (s.p i : ℝ) := by
    linear_combination s.w (i+1) * s.bezout i - (s.p i : ℝ) * s.normalize i
  have hneg : s.w (i+1) * (s.b i : ℝ) ≤ 0 := by
    apply nonpos_of_mul_nonpos_left _ hDr
    rw [he]
    have hx := mul_le_mul_of_nonneg_left hpr2 (hw i)
    have hd : 2 * s.w (i+1) ≤ s.w i := hdec k
    linarith [hw i, hw (i+1)]
  have hlow : -(s.w i) ≤ s.w (i+1) * (s.b i : ℝ) := by
    apply (le_of_mul_le_mul_right _ hDr)
    rw [he, neg_mul]
    linarith [mul_le_mul_of_nonneg_left hpr (hw i), hw (i+1)]
  change ‖‖((s.w (i+1) * (s.b i : ℝ) : ℝ) : ℂ)‖‖ ≤ _
  rw [norm_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hneg]
  linarith [hpow k, show s.w i = s.w (k+1) by rfl]

def changeFirstToThree (hD : s.D 0 = 2) (hp : s.p 0 = 3)
    (ha : s.a 0 = 1) (hw : s.w 0 = 1) : NormalizedCarryChain where
  D := s.D
  p := s.p
  a := fun k => if k = 0 then 3 else s.a k
  b := fun k => if k = 0 then -4 else s.b k
  w := fun k => if k = 0 then 1 else s.w k / 3
  start_pos := s.start_pos
  radix_ge := s.radix_ge
  next := s.next
  bezout := by
    intro k
    cases k with
    | zero => norm_num [hD, hp]
    | succ k => simpa using s.bezout (k+1)
  normalize := by
    intro k
    cases k with
    | zero =>
      have h1 : s.w 1 = 1 := by simpa [ha, hw] using s.normalize 0
      norm_num [h1]
    | succ k =>
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      linear_combination (1/3 : ℝ) * s.normalize (k+1)
  weight_bound := by
    intro k
    cases k with
    | zero => norm_num
    | succ k =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, abs_div]
      norm_num
      linarith [s.weight_bound (k+1)]

/-- The change from the first lift one to three agrees exactly with the
periodic physical mixture at every site of the two actual carry chains. -/
theorem changeFirst_chainSignal (hD : s.D 0 = 2) (hp : s.p 0 = 3)
    (ha : s.a 0 = 1) (hw : s.w 0 = 1) :
    (s.changeFirstToThree hD hp ha hw).chainSignal = thirdLift s.chainSignal := by
  let t := s.changeFirstToThree hD hp ha hw
  have h1 : s.w 1 = 1 := by simpa [ha, hw] using s.normalize 0
  have hb : s.b 0 = -1 := by
    have h := s.bezout 0
    rw [hD, hp, ha] at h
    norm_num at h
    exact_mod_cast (show (s.b 0 : ℝ) = -1 by linarith)
  funext n
  have he (k : ℕ) : t.primeTerm n (k+1) = (1/3 : ℝ) * s.primeTerm n (k+1) := by
    simp [t, changeFirstToThree, primeTerm]
    ring
  have ht : (∑' k, t.primeTerm n (k+1)) = (1/3 : ℝ) * ∑' k, s.primeTerm n (k+1) := by
    simp_rw [he]
    rw [tsum_mul_left]
  have hr : (∑' k, t.carryTerm n k) =
      (2/3 : ℝ) * (residueFraction 2 n - (3/2 : ℝ) * residueFraction 3 n) +
      (1/3 : ℝ) * (∑' k, s.carryTerm n k) := by
    rw [(t.infinite_carry_expansion n).2.2, (s.infinite_carry_expansion n).2.2,
      (t.infinite_carry_expansion n).1.tsum_eq_zero_add,
      (s.infinite_carry_expansion n).1.tsum_eq_zero_add, ht]
    simp [parentTerm, primeTerm, t, changeFirstToThree, hD, hp, hb, hw, h1]
    ring
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hr
  simpa only [chainSignal, thirdLift, periodicDifference, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one] using hc

/-- The joint zeros of the Mellin integrals of the two actual chains coincide
with the zeros of zeta in the open strip under the elementary path inequalities
which hold for the successive-prime, positive-inverse path in the paper. -/
theorem paired_chain_zero_iff (hD : s.D 0 = 2) (hp : s.p 0 = 3)
    (ha : s.a 0 = 1) (hw : s.w 0 = 1) (hnn : ∀ k, 0 ≤ s.w k)
    (hinv : ∀ k, (2 : ℤ) ≤ s.a (k+1)) (hrad : ∀ k, s.p (k+1) ≤ s.D (k+1))
    (z : ℂ) (hz : 0 < z.re) (h1 : z.re < 1) :
    (readout s.chainSignal z = 0 ∧ readout (s.changeFirstToThree hD hp ha hw).chainSignal z = 0) ↔
      riemannZeta z = 0 := by
  rw [s.changeFirst_chainSignal hD hp ha hw, s.chainSignal_eq_atomSeries]
  apply paired_readout_zero_iff _ _ _ (s.chainCoefficients_summable hnn hinv hrad) z hz h1
  intro k
  cases k with
  | zero => exact s.start_pos
  | succ k => exact lt_of_lt_of_le (by decide : 0 < 2) (s.radix_ge k)

end RiemannResearch.RH.CRTCarryArithmetic.NormalizedCarryChain
