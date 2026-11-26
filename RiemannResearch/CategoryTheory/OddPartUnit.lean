import RiemannResearch.CategoryTheory.OddConditionalUnit
import RiemannResearch.RH.QParityBasis
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Nat.Factorization.Basic

/-! # Removing odd conditioning from the physical Q unit

Source: the user's Q prime Parseval tower handoff and prime valuation question.
The inverse-square law factors along the two-adic exponent and the odd part.
Two unconditional expectations recover the odd conditional unit of the
Pareto screened section using the full integration weight B = dP/dQ.
-/

noncomputable section
open RiemannResearch.RH RiemannResearch.RH.ZetaTwoHilbert
open RiemannResearch.RH.ZetaTwoParitySignal RiemannResearch.RH.ZetaTwoParetoTransfer
open RiemannResearch.CategoryTheory.PhysicalParityObject

namespace RiemannResearch.CategoryTheory.OddConditionalUnit

/-- Remove the two-adic coordinate of a physical site. The zero site has Q mass zero. -/
def oddPart (n : ℕ) : ℕ := n / 2 ^ n.factorization 2

private theorem oddPart_pow_mul (a m : ℕ) (hm : ¬ 2 ∣ m) :
    oddPart (2 ^ a * m) = m :=
  (Nat.ordCompl_self_pow_mul m a Nat.prime_two).trans
    ((Nat.ordCompl_eq_self_iff_zero_or_not_dvd m Nat.prime_two).mpr (Or.inr hm))

/-- Each additional factor of two reduces the Q mass by a factor of four. -/
theorem qWeight_two_pow_mul (a m : ℕ) :
    positiveQWeight (2 ^ a * m) = (1 / 4 : ℝ) ^ a * positiveQWeight m := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ' (2 : ℕ), Nat.mul_assoc, ZetaTwoParitySignal.positiveQWeight_mul 2, ih,
      pow_succ' (1 / 4 : ℝ)]
    norm_num [mul_assoc]

/-- Ordinary Q expectation after evaluating the observable at the odd part of N. -/
def oddPartQMean (f : QHilbert) : ℝ :=
  ∑' n : ℕ, positiveQWeight n * qSequence f (oddPart n)

/-- Removing the independent two-adic exponent gives the odd conditional law for
every physical square-integrable observable, including one depending on parity. -/
theorem oddPartQMean_eq_nativeOddMean (f : QHilbert) :
    oddPartQMean f = nativeOddMean f := by
  classical
  let geom := fun a : ℕ => (1 / 4 : ℝ) ^ a
  let row := fun m : ℕ => positiveQWeight m * qSequence f m * qSequence qOdd m
  have support_odd {a m : ℕ} (h : geom a * row m ≠ 0) : ¬ 2 ∣ m := by
    intro hd
    simp [row, qSequence_qOdd, hd] at h
  have term (a m : ℕ) (hm : ¬ 2 ∣ m) :
      positiveQWeight (2 ^ a * m) * qSequence f (oddPart (2 ^ a * m)) =
        geom a * row m := by
    rw [qWeight_two_pow_mul, oddPart_pow_mul a m hm]
    simp only [geom, row, qSequence_qOdd, if_neg hm, mul_one, mul_assoc]
  have hreindex : oddPartQMean f = ∑' z : ℕ × ℕ, geom z.1 * row z.2 := by
    unfold oddPartQMean
    apply tsum_eq_tsum_of_ne_zero_bij
      (fun z : Function.support (fun z : ℕ × ℕ => geom z.1 * row z.2) => 2 ^ z.val.1 * z.val.2)
    · intro x y hxy
      change 2 ^ x.val.1 * x.val.2 = 2 ^ y.val.1 * y.val.2 at hxy
      have hx := support_odd x.property
      have hy := support_odd y.property
      have he : x.val.2 = y.val.2 := by
        simpa only [oddPart_pow_mul _ _ hx, oddPart_pow_mul _ _ hy] using congrArg oddPart hxy
      have hyn : y.val.2 ≠ 0 := by
        intro h
        exact hy (h.symm ▸ dvd_zero 2)
      apply Subtype.ext
      apply Prod.ext
      · apply Nat.pow_right_injective (by decide : 2 ≤ 2)
        apply mul_right_cancel₀ hyn
        simpa only [he] using hxy
      · exact he
    · intro n hn
      change positiveQWeight n * qSequence f (oddPart n) ≠ 0 at hn
      have hn0 : n ≠ 0 := by
        rintro rfl
        simp [positiveQWeight] at hn
      have hodd : ¬ 2 ∣ oddPart n :=
        Nat.prime_two.coprime_iff_not_dvd.mp (Nat.coprime_ordCompl Nat.prime_two hn0)
      have hjoin : 2 ^ n.factorization 2 * oddPart n = n :=
        Nat.ordProj_mul_ordCompl_eq_self n 2
      refine ⟨⟨(n.factorization 2, oddPart n), ?_⟩, hjoin⟩
      change geom (n.factorization 2) * row (oddPart n) ≠ 0
      rwa [← term _ _ hodd, hjoin]
    · intro z
      exact term z.val.1 z.val.2 (support_odd z.property)
  have hlt : ‖(1 / 4 : ℝ)‖ < 1 := by norm_num
  have hg : Summable geom := summable_geometric_of_norm_lt_one hlt
  have hr : Summable row := qSequence_product_summable f qOdd
  have hgn : Summable (fun a => ‖geom a‖) := by simpa only [Real.norm_eq_abs] using hg.abs
  have hrn : Summable (fun m => ‖row m‖) := by simpa only [Real.norm_eq_abs] using hr.abs
  have hgeom : ∑' a, geom a = (4 / 3 : ℝ) := by
    change (∑' a : ℕ, (1 / 4 : ℝ) ^ a) = _
    rw [tsum_geometric_of_norm_lt_one hlt]
    norm_num
  have hrow : ∑' m, row m = inner ℝ f qOdd := (qInner_weighted f qOdd).symm
  rw [hreindex, ← tsum_mul_tsum_of_summable_norm hgn hrn, hgeom, hrow, nativeOddMean]
  ring

/-- The unit is a single unconditional expectation of B(M)u(M), with M the odd part. -/
theorem rh_iff_oddPart_B_moment :
    RiemannHypothesis ↔ oddPartQMean (B transportedCarry) = 4 * Real.log 2 / 3 := by
  rw [oddPartQMean_eq_nativeOddMean]
  exact rh_iff_B_odd_moment

/-- Ordinary Q expectation of the physical observable evaluated at twice N. -/
def doubledQMean (f : QHilbert) : ℝ :=
  ∑' n : ℕ, positiveQWeight n * qSequence f (2 * n)

theorem nativeOddMean_eq_doubled (f : QHilbert) :
    nativeOddMean f = (4 * inner ℝ f qOne - doubledQMean f) / 3 := by
  have hev : inner ℝ f qEven = (1 / 4 : ℝ) * doubledQMean f := by
    rw [qInner_even_reindex, doubledQMean, ← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [ZetaTwoParitySignal.positiveQWeight_mul]
    norm_num [mul_assoc]
  have hall : inner ℝ f qEven + inner ℝ f qOdd = inner ℝ f qOne := by
    rw [← inner_add_right, qEven_add_qOdd]
  rw [hev] at hall
  unfold nativeOddMean
  linarith

/-- The doubling test uses the known unconditional mean E_Q[B(N)u(N)] = 1. -/
theorem rh_iff_doubled_B_moment :
    RiemannHypothesis ↔ doubledQMean (B transportedCarry) = 4 * (1 - Real.log 2) := by
  rw [rh_iff_B_odd_moment, nativeOddMean_eq_doubled, B_screened_mean]
  constructor <;> intro h <;> linarith

/-- Exact positive deficit below the doubled target. -/
theorem doubled_B_deficit :
    4 * (1 - Real.log 2) - doubledQMean (B transportedCarry) =
      4 * Real.log 2 * densityInner (transportedCarry - qOne) (transportedCarry - qOne) := by
  have h := weighted_odd_moment transportedCarry
  rw [nativeOddMean_eq_doubled, B_screened_mean, ← densityOddMean_eq_pareto] at h
  rw [← densityOddMean_excess]
  nlinarith only [h]

/--
info: 'RiemannResearch.CategoryTheory.OddConditionalUnit.rh_iff_oddPart_B_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rh_iff_oddPart_B_moment

/--
info: 'RiemannResearch.CategoryTheory.OddConditionalUnit.rh_iff_doubled_B_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rh_iff_doubled_B_moment

end RiemannResearch.CategoryTheory.OddConditionalUnit
