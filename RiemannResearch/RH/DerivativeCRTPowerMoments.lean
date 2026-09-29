import RiemannResearch.RH.DerivativeCRT
import RiemannResearch.RH.CRTGCDGram
import Mathlib.Analysis.PSeries

/-!
# Exact zeta moments of the actual derivative CRT rows

Source: user-directed three-route continuation, September 29, 2026.
This generalizes the repository's reciprocal-square divisibility identity
to every integer exponent above one. These are exact Dirichlet-series
moments of the actual anchored derivative atoms. No explicit formula over
zeta zeros, positivity of a Weil form, or RH is assumed.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.DerivativeCompatibility
open ArithmeticCumulative GramMobiusCorrection

/-- The convergent Dirichlet series at an integer greater than one. -/
def inversePowerSeries (p : ℕ) : ℝ := ∑' k : ℕ, 1 / (k : ℝ)^p


/-- Identification with Mathlib's actual zeta function at every integer p>1. -/
theorem inversePowerSeries_eq_riemannZeta (p : ℕ) (hp : 1 < p) :
    (inversePowerSeries p : ℂ) = riemannZeta (p : ℂ) := by
  rw [zeta_nat_eq_tsum_of_gt_one hp]
  unfold inversePowerSeries
  rw [Complex.ofReal_tsum]
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow,
    Complex.ofReal_natCast]

/-- Exact reciprocal-power mass of a complete positive divisibility class.
The anchored zero term is zero because p is positive. -/
theorem inversePower_multiples (p L : ℕ) (hp : 0 < p) (hL : 0 < L) :
    (∑' k : ℕ, if L ∣ k then 1 / (k : ℝ)^p else 0) =
      inversePowerSeries p / (L : ℝ)^p := by
  have hp0 : p ≠ 0 := by omega
  have he : (∑' k : ℕ, if L ∣ k then 1 / (k : ℝ)^p else 0) =
      ∑' a : ℕ, (1 / (L : ℝ)^p) * (1 / (a : ℝ)^p) := by
    apply tsum_eq_tsum_of_ne_zero_bij
      (fun a : Function.support (fun a : ℕ =>
        (1 / (L : ℝ)^p) * (1 / (a : ℝ)^p)) => L*a.val)
    · intro a b hab
      exact Subtype.ext (Nat.eq_of_mul_eq_mul_left hL hab)
    · intro k hk
      have hdiv : L ∣ k := by
        by_contra hh
        simpa only [Function.mem_support, if_neg hh, ne_eq, not_true_eq_false] using hk
      have hkz : k ≠ 0 := by
        intro hh
        subst k
        simpa [Function.mem_support, hp0] using hk
      obtain ⟨a, rfl⟩ := hdiv
      have ha : 0 < a := by
        by_contra hh
        have hz : a=0 := Nat.eq_zero_of_not_pos hh
        simp [hz] at hkz
      refine ⟨⟨a, ?_⟩, rfl⟩
      change (1 / (L : ℝ)^p) * (1 / (a : ℝ)^p) ≠ 0
      positivity
    · intro a
      rw [if_pos (dvd_mul_right L a.val)]
      push_cast
      simp only [mul_pow, one_div, mul_inv]
  rw [he, tsum_mul_left]
  unfold inversePowerSeries
  ring

theorem inversePowerSeries_summable (p : ℕ) (hp : 1 < p) :
    Summable (fun k : ℕ => 1 / (k : ℝ)^p) :=
  Real.summable_one_div_nat_pow.mpr hp

theorem powerDivisorTerm_summable (p : ℕ) (hp : 1 < p) (q : ℕ) :
    Summable (fun k : ℕ => divisorIndicator q k / (k : ℝ)^p) := by
  apply Summable.of_nonneg_of_le (fun k => by
    unfold divisorIndicator; split_ifs <;> positivity) _
    (inversePowerSeries_summable p hp)
  intro k
  unfold divisorIndicator
  split_ifs <;> simp

theorem powerDivisorTerm_tsum (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    (∑' k : ℕ, divisorIndicator q k / (k : ℝ)^p) =
      inversePowerSeries p / (q : ℝ)^p := by
  simpa only [divisorIndicator, ite_div, zero_div] using
    inversePower_multiples p q hp hq

/-- Dirichlet-series pairing of two actual anchored derivative atoms. -/
def derivativePowerKernel (p i j : ℕ) : ℝ :=
  ∑' k : ℕ, hilbertSequence (derivativeAtom i) k *
    hilbertSequence (derivativeAtom j) k / (k : ℝ)^p

/-- The exact pointwise CRT expansion keeps both linear divisor terms and
its lcm intersection term, with no contribution inserted at k=0. -/
theorem derivativePowerTerm_crt (p i j k : ℕ) (hp : 0 < p) :
    hilbertSequence (derivativeAtom i) k *
        hilbertSequence (derivativeAtom j) k / (k : ℝ)^p =
      (1 / (k : ℝ)^p) *
          (1 / ((i + 2 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) -
        (divisorIndicator (j + 2) k / (k : ℝ)^p) *
          (1 / ((i + 2 : ℕ) : ℝ)) -
        (divisorIndicator (i + 2) k / (k : ℝ)^p) *
          (1 / ((j + 2 : ℕ) : ℝ)) +
        divisorIndicator (Nat.lcm (i + 2) (j + 2)) k / (k : ℝ)^p := by
  by_cases hk : k = 0
  · subst k
    have hp0 : p ≠ 0 := by omega
    simp [hp0]
  · rw [derivativeAtom_sequence_positive i k (Nat.pos_of_ne_zero hk),
      derivativeAtom_sequence_positive j k (Nat.pos_of_ne_zero hk),
      ← divisorIndicator_mul]
    ring

theorem derivativePowerTerm_summable (p i j : ℕ) (hp : 1 < p) :
    Summable (fun k : ℕ => hilbertSequence (derivativeAtom i) k *
      hilbertSequence (derivativeAtom j) k / (k : ℝ)^p) := by
  simp_rw [derivativePowerTerm_crt p i j _ (by omega : 0 < p)]
  exact (((inversePowerSeries_summable p hp).mul_right _).sub
    ((powerDivisorTerm_summable p hp (j + 2)).mul_right _)).sub
      ((powerDivisorTerm_summable p hp (i + 2)).mul_right _) |>.add
        (powerDivisorTerm_summable p hp (Nat.lcm (i + 2) (j + 2)))

/-- Closed exact CRT/zeta Gram entry for every integer p>1. -/
theorem derivativePowerKernel_crt (p i j : ℕ) (hp : 1 < p) :
    derivativePowerKernel p i j = inversePowerSeries p *
      (1 / ((i + 2 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ) -
        1 / ((i + 2 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)^p -
        1 / ((j + 2 : ℕ) : ℝ) / ((i + 2 : ℕ) : ℝ)^p +
        1 / (Nat.lcm (i + 2) (j + 2) : ℝ)^p) := by
  unfold derivativePowerKernel
  simp_rw [derivativePowerTerm_crt p i j _ (by omega : 0 < p)]
  have hs0 := (inversePowerSeries_summable p hp).mul_right
    (1 / ((i + 2 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  have hs1 := (powerDivisorTerm_summable p hp (j + 2)).mul_right
    (1 / ((i + 2 : ℕ) : ℝ))
  have hs2 := (powerDivisorTerm_summable p hp (i + 2)).mul_right
    (1 / ((j + 2 : ℕ) : ℝ))
  have hs3 := powerDivisorTerm_summable p hp (Nat.lcm (i + 2) (j + 2))
  rw [((hs0.sub hs1).sub hs2).tsum_add hs3,
    (hs0.sub hs1).tsum_sub hs2, hs0.tsum_sub hs1]
  simp only [tsum_mul_right]
  rw [powerDivisorTerm_tsum p (j + 2) (by omega) (by omega),
    powerDivisorTerm_tsum p (i + 2) (by omega) (by omega),
    powerDivisorTerm_tsum p (Nat.lcm (i + 2) (j + 2)) (by omega)
      (Nat.lcm_pos (by omega) (by omega))]
  unfold inversePowerSeries
  ring

/-- Finite signed row; no limit or growing sum is interchanged. -/
def correctionPowerMoment (p n i : ℕ) : ℝ :=
  ∑ j : Fin n, correctionVector n j * derivativePowerKernel p i j.val

def correctionInversePowerMoment (p n : ℕ) : ℝ :=
  ∑ j : Fin n, correctionVector n j / ((j.val + 2 : ℕ) : ℝ)^p

def correctionLCMPowerMoment (p n i : ℕ) : ℝ :=
  ∑ j : Fin n, correctionVector n j /
    (Nat.lcm (i + 2) (j.val + 2) : ℝ)^p

/-- The entire signed correction moment in three finite arithmetic sums. -/
theorem correctionPowerMoment_crt (p n i : ℕ) (hp : 1 < p) :
    correctionPowerMoment p n i = inversePowerSeries p *
      (correctionReciprocalMoment n / ((i + 2 : ℕ) : ℝ) -
        correctionInversePowerMoment p n / ((i + 2 : ℕ) : ℝ) -
        correctionReciprocalMoment n / ((i + 2 : ℕ) : ℝ)^p +
        correctionLCMPowerMoment p n i) := by
  unfold correctionPowerMoment
  simp_rw [derivativePowerKernel_crt p i _ hp]
  unfold correctionReciprocalMoment correctionInversePowerMoment correctionLCMPowerMoment
  simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- First-site mass is retained separately when using moments over k≥2. -/
theorem derivativePowerKernel_tail (p i j : ℕ) (hp : 1 < p) :
    (∑' k : ℕ, hilbertSequence (derivativeAtom i) (k + 2) *
      hilbertSequence (derivativeAtom j) (k + 2) / ((k + 2 : ℕ) : ℝ)^p) =
        derivativePowerKernel p i j -
          1 / ((i + 2 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ) := by
  have h := (derivativePowerTerm_summable p i j hp).sum_add_tsum_nat_add 2
  have hdi : ¬ (i + 2) ∣ 1 := by intro hd; have := Nat.le_of_dvd (by omega) hd; omega
  have hdj : ¬ (j + 2) ∣ 1 := by intro hd; have := Nat.le_of_dvd (by omega) hd; omega
  have hp0 : p ≠ 0 := by omega
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.cast_zero, zero_pow hp0, div_zero, Nat.zero_add, zero_add,
    derivativeAtom_sequence_positive i 1 (by omega),
    derivativeAtom_sequence_positive j 1 (by omega),
    divisorIndicator, if_neg hdi, if_neg hdj, sub_zero, Nat.cast_one, one_pow,
    div_one] at h
  change _ + _ = derivativePowerKernel p i j at h
  simp only [div_eq_mul_inv, one_mul] at h ⊢
  linarith

end RiemannResearch.RH.Pareto.CoefficientStabilization.DerivativeCompatibility
