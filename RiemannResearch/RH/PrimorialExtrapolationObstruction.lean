import RiemannResearch.RH.PrimeSievePointEnergy
import RiemannResearch.RH.ParetoFiniteGram
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import RiemannResearch.RH.CanonicalMobiusConditionalHead

/-!
# Full Pareto obstruction for single-prime sieve extrapolation

The actual legal atom combination here is
`p * sieveResidue Q p - sieveResidue Q 1`.
For a prime p coprime to Q this is the paper's
`p F_(Qp) - (p-1) F_Q`, by finite Möbius divisor regrouping.
This module proves its exact rough-count identity and the full infinite
Pareto lower bounds directly, without requiring that regrouping as a premise.

Source: user-provided continuation, 6 October 2026, Section 26
(statements and block-count proof strategy). The direct prime-divisor regrouping and the resulting identification
are proved below.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.PrimorialExtrapolation
open RiemannResearch.RH.Pareto
open RiemannResearch.RH.ArithmeticCumulative

def extrapolant (Q p j : ℕ) : ℝ :=
  (p : ℝ)*sieveResidue Q p j - sieveResidue Q 1 j

theorem extrapolant_atoms (Q p j : ℕ) :
    extrapolant Q p j = ∑ d ∈ Q.divisors,
      (ArithmeticFunction.moebius d : ℝ) *
        ((p : ℝ)*residueFraction (p*d) j - residueFraction d j) := by
  unfold extrapolant sieveResidue
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Nat.one_mul]
  ring

theorem extrapolant_count (Q p j : ℕ) (hQ : 0 < Q) (hp : 0 < p) :
    extrapolant Q p j = sieveRoughCount Q j - (p : ℝ)*sieveRoughCount Q (j/p) := by
  unfold extrapolant
  rw [sieveResidue_exact Q p j hQ hp,
    sieveResidue_exact Q 1 j hQ (by decide)]
  simp only [Nat.div_one, Nat.cast_one, div_one]
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  field_simp [hp0]
  ring

theorem extrapolant_mem_legal (Q p : ℕ) (hp : 0 < p) :
    extrapolant Q p ∈ legalSeedSpan allPositiveSeeds := by
  have hs := (legalSeedSpan allPositiveSeeds).sub_mem
    ((legalSeedSpan allPositiveSeeds).smul_mem (p : ℝ)
      (sieveResidue_mem_legal Q p hp))
    (sieveResidue_mem_legal Q 1 (by decide))
  convert hs using 1
  funext j
  simp only [extrapolant, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

theorem roughCount_mono_of_dvd (A Q j : ℕ) (hAQ : A ∣ Q) :
    sieveRoughCount Q j ≤ sieveRoughCount A j := by
  unfold sieveRoughCount cumulative
  apply Finset.sum_le_sum
  intro i hi
  dsimp only
  by_cases hQ : Nat.gcd Q (i+1) = 1
  · have hA : Nat.gcd A (i+1) = 1 := by
      have hd : Nat.gcd A (i+1) ∣ Nat.gcd Q (i+1) := Nat.dvd_gcd
        (dvd_trans (Nat.gcd_dvd_left A (i+1)) hAQ)
        (Nat.gcd_dvd_right A (i+1))
      rw [hQ] at hd
      exact Nat.dvd_one.mp hd
    simp [hQ, hA]
  · simp only [if_neg hQ]
    split_ifs <;> norm_num

theorem roughCount_six_exact (j : ℕ) :
    sieveRoughCount 6 j = (j : ℝ) - ((j/2 : ℕ) : ℝ) -
      ((j/3 : ℕ) : ℝ) + ((j/6 : ℕ) : ℝ) := by
  have hd : (6 : ℕ).divisors = {1,2,3,6} := by decide
  have hm6 : ArithmeticFunction.moebius 6 = 1 := by
    rw [show 6 = 2*3 by rfl, moebius_prime_mul 2 3 (by decide)]
    norm_num [ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 3)]
  have hf := sieve_floor_count 6 j (by decide)
  rw [hd] at hf
  norm_num [ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 3), hm6] at hf
  nlinarith [hf]

theorem roughCount_six_le (j : ℕ) : sieveRoughCount 6 j ≤ (j : ℝ)/3 + 2 := by
  rw [roughCount_six_exact]
  have hn2 : j ≤ 2*(j/2)+1 := by omega
  have hn3 : j ≤ 3*(j/3)+2 := by omega
  have hn6 : 6*(j/6) ≤ j := by omega
  have h2 : (j : ℝ) ≤ 2*((j/2 : ℕ) : ℝ)+1 := by exact_mod_cast hn2
  have h3 : (j : ℝ) ≤ 3*((j/3 : ℕ) : ℝ)+2 := by exact_mod_cast hn3
  have h6 : 6*((j/6 : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hn6
  nlinarith

theorem roughCount_le_six (Q j : ℕ) (h6Q : 6 ∣ Q) :
    sieveRoughCount Q j ≤ (j : ℝ)/3 + 2 :=
  (roughCount_mono_of_dvd 6 Q j h6Q).trans (roughCount_six_le j)

theorem roughCount_one (Q : ℕ) : sieveRoughCount Q 1 = 1 := by
  simp [sieveRoughCount, cumulative, Finset.filter_singleton]

theorem extrapolant_factorial_head (Y p j : ℕ) (hj : 0 < j)
    (hjY : j ≤ Y) (hYp : Y < p) : extrapolant Y.factorial p j = 1 := by
  have hp : 0 < p := by omega
  rw [extrapolant_count _ _ _ (Nat.factorial_pos Y) hp,
    sieveRoughCount_factorial_head Y j hj hjY,
    Nat.div_eq_of_lt (by omega : j < p), sieveRoughCount_zero, mul_zero, sub_zero]

theorem extrapolant_block_upper (Q p j : ℕ) (hQ : 0 < Q) (hp : 0 < p)
    (h6Q : 6 ∣ Q) (hj : j ∈ Finset.Ico p (2*p)) :
    extrapolant Q p j ≤ -(p : ℝ)/3 + 2 := by
  have hdiv : j/p = 1 := by
    apply Nat.div_eq_of_lt_le
    · simpa using (Finset.mem_Ico.mp hj).1
    · simpa [Nat.mul_comm] using (Finset.mem_Ico.mp hj).2
  rw [extrapolant_count Q p j hQ hp, hdiv, roughCount_one, mul_one]
  have hc := roughCount_le_six Q j h6Q
  have hjp : (j : ℝ) ≤ 2*(p : ℝ) := by
    exact_mod_cast (Finset.mem_Ico.mp hj).2.le
  nlinarith

theorem block_energy_lower (f : ℕ → ℝ) (p : ℕ) (hp : 0 < p)
    (B : ℝ) (hB : 0 ≤ B) (hf : ∀ j ∈ Finset.Ico p (2*p), B ≤ |f j|) :
    B^2/(2*(p : ℝ)) ≤ ∑ j ∈ Finset.Ico p (2*p), positiveWeight j*(f j)^2 := by
  have hw : (∑ j ∈ Finset.Ico p (2*p), positiveWeight j) = 1/(2*(p : ℝ)) := by
    rw [positiveWeight_interval p (2*p) hp (by omega)]
    push_cast
    have hp0 : (p : ℝ) ≠ 0 := by positivity
    field_simp [hp0]
    ring
  calc
    _ = (∑ j ∈ Finset.Ico p (2*p), positiveWeight j)*B^2 := by rw [hw]; ring
    _ = ∑ j ∈ Finset.Ico p (2*p), positiveWeight j*B^2 := by rw [Finset.sum_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (positiveWeight_nonneg j)
      have hh := mul_self_le_mul_self hB (hf j hj)
      simpa only [← pow_two, sq_abs] using hh

theorem extrapolant_block_norm_lower (Q p : ℕ) (hQ : 0 < Q)
    (hp : 0 < p) (h6Q : 6 ∣ Q) :
    (max ((p : ℝ)/3-2) 0)^2/(2*(p : ℝ)) ≤
      ∑ j ∈ Finset.Ico p (2*p), positiveWeight j*(extrapolant Q p j)^2 := by
  apply block_energy_lower _ p hp _ (le_max_right _ _)
  intro j hj
  have hu := extrapolant_block_upper Q p j hQ hp h6Q hj
  by_cases hB : 0 ≤ (p : ℝ)/3-2
  · rw [max_eq_left hB]
    have hf : extrapolant Q p j ≤ 0 := by linarith
    rw [abs_of_nonpos hf]
    linarith
  · rw [max_eq_right (le_of_not_ge hB)]
    exact abs_nonneg _

theorem extrapolant_block_error_lower (Q p : ℕ) (hQ : 0 < Q)
    (hp : 0 < p) (h6Q : 6 ∣ Q) :
    (max ((p : ℝ)/3-1) 0)^2/(2*(p : ℝ)) ≤
      ∑ j ∈ Finset.Ico p (2*p), positiveWeight j*(1-extrapolant Q p j)^2 := by
  apply block_energy_lower _ p hp _ (le_max_right _ _)
  intro j hj
  have hu := extrapolant_block_upper Q p j hQ hp h6Q hj
  by_cases hB : 0 ≤ (p : ℝ)/3-1
  · rw [max_eq_left hB]
    have hf : 0 ≤ 1-extrapolant Q p j := by linarith
    rw [abs_of_nonneg hf]
    linarith
  · rw [max_eq_right (le_of_not_ge hB)]
    exact abs_nonneg _

private theorem residueFraction_abs_le_one_all (d j : ℕ) : |residueFraction d j| ≤ 1 := by
  by_cases hd : d = 0
  · simp [hd, residueFraction]
  · exact residueFraction_abs_le_one d j (Nat.pos_of_ne_zero hd)

def coefficientCap (Q : ℕ) : ℝ := ∑ d ∈ Q.divisors, |(ArithmeticFunction.moebius d : ℝ)|

theorem sieveResidue_abs_le_cap (Q n j : ℕ) : |sieveResidue Q n j| ≤ coefficientCap Q := by
  have hs := bounded_finsetCombination Q.divisors
    (fun d => (ArithmeticFunction.moebius d : ℝ))
    (f := fun d => residueFraction (n*d)) (B := fun _ => (1 : ℝ))
    (fun d k => residueFraction_abs_le_one_all (n*d) k) j
  simpa only [sieveResidue, coefficientCap, mul_one] using hs

theorem extrapolant_abs_le (Q p j : ℕ) :
    |extrapolant Q p j| ≤ (p : ℝ)*coefficientCap Q + coefficientCap Q := by
  unfold extrapolant
  calc
    _ ≤ |(p : ℝ)*sieveResidue Q p j| + |sieveResidue Q 1 j| := by simpa only [sub_eq_add_neg, abs_neg] using abs_add_le ((p : ℝ)*sieveResidue Q p j) (-sieveResidue Q 1 j)
    _ = (p : ℝ)*|sieveResidue Q p j| + |sieveResidue Q 1 j| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg p)]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (sieveResidue_abs_le_cap Q p j) (Nat.cast_nonneg p))
      (sieveResidue_abs_le_cap Q 1 j)

theorem extrapolant_square_summable (Q p : ℕ) :
    Summable (fun j => positiveWeight j*(extrapolant Q p j)^2) := by
  have hb := fun j => extrapolant_abs_le Q p j
  simpa only [pow_two] using weighted_summable_of_bounded (bounded_product hb hb)

theorem extrapolant_error_square_summable (Q p : ℕ) :
    Summable (fun j => positiveWeight j*(1-extrapolant Q p j)^2) := by
  have hb : ∀ j, |1-extrapolant Q p j| ≤ 1 +
      ((p : ℝ)*coefficientCap Q + coefficientCap Q) := by
    intro j
    have hs := abs_add_le (1 : ℝ) (-extrapolant Q p j)
    rw [abs_one, abs_neg] at hs
    change |1 - extrapolant Q p j| ≤ 1 + |extrapolant Q p j| at hs
    linarith [extrapolant_abs_le Q p j]
  simpa only [pow_two] using weighted_summable_of_bounded (bounded_product hb hb)

theorem extrapolant_full_norm_lower (Q p : ℕ) (hQ : 0 < Q)
    (hp : 0 < p) (h6Q : 6 ∣ Q) :
    (max ((p : ℝ)/3-2) 0)^2/(2*(p : ℝ)) ≤
      paretoInner (extrapolant Q p) (extrapolant Q p) := by
  have hf := (extrapolant_square_summable Q p).sum_le_tsum
    (Finset.Ico p (2*p)) (fun j hj =>
      mul_nonneg (positiveWeight_nonneg j) (sq_nonneg _))
  simpa only [paretoInner, pow_two] using
    (extrapolant_block_norm_lower Q p hQ hp h6Q).trans hf

theorem extrapolant_full_error_lower (Q p : ℕ) (hQ : 0 < Q)
    (hp : 0 < p) (h6Q : 6 ∣ Q) :
    (max ((p : ℝ)/3-1) 0)^2/(2*(p : ℝ)) ≤
      paretoInner (fun j => 1-extrapolant Q p j) (fun j => 1-extrapolant Q p j) := by
  have hf := (extrapolant_error_square_summable Q p).sum_le_tsum
    (Finset.Ico p (2*p)) (fun j hj =>
      mul_nonneg (positiveWeight_nonneg j) (sq_nonneg _))
  simpa only [paretoInner, pow_two] using
    (extrapolant_block_error_lower Q p hQ hp h6Q).trans hf

end RiemannResearch.RH.Pareto.PrimorialExtrapolation

namespace RiemannResearch.RH.Pareto.PrimorialExtrapolation
open RiemannResearch.RH.Pareto
open RiemannResearch.RH.ArithmeticCumulative

theorem direct_prime_divisor_transform (p Q : ℕ) (hp : p.Prime)
    (hQ : 0 < Q) (hpQ : ¬ p ∣ Q) (F : ℕ → ℝ) :
    (∑ d ∈ (p*Q).divisors, (ArithmeticFunction.moebius d : ℝ)*F d) =
      (∑ d ∈ Q.divisors, (ArithmeticFunction.moebius d : ℝ)*F d) -
        ∑ d ∈ Q.divisors, (ArithmeticFunction.moebius d : ℝ)*F (p*d) := by
  have hpos : p*Q ≠ 0 := ne_of_gt (Nat.mul_pos hp.pos hQ)
  have hdiv (d : ℕ) (hd : d ∈ (p*Q).divisors) (hpd : ¬ p ∣ d) : d ∣ Q := by
    exact (hp.coprime_iff_not_dvd.mpr hpd).symm.dvd_mul_left.mp
      (Nat.dvd_of_mem_divisors hd)
  have hyes :
      (∑ d ∈ (p*Q).divisors.filter (fun d => p ∣ d),
        (ArithmeticFunction.moebius d : ℝ)*F d) =
      -(∑ d ∈ Q.divisors, (ArithmeticFunction.moebius d : ℝ)*F (p*d)) := by
    calc
      _ = ∑ d ∈ Q.divisors, (ArithmeticFunction.moebius (p*d) : ℝ)*F (p*d) := by
        symm
        apply Finset.sum_bij (fun d _ => p*d)
        · intro d hd
          simp only [Finset.mem_filter, Nat.mem_divisors]
          exact ⟨⟨Nat.mul_dvd_mul_left p (Nat.dvd_of_mem_divisors hd), hpos⟩,
            dvd_mul_right p d⟩
        · intro d hd e he h
          exact Nat.eq_of_mul_eq_mul_left hp.pos h
        · intro d hd
          rcases Finset.mem_filter.mp hd with ⟨hd, ⟨e, rfl⟩⟩
          refine ⟨e, ?_, rfl⟩
          exact Nat.mem_divisors.mpr ⟨(Nat.mul_dvd_mul_iff_left hp.pos).mp
            (Nat.dvd_of_mem_divisors hd), ne_of_gt hQ⟩
        · intro d hd
          rfl
      _ = _ := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro d hd
        have hpd : ¬ p ∣ d := fun h => hpQ (dvd_trans h (Nat.dvd_of_mem_divisors hd))
        rw [moebius_prime_mul p d hp, if_neg hpd]
        push_cast
        ring
  have hset : (p*Q).divisors.filter (fun d => ¬ p ∣ d) = Q.divisors := by
    ext d
    constructor
    · intro hd
      rcases Finset.mem_filter.mp hd with ⟨hd, hpd⟩
      exact Nat.mem_divisors.mpr ⟨hdiv d hd hpd, ne_of_gt hQ⟩
    · intro hd
      have hdQ := Nat.dvd_of_mem_divisors hd
      exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
        ⟨dvd_mul_of_dvd_right hdQ p, hpos⟩, fun h => hpQ (dvd_trans h hdQ)⟩
  rw [← Finset.sum_filter_add_sum_filter_not (p*Q).divisors (fun d => p ∣ d),
    hyes, hset]
  ring

theorem sieveResidue_prime_factor (p Q j : ℕ) (hp : p.Prime)
    (hQ : 0 < Q) (hpQ : ¬ p ∣ Q) :
    sieveResidue (p*Q) 1 j = sieveResidue Q 1 j - sieveResidue Q p j := by
  simp only [sieveResidue, Nat.one_mul]
  exact direct_prime_divisor_transform p Q hp hQ hpQ (fun d => residueFraction d j)

theorem extrapolation_eq_atom_combination (p Q j : ℕ) (hp : p.Prime)
    (hQ : 0 < Q) (hpQ : ¬ p ∣ Q) :
    (p : ℝ)*(-sieveResidue (Q*p) 1 j) - ((p : ℝ)-1)*(-sieveResidue Q 1 j) =
      (p : ℝ)*sieveResidue Q p j - sieveResidue Q 1 j := by
  rw [Nat.mul_comm Q p, sieveResidue_prime_factor p Q j hp hQ hpQ]
  ring

end RiemannResearch.RH.Pareto.PrimorialExtrapolation

namespace RiemannResearch.RH.Pareto.PrimorialExtrapolation
open Filter

private theorem obstruction_floor_ge_linear (p : ℝ) (hp : 12 ≤ p) :
    p/72 ≤ (max (p/3-2) 0)^2/(2*p) := by
  have hp0 : 0 < p := by linarith
  have hnonneg : 0 ≤ p/3-2 := by linarith
  rw [max_eq_left hnonneg]
  apply (le_div_iff₀ (mul_pos (by norm_num) hp0)).2
  nlinarith [sq_nonneg (p-12)]

/-- A cofinal large-prime family has divergent complete physical energy. -/
theorem extrapolant_full_energy_tendsto_atTop
    (Q p : ℕ → ℕ)
    (hp : Tendsto (fun i => (p i : ℝ)) atTop atTop)
    (hQ : ∀ i, 0 < Q i) (hp0 : ∀ i, 0 < p i) (h6Q : ∀ i, 6 ∣ Q i) :
    Tendsto (fun i => paretoInner (extrapolant (Q i) (p i))
      (extrapolant (Q i) (p i))) atTop atTop := by
  have hl : Tendsto (fun i => (p i : ℝ)/72) atTop atTop :=
    hp.atTop_div_const (by norm_num)
  have hb : ∀ᶠ i : ℕ in atTop, (p i : ℝ)/72 ≤
      paretoInner (extrapolant (Q i) (p i)) (extrapolant (Q i) (p i)) := by
    filter_upwards [hp.eventually (eventually_ge_atTop 12)] with i hi
    exact (obstruction_floor_ge_linear _ hi).trans
      (extrapolant_full_norm_lower _ _ (hQ i) (hp0 i) (h6Q i))
  exact tendsto_atTop_mono' atTop hb hl

end RiemannResearch.RH.Pareto.PrimorialExtrapolation
