import RiemannResearch.RH.MultiRangeFloorCoordinates
import RiemannResearch.RH.MultiRangeCertificateConvergence

/-! Delayed activation uses the entire correction support, including its anchor.
Source: Section 8 of RH_Multi_Range_Divisor_Corrections_2026-09-18.md. -/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open Probability.ConditionalIID Analysis.Cesaro

/-- Floors whose divisors exceed N cannot change any of the first N means. -/
theorem delayed_floor_correction_prefix (R : ℕ → ℝ) (s : Finset ℕ)
    (x : ℕ → ℝ) (N : ℕ) (hs : ∀ d ∈ s, N < d) :
    conditionalMeanPrefix (fun n => R n + ∑ d ∈ s, x d * (n / d : ℕ)) N =
      conditionalMeanPrefix R N := by
  have he (n : ℕ) (hn : n ≤ N) : (∑ d ∈ s, x d * (n / d : ℕ)) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    rw [Nat.div_eq_of_lt (hn.trans_lt (hs d hd))]
    simp
  unfold conditionalMeanPrefix
  apply Finset.sum_congr rfl
  intro k hk
  congr 2
  unfold cesaro
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  change R n + (∑ d ∈ s, x d * (n / d : ℕ)) = R n
  rw [he n ((Finset.mem_Icc.mp hn).2.trans (by have := Finset.mem_range.mp hk; omega)),add_zero]

/-- An exact finite lower obstruction for a legal corrected sequence; the sieve
baseline need not itself have finite infinite energy. -/
theorem delayed_floor_correction_energy_ge_prefix (R : ℕ → ℝ) (s : Finset ℕ)
    (x : ℕ → ℝ) (N : ℕ) (hs : ∀ d ∈ s, N < d)
    (hF : (fun n => R n + ∑ d ∈ s, x d * (n / d : ℕ)) ∈ legalSeedSpan (Set.Ici 1)) :
    conditionalMeanPrefix R N ≤
      conditionalMeanSquare (fun n => R n + ∑ d ∈ s, x d * (n / d : ℕ)) := by
  rw [← delayed_floor_correction_prefix R s x N hs]
  exact (legal_conditionalMeanSquare_summable (Set.Ici 1)
    (by intro a ha; exact ha) hF).sum_le_tsum (Finset.range N)
      (fun k _ => mul_nonneg (conditionalWeight_pos k).le (sq_nonneg _))

/-- A distant non-anchor divisor still activates at the balance anchor. -/
theorem divisorAnchorDirection_anchor_value (A d : ℕ) (hA : 0 < A) (hAd : A < d) :
    divisorAnchorDirection A d A = -(A : ℝ)/(d : ℝ) := by
  rw [divisorAnchorDirection_floor A d A hA (by omega),
    Nat.div_eq_of_lt hAd, Nat.div_self hA]
  simp [neg_div]

theorem divisorAnchorDirection_anchor_ne_zero (A d : ℕ) (hA : 0 < A) (hAd : A < d) :
    divisorAnchorDirection A d A ≠ 0 := by
  rw [divisorAnchorDirection_anchor_value A d hA hAd]
  have hd : 0 < d := by omega
  exact div_ne_zero (neg_ne_zero.mpr (by positivity)) (by positivity)

end RiemannResearch.RH.Pareto
