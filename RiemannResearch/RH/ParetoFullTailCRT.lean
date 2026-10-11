import RiemannResearch.RH.ParetoProgressionDigamma
import RiemannResearch.RH.ParetoFiniteGram
import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.RH.ParetoNormalizedResidueHilbert

/-!
# Exact CRT formulas after removing only the first physical coordinate

Source: user-provided
`RH_First_Coordinate_and_Tail_Capacity_Continuation_2026-09-19.md`,
Section 13, for the statement and proof strategy. The exact progression
integral and digamma identities are already established in
`ParetoProgressionIntegral` and `ParetoProgressionDigamma`. This module
specializes the actual weighted regrouping to the complete physical tail.
No uniform residue weight, physical cutoff, or Cesaro energy is substituted.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative

/-- Remove exactly coordinate one, while retaining every coordinate at least two. -/
theorem pareto_full_tail_inner (f g : ℕ → ℝ) {C D : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hg : ∀ k, |g k| ≤ D) :
    (∑' k : ℕ, positiveWeight (k + 2) * (f (k + 2) * g (k + 2))) =
      paretoInner f g - f 1 * g 1 / 2 := by
  have hs := weighted_summable_of_bounded (bounded_product hf hg)
  have h := hs.sum_add_tsum_nat_add 2
  have hh : (∑ k ∈ Finset.range 2,
      positiveWeight k * (f k * g k)) = f 1 * g 1 / 2 := by
    norm_num [Finset.sum_range_succ, positiveWeight]
    ring
  rw [hh] at h
  change f 1 * g 1 / 2 +
    (∑' k : ℕ, positiveWeight (k + 2) * (f (k + 2) * g (k + 2))) =
      paretoInner f g at h
  linarith

/-- The finite residue expression is the entire signed physical tail. -/
theorem periodic_pareto_full_tail_inner (Q : ℕ) (hQ : 0 < Q)
    (f g : ℕ → ℝ) {C D : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hg : ∀ k, |g k| ≤ D)
    (hpf : ∀ k, f (k + Q) = f k) (hpg : ∀ k, g (k + Q) = g k) :
    (∑' k : ℕ, positiveWeight (k + 2) * (f (k + 2) * g (k + 2))) =
      (∑ r : Fin Q, progressionWeight Q (r.val + 1) *
        (f (r.val + 1) * g (r.val + 1))) - f 1 * g 1 / 2 := by
  rw [pareto_full_tail_inner f g hf hg,
    periodic_paretoInner_mixed Q hQ f g hf hg hpf hpg]

private theorem normalizedResidue_bounded (d : ℕ) (hd : 0 < d) :
    ∀ k, |residueFraction d k| ≤ 1 := by
  intro k
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hm : ((k % d : ℕ) : ℝ) ≤ d := by
    exact_mod_cast (Nat.mod_lt k hd).le
  unfold residueFraction
  rw [abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ hdR).2
  simpa using hm

private theorem normalizedResidue_period (d Q : ℕ) (hdiv : d ∣ Q) :
    ∀ k, residueFraction d (k + Q) = residueFraction d k := by
  intro k
  simp [residueFraction, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdiv]

/-- Section 13.2 for any common period, and therefore for the pairwise lcm.
The subtraction removes physical coordinate one, not its whole CRT class. -/
theorem normalizedResidue_full_tail_crt (d e Q : ℕ)
    (hd : 1 < d) (he : 1 < e) (hQ : 0 < Q)
    (hdQ : d ∣ Q) (heQ : e ∣ Q) :
    (∑' k : ℕ, positiveWeight (k + 2) *
      (residueFraction d (k + 2) * residueFraction e (k + 2))) =
      (∑ r : Fin Q, progressionWeight Q (r.val + 1) *
        (residueFraction d (r.val + 1) * residueFraction e (r.val + 1))) -
        1 / (2 * (d : ℝ) * (e : ℝ)) := by
  rw [periodic_pareto_full_tail_inner Q hQ (residueFraction d) (residueFraction e)
    (normalizedResidue_bounded d (by omega)) (normalizedResidue_bounded e (by omega))
    (normalizedResidue_period d Q hdQ) (normalizedResidue_period e Q heQ)]
  simp only [residueFraction, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt he,
    Nat.cast_one]
  congr 1
  ring

/-- The actual bundled Hilbert Gram entry has precisely the same CRT formula. -/
theorem normalizedResidue_hilbert_tail_crt (d e Q : ℕ)
    (hd : 1 < d) (he : 1 < e) (hQ : 0 < Q)
    (hdQ : d ∣ Q) (heQ : e ∣ Q) :
    inner ℝ (normalizedResidueHilbert d (by omega))
        (normalizedResidueHilbert e (by omega)) - 1 / (2 * (d : ℝ) * (e : ℝ)) =
      (∑ r : Fin Q, progressionWeight Q (r.val + 1) *
        (residueFraction d (r.val + 1) * residueFraction e (r.val + 1))) -
        1 / (2 * (d : ℝ) * (e : ℝ)) := by
  rw [hilbert_inner_weighted, normalizedResidueHilbert_sequence,
    normalizedResidueHilbert_sequence,
    periodic_paretoInner_mixed Q hQ _ _
      (normalizedResidue_bounded d (by omega)) (normalizedResidue_bounded e (by omega))
      (normalizedResidue_period d Q hdQ) (normalizedResidue_period e Q heQ)]

/-- A finite exact special-function formula for each full-tail matrix entry. -/
theorem normalizedResidue_full_tail_digamma (d e Q : ℕ)
    (hd : 1 < d) (he : 1 < e) (hQ : 0 < Q)
    (hdQ : d ∣ Q) (heQ : e ∣ Q) :
    (∑' k : ℕ, positiveWeight (k + 2) *
      (residueFraction d (k + 2) * residueFraction e (k + 2))) =
      (∑ r : Fin Q,
        (1 / (Q : ℝ) *
          ((Complex.digamma ((((r.val : ℝ) + 2) / Q : ℝ) : ℂ)).re -
           (Complex.digamma ((((r.val : ℝ) + 1) / Q : ℝ) : ℂ)).re)) *
        (residueFraction d (r.val + 1) * residueFraction e (r.val + 1))) -
        1 / (2 * (d : ℝ) * (e : ℝ)) := by
  rw [normalizedResidue_full_tail_crt d e Q hd he hQ hdQ heQ]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [progressionWeight_eq_digamma Q (r.val + 1) hQ (by omega) (by omega)]
  push_cast
  ring

/-- Section 13.3 as an exact full-tail energy, including every signed cross term. -/
theorem normalizedResidue_combination_full_tail_crt
    (s : Finset ℕ) (a : ℕ → ℝ) (Q : ℕ) (hQ : 0 < Q)
    (hd : ∀ d ∈ s, 1 < d) (hdiv : ∀ d ∈ s, d ∣ Q) :
    (∑' k : ℕ, positiveWeight (k + 2) *
      (∑ d ∈ s, a d * residueFraction d (k + 2)) ^ 2) =
      (∑ r : Fin Q, progressionWeight Q (r.val + 1) *
        (∑ d ∈ s, a d * residueFraction d (r.val + 1)) ^ 2) -
        (∑ d ∈ s, a d / (d : ℝ)) ^ 2 / 2 := by
  let F : ℕ → ℝ := fun k => ∑ d ∈ s, a d * residueFraction d k
  have hf : ∀ k, |F k| ≤ ∑ d ∈ s, |a d| := by
    intro k
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro d hds
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (normalizedResidue_bounded d (by have := hd d hds; omega) k) (abs_nonneg (a d))
  have hp : ∀ k, F (k + Q) = F k := by
    intro k
    dsimp [F]
    apply Finset.sum_congr rfl
    intro d hds
    rw [normalizedResidue_period d Q (hdiv d hds) k]
  have hh : F 1 = ∑ d ∈ s, a d / (d : ℝ) := by
    dsimp [F]
    apply Finset.sum_congr rfl
    intro d hds
    simp only [residueFraction, Nat.mod_eq_of_lt (hd d hds), Nat.cast_one]
    ring
  have h := periodic_pareto_full_tail_inner Q hQ F F hf hf hp hp
  rw [hh] at h
  simpa only [F, ← pow_two] using h

end RiemannResearch.RH.Pareto
