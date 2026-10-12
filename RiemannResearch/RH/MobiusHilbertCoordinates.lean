import RiemannResearch.RH.MobiusDifferenceCLM
import RiemannResearch.RH.ParetoResidueDuality
import RiemannResearch.RH.ParetoDilation
import RiemannResearch.RH.ParetoGibbsTailBasis
import RiemannResearch.RH.ParetoNormalizedResidueHilbert
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Möbius coordinates on the actual Pareto Hilbert space

Source: the coefficient-stabilization argument developed with the user,
RH_Coefficient_Stabilization_Theorem_2026-09-18.md (coefficient recovery and
joint separation of points). Finite Möbius inversion and the already proved
exclusion of nonzero linear square-summable sequences supply the proofs.
No density or Riemann-hypothesis assertion is assumed.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.RH.ArithmeticCumulative

theorem mobius_coordinate_one (m : ℕ) (hm : 0 < m) :
    mobiusDifferenceCLM m hilbertOne = (ArithmeticFunction.moebius m : ℝ) := by
  rw [mobiusDifferenceCLM_apply, hilbertOne_sequence]
  exact mobiusDifference_one m hm

theorem sequence_linear_of_mobius_zero (f : ThresholdHilbert)
    (hf : ∀ m : ℕ, 1 < m → mobiusDifferenceCLM m f = 0) :
    ∀ n : ℕ, hilbertSequence f n = (n : ℝ) * hilbertSequence f 1 := by
  have hstep (n : ℕ) : hilbertSequence f (n+1) - hilbertSequence f n =
      hilbertSequence f 1 := by
    have hi := sum_mobiusDifference (hilbertSequence f) (n+1) (by omega)
    simp only [Nat.add_sub_cancel] at hi
    rw [← hi]
    calc
      (∑ d ∈ (n+1).divisors, mobiusDifference d (hilbertSequence f)) =
          ∑ d ∈ (n+1).divisors, if d = 1 then hilbertSequence f 1 else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        by_cases h1 : d = 1
        · subst d
          simp [mobiusDifference]
        · have hp := Nat.pos_of_mem_divisors hd
          rw [if_neg h1]
          simpa only [mobiusDifferenceCLM_apply] using hf d (by omega)
      _ = _ := by simp [Nat.mem_divisors]
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := hstep n
    rw [ih] at hs
    push_cast
    nlinarith

theorem zero_of_linear_hilbertSequence (f : ThresholdHilbert) (c : ℝ)
    (hf : ∀ n : ℕ, hilbertSequence f n = (n : ℝ) * c) : f = 0 := by
  have hs : Summable (fun n : ℕ => positiveWeight n * (c * (n : ℝ))^2) := by
    simpa only [hf, mul_comm c] using hilbertSequence_square_summable f
  have hc0 : c = 0 := (linear_square_summable_iff c).mp hs
  apply hilbertSequence_injective
  funext n
  rw [hf, hc0]
  cases n <;> simp [hilbertSequence]

theorem eq_zero_of_mobius_coordinates_zero (f : ThresholdHilbert)
    (hf : ∀ m : ℕ, 1 < m → mobiusDifferenceCLM m f = 0) : f = 0 :=
  zero_of_linear_hilbertSequence f _ (sequence_linear_of_mobius_zero f hf)

theorem mobius_normalizedResidue (m d : ℕ) (hm : 1 < m) (hd : 0 < d) :
    mobiusDifferenceCLM m (normalizedResidueHilbert d hd) =
      if m = d then -1 else 0 := by
  rw [mobiusDifferenceCLM_apply, normalizedResidueHilbert_sequence]
  have he : mobiusDifference m (residueFraction d) =
      mobiusDifference m (residue d) / (d : ℝ) := by
    simp only [mobiusDifference, residueFraction, residue, div_sub_div_same,
      mul_div_assoc, Finset.sum_div]
  rw [he, mobiusDifference_residue m d hm]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  split_ifs <;> simp_all



/-- The normalized Möbius-difference functional on a physical point vector. -/
theorem mobiusDifferenceCLM_paretoPoint (m k : ℕ) (hm : 0 < m) :
    mobiusDifferenceCLM m (paretoPointHilbert k) =
      (dualCoeff m (k + 1) : ℝ) := by
  rw [mobiusDifferenceCLM_apply, hilbertSequence_paretoPoint]
  unfold mobiusDifference paretoPointSequence
  have hp (d : ℕ) : d - 1 = k + 1 ↔ d = k + 2 := by omega
  simp_rw [hp, mul_sub, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_sub_distrib]
  have hfirst :
      (∑ d ∈ m.divisors,
        if d = k + 1 then (ArithmeticFunction.moebius (m / d) : ℝ) else 0) =
      if k + 1 ∣ m then (ArithmeticFunction.moebius (m / (k + 1)) : ℝ) else 0 := by
    simp [Nat.mem_divisors, ne_of_gt hm]
  have hsecond :
      (∑ d ∈ m.divisors,
        if d = k + 2 then (ArithmeticFunction.moebius (m / d) : ℝ) else 0) =
      if k + 2 ∣ m then (ArithmeticFunction.moebius (m / (k + 2)) : ℝ) else 0 := by
    simp [Nat.mem_divisors, ne_of_gt hm]
  rw [hfirst, hsecond]
  unfold dualCoeff
  have hadd : k + 1 + 1 = k + 2 := by omega
  rw [hadd]
  split_ifs <;> push_cast <;> ring

/-- Divisor coefficients have no positive-coordinate support beyond the conductor. -/
theorem dualCoeff_eq_zero_of_lt {m j : ℕ} (hm : 0 < m) (hj : m < j) :
    dualCoeff m j = 0 := by
  have hnd : ¬ j ∣ m := by
    intro hd
    have hle := Nat.le_of_dvd hm hd
    omega
  have hns : ¬ j + 1 ∣ m := by
    intro hd
    have hle := Nat.le_of_dvd hm hd
    omega
  simp [dualCoeff, hnd, hns]

/-- The actual Riesz vector, with no external representer-provider hypothesis. -/
def mobiusRieszHilbert (m : ℕ) : ThresholdHilbert :=
  (InnerProductSpace.toDual ℝ ThresholdHilbert).symm (mobiusDifferenceCLM m)

/-- Defining Riesz pairing, holding on the entire Pareto Hilbert space. -/
theorem mobiusRieszHilbert_inner (m : ℕ) (f : ThresholdHilbert) :
    inner ℝ (mobiusRieszHilbert m) f = mobiusDifferenceCLM m f := by
  have h := congrArg (fun ℓ : ThresholdHilbert →L[ℝ] ℝ => ℓ f)
    ((InnerProductSpace.toDual ℝ ThresholdHilbert).apply_symm_apply
      (mobiusDifferenceCLM m))
  exact h

/-- The Riesz isometry identifies operator norm with actual Hilbert norm. -/
theorem mobiusRieszHilbert_norm (m : ℕ) :
    ‖mobiusRieszHilbert m‖ = ‖mobiusDifferenceCLM m‖ :=
  (InnerProductSpace.toDual ℝ ThresholdHilbert).symm.norm_map _

/-- Every positive physical coordinate of the representer is explicit. -/
theorem mobiusRieszHilbert_sequence_succ (m k : ℕ) (hm : 0 < m) :
    hilbertSequence (mobiusRieszHilbert m) (k + 1) =
      ((k : ℝ) + 1) * ((k : ℝ) + 2) * (dualCoeff m (k + 1) : ℝ) := by
  have h := mobiusRieszHilbert_inner m (paretoPointHilbert k)
  rw [inner_paretoPoint, hilbertGibbsPhysical_eq,
    mobiusDifferenceCLM_paretoPoint m k hm] at h
  apply mul_left_cancel₀ (ne_of_gt (paretoWeight_pos k))
  rw [h]
  unfold paretoWeight
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
  field_simp [hk1, hk2]

/-- The anchored zero coordinate is included in this formula. -/
theorem mobiusRieszHilbert_sequence (m j : ℕ) (hm : 0 < m) :
    hilbertSequence (mobiusRieszHilbert m) j =
      (j : ℝ) * ((j : ℝ) + 1) * (dualCoeff m j : ℝ) := by
  cases j with
  | zero => simp
  | succ k =>
    simpa only [Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one,
      show (k : ℝ) + 1 + 1 = (k : ℝ) + 2 by ring] using
      mobiusRieszHilbert_sequence_succ m k hm

/-- The exact squared dual norm for every positive conductor.
This retains overlapping divisor contributions inside `dualCoeff` before squaring. -/
theorem mobiusDifferenceCLM_norm_sq (m : ℕ) (hm : 0 < m) :
    ‖mobiusDifferenceCLM m‖ ^ 2 =
      ∑ j ∈ Finset.Icc 1 m,
        (j : ℝ) * ((j : ℝ) + 1) * (dualCoeff m j : ℝ) ^ 2 := by
  rw [← mobiusRieszHilbert_norm, hilbert_norm_weighted_sq]
  rw [tsum_eq_sum (s := Finset.Icc 1 m) (by
    intro j hj
    by_cases hj0 : j = 0
    · simp [hj0]
    · have hgt : m < j := by
        have hn : ¬ (1 ≤ j ∧ j ≤ m) := by simpa only [Finset.mem_Icc] using hj
        omega
      rw [mobiusRieszHilbert_sequence m j hm, dualCoeff_eq_zero_of_lt hm hgt]
      simp)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mobiusRieszHilbert_sequence m j hm]
  have hjpos : 0 < j := (Finset.mem_Icc.mp hj).1
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hjpos
  have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
  unfold positiveWeight
  field_simp [hjR, hj1]


end RiemannResearch.RH.Pareto
