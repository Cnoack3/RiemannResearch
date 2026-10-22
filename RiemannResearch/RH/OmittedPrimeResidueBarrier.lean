import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.ParetoPrimeDualNorm
import RiemannResearch.RH.ThresholdHilbertAdjoint

/-!
# Permanent approximation barriers when a prime modulus is omitted

Source: user-provided `RH_First_Coordinate_and_Tail_Capacity_Continuation_2026-09-19.md`,
Section 18, for the statements and proof strategy. These results use the full
Pareto norm and the actual normalized residue functions. The hypothesis that
the prime coefficient vanishes describes a closed hyperplane and includes all
finite combinations from a dictionary omitting that modulus. No RH hypothesis
or all-modulus approximation bound occurs.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- The exact jump recovers the coefficient of a prime modulus. -/
theorem prime_jump (f : ThresholdHilbert) (p : ℕ) (hp : p.Prime) :
    hilbertSequence f p - hilbertSequence f (p - 1) =
      hilbertSequence f 1 - coefficientCLM p f := by
  have h := mobiusDifference_prime p hp (hilbertSequence f) (by simp)
  rw [← mobiusDifferenceCLM_apply] at h
  simp only [coefficientCLM, neg_apply]
  linarith

/-- Section 18.1 with the actual finite synthesis coefficients. -/
theorem prime_jump_finite_sum (n : ℕ) (a : Fin n → ℝ) (i : Fin n)
    (hp : (i.val + 2).Prime) :
    hilbertSequence (∑ j : Fin n, a j • residueAtom j.val) (i.val + 2) -
        hilbertSequence (∑ j : Fin n, a j • residueAtom j.val) (i.val + 1) =
      hilbertSequence (∑ j : Fin n, a j • residueAtom j.val) 1 - a i := by
  have h := prime_jump (∑ j : Fin n, a j • residueAtom j.val) (i.val + 2) hp
  rw [coefficient_finite_sum] at h
  simpa only [show i.val + 2 - 1 = i.val + 1 by omega] using h

/-- Every finite signed combination omitting modulus p has coefficient zero. -/
theorem coefficient_eq_zero_of_omitted_modulus (s : Finset ℕ) (a : ℕ → ℝ)
    (p : ℕ) (hp : 1 < p) (homit : ∀ i ∈ s, i + 2 ≠ p) :
    coefficientCLM p (∑ i ∈ s, a i • residueAtom i) = 0 := by
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [map_smul]
  have hne : p ≠ i + 2 := Ne.symm (homit i hi)
  simp [coefficientCLM, residueAtom, mobius_normalizedResidue p (i + 2) hp,
    hne]

/-- The omission relation survives closure in the full Hilbert norm. -/
theorem coefficient_eq_zero_of_mem_omitted_modulus_closure (p : ℕ) (hp : 1 < p)
    (f : ThresholdHilbert)
    (hf : f ∈ closure
      ((Submodule.span ℝ (residueAtom '' {i : ℕ | i + 2 ≠ p})) :
        Set ThresholdHilbert)) :
    coefficientCLM p f = 0 := by
  have hsub : Submodule.span ℝ (residueAtom '' {i : ℕ | i + 2 ≠ p}) ≤
      LinearMap.ker (coefficientCLM p).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro g ⟨i, hi, rfl⟩
    change coefficientCLM p (residueAtom i) = 0
    have hne : p ≠ i + 2 := Ne.symm hi
    simp [coefficientCLM, residueAtom, mobius_normalizedResidue p (i + 2) hp,
      hne]
  have hclosed : IsClosed {g : ThresholdHilbert | coefficientCLM p g = 0} :=
    isClosed_eq (coefficientCLM p).continuous continuous_const
  exact closure_minimal hsub hclosed hf

/-- The complete point approximation error has a uniform positive lower bound.
This applies to every vector in the coefficient kernel, including its closed
restricted dictionary spans, rather than only to a particular finite cutoff. -/
theorem omitted_prime_point_error_bound (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (f : ThresholdHilbert) (homit : coefficientCLM p f = 0) :
    1 / (2 * ((p : ℝ) ^ 2 + 1)) ≤ ‖paretoPointHilbert 0 - f‖ ^ 2 := by
  have hj := prime_jump f p hp
  rw [homit, sub_zero] at hj
  have hp1 : p ≠ 1 := by omega
  have hm1 : p - 1 ≠ 1 := by omega
  have hval :
      hilbertSequence (paretoPointHilbert 0 - f) p -
          hilbertSequence (paretoPointHilbert 0 - f) (p - 1) -
          hilbertSequence (paretoPointHilbert 0 - f) 1 = -1 := by
    simp only [hilbertSequence_sub, Pi.sub_apply, hilbertSequence_paretoPoint,
      paretoPointSequence, Nat.zero_add, if_neg hp1, if_neg hm1, ite_true]
    linarith
  have hb := prime_dual_full_sq_bound p hp3
    (hilbertSequence (paretoPointHilbert 0 - f))
    (hilbertSequence_square_summable (paretoPointHilbert 0 - f))
  rw [hval] at hb
  have hnorm : paretoInner (hilbertSequence (paretoPointHilbert 0 - f))
      (hilbertSequence (paretoPointHilbert 0 - f)) =
      ‖paretoPointHilbert 0 - f‖ ^ 2 := by
    rw [hilbert_norm_weighted_sq]
    simp only [paretoInner, pow_two]
  rw [hnorm] at hb
  have hc : 0 < 2 * ((p : ℝ) ^ 2 + 1) := by positivity
  apply (div_le_iff₀ hc).2
  nlinarith

/-- Exact two-coordinate completion of the square. -/
theorem prime_tail_pair_identity (p x : ℝ) (hp : 1 < p) :
    x ^ 2 / ((p - 1) * p) + (x + 1) ^ 2 / (p * (p + 1)) =
      (2 / (p ^ 2 - 1)) * (x + (p - 1) / (2 * p)) ^ 2 +
        1 / (2 * p ^ 2) := by
  have hp0 : p ≠ 0 := by linarith
  have hm0 : p - 1 ≠ 0 := by linarith
  have hplus : p + 1 ≠ 0 := by linarith
  have hs0 : p ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp
  ring

/-- Full-tail energy barrier for every head-one vector with omitted prime coefficient.
The right side is exactly the physical energy after deleting coordinate one. -/
theorem omitted_prime_tail_energy_bound (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (f : ThresholdHilbert) (hhead : hilbertSequence f 1 = 1)
    (homit : coefficientCLM p f = 0) :
    1 / (2 * (p : ℝ) ^ 2) ≤ ‖f‖ ^ 2 - 1 / 2 := by
  have hj := prime_jump f p hp
  rw [hhead, homit, sub_zero] at hj
  have hp1 : p ≠ 1 := by omega
  have hm1 : p - 1 ≠ 1 := by omega
  have hmp : p - 1 ≠ p := by omega
  have hple : 1 ≤ p := by omega
  have hpR : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hfinite := (hilbertSequence_square_summable f).sum_le_tsum
    ({1, p - 1, p} : Finset ℕ)
    (fun k _ => mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _))
  rw [Finset.sum_insert (by simp [hm1, hp1, Ne.symm hm1, Ne.symm hp1]),
    Finset.sum_insert (by simp [hmp]), Finset.sum_singleton] at hfinite
  have hw1 : positiveWeight 1 = (1 : ℝ) / 2 := by norm_num [positiveWeight]
  have hwm : positiveWeight (p - 1) = 1 / (((p : ℝ) - 1) * p) := by
    simp only [positiveWeight, Nat.cast_sub hple, Nat.cast_one, sub_add_cancel]
  have hwp : positiveWeight p = 1 / ((p : ℝ) * (p + 1)) := rfl
  rw [hw1, hwm, hwp, hhead, ← hilbert_norm_weighted_sq] at hfinite
  have hpair := prime_tail_pair_identity (p : ℝ) (hilbertSequence f (p - 1)) hpR
  have hpred : hilbertSequence f p = hilbertSequence f (p - 1) + 1 := by linarith
  rw [hpred] at hfinite
  have hfinite' : (1 : ℝ) / 2 +
      ((hilbertSequence f (p - 1)) ^ 2 / (((p : ℝ) - 1) * p) +
        (hilbertSequence f (p - 1) + 1) ^ 2 / ((p : ℝ) * (p + 1))) ≤
          ‖f‖ ^ 2 := by
    calc
      _ = (1 / 2 : ℝ) * 1 ^ 2 +
          (1 / (((p : ℝ) - 1) * p) * (hilbertSequence f (p - 1)) ^ 2 +
            1 / ((p : ℝ) * (p + 1)) *
              (hilbertSequence f (p - 1) + 1) ^ 2) := by ring
      _ ≤ ‖f‖ ^ 2 := hfinite
  rw [hpair] at hfinite'
  have hs : 0 < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hnonneg : 0 ≤ (2 / ((p : ℝ) ^ 2 - 1)) *
      (hilbertSequence f (p - 1) + ((p : ℝ) - 1) / (2 * p)) ^ 2 := by positivity
  linarith

/-- The reciprocal capacity associated with such a head-one witness is bounded.
The energy-to-capacity identity, when available for an optimizer, specializes
this elementary reciprocal estimate to tau ≤ 2 p². -/
theorem omitted_prime_reciprocal_tail_bound (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (f : ThresholdHilbert) (hhead : hilbertSequence f 1 = 1)
    (homit : coefficientCLM p f = 0) :
    1 / (‖f‖ ^ 2 - 1 / 2) ≤ 2 * (p : ℝ) ^ 2 := by
  have h := omitted_prime_tail_energy_bound p hp hp3 f hhead homit
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hc : 0 < 2 * (p : ℝ) ^ 2 := by positivity
  have he : 0 < ‖f‖ ^ 2 - 1 / 2 := lt_of_lt_of_le (one_div_pos.mpr hc) h
  apply (div_le_iff₀ he).2
  have hm := (div_le_iff₀ hc).1 h
  nlinarith

end RiemannResearch.RH.Pareto.CoefficientStabilization
