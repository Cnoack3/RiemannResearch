import RiemannResearch.RH.ParetoCoprimeDefectVariational

/-!
# A concrete sign obstruction for normalized odd-moment witnesses

Source: independently derived continuation of the user-provided Pareto
capacity handoff (2026-09-21); no novelty claim is intended.
The physical site two alone rules out nonnegative small-energy witnesses.
All statements use the actual full Pareto tail norm.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.RH.ArithmeticCumulative

theorem tailAtom_value_two (i : ℕ) :
    hilbertSequence (tailAtom i) 2 = residueFraction (i+2) 2 := by
  change hilbertSequenceLinear
    (residueAtom i - anchoredEvaluationCLM 1 (residueAtom i) • paretoPointHilbert 0) 2 = _
  rw [map_sub, map_smul]
  change hilbertSequence (residueAtom i) 2 -
    anchoredEvaluationCLM 1 (residueAtom i) * hilbertSequence (paretoPointHilbert 0) 2 = _
  rw [residueAtom, normalizedResidueHilbert_sequence, hilbertSequence_paretoPoint]
  simp [paretoPointSequence]

theorem tailCombination_value_two (n : ℕ) (c : Fin n → ℝ) :
    hilbertSequence (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c) 2 =
      ∑ i, c i * residueFraction (i.val+2) 2 := by
  change hilbertSequenceLinear (Fintype.linearCombination ℝ _ c) 2 = _
  simp only [Fintype.linearCombination_apply, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ i, c i * hilbertSequence (tailAtom i.val) 2) = _
  simp only [tailAtom_value_two]

/-- Nonnegative coefficients with odd moment one force a value at least six at site two. -/
theorem nonnegative_oddMoment_value_two_lower (n : ℕ) (c : Fin n → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hm : (∑ i, if 2 ∣ i.val+2 then 0 else c i / ((i.val+2 : ℕ) : ℝ)^2) = 1) :
    6 ≤ hilbertSequence
      (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c) 2 := by
  rw [tailCombination_value_two]
  have hterm (i : Fin n) :
      6 * (if 2 ∣ i.val+2 then 0 else c i / ((i.val+2 : ℕ) : ℝ)^2) ≤
        c i * residueFraction (i.val+2) 2 := by
    by_cases hi : 2 ∣ i.val+2
    · rw [if_pos hi, mul_zero]
      exact mul_nonneg (hc i) (by unfold residueFraction; positivity)
    · have hd : 3 ≤ i.val+2 := by omega
      have hR : (3 : ℝ) ≤ ((i.val+2 : ℕ) : ℝ) := by exact_mod_cast hd
      have hp : (0 : ℝ) < ((i.val+2 : ℕ) : ℝ) := by positivity
      have hs : 6 / ((i.val+2 : ℕ) : ℝ)^2 ≤ 2 / ((i.val+2 : ℕ) : ℝ) := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hp) hp).mpr
        nlinarith
      rw [if_neg hi, residueFraction, Nat.mod_eq_of_lt (by omega : 2 < i.val+2)]
      change 6 * (c i / ((i.val+2 : ℕ) : ℝ)^2) ≤ c i * (2 / ((i.val+2 : ℕ) : ℝ))
      calc
        _ = c i * (6 / ((i.val+2 : ℕ) : ℝ)^2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hs (hc i)
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  rwa [← Finset.mul_sum, hm, mul_one] at h

/-- The full tail energy is at least six, independently of dictionary size. -/
theorem nonnegative_oddMoment_energy_lower (n : ℕ) (c : Fin n → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hm : (∑ i, if 2 ∣ i.val+2 then 0 else c i / ((i.val+2 : ℕ) : ℝ)^2) = 1) :
    6 ≤ ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖^2 := by
  let f := Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c
  have hv : 6 ≤ hilbertSequence f 2 := nonnegative_oddMoment_value_two_lower n c hc hm
  have hs := (hilbertSequence_square_summable f).le_tsum 2
    (fun k _ => mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _))
  rw [← hilbert_norm_weighted_sq] at hs
  rw [show positiveWeight 2 = (1/6 : ℝ) by norm_num [positiveWeight]] at hs
  change 6 ≤ ‖f‖^2
  nlinarith

/-- Every normalized witness with energy below six has a negative coefficient. -/
theorem oddMoment_small_energy_requires_negative (n : ℕ) (c : Fin n → ℝ)
    (hm : (∑ i, if 2 ∣ i.val+2 then 0 else c i / ((i.val+2 : ℕ) : ℝ)^2) = 1)
    (he : ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖^2 < 6) :
    ∃ i, c i < 0 := by
  by_contra h
  push Not at h
  exact (not_le_of_gt he) (nonnegative_oddMoment_energy_lower n c h hm)

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
