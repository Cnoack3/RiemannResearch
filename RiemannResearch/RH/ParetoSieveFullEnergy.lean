import RiemannResearch.RH.ParetoSieveMobiusBridge
import RiemannResearch.RH.ParetoOddMomentSignObstruction

/-!
An actual site-two test for the normalized all-divisor Möbius sieve.
This checks a full-energy quantity that is invisible to the vanishing
odd-pair contrast component. No asymptotic Euler-product input is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open CoefficientStabilization.TailCapacity
open RiemannResearch.RH.ArithmeticCumulative

theorem sieveMobiusTail_value_two (P : ℕ) (a : ℝ) (hP : P ≠ 0) (h2 : 2 ∣ P) :
    hilbertSequence (sieveMobiusTail P a) 2 = 2*sieveMobiusHead P a-a := by
  have hmem2 : 2 ∈ P.divisors.erase 1 := by
    exact Finset.mem_erase.mpr ⟨by decide, Nat.mem_divisors.mpr ⟨h2, hP⟩⟩
  have he (d : ℕ) (hd : d ∈ P.divisors.erase 1) :
      (-a*(ArithmeticFunction.moebius d : ℝ))*residueFraction d 2 =
      2*((-a*(ArithmeticFunction.moebius d : ℝ))/(d : ℝ)) -
        (if d=2 then a else 0) := by
    have hd2 := sieve_nonunit_divisor_ge_two P d hd
    by_cases hdval : d=2
    · subst d
      norm_num [residueFraction, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
      ring
    · have hlt : 2<d := by omega
      rw [if_neg hdval, sub_zero, residueFraction, Nat.mod_eq_of_lt hlt]
      push_cast
      ring
  have hv : hilbertSequence (sieveMobiusTail P a) 2 =
      ∑ d ∈ P.divisors.erase 1,
        (-a*(ArithmeticFunction.moebius d : ℝ))*residueFraction d 2 := by
    change hilbertSequenceLinear (sieveMobiusTail P a) 2 = _
    simp only [sieveMobiusTail, map_sum, map_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro d hd
    have hd2 := sieve_nonunit_divisor_ge_two P d hd
    change (-a*(ArithmeticFunction.moebius d : ℝ))*hilbertSequence (tailAtom (d-2)) 2 =
      (-a*(ArithmeticFunction.moebius d : ℝ))*residueFraction d 2
    rw [tailAtom_value_two, Nat.sub_add_cancel hd2]
  rw [hv]
  calc
    _ = ∑ d ∈ P.divisors.erase 1,
        (2*((-a*(ArithmeticFunction.moebius d : ℝ))/(d : ℝ))-
          (if d=2 then a else 0)) := Finset.sum_congr rfl he
    _ = 2*sieveMobiusHead P a-a := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp [sieveMobiusHead, hmem2]

theorem sieveMobiusNormalizedTail_value_two (P : ℕ) (a : ℝ)
    (hP : P ≠ 0) (h2 : 2 ∣ P) :
    hilbertSequence (sieveMobiusNormalizedTail P a) 2 =
      2*sieveMobiusHead P a-a := by
  change hilbertSequenceLinear
    (sieveMobiusTail P a+(2*(oddHeadConstant-sieveMobiusHead P a)) • tailAtom 0) 2 = _
  rw [map_add, map_smul]
  change hilbertSequence (sieveMobiusTail P a) 2 +
    (2*(oddHeadConstant-sieveMobiusHead P a))*hilbertSequence (tailAtom 0) 2 = _
  rw [sieveMobiusTail_value_two P a hP h2, tailAtom_value_two]
  norm_num [residueFraction]

/-- A complete-tail lower bound from the actual normalized sieve value at two. -/
theorem sieveMobiusNormalizedTail_fullEnergy_lower (P : ℕ) (a : ℝ)
    (hP : P ≠ 0) (h2 : 2 ∣ P) :
    (2*sieveMobiusHead P a-a)^2/6 ≤ ‖sieveMobiusNormalizedTail P a‖^2 := by
  have hs := (hilbertSequence_square_summable (sieveMobiusNormalizedTail P a)).le_tsum 2
    (fun k _ => mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _))
  rw [← hilbert_norm_weighted_sq,
    sieveMobiusNormalizedTail_value_two P a hP h2] at hs
  rw [show positiveWeight 2=(1/6 : ℝ) by norm_num [positiveWeight]] at hs
  nlinarith

end RiemannResearch.RH.Pareto
