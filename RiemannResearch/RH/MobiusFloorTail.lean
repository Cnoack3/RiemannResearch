import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open scoped BigOperators

/-!
Source: Christian Noack, user-provided `signal_to_noise_RH_program (2)(1).pdf`,
Section 10.1, equation (20) and the following residual display.
This module corrects that finite residual statement.
No analytic estimate or RH assumption is encoded here.
The arithmetic occurrence-count identity is supplied explicitly in
`occurrence_residual`; `mobius_floor_split` proves the underlying finite split.
-/

namespace RiemannResearch.RH.Pareto

noncomputable def mobiusFloorTerm (r d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((r / d : ℕ) : ℝ)

noncomputable def mobiusFloorTotal (P r : ℕ) : ℝ :=
  ∑ d ∈ P.divisors, mobiusFloorTerm r d

noncomputable def mobiusFloorHead (P x r : ℕ) : ℝ :=
  ∑ d ∈ P.divisors.filter (fun d => d ≤ x), mobiusFloorTerm r d

noncomputable def mobiusFloorTail (P x r : ℕ) : ℝ :=
  ∑ d ∈ P.divisors.filter (fun d => x < d), mobiusFloorTerm r d

theorem mobius_floor_split (P x r : ℕ) :
    mobiusFloorHead P x r + mobiusFloorTail P x r = mobiusFloorTotal P r := by
  classical
  unfold mobiusFloorHead mobiusFloorTail mobiusFloorTotal
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : d ≤ x
  · simp [h, Nat.not_lt.mpr h]
  · have hx : x < d := Nat.lt_of_not_ge h
    simp [h, hx]

/-- The signed residual is `head - 1`, not `-head`. -/
theorem occurrence_residual (P x r : ℕ) (C : ℝ)
    (inclusion_exclusion : C + 1 = mobiusFloorTotal P r) :
    C - mobiusFloorTail P x r = mobiusFloorHead P x r - 1 := by
  have hsplit := mobius_floor_split P x r
  linarith

/-- Reversing the residual changes its sign and still retains the constant. -/
theorem opposite_occurrence_residual (P x r : ℕ) (C : ℝ)
    (inclusion_exclusion : C + 1 = mobiusFloorTotal P r) :
    mobiusFloorTail P x r - C = 1 - mobiusFloorHead P x r := by
  have h := occurrence_residual P x r C inclusion_exclusion
  linarith

noncomputable def coprimeHeadCount (P r : ℕ) : ℝ :=
  (((Finset.Icc 2 r).filter (fun n => Nat.Coprime n P)).card : ℝ)

theorem mobius_floor_head_one (P x : ℕ) (hP : P ≠ 0) (hx : 1 ≤ x) :
    mobiusFloorHead P x 1 = 1 := by
  classical
  unfold mobiusFloorHead
  rw [Finset.sum_eq_single 1]
  · simp [mobiusFloorTerm]
  · intro d hd hd1
    have hdvd : d ∣ P := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact hP (by simpa using hdvd)
    have hlt : 1 < d := by omega
    simp [mobiusFloorTerm, Nat.div_eq_of_lt hlt]
  · intro h1
    exact False.elim (h1 (Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨one_dvd P, hP⟩, hx⟩))

theorem mobius_floor_tail_one (P x : ℕ) (hx : 1 ≤ x) :
    mobiusFloorTail P x 1 = 0 := by
  classical
  unfold mobiusFloorTail
  apply Finset.sum_eq_zero
  intro d hd
  have hlt : 1 < d := lt_of_le_of_lt hx (Finset.mem_filter.mp hd).2
  simp [mobiusFloorTerm, Nat.div_eq_of_lt hlt]

theorem coprime_head_count_one (P : ℕ) : coprimeHeadCount P 1 = 0 := by
  norm_num [coprimeHeadCount]

/-- Actual arithmetic endpoint refutes the PDF's constant-free display. -/
theorem missing_constant_endpoint_refutation (P x : ℕ)
    (hP : P ≠ 0) (hx : 1 ≤ x) :
    coprimeHeadCount P 1 - mobiusFloorTail P x 1 ≠ -mobiusFloorHead P x 1 := by
  rw [coprime_head_count_one, mobius_floor_tail_one P x hx,
    mobius_floor_head_one P x hP hx]
  norm_num

end RiemannResearch.RH.Pareto
