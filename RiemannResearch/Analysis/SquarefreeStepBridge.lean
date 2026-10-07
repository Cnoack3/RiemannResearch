import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.Ring

/-!
# Exact corrected fractional-part step bridge

Source: user-provided CRT and Four Improvements continuation, 6–7 October 2026.
The extensions retain complete signed identities and correction squares.


arithmetic identities underlying the squarefree Pareto consequence of the
conditional Báez-Duarte approximation theorem. It does not assume or prove that
analytic approximation theorem, nor does it state RH unconditionally.
-/

noncomputable section

open scoped BigOperators

namespace RiemannResearch.Analysis.SquarefreeStepBridge

def correctedAtom (d : ℕ) (t : ℝ) : ℝ :=
  Int.fract (t / (d : ℝ)) - Int.fract t / (d : ℝ)

def discreteAtom (d j : ℕ) : ℝ := ((j % d : ℕ) : ℝ) / (d : ℝ)

/-- The corrected atom is exactly constant on every physical integer cell.
This identity even holds for `d=0`, with Lean's totalized division convention.
-/
theorem correctedAtom_cell (d j : ℕ) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    correctedAtom d ((j : ℝ) + u) = discreteAtom d j := by
  have huFloor : Int.floor u = 0 := Int.floor_eq_zero_iff.mpr ⟨hu0, hu1⟩
  have htFloor : Int.floor ((j : ℝ) + u) = Int.floor (j : ℝ) := by
    rw [Int.floor_natCast_add, huFloor, Int.floor_natCast]
    simp
  have htFract : Int.fract ((j : ℝ) + u) = u := by
    rw [Int.fract_natCast_add]
    exact Int.fract_eq_self.mpr ⟨hu0, hu1⟩
  unfold correctedAtom discreteAtom
  rw [htFract]
  calc
    Int.fract (((j : ℝ) + u) / (d : ℝ)) - u / (d : ℝ) =
        Int.fract ((j : ℝ) / (d : ℝ)) := by
      unfold Int.fract
      rw [Int.floor_div_natCast, Int.floor_div_natCast, htFloor]
      ring
    _ = _ := Int.fract_div_natCast_eq_div_natCast_mod

/-- The entire first cell vanishes, so the discrete embedding has no origin cost. -/
theorem correctedAtom_below_one (d : ℕ) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    correctedAtom d u = 0 := by
  simpa [discreteAtom] using correctedAtom_cell d 0 u hu0 hu1

/-- The `d=1` corrected atom vanishes identically. -/
theorem correctedAtom_one (t : ℝ) : correctedAtom 1 t = 0 := by
  simp [correctedAtom]

/-- Any finite signed fractional-part sum has the exact correction algebra.
For the damped Möbius coefficients, only squarefree corrected atoms survive.
-/
theorem finite_correction_identity (s : Finset ℕ) (c : ℕ → ℝ) (t : ℝ) :
    (∑ d ∈ s, c d * Int.fract (t / (d : ℝ))) -
      (∑ d ∈ s, c d / (d : ℝ)) * Int.fract t =
    ∑ d ∈ s, c d * correctedAtom d t := by
  simp only [correctedAtom, mul_sub, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- A finite corrected continuous trial is literally the corresponding discrete trial. -/
theorem finite_trial_cell (s : Finset ℕ) (c : ℕ → ℝ) (j : ℕ) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (∑ d ∈ s, c d * correctedAtom d ((j : ℝ) + u)) =
      ∑ d ∈ s, c d * discreteAtom d j := by
  apply Finset.sum_congr rfl
  intro d hd
  rw [correctedAtom_cell d j u hu0 hu1]

/-- The raw finite trial is exactly its correction coefficient times `u` on
the first cell. This is the algebraic input to the coefficient norm bound. -/
theorem finite_raw_first_cell (s : Finset ℕ) (c : ℕ → ℝ) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (∑ d ∈ s, c d * Int.fract (u / (d : ℝ))) =
      (∑ d ∈ s, c d / (d : ℝ)) * u := by
  have hzero : (∑ d ∈ s, c d * correctedAtom d u) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    rw [correctedAtom_below_one d u hu0 hu1, mul_zero]
  have hidentity := finite_correction_identity s c u
  rw [Int.fract_eq_self.mpr ⟨hu0, hu1⟩, hzero] at hidentity
  exact sub_eq_zero.mp hidentity

/-- Exact cell decomposition of the raw fractional-part trial. The entire
within-cell variation is the single signed correction coefficient. -/
theorem finite_raw_cell (s : Finset ℕ) (c : ℕ → ℝ) (j : ℕ) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (∑ d ∈ s, c d * Int.fract (((j : ℝ) + u) / (d : ℝ))) =
      (∑ d ∈ s, c d * discreteAtom d j) +
        (∑ d ∈ s, c d / (d : ℝ)) * u := by
  have hfract : Int.fract ((j : ℝ) + u) = u := by
    rw [Int.fract_natCast_add]
    exact Int.fract_eq_self.mpr ⟨hu0, hu1⟩
  have hidentity := finite_correction_identity s c ((j : ℝ) + u)
  rw [hfract, finite_trial_cell s c j u hu0 hu1] at hidentity
  exact sub_eq_iff_eq_add.mp hidentity

/-- When the signed correction coefficient vanishes, the raw and discrete
trials coincide exactly on every integer cell. -/
theorem finite_raw_cell_of_zero_correction (s : Finset ℕ) (c : ℕ → ℝ)
    (hc : (∑ d ∈ s, c d / (d : ℝ)) = 0) (j : ℕ) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (∑ d ∈ s, c d * Int.fract (((j : ℝ) + u) / (d : ℝ))) =
      ∑ d ∈ s, c d * discreteAtom d j := by
  rw [finite_raw_cell s c j u hu0 hu1, hc, zero_mul, add_zero]

/-- Zero coefficients may be removed without taking absolute values. Applying
this to Möbius coefficients with their known zero support retains exactly the
squarefree part of any finite corrected trial. -/
theorem finite_trial_filter_zero_support (s : Finset ℕ) (c : ℕ → ℝ)
    (P : ℕ → Prop) [DecidablePred P]
    (hc : ∀ d ∈ s, ¬ P d → c d = 0) (t : ℝ) :
    (∑ d ∈ s, c d * correctedAtom d t) =
      ∑ d ∈ s.filter P, c d * correctedAtom d t := by
  symm
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hP : P d
  · simp [hP]
  · simp [hP, hc d hd hP]

/-- The same exact signed-support reduction holds for the physical discrete
trial, so support restriction commutes with the cell transfer. -/
theorem finite_discrete_filter_zero_support (s : Finset ℕ) (c : ℕ → ℝ)
    (P : ℕ → Prop) [DecidablePred P]
    (hc : ∀ d ∈ s, ¬ P d → c d = 0) (j : ℕ) :
    (∑ d ∈ s, c d * discreteAtom d j) =
      ∑ d ∈ s.filter P, c d * discreteAtom d j := by
  symm
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hP : P d
  · simp [hP]
  · simp [hP, hc d hd hP]

/-- Arbitrarily weighted alternating Möbius corrected atoms have exact
squarefree support. This includes damped Möbius coefficients. -/
theorem finite_mobius_corrected_squarefree (s : Finset ℕ) (a : ℕ → ℝ) (t : ℝ) :
    (∑ d ∈ s, (-(ArithmeticFunction.moebius d : ℝ) * a d) * correctedAtom d t) =
      ∑ d ∈ s.filter Squarefree,
        (-(ArithmeticFunction.moebius d : ℝ) * a d) * correctedAtom d t := by
  apply finite_trial_filter_zero_support
  intro d hd hnot
  simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnot]

/-- The physical alternating Möbius trial has precisely the same exact
squarefree support, before any norm or limiting argument. -/
theorem finite_mobius_discrete_squarefree (s : Finset ℕ) (a : ℕ → ℝ) (j : ℕ) :
    (∑ d ∈ s, (-(ArithmeticFunction.moebius d : ℝ) * a d) * discreteAtom d j) =
      ∑ d ∈ s.filter Squarefree,
        (-(ArithmeticFunction.moebius d : ℝ) * a d) * discreteAtom d j := by
  apply finite_discrete_filter_zero_support
  intro d hd hnot
  simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnot]

end RiemannResearch.Analysis.SquarefreeStepBridge
