import RiemannResearch.RH.PrimePowerCriticalEnergy
import RiemannResearch.RH.ChebyshevMellin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

This module does not assert any open analytic estimate. Its target declarations
are explicitly open propositions and supply no hidden analytic assumptions
inside an unconditional RH theorem. The exact raw cell assembly is
proved for explicit complete enumeration data. RawPrimePowerEnumeration
constructs the canonical infinite enumeration; the arithmetic bounds remain
open. The geometric theorem reuses the
repository's explicit conditional result.

The raw finite-cell theorem in PrimePowerCriticalEnergy covers [q 0,q N].
The assembly target below explicitly adds the initial [1,2] contribution 1.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RiemannResearch.RH.RawPrimePowerContinuation

open RiemannResearch.LinearAlgebra.CumulativeCellEnergy

def actualRawError (x : ℝ) : ℝ := Chebyshev.psi x - x

def actualRawCriticalPrefix (X : ℝ) : ℝ :=
  ∫ x in (1 : ℝ)..X, actualRawError x ^ 2 / x ^ 2

def ActualRawCriticalLogBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 2 ≤ X →
    actualRawCriticalPrefix X ≤ C * Real.log X

def ActualRawDampedIntegrable (ε : ℝ) : Prop :=
  IntegrableOn (fun x : ℝ => actualRawError x ^ 2 * Real.rpow x (-2 - ε)) (Ioi 1)

def ActualRawAllPositiveDampedEnergies : Prop :=
  ∀ ε : ℝ, 0 < ε → ActualRawDampedIntegrable ε

/-- An actual pointwise arithmetic estimate. This definition does not assert it. -/
def ActualRawPowerBound (a : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x →
    |actualRawError x| ≤ C * Real.rpow x a

/-- Complete enumeration data. RawPrimePowerEnumeration constructs the
canonical infinite instance; no incomplete finite list is called the sequence. -/
structure ActualPrimePowerEnumeration where
  q : ℕ → ℕ
  strictMono : StrictMono q
  first : q 0 = 2
  positive : ∀ i, 0 < q i
  primePower : ∀ i, IsPrimePow (q i)
  complete : ∀ N, PrimePowerCriticalEnergy.CompleteThrough q N

/-- Exact raw-psi cell assembly target. The initial singleton-free interval has
energy 1; point jumps at cell endpoints must be handled almost everywhere. -/
def ActualRawCellAssembly (e : ActualPrimePowerEnumeration) : Prop :=
  ∀ N : ℕ,
    actualRawCriticalPrefix (e.q N : ℝ) =
      1 +
        LinearAlgebra.CumulativeCellEnergy.weightedPrefixEnergy
          (PrimePowerCriticalEnergy.cellWeight e.q)
          (PrimePowerCriticalEnergy.signedJump e.q) N +
        ∑ i ∈ Finset.range N,
          Analysis.ReciprocalCellEnergy.intervalRemainder (e.q i) (e.q (i + 1))

/-- The actual, still-unproved arithmetic discrepancy estimate on the full grid.
It is logarithmic growth, not uniform undamped boundedness. -/
def ActualArithmeticGridLogBound (e : ActualPrimePowerEnumeration) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
    LinearAlgebra.CumulativeCellEnergy.weightedPrefixEnergy
      (PrimePowerCriticalEnergy.cellWeight e.q)
      (PrimePowerCriticalEnergy.signedJump e.q) N ≤ C * Real.log (e.q N : ℝ)

/-- Actual cubic-gap provider; proving this requires formalizing prime-gap inputs
or another unconditional arithmetic proof. -/
def ActualCubicGapSummability (e : ActualPrimePowerEnumeration) : Prop :=
  Summable (fun i =>
    PrimePowerCriticalEnergy.cellLength e.q i ^ 3 / (e.q i : ℝ) ^ 2)

def ActualGeometricSummability (e : ActualPrimePowerEnumeration) : Prop :=
  Summable (fun i =>
    Analysis.ReciprocalCellEnergy.intervalRemainder (e.q i) (e.q (i + 1)))

/-- Reuses the existing exact conditional geometric reduction. This does not
prove its actual prime-gap hypothesis. -/
theorem actualGeometry_of_actualCubicGap (e : ActualPrimePowerEnumeration)
    (h : ActualCubicGapSummability e) : ActualGeometricSummability e := by
  exact PrimePowerCriticalEnergy.actual_remainder_summable_of_external_cubic_gap
    e.q e.strictMono e.positive h

/-! ## Exact assembly from complete enumeration data

The cell identity is used only on open intervals. Thus no false pointwise
identity is asserted at the right endpoint, where psi has its next jump.
The interval congruence lemmas discard the null endpoints explicitly.
-/

lemma actualPsi_eq_range (x : ℝ) :
    Chebyshev.psi x =
      ∑ k ∈ Finset.range (⌊x⌋₊ + 1), ArithmeticFunction.vonMangoldt k := by
  have hs : Finset.Icc 0 ⌊x⌋₊ = Finset.range (⌊x⌋₊ + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_range, Nat.zero_le, true_and,
      Nat.lt_succ_iff]
  rw [Chebyshev.psi_eq_sum_Icc, hs]

/-- Completeness rules out omitted von Mangoldt jumps inside a cell.
The left endpoint is included, but the next jump at the right endpoint is not. -/
theorem actualPsi_eq_cell_level (e : ActualPrimePowerEnumeration) (i : ℕ)
    {x : ℝ} (hxleft : (e.q i : ℝ) ≤ x) (hxright : x < (e.q (i + 1) : ℝ)) :
    Chebyshev.psi x = cumulative (PrimePowerCriticalEnergy.actualJump e.q) (i + 1) := by
  classical
  have hxnonneg : 0 ≤ x := le_trans (Nat.cast_nonneg (e.q i)) hxleft
  have hlo : e.q i ≤ ⌊x⌋₊ := (Nat.le_floor_iff hxnonneg).mpr hxleft
  have hhi : ⌊x⌋₊ < e.q (i + 1) := (Nat.floor_lt hxnonneg).mpr hxright
  rw [PrimePowerCriticalEnergy.actualCumulative_eq_chebyshev
    e.q e.strictMono i (e.complete i), actualPsi_eq_range]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hlo 1))
  intro k hk hnot
  by_contra hne
  have hkfloor : k ≤ ⌊x⌋₊ := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hknext : k < e.q (i + 1) := lt_of_le_of_lt hkfloor hhi
  have hkcutoff : k ∈ Finset.range (e.q (i + 1) + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hknext.le)
  obtain ⟨j, hj, he⟩ := e.complete (i + 1) k hkcutoff hne
  have hjlt : j < i + 1 := by
    by_contra h
    have hq := e.strictMono.monotone (Nat.le_of_not_gt h)
    rw [he] at hq
    exact (not_le_of_gt hknext) hq
  have hkold : k ≤ e.q i := by
    rw [← he]
    exact e.strictMono.monotone (Nat.le_of_lt_succ hjlt)
  exact hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le hkold))

lemma actualRawEnergy_eq_cell_on (e : ActualPrimePowerEnumeration) (i : ℕ) :
    EqOn (fun x : ℝ => actualRawError x ^ 2 / x ^ 2)
      (fun x : ℝ =>
        (cumulative (PrimePowerCriticalEnergy.actualJump e.q) (i + 1) - x) ^ 2 / x ^ 2)
      (uIoo (e.q i : ℝ) (e.q (i + 1) : ℝ)) := by
  have hq : (e.q i : ℝ) < (e.q (i + 1) : ℝ) := by
    exact_mod_cast e.strictMono (Nat.lt_succ_self i)
  rw [uIoo_of_lt hq]
  intro x hx
  change (Chebyshev.psi x - x) ^ 2 / x ^ 2 = _
  rw [actualPsi_eq_cell_level e i hx.1.le hx.2]

theorem actualRawCellIntegral (e : ActualPrimePowerEnumeration) (i : ℕ) :
    (∫ x in (e.q i : ℝ)..(e.q (i + 1) : ℝ), actualRawError x ^ 2 / x ^ 2) =
      ∫ x in (e.q i : ℝ)..(e.q (i + 1) : ℝ),
        (cumulative (PrimePowerCriticalEnergy.actualJump e.q) (i + 1) - x) ^ 2 / x ^ 2 :=
  intervalIntegral.integral_congr_uIoo (actualRawEnergy_eq_cell_on e i)

theorem actualRawIntervalIntegrable_cell (e : ActualPrimePowerEnumeration) (i : ℕ) :
    IntervalIntegrable (fun x : ℝ => actualRawError x ^ 2 / x ^ 2)
      volume (e.q i : ℝ) (e.q (i + 1) : ℝ) := by
  have hm := Analysis.ReciprocalCellEnergy.intervalIntegrable_weighted_residual_square
    (by exact_mod_cast e.positive i : (0 : ℝ) < (e.q i : ℝ))
    (by exact_mod_cast e.strictMono (Nat.lt_succ_self i) :
      (e.q i : ℝ) < (e.q (i + 1) : ℝ))
    (cumulative (PrimePowerCriticalEnergy.actualJump e.q) (i + 1))
  apply hm.congr_uIoo
  intro x hx
  exact (actualRawEnergy_eq_cell_on e i hx).symm

lemma actualRawEnergy_eq_one_on_initial :
    EqOn (fun x : ℝ => actualRawError x ^ 2 / x ^ 2)
      (fun _ : ℝ => (1 : ℝ)) (uIoo (1 : ℝ) 2) := by
  rw [uIoo_of_lt (by norm_num : (1 : ℝ) < 2)]
  intro x hx
  have hxne : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx.1)
  change (Chebyshev.psi x - x) ^ 2 / x ^ 2 = 1
  rw [Chebyshev.psi_eq_zero_of_lt_two hx.2]
  field_simp [hxne]
  <;> ring

theorem actualRawIntervalIntegrable_initial :
    IntervalIntegrable (fun x : ℝ => actualRawError x ^ 2 / x ^ 2)
      volume (1 : ℝ) 2 := by
  have hc : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (1 : ℝ) 2 :=
    intervalIntegrable_const
  apply hc.congr_uIoo
  intro x hx
  exact (actualRawEnergy_eq_one_on_initial hx).symm

theorem actualRawInitialIntegral :
    (∫ x in (1 : ℝ)..2, actualRawError x ^ 2 / x ^ 2) = 1 := by
  rw [intervalIntegral.integral_congr_uIoo actualRawEnergy_eq_one_on_initial]
  norm_num

theorem actualRawIntervalIntegrable_grid (e : ActualPrimePowerEnumeration) (N : ℕ) :
    IntervalIntegrable (fun x : ℝ => actualRawError x ^ 2 / x ^ 2)
      volume (e.q 0 : ℝ) (e.q N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih => exact ih.trans (actualRawIntervalIntegrable_cell e N)

/-- The exact raw prefix assembly uses complete enumeration data, without
any RH or prime-gap hypothesis. RawPrimePowerEnumeration constructs the actual
instance; the logarithmic arithmetic discrepancy bound remains open. -/
theorem actualRawCellAssembly_proved (e : ActualPrimePowerEnumeration) :
    ActualRawCellAssembly e := by
  unfold ActualRawCellAssembly
  intro N
  have hfirst : (e.q 0 : ℝ) = 2 := by rw [e.first]; norm_num
  have hinit : IntervalIntegrable (fun x : ℝ => actualRawError x ^ 2 / x ^ 2)
      volume (1 : ℝ) (e.q 0 : ℝ) := by
    simpa only [hfirst] using actualRawIntervalIntegrable_initial
  have hinitvalue :
      (∫ x in (1 : ℝ)..(e.q 0 : ℝ), actualRawError x ^ 2 / x ^ 2) = 1 := by
    simpa only [hfirst] using actualRawInitialIntegral
  have hsum :
      (∑ i ∈ Finset.range N,
        ∫ x in (e.q i : ℝ)..(e.q (i + 1) : ℝ), actualRawError x ^ 2 / x ^ 2) =
      ∫ x in (e.q 0 : ℝ)..(e.q N : ℝ), actualRawError x ^ 2 / x ^ 2 :=
    intervalIntegral.sum_integral_adjacent_intervals
      (fun i _ => actualRawIntervalIntegrable_cell e i)
  unfold actualRawCriticalPrefix
  calc
    (∫ x in (1 : ℝ)..(e.q N : ℝ), actualRawError x ^ 2 / x ^ 2) =
        (∫ x in (1 : ℝ)..(e.q 0 : ℝ), actualRawError x ^ 2 / x ^ 2) +
        (∫ x in (e.q 0 : ℝ)..(e.q N : ℝ), actualRawError x ^ 2 / x ^ 2) :=
      (intervalIntegral.integral_add_adjacent_intervals hinit
        (actualRawIntervalIntegrable_grid e N)).symm
    _ = 1 + (∑ i ∈ Finset.range N,
        ∫ x in (e.q i : ℝ)..(e.q (i + 1) : ℝ), actualRawError x ^ 2 / x ^ 2) := by
      rw [hinitvalue, ← hsum]
    _ = 1 + (∑ i ∈ Finset.range N,
        ∫ x in (e.q i : ℝ)..(e.q (i + 1) : ℝ),
          (cumulative (PrimePowerCriticalEnergy.actualJump e.q) (i + 1) - x) ^ 2 / x ^ 2) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact actualRawCellIntegral e i
    _ = 1 + weightedPrefixEnergy (PrimePowerCriticalEnergy.cellWeight e.q)
        (PrimePowerCriticalEnergy.signedJump e.q) N +
        ∑ i ∈ Finset.range N,
          Analysis.ReciprocalCellEnergy.intervalRemainder (e.q i) (e.q (i + 1)) := by
      rw [PrimePowerCriticalEnergy.actual_interval_energy_split e.q e.strictMono e.positive N]
      ring

end RiemannResearch.RH.RawPrimePowerContinuation
