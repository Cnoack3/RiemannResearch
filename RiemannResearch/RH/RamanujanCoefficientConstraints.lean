import RiemannResearch.RH.RamanujanCoefficientLimits
import RiemannResearch.Analysis.FiniteGramScalarConstraint
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Legal Ramanujan approximation with a prescribed Moebius coordinate

Source: user-requested continuation of the duality structure, 23 October 2026.
The original legal coefficient is a finite signed multiple transform of packet
coefficients. Its arithmetic constraint vector is nonzero as soon as its
conductor occurs in the finite dictionary. This constructs the actual unique
optimizer with any prescribed value, including the negative Moebius target,
and retains the entire normalization penalty and Gram remainder.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.RamanujanCoefficientConstraints
open Pareto RamanujanCanonicalOptimizer
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteGramCapacity

/-- The exact arithmetic source representing the original coefficient at m. -/
def coordinateSource (n m : ℕ) (i : Fin n) : ℝ :=
  if m ∣ i.val + 2 then
    (m : ℝ) * (ArithmeticFunction.moebius ((i.val + 2) / m) : ℝ) else 0

theorem coordinateSource_pairing (n m : ℕ) (a : Fin n → ℝ) :
    packetMultipleTransform n a m = ∑ i, a i * coordinateSource n m i := by
  unfold packetMultipleTransform coordinateSource
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

/-- The diagonal arithmetic entry is m, so no capacity hypothesis is needed. -/
theorem coordinateSource_ne_zero (n m : ℕ) (hm : 1 < m) (hmn : m ≤ n + 1) :
    coordinateSource n m ≠ 0 := by
  let i : Fin n := ⟨m - 2, by omega⟩
  have hi : i.val + 2 = m := by dsimp [i]; omega
  have hv : coordinateSource n m i = (m : ℝ) := by
    simp [coordinateSource, hi, Nat.div_self (show 0 < m by omega)]
  intro hz
  have h := congrFun hz i
  rw [hv] at h
  have hpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  change (m : ℝ) = 0 at h
  linarith

theorem coordinateSource_eq_zero_of_large (n m : ℕ) (hmn : n + 1 < m) :
    coordinateSource n m = 0 := by
  funext i
  have hnd : ¬ m ∣ i.val + 2 := by
    intro hd
    have hle := Nat.le_of_dvd (show 0 < i.val + 2 by omega) hd
    have hi := i.isLt
    omega
  simp [coordinateSource, hnd]

def coordinateCapacity (n m : ℕ) : ℝ :=
  capacity (finitePacket_independent n) (coordinateSource n m)

theorem coordinateCapacity_pos (n m : ℕ) (hm : 1 < m) (hmn : m ≤ n + 1) :
    0 < coordinateCapacity n m :=
  capacity_pos (finitePacket_independent n) _ (coordinateSource_ne_zero n m hm hmn)

theorem coordinateCapacity_inverseGram (n m : ℕ) :
    coordinateCapacity n m = dotProduct (coordinateSource n m)
      ((finitePacketGram n)⁻¹.mulVec (coordinateSource n m)) := by
  rw [finitePacketGram, gramMatrix_inverseSource (finitePacket_independent n)]
  unfold coordinateCapacity capacity dotProduct
  apply Finset.sum_congr rfl
  intro i _
  ring

def coefficients (n m : ℕ) (t : ℝ) : Fin n → ℝ :=
  scalarCoefficients (finitePacket_independent n) (coordinateSource n m) hilbertOne t

def candidate (n m : ℕ) (t : ℝ) : ThresholdHilbert :=
  Fintype.linearCombination ℝ
    (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) (coefficients n m t)

theorem mismatch_eq (n m : ℕ) (t : ℝ) :
    scalarMismatch (finitePacket_independent n) (coordinateSource n m) hilbertOne t =
      t - packetMultipleCoefficient n m := by
  unfold scalarMismatch packetMultipleCoefficient
  rw [coordinateSource_pairing]
  rfl

/-- The exact inverse-Gram correction needed to prescribe the original coordinate. -/
theorem coefficients_exact (n m : ℕ) (t : ℝ) :
    coefficients n m t = packetCoefficients n +
      ((t - packetMultipleCoefficient n m) / coordinateCapacity n m) •
        inverseSource (finitePacket_independent n) (coordinateSource n m) := by
  unfold coefficients scalarCoefficients
  rw [mismatch_eq]
  rfl

theorem prescribed_coordinate (n m : ℕ) (hm : 1 < m) (hmn : m ≤ n + 1) (t : ℝ) :
    packetMultipleTransform n (coefficients n m t) m = t := by
  rw [coordinateSource_pairing]
  exact scalarCoefficients_source (finitePacket_independent n) (coordinateSource n m)
    (coordinateSource_ne_zero n m hm hmn) hilbertOne t

/-- Complete feasibility classification, including coordinates outside the stage. -/
theorem prescribed_coordinate_feasible_iff (n m : ℕ) (hm : 1 < m) (t : ℝ) :
    (∃ a : Fin n → ℝ, packetMultipleTransform n a m = t) ↔ m ≤ n + 1 ∨ t = 0 := by
  constructor
  · rintro ⟨a, ha⟩
    by_cases hmn : m ≤ n + 1
    · exact Or.inl hmn
    · right
      rw [coordinateSource_pairing, coordinateSource_eq_zero_of_large n m
        (Nat.lt_of_not_ge hmn)] at ha
      simpa using ha.symm
  · rintro (hmn | rfl)
    · exact ⟨coefficients n m t, prescribed_coordinate n m hm hmn t⟩
    · exact ⟨0, by simp [packetMultipleTransform]⟩

theorem candidate_coordinate (n m : ℕ) (hm : 1 < m) (hmn : m ≤ n + 1) (t : ℝ) :
    CoefficientStabilization.coefficientCLM m (candidate n m t) = t := by
  rw [candidate, coefficient_packet_synthesis n _ m hm]
  exact prescribed_coordinate n m hm hmn t

/-- Exact constrained minimum: the target discrepancy pays its inverse capacity. -/
theorem candidate_error_exact (n m : ℕ) (hm : 1 < m) (hmn : m ≤ n + 1) (t : ℝ) :
    ‖hilbertOne - candidate n m t‖ ^ 2 =
      1 - packetMass n + (t - packetMultipleCoefficient n m) ^ 2 /
        coordinateCapacity n m := by
  have h := scalarCoefficients_energy (finitePacket_independent n) (coordinateSource n m)
    (coordinateSource_ne_zero n m hm hmn) hilbertOne t
  simpa only [candidate, coefficients, hilbertOne_norm_sq, mismatch_eq,
    cross, packet_inner_one, packetCoefficients, packetMass, coordinateCapacity] using h

/-- The full signed Gram remainder survives for every feasible trial vector. -/
theorem constrained_completion (n m : ℕ) (hm : 1 < m) (hmn : m ≤ n + 1)
    (t : ℝ) (a : Fin n → ℝ) (ha : packetMultipleTransform n a m = t) :
    ‖hilbertOne - Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a‖ ^ 2 =
    1 - packetMass n + (t - packetMultipleCoefficient n m) ^ 2 /
      coordinateCapacity n m +
      ‖Fintype.linearCombination ℝ
        (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))
        (a - coefficients n m t)‖ ^ 2 := by
  rw [coordinateSource_pairing] at ha
  have h := scalarCoefficients_completion (finitePacket_independent n)
    (coordinateSource n m) (coordinateSource_ne_zero n m hm hmn) hilbertOne t a ha
  change _ = ‖hilbertOne - candidate n m t‖ ^ 2 + _ at h
  rw [candidate_error_exact n m hm hmn t] at h
  exact h

/-- Equality in the constrained minimum identifies all packet coefficients. -/
theorem constrained_optimal_iff (n m : ℕ) (hm : 1 < m) (hmn : m ≤ n + 1)
    (t : ℝ) (a : Fin n → ℝ) (ha : packetMultipleTransform n a m = t) :
    ‖hilbertOne - Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a‖ ^ 2 =
      1 - packetMass n + (t - packetMultipleCoefficient n m) ^ 2 /
        coordinateCapacity n m ↔ a = coefficients n m t := by
  constructor
  · intro he
    apply scalarCoefficients_unique (finitePacket_independent n) (coordinateSource n m)
      (coordinateSource_ne_zero n m hm hmn) hilbertOne t a
    · rwa [← coordinateSource_pairing]
    · change _ = ‖hilbertOne - candidate n m t‖ ^ 2
      rw [candidate_error_exact n m hm hmn t]
      exact he
  · rintro rfl
    exact candidate_error_exact n m hm hmn t

/-- The literal negative-Moebius constraint has an exact positive cost. -/
theorem moebius_target_error (n m : ℕ) (hm : 1 < m) (hmn : m ≤ n + 1) :
    ‖hilbertOne - candidate n m (-(ArithmeticFunction.moebius m : ℝ))‖ ^ 2 =
      1 - packetMass n +
        (packetMultipleCoefficient n m + (ArithmeticFunction.moebius m : ℝ)) ^ 2 /
          coordinateCapacity n m := by
  rw [candidate_error_exact n m hm hmn]
  ring

end RiemannResearch.RH.RamanujanCoefficientConstraints
