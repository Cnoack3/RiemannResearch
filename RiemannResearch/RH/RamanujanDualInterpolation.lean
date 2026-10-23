import RiemannResearch.RH.IntegratedRamanujanGram
import RiemannResearch.RH.IntegratedRamanujanHilbert
import RiemannResearch.RH.ThresholdHilbertMean
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# Full Hilbert interpolation by integrated Ramanujan packets

Source: user-requested duality program, 23 October 2026.
The arithmetic Gram solve supplies an actual representer for every finite
moment vector. Its inverse metric is the complete Pareto inner product.
All affine interpolation statements range over the full Hilbert space;
bounded physical sequences and density hypotheses are unnecessary.
-/

open scoped BigOperators
noncomputable section
namespace RiemannResearch.RH.Pareto.RamanujanDual
def representer (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) (y : s → ℝ) : ThresholdHilbert :=
  ∑ i : s, ramanujanGramSolve s hs y i • ramanujanPacketHilbert i
def inverseMetric (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) (y z : s → ℝ) : ℝ :=
  ∑ i : s, ramanujanGramSolve s hs y i * z i
theorem representer_normal (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (y : s → ℝ) (i : s) : inner ℝ (ramanujanPacketHilbert i) (representer s hs y) = y i := by
  calc
    _ = ∑ j : s, ramanujanGramSolve s hs y j *
          inner ℝ (ramanujanPacketHilbert i) (ramanujanPacketHilbert j) := by
      simp only [representer, inner_sum, inner_smul_right]
    _ = ramanujanGramAction s (ramanujanGramSolve s hs y) i := by
      change (∑ j : s, _) = ∑ j : s,
        paretoInner (ramanujanPacket i) (ramanujanPacket j) * ramanujanGramSolve s hs y j
      apply Finset.sum_congr rfl
      intro j _
      rw [hilbert_inner_weighted]
      simp only [hilbertSequence_ramanujanPacketHilbert]
      ring
    _ = y i := congrFun (ramanujanGramSolve_normal_equations s hs y) i
theorem representer_pairing (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (y z : s → ℝ) (f : ThresholdHilbert)
    (hf : ∀ i : s, inner ℝ (ramanujanPacketHilbert i) f = z i) :
    inner ℝ (representer s hs y) f = inverseMetric s hs y z := by
  simp only [representer, sum_inner, real_inner_smul_left, hf, inverseMetric]
theorem inverseMetric_eq_inner (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (y z : s → ℝ) :
    inverseMetric s hs y z = inner ℝ (representer s hs y) (representer s hs z) :=
  (representer_pairing s hs y z _ (representer_normal s hs z)).symm
theorem inverseMetric_symm (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (y z : s → ℝ) : inverseMetric s hs y z = inverseMetric s hs z y := by
  rw [inverseMetric_eq_inner, inverseMetric_eq_inner, real_inner_comm]
theorem inverseMetric_self (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (y : s → ℝ) : inverseMetric s hs y y = ‖representer s hs y‖ ^ 2 := by
  rw [inverseMetric_eq_inner, real_inner_self_eq_norm_sq]
theorem inverseMetric_pos (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (y : s → ℝ) (hy : y ≠ 0) : 0 < inverseMetric s hs y y := by
  rw [inverseMetric_self]
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro hzero
  apply hy
  funext i
  have h := representer_normal s hs y i
  simpa [hzero] using h.symm
theorem interpolation_completion (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (y : s → ℝ) (f : ThresholdHilbert)
    (hf : ∀ i : s, inner ℝ (ramanujanPacketHilbert i) f = y i) :
    ‖f‖ ^ 2 = inverseMetric s hs y y + ‖f - representer s hs y‖ ^ 2 := by
  rw [norm_sub_sq_real, ← inverseMetric_self, real_inner_comm,
    representer_pairing s hs y y f hf]
  ring
theorem interpolation_minimum (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (y : s → ℝ) (f : ThresholdHilbert)
    (hf : ∀ i : s, inner ℝ (ramanujanPacketHilbert i) f = y i) :
    inverseMetric s hs y y ≤ ‖f‖ ^ 2 := by
  rw [interpolation_completion s hs y f hf]
  exact le_add_of_nonneg_right (sq_nonneg _)
theorem interpolation_equality_iff (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (y : s → ℝ) (f : ThresholdHilbert)
    (hf : ∀ i : s, inner ℝ (ramanujanPacketHilbert i) f = y i) :
    ‖f‖ ^ 2 = inverseMetric s hs y y ↔ f = representer s hs y := by
  constructor
  · intro h
    have hc := interpolation_completion s hs y f hf
    have hz : ‖f - representer s hs y‖ ^ 2 = 0 := by linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
  · rintro rfl
    exact (inverseMetric_self s hs y).symm
end RiemannResearch.RH.Pareto.RamanujanDual
