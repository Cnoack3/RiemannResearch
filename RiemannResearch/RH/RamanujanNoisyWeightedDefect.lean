import RiemannResearch.Analysis.NoisyWeightedCoordinates
import RiemannResearch.RH.RamanujanAdmissibleWeights

/-!
# Complete noisy conductor measurements and robust Ramanujan criteria

Source: sixth transfer program, 24 October 2026. A measurement error is an
arbitrary full weighted square-summable array; it need not come from a vector
in either arithmetic Hilbert space. The complete signed cross series and
noise energy are retained before the two-sided error estimates. Vanishing
noise preserves the exact saturation and conditional RH criteria.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.RamanujanNoisyWeightedDefect
open Pareto ZetaTwoHilbert RamanujanWeightedDefect RamanujanAdmissibleWeights
open RiemannResearch.Analysis.WeightedCoordinateEnergy
open RiemannResearch.Analysis.NoisyWeightedCoordinates

def paretoCoordinateError (n j : ℕ) : ℝ :=
  RamanujanCanonicalOptimizer.packetMultipleCoefficient n (j + 2) +
    (ArithmeticFunction.moebius (j + 2) : ℝ)

def qCoordinateError (n j : ℕ) : ℝ :=
  QRamanujanCanonicalOptimizer.packetCoordinate n (j + 2) +
    (ArithmeticFunction.moebius (j + 2) : ℝ)

def paretoNoisyDefect (w : ℕ → ℝ) (n : ℕ) (e : ℕ → ℝ) : ℝ :=
  arrayEnergy w (fun j => paretoCoordinateError n j + e j)

def qNoisyDefect (w : ℕ → ℝ) (n : ℕ) (e : ℕ → ℝ) : ℝ :=
  arrayEnergy w (fun j => qCoordinateError n j + e j)

theorem pareto_error_summable (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖paretoCoordinates j‖ ^ 2)) (n : ℕ) :
    Summable (fun j => w j * (paretoCoordinateError n j) ^ 2) := by
  simpa only [pareto_coordinate_residual, neg_sq, paretoCoordinateError] using
    observation_summable w paretoCoordinates hw hs
      (hilbertOne - CoefficientStabilization.projection n)

theorem q_error_summable (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖qCoordinates j‖ ^ 2)) (n : ℕ) :
    Summable (fun j => w j * (qCoordinateError n j) ^ 2) := by
  simpa only [q_coordinate_residual, neg_sq, qCoordinateError] using
    observation_summable w qCoordinates hw hs
      (qOne - QRamanujanCanonicalOptimizer.packetCandidate n)

theorem pareto_arrayEnergy (w : ℕ → ℝ) (n : ℕ) :
    arrayEnergy w (paretoCoordinateError n) = paretoDefectWith w n :=
  (paretoDefectWith_series w n).symm

theorem q_arrayEnergy (w : ℕ → ℝ) (n : ℕ) :
    arrayEnergy w (qCoordinateError n) = qDefectWith w n :=
  (qDefectWith_series w n).symm

/-- Exact signed completion for noisy measurements of the Pareto conductor array. -/
theorem pareto_noisy_exact (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖paretoCoordinates j‖ ^ 2))
    (n : ℕ) (e : ℕ → ℝ) (he : Summable (fun j => w j * (e j) ^ 2)) :
    paretoNoisyDefect w n e = paretoDefectWith w n +
      2 * (∑' j, w j * paretoCoordinateError n j * e j) + arrayEnergy w e := by
  rw [paretoNoisyDefect, array_add_exact w _ e hw (pareto_error_summable w hw hs n) he,
    pareto_arrayEnergy] <;> rfl

/-- Exact signed completion for noisy measurements of the Q conductor array. -/
theorem q_noisy_exact (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖qCoordinates j‖ ^ 2))
    (n : ℕ) (e : ℕ → ℝ) (he : Summable (fun j => w j * (e j) ^ 2)) :
    qNoisyDefect w n e = qDefectWith w n +
      2 * (∑' j, w j * qCoordinateError n j * e j) + arrayEnergy w e := by
  rw [qNoisyDefect, array_add_exact w _ e hw (q_error_summable w hw hs n) he,
    q_arrayEnergy] <;> rfl

/-- The cross term satisfies the sharp weighted Cauchy bound. -/
theorem pareto_noisy_cross_sq_le (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖paretoCoordinates j‖ ^ 2))
    (n : ℕ) (e : ℕ → ℝ) (he : Summable (fun j => w j * (e j) ^ 2)) :
    (∑' j, w j * paretoCoordinateError n j * e j) ^ 2 ≤
      paretoDefectWith w n * arrayEnergy w e := by
  simpa only [arrayPairing, pareto_arrayEnergy] using
    array_pairing_sq_le w (paretoCoordinateError n) e hw (pareto_error_summable w hw hs n) he

theorem q_noisy_cross_sq_le (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖qCoordinates j‖ ^ 2))
    (n : ℕ) (e : ℕ → ℝ) (he : Summable (fun j => w j * (e j) ^ 2)) :
    (∑' j, w j * qCoordinateError n j * e j) ^ 2 ≤
      qDefectWith w n * arrayEnergy w e := by
  simpa only [arrayPairing, q_arrayEnergy] using
    array_pairing_sq_le w (qCoordinateError n) e hw (q_error_summable w hw hs n) he

theorem pareto_noisy_two_sided (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖paretoCoordinates j‖ ^ 2))
    (n : ℕ) (e : ℕ → ℝ) (he : Summable (fun j => w j * (e j) ^ 2)) :
    paretoNoisyDefect w n e ≤ 2 * paretoDefectWith w n + 2 * arrayEnergy w e ∧
      paretoDefectWith w n ≤ 2 * paretoNoisyDefect w n e + 2 * arrayEnergy w e := by
  simpa only [paretoNoisyDefect, pareto_arrayEnergy] using
    And.intro (array_add_le w _ e hw (pareto_error_summable w hw hs n) he)
      (array_true_le_noisy w _ e hw (pareto_error_summable w hw hs n) he)

theorem q_noisy_two_sided (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖qCoordinates j‖ ^ 2))
    (n : ℕ) (e : ℕ → ℝ) (he : Summable (fun j => w j * (e j) ^ 2)) :
    qNoisyDefect w n e ≤ 2 * qDefectWith w n + 2 * arrayEnergy w e ∧
      qDefectWith w n ≤ 2 * qNoisyDefect w n e + 2 * arrayEnergy w e := by
  simpa only [qNoisyDefect, q_arrayEnergy] using
    And.intro (array_add_le w _ e hw (q_error_summable w hw hs n) he)
      (array_true_le_noisy w _ e hw (q_error_summable w hw hs n) he)

variable {α : Type*} {l : Filter α}

/-- Even varying nonnegative weights and arbitrary packet-stage selections
preserve zero-convergence under vanishing complete noise energy. -/
theorem pareto_noisy_zero_iff (W E : α → ℕ → ℝ) (N : α → ℕ)
    (hw : ∀ i j, 0 ≤ W i j)
    (hs : ∀ i, Summable (fun j => W i j * ‖paretoCoordinates j‖ ^ 2))
    (he : ∀ i, Summable (fun j => W i j * (E i j) ^ 2))
    (hnoise : Tendsto (fun i => arrayEnergy (W i) (E i)) l (𝓝 0)) :
    Tendsto (fun i => paretoNoisyDefect (W i) (N i) (E i)) l (𝓝 0) ↔
      Tendsto (fun i => paretoDefectWith (W i) (N i)) l (𝓝 0) := by
  simpa only [paretoNoisyDefect, pareto_arrayEnergy] using
    noisy_zero_iff W (fun i => paretoCoordinateError (N i)) E hw
      (fun i => pareto_error_summable (W i) (hw i) (hs i) (N i)) he hnoise

theorem q_noisy_zero_iff (W E : α → ℕ → ℝ) (N : α → ℕ)
    (hw : ∀ i j, 0 ≤ W i j)
    (hs : ∀ i, Summable (fun j => W i j * ‖qCoordinates j‖ ^ 2))
    (he : ∀ i, Summable (fun j => W i j * (E i j) ^ 2))
    (hnoise : Tendsto (fun i => arrayEnergy (W i) (E i)) l (𝓝 0)) :
    Tendsto (fun i => qNoisyDefect (W i) (N i) (E i)) l (𝓝 0) ↔
      Tendsto (fun i => qDefectWith (W i) (N i)) l (𝓝 0) := by
  simpa only [qNoisyDefect, q_arrayEnergy] using
    noisy_zero_iff W (fun i => qCoordinateError (N i)) E hw
      (fun i => q_error_summable (W i) (hw i) (hs i) (N i)) he hnoise

theorem pareto_noisy_saturation_iff [NeBot l]
    (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hs : Summable (fun j => w j * ‖paretoCoordinates j‖ ^ 2))
    (N : α → ℕ) (hN : Tendsto N l atTop) (E : α → ℕ → ℝ)
    (he : ∀ i, Summable (fun j => w j * (E i j) ^ 2))
    (hnoise : Tendsto (fun i => arrayEnergy w (E i)) l (𝓝 0)) :
    Tendsto (fun i => paretoNoisyDefect w (N i) (E i)) l (𝓝 0) ↔
      CoefficientStabilization.limitEnergy = 0 :=
  (pareto_noisy_zero_iff (fun _ => w) E N (fun _ j => (hw j).le) (fun _ => hs) he hnoise).trans
    (paretoDefectWith_cofinal_zero_iff w hw hs N hN)

theorem q_noisy_saturation_iff [NeBot l]
    (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hs : Summable (fun j => w j * ‖qCoordinates j‖ ^ 2))
    (N : α → ℕ) (hN : Tendsto N l atTop) (E : α → ℕ → ℝ)
    (he : ∀ i, Summable (fun j => w j * (E i j) ^ 2))
    (hnoise : Tendsto (fun i => arrayEnergy w (E i)) l (𝓝 0)) :
    Tendsto (fun i => qNoisyDefect w (N i) (E i)) l (𝓝 0) ↔
      QRamanujanCanonicalOptimizer.packetLimitEnergy = 0 :=
  (q_noisy_zero_iff (fun _ => w) E N (fun _ j => (hw j).le) (fun _ => hs) he hnoise).trans
    (qDefectWith_cofinal_zero_iff w hw hs N hN)

theorem pareto_noisy_rh_iff [NeBot l]
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hs : Summable (fun j => w j * ‖paretoCoordinates j‖ ^ 2))
    (N : α → ℕ) (hN : Tendsto N l atTop) (E : α → ℕ → ℝ)
    (he : ∀ i, Summable (fun j => w j * (E i j) ^ 2))
    (hnoise : Tendsto (fun i => arrayEnergy w (E i)) l (𝓝 0)) :
    Tendsto (fun i => paretoNoisyDefect w (N i) (E i)) l (𝓝 0) ↔ RiemannHypothesis :=
  (pareto_noisy_saturation_iff w hw hs N hN E he hnoise).trans
    ((RamanujanCanonicalOptimizer.packet_cofinal_mass_iff N hN).symm.trans
      (RamanujanCanonicalOptimizer.packet_cofinal_rh_equivalences hBaezDuarte N hN).1)

theorem q_noisy_rh_iff [NeBot l]
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hs : Summable (fun j => w j * ‖qCoordinates j‖ ^ 2))
    (N : α → ℕ) (hN : Tendsto N l atTop) (E : α → ℕ → ℝ)
    (he : ∀ i, Summable (fun j => w j * (E i j) ^ 2))
    (hnoise : Tendsto (fun i => arrayEnergy w (E i)) l (𝓝 0)) :
    Tendsto (fun i => qNoisyDefect w (N i) (E i)) l (𝓝 0) ↔ RiemannHypothesis :=
  (q_noisy_saturation_iff w hw hs N hN E he hnoise).trans
    ((QRamanujanCanonicalOptimizer.packet_cofinal_mass_iff N hN).symm.trans
      (QRamanujanCanonicalOptimizer.packet_cofinal_rh_equivalences hBaezDuarte N hN).1)

end RiemannResearch.RH.RamanujanNoisyWeightedDefect
