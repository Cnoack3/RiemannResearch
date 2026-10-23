import RiemannResearch.RH.RamanujanCanonicalOptimizer
import RiemannResearch.RH.ResidueGramMobiusCorrection
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.IntegratedRamanujanHilbert
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
/-!
# Exact finite multiple coordinates and their stabilized defects

Source: user-requested duality program, 23 October 2026.
The signed multiple transforms of the actual packet optimizer are precisely
the original continuous legal coefficients. Their limits exist unconditionally;
identifying every limit with negative Mobius is equivalent to zero residual.
No convergence of individual packet coefficients or infinite sum interchange
is asserted. The complete limiting residual is retained in every estimate.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.RamanujanCanonicalOptimizer
open Pareto Pareto.CoefficientStabilization
open RiemannResearch.Analysis.FiniteHilbertGram

def packetMultipleTransform (n : ℕ) (a : Fin n → ℝ) (m : ℕ) : ℝ :=
  (m : ℝ) * ∑ i : Fin n,
    if m ∣ i.val + 2 then
      (ArithmeticFunction.moebius ((i.val + 2) / m) : ℝ) * a i else 0

def packetMultipleCoefficient (n m : ℕ) : ℝ :=
  packetMultipleTransform n (packetCoefficients n) m

theorem coefficient_packet_synthesis
    (n : ℕ) (a : Fin n → ℝ) (m : ℕ) (hm : 1 < m) :
    coefficientCLM m (Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a) =
      packetMultipleTransform n a m := by
  classical
  simp only [Fintype.linearCombination_apply, map_sum, map_smul, smul_eq_mul]
  unfold packetMultipleTransform
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change a i * (-mobiusDifferenceCLM m
    (ramanujanPacketHilbert (i.val + 2))) = _
  rw [mobiusDifferenceCLM_ramanujanPacketHilbert m (i.val + 2) hm (by omega)]
  split_ifs <;> ring

theorem packetMultipleCoefficient_eq (n m : ℕ) (hm : 1 < m) :
    packetMultipleCoefficient n m = coefficient n m := by
  rw [coefficient, ← packetCandidate_eq_projection]
  exact (coefficient_packet_synthesis n (packetCoefficients n) m hm).symm

theorem packet_energy_eq_original (n : ℕ) :
    energy n = 1 - packetMass n := by
  change ‖hilbertOne - CoefficientStabilization.projection n‖ ^ 2 = _
  rw [← packetCandidate_eq_projection, packet_error]

theorem packetMultipleCoefficient_tendsto (m : ℕ) (hm : 1 < m) :
    Tendsto (fun n => packetMultipleCoefficient n m) atTop
      (𝓝 (limitCoefficient m)) := by
  simpa only [packetMultipleCoefficient_eq _ m hm] using coefficient_tendsto m

theorem packetMultipleCoefficient_defect (n m : ℕ) (hm : 1 < m) :
    packetMultipleCoefficient n m + (ArithmeticFunction.moebius m : ℝ) =
      mobiusDifferenceCLM m (hilbertOne - packetCandidate n) := by
  rw [packetMultipleCoefficient_eq n m hm, packetCandidate_eq_projection]
  exact GramMobiusCorrection.correction_eq_residual_coordinate n m (by omega)

theorem packetMultipleCoefficient_correction_tendsto (m : ℕ) (hm : 1 < m) :
    Tendsto (fun n => packetMultipleCoefficient n m +
      (ArithmeticFunction.moebius m : ℝ)) atTop
      (𝓝 (mobiusDifferenceCLM m limitResidual)) := by
  simpa only [packetMultipleCoefficient_eq _ m hm, GramMobiusCorrection.correction]
    using GramMobiusCorrection.correction_tendsto_residual m (by omega)

theorem packetMultipleCoefficient_error_bound (n m : ℕ) (hm : 1 < m) :
    ‖limitCoefficient m - packetMultipleCoefficient n m‖ ^ 2 ≤
      ‖mobiusDifferenceCLM m‖ ^ 2 * (1 - packetMass n - limitEnergy) := by
  rw [packetMultipleCoefficient_eq n m hm, ← packet_energy_eq_original]
  exact coefficient_error_bound n m

theorem packetMultipleCoefficient_targets_iff_residual_zero :
    (∀ m : ℕ, 1 < m → Tendsto (fun n => packetMultipleCoefficient n m) atTop
      (𝓝 (-(ArithmeticFunction.moebius m : ℝ)))) ↔ limitResidual = 0 := by
  simpa (config := { contextual := true }) only [packetMultipleCoefficient_eq] using
    (coefficients_tendsto_mobius_iff.trans
      limitCoefficients_eq_mobius_iff_residual_zero)

theorem packetMultipleCoefficient_targets_iff_norm :
    (∀ m : ℕ, 1 < m → Tendsto (fun n => packetMultipleCoefficient n m) atTop
      (𝓝 (-(ArithmeticFunction.moebius m : ℝ)))) ↔
      Tendsto (fun n => ‖hilbertOne - packetCandidate n‖) atTop (𝓝 0) := by
  simpa (config := { contextual := true }) only
    [packetMultipleCoefficient_eq, packetCandidate_eq_projection] using
    (coefficients_tendsto_mobius_iff.trans
      (limitCoefficients_eq_mobius_iff_mem.trans
        projection_norm_tendsto_zero_iff_mem.symm))

end RiemannResearch.RH.RamanujanCanonicalOptimizer
