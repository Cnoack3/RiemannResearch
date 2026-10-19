import RiemannResearch.RH.MobiusPrimitiveCharge
import RiemannResearch.RH.MobiusReciprocalChargeBridge
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MobiusReciprocal
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity

/-!
# Triangular reciprocal-charge algebra

Source: user-directed review of Michel Balazard, arXiv:1812.04309,
Propositions 6--7, 19 October 2026. The imported paper formalization
supplies the reciprocal Riesz kernels. This module proves their exact
triangular pairing and the unconditional decay of the arithmetic
mean-square energy proposed as their majorant.

Formal boundary: this module does not assert the actual norm bound by
that energy. Its ordinary mathematical proof and the still-unformalized
overlap identification are recorded in BalazardTriangularResearch20261019.md.
The repository Riesz sign is opposite to the paper's dual vectors.
-/

noncomputable section
open scoped Topology BigOperators
open Filter
namespace RiemannResearch.RH.Pareto
def triangularChargeRiesz (N : ℕ) : ThresholdHilbert :=
  (N : ℝ)⁻¹ • ∑ k ∈ Finset.range N, reciprocalChargeRiesz k
theorem triangularChargeRiesz_eq_sub (N : ℕ) :
    triangularChargeRiesz N = reciprocalChargeRiesz N - primitiveChargeRiesz N := by
  simp [triangularChargeRiesz, primitiveChargeRiesz]
theorem triangularChargeRiesz_inner (N : ℕ) (f : ThresholdHilbert) :
    inner ℝ (triangularChargeRiesz N) f =
      ∑ d ∈ Finset.Icc 1 N,
        (1 - (d : ℝ) / (N : ℝ)) * mobiusDifferenceCLM d f / (d : ℝ) := by
  rw [triangularChargeRiesz_eq_sub, inner_sub_left,
    reciprocalChargeRiesz_inner, primitiveChargeRiesz_inner, Finset.sum_div,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : (d : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (show 0 < d by have := (Finset.mem_Icc.mp hd).1; omega)
  have hN0 : (N : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (show 0 < N by have := Finset.mem_Icc.mp hd; omega)
  field_simp [hd0, hN0]
def reciprocalMobiusCesaroEnergy (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, mobiusReciprocalSum j ^ 2
theorem reciprocalMobiusCesaroEnergy_nonneg (N : ℕ) :
    0 ≤ reciprocalMobiusCesaroEnergy N := by
  unfold reciprocalMobiusCesaroEnergy
  positivity
theorem reciprocalMobiusCesaroEnergy_tendsto_zero :
    Tendsto reciprocalMobiusCesaroEnergy atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
    ∑ j ∈ Finset.range N, mobiusReciprocalSum j ^ 2) atTop (𝓝 0)
  simpa only [zero_pow (by decide : 2 ≠ 0)] using
    (mobiusReciprocalSum_tendsto_zero.pow 2).cesaro
end RiemannResearch.RH.Pareto
