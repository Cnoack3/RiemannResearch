import RiemannResearch.RH.IntegratedRamanujanHilbert
import RiemannResearch.RH.ParetoFiniteCertificates
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The logarithmic prime-power packet obstruction

Source: the user's proposal to synthesize log_* of the arithmetic constant-one
function in Ramanujan coordinates. Its coefficients are 1/k at p^k. This file
defines their finite packet synthesis explicitly; it does not identify
arithmetic convolution with a Hilbert-space operation.

The earlier ParetoFiniteCertificates gives finite-coordinate witnesses.
Here the continuous conductor-six functional gives an exact decomposition in
the complete Pareto Hilbert space, excludes the entire closed raw prime-power
span, and quantifies the necessary charge of any correction. The full residue
closure problem remains open. Mixed-screened packets are different vectors;
see PrimePowerRamanujanClosure for that valid conditional reduction.
-/

open Filter
open scoped BigOperators Topology
noncomputable section
namespace RiemannResearch.RH.Pareto.RamanujanLogarithm

/-- Closure of the uncorrected prime-power packets, including all signed
coefficients and every prime. The exponent-zero packet is identically zero. -/
def rawPrimePowerClosure : Submodule ℝ ThresholdHilbert :=
  (Submodule.span ℝ {v : ThresholdHilbert |
    ∃ p k : ℕ, p.Prime ∧ v = ramanujanPacketHilbert (p ^ k)}).topologicalClosure

theorem rawPrimePowerClosure_le_kernel :
    rawPrimePowerClosure ≤ LinearMap.ker (mobiusDifferenceCLM 6).toLinearMap := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro v ⟨p, k, hp, rfl⟩
    change mobiusDifferenceCLM 6 (ramanujanPacketHilbert (p ^ k)) = 0
    rw [mobiusDifferenceCLM_apply, hilbertSequence_ramanujanPacketHilbert]
    exact primePowerPacket_dualSix_zero p k hp
  · exact (mobiusDifferenceCLM 6).isClosed_ker

theorem dualSix_riesz_norm_sq : ‖mobiusRieszHilbert 6‖ ^ 2 = 92 := by
  rw [mobiusRieszHilbert_norm, mobiusDifferenceCLM_norm_sq 6 (by norm_num)]
  norm_num [show Finset.Icc 1 6 = {1, 2, 3, 4, 5, 6} by decide, dualCoeff,
    ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 3)]

/-- The full equality retains the signed conductor-six charge and the
orthogonal norm-square remainder for every actual Hilbert vector. -/
theorem error_eq_charge_add_remainder (f : ThresholdHilbert) :
    ‖hilbertOne - f‖ ^ 2 = (1 - mobiusDifferenceCLM 6 f) ^ 2 / 92 +
      ‖hilbertOne - f - ((1 - mobiusDifferenceCLM 6 f) / 92) •
        mobiusRieszHilbert 6‖ ^ 2 := by
  have hi : inner ℝ (hilbertOne - f) (mobiusRieszHilbert 6) =
      1 - mobiusDifferenceCLM 6 f := by
    rw [real_inner_comm, mobiusRieszHilbert_inner, map_sub,
      mobius_coordinate_one 6 (by norm_num)]
    norm_num
  have he := norm_sub_sq_real (hilbertOne - f)
    (((1 - mobiusDifferenceCLM 6 f) / 92) • mobiusRieszHilbert 6)
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right, hi, dualSix_riesz_norm_sq] at he
  nlinarith only [he]

theorem error_eq_obstruction_add_remainder (f : ThresholdHilbert)
    (hf : mobiusDifferenceCLM 6 f = 0) :
    ‖hilbertOne - f‖ ^ 2 = (1 : ℝ) / 92 +
      ‖hilbertOne - f - ((1 : ℝ) / 92) • mobiusRieszHilbert 6‖ ^ 2 := by
  simpa only [hf, sub_zero, one_pow] using error_eq_charge_add_remainder f

theorem rawPrimePowerClosure_error_floor (f : ThresholdHilbert)
    (hf : f ∈ rawPrimePowerClosure) :
    (1 : ℝ) / 92 ≤ ‖hilbertOne - f‖ ^ 2 := by
  have hz : mobiusDifferenceCLM 6 f = 0 := rawPrimePowerClosure_le_kernel hf
  rw [error_eq_obstruction_add_remainder f hz]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem one_not_mem_rawPrimePowerClosure :
    hilbertOne ∉ rawPrimePowerClosure := by
  intro h
  have he := rawPrimePowerClosure_error_floor hilbertOne h
  norm_num at he

/-- Finite synthesis of the logarithmic coefficients 1/k.
For the intended logarithm one takes k >= 1; allowing k = 0 merely adds zero. -/
def logPacketCombination (s : Finset (ℕ × ℕ)) : ThresholdHilbert :=
  ∑ u ∈ s, ((1 : ℝ) / (u.2 : ℝ)) • ramanujanPacketHilbert (u.1 ^ u.2)

theorem logPacketCombination_mem (s : Finset (ℕ × ℕ))
    (hs : ∀ u ∈ s, u.1.Prime) :
    logPacketCombination s ∈ rawPrimePowerClosure := by
  apply Submodule.le_topologicalClosure
  apply Submodule.sum_mem
  intro u hu
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨u.1, u.2, hs u hu, rfl⟩

theorem logPacketCombination_error_floor (s : Finset (ℕ × ℕ))
    (hs : ∀ u ∈ s, u.1.Prime) :
    (1 : ℝ) / 92 ≤ ‖hilbertOne - logPacketCombination s‖ ^ 2 :=
  rawPrimePowerClosure_error_floor _ (logPacketCombination_mem s hs)

/-- Any correction converting a raw prime-power family into a sequence
converging to one must supply asymptotic conductor-six charge exactly one. -/
theorem correction_charge_tendsto_one
    (f correction : ℕ → ThresholdHilbert)
    (hf : ∀ n, f n ∈ rawPrimePowerClosure)
    (ht : Tendsto (fun n => f n + correction n) atTop (𝓝 hilbertOne)) :
    Tendsto (fun n => mobiusDifferenceCLM 6 (correction n)) atTop (𝓝 1) := by
  have hz (n : ℕ) : mobiusDifferenceCLM 6 (f n) = 0 :=
    rawPrimePowerClosure_le_kernel (hf n)
  have hh := ((mobiusDifferenceCLM 6).continuous.tendsto hilbertOne).comp ht
  simpa only [Function.comp_def, map_add, hz, zero_add,
    mobius_coordinate_one 6 (by norm_num), moebius_six, Int.cast_one] using hh

end RiemannResearch.RH.Pareto.RamanujanLogarithm
