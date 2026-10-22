/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.FiniteDilationMobiusKernel
import RiemannResearch.RH.BalazardReciprocalCharge

/-!
# Finite signed dilation certificates in the physical Hilbert space

Source: Section 5 of the lateral-screening continuation, 24 September 2026.
At common cutoff Q*N the kernel dilation h represents the physical charge
at (Q/h)*N. The reversal is explicit, so no unproved symmetry of mixed
Möbius correlation series is used. All finite signed combinations of
integer-dilated charges are covered by a common multiple Q.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

def finiteDilationReciprocalCharge (S : Finset ℕ) (w : ℕ → ℝ) (Q N : ℕ) :
    ThresholdHilbert :=
  ∑ h ∈ S, w h • reciprocalChargeRiesz ((Q / h) * N)

theorem finiteDilation_quotient_reverse (Q N k h : ℕ)
    (hh : 0 < h) (hQ : h ∣ Q) :
    (Q * N / k) / h = ((Q / h) * N) / k := by
  have hdvd : h ∣ Q * N := hQ.trans (dvd_mul_right Q N)
  have hdiv : Q * N / h = (Q / h) * N := by
    apply Nat.eq_of_mul_eq_mul_left hh
    calc
      h * (Q * N / h) = Q * N := by
        simpa only [Nat.mul_comm] using Nat.div_mul_cancel hdvd
      _ = ((Q / h) * h) * N := congrArg (fun t : ℕ => t * N)
        (Nat.div_mul_cancel hQ).symm
      _ = h * ((Q / h) * N) := by ring
  calc
    (Q * N / k) / h = (Q * N / h) / k := by
      simp only [Nat.div_div_eq_div_mul, Nat.mul_comm k h]
    _ = ((Q / h) * N) / k := by rw [hdiv]

theorem finiteDilationReciprocalCharge_sequence
    (S : Finset ℕ) (w : ℕ → ℝ) (Q N k : ℕ)
    (hS : ∀ h ∈ S, 0 < h) (hSQ : ∀ h ∈ S, h ∣ Q) (hk : 0 < k) :
    hilbertSequence (finiteDilationReciprocalCharge S w Q N) k =
      (k : ℝ) * ((k : ℝ) + 1) *
        (finiteDilationMobiusKernel S w (Q * N / k) / (k : ℝ) -
          finiteDilationMobiusKernel S w (Q * N / (k + 1)) / ((k : ℝ) + 1)) := by
  rw [← anchoredEvaluationCLM_apply]
  simp only [finiteDilationReciprocalCharge, map_sum, map_smul,
    anchoredEvaluationCLM_apply, smul_eq_mul]
  unfold finiteDilationMobiusKernel
  rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [reciprocalChargeRiesz_sequence ((Q / h) * N) k hk,
    finiteDilation_quotient_reverse Q N k h (hS h hh) (hSQ h hh),
    finiteDilation_quotient_reverse Q N (k + 1) h (hS h hh) (hSQ h hh)]
  ring

theorem finiteDilationReciprocalCharge_norm_sq_eq_energy
    (S : Finset ℕ) (w : ℕ → ℝ) (Q N : ℕ)
    (hS : ∀ h ∈ S, 0 < h) (hSQ : ∀ h ∈ S, h ∣ Q) :
    ‖finiteDilationReciprocalCharge S w Q N‖ ^ 2 =
      ∑ k ∈ Finset.Icc 1 (Q * N),
        (k : ℝ) * ((k : ℝ) + 1) *
          (finiteDilationMobiusKernel S w (Q * N / k) / (k : ℝ) -
            finiteDilationMobiusKernel S w (Q * N / (k + 1)) /
              ((k : ℝ) + 1)) ^ 2 := by
  rw [hilbert_norm_weighted_sq]
  rw [tsum_eq_sum (s := Finset.Icc 1 (Q * N)) (by
    intro k hk
    by_cases hk0 : k = 0
    · simp [hk0]
    · have hkN : Q * N < k := by
        have hn : ¬ (1 ≤ k ∧ k ≤ Q * N) := by
          simpa only [Finset.mem_Icc] using hk
        omega
      rw [finiteDilationReciprocalCharge_sequence S w Q N k hS hSQ
        (Nat.pos_of_ne_zero hk0)]
      have hkS : Q * N < k + 1 := by omega
      simp [Nat.div_eq_of_lt hkN, Nat.div_eq_of_lt hkS,
        finiteDilationMobiusKernel, mobiusReciprocalSum])]
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hk0
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  rw [finiteDilationReciprocalCharge_sequence S w Q N k hS hSQ hk0]
  unfold positiveWeight
  change 1 / ((k : ℝ) * ((k : ℝ) + 1)) *
    ((k : ℝ) * ((k : ℝ) + 1) *
      (finiteDilationMobiusKernel S w (Q * N / k) / (k : ℝ) -
        finiteDilationMobiusKernel S w (Q * N / (k + 1)) / ((k : ℝ) + 1))) ^ 2 = _
  field_simp

/-- Exact limiting norm of a general finite signed physical charge combination. -/
theorem finiteDilationReciprocalCharge_norm_sq_tendsto
    (S : Finset ℕ) (w : ℕ → ℝ) (Q : ℕ) (hQ : 0 < Q)
    (hS : ∀ h ∈ S, 0 < h) (hSQ : ∀ h ∈ S, h ∣ Q) :
    Tendsto (fun N => ‖finiteDilationReciprocalCharge S w Q N‖ ^ 2)
      atTop (𝓝 (∑' n, finiteDilationMobiusCoefficient S w n ^ 2)) := by
  have hcofinal : Tendsto (fun N : ℕ => Q * N) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with N hN
    nlinarith
  have ht := (finiteDilationMobiusKernel_square_energy_tendsto S w hS).comp hcofinal
  simpa only [Function.comp_def,
    ← finiteDilationReciprocalCharge_norm_sq_eq_energy S w Q _ hS hSQ] using ht

end RiemannResearch.RH.Pareto
