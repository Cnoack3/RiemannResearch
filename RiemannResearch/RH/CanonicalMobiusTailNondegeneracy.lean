import RiemannResearch.RH.CanonicalMobiusSignedAverages
import Mathlib.Data.Nat.Factorial.Basic

/-!
# No admissible covariance-null vector for finite canonical averages

Source: user-provided `Pareto_Direct_Attempt_Sublinear_Energy_2026-09-22.md`,
Section 7, for the singular covariance question. The specialization proved
here uses periodicity of finite residue combinations: an infinite tail cannot
vanish when the first physical coordinate equals one. This is a finite-stage
strict positivity result and gives no uniform positive lower bound in the cutoff.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.RH.ArithmeticCumulative

/-- Every common multiple of the finitely many conductors is a physical period. -/
theorem finiteSpace_sequence_add_of_dvd (M n q : ℕ)
    (hdiv : ∀ d : Fin M, d.val + 2 ∣ q)
    (f : ThresholdHilbert) (hf : f ∈ finiteSpace M) :
    hilbertSequence f (n + q) = hilbertSequence f n := by
  obtain ⟨a, ha⟩ := finiteSpace_expansion M f hf
  rw [ha]
  change hilbertSequenceLinear (∑ d : Fin M, a d • residueAtom d.val) (n + q) =
    hilbertSequenceLinear (∑ d : Fin M, a d • residueAtom d.val) n
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro d hd
  change a d * hilbertSequence (residueAtom d.val) (n + q) =
    a d * hilbertSequence (residueAtom d.val) n
  simp only [residueAtom, normalizedResidueHilbert_sequence]
  simp [residueFraction, Nat.add_mod, Nat.mod_eq_zero_of_dvd (hdiv d)]

/-- Vanishing of the complete infinite tail forces the first physical value to
vanish for every finite legal vector. The factorial supplies a common period. -/
theorem finiteSpace_first_eq_zero_of_tailShift_eq_zero (M N : ℕ)
    (f : ThresholdHilbert) (hf : f ∈ finiteSpace M)
    (htail : hilbertTailShift f N = 0) : hilbertSequence f 1 = 0 := by
  let q : ℕ := N * (M + 1).factorial
  have hNq : N ≤ q := by
    dsimp [q]
    have hp := Nat.factorial_pos (M + 1)
    nlinarith
  have hdiv : ∀ d : Fin M, d.val + 2 ∣ q := by
    intro d
    have hd : d.val + 2 ∣ (M + 1).factorial :=
      Nat.dvd_factorial (by omega) (by omega)
    exact dvd_mul_of_dvd_right hd N
  have hperiod := finiteSpace_sequence_add_of_dvd M 1 q hdiv f hf
  have hc : f q = 0 := by
    have h := congrArg (fun x : ThresholdHilbert => x (q - N)) htail
    change f (q - N + N) = 0 at h
    simpa only [Nat.sub_add_cancel hNq] using h
  have hzero : hilbertSequence f (q + 1) = 0 := by
    rw [hilbertSequence_succ, hc, zero_div]
  have heq : 1 + q = q + 1 := by omega
  rw [heq, hzero] at hperiod
  exact hperiod.symm

theorem finiteSpace_tail_energy_pos_of_first_ne_zero (M N : ℕ)
    (f : ThresholdHilbert) (hf : f ∈ finiteSpace M)
    (hfirst : hilbertSequence f 1 ≠ 0) : 0 < ‖hilbertTailShift f N‖ ^ 2 := by
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro hz
  exact hfirst (finiteSpace_first_eq_zero_of_tailShift_eq_zero M N f hf hz)

/-- The manuscript's zero-minimum singular case cannot occur for an admissible
finite average with positive head cutoff, although its covariance may be singular. -/
theorem signedMobiusAverage_covariance_pos (s : Finset ℕ) (a : ℕ → ℝ)
    (N M : ℕ) (hN : 0 < N)
    (hsum : ∑ k ∈ s, a k = 1)
    (hindex : ∀ k ∈ s, N ≤ k) (hupper : ∀ k ∈ s, k ≤ M) :
    0 < ∑ k ∈ s, ∑ l ∈ s, a k * a l * canonicalMobiusTailCovariance N k l := by
  rw [← signedMobiusAverage_tail_energy]
  apply finiteSpace_tail_energy_pos_of_first_ne_zero M N _
    (signedMobiusAverage_mem_finiteSpace s a M hupper)
  rw [signedMobiusAverage_exact s a N hsum hindex 1 (by omega) (by omega)]
  norm_num

/-- Every null direction of the actual tail Gram form has zero total weight.
Thus covariance singularity produces only head-preserving coefficient redundancies. -/
theorem signedMobiusAverage_covariance_zero_imp_sum_zero
    (s : Finset ℕ) (a : ℕ → ℝ) (N M : ℕ)
    (hindex : ∀ k ∈ s, 0 < k) (hupper : ∀ k ∈ s, k ≤ M)
    (hzero : (∑ k ∈ s, ∑ l ∈ s,
      a k * a l * canonicalMobiusTailCovariance N k l) = 0) :
    ∑ k ∈ s, a k = 0 := by
  have ht : hilbertTailShift (signedMobiusAverage s a) N = 0 := by
    apply norm_eq_zero.mp
    apply (sq_eq_zero_iff).mp
    rwa [signedMobiusAverage_tail_energy]
  have hf := finiteSpace_first_eq_zero_of_tailShift_eq_zero M N
    (signedMobiusAverage s a) (signedMobiusAverage_mem_finiteSpace s a M hupper) ht
  rw [signedMobiusAverage_sequence] at hf
  have he : (∑ k ∈ s, a k * canonicalMobiusHead k 1) = ∑ k ∈ s, a k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [canonicalMobiusHead_exact k 1 (by omega) (hindex k hk), mul_one]
  rwa [he] at hf

end RiemannResearch.RH.Pareto.CoefficientStabilization
