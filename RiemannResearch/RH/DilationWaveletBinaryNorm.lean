import RiemannResearch.RH.DilationWaveletAlgebra
import Mathlib.Analysis.Real.Pi.Leibniz
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact norm of every binary dilation wavelet

Source: user-provided analytic_wavelet_foothold.md, Sections 3 and 7,
September 8, 2026. The complete weighted norm, including its infinite tail,
is evaluated using four-term blocks and Mathlib's formalized Leibniz formula
for pi. No finite conductor or RH hypothesis occurs.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
open Filter
noncomputable section

private def binaryMother (k : ℕ) : ℝ :=
  ((k % 2 : ℕ) : ℝ) - ((k / 2 % 2 : ℕ) : ℝ)

private theorem binaryMother_eq (k : ℕ) :
    binaryMother k = dilationWaveletSequence 2 1 k := by
  simp [binaryMother, dilationWaveletSequence, digitSequence]

private theorem binaryMother_zero (n : ℕ) : binaryMother (4*n) = 0 := by
  have h₁ : (4*n) % 2 = 0 := by omega
  have h₂ : (4*n/2) % 2 = 0 := by omega
  simp only [binaryMother, h₁, h₂]
  norm_num

private theorem binaryMother_one (n : ℕ) : binaryMother (4*n+1) = 1 := by
  have h₁ : (4*n+1) % 2 = 1 := by omega
  have h₂ : ((4*n+1)/2) % 2 = 0 := by omega
  simp only [binaryMother, h₁, h₂]
  norm_num

private theorem binaryMother_two (n : ℕ) : binaryMother (4*n+2) = -1 := by
  have h₁ : (4*n+2) % 2 = 0 := by omega
  have h₂ : ((4*n+2)/2) % 2 = 1 := by omega
  simp only [binaryMother, h₁, h₂]
  norm_num

private theorem binaryMother_three (n : ℕ) : binaryMother (4*n+3) = 0 := by
  have h₁ : (4*n+3) % 2 = 1 := by omega
  have h₂ : ((4*n+3)/2) % 2 = 1 := by omega
  simp only [binaryMother, h₁, h₂]
  norm_num

private theorem binaryMother_sq_bound (k : ℕ) : |binaryMother k ^ 2| ≤ 1 := by
  have h₁ : k % 2 < 2 := Nat.mod_lt _ (by omega)
  have h₂ : k / 2 % 2 < 2 := Nat.mod_lt _ (by omega)
  have h₁' : k % 2 = 0 ∨ k % 2 = 1 := by omega
  have h₂' : k / 2 % 2 = 0 ∨ k / 2 % 2 = 1 := by omega
  rcases h₁' with h₁' | h₁' <;> rcases h₂' with h₂' | h₂' <;>
    norm_num [binaryMother, h₁', h₂']

private def oddPair (n : ℕ) : ℝ :=
  1 / (4*(n:ℝ)+1) - 1 / (4*(n:ℝ)+3)

private theorem binaryMother_block (n : ℕ) :
    (∑ j ∈ Finset.range 4, positiveWeight (4*n+j) * binaryMother (4*n+j)^2) =
      oddPair n := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.add_zero]
  rw [binaryMother_zero, binaryMother_one, binaryMother_two, binaryMother_three]
  norm_num only [zero_pow, one_pow, neg_one_sq, mul_zero, mul_one, add_zero, zero_add]
  rw [positiveWeight_difference _ (by omega), positiveWeight_difference _ (by omega)]
  push_cast
  unfold oddPair
  ring

/-- Exact finite block identity before taking any limit. -/
theorem binary_wavelet_partial_energy (N : ℕ) :
    (∑ k ∈ Finset.range (4*N), positiveWeight k * dilationWaveletSequence 2 1 k ^ 2) =
      ∑ j ∈ Finset.range N, (1 / (4*(j:ℝ)+1) - 1 / (4*(j:ℝ)+3)) := by
  simp_rw [← binaryMother_eq]
  change (∑ k ∈ Finset.range (4*N), positiveWeight k * binaryMother k ^ 2) =
    ∑ j ∈ Finset.range N, oddPair j
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, binaryMother_block]
    exact (Finset.sum_range_succ oddPair N).symm

private theorem oddPair_partial_sum (N : ℕ) :
    (∑ j ∈ Finset.range N, oddPair j) =
      ∑ j ∈ Finset.range (2*N), (-1:ℝ)^j / (2*(j:ℝ)+1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Nat.mul_succ, Finset.sum_range_add, ← ih]
    congr 1
    simp [oddPair, Finset.sum_range_succ, pow_add, pow_mul]
    <;> ring

/-- The infinite weighted sum is pi/4, rather than a finite numerical estimate. -/
theorem binary_wavelet_energy_one :
    (∑' k, positiveWeight k * dilationWaveletSequence 2 1 k ^ 2) = Real.pi / 4 := by
  have hs : Summable (fun k => positiveWeight k * binaryMother k^2) :=
    weighted_summable_of_bounded binaryMother_sq_bound
  have hcofinal (p : ℕ) (hp : 0 < p) :
      Tendsto (fun n : ℕ => p*n) atTop atTop := by
    apply tendsto_atTop_mono (fun n => ?_) tendsto_id
    exact Nat.le_mul_of_pos_left n hp
  have h₁ := hs.hasSum.tendsto_sum_nat.comp (hcofinal 4 (by omega))
  have h₂ := Real.tendsto_sum_pi_div_four.comp (hcofinal 2 (by omega))
  have heq :
      (fun N => ∑ k ∈ Finset.range (4*N), positiveWeight k * binaryMother k^2) =
      (fun N => ∑ j ∈ Finset.range (2*N), (-1:ℝ)^j / (2*(j:ℝ)+1)) := by
    funext N
    simp_rw [binaryMother_eq]
    rw [binary_wavelet_partial_energy]
    exact oddPair_partial_sum N
  simp only [Function.comp_def] at h₁ h₂
  rw [heq] at h₁
  have h := tendsto_nhds_unique h₁ h₂
  simpa only [binaryMother_eq] using h

/-- Base binary wavelet norm in the actual complete weighted Hilbert space. -/
theorem binary_wavelet_hilbert_norm_one :
    ‖dilationWaveletHilbert 2 1 (by omega) (by omega)‖^2 = Real.pi / 4 := by
  rw [hilbert_norm_weighted_sq, hilbertSequence_dilationWaveletHilbert]
  exact binary_wavelet_energy_one

/-- All positive integer dilations have exact norm pi/(4m). -/
theorem binary_wavelet_hilbert_norm_sq (m : ℕ) (hm : 0 < m) :
    ‖dilationWaveletHilbert 2 m (by omega) hm‖^2 = Real.pi / (4*(m:ℝ)) := by
  rw [dilationWaveletHilbert_norm_sq, binary_wavelet_hilbert_norm_one]
  ring

end
end RiemannResearch.RH.Pareto
