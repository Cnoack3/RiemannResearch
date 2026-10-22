import RiemannResearch.RH.ParetoCyclotomicTransform
import RiemannResearch.RH.DilationWaveletAlgebra

/-!
# Exact geometric transforms of the legal dilation wavelets

The explicit rational functions here are proved to be the actual infinite
transforms, rather than defined as candidate substitutes for them.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

theorem geometricTransform_smul (c : ℝ) (f : ℕ → ℝ) (t : ℝ) :
    geometricTransform (fun n => c * f n) t = c * geometricTransform f t := by
  unfold geometricTransform
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  ring

theorem geometricTransform_sub {f g : ℕ → ℝ} {C D t : ℝ}
    (hf : ∀ n, |f n| ≤ C) (hg : ∀ n, |g n| ≤ D) (ht : t ∈ Set.Ico 0 1) :
    geometricTransform (fun n => f n - g n) t =
      geometricTransform f t - geometricTransform g t := by
  unfold geometricTransform
  simp only [sub_mul]
  exact (geometricTransform_norm_summable hf ht).of_norm.tsum_sub
    (geometricTransform_norm_summable hg ht).of_norm

/-- Exact transform of a scaled actual integer residue generator. -/
theorem geometricTransform_digitSequence (a m : ℕ) (ha : 0 < a) (hm : 0 < m)
    {t : ℝ} (ht : t ∈ Set.Ico 0 1) :
    geometricTransform (fun n => digitSequence a m (n+1)) t =
      t ^ (m-1) / (1-t ^ m) - (a : ℝ) * t ^ (a*m-1) / (1-t ^ (a*m)) := by
  have h := geometricTransform_residue_generator a m ha hm ht
  have he : (fun n => residue (a*m) (n+1) - residue m (n+1)) =
      fun n => (m : ℝ) * digitSequence a m (n+1) := by
    funext n
    exact (digitSequence_generator a m (n+1)).symm
  rw [he, geometricTransform_smul] at h
  exact mul_left_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hm)) h

/-- Full two-seed wavelet transform, retaining every signed rational term. -/
theorem geometricTransform_dilationWavelet (a m : ℕ) (ha : 0 < a) (hm : 0 < m)
    {t : ℝ} (ht : t ∈ Set.Ico 0 1) :
    geometricTransform (fun n => dilationWaveletSequence a m (n+1)) t =
      (t ^ (m-1) / (1-t ^ m) - (a : ℝ) * t ^ (a*m-1) / (1-t ^ (a*m))) -
      (t ^ (a*m-1) / (1-t ^ (a*m)) -
        (a : ℝ) * t ^ (a*(a*m)-1) / (1-t ^ (a*(a*m)))) := by
  change geometricTransform (fun n => digitSequence a m (n+1) - digitSequence a (a*m) (n+1)) t = _
  rw [geometricTransform_sub (fun n => digitSequence_abs_le a m ha (n+1))
    (fun n => digitSequence_abs_le a (a*m) ha (n+1)) ht,
    geometricTransform_digitSequence a m ha hm ht,
    geometricTransform_digitSequence a (a*m) ha (Nat.mul_pos ha hm) ht]

/-- The explicit binary cyclotomic function is the genuine infinite wavelet transform. -/
theorem geometricTransform_binaryWavelet (m : ℕ) (hm : 0 < m)
    {t : ℝ} (ht : t ∈ Set.Ico 0 1) :
    geometricTransform (fun n => dilationWaveletSequence 2 m (n+1)) t =
      t ^ (m-1) * (1-t ^ m) / ((1+t ^ m) * (1+t ^ (2*m))) := by
  rw [geometricTransform_dilationWavelet 2 m (by decide) hm ht]
  norm_num only [Nat.cast_ofNat]
  have h2 : t ^ (2*m-1) = t ^ (m-1) * t ^ m := by
    rw [← pow_add]
    congr 1
    omega
  have h4 : t ^ (2*(2*m)-1) = t ^ (m-1) * (t ^ m) ^ 3 := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hp2 : t ^ (2*m) = (t ^ m) ^ 2 := by rw [← pow_mul, Nat.mul_comm]
  have hp4 : t ^ (2*(2*m)) = (t ^ m) ^ 4 := by
    rw [← pow_mul]
    congr 1
    omega
  rw [h2, h4, hp2, hp4]
  have hm0 : 0 ≤ t ^ m := pow_nonneg ht.1 m
  have hm1 : t ^ m < 1 := pow_lt_one₀ ht.1 ht.2 (Nat.ne_of_gt hm)
  have hA : 1 - t ^ m ≠ 0 := by linarith
  have hB : 1 - (t ^ m) ^ 2 ≠ 0 := by
    have h2lt := pow_lt_one₀ hm0 hm1 (by decide : (2 : ℕ) ≠ 0)
    linarith
  have hC : 1 - (t ^ m) ^ 4 ≠ 0 := by
    have h4lt := pow_lt_one₀ hm0 hm1 (by decide : (4 : ℕ) ≠ 0)
    linarith
  have hD : 1 + t ^ m ≠ 0 := by positivity
  have hE : 1 + (t ^ m) ^ 2 ≠ 0 := by positivity
  field_simp [hA, hB, hC, hD, hE]
  <;> ring

end
end RiemannResearch.RH.Pareto
