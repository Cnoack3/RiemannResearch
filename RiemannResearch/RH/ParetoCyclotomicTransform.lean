import RiemannResearch.RH.ParetoGeometricTransform
import RiemannResearch.RH.ParetoSequenceCertificates
import Mathlib.Tactic.Linarith

/-!
# Actual cyclotomic geometric transforms of residue generators

The complete infinite geometric transform is evaluated through the exact
discrete jump identity. The arithmetic progression series is reindexed with
its support proved, and every infinite-series subtraction is justified.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

private theorem bounded_power_summable {f : ℕ → ℝ} {C t : ℝ}
    (hf : ∀ n, |f n| ≤ C) (ht : t ∈ Set.Ico 0 1) :
    Summable (fun n => f n * t ^ n) := by
  have ha : |t| < 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
  apply ((hasSum_geometric_of_abs_lt_one ha).summable.mul_left C).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ht.1 n)]
  exact mul_le_mul_of_nonneg_right (hf n) (pow_nonneg ht.1 n)

/-- The actual bounded transform equals the full discrete jump series. -/
theorem geometricTransform_eq_jump_series {f : ℕ → ℝ} {C t : ℝ}
    (hf : ∀ n, |f n| ≤ C) (h0 : f 0 = 0) (ht : t ∈ Set.Ico 0 1) :
    geometricTransform (fun n => f (n+1)) t =
      ∑' n, (f (n+1) - f n) * t ^ n := by
  have hs := bounded_power_summable (fun n => hf (n+1)) ht
  have hb := bounded_power_summable hf ht
  have hshift : (∑' n, f n * t ^ n) = t * (∑' n, f (n+1) * t ^ n) := by
    rw [hb.tsum_eq_zero_add]
    simp only [h0, zero_mul, zero_add, pow_succ]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    ring
  calc
    _ = (1-t) * (∑' n, f (n+1) * t ^ n) := by
      unfold geometricTransform geometricProbability
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      ring
    _ = (∑' n, f (n+1) * t ^ n) - (∑' n, f n * t ^ n) := by
      rw [hshift]
      ring
    _ = _ := by
      rw [← hs.tsum_sub hb]
      apply tsum_congr
      intro n
      ring

def divisorPower (m : ℕ) (t : ℝ) (n : ℕ) : ℝ := if m ∣ n+1 then t ^ n else 0

theorem divisorPower_summable (m : ℕ) {t : ℝ} (ht : t ∈ Set.Ico 0 1) :
    Summable (divisorPower m t) := by
  have ha : |t| < 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
  apply Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (hasSum_geometric_of_abs_lt_one ha).summable
  · unfold divisorPower
    split_ifs
    · exact pow_nonneg ht.1 n
    · exact le_rfl
  · unfold divisorPower
    split_ifs
    · exact le_rfl
    · exact pow_nonneg ht.1 n

/-- Exact geometric sum on all positive multiples of an arbitrary dilation. -/
theorem divisorPower_tsum (m : ℕ) (hm : 0 < m) {t : ℝ} (ht : t ∈ Set.Ico 0 1) :
    (∑' n, divisorPower m t n) = t ^ (m-1) / (1-t ^ m) := by
  let j : ℕ → ℕ := fun r => m*r+(m-1)
  have hj : Function.Injective j := by
    intro r s h
    exact Nat.eq_of_mul_eq_mul_left hm (Nat.add_right_cancel h)
  have hsupport : Function.support (divisorPower m t) ⊆ Set.range j := by
    intro n hn
    have hd : m ∣ n+1 := by
      by_contra h
      exact hn (by simp [divisorPower, h])
    obtain ⟨q, hq⟩ := hd
    have hq0 : q ≠ 0 := by intro h; subst q; simp at hq
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0
    refine ⟨r, ?_⟩
    dsimp [j]
    rw [Nat.mul_succ] at hq
    omega
  rw [← hj.tsum_eq hsupport]
  have he (r : ℕ) : divisorPower m t (j r) = (t ^ m) ^ r * t ^ (m-1) := by
    have hd : m ∣ j r + 1 := by
      refine ⟨r+1, ?_⟩
      dsimp [j]
      rw [Nat.mul_add, Nat.mul_one]
      omega
    simp only [divisorPower, if_pos hd, j, pow_add, pow_mul]
  simp_rw [he]
  rw [tsum_mul_right]
  have ha : |t| < 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
  have ham : |t ^ m| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg t) ha (Nat.ne_of_gt hm)
  rw [(hasSum_geometric_of_abs_lt_one ham).tsum_eq]
  ring

/-- Exact cyclotomic transform for every genuine integer residue generator. -/
theorem geometricTransform_residue_generator (a m : ℕ) (ha : 0 < a) (hm : 0 < m)
    {t : ℝ} (ht : t ∈ Set.Ico 0 1) :
    geometricTransform (fun n => residue (a*m) (n+1) - residue m (n+1)) t =
      (m : ℝ) * (t ^ (m-1) / (1-t ^ m) -
        (a : ℝ) * t ^ (a*m-1) / (1-t ^ (a*m))) := by
  let f : ℕ → ℝ := fun k => residue (a*m) k - residue m k
  have hf : ∀ k, |f k| ≤ (a*m : ℕ) + (m : ℝ) := by
    intro k
    dsimp [f]
    calc
      _ ≤ |residue (a*m) k| + |residue m k| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le (residue (a*m) k) (residue m k)
      _ ≤ _ := add_le_add (residue_abs_le (a*m) k (Nat.mul_pos ha hm)) (residue_abs_le m k hm)
  have h0 : f 0 = 0 := by simp [f, residue]
  rw [geometricTransform_eq_jump_series hf h0 ht]
  have he (n : ℕ) : (f (n+1)-f n) * t ^ n =
      (m : ℝ) * divisorPower m t n - ((a*m : ℕ) : ℝ) * divisorPower (a*m) t n := by
    have h1 := residue_difference m (n+1) (by omega)
    have h2 := residue_difference (a*m) (n+1) (by omega)
    simp only [Nat.add_sub_cancel] at h1 h2
    have hj : f (n+1)-f n = (if m ∣ n+1 then (m : ℝ) else 0) -
        (if a*m ∣ n+1 then ((a*m : ℕ) : ℝ) else 0) := by
      dsimp [f]
      split_ifs at h1 h2 ⊢ <;> linarith
    rw [hj]
    unfold divisorPower
    split_ifs <;> ring
  simp_rw [he]
  rw [((divisorPower_summable m ht).mul_left _).tsum_sub
    ((divisorPower_summable (a*m) ht).mul_left _), tsum_mul_left, tsum_mul_left,
    divisorPower_tsum m hm ht, divisorPower_tsum (a*m) (Nat.mul_pos ha hm) ht]
  push_cast
  ring

end
end RiemannResearch.RH.Pareto
