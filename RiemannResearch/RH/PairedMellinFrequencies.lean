import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Quantitative selection of two logarithmic resonance frequencies.
The proof uses Mathlib's finite-cutoff Dirichlet approximation theorem. -/

noncomputable section
namespace RiemannResearch.RH.Pareto.CompressedMellin

theorem pairedMellinFrequencies (r : ℝ) (hr : 4 ≤ r) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧
      let t := 2 * Real.pi * (m : ℝ) / Real.log 2
      let s := 2 * Real.pi * (n : ℝ) / Real.log 3
      1 ≤ t ∧ 1 ≤ s ∧ max t s ≤ 64 * r ^ 2 ∧
        |t - s| ≤ 16 / r ^ 2 ∧ |t - s| ≤ 1 := by
  have hr0 : 0 < r := by linarith
  have hr2 : 16 ≤ r ^ 2 := by nlinarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlog2p : 0 < Real.log 2 := by linarith
  have hlog23 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have hlog3p : 0 < Real.log 3 := hlog2p.trans hlog23
  have hlog3u : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_four
  let Q : ℕ := ⌈r ^ 2⌉₊
  have hQlo : r ^ 2 ≤ (Q : ℝ) := Nat.le_ceil _
  have hQhi : (Q : ℝ) < r ^ 2 + 1 := Nat.ceil_lt_add_one (sq_nonneg r)
  have hQpos : 0 < Q := by
    by_contra h
    have hz : Q = 0 := by omega
    rw [hz] at hQlo
    norm_num at hQlo
    nlinarith
  let α : ℝ := Real.log 3 / Real.log 2
  have hα : 1 < α := by
    dsimp [α]
    rw [lt_div_iff₀ hlog2p]
    simpa using hlog23
  obtain ⟨m, hm, hmQ, happ⟩ := Real.exists_nat_abs_mul_sub_round_le α hQpos
  let z : ℤ := round ((m : ℝ) * α)
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have happ' : |(m : ℝ) * α - (z : ℝ)| ≤ 1 / ((Q : ℝ) + 1) := happ
  have hsmall : 1 / ((Q : ℝ) + 1) ≤ 1 := by
    rw [div_le_iff₀ (by positivity : 0 < (Q : ℝ) + 1)]
    have h := Nat.cast_nonneg (α := ℝ) Q
    linarith
  have hzpos : 0 < z := by
    have h := (abs_le.mp (happ'.trans hsmall)).2
    have hprod : 1 < (m : ℝ) * α := by nlinarith
    have hzR : (0 : ℝ) < (z : ℝ) := by linarith
    exact_mod_cast hzR
  let n : ℕ := z.toNat
  have hn : 0 < n := by dsimp [n]; omega
  have hncast : (n : ℝ) = (z : ℝ) := by
    have he : (n : ℤ) = z := Int.toNat_of_nonneg hzpos.le
    exact_mod_cast he
  let t : ℝ := 2 * Real.pi * (m : ℝ) / Real.log 2
  let s : ℝ := 2 * Real.pi * (n : ℝ) / Real.log 3
  have ht1 : 1 ≤ t := by
    dsimp [t]
    rw [le_div_iff₀ hlog2p]
    nlinarith
  have hs1 : 1 ≤ s := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    dsimp [s]
    rw [le_div_iff₀ hlog3p]
    nlinarith
  have hdiff : |t - s| = (2 * Real.pi / Real.log 3) * |(m : ℝ) * α - (z : ℝ)| := by
    rw [← abs_of_pos (div_pos (by positivity) hlog3p), ← abs_mul]
    congr 1
    dsimp [t, s, α]
    rw [hncast]
    field_simp
    <;> ring
  have hcoef : 2 * Real.pi / Real.log 3 ≤ 16 := by
    rw [div_le_iff₀ hlog3p]
    nlinarith
  have hdist : |t - s| ≤ 16 / r ^ 2 := by
    rw [hdiff]
    calc
      _ ≤ 16 * (1 / ((Q : ℝ) + 1)) :=
        mul_le_mul hcoef happ' (abs_nonneg _) (by norm_num)
      _ ≤ 16 * (1 / r ^ 2) :=
        mul_le_mul_of_nonneg_left
          (one_div_le_one_div_of_le (sq_pos_of_pos hr0) (by linarith)) (by norm_num)
      _ = _ := by ring
  have hdist1 : |t - s| ≤ 1 := by
    apply hdist.trans
    rw [div_le_iff₀ (sq_pos_of_pos hr0)]
    linarith
  have htupper : t ≤ 32 * r ^ 2 := by
    have hmQ' : (m : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hmQ
    have htm : t ≤ 16 * (m : ℝ) := by
      dsimp [t]
      rw [div_le_iff₀ hlog2p]
      have hp := mul_le_mul_of_nonneg_right hlog2 (Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))
      nlinarith
    nlinarith
  have hsupper : s ≤ 64 * r ^ 2 := by
    have h := (abs_le.mp hdist1).1
    linarith
  exact ⟨m,n,hm,hn,ht1,hs1,max_le (by linarith) hsupper,hdist,hdist1⟩

end RiemannResearch.RH.Pareto.CompressedMellin
