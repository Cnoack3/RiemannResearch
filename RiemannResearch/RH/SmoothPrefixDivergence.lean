import RiemannResearch.RH.SmoothPrefixFlow

/-!
# Full Pareto energy growth of fixed-prefix exact interpolation

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Section 9.1. All infinite sums below are the original Pareto sums. Their
summability is supplied by actual finite generator bounds.
-/

namespace RiemannResearch.RH.Pareto

open scoped BigOperators
open PositiveSeedCone SmoothRepairAntichain

noncomputable section

private theorem prefix_bounded (N : ℕ) (u v : ℕ → ℝ) :
    ∃ C : ℝ, ∀ k, |twoChannelPrefix N u v k| ≤ C := by
  refine ⟨coefficientBound (Finset.Icc 1 N) (fun _ => 2) id u +
    coefficientBound (Finset.Icc 1 N) (fun _ => 3) id v, ?_⟩
  intro k
  have hu := seedCombination_abs_le (Finset.Icc 1 N) (fun _ => 2) id u
    (by intro i hi; omega) (fun i hi => (Finset.mem_Icc.mp hi).1) k
  have hv := seedCombination_abs_le (Finset.Icc 1 N) (fun _ => 3) id v
    (by intro i hi; omega) (fun i hi => (Finset.mem_Icc.mp hi).1) k
  change |channelPrefix 2 N u k| ≤ _ at hu
  change |channelPrefix 3 N v k| ≤ _ at hv
  exact (abs_add_le _ _).trans (add_le_add hu hv)

private theorem bounded_square_summable {F : ℕ → ℝ} {C : ℝ}
    (hF : ∀ k, |F k| ≤ C) :
    Summable (fun k => positiveWeight k * (F k) ^ 2) := by
  simpa only [pow_two] using weighted_summable_of_bounded (bounded_product hF hF)

private theorem bounded_difference {F G : ℕ → ℝ} {C D : ℝ}
    (hF : ∀ k, |F k| ≤ C) (hG : ∀ k, |G k| ≤ D) :
    ∀ k, |F k - G k| ≤ C + D := by
  intro k
  calc
    |F k - G k| = |F k + -G k| := by rw [sub_eq_add_neg]
    _ ≤ |F k| + |-G k| := abs_add_le _ _
    _ ≤ C + D := by rw [abs_neg]; exact add_le_add (hF k) (hG k)

private theorem finite_difference_energy_le_four_max
    (s : Finset ℕ) (F G : ℕ → ℝ) {C D : ℝ}
    (hF : ∀ k, |F k| ≤ C) (hG : ∀ k, |G k| ≤ D) :
    (∑ k ∈ s, positiveWeight k * (F k - G k) ^ 2) ≤
      4 * max (paretoInner F F) (paretoInner G G) := by
  have hfs := bounded_square_summable hF
  have hgs := bounded_square_summable hG
  have hf : (∑ k ∈ s, positiveWeight k * (F k) ^ 2) ≤ paretoInner F F := by
    simpa only [paretoInner, pow_two] using
      hfs.sum_le_tsum s (fun k hk => mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _))
  have hg : (∑ k ∈ s, positiveWeight k * (G k) ^ 2) ≤ paretoInner G G := by
    simpa only [paretoInner, pow_two] using
      hgs.sum_le_tsum s (fun k hk => mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _))
  have hpoint : (∑ k ∈ s, positiveWeight k * (F k - G k) ^ 2) ≤
      2 * (∑ k ∈ s, positiveWeight k * (F k) ^ 2) +
        2 * (∑ k ∈ s, positiveWeight k * (G k) ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro k hk
    nlinarith [mul_nonneg (positiveWeight_nonneg k) (sq_nonneg (F k + G k))]
  have hmF := le_max_left (paretoInner F F) (paretoInner G G)
  have hmG := le_max_right (paretoInner F F) (paretoInner G G)
  linarith

/-- Equation (43), including both the complete increment norm and the prefix norms. -/
theorem fixed_prefix_energy_growth (u v : ℕ → ℝ)
    (hhead : ∀ N k, 0 < k → k ≤ N → twoChannelPrefix N u v k = 1)
    (r : ℕ) (hr : 2 ≤ r) :
    ∃ n : ℕ, 2 ^ r ≤ n ∧
      ((2 : ℝ) ^ r / (18 * ((r : ℝ) + 1) ^ 2) ≤
        paretoInner (fun k => twoChannelPrefix n u v k - twoChannelPrefix (n - 1) u v k)
          (fun k => twoChannelPrefix n u v k - twoChannelPrefix (n - 1) u v k)) ∧
      ((2 : ℝ) ^ r / (72 * ((r : ℝ) + 1) ^ 2) ≤
        max (paretoInner (twoChannelPrefix n u v) (twoChannelPrefix n u v))
          (paretoInner (twoChannelPrefix (n - 1) u v) (twoChannelPrefix (n - 1) u v))) := by
  obtain ⟨i, hi, hcoeff⟩ := exists_large_smooth_prefix_coefficient u v hhead r hr
  let n := 2 ^ i * 3 ^ (r - i)
  have hiR : i ≤ r := by have := Finset.mem_range.mp hi; omega
  have hn : 0 < n := by dsimp [n]; positivity
  have hlower : 2 ^ r ≤ n := endpoint_lower r i hiR
  have hblock := twoChannelPrefix_increment_block_energy (n - 1) u v
  have hsucc : n - 1 + 1 = n := by omega
  rw [hsucc] at hblock
  have hcoefsq : (1 / (3 * ((r : ℝ) + 1))) ^ 2 ≤ (u n + v n) ^ 2 := by
    have h0 : 0 ≤ 1 / (3 * ((r : ℝ) + 1)) := by positivity
    have hm := mul_self_le_mul_self h0 hcoeff
    simpa only [← pow_two, sq_abs] using hm
  have hnR : (2 : ℝ) ^ r ≤ (n : ℝ) := by exact_mod_cast hlower
  have hden : (r : ℝ) + 1 ≠ 0 := by positivity
  have hnorm : (2 : ℝ) ^ r / (18 * ((r : ℝ) + 1) ^ 2) =
      (2 : ℝ) ^ r / 2 * (1 / (3 * ((r : ℝ) + 1))) ^ 2 := by
    field_simp
    ring
  have hscale : (2 : ℝ) ^ r / (18 * ((r : ℝ) + 1) ^ 2) ≤
      (n : ℝ) / 2 * (u n + v n) ^ 2 := by
    rw [hnorm]
    exact mul_le_mul (by linarith) hcoefsq (sq_nonneg _)
      (by positivity : 0 ≤ (n : ℝ) / 2)
  obtain ⟨C, hF⟩ := prefix_bounded n u v
  obtain ⟨D, hG⟩ := prefix_bounded (n - 1) u v
  have hinc := bounded_square_summable (bounded_difference hF hG)
  have hfull : (∑ k ∈ Finset.Ico n (2 * n), positiveWeight k *
      (twoChannelPrefix n u v k - twoChannelPrefix (n - 1) u v k) ^ 2) ≤
      paretoInner (fun k => twoChannelPrefix n u v k - twoChannelPrefix (n - 1) u v k)
        (fun k => twoChannelPrefix n u v k - twoChannelPrefix (n - 1) u v k) := by
    simpa only [paretoInner, pow_two] using hinc.sum_le_tsum (Finset.Ico n (2 * n))
      (fun k hk => mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _))
  have hmax := finite_difference_energy_le_four_max (Finset.Ico n (2 * n))
    (twoChannelPrefix n u v) (twoChannelPrefix (n - 1) u v) hF hG
  rw [hblock] at hfull hmax
  refine ⟨n, hlower, hscale.trans hfull, ?_⟩
  have hquarter : (2 : ℝ) ^ r / (18 * ((r : ℝ) + 1) ^ 2) =
      4 * ((2 : ℝ) ^ r / (72 * ((r : ℝ) + 1) ^ 2)) := by
    field_simp <;> ring
  rw [hquarter] at hscale
  linarith

private theorem cubic_le_two_pow (r : ℕ) (hr : 10 ≤ r) :
    (r : ℝ) ^ 3 ≤ (2 : ℝ) ^ r := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hr
  clear hr
  induction s with
  | zero => norm_num
  | succ s ih =>
    rw [show 10 + (s + 1) = 10 + s + 1 by omega,
      Nat.cast_add, Nat.cast_one, pow_succ (2 : ℝ) (10 + s)]
    have hx : (10 : ℝ) ≤ ((10 + s : ℕ) : ℝ) := by norm_cast; omega
    have hm := mul_nonneg (show 0 ≤ ((10 + s : ℕ) : ℝ) - 4 by linarith)
      (sq_nonneg (((10 + s : ℕ) : ℝ)))
    have hs := sq_nonneg (((10 + s : ℕ) : ℝ) - 2)
    nlinarith

/-- No fixed pair of original-generator coefficient streams can have uniformly
bounded full Pareto norms while interpolating every initial segment. -/
theorem fixed_prefix_norms_not_bounded (u v : ℕ → ℝ)
    (hhead : ∀ N k, 0 < k → k ≤ N → twoChannelPrefix N u v k = 1) :
    ¬ ∃ C : ℝ, ∀ N : ℕ,
      paretoInner (twoChannelPrefix N u v) (twoChannelPrefix N u v) ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨r, hr⟩ := exists_nat_gt (max (10 : ℝ) (288 * C))
  have hrR : (10 : ℝ) ≤ (r : ℝ) := (le_max_left _ _).trans hr.le
  have hr10 : 10 ≤ r := by exact_mod_cast hrR
  have hCr : C < (r : ℝ) / 288 := by
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 288)).mpr
    nlinarith [(le_max_right (10 : ℝ) (288 * C)).trans_lt hr]
  have hpoly : (r : ℝ) / 288 ≤ (2 : ℝ) ^ r / (72 * ((r : ℝ) + 1) ^ 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 72 * ((r : ℝ) + 1) ^ 2)).mpr
    have hquad : ((r : ℝ) + 1) ^ 2 ≤ 4 * (r : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((r : ℝ) - 1)]
    calc
      ((r : ℝ) / 288) * (72 * ((r : ℝ) + 1) ^ 2) =
          (r : ℝ) / 4 * ((r : ℝ) + 1) ^ 2 := by ring
      _ ≤ (r : ℝ) / 4 * (4 * (r : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hquad (by positivity)
      _ = (r : ℝ) ^ 3 := by ring
      _ ≤ (2 : ℝ) ^ r := cubic_le_two_pow r hr10
  obtain ⟨n, hn, hinc, hmax⟩ := fixed_prefix_energy_growth u v hhead r (by omega)
  have hh := max_le (hC n) (hC (n - 1))
  linarith

end
end RiemannResearch.RH.Pareto
