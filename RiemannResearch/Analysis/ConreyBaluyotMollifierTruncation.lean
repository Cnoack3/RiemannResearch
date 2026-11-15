/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotMellinNormalization
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Exact-floor truncation of the Conrey--Baluyot mollifier

Source: the user's 14 November 2026 density-closure plan, section 5.3,
and Baluyot (2017), Lemma 3.1.1 and the truncations in section 3.4:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320 .

The actual coefficient Dirichlet tail is absolutely convergent for Re(s) >= 0.
The first bound retains the denominator 1 - exp(-1/(2y)).
For each fixed positive cutoff exponent, the floor-cutoff tail is uniformly
bounded by 864 exp(-y^epsilon/4) for large y on the proved coupled sigma strip.
No infinite/finite moment interchange is asserted by these estimates.
-/

open Complex Filter Set
open scoped Topology
noncomputable section
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- The normalized coefficient tail follows from the proved numerator decay. -/
theorem norm_mollifierCoefficient_le_exp {σ y : ℝ} {n : ℕ}
    (hσ : 1 / 2 < σ) (hy : 0 < y) (hW : 1 / 4 ≤ (weight σ y).re) (hn : y ≤ n) :
    ‖mollifierCoefficient σ y n‖ ≤ 288 * Real.exp (-(n : ℝ) / (2 * y)) := by
  have hmu : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]
  have hi := norm_weight_inv_le_of_re_lower_bound hW
  have hw := norm_weight_ratio_le_exp hσ hy hn
  unfold mollifierCoefficient
  rw [div_eq_mul_inv, norm_mul, norm_mul]
  calc
    _ ≤ 1 * ((72 * Real.exp (-(n : ℝ) / (2 * y))) * 4) :=
      mul_le_mul hmu (mul_le_mul hw hi (norm_nonneg _) (by positivity))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _ = _ := by ring

/-- A convergent actual Dirichlet tail, with its geometric denominator retained. -/
theorem mollifier_tail_geometric_bound {σ y : ℝ} {N : ℕ} {s : ℂ}
    (hσ : 1 / 2 < σ) (hy : 0 < y) (hW : 1 / 4 ≤ (weight σ y).re)
    (hN : y ≤ (N : ℝ) + 1) (hs : 0 ≤ s.re) :
    Summable (fun k : ℕ => ‖mollifierCoefficient σ y (N + 1 + k) /
      ((N + 1 + k : ℕ) : ℂ) ^ s‖) ∧
    Summable (fun k : ℕ => mollifierCoefficient σ y (N + 1 + k) /
      ((N + 1 + k : ℕ) : ℂ) ^ s) ∧
    ‖∑' k : ℕ, mollifierCoefficient σ y (N + 1 + k) /
      ((N + 1 + k : ℕ) : ℂ) ^ s‖ ≤
      288 * Real.exp (-((N : ℝ) + 1) / (2 * y)) /
        (1 - Real.exp (-1 / (2 * y))) := by
  let q := Real.exp (-1 / (2 * y))
  let A := 288 * Real.exp (-((N : ℝ) + 1) / (2 * y))
  have hqpos : 0 < q := Real.exp_pos _
  have hqlt : q < 1 := by
    apply Real.exp_lt_one_iff.mpr
    exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  have hq : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_pos hqpos] using hqlt
  have hgeom : HasSum (fun k : ℕ => A * q ^ k) (A / (1 - q)) := by
    simpa only [div_eq_mul_inv] using (hasSum_geometric_of_norm_lt_one hq).mul_left A
  have hb (k : ℕ) : ‖mollifierCoefficient σ y (N + 1 + k) /
      ((N + 1 + k : ℕ) : ℂ) ^ s‖ ≤ A * q ^ k := by
    have hn : y ≤ ((N + 1 + k : ℕ) : ℝ) := by
      push_cast
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have hn1 : (1 : ℝ) ≤ ((N + 1 + k : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ N + 1 + k)
    have hnp : (0 : ℝ) < ((N + 1 + k : ℕ) : ℝ) := by linarith
    have hp : 1 ≤ ‖((N + 1 + k : ℕ) : ℂ) ^ s‖ := by
      have he : ((N + 1 + k : ℕ) : ℂ) = (((N + 1 + k : ℕ) : ℝ) : ℂ) := by simp
      rw [he, Complex.norm_cpow_eq_rpow_re_of_pos hnp]
      exact Real.one_le_rpow hn1 hs
    calc
      _ ≤ ‖mollifierCoefficient σ y (N + 1 + k)‖ := by
        rw [norm_div]
        exact div_le_self (norm_nonneg _) hp
      _ ≤ 288 * Real.exp (-((N + 1 + k : ℕ) : ℝ) / (2 * y)) :=
        norm_mollifierCoefficient_le_exp hσ hy hW hn
      _ = A * q ^ k := by
        dsimp [A, q]
        rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
        congr 2
        push_cast
        ring
  have habs : Summable (fun k : ℕ =>
      ‖mollifierCoefficient σ y (N + 1 + k) / ((N + 1 + k : ℕ) : ℂ) ^ s‖) :=
    hgeom.summable.of_norm_bounded (fun k => by simpa only [norm_norm] using hb k)
  exact ⟨habs, habs.of_norm, tsum_of_norm_bounded hgeom hb⟩

/-- The exact floor cutoff is admissible without replacing it by a real-valued cutoff. -/
theorem mollifier_floor_tail_geometric_bound {σ y ε : ℝ} {s : ℂ}
    (hσ : 1 / 2 < σ) (hy : 1 ≤ y) (hW : 1 / 4 ≤ (weight σ y).re)
    (hε : 0 ≤ ε) (hs : 0 ≤ s.re) :
    let N := ⌊y ^ (1 + ε)⌋₊
    Summable (fun k : ℕ => ‖mollifierCoefficient σ y (N + 1 + k) /
      ((N + 1 + k : ℕ) : ℂ) ^ s‖) ∧
    Summable (fun k : ℕ => mollifierCoefficient σ y (N + 1 + k) /
      ((N + 1 + k : ℕ) : ℂ) ^ s) ∧
    ‖∑' k : ℕ, mollifierCoefficient σ y (N + 1 + k) /
      ((N + 1 + k : ℕ) : ℂ) ^ s‖ ≤
      288 * Real.exp (-((N : ℝ) + 1) / (2 * y)) /
        (1 - Real.exp (-1 / (2 * y))) := by
  dsimp only
  apply mollifier_tail_geometric_bound hσ (by linarith) hW _ hs
  have hp : y ≤ y ^ (1 + ε) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hy
      (show (1 : ℝ) ≤ 1 + ε by linarith)
  exact hp.trans (Nat.lt_floor_add_one (y ^ (1 + ε))).le

/-- The reciprocal geometric denominator grows at most linearly in y. -/
theorem geometric_denominator_inv_le {y : ℝ} (hy : 1 ≤ y) :
    (1 - Real.exp (-1 / (2 * y)))⁻¹ ≤ 3 * y := by
  have hy0 : 0 < y := by linarith
  let x := 1 / (2 * y)
  have hx : 0 < x := by dsimp [x]; positivity
  have hd : 0 < 1 - Real.exp (-x) := by
    have hh := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx)
    linarith
  have hb : 1 + x ≤ Real.exp x := by simpa only [add_comm] using Real.add_one_le_exp x
  have hm := mul_le_mul_of_nonneg_right hb (show 0 ≤ 2 * y * Real.exp (-x) by positivity)
  have he : Real.exp x * (2 * y * Real.exp (-x)) = 2 * y := by
    rw [mul_left_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have he' : (1 + x) * (2 * y * Real.exp (-x)) = (2 * y + 1) * Real.exp (-x) := by
    dsimp [x]
    field_simp
    <;> ring
  rw [he, he'] at hm
  have hi : (1 - Real.exp (-x))⁻¹ ≤ 1 + 2 * y := by
    rw [← one_div]
    apply (div_le_iff₀ hd).mpr
    nlinarith only [hm]
  have heq : -x = -1 / (2 * y) := by dsimp [x]; ring
  rw [heq] at hi
  exact hi.trans (by linarith)

/-- Polynomial prefactors are absorbed only after choosing a threshold for fixed epsilon. -/
theorem exists_stretched_tail_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ Y : ℝ, 1 ≤ Y ∧ ∀ y : ℝ, Y ≤ y → ∀ σ : ℝ,
      1 / 2 < σ → 1 / 4 ≤ (weight σ y).re → ∀ s : ℂ, 0 ≤ s.re →
      let N := ⌊y ^ (1 + ε)⌋₊
      Summable (fun k : ℕ => ‖mollifierCoefficient σ y (N + 1 + k) /
        ((N + 1 + k : ℕ) : ℂ) ^ s‖) ∧
      Summable (fun k : ℕ => mollifierCoefficient σ y (N + 1 + k) /
        ((N + 1 + k : ℕ) : ℂ) ^ s) ∧
      ‖∑' k : ℕ, mollifierCoefficient σ y (N + 1 + k) /
        ((N + 1 + k : ℕ) : ℂ) ^ s‖ ≤ 864 * Real.exp (-(y ^ ε) / 4) := by
  have hlog := (isLittleO_log_rpow_atTop hε).bound (by norm_num : (0 : ℝ) < 1 / 4)
  obtain ⟨Y, hY⟩ := eventually_atTop.mp hlog
  refine ⟨max 1 Y, le_max_left _ _, ?_⟩
  intro y hy σ hσ hW s hs
  have hy1 : 1 ≤ y := (le_max_left _ _).trans hy
  have hy0 : 0 < y := by linarith
  have hl := hY y ((le_max_right _ _).trans hy)
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hy1),
    abs_of_nonneg (Real.rpow_nonneg hy0.le _)] at hl
  let N := ⌊y ^ (1 + ε)⌋₊
  obtain ⟨habs, hsum, hb⟩ := mollifier_floor_tail_geometric_bound hσ hy1 hW hε.le hs
  refine ⟨habs, hsum, hb.trans ?_⟩
  have hf : y ^ (1 + ε) ≤ (N : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  have hp : y ^ (1 + ε) = y * y ^ ε := by rw [Real.rpow_add hy0, Real.rpow_one]
  have hpower : -((N : ℝ) + 1) / (2 * y) ≤ -(y ^ ε) / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * y)).mpr
    rw [hp] at hf
    nlinarith only [hf]
  have hden := geometric_denominator_inv_le hy1
  have he : y * Real.exp (-(y ^ ε) / 2) ≤ Real.exp (-(y ^ ε) / 4) := by
    calc
      _ = Real.exp (Real.log y - (y ^ ε) / 2) := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hy0]
        congr 1
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ (288 * Real.exp (-(y ^ ε) / 2)) * (3 * y) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hpower) (by norm_num))
        hden (inv_nonneg.mpr (by
          have ht := Real.exp_lt_one_iff.mpr
            (div_neg_of_neg_of_pos (by norm_num : (-1 : ℝ) < 0) (by positivity : 0 < 2 * y))
          linarith)) (by positivity)
    _ = 864 * (y * Real.exp (-(y ^ ε) / 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by norm_num)

/-- Uniform truncation for the actual normalized coefficients on the proved coupled strip. -/
theorem exists_uniform_mollifier_truncation {ε : ℝ} (hε : 0 < ε) :
    ∃ ε₀ Y₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 / 4 ∧ 1 < Y₀ ∧
      Real.exp (1 / ε₀) ≤ Y₀ ∧ ∀ y : ℝ, Y₀ ≤ y → ∀ σ : ℝ,
      1 / 2 + 1 / Real.log y ≤ σ → σ ≤ 1 / 2 + ε₀ → ∀ s : ℂ, 0 ≤ s.re →
      let N := ⌊y ^ (1 + ε)⌋₊
      Summable (fun k : ℕ => ‖mollifierCoefficient σ y (N + 1 + k) /
        ((N + 1 + k : ℕ) : ℂ) ^ s‖) ∧
      Summable (fun k : ℕ => mollifierCoefficient σ y (N + 1 + k) /
        ((N + 1 + k : ℕ) : ℂ) ^ s) ∧
      ‖∑' k : ℕ, mollifierCoefficient σ y (N + 1 + k) /
        ((N + 1 + k : ℕ) : ℂ) ^ s‖ ≤ 864 * Real.exp (-(y ^ ε) / 4) := by
  obtain ⟨ε₀, Y₀, hε₀, hεhi, hY₀, hexp, _, hnorm⟩ := exists_uniform_weight_normalization
  obtain ⟨Y, _, htail⟩ := exists_stretched_tail_bound hε
  refine ⟨ε₀, max Y₀ Y, hε₀, hεhi, hY₀.trans_le (le_max_left _ _),
    hexp.trans (le_max_left _ _), ?_⟩
  intro y hy σ hσ hσhi s hs
  have hy₀ : Y₀ ≤ y := (le_max_left _ _).trans hy
  have hy1 : 1 < y := hY₀.trans_le hy₀
  have hσ' : 1 / 2 < σ := by
    have := one_div_pos.mpr (Real.log_pos hy1)
    linarith
  exact htail y ((le_max_right _ _).trans hy) σ hσ' (hnorm y hy₀ σ hσ hσhi) s hs

end RiemannResearch.Analysis.ConreyBaluyot
