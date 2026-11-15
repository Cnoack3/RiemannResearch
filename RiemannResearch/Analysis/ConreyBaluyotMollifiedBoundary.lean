/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotMellinNormalization
import RiemannResearch.Analysis.ConreyBaluyotMellinWeight
import RiemannResearch.Analysis.ComplexLogSecondMoment
import RiemannResearch.Analysis.PSeriesTail
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The actual Conrey--Baluyot mollified zeta and its vertical boundaries

Source for the upper moment and right normalization: Baluyot (2017),
*On the Zeros of Riemann's Zeta-function*, equations (3.2.1) and
(3.2.4)--(3.2.9):
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320 .

The mollifier and its complex argument are kept distinct. Uniform
coefficient bounds give right-half-plane exponential normalization.
On a zero-free left segment the actual upper second moment suffices for
the logarithmic integral. The moment and horizontal estimates are separate.
-/

noncomputable section
open Complex MeasureTheory Set
open scoped BigOperators

namespace RiemannResearch.Analysis.ConreyBaluyot

/-- The source's direct product with the fixed-parameter nonstandard mollifier. -/
def mollifiedZeta (σ y ε : ℝ) (s : ℂ) : ℂ :=
  riemannZeta s * nonstandardMollifier σ y ε s

theorem analyticAt_nonstandardMollifier (σ y ε : ℝ) (s : ℂ) :
    AnalyticAt ℂ (nonstandardMollifier σ y ε) s := by
  have hform : nonstandardMollifier σ y ε =
      fun u => ∑ n ∈ Finset.Icc 1 ⌊y ^ (1 + ε)⌋₊,
        mollifierCoefficient σ y n * Complex.exp (-(Complex.log (n : ℂ) * u)) := by
    funext u
    unfold nonstandardMollifier
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by
      have h₁ := (Finset.mem_Icc.mp hn).1
      omega
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn0), Complex.exp_neg, div_eq_mul_inv]
  rw [hform]
  fun_prop

theorem analyticAt_mollifiedZeta (σ y ε : ℝ) {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ (mollifiedZeta σ y ε) s :=
  (analyticAt_riemannZeta hs).mul (analyticAt_nonstandardMollifier σ y ε s)

/-- Exact first-coefficient subtraction with the floor cutoff retained. -/
theorem nonstandardMollifier_sub_one_eq_tail {σ y ε : ℝ}
    (hN : 1 ≤ ⌊y ^ (1 + ε)⌋₊) (hfirst : mollifierCoefficient σ y 1 = 1) (s : ℂ) :
    nonstandardMollifier σ y ε s - 1 =
      ∑ n ∈ Finset.Icc 2 ⌊y ^ (1 + ε)⌋₊, mollifierCoefficient σ y n / (n : ℂ) ^ s := by
  let N := ⌊y ^ (1 + ε)⌋₊
  have hset : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  unfold nonstandardMollifier
  change (∑ n ∈ Finset.Icc 1 N, mollifierCoefficient σ y n / (n : ℂ) ^ s) - 1 = _
  rw [hset, Finset.sum_insert (by simp), hfirst, Nat.cast_one, Complex.one_cpow, div_one]
  ring

private theorem norm_one_div_nat_cpow_le {s : ℂ} (hs : 2 ≤ s.re)
    {n : ℕ} (hn : 2 ≤ n) :
    ‖(1 : ℂ) / (n : ℂ) ^ s‖ ≤ (2 : ℝ) ^ (2 - s.re) * (n : ℝ) ^ (-(2 : ℝ)) := by
  have hn0 : 0 < n := by omega
  have hnℝ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hn0, one_div,
    ← Real.rpow_neg hnℝ.le, show -s.re = (2 - s.re) + -(2 : ℝ) by ring,
    Real.rpow_add hnℝ]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hn) (by linarith))
    (Real.rpow_nonneg hnℝ.le _)

private theorem tsum_rpow_neg_two_tail_le_one :
    (∑' k : ℕ, ((k + 2 : ℕ) : ℝ) ^ (-(2 : ℝ))) ≤ 1 := by
  have h := Real.tsum_nat_rpow_tail_le (p := (2 : ℝ)) (by norm_num) (N := 1) (by norm_num)
  norm_num [Nat.add_assoc] at h ⊢
  exact h

private theorem norm_riemannZeta_sub_one_le_dyadic {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ (2 : ℝ) ^ (2 - s.re) := by
  let f : ℕ → ℂ := fun n => (1 : ℂ) / (n : ℂ) ^ s
  have hs' : 1 < s.re := by linarith
  have hf : Summable f := Complex.summable_one_div_nat_cpow.mpr hs'
  have htail : Summable (fun k : ℕ => f (k + 2)) := (summable_nat_add_iff 2).mpr hf
  have hz : riemannZeta s = ∑' n : ℕ, f (n + 1) := by
    simpa [f, Nat.cast_add] using zeta_eq_tsum_one_div_nat_add_one_cpow hs'
  have hf1 : f 1 = 1 := by simp [f]
  have he : riemannZeta s - 1 = ∑' n : ℕ, f (n + 2) := by
    rw [hz, ((summable_nat_add_iff 1).mpr hf).tsum_eq_zero_add]
    simp [hf1, Nat.add_assoc]
  have hR : Summable (fun k : ℕ => ((k + 2 : ℕ) : ℝ) ^ (-(2 : ℝ))) :=
    (summable_nat_add_iff 2).mpr (Real.summable_nat_rpow.mpr (by norm_num))
  let r : ℝ := (2 : ℝ) ^ (2 - s.re)
  rw [he]
  calc
    _ ≤ ∑' k : ℕ, ‖f (k + 2)‖ := norm_tsum_le_tsum_norm htail.norm
    _ ≤ ∑' k : ℕ, r * ((k + 2 : ℕ) : ℝ) ^ (-(2 : ℝ)) :=
      htail.norm.tsum_le_tsum
        (fun k => norm_one_div_nat_cpow_le hs (by omega : 2 ≤ k + 2)) (hR.mul_left r)
    _ = r * ∑' k : ℕ, ((k + 2 : ℕ) : ℝ) ^ (-(2 : ℝ)) := by rw [tsum_mul_left]
    _ ≤ r := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left tsum_rpow_neg_two_tail_le_one
        (show 0 ≤ r by dsimp [r]; positivity)

private theorem sum_rpow_neg_two_le_two (S : Finset ℕ) :
    (∑ n ∈ S, (n : ℝ) ^ (-(2 : ℝ))) ≤ 2 := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-(2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have he := hs.sum_add_tsum_nat_add 2
  have ht := tsum_rpow_neg_two_tail_le_one
  have htotal : (∑' n : ℕ, (n : ℝ) ^ (-(2 : ℝ))) ≤ 2 := by
    norm_num [Finset.sum_range_succ, Real.zero_rpow] at he ht ⊢
    linarith only [he, ht]
  exact (hs.sum_le_tsum S (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)).trans htotal

theorem norm_nonstandardMollifier_sub_one_le_dyadic {σ y ε C : ℝ}
    (hC : 0 ≤ C) (hN : 1 ≤ ⌊y ^ (1 + ε)⌋₊) (hfirst : mollifierCoefficient σ y 1 = 1)
    (hcoef : ∀ n : ℕ, 0 < n → ‖mollifierCoefficient σ y n‖ ≤ C)
    {s : ℂ} (hs : 2 ≤ s.re) :
    ‖nonstandardMollifier σ y ε s - 1‖ ≤ 2 * C * (2 : ℝ) ^ (2 - s.re) := by
  rw [nonstandardMollifier_sub_one_eq_tail hN hfirst]
  let S := Finset.Icc 2 ⌊y ^ (1 + ε)⌋₊
  let r : ℝ := (2 : ℝ) ^ (2 - s.re)
  calc
    _ ≤ ∑ n ∈ S, ‖mollifierCoefficient σ y n / (n : ℂ) ^ s‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, (C * r) * (n : ℝ) ^ (-(2 : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn2 := (Finset.mem_Icc.mp hn).1
      have hn0 : 0 < n := by omega
      rw [show mollifierCoefficient σ y n / (n : ℂ) ^ s =
        mollifierCoefficient σ y n * ((1 : ℂ) / (n : ℂ) ^ s) by ring, norm_mul]
      calc
        _ ≤ C * (r * (n : ℝ) ^ (-(2 : ℝ))) :=
          mul_le_mul (hcoef n hn0) (norm_one_div_nat_cpow_le hs hn2) (norm_nonneg _) hC
        _ = _ := by ring
    _ = (C * r) * ∑ n ∈ S, (n : ℝ) ^ (-(2 : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ (C * r) * 2 := mul_le_mul_of_nonneg_left (sum_rpow_neg_two_le_two S)
      (mul_nonneg hC (by dsimp [r]; positivity))
    _ = _ := by dsimp [r]; ring

/-- Uniform in the finite cutoff and ordinate once the coefficients
have a common bound and are normalized at one. -/
theorem norm_mollifiedZeta_sub_one_le_dyadic {σ y ε C : ℝ}
    (hC : 0 ≤ C) (hN : 1 ≤ ⌊y ^ (1 + ε)⌋₊) (hfirst : mollifierCoefficient σ y 1 = 1)
    (hcoef : ∀ n : ℕ, 0 < n → ‖mollifierCoefficient σ y n‖ ≤ C)
    {s : ℂ} (hs : 2 ≤ s.re) :
    ‖mollifiedZeta σ y ε s - 1‖ ≤ (1 + 4 * C) * (2 : ℝ) ^ (2 - s.re) := by
  let r : ℝ := (2 : ℝ) ^ (2 - s.re)
  have hz := norm_riemannZeta_sub_one_le_dyadic hs
  have hr : r ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hz₂ : ‖riemannZeta s‖ ≤ 2 := by
    have hh := norm_le_norm_sub_add (riemannZeta s) (1 : ℂ)
    rw [norm_one] at hh
    exact hh.trans (by linarith [show ‖riemannZeta s - 1‖ ≤ r from hz])
  have hm := norm_nonstandardMollifier_sub_one_le_dyadic hC hN hfirst hcoef hs
  unfold mollifiedZeta
  rw [show riemannZeta s * nonstandardMollifier σ y ε s - 1 =
    (riemannZeta s - 1) + riemannZeta s * (nonstandardMollifier σ y ε s - 1) by ring]
  calc
    _ ≤ ‖riemannZeta s - 1‖ +
        ‖riemannZeta s‖ * ‖nonstandardMollifier σ y ε s - 1‖ := by
        rw [← norm_mul]
        exact norm_add_le _ _
    _ ≤ r + 2 * (2 * C * r) :=
      add_le_add hz (mul_le_mul hz₂ hm (norm_nonneg _) (by norm_num))
    _ = _ := by dsimp [r]; ring

/-- The actual coefficients give a uniform right-half-plane normalization
on the coupled logarithmic strip. The constants are fixed before y and σ. -/
theorem exists_uniform_mollifiedZeta_right_decay {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ η Y D : ℝ, 0 < η ∧ η < 1 / 4 ∧ 1 < Y ∧ 0 < D ∧
      ∀ y : ℝ, Y ≤ y → ∀ σ : ℝ, 1 / 2 + 1 / Real.log y ≤ σ → σ ≤ 1 / 2 + η →
        ∀ s : ℂ, 2 ≤ s.re →
          ‖mollifiedZeta σ y ε s - 1‖ ≤ D * (2 : ℝ) ^ (2 - s.re) := by
  obtain ⟨η, Y, K, hη, hη', hY, _, hK, hcoeff⟩ :=
    exists_uniform_mollifier_coefficient_bounds
  refine ⟨η, Y, 1 + 4 * (4 * K), hη, hη', hY, by positivity, ?_⟩
  intro y hy σ hσ hση s hs
  obtain ⟨_, _, hfirst, hcoef, _⟩ := hcoeff y hy σ hσ hση
  have hy1 : 1 ≤ y := hY.le.trans hy
  have hpow : 1 ≤ y ^ (1 + ε) := Real.one_le_rpow hy1 (by linarith)
  have hN : 1 ≤ ⌊y ^ (1 + ε)⌋₊ := by
    by_contra hn
    have hz : ⌊y ^ (1 + ε)⌋₊ = 0 := by omega
    have hlt := Nat.lt_floor_add_one (y ^ (1 + ε))
    simp [hz] at hlt
    linarith
  exact norm_mollifiedZeta_sub_one_le_dyadic (by positivity) hN hfirst hcoef hs

/-- A fixed right line works uniformly over the actual source strip.
In the half-plane to its right the product has real part at least one half. -/
theorem exists_uniform_mollifiedZeta_right_real_lower {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ η Y b : ℝ, 0 < η ∧ η < 1 / 4 ∧ 1 < Y ∧ 2 ≤ b ∧
      ∀ y : ℝ, Y ≤ y → ∀ σ : ℝ, 1 / 2 + 1 / Real.log y ≤ σ → σ ≤ 1 / 2 + η →
        ∀ s : ℂ, b ≤ s.re → 1 / 2 ≤ (mollifiedZeta σ y ε s).re := by
  obtain ⟨η, Y, D, hη, hη', hY, hD, hbound⟩ := exists_uniform_mollifiedZeta_right_decay hε
  let b := max 2 (2 + Real.log (2 * D) / Real.log 2)
  have hb : 2 ≤ b := le_max_left _ _
  refine ⟨η, Y, b, hη, hη', hY, hb, ?_⟩
  intro y hy σ hσ hση s hs
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsb : 2 + Real.log (2 * D) / Real.log 2 ≤ s.re := (le_max_right _ _).trans hs
  have hmul := mul_le_mul_of_nonneg_left hsb hlog.le
  have hmulEq : Real.log 2 * (2 + Real.log (2 * D) / Real.log 2) =
      2 * Real.log 2 + Real.log (2 * D) := by
    field_simp [hlog.ne']
  rw [hmulEq] at hmul
  have he : Real.log 2 * (2 - s.re) ≤ -Real.log (2 * D) := by linarith
  have hhalf : D * (2 : ℝ) ^ (2 - s.re) ≤ 1 / 2 := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      _ ≤ D * Real.exp (-Real.log (2 * D)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hD.le
      _ = _ := by
        rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 2 * D)]
        field_simp [hD.ne']
  have hnorm := (hbound y hy σ hσ hση s (hb.trans hs)).trans hhalf
  have hre := Complex.re_le_norm (1 - mollifiedZeta σ y ε s)
  rw [norm_sub_rev] at hre
  simp only [Complex.sub_re, Complex.one_re] at hre
  linarith

/-- The one-sided uncentered moment bounds the actual direct-product
left logarithmic integral. The zero-free segment is the Littlewood domain
condition. Both interval integrability proofs follow from analyticity. -/
theorem integral_log_mollifiedZeta_le_of_moment (σ y ε α : ℝ) {H T E : ℝ}
    (hH : 0 < H) (hHT : H ≤ T)
    (hne : ∀ t ∈ Icc H T, mollifiedZeta σ y ε ((α : ℂ) + (t : ℂ) * I) ≠ 0)
    (hm : (∫ t in H..T, ‖mollifiedZeta σ y ε ((α : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ T - H + E) :
    (∫ t in H..T, Real.log ‖mollifiedZeta σ y ε ((α : ℂ) + (t : ℂ) * I)‖) ≤ E / 2 := by
  let f : ℝ → ℂ := fun t => mollifiedZeta σ y ε ((α : ℂ) + (t : ℂ) * I)
  have hf : ContinuousOn f (Icc H T) := by
    intro t ht
    have ht0 : 0 < t := hH.trans_le ht.1
    have hs : (α : ℂ) + (t : ℂ) * I ≠ 1 := by
      intro he
      have hi := congrArg Complex.im he
      simp at hi
      linarith
    have hpt : ContinuousAt (fun v : ℝ => (α : ℂ) + (v : ℂ) * I) t := by fun_prop
    have hcomp : ContinuousAt
        (mollifiedZeta σ y ε ∘ (fun v : ℝ => (α : ℂ) + (v : ℂ) * I)) t :=
      ContinuousAt.comp (g := mollifiedZeta σ y ε)
        (f := fun v : ℝ => (α : ℂ) + (v : ℂ) * I)
        (analyticAt_mollifiedZeta σ y ε hs).continuousAt hpt
    exact hcomp.continuousWithinAt
  have hsq : ContinuousOn (fun t => ‖f t‖ ^ 2) (uIcc H T) := by
    rw [uIcc_of_le hHT]
    exact hf.norm.pow 2
  have hlog : ContinuousOn (fun t => Real.log ‖f t‖) (uIcc H T) := by
    rw [uIcc_of_le hHT]
    intro t ht
    exact (hf t ht).norm.log (norm_ne_zero_iff.mpr (hne t ht))
  exact Complex.integral_log_norm_le_of_second_moment hHT hne
    hlog.intervalIntegrable hsq.intervalIntegrable hm

/-- Sharper logarithmic conversion of the actual uncentered moment bound.
For positive interval length and nonnegative excess E, this improves E/2 to
length * log(1 + E/length) / 2. The moment estimate itself remains a premise. -/
theorem integral_log_mollifiedZeta_le_log_of_moment (σ y ε α : ℝ) {H T E : ℝ}
    (hH : 0 < H) (hHT : H < T) (hE : 0 ≤ E)
    (hne : ∀ t ∈ Icc H T, mollifiedZeta σ y ε ((α : ℂ) + (t : ℂ) * I) ≠ 0)
    (hm : (∫ t in H..T, ‖mollifiedZeta σ y ε ((α : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ T - H + E) :
    (∫ t in H..T, Real.log ‖mollifiedZeta σ y ε ((α : ℂ) + (t : ℂ) * I)‖) ≤
        (T - H) * Real.log (1 + E / (T - H)) / 2 ∧
      (T - H) * Real.log (1 + E / (T - H)) / 2 ≤ E / 2 := by
  let f : ℝ → ℂ := fun t => mollifiedZeta σ y ε ((α : ℂ) + (t : ℂ) * I)
  have hf : ContinuousOn f (Icc H T) := by
    intro t ht
    have ht0 : 0 < t := hH.trans_le ht.1
    have hs : (α : ℂ) + (t : ℂ) * I ≠ 1 := by
      intro he
      have hi := congrArg Complex.im he
      simp at hi
      linarith
    have hpt : ContinuousAt (fun v : ℝ => (α : ℂ) + (v : ℂ) * I) t := by fun_prop
    have hcomp : ContinuousAt
        (mollifiedZeta σ y ε ∘ (fun v : ℝ => (α : ℂ) + (v : ℂ) * I)) t :=
      ContinuousAt.comp (g := mollifiedZeta σ y ε)
        (f := fun v : ℝ => (α : ℂ) + (v : ℂ) * I)
        (analyticAt_mollifiedZeta σ y ε hs).continuousAt hpt
    exact hcomp.continuousWithinAt
  have hsq : ContinuousOn (fun t => ‖f t‖ ^ 2) (uIcc H T) := by
    rw [uIcc_of_le hHT.le]
    exact hf.norm.pow 2
  have hlog : ContinuousOn (fun t => Real.log ‖f t‖) (uIcc H T) := by
    rw [uIcc_of_le hHT.le]
    intro t ht
    exact (hf t ht).norm.log (norm_ne_zero_iff.mpr (hne t ht))
  have hlen : 0 < T - H := sub_pos.mpr hHT
  have hA : 0 < 1 + E / (T - H) := by positivity
  have hmul : (T - H) * (1 + E / (T - H)) = T - H + E := by
    field_simp [ne_of_gt hlen]
    <;> ring
  refine ⟨?_, ?_⟩
  · apply Complex.integral_log_norm_le_of_mean_square_bound hHT.le hA hne
      hlog.intervalIntegrable hsq.intervalIntegrable
    rw [hmul]
    exact hm
  · have hh := Real.log_le_sub_one_of_pos hA
    have hh' := mul_le_mul_of_nonneg_left hh hlen.le
    have he : (T - H) * ((1 + E / (T - H)) - 1) = E := by
      field_simp [ne_of_gt hlen]
      <;> ring
    rw [he] at hh'
    linarith

end RiemannResearch.Analysis.ConreyBaluyot
