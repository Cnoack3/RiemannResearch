/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MertensPowerEndpoint
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Cesàro growth at the critical Mertens power

Summation by parts compares absolute displacement mass against a power in
each prefix, using the decreasing physical kernel instead of a pointwise
majorant on the displacement. The discrete comparison is the elementary
Abel transformation (`Finset.sum_range_by_parts` in Mathlib).
-/
noncomputable section
open Filter Set
open scoped BigOperators Topology
namespace RiemannResearch.Analysis

private theorem weighted_prefix_comparison
    (g v c : ℕ → ℝ) (hg : Antitone g) (hg0 : ∀ n, 0 ≤ g n)
    (h : ∀ k, ∑ i ∈ Finset.range k, v i ≤ ∑ i ∈ Finset.range k, c i) (k : ℕ) :
    ∑ i ∈ Finset.range k, g i * v i ≤ ∑ i ∈ Finset.range k, g i * c i := by
  have hh (m : ℕ) : 0 ≤ ∑ i ∈ Finset.range m, (c i - v i) := by
    rw [Finset.sum_sub_distrib]
    exact sub_nonneg.mpr (h m)
  have hp := Finset.sum_range_by_parts g (fun i => c i - v i) k
  simp only [smul_eq_mul] at hp
  rw [← sub_nonneg, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  rw [hp]
  apply sub_nonneg.mpr
  exact (Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr (hg (Nat.le_succ i))) (hh _))).trans
    (mul_nonneg (hg0 _) (hh _))

/-- Growth measured relative to `k^(1+β)` controls the same prefix
relative to the exact sum of the comparison powers. -/
theorem critical_power_prefix_comparison (k : ℕ) (β : ℝ) (hβ : 0 < β) :
    (k : ℝ) ^ (1+β) ≤ (1+β) * ∑ n ∈ Finset.range k, ((n:ℝ)+1)^β := by
  have hm : MonotoneOn (fun x : ℝ => x^β) (Icc 0 (0+(k:ℝ))) :=
    fun _ hx _ _ hxy => Real.rpow_le_rpow hx.1 hxy hβ.le
  have h := hm.integral_le_sum
  simp only [zero_add, Nat.cast_add, Nat.cast_one] at h
  rw [integral_rpow (Or.inl (show -1 < β by linarith)), Real.zero_rpow (by linarith : β+1 ≠ 0),
    sub_zero, add_comm β 1] at h
  simpa only [mul_comm (1+β)] using (div_le_iff₀ (show 0 < 1+β by linarith)).mp h

/-- The displacement may be large on individual sites. It suffices that its
unsigned mass through `k` is `o(k^(1+β))` for the critical `β=a/(1+a)`. -/
theorem power_defect_pairing_tendsto_zero_of_critical_prefix
    (D : ℕ → ℕ → ℝ) (w : ℕ → ℝ) (N : ℕ → ℕ) (a β C : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (hβ1 : β < 1) (hC : 0 ≤ C)
    (hcrit : (1 + a) * β = a) (hN : Tendsto N atTop atTop)
    (hhead : ∀ j n, n+1 ≤ N j → D j n = 0)
    (hdef : ∀ᶠ j : ℕ in atTop, ∀ n : ℕ, |D j n| ≤
      C * min (N j : ℝ) (((n:ℝ)+1) * (N j:ℝ)^(-a)))
    (hw : ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop,
      ∑ n ∈ Finset.range k, |w n| ≤ η * (k:ℝ)^(1+β)) :
    Tendsto (fun j => ∑' n : ℕ, D j n * w n / ((n:ℝ)+1)^2) atTop (𝓝 0) := by
  let L := 1/β + 1/(1-β)
  let x (n : ℕ) := (n:ℝ)+1
  have hx (n : ℕ) : 0 < x n := by dsimp [x]; positivity
  have hL : 0 < L := add_pos (one_div_pos.mpr hβ) (one_div_pos.mpr (sub_pos.mpr hβ1))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hM : 0 < C*L+1 := by linarith only [mul_nonneg hC hL.le]
  let η := ε / (C*L+1)
  have hη : 0 < η := div_pos hε hM
  have hpb : 0 < 1+β := by linarith
  obtain ⟨m,hm⟩ := eventually_atTop.mp (hw (η/(1+β)) (div_pos hη hpb))
  filter_upwards [hdef, hN.eventually (eventually_ge_atTop (m+1))] with j hj hjN
  let T : ℝ := N j
  have hT : 1 ≤ T := by
    change (1:ℝ) ≤ (N j:ℝ)
    exact_mod_cast (show 1 ≤ N j by omega)
  have hT0 := zero_le_one.trans hT
  let A := T^(-a)
  have hA : 0 ≤ A := Real.rpow_nonneg hT0 _
  let g (n : ℕ) := min (A / x n) (T / (x n)^2)
  let v (n : ℕ) := if n < N j then 0 else |w n|
  let K (n : ℕ) := min (A * (x n)^(β-1)) (T * (x n)^(β-2))
  have hg : Antitone g := by
    intro n k hnk
    have hnk' : x n ≤ x k := by dsimp only [x]; exact_mod_cast Nat.add_le_add_right hnk 1
    exact min_le_min (div_le_div_of_nonneg_left hA (hx n) hnk')
      (div_le_div_of_nonneg_left hT0 (sq_pos_of_pos (hx n)) (sq_le_sq' (by linarith only [(hx k), (hx n)]) hnk'))
  have hg0 (n : ℕ) : 0 ≤ g n :=
    le_min (div_nonneg hA (hx n).le) (div_nonneg hT0 (sq_nonneg _))
  have hscale (n : ℕ) : min T (x n*A) / (x n)^2 = g n := by
    rw [min_comm T _, div_eq_mul_inv, min_mul_of_nonneg _ _ (inv_nonneg.mpr (sq_nonneg (x n)))]
    dsimp only [g]
    congr 1
    field_simp [(hx n).ne'] <;> ring
  have hid (n : ℕ) : g n * (x n)^β = K n := by
    dsimp only [g,K]
    rw [min_mul_of_nonneg _ _ (Real.rpow_nonneg (hx n).le _), Real.rpow_sub (hx n) β 1,
      Real.rpow_sub (hx n) β 2, Real.rpow_one, Real.rpow_two]
    congr 1 <;> ring
  have hpre (k : ℕ) : ∑ n ∈ Finset.range k, v n ≤ ∑ n ∈ Finset.range k, η*(x n)^β := by
    rw [← Finset.mul_sum]
    by_cases hk : k < m
    · have hzero : ∑ n ∈ Finset.range k, v n = 0 := by
        apply Finset.sum_eq_zero
        intro n hn
        exact if_pos (show n < N j by have := Finset.mem_range.mp hn; omega)
      rw [hzero]
      exact mul_nonneg hη.le (Finset.sum_nonneg (fun n _ => Real.rpow_nonneg (hx n).le _))
    calc
      _ ≤ ∑ n ∈ Finset.range k, |w n| := Finset.sum_le_sum (fun n _ => by
        dsimp only [v]
        split_ifs <;> first | exact abs_nonneg _ | exact le_rfl)
      _ ≤ (η/(1+β)) * (k:ℝ)^(1+β) := hm k (by omega)
      _ ≤ (η/(1+β)) * ((1+β) * ∑ n ∈ Finset.range k, (x n)^β) :=
        mul_le_mul_of_nonneg_left (critical_power_prefix_comparison k β hβ) (div_nonneg hη.le hpb.le)
      _ = _ := by rw [← mul_assoc, div_mul_cancel₀ _ hpb.ne']
  obtain ⟨hs,hb⟩ := critical_power_kernel_bound T a β hT ha hβ hβ1 hcrit
  have hCη := mul_nonneg hC hη.le
  have hK (n : ℕ) : 0 ≤ K n := le_min
    (mul_nonneg hA (Real.rpow_nonneg (hx n).le _))
    (mul_nonneg hT0 (Real.rpow_nonneg (hx n).le _))
  let b (n : ℕ) := D j n * w n / (x n)^2
  have hpoint (n : ℕ) : ‖b n‖ ≤ C * (g n * v n) := by
    by_cases hn : n < N j
    · simp [b, hhead j n (by omega), v, hn]
    rw [show v n = |w n| by simp [v,hn]]
    dsimp only [b]
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (sq_nonneg (x n))]
    calc
      _ ≤ (C * min T (x n*A)) * |w n| / (x n)^2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hj n) (abs_nonneg _)) (sq_nonneg _)
      _ = C * ((min T (x n*A) / (x n)^2) * |w n|) := by ring
      _ = _ := by rw [hscale]
  have hsum (k : ℕ) : ∑ n ∈ Finset.range k, ‖b n‖ ≤ (C*η)*L := by
    calc
      _ ≤ ∑ n ∈ Finset.range k, C*(g n*v n) := Finset.sum_le_sum (fun n _ => hpoint n)
      _ = C * (∑ n ∈ Finset.range k, g n*v n) := (Finset.mul_sum ..).symm
      _ ≤ C * (∑ n ∈ Finset.range k, g n*(η*(x n)^β)) :=
        mul_le_mul_of_nonneg_left (weighted_prefix_comparison g v _ hg hg0 hpre k) hC
      _ = (C*η) * ∑ n ∈ Finset.range k, K n := by
        simp_rw [mul_left_comm (g _) η, hid]
        rw [← Finset.mul_sum, mul_assoc]
      _ ≤ (C*η)*L := mul_le_mul_of_nonneg_left ((hs.sum_le_tsum _ (fun n _ => hK n)).trans hb) hCη
  have hsabs : Summable (fun n => ‖b n‖) := summable_of_sum_range_le (fun n => norm_nonneg _) hsum
  rw [Real.dist_eq, sub_zero, ← Real.norm_eq_abs]
  calc
    _ ≤ ∑' n, ‖b n‖ := norm_tsum_le_tsum_norm hsabs
    _ ≤ (C*η)*L := hsabs.tsum_le_of_sum_range_le hsum
    _ = η*(C*L) := by ring
    _ < η*(C*L+1) := mul_lt_mul_of_pos_left (by linarith) hη
    _ = ε := div_mul_cancel₀ ε hM.ne'

/-- Pointwise little-o implies little-o for the polynomially normalized
absolute prefix, including the case of constant comparison powers. -/
theorem power_prefix_little_o_of_pointwise (w : ℕ → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (hw : ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, |w n| ≤ η*((n:ℝ)+1)^β)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop, ∑ n ∈ Finset.range k, |w n| ≤ η*(k:ℝ)^(1+β) := by
  have hη2 : 0 < η/2 := half_pos hη
  obtain ⟨m, hm⟩ := eventually_atTop.mp (hw (η/2) hη2)
  let A := ∑ n ∈ Finset.range m, |w n|
  have hp : Tendsto (fun k : ℕ => (k:ℝ)^(1+β)) atTop atTop :=
    (tendsto_rpow_atTop (show 0 < 1+β by linarith)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop m, eventually_ge_atTop (1:ℕ),
    hp.eventually (eventually_ge_atTop (A/(η/2)))] with k hmk hk hmass
  have hkr : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hA := (div_le_iff₀ hη2).mp hmass
  have hpart : ∑ n ∈ Finset.Ico m k, |w n| ≤ (η/2)*(k:ℝ)^(1+β) := by
    calc
      _ ≤ ∑ _n ∈ Finset.Ico m k, (η/2)*(k:ℝ)^β := by
        apply Finset.sum_le_sum
        intro n hn
        have hnr : (n:ℝ)+1 ≤ (k:ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt (Finset.mem_Ico.mp hn).2)
        exact (hm n (Finset.mem_Ico.mp hn).1).trans
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (by positivity : 0 ≤ (n:ℝ)+1) hnr hβ) hη2.le)
      _ ≤ ∑ _n ∈ Finset.range k, (η/2)*(k:ℝ)^β :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun n hn => Finset.mem_range.mpr (Finset.mem_Ico.mp hn).2)
          (fun _ _ _ => mul_nonneg hη2.le (Real.rpow_nonneg hkr.le _))
      _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Real.rpow_add hkr, Real.rpow_one]
        ring
  rw [← Finset.sum_range_add_sum_Ico (fun n => |w n|) hmk]
  change A + _ ≤ _
  linarith only [hA, hpart]

/-- Pointwise little-o at the critical exponent suffices. The parameter `n`
in the series stands for the positive physical site `n+1`. -/
theorem power_defect_pairing_tendsto_zero_of_endpoint_little_o
    (D : ℕ → ℕ → ℝ) (w : ℕ → ℝ) (N : ℕ → ℕ) (a β C : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (hβ1 : β < 1) (hC : 0 ≤ C)
    (hcrit : (1 + a) * β = a) (hN : Tendsto N atTop atTop)
    (hhead : ∀ j n, n+1 ≤ N j → D j n = 0)
    (hdef : ∀ᶠ j : ℕ in atTop, ∀ n : ℕ, |D j n| ≤
      C * min (N j : ℝ) (((n:ℝ)+1) * (N j:ℝ)^(-a)))
    (hw : ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, |w n| ≤ η * ((n:ℝ)+1)^β) :
    Tendsto (fun j => ∑' n : ℕ, D j n * w n / ((n:ℝ)+1)^2) atTop (𝓝 0) :=
  power_defect_pairing_tendsto_zero_of_critical_prefix D w N a β C ha hβ hβ1 hC hcrit
    hN hhead hdef (power_prefix_little_o_of_pointwise w β hβ.le hw)

end RiemannResearch.Analysis
