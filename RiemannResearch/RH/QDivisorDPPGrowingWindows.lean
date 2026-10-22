/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QDivisorDPPOverlapPower
import RiemannResearch.NumberTheory.GcdWindowMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Quantitative growing-window Hilbert--Schmidt bounds

Source: the user-provided QDPPMovingWindowsResearch20261014.md, Section 7.
The verified absolute overlap and an unconditional gcd-moment estimate give
a bound uniform in projection rank, for 0 < epsilon < 3/4.
The limit consumer retains only its explicit geometric vanishing budget.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QDivisorDPP
open RiemannResearch.NumberTheory

theorem basisKernel_pair_sq_le_rpow (e C : ℝ) (he : e ≤ 1) (hC : 0 ≤ C)
    (hbound : ∀ N i j : ℕ, |basisKernel N i j| ≤ C *
      ((Nat.gcd (i+1) (j+1) : ℝ) ^ 2 /
        (((i+1 : ℕ) : ℝ) * ((j+1 : ℕ) : ℝ))) ^ (1 - e))
    (N x h : ℕ) (p : ℕ × ℕ) (hp : p ∈ distinctWindowPairs x h) :
    basisKernel N (p.1 - 1) (p.2 - 1) ^ 2 ≤
      C ^ 2 / ((x+1 : ℕ) : ℝ) ^ (4 - 4 * e) * (Nat.gcd p.1 p.2 : ℝ) ^ (4 - 4 * e) := by
  have hpw := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
  have hn := Finset.mem_Icc.mp hpw.1
  have hm := Finset.mem_Icc.mp hpw.2
  have hn0 : 0 < p.1 := by omega
  have hm0 : 0 < p.2 := by omega
  have hne : p.1 - 1+1=p.1 := Nat.sub_add_cancel hn0
  have hme : p.2 - 1+1=p.2 := Nat.sub_add_cancel hm0
  let g : ℝ := Nat.gcd p.1 p.2
  let k : ℝ := (p.1 : ℝ)*(p.2 : ℝ)
  let X : ℝ := ((x+1 : ℕ) : ℝ)
  have hg0 : 0 ≤ g := Nat.cast_nonneg _
  have hk : 0 < k := by dsimp [k]; positivity
  have hX : 0 < X := by dsimp [X]; positivity
  have hnR : X ≤ (p.1 : ℝ) := by dsimp [X]; exact_mod_cast hn.1
  have hmR : X ≤ (p.2 : ℝ) := by dsimp [X]; exact_mod_cast hm.1
  have hXk : X ^ 2 ≤ k := by
    dsimp [k]
    nlinarith [mul_nonneg (sub_nonneg.mpr hnR) (sub_nonneg.mpr hmR)]
  have hbe := hbound N (p.1 - 1) (p.2 - 1)
  rw [hne,hme] at hbe
  have hs : basisKernel N (p.1 - 1) (p.2 - 1) ^ 2 ≤
      (C * (g ^ 2/k) ^ (1 - e)) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC (Real.rpow_nonneg (by positivity) _))).mpr hbe
  have ha : 0 ≤ 2-2*e := by linarith
  have heq : (C * (g ^ 2/k) ^ (1 - e)) ^ 2 = C ^ 2 * g ^ (4 - 4 * e)/k ^ (2-2*e) := by
    rw [mul_pow, ←Real.rpow_mul_natCast (by positivity : 0 ≤ g ^ 2/k)]
    norm_num only [Nat.cast_ofNat]
    rw [show (1 - e)*2=2-2*e by ring,
      Real.div_rpow (sq_nonneg _) hk.le,
      ←Real.rpow_natCast_mul hg0 2 (2-2*e)]
    norm_num only [Nat.cast_ofNat]
    rw [show (2:ℝ)*(2-2*e)=4 - 4 * e by ring]
    ring
  have hd : X ^ (4 - 4 * e) ≤ k ^ (2-2*e) := by
    have hh := Real.rpow_le_rpow (sq_nonneg X) hXk ha
    rw [←Real.rpow_natCast_mul hX.le 2 (2-2*e)] at hh
    norm_num only [Nat.cast_ofNat] at hh
    convert hh using 1 <;> congr 1 <;> ring
  calc
    _ ≤ C ^ 2 * g ^ (4 - 4 * e)/k ^ (2-2*e) := hs.trans_eq heq
    _ ≤ C ^ 2 * g ^ (4 - 4 * e)/X ^ (4 - 4 * e) :=
      div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hX _) hd
    _ = _ := by change _ = C ^ 2/X ^ (4 - 4 * e)*g ^ (4 - 4 * e); ring

theorem basisKernel_growing_window_hilbertSchmidt (e : ℝ) (he : 0 < e)
    (hethree : e < 3 / 4) :
    ∃ D : ℝ, 0 < D ∧ ∀ N x h : ℕ, 0 < h →
      (∑ p ∈ distinctWindowPairs x h, basisKernel N (p.1 - 1) (p.2 - 1) ^ 2) ≤
        D * (h : ℝ) ^ (5 - 4 * e) / ((x+1 : ℕ) : ℝ) ^ (4 - 4 * e) := by
  obtain ⟨C,hC,hbound⟩ := basisKernel_abs_le_rpow e he
  have hepos : 0 < 3 - 4 * e := by linarith
  refine ⟨(4 + 4 / (3 - 4 * e)) * C ^ 2, by positivity, ?_⟩
  intro N x h hh
  have hgcd := window_gcd_moment_le_all x h hh (4 - 4 * e) (by linarith)
  calc
    _ ≤ ∑ p ∈ distinctWindowPairs x h,
        C ^ 2 / ((x+1 : ℕ) : ℝ) ^ (4 - 4 * e) * (Nat.gcd p.1 p.2 : ℝ) ^ (4 - 4 * e) := by
      exact Finset.sum_le_sum (fun p hp => basisKernel_pair_sq_le_rpow e C
        (by linarith) hC.le hbound N x h p hp)
    _ = C ^ 2 / ((x+1 : ℕ) : ℝ) ^ (4 - 4 * e) *
        ∑ p ∈ distinctWindowPairs x h, (Nat.gcd p.1 p.2 : ℝ) ^ (4 - 4 * e) := by
      rw [Finset.mul_sum]
    _ ≤ C ^ 2 / ((x+1 : ℕ) : ℝ) ^ (4 - 4 * e) * ((4 + 4 / ((4 - 4 * e)-1)) * (h : ℝ) ^ ((4 - 4 * e)+1)) :=
      mul_le_mul_of_nonneg_left hgcd (by positivity)
    _ = _ := by rw [show (4 - 4 * e)+1=5 - 4 * e by ring, show (4 - 4 * e)-1=3 - 4 * e by ring]; ring

theorem basisKernel_growing_window_energy_tendsto
    (e : ℝ) (he : 0 < e) (hethree : e < 3 / 4)
    (rank x h : ℕ → ℕ) (hh : ∀ n, 0 < h n)
    (hbudget : Tendsto (fun n => (h n : ℝ) ^ (5 - 4 * e) /
      ((x n + 1 : ℕ) : ℝ) ^ (4 - 4 * e)) atTop (𝓝 0)) :
    Tendsto (fun n => ∑ p ∈ distinctWindowPairs (x n) (h n),
      basisKernel (rank n) (p.1 - 1) (p.2 - 1) ^ 2) atTop (𝓝 0) := by
  obtain ⟨D,hD,hbound⟩ := basisKernel_growing_window_hilbertSchmidt e he hethree
  have ht : Tendsto (fun n => D * (h n : ℝ) ^ (5 - 4 * e) /
      ((x n + 1 : ℕ) : ℝ) ^ (4 - 4 * e)) atTop (𝓝 0) := by
    simpa only [mul_div_assoc,mul_zero] using hbudget.const_mul D
  exact squeeze_zero (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (fun n => hbound (rank n) (x n) (h n) (hh n)) ht

end RiemannResearch.RH.QDivisorDPP

namespace RiemannResearch.RH.QDivisorDPP

open RiemannResearch.NumberTheory

/-- The quantitative physical HS sum is exactly the offset-indexed matrix sum. -/
theorem basisKernel_distinct_window_eq_fin (N x h : ℕ) :
    (∑ p ∈ distinctWindowPairs x h,
      basisKernel N (p.1 - 1) (p.2 - 1) ^ 2) =
      ∑ i : Fin h, ∑ j : Fin h,
        if i = j then 0 else basisKernel N (x + (i : ℕ)) (x + (j : ℕ)) ^ 2 := by
  rw [distinctWindowPairs_sum_eq_fin x h
    (fun n m => basisKernel N (n - 1) (m - 1) ^ 2)]
  simp only [Nat.add_sub_cancel]

/-- The physical occupation mean is exactly the finite matrix trace. -/
theorem basisKernel_window_diagonal_eq_fin (N x h : ℕ) :
    (∑ n ∈ natWindow x h, basisKernel N (n - 1) (n - 1)) =
      ∑ i : Fin h, basisKernel N (x + (i : ℕ)) (x + (i : ℕ)) := by
  rw [natWindow_sum_eq_fin x h (fun n => basisKernel N (n - 1) (n - 1))]
  simp only [Nat.add_sub_cancel]

end RiemannResearch.RH.QDivisorDPP
