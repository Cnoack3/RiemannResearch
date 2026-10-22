/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Elementary decay of finite Euler products below exponent one

Source: user-provided two-stage sieve obstruction argument,
`RH/TwoStageSieveObstructionResearch20261020.md`, Section 4, for the required
decay statement. The proof here uses exponent amplification: compare the
factors at `σ` with powers of the factors at a fixed `τ > σ`, then use the
positive finite Euler expansion and its first `H` terms. This removes the
need for reduced-residue asymptotics, prime reciprocal divergence, or PNT.
The finite Euler expansion is Mathlib's
`EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric`.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace RiemannResearch.Analysis

/-- The finite Euler product at a positive real exponent. -/
def primePowerEulerProduct (σ : ℝ) (H : ℕ) : ℝ :=
  ∏ p ∈ H.succ.primesBelow, (1 - (p : ℝ) ^ (-σ))

private def natNegPower (σ : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-σ)
  map_one' := by simp
  map_mul' m n := by
    simp only [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

private theorem prime_neg_rpow_lt_one (σ : ℝ) (hσ : 0 < σ)
    (p : ℕ) (hp : p.Prime) : (p : ℝ) ^ (-σ) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)

theorem primePowerEulerProduct_pos (σ : ℝ) (hσ : 0 < σ) (H : ℕ) :
    0 < primePowerEulerProduct σ H := by
  apply Finset.prod_pos
  intro p hp
  have hp' : p.Prime := (Nat.mem_primesBelow.mp hp).2
  exact sub_pos.mpr (prime_neg_rpow_lt_one σ hσ p hp')

private theorem factored_mem_of_le (H n : ℕ) (hn : 1 ≤ n) (hH : n ≤ H) :
    n ∈ Nat.factoredNumbers (Finset.range (H+1)) := by
  rw [Nat.mem_factoredNumbers_iff_forall_le]
  refine ⟨by omega, ?_⟩
  intro p hp _ _
  simp only [Finset.mem_range]
  omega

/-- Every partial power sum is bounded by the positive finite Euler expansion.
The only infinite sum is over integers supported on a fixed finite set of primes. -/
theorem sum_Icc_neg_rpow_le_euler_inv (σ : ℝ) (hσ : 0 < σ) (H : ℕ) :
    (∑ n ∈ Finset.Icc 1 H, (n : ℝ) ^ (-σ)) ≤
      (primePowerEulerProduct σ H)⁻¹ := by
  classical
  let f := natNegPower σ
  have hf : ∀ {p : ℕ}, p.Prime → ‖f p‖ < 1 := by
    intro p hp
    change ‖(p : ℝ) ^ (-σ)‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact prime_neg_rpow_lt_one σ hσ p hp
  have hs := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := f) hf (Finset.range (H+1))
  let t := (Finset.Icc 1 H).subtype
    (fun n => n ∈ Nat.factoredNumbers (Finset.range (H+1)))
  have ht : (∑ n ∈ t, f n.val) = ∑ n ∈ Finset.Icc 1 H, (n : ℝ) ^ (-σ) := by
    dsimp only [t]
    rw [Finset.sum_subtype_eq_sum_filter]
    have he : (Finset.Icc 1 H).filter
        (fun n => n ∈ Nat.factoredNumbers (Finset.range (H+1))) = Finset.Icc 1 H := by
      apply Finset.filter_eq_self.mpr
      intro n hn
      obtain ⟨hn1, hnH⟩ := Finset.mem_Icc.mp hn
      exact factored_mem_of_le H n hn1 hnH
    rw [he]
    rfl
  have hb := hs.2.summable.sum_le_tsum t (fun n _ =>
    Real.rpow_nonneg (Nat.cast_nonneg n.val) (-σ))
  change (∑ n ∈ t, f n.val) ≤
    ∑' n : Nat.factoredNumbers (Finset.range (H+1)), f n.val at hb
  rw [ht, hs.2.tsum_eq] at hb
  simpa [primePowerEulerProduct, Nat.primesBelow, Nat.succ_eq_add_one,
    Finset.prod_inv_distrib, f, natNegPower] using hb

/-- A coarse Euler bound suffices: no asymptotic power sum or PNT is used. -/
theorem primePowerEulerProduct_le_rpow (σ : ℝ) (hσ : 0 < σ)
    (H : ℕ) (hH : 1 ≤ H) :
    primePowerEulerProduct σ H ≤ (H : ℝ) ^ (σ-1) := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hs : (H : ℝ) * (H : ℝ) ^ (-σ) ≤
      ∑ n ∈ Finset.Icc 1 H, (n : ℝ) ^ (-σ) := by
    have h := Finset.sum_le_sum (s := Finset.Icc 1 H)
      (f := fun _ : ℕ => (H : ℝ) ^ (-σ)) (g := fun n : ℕ => (n : ℝ) ^ (-σ))
      (fun n hn => Real.rpow_le_rpow_of_nonpos
        (by exact_mod_cast (show 0 < n from lt_of_lt_of_le Nat.zero_lt_one
          (Finset.mem_Icc.mp hn).1))
        (by exact_mod_cast (Finset.mem_Icc.mp hn).2) (by linarith))
    simpa using h
  have hb := hs.trans (sum_Icc_neg_rpow_le_euler_inv σ hσ H)
  have hpos := primePowerEulerProduct_pos σ hσ H
  have hh : (H : ℝ) ^ (1-σ) ≤ (primePowerEulerProduct σ H)⁻¹ := by
    simpa [sub_eq_add_neg, Real.rpow_add hHR, Real.rpow_one] using hb
  have he : ((H : ℝ) ^ (1-σ))⁻¹ = (H : ℝ) ^ (σ-1) := by
    rw [← Real.rpow_neg (le_of_lt hHR)]
    congr 1
    ring
  rw [← he]
  exact (le_inv_comm₀ (Real.rpow_pos_of_pos hHR _) hpos).mp hh

private def primePowerFactor (σ : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then 1 - (n : ℝ)^(-σ) else 1

private theorem primePowerFactor_pos (σ : ℝ) (hσ : 0 < σ) (n : ℕ) :
    0 < primePowerFactor σ n := by
  unfold primePowerFactor
  split_ifs with hn
  · exact sub_pos.mpr (prime_neg_rpow_lt_one σ hσ n hn)
  · norm_num

private theorem primePowerEulerProduct_eq_range (σ : ℝ) (H : ℕ) :
    primePowerEulerProduct σ H =
      ∏ n ∈ Finset.range (H+1), primePowerFactor σ n := by
  simp only [primePowerEulerProduct, Nat.primesBelow, Finset.prod_filter,
    primePowerFactor, Nat.succ_eq_add_one]

/-- Exponent separation makes each sufficiently late factor dominate any fixed
natural power of the factor at the larger exponent. -/
private theorem eventually_primePowerFactor_le_pow (σ τ : ℝ)
    (hσ : 0 < σ) (hστ : σ < τ) (m : ℕ) :
    ∀ᶠ n : ℕ in atTop, primePowerFactor σ n ≤ primePowerFactor τ n ^ m := by
  have hτ : 0 < τ := hσ.trans hστ
  have ht : Tendsto (fun n : ℕ => (n : ℝ)^(τ-σ)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < τ-σ)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop (m : ℝ)), eventually_ge_atTop 1]
    with n hn hn1
  by_cases hp : n.Prime
  · have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hpow : (m : ℝ) * (n : ℝ)^(-τ) ≤ (n : ℝ)^(-σ) := by
      have hh := mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hnR.le (-τ))
      rw [← Real.rpow_add hnR] at hh
      rw [show τ - σ + -τ = -σ by ring] at hh
      exact hh
    have hb := one_add_mul_le_pow
      (show (-2 : ℝ) ≤ -(n : ℝ)^(-τ) by
        have hlt := prime_neg_rpow_lt_one τ hτ n hp
        linarith) m
    simp only [primePowerFactor, if_pos hp]
    calc
      1 - (n : ℝ)^(-σ) ≤ 1 + (m : ℝ) * (-(n : ℝ)^(-τ)) := by linarith
      _ ≤ (1 + (-(n : ℝ)^(-τ)))^m := hb
      _ = _ := by rw [sub_eq_add_neg]
  · simp [primePowerFactor, hp]

/-- The finite exceptional factors cost only a fixed positive constant. -/
theorem primePowerEulerProduct_eventually_le_pow (σ τ : ℝ)
    (hσ : 0 < σ) (hστ : σ < τ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℕ in atTop,
      primePowerEulerProduct σ H ≤ C * primePowerEulerProduct τ H ^ m := by
  obtain ⟨N, hN⟩ := (eventually_atTop.1
    (eventually_primePowerFactor_le_pow σ τ hσ hστ m))
  let a : ℕ → ℝ := primePowerFactor σ
  let b : ℕ → ℝ := primePowerFactor τ
  let A : ℝ := ∏ n ∈ Finset.range N, a n
  let B : ℝ := ∏ n ∈ Finset.range N, b n
  have hA : 0 < A := Finset.prod_pos (fun n _ => primePowerFactor_pos σ hσ n)
  have hB : 0 < B := Finset.prod_pos (fun n _ => primePowerFactor_pos τ (hσ.trans hστ) n)
  refine ⟨A / B^m, div_pos hA (pow_pos hB m), ?_⟩
  have hprod : ∀ k : ℕ,
      (∏ n ∈ Finset.range (N+k), a n) ≤
        (A / B^m) * (∏ n ∈ Finset.range (N+k), b n)^m := by
    intro k
    induction k with
    | zero =>
        simp only [Nat.add_zero]
        change A ≤ A / B^m * B^m
        rw [div_mul_cancel₀ _ (ne_of_gt (pow_pos hB m))]
    | succ k ih =>
        rw [Nat.add_succ, Finset.prod_range_succ, Finset.prod_range_succ, mul_pow]
        have ha := (primePowerFactor_pos σ hσ (N+k)).le
        have hright : 0 ≤ (A / B^m) * (∏ n ∈ Finset.range (N+k), b n)^m := by
          apply mul_nonneg (le_of_lt (div_pos hA (pow_pos hB m)))
          exact pow_nonneg (Finset.prod_nonneg (fun n _ =>
            (primePowerFactor_pos τ (hσ.trans hστ) n).le)) _
        calc
          _ ≤ ((A / B^m) * (∏ n ∈ Finset.range (N+k), b n)^m) * (b (N+k))^m :=
            mul_le_mul ih (hN (N+k) (by omega)) ha hright
          _ = _ := by ring
  filter_upwards [eventually_ge_atTop N] with H hH
  simpa only [primePowerEulerProduct_eq_range,
    show N+(H+1-N)=H+1 by omega] using hprod (H+1-N)

/-- Elementary Euler-product decay at the exact rate required by the adjacent
Mellin estimate. Exponent amplification replaces all prime-counting asymptotics. -/
theorem primePowerEulerProduct_scaled_tendsto_zero (σ : ℝ)
    (hσ : 0 < σ) (hσ1 : σ < 1) :
    Tendsto (fun H : ℕ => (H : ℝ)^(1-σ) * primePowerEulerProduct σ H)
      atTop (𝓝 0) := by
  let τ : ℝ := (1+σ)/2
  have hστ : σ < τ := by dsimp [τ]; linarith
  have hτ : 0 < τ := hσ.trans hστ
  obtain ⟨C, hC, hbound⟩ := primePowerEulerProduct_eventually_le_pow σ τ hσ hστ 3
  have ht : Tendsto (fun H : ℕ => C * (H : ℝ)^(-(1-σ)/2)) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop (by linarith : 0 < (1-σ)/2)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun H : ℕ => (H : ℝ)) atTop atTop)).const_mul C
    simpa only [Function.comp_def, neg_div, mul_zero] using h
  apply squeeze_zero' ?_ ?_ ht
  · exact Filter.Eventually.of_forall (fun H =>
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg H) _)
        (primePowerEulerProduct_pos σ hσ H).le)
  · filter_upwards [hbound, eventually_ge_atTop 1] with H hH hH1
    have hHR : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
    have hbase := primePowerEulerProduct_le_rpow τ hτ H hH1
    have hcube := pow_le_pow_left₀ (primePowerEulerProduct_pos τ hτ H).le hbase 3
    calc
      _ ≤ (H : ℝ)^(1-σ) * (C * primePowerEulerProduct τ H^3) :=
        mul_le_mul_of_nonneg_left hH (Real.rpow_nonneg hHR.le _)
      _ ≤ (H : ℝ)^(1-σ) * (C * ((H : ℝ)^(τ-1))^3) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcube hC.le)
          (Real.rpow_nonneg hHR.le _)
      _ = C * (H : ℝ)^(-(1-σ)/2) := by
        rw [← Real.rpow_mul_natCast hHR.le]
        rw [mul_left_comm, ← Real.rpow_add hHR]
        congr 2
        dsimp [τ]
        ring

/-- Finite Euler products below one decay faster than every fixed real power.
The proof uses only the existing finite Euler expansion and exponent comparison. -/
theorem primePowerEulerProduct_any_power_tendsto_zero (σ A : ℝ)
    (hσ : 0 < σ) (hσ1 : σ < 1) :
    Tendsto (fun H : ℕ => (H : ℝ) ^ A * primePowerEulerProduct σ H)
      atTop (𝓝 0) := by
  let τ : ℝ := (1 + σ) / 2
  have hστ : σ < τ := by dsimp [τ]; linarith
  have hτ : 0 < τ := hσ.trans hστ
  have hτ1 : 0 < 1 - τ := by dsimp [τ]; linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (A / (1 - τ))
  have hexp : A + (τ - 1) * (m : ℝ) < 0 := by
    have hh := (div_lt_iff₀ hτ1).mp hm
    nlinarith
  obtain ⟨C, hC, hbound⟩ := primePowerEulerProduct_eventually_le_pow σ τ hσ hστ m
  have ht : Tendsto (fun H : ℕ => C * (H : ℝ) ^ (A + (τ - 1) * (m : ℝ))) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop (neg_pos.mpr hexp)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun H : ℕ => (H : ℝ)) atTop atTop)).const_mul C
    simpa only [neg_neg, Function.comp_def, mul_zero] using h
  apply squeeze_zero' ?_ ?_ ht
  · exact Filter.Eventually.of_forall (fun H =>
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg H) _)
        (primePowerEulerProduct_pos σ hσ H).le)
  · filter_upwards [hbound, eventually_ge_atTop 1] with H hH hH1
    have hHR : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
    have hbase := primePowerEulerProduct_le_rpow τ hτ H hH1
    have hpow := pow_le_pow_left₀ (primePowerEulerProduct_pos τ hτ H).le hbase m
    calc
      _ ≤ (H : ℝ) ^ A * (C * primePowerEulerProduct τ H ^ m) :=
        mul_le_mul_of_nonneg_left hH (Real.rpow_nonneg hHR.le _)
      _ ≤ (H : ℝ) ^ A * (C * ((H : ℝ) ^ (τ - 1)) ^ m) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hC.le)
          (Real.rpow_nonneg hHR.le _)
      _ = C * (H : ℝ) ^ (A + (τ - 1) * (m : ℝ)) := by
        rw [← Real.rpow_mul_natCast hHR.le, mul_left_comm, ← Real.rpow_add hHR]


end RiemannResearch.Analysis


noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiemannResearch.Analysis

/-- Removing a fixed prime changes the Euler product by one fixed factor. -/
theorem primePowerEulerProduct_erase (σ : ℝ) (hσ : 0 < σ)
    (p H : ℕ) (hp : p.Prime) (hpH : p ≤ H) :
    (p : ℝ)^(-σ) *
      (∏ q ∈ H.succ.primesBelow.erase p, (1-(q : ℝ)^(-σ))) =
    ((p : ℝ)^(-σ) / (1-(p : ℝ)^(-σ))) * primePowerEulerProduct σ H := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlt : (p : ℝ)^(-σ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith)
  have hd : 1-(p : ℝ)^(-σ) ≠ 0 := ne_of_gt (by linarith)
  have hm : p ∈ H.succ.primesBelow := Nat.mem_primesBelow.mpr ⟨by omega, hp⟩
  rw [primePowerEulerProduct, ← Finset.mul_prod_erase _ _ hm]
  field_simp [hd]

/-- The scaled sieve Euler factor with a fixed prime removed also tends to zero. -/
theorem primePowerEulerProduct_erase_scaled_tendsto_zero (σ : ℝ)
    (hσ : 0 < σ) (hσ1 : σ < 1) (p : ℕ) (hp : p.Prime) :
    Tendsto (fun H : ℕ => (H : ℝ)^(1-σ) * ((p : ℝ)^(-σ) *
      ∏ q ∈ H.succ.primesBelow.erase p, (1-(q : ℝ)^(-σ)))) atTop (𝓝 0) := by
  have h := (primePowerEulerProduct_scaled_tendsto_zero σ hσ hσ1).const_mul
    ((p : ℝ)^(-σ)/(1-(p : ℝ)^(-σ)))
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop p] with H hH
  rw [primePowerEulerProduct_erase σ hσ p H hp hH]
  ring

end RiemannResearch.Analysis
