/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.PrimeTreeMobiusSubtree
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MobiusReciprocal
import Mathlib.Analysis.Normed.Group.Tannery

/-! # Reciprocal Möbius cancellation after finitely many prime exclusions

Source: Tao, A remark on partial sums involving the Möbius function,
Bull. Aust. Math. Soc. 81 (2010), 343–349, doi:10.1017/S0004972709000884.
This module proves the cofinite-prime case used in §7.2 of Prime Trees,
Carries and Zeta Zeros from the ordinary prime number theorem by removing
the excluded Euler factors one at a time.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.NumberTheory.PrimeNumberTheorem.FixedPrimeCylinder
open RiemannResearch.RH.Pareto

def roughReciprocal (B : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, coefficient B (j+1) / ((j+1 : ℕ) : ℝ)

private theorem roughReciprocal_succ (B : Finset ℕ) (n : ℕ) :
    roughReciprocal B (n+1) = roughReciprocal B n + coefficient B (n+1) / ((n+1 : ℕ) : ℝ) :=
  Finset.sum_range_succ _ _

private theorem roughReciprocal_empty (n : ℕ) : roughReciprocal ∅ n = mobiusReciprocalSum n := by
  induction n with
  | zero => simp [roughReciprocal, mobiusReciprocalSum]
  | succ n ih => simp [roughReciprocal_succ, mobiusReciprocalSum_succ, coefficient, ih]

/-- The reciprocal weight puts an extra 1/p on the smaller quotient. -/
theorem roughReciprocal_delete_factor {B : Finset ℕ} {p : ℕ}
    (hB : ∀ q ∈ B, q.Prime) (hp : p.Prime) (hfresh : p ∉ B) (n : ℕ) :
    roughReciprocal (insert p B) n =
      roughReciprocal B n + (p : ℝ)⁻¹ * roughReciprocal (insert p B) (n / p) := by
  classical
  induction n with
  | zero => simp [roughReciprocal]
  | succ n ih =>
    rw [roughReciprocal_succ B, roughReciprocal_succ (insert p B), ih]
    by_cases hd : p ∣ n+1
    · have hdiv := Nat.succ_div_of_dvd hd
      have hx : n+1 = p * (n/p+1) := by rw [← hdiv, Nat.mul_div_cancel' hd]
      have ht : coefficient B (n+1) = -coefficient (insert p B) (n/p+1) := by
        rw [hx, coefficient_mul_prime hB hp hfresh]
      have hz : coefficient (insert p B) (n+1) = 0 := by simp [coefficient, hd]
      rw [hdiv, roughReciprocal_succ, hz, ht]
      have hm : ((n+1 : ℕ) : ℝ) = (p : ℝ) * ((n/p+1 : ℕ) : ℝ) := by exact_mod_cast hx
      rw [hm]
      field_simp
      <;> ring
    · have he : coefficient (insert p B) (n+1) = coefficient B (n+1) := by
        simp [coefficient, hd]
      rw [Nat.succ_div_of_not_dvd hd, he]
      ring

private theorem floor_div_tendsto (q : ℕ) (hq : 0 < q) :
    Tendsto (fun n : ℕ => n/q) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b*q)] with n hn
  exact (Nat.le_div_iff_mul_le hq).mpr hn

/-- The bounded geometric resolvent of the quotient recursion preserves
convergence to zero. -/
private theorem tends_zero_under_prime_deletion (p : ℕ) (hp : 1 < p)
    (g f : ℕ → ℝ) (hg0 : g 0 = 0) (hf0 : f 0 = 0)
    (hg : Tendsto g atTop (𝓝 0))
    (hrec : ∀ n : ℕ, f n = g n + (p : ℝ)⁻¹ * f (n/p)) : Tendsto f atTop (𝓝 0) := by
  let c := (p : ℝ)⁻¹
  have hpR : 1 < (p : ℝ) := by exact_mod_cast hp
  have hc0 : 0 ≤ c := inv_nonneg.mpr (Nat.cast_nonneg p)
  have hc1 : c < 1 := (inv_lt_one₀ (by linarith : 0 < (p : ℝ))).mpr hpR
  have hbounded := hg.abs
  rw [← Nat.cofinite_eq_atTop] at hbounded
  obtain ⟨M, hM⟩ := hbounded.bddAbove_range_of_cofinite
  have hbound (n : ℕ) : |g n| ≤ M := hM (Set.mem_range_self n)
  let u (n k : ℕ) := c^k * g (n/(p^k))
  have hs := (summable_geometric_of_lt_one hc0 hc1).mul_left M
  have hU (n k : ℕ) : ‖u n k‖ ≤ M * c^k := by
    change ‖c ^ k * g (n / p^k)‖ ≤ M * c^k
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hc0 k)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hbound (n/p^k)) (pow_nonneg hc0 k)
  have hseries (n : ℕ) : Summable (u n) := hs.of_norm_bounded (hU n)
  have hvalue (n : ℕ) : (∑' k : ℕ, u n k) = f n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [u, hg0, hf0]
      · have he (k : ℕ) : u n (k+1) = c * u (n/p) k := by
          simp only [u, pow_succ', Nat.div_div_eq_div_mul, mul_assoc]
        rw [(hseries n).tsum_eq_zero_add, hrec n, ← ih (n/p) (Nat.div_lt_self hn hp)]
        simp only [he, tsum_mul_left, u, pow_zero, Nat.div_one, one_mul, c]
  have ht := tendsto_tsum_of_dominated_convergence hs
    (f := u) (g := fun _ : ℕ => (0 : ℝ))
    (fun k => by
      have h := (hg.comp (floor_div_tendsto (p^k) (pow_pos (by omega) k))).const_mul (c^k)
      simpa only [Function.comp_def, mul_zero, u] using h)
    (Eventually.of_forall hU)
  simpa only [hvalue, tsum_zero] using ht

/-- The ordinary, undamped reciprocal series vanishes on the semigroup
of integers whose prime factors avoid any fixed finite collection. -/
theorem roughReciprocal_tendsto (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime) :
    Tendsto (roughReciprocal B) atTop (𝓝 0) := by
  classical
  induction B using Finset.induction_on with
  | empty =>
    simpa only [funext roughReciprocal_empty] using mobiusReciprocalSum_tendsto_zero
  | @insert p B hnot ih =>
    have hsmall : ∀ q ∈ B, q.Prime := fun q hq => hB q (Finset.mem_insert_of_mem hq)
    have hp := hB p (Finset.mem_insert_self p B)
    apply tends_zero_under_prime_deletion p hp.one_lt (roughReciprocal B) _
    · simp [roughReciprocal]
    · simp [roughReciprocal]
    · exact ih hsmall
    · exact roughReciprocal_delete_factor hsmall hp hnot

end RiemannResearch.NumberTheory.PrimeNumberTheorem.FixedPrimeCylinder
