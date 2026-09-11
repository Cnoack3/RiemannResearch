import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Final dyadic-orbit step of summable-tail rigidity
Source: user-provided argument, RH_Two_Seed_Tail_Rigidity_Continuation_20260911,
Section 2.3. This proves the final sequence step, not the Fourier regularity bridge.
-/
open Filter
open scoped Topology
namespace RiemannResearch.Analysis.DyadicTailRigidity
theorem eq_zero_of_dyadic_invariant_of_tendsto
    (c : ℕ → ℝ)
    (hscale : ∀ n : ℕ, 0 < n → c (2 * n) = c n)
    (hlim : Tendsto c atTop (𝓝 0))
    (m : ℕ) (hm : 0 < m) : c m = 0 := by
  have horbit : ∀ k : ℕ, c (2 ^ k * m) = c m := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hpos : 0 < 2 ^ k * m := Nat.mul_pos (by positivity) hm
      calc
        c (2 ^ (k + 1) * m) = c (2 * (2 ^ k * m)) := by congr 1; ring
        _ = c (2 ^ k * m) := hscale _ hpos
        _ = c m := ih
  have hpow : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hindices : Tendsto (fun k : ℕ => 2 ^ k * m) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact ((tendsto_atTop.1 hpow) b).mono fun k hk => by
      have : 1 ≤ m := hm
      nlinarith
  have hzero : Tendsto (fun _ : ℕ => c m) atTop (𝓝 0) := by
    simpa only [Function.comp_def, horbit] using hlim.comp hindices
  exact tendsto_nhds_unique tendsto_const_nhds hzero

theorem eq_zero_of_dyadic_scaling_of_weighted_tendsto
    (A : ℕ → ℝ)
    (hscale : ∀ n : ℕ, 0 < n → A (2 * n) = A n / 2)
    (hlim : Tendsto (fun n : ℕ => (n : ℝ) * A n) atTop (𝓝 0))
    (m : ℕ) (hm : 0 < m) : A m = 0 := by
  have hz : (m : ℝ) * A m = 0 :=
    eq_zero_of_dyadic_invariant_of_tendsto (fun n : ℕ => (n : ℝ) * A n)
      (by
        intro n hn
        simp only [Nat.cast_mul, Nat.cast_ofNat, hscale n hn]
        ring) hlim m hm
  exact (mul_eq_zero.mp hz).resolve_left (by positivity)

theorem eq_zero_of_dyadic_scaling_of_weighted_square_summable
    (A : ℕ → ℝ)
    (hscale : ∀ n : ℕ, 0 < n → A (2 * n) = A n / 2)
    (hsum : Summable (fun n : ℕ => ((n : ℝ) * A n) ^ 2))
    (m : ℕ) (hm : 0 < m) : A m = 0 := by
  have hz : ((m : ℝ) * A m) ^ 2 = 0 :=
    eq_zero_of_dyadic_invariant_of_tendsto (fun n : ℕ => ((n : ℝ) * A n) ^ 2)
      (by
        intro n hn
        simp only [Nat.cast_mul, Nat.cast_ofNat, hscale n hn]
        ring) hsum.tendsto_atTop_zero m hm
  have hmreal : 0 < (m : ℝ) := by positivity
  have hprod : (m : ℝ) * A m = 0 := by nlinarith [sq_nonneg ((m : ℝ) * A m)]
  exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hmreal)
end RiemannResearch.Analysis.DyadicTailRigidity
