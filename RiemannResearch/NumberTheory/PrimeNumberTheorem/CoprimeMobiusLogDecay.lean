/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.PrimeTreeRoughReciprocal
import RiemannResearch.RH.ZetaTwoMobiusQuarticFloorDecay
import Mathlib.Tactic

/-!
# Uniform logarithmic decay after removing prime factors

The exact one-prime deletion recurrence and the unconditional ordinary
reciprocal Möbius bound control all finite sets of forbidden primes. The
dependence on that set is an explicit product with a square-root local factor.
These are the coprime sums in the totient decomposition of the truncated
Möbius LCM form. Compare Ramaré and Zúñiga Alterman, *On a Möbius double sum*,
arXiv:2603.25961, Sections 2 and 5.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.NumberTheory.PrimeNumberTheorem.FixedPrimeCylinder
open RiemannResearch.RH.Pareto

/-- The shift two absorbs logarithmic dilation by a prime into its square root. -/
def roughLogWeight (n : ℕ) : ℝ := 2 + Real.log ((n : ℝ) + 1)

theorem roughLogWeight_two_le (n : ℕ) : 2 ≤ roughLogWeight n := by
  have h := Real.log_nonneg (show (1:ℝ) ≤ (n:ℝ)+1 by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
  unfold roughLogWeight
  linarith

theorem roughLogWeight_div_prime (n : ℕ) {p : ℕ} (hp : p.Prime) :
    roughLogWeight n ≤ Real.sqrt (p : ℝ) * roughLogWeight (n / p) := by
  have hpR : 1 < (p:ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : 0 < (p:ℝ) := by linarith
  have hd : n + 1 ≤ p * (n/p + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    have h := Nat.mod_add_div n p
    have h' := Nat.mod_lt n hp.pos
    omega
  have hdR : (n:ℝ)+1 ≤ (p:ℝ)*((n/p:ℕ)+1) := by exact_mod_cast hd
  have hlog := Real.log_le_log (by positivity : 0 < (n:ℝ)+1) hdR
  rw [Real.log_mul hp0.ne' (by positivity : (((n/p:ℕ):ℝ)+1) ≠ 0)] at hlog
  have hs := Real.sqrt_pos.mpr hp0
  have hroot : 1 ≤ Real.sqrt (p:ℝ) := by
    have := Real.sqrt_le_sqrt hpR.le
    simpa using this
  have hlogp := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt hp0.le] at hlogp
  have hg := Real.log_nonneg (show (1:ℝ) ≤ ((n/p:ℕ):ℝ)+1 by linarith [(Nat.cast_nonneg (n/p) : (0:ℝ) ≤ (n/p:ℕ))])
  unfold roughLogWeight
  nlinarith [mul_nonneg (sub_nonneg.mpr hroot) hg]

private theorem rough_empty_weight_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |roughReciprocal ∅ n| * roughLogWeight n ≤ C := by
  have he (n : ℕ) : roughReciprocal ∅ n = mobiusReciprocalSum n := by
    induction n with
    | zero => simp [roughReciprocal, mobiusReciprocalSum]
    | succ n ih =>
      simp only [roughReciprocal, Finset.sum_range_succ] at ih ⊢
      rw [ih, mobiusReciprocalSum_succ]
      simp [coefficient]
  have hz := ZetaTwoMobiusFloor.mobiusReciprocalSum_abs_mul_shiftedLogPow_tendsto_zero 1
  simp only [pow_one] at hz
  rw [← Nat.cofinite_eq_atTop] at hz
  obtain ⟨K,hK⟩ := hz.bddAbove_range_of_cofinite
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [roughReciprocal]
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hln := Real.log_le_log (by positivity : (0:ℝ)<n+1)
    (show (n:ℝ)+1 ≤ (n:ℝ)*2 by linarith)
  rw [Real.log_mul hn0.ne' (by norm_num : (2:ℝ) ≠ 0)] at hln
  have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have hcomp : roughLogWeight n ≤ 6+Real.log (n:ℝ) := by unfold roughLogWeight; linarith
  rw [he]
  exact (mul_le_mul_of_nonneg_left hcomp (abs_nonneg _)).trans
    ((hK (Set.mem_range_self n)).trans (le_max_left _ _))

/-- A single constant controls every forbidden set, every cutoff and all their local factors. -/
theorem roughReciprocal_log_product_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : Finset ℕ), (∀ p ∈ B, p.Prime) → ∀ n : ℕ,
      |roughReciprocal B n| * roughLogWeight n ≤ C *
        ∏ p ∈ B, (1-(Real.sqrt (p:ℝ))⁻¹)⁻¹ := by
  classical
  obtain ⟨C,hC,hbase⟩ := rough_empty_weight_bound
  refine ⟨C,hC,?_⟩
  intro B
  induction B using Finset.induction_on with
  | empty => simpa using hbase
  | @insert p B hnew ih =>
    intro hpr
    have hp := hpr p (Finset.mem_insert_self p B)
    have hB : ∀ q ∈ B, q.Prime := fun q hq => hpr q (Finset.mem_insert_of_mem hq)
    let x := Real.sqrt (p:ℝ)
    have hpR : 1 < (p:ℝ) := by exact_mod_cast hp.one_lt
    have hx : 1 < x := by
      have hh := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ)≤1) hpR
      simpa [x] using hh
    have hx0 : 0 < x := by linarith
    have hx2 : x^2 = (p:ℝ) := Real.sq_sqrt (by positivity)
    have hgap : 0 < 1-x⁻¹ := sub_pos.mpr ((inv_lt_one₀ hx0).mpr hx)
    let K := C * ∏ q ∈ B, (1-(Real.sqrt (q:ℝ))⁻¹)⁻¹
    let A := K*(1-x⁻¹)⁻¹
    have hb := ih hB
    have hpres (n : ℕ) : |roughReciprocal B n| * roughLogWeight n ≤ K := hb n
    have hK : 0 ≤ K := by
      have h0 := hpres 0
      simpa [roughReciprocal] using h0
    have hA : 0 ≤ A := mul_nonneg hK (inv_nonneg.mpr hgap.le)
    have hbalance : K+x⁻¹*A=A := by
      have hc : (1-x⁻¹)*A=K := by
        dsimp only [A]
        rw [mul_left_comm, mul_inv_cancel₀ hgap.ne', mul_one]
      nlinarith only [hc]
    have hscale : (p:ℝ)⁻¹ * x = x⁻¹ := by
      rw [← hx2]
      field_simp [hx0.ne']
    have hgoal (n : ℕ) : |roughReciprocal (insert p B) n| * roughLogWeight n ≤ A := by
      induction n using Nat.strong_induction_on with
      | h n hn =>
        rcases Nat.eq_zero_or_pos n with rfl | hn0
        · simpa [roughReciprocal] using hA
        have hdiv := hn (n/p) (Nat.div_lt_self hn0 hp.one_lt)
        have hlog := roughLogWeight_div_prime n hp
        have hw := roughLogWeight_two_le n
        have hrec := roughReciprocal_delete_factor hB hp hnew n
        have ha : |roughReciprocal (insert p B) n| ≤ |roughReciprocal B n| +
            (p:ℝ)⁻¹ * |roughReciprocal (insert p B) (n/p)| := by
          rw [hrec]
          simpa only [abs_mul, abs_of_nonneg (show 0 ≤ (p:ℝ)⁻¹ by positivity)]
            using abs_add_le (roughReciprocal B n) ((p:ℝ)⁻¹ * roughReciprocal (insert p B) (n/p))
        calc
          _ ≤ (|roughReciprocal B n|+(p:ℝ)⁻¹*|roughReciprocal (insert p B) (n/p)|)*
                roughLogWeight n := mul_le_mul_of_nonneg_right ha (by linarith)
          _ ≤ K+((p:ℝ)⁻¹*|roughReciprocal (insert p B) (n/p)|)*(x*roughLogWeight (n/p)) := by
            rw [add_mul]
            exact add_le_add (hpres n) (mul_le_mul_of_nonneg_left hlog (by positivity))
          _ = K+x⁻¹*(|roughReciprocal (insert p B) (n/p)| * roughLogWeight (n/p)) := by
            rw [← hscale]
            ring
          _ ≤ K+x⁻¹*A := by gcongr
          _ = A := hbalance
    intro n
    rw [Finset.prod_insert hnew]
    simpa only [A, K, x, mul_comm, mul_left_comm, mul_assoc] using hgoal n

end RiemannResearch.NumberTheory.PrimeNumberTheorem.FixedPrimeCylinder
