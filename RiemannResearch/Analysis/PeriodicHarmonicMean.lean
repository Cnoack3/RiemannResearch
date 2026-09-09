import RiemannResearch.Analysis.BoundedPrimitiveAbel
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Periodic harmonic means

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Section 3. These unconditional estimates supply the periodic harmonic main
term in the nearby-packet asymptotic. Signed terms remain together until
the finite Abel identity has been applied.
-/

namespace RiemannResearch.Analysis
open scoped BigOperators
open Filter
noncomputable section

theorem periodic_zero_sum_prefix_bound (a : ℕ → ℝ) (p : ℕ) (hp : 0 < p)
    (hperiod : ∀ k, a (k+p) = a k) (hmean : ∑ k ∈ Finset.range p, a k = 0)
    (C : ℝ) (hC : ∀ k, |a k| ≤ C) (n : ℕ) :
    |∑ k ∈ Finset.range n, a k| ≤ (p:ℝ)*C := by
  have hC0 : 0 ≤ C := (abs_nonneg (a 0)).trans (hC 0)
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < p
    · calc
        _ ≤ ∑ k ∈ Finset.range n, |a k| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.range n, C := Finset.sum_le_sum (fun k _ => hC k)
        _ = (n:ℝ)*C := by simp
        _ ≤ (p:ℝ)*C := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_of_lt hn) hC0
    · have hpn : p ≤ n := Nat.le_of_not_gt hn
      have he : n = p + (n-p) := (Nat.add_sub_of_le hpn).symm
      have hshift : (∑ k ∈ Finset.range (n-p), a (p+k)) =
          ∑ k ∈ Finset.range (n-p), a k := by
        apply Finset.sum_congr rfl
        intro k hk
        simpa only [Nat.add_comm p k] using hperiod k
      calc
        _ = |∑ k ∈ Finset.range (n-p), a k| := by
          conv_lhs => rw [he, Finset.sum_range_add, hmean, zero_add, hshift]
        _ ≤ _ := ih (n-p) (by omega)

theorem periodic_zero_sum_harmonic_bound (a : ℕ → ℝ) (p : ℕ) (hp : 0 < p)
    (hperiod : ∀ k, a (k+p) = a k) (hmean : ∑ k ∈ Finset.range p, a k = 0)
    (C : ℝ) (hC : ∀ k, |a k| ≤ C) (n : ℕ) :
    |∑ k ∈ Finset.range n, a k / ((k:ℝ)+1)| ≤ 2*(p:ℝ)*C := by
  let B := fun k => (∑ j ∈ Finset.range k, a j) + (p:ℝ)*C
  let f := fun k : ℕ => 1 / ((k:ℝ)+1)
  have hB (k : ℕ) : 0 ≤ B k ∧ B k ≤ 2*(p:ℝ)*C := by
    have h := abs_le.mp (periodic_zero_sum_prefix_bound a p hp hperiod hmean C hC k)
    dsimp [B]
    constructor <;> linarith
  have hf (k : ℕ) : 0 ≤ f k := by dsimp [f]; positivity
  have hm : Antitone f := by
    intro i j hij
    dsimp [f]
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hij 1
  have h := boundedPrimitive_weighted_interval_bound B f (2*(p:ℝ)*C) n hB hf hm
  have hstep (k : ℕ) : B (k+1)-B k = a k := by
    dsimp [B]
    rw [Finset.sum_range_succ]
    ring
  simpa only [hstep, f, Nat.cast_zero, zero_add, div_one, mul_one, div_eq_mul_inv,
    one_mul, inv_one] using h

def periodicMean (a : ℕ → ℝ) (p : ℕ) : ℝ :=
  (∑ k ∈ Finset.range p, a k) / (p:ℝ)

/-- Uniform bounded deviation from the exact period mean times the harmonic sum. -/
theorem periodic_harmonic_mean_error_bound (a : ℕ → ℝ) (p : ℕ) (hp : 0 < p)
    (hperiod : ∀ k, a (k+p) = a k) (C : ℝ) (hC : ∀ k, |a k| ≤ C) (n : ℕ) :
    |(∑ k ∈ Finset.range n, a k / ((k:ℝ)+1)) -
      periodicMean a p * (harmonic n : ℝ)| ≤
      2*(p:ℝ)*(C+|periodicMean a p|) := by
  let μ := periodicMean a p
  have hp0 : (p:ℝ) ≠ 0 := by positivity
  have hmean : (∑ k ∈ Finset.range p, (a k-μ)) = 0 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    dsimp [μ, periodicMean]
    field_simp
    ring
  have hbound (k : ℕ) : |a k-μ| ≤ C+|μ| := by
    have ht : |a k-μ| ≤ |a k|+|μ| := by
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (a k) 0 μ
    exact ht.trans (add_le_add (hC k) (le_refl |μ|))
  have h := periodic_zero_sum_harmonic_bound (fun k => a k-μ) p hp
    (fun k => by rw [hperiod]) hmean (C+|μ|) hbound n
  have hharm : (harmonic n : ℝ) = ∑ k ∈ Finset.range n, 1/((k:ℝ)+1) := by
    simp [harmonic, one_div]
  have he : (∑ k ∈ Finset.range n, (a k-μ)/((k:ℝ)+1)) =
      (∑ k ∈ Finset.range n, a k/((k:ℝ)+1)) - μ*(harmonic n:ℝ) := by
    rw [hharm, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  simpa only [he] using h

theorem bounded_error_div_log_tendsto_zero (e : ℕ → ℝ) (C : ℝ)
    (hC : ∀ n, 0 < n → |e n| ≤ C) :
    Tendsto (fun n : ℕ => e n / Real.log n) atTop (nhds 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply squeeze_zero_norm' _ (hlog.const_div_atTop C)
  filter_upwards [eventually_gt_atTop (1:ℕ)] with n hn
  have hlogpos : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hlogpos]
  exact div_le_div_of_nonneg_right (hC n (by omega)) (le_of_lt hlogpos)

theorem harmonic_div_log_tendsto_one :
    Tendsto (fun n : ℕ => (harmonic n:ℝ) / Real.log n) atTop (nhds 1) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hz := Real.tendsto_harmonic_sub_log.div_atTop hlog
  have h := hz.const_add 1
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1:ℕ)] with n hn
  have hn0 : Real.log (n:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  field_simp
  <;> ring

/-- The logarithmic leading coefficient is the ordinary exact period mean. -/
theorem periodic_harmonic_div_log_tendsto (a : ℕ → ℝ) (p : ℕ) (hp : 0 < p)
    (hperiod : ∀ k, a (k+p) = a k) (C : ℝ) (hC : ∀ k, |a k| ≤ C) :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, a k/((k:ℝ)+1)) / Real.log n)
      atTop (nhds (periodicMean a p)) := by
  have he := bounded_error_div_log_tendsto_zero
    (fun n => (∑ k ∈ Finset.range n, a k/((k:ℝ)+1)) - periodicMean a p*(harmonic n:ℝ))
    (2*(p:ℝ)*(C+|periodicMean a p|))
    (fun n _ => periodic_harmonic_mean_error_bound a p hp hperiod C hC n)
  have h := he.add (harmonic_div_log_tendsto_one.const_mul (periodicMean a p))
  simp only [zero_add, mul_one] at h
  apply h.congr'
  filter_upwards [] with n
  ring

end
end RiemannResearch.Analysis
