import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact harmonic blocks and their logarithmic limits

Source: user-provided `DyadicTentTerminalVerification20260910(1).md` and
the September 10, 2026 continuation. These elementary limits are consumed
by the exact binary dyadic boundary coefficient calculation.
-/

namespace RiemannResearch.Analysis
open scoped BigOperators
open Filter
noncomputable section

def scaledHarmonicBlock (q H : ℕ) : ℝ :=
  ∑ r ∈ Finset.range H, 1 / ((H : ℝ)*q+r+1)

private theorem harmonic_cast_sum (N : ℕ) :
    (harmonic N : ℝ) = ∑ k ∈ Finset.range N, 1 / ((k : ℝ)+1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [harmonic_succ, Finset.sum_range_succ]
    push_cast
    rw [ih]
    simp only [one_div]

theorem scaledHarmonicBlock_eq_harmonic (q H : ℕ) :
    scaledHarmonicBlock q H =
      (harmonic ((q+1)*H) : ℝ) - harmonic (q*H) := by
  rw [harmonic_cast_sum, harmonic_cast_sum]
  have he : (q+1)*H = q*H+H := by ring
  rw [he, Finset.sum_range_add]
  simp only [Nat.cast_add, Nat.cast_mul]
  unfold scaledHarmonicBlock
  have h : (∑ x ∈ Finset.range H, 1 / ((q : ℝ)*H+x+1)) =
      ∑ x ∈ Finset.range H, 1 / ((H : ℝ)*q+x+1) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [mul_comm (q : ℝ)]
  rw [h]
  ring

/-- A difference of finite harmonic sums converges to the logarithm of the
scale ratio; no difference of divergent infinite sums is formed. -/
theorem harmonic_scaled_difference_tendsto (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun H : ℕ => (harmonic (b*H) : ℝ) - harmonic (a*H))
      atTop (nhds (Real.log b - Real.log a)) := by
  have ht (q : ℕ) (hq : 0 < q) :
      Tendsto (fun H : ℕ => q*H) atTop atTop :=
    tendsto_atTop_mono (fun H => Nat.le_mul_of_pos_left H hq) tendsto_id
  have h := (Real.tendsto_harmonic_sub_log.comp (ht b hb)).sub
    (Real.tendsto_harmonic_sub_log.comp (ht a ha))
  have h' := h.add_const (Real.log b - Real.log a)
  simp only [sub_self, zero_add] at h'
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with H hH
  have ha0 : (a : ℝ) ≠ 0 := by positivity
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  have hH0 : (H : ℝ) ≠ 0 := by positivity
  simp only [Function.comp_def, Nat.cast_mul, Real.log_mul ha0 hH0,
    Real.log_mul hb0 hH0]
  ring

theorem scaledHarmonicBlock_tendsto (q : ℕ) (hq : 0 < q) :
    Tendsto (scaledHarmonicBlock q) atTop
      (nhds (Real.log (q+1 : ℝ) - Real.log q)) := by
  change Tendsto (fun H => scaledHarmonicBlock q H) _ _
  simpa only [scaledHarmonicBlock_eq_harmonic, Nat.cast_add, Nat.cast_one] using
    harmonic_scaled_difference_tendsto q (q+1) hq (by positivity)

end
end RiemannResearch.Analysis
