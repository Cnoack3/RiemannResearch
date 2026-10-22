import RiemannResearch.RH.ParetoCovariance
import RiemannResearch.RH.ParetoArithmeticRepair
import RiemannResearch.RH.ParetoNoiseSignal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Exact covariance of head-preserving Pareto repairs

Source: RH_Noise_Signal_Arithmetic_Repair_2026-09-07.pdf, §§4,5,8,
with canonical source report-source.md. These are identities for the actual full
Pareto sums. The bounds use proved boundedness and nonnegativity. No smooth-number
gap estimate, asymptotic noise estimate, or Bessel bound is assumed here.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Normalized difference of two mean-preserving dilations.
For `f = residue b` this is the report's repair with multiplier `b`.
The definition uses the project's weighted dilation `a * f (k / a)`. -/
def scaleRepair (p E : ℕ) (f : ℕ → ℝ) (k : ℕ) : ℝ :=
  (p : ℝ)⁻¹ * (dilation E f k - dilation p f k)

theorem scaleRepair_abs_le {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) (p E k : ℕ) :
    |scaleRepair p E f k| ≤ |(p : ℝ)⁻¹| * ((E : ℝ) * C + (p : ℝ) * C) :=
  bounded_const_mul (bounded_sub (dilation_abs_le hf E) (dilation_abs_le hf p)) _ k

/-- Exact bridge from the dilation repair to the four genuine residue functions. -/
theorem scaleRepair_residue_eq (b p E k : ℕ) :
    scaleRepair p E (residue b) k =
      (p : ℝ)⁻¹ * (residue p k - residue (b*p) k - residue E k + residue (b*E) k) := by
  unfold scaleRepair
  rw [residue_mul_floor, residue_mul_floor]
  rw [Nat.mul_comm E b, Nat.mul_comm p b]
  ring

/-- The head is preserved pointwise; this needs no summability assumption. -/
theorem scaleRepair_head_zero {f : ℕ → ℝ} (hf0 : f 0 = 0)
    (p E k : ℕ) (hpE : p ≤ E) (hk : k < p) : scaleRepair p E f k = 0 := by
  have hkE : k < E := lt_of_lt_of_le hk hpE
  simp [scaleRepair, dilation, Nat.div_eq_of_lt hk, Nat.div_eq_of_lt hkE, hf0]

/-- Differences at any two positive dilation scales have exactly zero mean. -/
theorem paretoMean_two_dilation_difference {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hf0 : f 0 = 0)
    (p E : ℕ) (hp : 0 < p) (hE : 0 < E) :
    paretoMean (fun k => dilation E f k - dilation p f k) = 0 := by
  rw [paretoMean_sub (dilation_abs_le hf E) (dilation_abs_le hf p),
    paretoMean_dilation hf hf0 E hE, paretoMean_dilation hf hf0 p hp]
  ring

/-- Exact zero mean for the normalized repair. -/
theorem paretoMean_scaleRepair {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hf0 : f 0 = 0)
    (p E : ℕ) (hp : 0 < p) (hE : 0 < E) :
    paretoMean (scaleRepair p E f) = 0 := by
  have hs := weighted_summable_of_bounded
    (bounded_sub (dilation_abs_le hf E) (dilation_abs_le hf p))
  calc
    _ = (p : ℝ)⁻¹ * paretoMean (fun k => dilation E f k - dilation p f k) := by
      unfold paretoMean scaleRepair
      rw [← hs.tsum_mul_left]
      apply tsum_congr
      intro k
      ring
    _ = 0 := by rw [paretoMean_two_dilation_difference hf hf0 p E hp hE, mul_zero]

/-- Full four-term covariance for repairs at distinct scales. -/
theorem paretoInner_scaleRepair {f g : ℕ → ℝ} {C D : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hg : ∀ k, |g k| ≤ D) (p E q F : ℕ) :
    paretoInner (scaleRepair p E f) (scaleRepair q F g) =
      (p : ℝ)⁻¹ * (q : ℝ)⁻¹ *
        (paretoInner (dilation E f) (dilation F g) -
          paretoInner (dilation E f) (dilation q g) -
          paretoInner (dilation p f) (dilation F g) +
          paretoInner (dilation p f) (dilation q g)) := by
  have hE := dilation_abs_le hf E
  have hp := dilation_abs_le hf p
  have hF := dilation_abs_le hg F
  have hq := dilation_abs_le hg q
  have hEp := bounded_sub hE hp
  have hFq := bounded_sub hF hq
  unfold scaleRepair
  rw [paretoInner_const_mul_left hEp (bounded_const_mul hFq _),
    paretoInner_const_mul_right hEp hFq,
    paretoInner_sub_left hE hp hFq,
    paretoInner_sub_right hE hF hq,
    paretoInner_sub_right hp hF hq]
  ring

/-- The exact full norm retains the mixed dilation covariance. -/
theorem paretoInner_scaleRepair_self {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hf0 : f 0 = 0)
    (p E : ℕ) (hp : 0 < p) (hE : 0 < E) :
    paretoInner (scaleRepair p E f) (scaleRepair p E f) =
      ((E : ℝ) + (p : ℝ)) / (p : ℝ)^2 * paretoInner f f -
        2 / (p : ℝ)^2 * paretoInner (dilation E f) (dilation p f) := by
  rw [paretoInner_scaleRepair hf hf,
    paretoInner_dilation hf hf hf0 E hE,
    paretoInner_dilation hf hf hf0 p hp,
    paretoInner_comm (dilation p f) (dilation E f)]
  simp only [div_eq_mul_inv, inv_pow]
  ring

/-- A nonnegative profile makes the cross term nonnegative. -/
theorem paretoInner_dilation_nonneg {f : ℕ → ℝ}
    (hf : ∀ k, 0 ≤ f k) (p E : ℕ) :
    0 ≤ paretoInner (dilation E f) (dilation p f) := by
  unfold paretoInner
  apply tsum_nonneg
  intro k
  exact mul_nonneg (positiveWeight_nonneg k)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg E) (hf _))
      (mul_nonneg (Nat.cast_nonneg p) (hf _)))

/-- Explicit `O(1/p)` upper bound, with the constant left exact. -/
theorem paretoInner_scaleRepair_self_le {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hf0 : f 0 = 0) (hnonneg : ∀ k, 0 ≤ f k)
    (p E : ℕ) (hp : 0 < p) (hE : 0 < E) :
    paretoInner (scaleRepair p E f) (scaleRepair p E f) ≤
      ((E : ℝ) + (p : ℝ)) / (p : ℝ)^2 * paretoInner f f := by
  rw [paretoInner_scaleRepair_self hf hf0 p E hp hE]
  exact sub_le_self _ (mul_nonneg (by positivity)
    (paretoInner_dilation_nonneg hnonneg p E))

/-- The geometric `E < 3p` construction has cost strictly below `4 ||f||² / p`. -/
theorem paretoInner_scaleRepair_self_lt {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hf0 : f 0 = 0) (hnonneg : ∀ k, 0 ≤ f k)
    (hnorm : 0 < paretoInner f f)
    (p E : ℕ) (hp : 0 < p) (hE : 0 < E) (hEp : E < 3 * p) :
    paretoInner (scaleRepair p E f) (scaleRepair p E f) <
      4 * paretoInner f f / (p : ℝ) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hEpR : (E : ℝ) < 3 * (p : ℝ) := by exact_mod_cast hEp
  have hsum : (E : ℝ) + (p : ℝ) < 4 * (p : ℝ) := by linarith
  have hbound := mul_lt_mul_of_pos_right
    (div_lt_div_of_pos_right hsum (sq_pos_of_pos hpR)) hnorm
  have heq : (4 * (p : ℝ) / (p : ℝ)^2) * paretoInner f f =
      4 * paretoInner f f / (p : ℝ) := by
    field_simp [ne_of_gt hpR]
    <;> ring
  rw [heq] at hbound
  exact lt_of_le_of_lt (paretoInner_scaleRepair_self_le hf hf0 hnonneg p E hp hE) hbound

/-- Exact norm of an unnormalized two-scale difference, including the covariance.
This applies directly to the adjacent-parity hidden-noise family. -/
theorem paretoInner_two_dilation_difference {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hf0 : f 0 = 0)
    (p E : ℕ) (hp : 0 < p) (hE : 0 < E) :
    paretoInner (fun k => dilation E f k - dilation p f k)
      (fun k => dilation E f k - dilation p f k) =
      ((E : ℝ) + (p : ℝ)) * paretoInner f f -
        2 * paretoInner (dilation E f) (dilation p f) := by
  have hd := dilation_abs_le hf E
  have he := dilation_abs_le hf p
  rw [paretoInner_sub_left hd he (bounded_sub hd he),
    paretoInner_sub_right hd hd he, paretoInner_sub_right he hd he,
    paretoInner_dilation hf hf hf0 E hE,
    paretoInner_dilation hf hf hf0 p hp,
    paretoInner_comm (dilation p f) (dilation E f)]
  ring

/-- The arithmetic and analytic constructions are the same actual sequence. -/
theorem arithmeticRepair_eq_scaleRepair (b p E : ℕ) :
    arithmeticRepair b p E = scaleRepair p E (residue b) := by
  funext k
  exact arithmeticRepair_eq_dilation b p E k

/-- Full zero mean for the report's genuine four-residue combination. -/
theorem arithmeticRepair_mean_zero (b p E : ℕ)
    (hb : 0 < b) (hp : 0 < p) (hE : 0 < E) :
    paretoMean (arithmeticRepair b p E) = 0 := by
  rw [arithmeticRepair_eq_scaleRepair]
  exact paretoMean_scaleRepair (fun k => residue_abs_le b k hb)
    (by simp [residue]) p E hp hE

/-- Exact variance of the arithmetic repair, including its cross covariance. -/
theorem arithmeticRepair_variance (b p E : ℕ)
    (hb : 0 < b) (hp : 0 < p) (hE : 0 < E) :
    paretoVariance (arithmeticRepair b p E) =
      ((E : ℝ) + (p : ℝ)) / (p : ℝ)^2 * paretoInner (residue b) (residue b) -
        2 / (p : ℝ)^2 * paretoInner (dilation E (residue b)) (dilation p (residue b)) := by
  simp only [paretoVariance, arithmeticRepair_mean_zero b p E hb hp hE, sub_zero]
  rw [arithmeticRepair_eq_scaleRepair]
  exact paretoInner_scaleRepair_self (fun k => residue_abs_le b k hb)
    (by simp [residue]) p E hp hE

/-- The full arithmetic repair variance obeys the stated explicit diagonal bound. -/
theorem arithmeticRepair_variance_le (b p E : ℕ)
    (hb : 0 < b) (hp : 0 < p) (hE : 0 < E) :
    paretoVariance (arithmeticRepair b p E) ≤
      ((E : ℝ) + (p : ℝ)) / (p : ℝ)^2 * paretoInner (residue b) (residue b) := by
  simp only [paretoVariance, arithmeticRepair_mean_zero b p E hb hp hE, sub_zero]
  rw [arithmeticRepair_eq_scaleRepair]
  exact paretoInner_scaleRepair_self_le (fun k => residue_abs_le b k hb)
    (by simp [residue]) (fun k => Nat.cast_nonneg _) p E hp hE

end
end RiemannResearch.RH.Pareto
