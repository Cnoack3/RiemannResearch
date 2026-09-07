import RiemannResearch.RH.ParetoSequenceCertificates
import Mathlib.Tactic.Linarith
import RiemannResearch.RH.ParetoPrimePackets

/-!
# Actual Pareto covariance identities for prime enlargement

Source: user-provided argument in RH_Pareto_CRT_Enlargement_and_Dual_Obstruction_2026-09-07.md
and RH_Smoothing_Mixed_Controls_and_Large_Prime_Gains_2026-09-07.md.
Every inner product below is the full weighted infinite sum. Boundedness supplies absolute
summability; no correlation or tail is omitted. The dilation identities need only p > 0.
-/
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

theorem bounded_sub {f g : ℕ → ℝ} {C D : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hg : ∀ k, |g k| ≤ D) :
    ∀ k, |f k - g k| ≤ C + D := by
  intro k
  have h := abs_sub_le (f k) 0 (g k)
  simp only [sub_zero, zero_sub, abs_neg] at h
  exact h.trans (add_le_add (hf k) (hg k))

theorem bounded_const_mul {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) (a : ℝ) : ∀ k, |a * f k| ≤ |a| * C := by
  intro k
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hf k) (abs_nonneg a)

theorem paretoMean_sub {f g : ℕ → ℝ} {C D : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hg : ∀ k, |g k| ≤ D) :
    paretoMean (fun k => f k - g k) = paretoMean f - paretoMean g := by
  unfold paretoMean
  simp_rw [mul_sub]
  exact (weighted_summable_of_bounded hf).tsum_sub (weighted_summable_of_bounded hg)

theorem paretoInner_comm (f g : ℕ → ℝ) : paretoInner f g = paretoInner g f := by
  unfold paretoInner
  apply tsum_congr
  intro k
  ring

theorem paretoInner_sub_left {f g h : ℕ → ℝ} {C D E : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hg : ∀ k, |g k| ≤ D) (hh : ∀ k, |h k| ≤ E) :
    paretoInner (fun k => f k - g k) h = paretoInner f h - paretoInner g h := by
  unfold paretoInner
  simp_rw [sub_mul, mul_sub]
  exact (weighted_summable_of_bounded (bounded_product hf hh)).tsum_sub
    (weighted_summable_of_bounded (bounded_product hg hh))

theorem paretoInner_sub_right {f g h : ℕ → ℝ} {C D E : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hg : ∀ k, |g k| ≤ D) (hh : ∀ k, |h k| ≤ E) :
    paretoInner f (fun k => g k - h k) = paretoInner f g - paretoInner f h := by
  rw [paretoInner_comm, paretoInner_sub_left hg hh hf]
  rw [paretoInner_comm g f, paretoInner_comm h f]

theorem paretoInner_const_mul_left {f g : ℕ → ℝ} {C D : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hg : ∀ k, |g k| ≤ D) (a : ℝ) :
    paretoInner (fun k => a * f k) g = a * paretoInner f g := by
  unfold paretoInner
  calc
    _ = ∑' k, a * (positiveWeight k * (f k * g k)) := by
      apply tsum_congr
      intro k
      ring
    _ = _ := (weighted_summable_of_bounded (bounded_product hf hg)).tsum_mul_left a

theorem paretoInner_const_mul_right {f g : ℕ → ℝ} {C D : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hg : ∀ k, |g k| ≤ D) (a : ℝ) :
    paretoInner f (fun k => a * g k) = a * paretoInner f g := by
  rw [paretoInner_comm, paretoInner_const_mul_left hg hf, paretoInner_comm g f]

theorem paretoInner_self_nonneg (f : ℕ → ℝ) : 0 ≤ paretoInner f f := by
  unfold paretoInner
  apply tsum_nonneg
  intro k
  exact mul_nonneg (positiveWeight_nonneg k) (mul_self_nonneg _)

/-- The actual added control D_p f-f has exactly zero Pareto mean. -/
theorem paretoMean_dilation_difference {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hf0 : f 0 = 0) (p : ℕ) (hp : 0 < p) :
    paretoMean (fun k => dilation p f k - f k) = 0 := by
  rw [paretoMean_sub (dilation_abs_le hf p) hf, paretoMean_dilation hf hf0 p hp]
  ring

/-- Full covariance change for two added controls, retaining both mixed terms. -/
theorem paretoInner_dilation_difference {f g : ℕ → ℝ} {C D : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hg : ∀ k, |g k| ≤ D)
    (hf0 : f 0 = 0) (p : ℕ) (hp : 0 < p) :
    paretoInner (fun k => dilation p f k - f k) (fun k => dilation p g k - g k) =
      ((p : ℝ) + 1) * paretoInner f g - paretoInner (dilation p f) g -
        paretoInner f (dilation p g) := by
  have hdf := dilation_abs_le hf p
  have hdg := dilation_abs_le hg p
  rw [paretoInner_sub_left hdf hf (bounded_sub hdg hg),
    paretoInner_sub_right hdf hdg hg, paretoInner_sub_right hf hdg hg,
    paretoInner_dilation hf hg hf0 p hp]
  ring

/-- Exact norm polynomial for a bounded residual and one bounded control. -/
theorem paretoInner_residual_polynomial {r g : ℕ → ℝ} {C D : ℝ}
    (hr : ∀ k, |r k| ≤ C) (hg : ∀ k, |g k| ≤ D) (a : ℝ) :
    paretoInner (fun k => r k - a * g k) (fun k => r k - a * g k) =
      paretoInner r r - 2 * a * paretoInner r g + a ^ 2 * paretoInner g g := by
  have hag := bounded_const_mul hg a
  rw [paretoInner_sub_left hr hag (bounded_sub hr hag),
    paretoInner_sub_right hr hr hag, paretoInner_sub_right hag hr hag,
    paretoInner_const_mul_right hr hg,
    paretoInner_const_mul_left hg hr,
    paretoInner_const_mul_left hg hag,
    paretoInner_const_mul_right hg hg,
    paretoInner_comm g r]
  ring

/-- Exact scalar Schur gain for the full Pareto norm, after actual summability is proved. -/
theorem paretoInner_optimal_scalar_gain {r g : ℕ → ℝ} {C D : ℝ}
    (hr : ∀ k, |r k| ≤ C) (hg : ∀ k, |g k| ≤ D)
    (hgg : paretoInner g g ≠ 0) (a : ℝ) :
    paretoInner (fun k => r k - a * g k) (fun k => r k - a * g k) =
      paretoInner r r - (paretoInner r g) ^ 2 / paretoInner g g +
        paretoInner g g * (a - paretoInner r g / paretoInner g g) ^ 2 := by
  rw [paretoInner_residual_polynomial hr hg]
  field_simp [hgg]
  <;> ring

/-- Absolute convergence of every genuine packet mean against the complete Pareto law. -/
theorem ramanujanPacket_weighted_summable (q : ℕ) :
    Summable (fun k => positiveWeight k * ramanujanPacket q k) :=
  weighted_summable_of_bounded (ramanujanPacket_abs_le q)

/-- Absolute convergence of every genuine packet covariance. -/
theorem ramanujanPacket_product_weighted_summable (q r : ℕ) :
    Summable (fun k => positiveWeight k * (ramanujanPacket q k * ramanujanPacket r k)) :=
  weighted_summable_of_bounded
    (bounded_product (ramanujanPacket_abs_le q) (ramanujanPacket_abs_le r))

/-- The new control made from a genuine arithmetic packet has exactly zero Pareto mean. -/
theorem ramanujanPacket_enlargement_mean_zero (q p : ℕ) (hp : 0 < p) :
    paretoMean (fun k => dilation p (ramanujanPacket q) k - ramanujanPacket q k) = 0 := by
  apply paretoMean_dilation_difference (ramanujanPacket_abs_le q) _ p hp
  simp [ramanujanPacket, residue]

/-- The complete covariance identity specialized to actual arithmetic packets. -/
theorem ramanujanPacket_enlargement_covariance (q r p : ℕ) (hp : 0 < p) :
    paretoInner (fun k => dilation p (ramanujanPacket q) k - ramanujanPacket q k)
      (fun k => dilation p (ramanujanPacket r) k - ramanujanPacket r k) =
      ((p : ℝ) + 1) * paretoInner (ramanujanPacket q) (ramanujanPacket r) -
        paretoInner (dilation p (ramanujanPacket q)) (ramanujanPacket r) -
        paretoInner (ramanujanPacket q) (dilation p (ramanujanPacket r)) := by
  apply paretoInner_dilation_difference (ramanujanPacket_abs_le q)
    (ramanujanPacket_abs_le r) _ p hp
  simp [ramanujanPacket, residue]

end
end RiemannResearch.RH.Pareto

/-!
# Exact zero means for genuine mixed-conductor packets

Source: user-provided argument in RH_Pareto_CRT_Enlargement_and_Dual_Obstruction_2026-09-07.md.
These statements use the actual complete Pareto mean and discharge packet boundedness.
-/
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Introducing a new prime into any nontrivial packet makes its complete Pareto mean zero. -/
theorem ramanujanPacket_new_prime_mean_zero (p q : ℕ)
    (hp : p.Prime) (hq : 1 < q) (hpq : ¬ p ∣ q) :
    paretoMean (ramanujanPacket (p*q)) = 0 := by
  have he : ramanujanPacket (p*q) =
      fun k => dilation p (ramanujanPacket q) k - ramanujanPacket q k := by
    funext k
    exact ramanujanPacket_mul_prime_of_not_dvd p q k hp hq hpq
  rw [he]
  exact ramanujanPacket_enlargement_mean_zero q p hp.pos

/-- Repeating a prime already present preserves the actual packet mean. -/
theorem ramanujanPacket_repeated_prime_mean (p q : ℕ)
    (hp : p.Prime) (hq : 1 < q) (hpq : p ∣ q) :
    paretoMean (ramanujanPacket (p*q)) = paretoMean (ramanujanPacket q) := by
  have he : ramanujanPacket (p*q) = dilation p (ramanujanPacket q) := by
    funext k
    exact ramanujanPacket_mul_prime_of_dvd p q k hp hq hpq
  rw [he]
  apply paretoMean_dilation (ramanujanPacket_abs_le q) _ p hp.pos
  simp [ramanujanPacket, residue]

/-- Every positive power of a new prime gives a genuine mean-zero mixed packet. -/
theorem ramanujanPacket_prime_power_mul_mean_zero (p q a : ℕ)
    (hp : p.Prime) (hq : 1 < q) (hpq : ¬ p ∣ q) :
    paretoMean (ramanujanPacket (p^(a+1)*q)) = 0 := by
  induction a with
  | zero => simpa using ramanujanPacket_new_prime_mean_zero p q hp hq hpq
  | succ a ih =>
    have hd : p ∣ p^(a+1)*q := by
      refine ⟨p^a*q, ?_⟩
      rw [pow_succ]
      ring
    have hpow : 0 < p^(a+1) := pow_pos hp.pos _
    have hbig : 1 < p^(a+1)*q :=
      lt_of_lt_of_le hq (Nat.le_mul_of_pos_left q hpow)
    have he : p^((a+1)+1)*q = p*(p^(a+1)*q) := by
      rw [pow_succ]
      ring
    change paretoMean (ramanujanPacket (p^((a+1)+1)*q)) = 0
    rw [he, ramanujanPacket_repeated_prime_mean p (p^(a+1)*q) hp hbig hd]
    exact ih

end
end RiemannResearch.RH.Pareto
