import RiemannResearch.RH.ParetoCovariance
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Unscaled dilation for normalized Pareto atoms

Source: user-provided CRT and Four Improvements continuation, 6–7 October 2026.
The extensions retain complete signed identities and correction squares.


This adapter uses the actual repository Pareto weights and residue identity.
The repository `dilation p f` includes the factor p; `unscaledDilation p f`
implements the paper's D_p f(k) = f(k / p).

All complete infinite sums below reuse the established ParetoDilation and
ParetoCovariance theorems. The norm recurrence retains both signed mixed Gram
terms; no truncated weights or uniform residue model is introduced.
-/

namespace RiemannResearch.RH.Pareto

noncomputable section

/-- Paper dilation, anchored by the supplied sequence value at zero. -/
def unscaledDilation (p : ℕ) (f : ℕ → ℝ) (k : ℕ) : ℝ := f (k / p)

/-- The legal normalized residue atom g_d(k) = (k % d) / d. -/
def normalizedAtom (d k : ℕ) : ℝ := residue d k / (d : ℝ)

@[simp] theorem normalizedAtom_zero (d : ℕ) : normalizedAtom d 0 = 0 := by
  simp [normalizedAtom, residue]

@[simp] theorem unscaledDilation_zero (p : ℕ) (f : ℕ → ℝ) (hf0 : f 0 = 0) :
    unscaledDilation p f 0 = 0 := by
  simp [unscaledDilation, hf0]

/-- Bounded sequences remain bounded under the paper dilation. -/
theorem unscaledDilation_abs_le {f : ℕ → ℝ} {C : ℝ}
    (hC : ∀ k, |f k| ≤ C) (p k : ℕ) :
    |unscaledDilation p f k| ≤ C := hC (k / p)

/-- Compatibility with the repository's scaled dilation convention. -/
theorem unscaledDilation_eq_scaled (p : ℕ) (f : ℕ → ℝ) (hp : 0 < p) :
    unscaledDilation p f = fun k => (1 / (p : ℝ)) * dilation p f k := by
  funext k
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hp)
  unfold unscaledDilation dilation
  field_simp [hp0]

/-- Exact normalized atom identity D_p g_d = g_(pd) - g_p / d.
Primality and squarefreeness are unnecessary for this arithmetic identity. -/
theorem unscaledDilation_normalizedAtom (p d k : ℕ) (hp : 0 < p) (hd : 0 < d) :
    unscaledDilation p (normalizedAtom d) k =
      normalizedAtom (p * d) k - normalizedAtom p k / (d : ℝ) := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hp)
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hd)
  have hraw := residue_mul_floor p d k
  change (p : ℝ) * residue d (k / p) =
    residue (p * d) k - residue p k at hraw
  unfold unscaledDilation normalizedAtom
  rw [Nat.cast_mul]
  field_simp [hp0, hd0]
  <;> nlinarith [hraw]

/-- Boundedness needed for complete Pareto sum identities is automatic for atoms. -/
theorem normalizedAtom_abs_le_one (d k : ℕ) (hd : 0 < d) :
    |normalizedAtom d k| ≤ 1 := by
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hres : 0 ≤ residue d k := Nat.cast_nonneg _
  have hlt : residue d k < (d : ℝ) := Nat.cast_lt.mpr (Nat.mod_lt k hd)
  have hnonneg : 0 ≤ normalizedAtom d k := div_nonneg hres hdR.le
  rw [abs_of_nonneg hnonneg]
  exact (div_le_one₀ hdR).mpr hlt.le

private theorem paretoMean_scalar_mul (a : ℝ) (f : ℕ → ℝ) :
    paretoMean (fun k => a * f k) = a * paretoMean f := by
  unfold paretoMean
  calc
    (∑' k, positiveWeight k * (a * f k)) =
        ∑' k, a * (positiveWeight k * f k) := by
      apply tsum_congr
      intro k
      ring
    _ = a * ∑' k, positiveWeight k * f k := tsum_mul_left

private theorem paretoInner_scalar_mul (a b : ℝ) (f g : ℕ → ℝ) :
    paretoInner (fun k => a * f k) (fun k => b * g k) =
      (a * b) * paretoInner f g := by
  unfold paretoInner
  calc
    (∑' k, positiveWeight k * ((a * f k) * (b * g k))) =
        ∑' k, (a * b) * (positiveWeight k * (f k * g k)) := by
      apply tsum_congr
      intro k
      ring
    _ = (a * b) * ∑' k, positiveWeight k * (f k * g k) := tsum_mul_left

/-- Complete mean scaling for bounded zero-anchored sequences. -/
theorem paretoMean_unscaledDilation {f : ℕ → ℝ} {C : ℝ}
    (hC : ∀ k, |f k| ≤ C) (hf0 : f 0 = 0) (p : ℕ) (hp : 0 < p) :
    paretoMean (unscaledDilation p f) = paretoMean f / (p : ℝ) := by
  rw [unscaledDilation_eq_scaled p f hp, paretoMean_scalar_mul,
    paretoMean_dilation hC hf0 p hp]
  ring

/-- Complete inner-product scaling. Only one zero anchor is needed because
its product with the other sequence vanishes on the first physical block. -/
theorem paretoInner_unscaledDilation {f g : ℕ → ℝ} {C D : ℝ}
    (hC : ∀ k, |f k| ≤ C) (hD : ∀ k, |g k| ≤ D)
    (hf0 : f 0 = 0) (p : ℕ) (hp : 0 < p) :
    paretoInner (unscaledDilation p f) (unscaledDilation p g) =
      paretoInner f g / (p : ℝ) := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hp)
  rw [unscaledDilation_eq_scaled p f hp, unscaledDilation_eq_scaled p g hp,
    paretoInner_scalar_mul, paretoInner_dilation hC hD hf0 p hp]
  field_simp [hp0]
  <;> ring

/-- The actual complete-weight normalized atom Gram scales by 1/p. -/
theorem paretoInner_unscaledDilation_atoms (p d e : ℕ)
    (hp : 0 < p) (hd : 0 < d) (he : 0 < e) :
    paretoInner (unscaledDilation p (normalizedAtom d))
        (unscaledDilation p (normalizedAtom e)) =
      paretoInner (normalizedAtom d) (normalizedAtom e) / (p : ℝ) := by
  exact paretoInner_unscaledDilation (fun k => normalizedAtom_abs_le_one d k hd)
    (fun k => normalizedAtom_abs_le_one e k he) (normalizedAtom_zero d) p hp

/-- Composition uses the literal integer floor, and includes the zero case. -/
theorem unscaledDilation_comp (p q : ℕ) (f : ℕ → ℝ) :
    unscaledDilation p (unscaledDilation q f) = unscaledDilation (p * q) f := by
  funext k
  simp only [unscaledDilation, Nat.div_div_eq_div_mul]

@[simp] theorem unscaledDilation_one (f : ℕ → ℝ) : unscaledDilation 1 f = f := by
  funext k
  simp [unscaledDilation]

/-- The unscaled increment retains its full signed mean. -/
theorem paretoMean_unscaledDifference {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hf0 : f 0 = 0) (p : ℕ) (hp : 0 < p) :
    paretoMean (fun k => unscaledDilation p f k - f k) =
      (1 / (p : ℝ) - 1) * paretoMean f := by
  rw [paretoMean_sub (fun k => unscaledDilation_abs_le hf p k) hf,
    paretoMean_unscaledDilation hf hf0 p hp]
  ring

/-- Complete covariance of two unscaled increments, with both mixed terms. -/
theorem paretoInner_unscaledDifference {f g : ℕ → ℝ} {C D : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hg : ∀ k, |g k| ≤ D)
    (hf0 : f 0 = 0) (p : ℕ) (hp : 0 < p) :
    paretoInner (fun k => unscaledDilation p f k - f k)
      (fun k => unscaledDilation p g k - g k) =
      (1 / (p : ℝ) + 1) * paretoInner f g -
        paretoInner (unscaledDilation p f) g -
        paretoInner f (unscaledDilation p g) := by
  have hdf := fun k => unscaledDilation_abs_le hf p k
  have hdg := fun k => unscaledDilation_abs_le hg p k
  rw [paretoInner_sub_left hdf hf (bounded_sub hdg hg),
    paretoInner_sub_right hdf hdg hg, paretoInner_sub_right hf hdg hg,
    paretoInner_unscaledDilation hf hg hf0 p hp]
  ring

/-- Reinsert the exact atom identity into the complete covariance before
estimating any cross term. No primality or coprimality is used. -/
theorem paretoInner_normalizedAtom_productRecurrence (p d e : ℕ)
    (hp : 0 < p) (hd : 0 < d) (he : 0 < e) :
    paretoInner (normalizedAtom (p * d)) (normalizedAtom (p * e)) =
      paretoInner (normalizedAtom d) (normalizedAtom e) / (p : ℝ) +
        paretoInner (normalizedAtom (p * d)) (normalizedAtom p) / (e : ℝ) +
        paretoInner (normalizedAtom p) (normalizedAtom (p * e)) / (d : ℝ) -
        paretoInner (normalizedAtom p) (normalizedAtom p) / ((d : ℝ) * (e : ℝ)) := by
  have hdp : 0 < p * d := Nat.mul_pos hp hd
  have hep : 0 < p * e := Nat.mul_pos hp he
  have hpB := fun k => normalizedAtom_abs_le_one p k hp
  have hdpB := fun k => normalizedAtom_abs_le_one (p * d) k hdp
  have hepB := fun k => normalizedAtom_abs_le_one (p * e) k hep
  have hpdB := bounded_const_mul hpB (1 / (d : ℝ))
  have hpeB := bounded_const_mul hpB (1 / (e : ℝ))
  have hdid : unscaledDilation p (normalizedAtom d) =
      fun k => normalizedAtom (p * d) k - (1 / (d : ℝ)) * normalizedAtom p k := by
    funext k
    rw [unscaledDilation_normalizedAtom p d k hp hd]
    ring
  have heid : unscaledDilation p (normalizedAtom e) =
      fun k => normalizedAtom (p * e) k - (1 / (e : ℝ)) * normalizedAtom p k := by
    funext k
    rw [unscaledDilation_normalizedAtom p e k hp he]
    ring
  have hs := paretoInner_unscaledDilation_atoms p d e hp hd he
  rw [hdid, heid, paretoInner_sub_left hdpB hpdB (bounded_sub hepB hpeB),
    paretoInner_sub_right hdpB hepB hpeB,
    paretoInner_sub_right hpdB hepB hpeB,
    paretoInner_const_mul_right hdpB hpB,
    paretoInner_const_mul_left hpB hepB,
    paretoInner_const_mul_left hpB hpeB,
    paretoInner_const_mul_right hpB hpB] at hs
  simp only [div_eq_mul_inv, mul_inv_rev] at hs ⊢
  nlinarith only [hs]

end
end RiemannResearch.RH.Pareto
