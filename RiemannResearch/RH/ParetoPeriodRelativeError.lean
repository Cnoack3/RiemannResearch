import RiemannResearch.RH.ParetoRationalWeightIntervals
import RiemannResearch.RH.ParetoLegalApproximationClosure
import RiemannResearch.RH.ParetoPeriodicRegrouping

/-! # Uniform relative precision for finite Pareto trials

After K exact terms in each congruence class, the available rational upper
enclosure exceeds its true mass by at most a fraction (K+1)⁻². The factor is
independent of the period, the coefficients and the residual being squared. -/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

private theorem interval_width (L r K : ℕ) (hL : 0 < L) (hr : 0 < r) :
    ((elementaryProgressionInterval L r K).hi : ℝ) -
      ((elementaryProgressionInterval L r K).lo : ℝ) =
      ((L : ℝ) - 1) / ((L : ℝ) * (r + L * (K : ℝ)) * (r + L * (K : ℝ) + 1)) := by
  have h₁ : (L : ℝ) ≠ 0 := by positivity
  have h₂ : (r : ℝ) + L * (K : ℝ) ≠ 0 := by positivity
  have h₃ : (r : ℝ) + L * (K : ℝ) + 1 ≠ 0 := by positivity
  unfold elementaryProgressionInterval
  push_cast
  field_simp [h₁, h₂, h₃]
  ring

/-- The excess of the rational upper endpoint is uniformly small relative to
the true mass, even in the last residue class. -/
theorem progressionWeight_upper_relative (L r K : ℕ) (hL : 0 < L)
    (hr : 0 < r) (hrL : r ≤ L) :
    ((elementaryProgressionInterval L r K).hi : ℝ) ≤
      (1 + 1 / ((K : ℝ) + 1)^2) * progressionWeight L r := by
  have hwidth := interval_width L r K hL hr
  have hpoly : ((L : ℝ)-1) * r * (r+1) * ((K : ℝ)+1)^2 ≤
      (L : ℝ) * (r + L * (K : ℝ)) * (r + L * (K : ℝ) + 1) := by
    obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hrL
    cases r with
    | zero => omega
    | succ i =>
      push_cast
      rw [← sub_nonneg]
      ring_nf
      positivity
  have hw : ((L : ℝ)-1) / ((L : ℝ) * (r + L * (K : ℝ)) * (r + L * (K : ℝ) + 1)) ≤
      positiveWeight r / ((K : ℝ)+1)^2 := by
    unfold positiveWeight
    rw [div_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    push_cast at hpoly ⊢
    simpa only [mul_assoc, one_mul] using hpoly
  have hl := (elementaryProgressionInterval_contains L r K hL hr).1
  have hu := div_le_div_of_nonneg_right (positiveWeight_le_progressionWeight L r hL)
    (sq_nonneg ((K : ℝ)+1))
  rw [add_mul, one_mul, one_div, ← div_eq_inv_mul]
  linarith only [hl, hwidth, hw, hu]

/-- A finite upper sum, rational whenever the trial has rational values. -/
def periodLossUpper (L K : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ i : Fin L, ((elementaryProgressionInterval L (i.val+1) K).hi : ℝ) *
    (1 - f (i.val+1))^2

/-- Uniform relative enclosure of the complete squared error. -/
theorem periodLossUpper_bounds (L K : ℕ) (hL : 0 < L) (f : ℕ → ℝ)
    {C : ℝ} (hb : ∀ k, |f k| ≤ C) (hp : ∀ k, f (k + L) = f k) :
    paretoError f ≤ periodLossUpper L K f ∧
      periodLossUpper L K f ≤ (1 + 1 / ((K : ℝ)+1)^2) * paretoError f := by
  have hres (k : ℕ) : |1 - f k| ≤ 1 + C :=
    (abs_sub _ _).trans (by simpa using add_le_add_left (hb k) (1 : ℝ))
  have he := periodic_paretoInner L hL (fun k => 1 - f k) hres (fun k => by rw [hp])
  change paretoError f = _ at he
  rw [he, Finset.mul_sum]
  constructor
  · exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
      (elementaryProgressionInterval_contains L (i.val+1) K hL (by omega)).2 (sq_nonneg _)
  · apply Finset.sum_le_sum
    intro i _
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (progressionWeight_upper_relative L (i.val+1) K hL (by omega) i.isLt) (sq_nonneg _)

/-- A minimizer computed with rational upper weights approximates any competing
trial within the same uniform factor in complete squared error. -/
theorem periodLossUpper_trial_comparison (L K : ℕ) (hL : 0 < L) (f g : ℕ → ℝ)
    {C D : ℝ} (hf : ∀ k, |f k| ≤ C) (hg : ∀ k, |g k| ≤ D)
    (hfp : ∀ k, f (k + L) = f k) (hgp : ∀ k, g (k + L) = g k)
    (hcmp : periodLossUpper L K f ≤ periodLossUpper L K g) :
    paretoError f ≤ (1 + 1 / ((K : ℝ) + 1)^2) * paretoError g :=
  (periodLossUpper_bounds L K hL f hf hfp).1.trans
    (hcmp.trans (periodLossUpper_bounds L K hL g hg hgp).2)

/-- For the actual two-seed span, any fixed quadrature depth suffices.
Only the arithmetic construction of arbitrarily small finite upper sums is required. -/
theorem riemannHypothesis_of_twoSeed_periodLossUpper (K : ℕ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ (L : ℕ) (f : ℕ → ℝ), 0 < L ∧
      f ∈ legalSeedSpan ({2, 3} : Set ℕ) ∧ (∀ k, f (k + L) = f k) ∧
      periodLossUpper L K f < ε) : RiemannHypothesis := by
  have hs (a : ℕ) (ha : a ∈ ({2, 3} : Set ℕ)) : 0 < a := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    omega
  apply riemannHypothesis_of_legal_paretoError _ hs
  intro ε hε
  obtain ⟨L, f, hL, hf, hp, hu⟩ := h ε hε
  obtain ⟨C, hC⟩ := legalSeedSpan_bounded _ hs hf
  exact ⟨f, hf, (periodLossUpper_bounds L K hL f hC hp).1.trans_lt hu⟩

end
end RiemannResearch.RH.Pareto
