import RiemannResearch.Analysis.FiniteProjectedDilationHierarchy
import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Real.Sqrt

/-!
# Bounded finite dilation certificates and a final optimal Krylov ray

Source: user-provided CRT and Four Improvements continuation, 6–7 October 2026.
The extensions retain complete signed identities and correction squares.


The source and pair identities are kept exactly. Positivity supplies monotone
finite certificates, but does not supply the arithmetic margin needed for RH.
The last ray can be optimized after any number of canonical corrections. Its
additional nonnegative bonus and the subsequent optimizer square are retained.
-/

noncomputable section

open scoped InnerProductSpace BigOperators Topology
open RiemannResearch.Analysis.ProjectedDilationGain
open RiemannResearch.Analysis.FiniteProjectedDilationHierarchy

namespace RiemannResearch.Analysis.FiniteProjectedDilationCertificates

variable {W H : Type*}
variable [NormedAddCommGroup W] [InnerProductSpace ℝ W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The actual compression has quadratic form bounded above by the identity. -/
theorem compression_quadratic_le
    (R : W → H) (K : W → W) (p : ℝ) (hp : 0 ≤ p)
    (hpair : ∀ x y, p * ⟪R x, R y⟫_ℝ = ⟪x, y - K y⟫_ℝ)
    (x : W) : ⟪x, K x⟫_ℝ ≤ ‖x‖ ^ 2 := by
  have h := hpair x x
  rw [inner_sub_right, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq] at h
  have hn := mul_nonneg hp (sq_nonneg ‖R x‖)
  linarith

/-- Canonical source corrections never increase the residual energy. -/
theorem residualIter_step_energy_le
    (R : W → H) (K : W → W) (p : ℝ) (r : H) (w : W) (hp : 0 ≤ p)
    (hpair : ∀ x y, p * ⟪R x, R y⟫_ℝ = ⟪x, y - K y⟫_ℝ)
    (hsymm : ∀ x y, ⟪K x, y⟫_ℝ = ⟪x, K y⟫_ℝ)
    (hsource : ∀ y, ⟪r, R y⟫_ℝ = ⟪w, y⟫_ℝ)
    (hpositive : ∀ x, 0 ≤ ⟪x, K x⟫_ℝ) (m : ℕ) :
    ‖residualIter R K p r w (m + 1)‖ ^ 2 ≤
      ‖residualIter R K p r w m‖ ^ 2 := by
  have h := residualIter_step_gain R K p r w hpair hsymm hsource m
  have hn := mul_nonneg hp
    (add_nonneg (sq_nonneg ‖sourceIter K w m‖) (hpositive (sourceIter K w m)))
  linarith

/-- Residual energies decrease along every pair of finite stages. -/
theorem residualIter_energy_antitone
    (R : W → H) (K : W → W) (p : ℝ) (r : H) (w : W) (hp : 0 ≤ p)
    (hpair : ∀ x y, p * ⟪R x, R y⟫_ℝ = ⟪x, y - K y⟫_ℝ)
    (hsymm : ∀ x y, ⟪K x, y⟫_ℝ = ⟪x, K y⟫_ℝ)
    (hsource : ∀ y, ⟪r, R y⟫_ℝ = ⟪w, y⟫_ℝ)
    (hpositive : ∀ x, 0 ≤ ⟪x, K x⟫_ℝ) :
    Antitone (fun m => ‖residualIter R K p r w m‖ ^ 2) := by
  exact antitone_nat_of_succ_le
    (residualIter_step_energy_le R K p r w hp hpair hsymm hsource hpositive)

/-- A finite moment certificate is bounded by the initial residual energy. -/
theorem finite_moment_certificate_le
    (R : W → H) (K : W → W) (p : ℝ) (r : H) (w : W)
    (hpair : ∀ x y, p * ⟪R x, R y⟫_ℝ = ⟪x, y - K y⟫_ℝ)
    (hsymm : ∀ x y, ⟪K x, y⟫_ℝ = ⟪x, K y⟫_ℝ)
    (hsource : ∀ y, ⟪r, R y⟫_ℝ = ⟪w, y⟫_ℝ) (m : ℕ) :
    p * (∑ k ∈ Finset.range (2 * m), ⟪w, sourceIter K w k⟫_ℝ) ≤ ‖r‖ ^ 2 := by
  have h := residualIter_gain R K p r w hpair hsymm hsource m
  rw [paired_moments_eq K w hsymm] at h
  linarith [sq_nonneg ‖residualIter R K p r w m‖]

/-- Increasing the finite depth strengthens its moment certificate. -/
theorem finite_moment_certificate_monotone
    (R : W → H) (K : W → W) (p : ℝ) (r : H) (w : W) (hp : 0 ≤ p)
    (hpair : ∀ x y, p * ⟪R x, R y⟫_ℝ = ⟪x, y - K y⟫_ℝ)
    (hsymm : ∀ x y, ⟪K x, y⟫_ℝ = ⟪x, K y⟫_ℝ)
    (hsource : ∀ y, ⟪r, R y⟫_ℝ = ⟪w, y⟫_ℝ)
    (hpositive : ∀ x, 0 ≤ ⟪x, K x⟫_ℝ) :
    Monotone (fun m =>
      p * (∑ k ∈ Finset.range (2 * m), ⟪w, sourceIter K w k⟫_ℝ)) := by
  intro m n hmn
  have hm := residualIter_gain R K p r w hpair hsymm hsource m
  have hn := residualIter_gain R K p r w hpair hsymm hsource n
  rw [paired_moments_eq K w hsymm] at hm hn
  have hle := residualIter_energy_antitone R K p r w hp hpair hsymm hsource hpositive hmn
  linarith

/-- All finite moment certificates are nonnegative. -/
theorem finite_moment_certificate_nonneg
    (K : W → W) (w : W) (p : ℝ) (hp : 0 ≤ p)
    (hsymm : ∀ x y, ⟪K x, y⟫_ℝ = ⟪x, K y⟫_ℝ)
    (hpositive : ∀ x, 0 ≤ ⟪x, K x⟫_ℝ) (m : ℕ) :
    0 ≤ p * (∑ k ∈ Finset.range (2 * m), ⟪w, sourceIter K w k⟫_ℝ) := by
  rw [← paired_moments_eq K w hsymm]
  exact paired_certificate_nonneg K w p hp hpositive m

/-- The source-square budget holds without an inverse or an infinite series. -/
theorem finite_source_square_budget
    (R : W → H) (K : W → W) (p : ℝ) (r : H) (w : W) (hp : 0 < p)
    (hpair : ∀ x y, p * ⟪R x, R y⟫_ℝ = ⟪x, y - K y⟫_ℝ)
    (hsymm : ∀ x y, ⟪K x, y⟫_ℝ = ⟪x, K y⟫_ℝ)
    (hsource : ∀ y, ⟪r, R y⟫_ℝ = ⟪w, y⟫_ℝ)
    (hpositive : ∀ x, 0 ≤ ⟪x, K x⟫_ℝ) (m : ℕ) :
    (∑ k ∈ Finset.range m, ‖sourceIter K w k‖ ^ 2) ≤ ‖r‖ ^ 2 / p := by
  have hsum :
      (∑ k ∈ Finset.range m, ‖sourceIter K w k‖ ^ 2) ≤
        ∑ k ∈ Finset.range m,
          (‖sourceIter K w k‖ ^ 2 +
            ⟪sourceIter K w k, K (sourceIter K w k)⟫_ℝ) := by
    apply Finset.sum_le_sum
    intro k hk
    exact le_add_of_nonneg_right (hpositive _)
  have hgain := residualIter_gain R K p r w hpair hsymm hsource m
  have hmul := mul_le_mul_of_nonneg_left hsum hp.le
  apply (le_div_iff₀ hp).mpr
  nlinarith [sq_nonneg ‖residualIter R K p r w m‖]

/-- The actual transported source squares are summable. No uniform spectral
gap, inverse, or Neumann-series convergence hypothesis is needed. -/
theorem summable_source_squares
    (R : W → H) (K : W → W) (p : ℝ) (r : H) (w : W) (hp : 0 < p)
    (hpair : ∀ x y, p * ⟪R x, R y⟫_ℝ = ⟪x, y - K y⟫_ℝ)
    (hsymm : ∀ x y, ⟪K x, y⟫_ℝ = ⟪x, K y⟫_ℝ)
    (hsource : ∀ y, ⟪r, R y⟫_ℝ = ⟪w, y⟫_ℝ)
    (hpositive : ∀ x, 0 ≤ ⟪x, K x⟫_ℝ) :
    Summable (fun m => ‖sourceIter K w m‖ ^ 2) := by
  apply summable_of_sum_range_le (fun m => sq_nonneg ‖sourceIter K w m‖)
  exact finite_source_square_budget R K p r w hp hpair hsymm hsource hpositive

/-- The infinite source-square budget is bounded by the same finite energy. -/
theorem source_square_tsum_le
    (R : W → H) (K : W → W) (p : ℝ) (r : H) (w : W) (hp : 0 < p)
    (hpair : ∀ x y, p * ⟪R x, R y⟫_ℝ = ⟪x, y - K y⟫_ℝ)
    (hsymm : ∀ x y, ⟪K x, y⟫_ℝ = ⟪x, K y⟫_ℝ)
    (hsource : ∀ y, ⟪r, R y⟫_ℝ = ⟪w, y⟫_ℝ)
    (hpositive : ∀ x, 0 ≤ ⟪x, K x⟫_ℝ) :
    (∑' m, ‖sourceIter K w m‖ ^ 2) ≤ ‖r‖ ^ 2 / p := by
  apply Real.tsum_le_of_sum_range_le (fun m => sq_nonneg ‖sourceIter K w m‖)
  exact finite_source_square_budget R K p r w hp hpair hsymm hsource hpositive

/-- Actual transported source norms vanish as the finite hierarchy deepens. -/
theorem source_norm_tendsto_zero
    (R : W → H) (K : W → W) (p : ℝ) (r : H) (w : W) (hp : 0 < p)
    (hpair : ∀ x y, p * ⟪R x, R y⟫_ℝ = ⟪x, y - K y⟫_ℝ)
    (hsymm : ∀ x y, ⟪K x, y⟫_ℝ = ⟪x, K y⟫_ℝ)
    (hsource : ∀ y, ⟪r, R y⟫_ℝ = ⟪w, y⟫_ℝ)
    (hpositive : ∀ x, 0 ≤ ⟪x, K x⟫_ℝ) :
    Filter.Tendsto (fun m => ‖sourceIter K w m‖) Filter.atTop (𝓝 0) := by
  have hsq :=
    (summable_source_squares R K p r w hp hpair hsymm hsource hpositive).tendsto_atTop_zero
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq

/-- The iterated compression source itself tends to zero in the original
Hilbert-space norm, without a uniform compression gap. -/
theorem source_tendsto_zero
    (R : W → H) (K : W → W) (p : ℝ) (r : H) (w : W) (hp : 0 < p)
    (hpair : ∀ x y, p * ⟪R x, R y⟫_ℝ = ⟪x, y - K y⟫_ℝ)
    (hsymm : ∀ x y, ⟪K x, y⟫_ℝ = ⟪x, K y⟫_ℝ)
    (hsource : ∀ y, ⟪r, R y⟫_ℝ = ⟪w, y⟫_ℝ)
    (hpositive : ∀ x, 0 ≤ ⟪x, K x⟫_ℝ) :
    Filter.Tendsto (sourceIter K w) Filter.atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact source_norm_tendsto_zero R K p r w hp hpair hsymm hsource hpositive

/-- A source-square lower bound can persist only for a bounded number of steps. -/
theorem uniform_source_floor_budget
    (R : W → H) (K : W → W) (p : ℝ) (r : H) (w : W) (hp : 0 < p)
    (hpair : ∀ x y, p * ⟪R x, R y⟫_ℝ = ⟪x, y - K y⟫_ℝ)
    (hsymm : ∀ x y, ⟪K x, y⟫_ℝ = ⟪x, K y⟫_ℝ)
    (hsource : ∀ y, ⟪r, R y⟫_ℝ = ⟪w, y⟫_ℝ)
    (hpositive : ∀ x, 0 ≤ ⟪x, K x⟫_ℝ) (m : ℕ) (δ : ℝ)
    (hfloor : ∀ k < m, δ ≤ ‖sourceIter K w k‖ ^ 2) :
    p * (m : ℝ) * δ ≤ ‖r‖ ^ 2 := by
  have hsum : (m : ℝ) * δ ≤
      ∑ k ∈ Finset.range m, ‖sourceIter K w k‖ ^ 2 := by
    have h := Finset.sum_le_sum (s := Finset.range m)
      (f := fun _ => δ) (g := fun k => ‖sourceIter K w k‖ ^ 2)
      (fun k hk => hfloor k (Finset.mem_range.mp hk))
    simpa using h
  have hbudget := finite_source_square_budget R K p r w hp hpair hsymm hsource hpositive m
  have hle := le_trans hsum hbudget
  have hmul := (le_div_iff₀ hp).mp hle
  nlinarith

/-- Every nonzero transported source gives a nonzero residualized direction.
Thus a vanishing line-search denominator cannot hide a nonzero source. -/
theorem iterated_direction_ne_zero_of_source_ne_zero
    (R : W → H) (K : W → W) (p : ℝ) (r : H) (w : W)
    (hpair : ∀ x y, p * ⟪R x, R y⟫_ℝ = ⟪x, y - K y⟫_ℝ)
    (hsymm : ∀ x y, ⟪K x, y⟫_ℝ = ⟪x, K y⟫_ℝ)
    (hsource : ∀ y, ⟪r, R y⟫_ℝ = ⟪w, y⟫_ℝ) (m : ℕ)
    (hne : sourceIter K w m ≠ 0) : R (sourceIter K w m) ≠ 0 := by
  intro hz
  have h := residualIter_source R K p r w hpair hsymm hsource m (sourceIter K w m)
  rw [hz, inner_zero_right, real_inner_self_eq_norm_sq] at h
  have hpos : 0 < ‖sourceIter K w m‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hne)
  linarith

/-- A nonzero transported source has a strictly positive source-energy gap. -/
theorem iterated_source_energy_gap_pos
    (R : W → H) (K : W → W) (p : ℝ) (r : H) (w : W) (hp : 0 < p)
    (hpair : ∀ x y, p * ⟪R x, R y⟫_ℝ = ⟪x, y - K y⟫_ℝ)
    (hsymm : ∀ x y, ⟪K x, y⟫_ℝ = ⟪x, K y⟫_ℝ)
    (hsource : ∀ y, ⟪r, R y⟫_ℝ = ⟪w, y⟫_ℝ) (m : ℕ)
    (hne : sourceIter K w m ≠ 0) :
    0 < ‖sourceIter K w m‖ ^ 2 -
      ⟪sourceIter K w m, K (sourceIter K w m)⟫_ℝ := by
  exact source_energy_gap_pos R K p (sourceIter K w m) hp hpair
    (iterated_direction_ne_zero_of_source_ne_zero R K p r w hpair hsymm hsource m hne)

/-- The scalar identity underlying the positive final-ray bonus. -/
theorem source_ray_bonus_identity (p a b : ℝ) (hgap : a - b ≠ 0) :
    p * a ^ 2 / (a - b) = p * (a + b) + p * b ^ 2 / (a - b) := by
  field_simp [hgap]
  <;> ring

/-- Finite hierarchy followed by optimal search on its next legal source ray.
The bonus over the next canonical step is exact and remains explicit. -/
theorem hierarchy_final_ray_gain
    (R : W → H) (K : W → W) (p : ℝ) (r : H) (w : W) (hp : 0 < p)
    (hpair : ∀ x y, p * ⟪R x, R y⟫_ℝ = ⟪x, y - K y⟫_ℝ)
    (hsymm : ∀ x y, ⟪K x, y⟫_ℝ = ⟪x, K y⟫_ℝ)
    (hsource : ∀ y, ⟪r, R y⟫_ℝ = ⟪w, y⟫_ℝ) (m : ℕ)
    (hne : sourceIter K w m ≠ 0) :
    let z := sourceIter K w m
    let a := ‖z‖ ^ 2
    let b := ⟪z, K z⟫_ℝ
    ‖r‖ ^ 2 -
      ‖residualIter R K p r w m - (p * a / (a - b)) • R z‖ ^ 2 =
      p * (∑ k ∈ Finset.range (2 * (m + 1)), ⟪w, sourceIter K w k⟫_ℝ) +
        p * b ^ 2 / (a - b) := by
  dsimp only
  let z := sourceIter K w m
  let a := ‖z‖ ^ 2
  let b := ⟪z, K z⟫_ℝ
  have hgap : 0 < a - b :=
    iterated_source_energy_gap_pos R K p r w hp hpair hsymm hsource m hne
  have hnorm : p * ‖R z‖ ^ 2 = a - b := by
    have h := hpair z z
    rw [inner_sub_right, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq] at h
    exact h
  have hnormpos : 0 < ‖R z‖ ^ 2 := by nlinarith [hnorm, hgap]
  have hpairing : ⟪residualIter R K p r w m, R z⟫_ℝ = a := by
    simpa only [z, a, real_inner_self_eq_norm_sq] using
      residualIter_source R K p r w hpair hsymm hsource m z
  have hcoefficient : p * a / (a - b) = a / ‖R z‖ ^ 2 := by
    rw [← hnorm]
    field_simp [ne_of_gt hp, ne_of_gt hnormpos]
  have hray := ray_optimal_gain (residualIter R K p r w m) (R z) hnormpos
  rw [hpairing] at hray
  have hgain := residualIter_gain R K p r w hpair hsymm hsource (m + 1)
  rw [paired_moments_eq K w hsymm] at hgain
  have hstep := residualIter_step_gain R K p r w hpair hsymm hsource m
  have hbonus := source_ray_bonus_identity p a b (ne_of_gt hgap)
  have hquotient : a ^ 2 / ‖R z‖ ^ 2 = p * a ^ 2 / (a - b) := by
    rw [← hnorm]
    field_simp [ne_of_gt hp, ne_of_gt hnormpos]
  rw [hquotient] at hray
  change ‖r‖ ^ 2 -
      ‖residualIter R K p r w m - (p * a / (a - b)) • R z‖ ^ 2 = _
  rw [hcoefficient]
  change ‖residualIter R K p r w m‖ ^ 2 -
    ‖residualIter R K p r w (m + 1)‖ ^ 2 = p * (a + b) at hstep
  linarith

/-- The final optimal ray never weakens the canonical next-step certificate. -/
theorem hierarchy_final_ray_bonus_nonneg
    (p a b : ℝ) (hp : 0 ≤ p) (hgap : 0 < a - b) :
    0 ≤ p * b ^ 2 / (a - b) := by
  exact div_nonneg (mul_nonneg hp (sq_nonneg b)) hgap.le

/-- Positivity of compression makes the last optimal coefficient at least the
canonical dilation coefficient. -/
theorem source_ray_coefficient_ge (p a b : ℝ) (hp : 0 ≤ p)
    (hb : 0 ≤ b) (hgap : 0 < a - b) :
    p ≤ p * a / (a - b) := by
  apply (le_div_iff₀ hgap).mpr
  nlinarith [mul_nonneg hp hb]

/-- The optimized next ray saves precisely its bonus over the canonical next
residual, without discarding any part of the preceding finite hierarchy. -/
theorem final_ray_improvement_exact
    (R : W → H) (K : W → W) (p : ℝ) (r : H) (w : W) (hp : 0 < p)
    (hpair : ∀ x y, p * ⟪R x, R y⟫_ℝ = ⟪x, y - K y⟫_ℝ)
    (hsymm : ∀ x y, ⟪K x, y⟫_ℝ = ⟪x, K y⟫_ℝ)
    (hsource : ∀ y, ⟪r, R y⟫_ℝ = ⟪w, y⟫_ℝ) (m : ℕ)
    (hne : sourceIter K w m ≠ 0) :
    let z := sourceIter K w m
    let a := ‖z‖ ^ 2
    let b := ⟪z, K z⟫_ℝ
    ‖residualIter R K p r w (m + 1)‖ ^ 2 -
      ‖residualIter R K p r w m - (p * a / (a - b)) • R z‖ ^ 2 =
        p * b ^ 2 / (a - b) := by
  have hcanonical := residualIter_gain R K p r w hpair hsymm hsource (m + 1)
  rw [paired_moments_eq K w hsymm] at hcanonical
  have hoptimal := hierarchy_final_ray_gain R K p r w hp hpair hsymm hsource m hne
  dsimp only at hoptimal ⊢
  linarith

/-- The optimal next ray has error no larger than the canonical next step. -/
theorem final_ray_error_le
    (R : W → H) (K : W → W) (p : ℝ) (r : H) (w : W) (hp : 0 < p)
    (hpair : ∀ x y, p * ⟪R x, R y⟫_ℝ = ⟪x, y - K y⟫_ℝ)
    (hsymm : ∀ x y, ⟪K x, y⟫_ℝ = ⟪x, K y⟫_ℝ)
    (hsource : ∀ y, ⟪r, R y⟫_ℝ = ⟪w, y⟫_ℝ) (m : ℕ)
    (hne : sourceIter K w m ≠ 0) :
    let z := sourceIter K w m
    let a := ‖z‖ ^ 2
    let b := ⟪z, K z⟫_ℝ
    ‖residualIter R K p r w m - (p * a / (a - b)) • R z‖ ^ 2 ≤
      ‖residualIter R K p r w (m + 1)‖ ^ 2 := by
  have h := final_ray_improvement_exact R K p r w hp hpair hsymm hsource m hne
  have hn := hierarchy_final_ray_bonus_nonneg p (‖sourceIter K w m‖ ^ 2)
    (⟪sourceIter K w m, K (sourceIter K w m)⟫_ℝ) hp.le
    (iterated_source_energy_gap_pos R K p r w hp hpair hsymm hsource m hne)
  dsimp only at h ⊢
  linarith

/-- The legal optimizer retains both the ray bonus and its complete correction square. -/
theorem hierarchy_final_ray_optimizer_gain_of_legal_space
    (S : Submodule ℝ H) (R : W → H) (K : W → W) (p : ℝ)
    (r rnew : H) (w : W) (hp : 0 < p)
    (hlegal : ∀ x, R x ∈ S)
    (hnew : r - rnew ∈ S)
    (hneworth : ∀ x ∈ S, ⟪rnew, x⟫_ℝ = 0)
    (hpair : ∀ x y, p * ⟪R x, R y⟫_ℝ = ⟪x, y - K y⟫_ℝ)
    (hsymm : ∀ x y, ⟪K x, y⟫_ℝ = ⟪x, K y⟫_ℝ)
    (hsource : ∀ y, ⟪r, R y⟫_ℝ = ⟪w, y⟫_ℝ) (m : ℕ)
    (hne : sourceIter K w m ≠ 0) :
    let z := sourceIter K w m
    let a := ‖z‖ ^ 2
    let b := ⟪z, K z⟫_ℝ
    let trial := residualIter R K p r w m - (p * a / (a - b)) • R z
    ‖r‖ ^ 2 - ‖rnew‖ ^ 2 =
      p * (∑ k ∈ Finset.range (2 * (m + 1)), ⟪w, sourceIter K w k⟫_ℝ) +
        p * b ^ 2 / (a - b) + ‖trial - rnew‖ ^ 2 := by
  dsimp only
  let z := sourceIter K w m
  let a := ‖z‖ ^ 2
  let b := ⟪z, K z⟫_ℝ
  let t := p * a / (a - b)
  let trial := residualIter R K p r w m - t • R z
  have hlegaltrial : r - trial ∈ S := by
    have h := S.add_mem
      (residualIter_legal_difference S R K p r w hlegal m)
      (S.smul_mem t (hlegal z))
    have heq : r - trial =
        (r - residualIter R K p r w m) + t • R z := by
      dsimp only [trial]
      abel
    rw [heq]
    exact h
  have hcorrection : trial - rnew ∈ S := by
    have h := S.sub_mem hnew hlegaltrial
    have heq : trial - rnew = (r - rnew) - (r - trial) := by abel
    rw [heq]
    exact h
  have horth := hneworth (trial - rnew) hcorrection
  have hsplit : ‖trial‖ ^ 2 = ‖rnew‖ ^ 2 + ‖trial - rnew‖ ^ 2 := by
    have heq : trial = rnew + (trial - rnew) := by abel
    calc
      ‖trial‖ ^ 2 = ‖rnew + (trial - rnew)‖ ^ 2 := by rw [← heq]
      _ = _ := by rw [norm_add_sq_real, horth]; ring
  have hgain := hierarchy_final_ray_gain R K p r w hp hpair hsymm hsource m hne
  change ‖r‖ ^ 2 - ‖trial‖ ^ 2 = _ at hgain
  change ‖r‖ ^ 2 - ‖rnew‖ ^ 2 = _ + ‖trial - rnew‖ ^ 2
  linarith

end RiemannResearch.Analysis.FiniteProjectedDilationCertificates
