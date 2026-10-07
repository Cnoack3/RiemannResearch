import RiemannResearch.Analysis.ProjectedDilationGain
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Abel

/-!
# Finite positive hierarchy for residualized dilation

Source: user-provided CRT and Four Improvements continuation, 6–7 October 2026.
The extensions retain complete signed identities and correction squares.



The structural inputs are the complete residualized-dilation pair identity and
the actual signed source identity. They contain no arithmetic margin. A finite
hierarchy is obtained without an inverse or an infinite Neumann series. The
positive terms are grouped into adjacent even/odd moments; the ungrouped identity
has exactly `2*m` moments.

The imported ProjectedDilationGain module supplies optimal line search.
All optimizer equalities retain their correction square.
-/

noncomputable section

open scoped InnerProductSpace BigOperators

open RiemannResearch.Analysis.ProjectedDilationGain

namespace RiemannResearch.Analysis.FiniteProjectedDilationHierarchy

variable {W H : Type*}
variable [NormedAddCommGroup W] [InnerProductSpace ℝ W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Iterated actual compression sources, starting from the post-prime source. -/
def sourceIter (K : W → W) (w : W) : ℕ → W
  | 0 => w
  | n + 1 => K (sourceIter K w n)

/-- Residual after the first `m` finite legal dilation corrections. -/
def residualIter (R : W → H) (K : W → W) (p : ℝ) (r : H) (w : W) : ℕ → H
  | 0 => r
  | n + 1 => residualIter R K p r w n - p • R (sourceIter K w n)

omit [NormedAddCommGroup W] [InnerProductSpace ℝ W] in
/-- Every finite hierarchy trial stays in the literal supplied legal subspace. -/
theorem residualIter_legal_difference
    (S : Submodule ℝ H) (R : W → H) (K : W → W) (p : ℝ) (r : H) (w : W)
    (hlegal : ∀ x, R x ∈ S) (m : ℕ) : r - residualIter R K p r w m ∈ S := by
  induction m with
  | zero => simp [residualIter]
  | succ m ih =>
      have heq : r - residualIter R K p r w (m + 1) =
          (r - residualIter R K p r w m) + p • R (sourceIter K w m) := by
        rw [residualIter]
        abel
      rw [heq]
      exact S.add_mem ih (S.smul_mem p (hlegal _))

/-- The residualized pair identity follows from physical dilation and projection.
The compression relation is the adjoint definition of the actual `K`.
-/
theorem projected_pair_identity
    (D : W → H) (P : H → H) (K : W → W) (p : ℝ)
    (hD : ∀ x y, p * ⟪D x, D y⟫_ℝ = ⟪x, y⟫_ℝ)
    (hP : ∀ x y, ⟪D x - P (D x), P (D y)⟫_ℝ = 0)
    (hK : ∀ x y, ⟪x, K y⟫_ℝ = p * ⟪P (D x), P (D y)⟫_ℝ)
    (x y : W) :
    p * ⟪D x - P (D x), D y - P (D y)⟫_ℝ = ⟪x, y - K y⟫_ℝ := by
  have hxy := hP x y
  have hyx := hP y x
  rw [inner_sub_left] at hxy hyx
  have hcross : ⟪P (D x), D y⟫_ℝ = ⟪P (D x), P (D y)⟫_ℝ := by
    rw [real_inner_comm (D y) (P (D x)), real_inner_comm (P (D y)) (P (D x))]
    linarith
  have hcross' : ⟪D x, P (D y)⟫_ℝ = ⟪P (D x), P (D y)⟫_ℝ := by
    linarith
  rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_sub_right]
  rw [hcross, hcross']
  nlinarith [hD x y, hK x y]

/-- Self-adjointness is derived from the actual compression inner products. -/
theorem compression_symmetric
    (D : W → H) (P : H → H) (K : W → W) (p : ℝ)
    (hK : ∀ x y, ⟪x, K y⟫_ℝ = p * ⟪P (D x), P (D y)⟫_ℝ)
    (x y : W) : ⟪K x, y⟫_ℝ = ⟪x, K y⟫_ℝ := by
  calc
    ⟪K x, y⟫_ℝ = ⟪y, K x⟫_ℝ := real_inner_comm y (K x)
    _ = p * ⟪P (D y), P (D x)⟫_ℝ := hK y x
    _ = p * ⟪P (D x), P (D y)⟫_ℝ := by
      rw [real_inner_comm (P (D x)) (P (D y))]
    _ = ⟪x, K y⟫_ℝ := (hK x y).symm

/-- Positivity is derived from the physical reprojection square. -/
theorem compression_positive
    (D : W → H) (P : H → H) (K : W → W) (p : ℝ) (hp : 0 ≤ p)
    (hK : ∀ x y, ⟪x, K y⟫_ℝ = p * ⟪P (D x), P (D y)⟫_ℝ)
    (x : W) : 0 ≤ ⟪x, K x⟫_ℝ := by
  rw [hK, real_inner_self_eq_norm_sq]
  exact mul_nonneg hp (sq_nonneg _)

/-- Every finite correction transports the complete signed source by `K`. -/
theorem residualIter_source
    (R : W → H) (K : W → W) (p : ℝ) (r : H) (w : W)
    (hpair : ∀ x y, p * ⟪R x, R y⟫_ℝ = ⟪x, y - K y⟫_ℝ)
    (hsymm : ∀ x y, ⟪K x, y⟫_ℝ = ⟪x, K y⟫_ℝ)
    (hsource : ∀ y, ⟪r, R y⟫_ℝ = ⟪w, y⟫_ℝ)
    (m : ℕ) (y : W) :
    ⟪residualIter R K p r w m, R y⟫_ℝ = ⟪sourceIter K w m, y⟫_ℝ := by
  induction m with
  | zero => simpa [residualIter, sourceIter] using hsource y
  | succ m ih =>
      rw [residualIter, inner_sub_left, real_inner_smul_left, ih, hpair,
        inner_sub_right, sourceIter, hsymm]
      ring

/-- A single complete dilation correction has two retained nonnegative moments. -/
theorem residualIter_step_gain
    (R : W → H) (K : W → W) (p : ℝ) (r : H) (w : W)
    (hpair : ∀ x y, p * ⟪R x, R y⟫_ℝ = ⟪x, y - K y⟫_ℝ)
    (hsymm : ∀ x y, ⟪K x, y⟫_ℝ = ⟪x, K y⟫_ℝ)
    (hsource : ∀ y, ⟪r, R y⟫_ℝ = ⟪w, y⟫_ℝ) (m : ℕ) :
    ‖residualIter R K p r w m‖ ^ 2 -
      ‖residualIter R K p r w (m + 1)‖ ^ 2 =
    p * (‖sourceIter K w m‖ ^ 2 +
      ⟪sourceIter K w m, K (sourceIter K w m)⟫_ℝ) := by
  have hnorm := hpair (sourceIter K w m) (sourceIter K w m)
  rw [inner_sub_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hnorm
  have hnormp := congrArg (fun a : ℝ => p * a) hnorm
  rw [residualIter, norm_sub_sq_real, real_inner_smul_right,
    residualIter_source R K p r w hpair hsymm hsource,
    real_inner_self_eq_norm_sq, real_smul_norm_sq]
  nlinarith [hnormp]

/-- Exact finite hierarchy, grouped into even/odd moment pairs. -/
theorem residualIter_gain
    (R : W → H) (K : W → W) (p : ℝ) (r : H) (w : W)
    (hpair : ∀ x y, p * ⟪R x, R y⟫_ℝ = ⟪x, y - K y⟫_ℝ)
    (hsymm : ∀ x y, ⟪K x, y⟫_ℝ = ⟪x, K y⟫_ℝ)
    (hsource : ∀ y, ⟪r, R y⟫_ℝ = ⟪w, y⟫_ℝ) (m : ℕ) :
    ‖r‖ ^ 2 - ‖residualIter R K p r w m‖ ^ 2 =
      p * ∑ k ∈ Finset.range m,
        (‖sourceIter K w k‖ ^ 2 + ⟪sourceIter K w k, K (sourceIter K w k)⟫_ℝ) := by
  induction m with
  | zero => simp [residualIter]
  | succ m ih =>
      rw [Finset.sum_range_succ]
      have hstep := residualIter_step_gain R K p r w hpair hsymm hsource m
      nlinarith [ih, hstep]

/-- Symmetry moves all compression iterates into the second argument. -/
theorem iterated_inner_transfer
    (K : W → W) (w : W)
    (hsymm : ∀ x y, ⟪K x, y⟫_ℝ = ⟪x, K y⟫_ℝ) (a b : ℕ) :
    ⟪sourceIter K w a, sourceIter K w b⟫_ℝ = ⟪w, sourceIter K w (a + b)⟫_ℝ := by
  induction a generalizing b with
  | zero => simp [sourceIter]
  | succ a ih =>
      change ⟪K (sourceIter K w a), sourceIter K w b⟫_ℝ = _
      rw [hsymm]
      change ⟪sourceIter K w a, sourceIter K w (b + 1)⟫_ℝ = _
      rw [ih]
      exact congrArg (fun n : ℕ => ⟪w, sourceIter K w n⟫_ℝ) (by omega)

/-- The grouped hierarchy is the exact `2*m`-moment finite geometric hierarchy. -/
theorem paired_moments_eq
    (K : W → W) (w : W)
    (hsymm : ∀ x y, ⟪K x, y⟫_ℝ = ⟪x, K y⟫_ℝ) (m : ℕ) :
    (∑ k ∈ Finset.range m,
        (‖sourceIter K w k‖ ^ 2 + ⟪sourceIter K w k, K (sourceIter K w k)⟫_ℝ)) =
      ∑ k ∈ Finset.range (2 * m), ⟪w, sourceIter K w k⟫_ℝ := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have heven : ‖sourceIter K w m‖ ^ 2 = ⟪w, sourceIter K w (2 * m)⟫_ℝ := by
        calc
          ‖sourceIter K w m‖ ^ 2 = ⟪sourceIter K w m, sourceIter K w m⟫_ℝ :=
            (real_inner_self_eq_norm_sq _).symm
          _ = ⟪w, sourceIter K w (m + m)⟫_ℝ := iterated_inner_transfer K w hsymm m m
          _ = _ := congrArg (fun n : ℕ => ⟪w, sourceIter K w n⟫_ℝ) (by omega)
      have hodd : ⟪sourceIter K w m, K (sourceIter K w m)⟫_ℝ =
          ⟪w, sourceIter K w (2 * m + 1)⟫_ℝ := by
        change ⟪sourceIter K w m, sourceIter K w (m + 1)⟫_ℝ = _
        rw [iterated_inner_transfer K w hsymm]
        exact congrArg (fun n : ℕ => ⟪w, sourceIter K w n⟫_ℝ) (by omega)
      rw [heven, hodd, show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ]
      ring

/-- The entire additional optimizer square remains visible in every hierarchy. -/
theorem hierarchy_optimizer_gain
    (R : W → H) (K : W → W) (p : ℝ) (r rnew : H) (w : W)
    (hpair : ∀ x y, p * ⟪R x, R y⟫_ℝ = ⟪x, y - K y⟫_ℝ)
    (hsymm : ∀ x y, ⟪K x, y⟫_ℝ = ⟪x, K y⟫_ℝ)
    (hsource : ∀ y, ⟪r, R y⟫_ℝ = ⟪w, y⟫_ℝ) (m : ℕ)
    (horth : ⟪rnew, residualIter R K p r w m - rnew⟫_ℝ = 0) :
    ‖r‖ ^ 2 - ‖rnew‖ ^ 2 =
      p * (∑ k ∈ Finset.range (2 * m), ⟪w, sourceIter K w k⟫_ℝ) +
      ‖residualIter R K p r w m - rnew‖ ^ 2 := by
  have hsplit : ‖residualIter R K p r w m‖ ^ 2 =
      ‖rnew‖ ^ 2 + ‖residualIter R K p r w m - rnew‖ ^ 2 := by
    have hdecomp : residualIter R K p r w m =
        rnew + (residualIter R K p r w m - rnew) := by abel
    calc
      ‖residualIter R K p r w m‖ ^ 2 =
          ‖rnew + (residualIter R K p r w m - rnew)‖ ^ 2 := congrArg (fun x : H => ‖x‖ ^ 2) hdecomp
      _ = _ := by rw [norm_add_sq_real, horth]; ring
  have hgain := residualIter_gain R K p r w hpair hsymm hsource m
  rw [paired_moments_eq K w hsymm] at hgain
  linarith

/-- The actual legal-subspace optimizer supplies the correction orthogonality.
Only legal membership and the ordinary optimizer residual orthogonality are
used; no additional arithmetic condition is introduced. -/
theorem hierarchy_optimizer_gain_of_legal_space
    (S : Submodule ℝ H) (R : W → H) (K : W → W) (p : ℝ) (r rnew : H) (w : W)
    (hlegal : ∀ x, R x ∈ S)
    (hnew : r - rnew ∈ S)
    (hneworth : ∀ x ∈ S, ⟪rnew, x⟫_ℝ = 0)
    (hpair : ∀ x y, p * ⟪R x, R y⟫_ℝ = ⟪x, y - K y⟫_ℝ)
    (hsymm : ∀ x y, ⟪K x, y⟫_ℝ = ⟪x, K y⟫_ℝ)
    (hsource : ∀ y, ⟪r, R y⟫_ℝ = ⟪w, y⟫_ℝ) (m : ℕ) :
    ‖r‖ ^ 2 - ‖rnew‖ ^ 2 =
      p * (∑ k ∈ Finset.range (2 * m), ⟪w, sourceIter K w k⟫_ℝ) +
      ‖residualIter R K p r w m - rnew‖ ^ 2 := by
  apply hierarchy_optimizer_gain R K p r rnew w hpair hsymm hsource m
  apply hneworth
  have hmem := S.sub_mem hnew (residualIter_legal_difference S R K p r w hlegal m)
  have heq : residualIter R K p r w m - rnew =
      (r - rnew) - (r - residualIter R K p r w m) := by abel
  rw [heq]
  exact hmem

/-- Positivity of `K` makes every actual source-iteration certificate nonnegative. -/
theorem paired_certificate_nonneg
    (K : W → W) (w : W) (p : ℝ) (hp : 0 ≤ p)
    (hpositive : ∀ x, 0 ≤ ⟪x, K x⟫_ℝ) (m : ℕ) :
    0 ≤ p * ∑ k ∈ Finset.range m,
      (‖sourceIter K w k‖ ^ 2 + ⟪sourceIter K w k, K (sourceIter K w k)⟫_ℝ) := by
  apply mul_nonneg hp
  exact Finset.sum_nonneg (fun k _ => add_nonneg (sq_nonneg _) (hpositive _))

/-- The line-search denominator is positive for every nonzero residualized
direction, by the physical pair identity. -/
theorem source_energy_gap_pos
    (R : W → H) (K : W → W) (p : ℝ) (w : W) (hp : 0 < p)
    (hpair : ∀ x y, p * ⟪R x, R y⟫_ℝ = ⟪x, y - K y⟫_ℝ)
    (hRw : R w ≠ 0) :
    0 < ‖w‖ ^ 2 - ⟪w, K w⟫_ℝ := by
  have hnorm := hpair w w
  rw [inner_sub_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hnorm
  rw [← hnorm]
  exact mul_pos hp (sq_pos_of_pos (norm_pos_iff.mpr hRw))

end RiemannResearch.Analysis.FiniteProjectedDilationHierarchy
