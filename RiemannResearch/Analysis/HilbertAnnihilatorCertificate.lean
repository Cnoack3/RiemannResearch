import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Ring

/-!
# Exact Hilbert annihilator certificates

Source: the standard orthogonal-complement characterization of closed spans;
developed for the user's Ramanujan duality program, 23 October 2026.
The Cauchy certificate holds for the full closed span and is attained by the
canonical residual. Outside the closure, its normalized version gives a
separator attaining the sharp nearest-point bound.
-/

noncomputable section

namespace RiemannResearch.Analysis.HilbertAnnihilatorCertificate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

abbrev closedSpan (A : Set H) : Submodule ℝ H :=
  (Submodule.span ℝ A).topologicalClosure

omit [CompleteSpace H] in
theorem span_annihilator_iff (A : Set H) (h : H) :
    h ∈ (Submodule.span ℝ A)ᗮ ↔
      ∀ v ∈ A, inner ℝ h v = 0 := by
  constructor
  · intro hh v hv
    exact (Submodule.mem_orthogonal' _ h).mp hh v
      (Submodule.subset_span hv)
  · intro hh
    have hs : Submodule.span ℝ A ≤ (innerSL ℝ h).ker := by
      apply Submodule.span_le.mpr
      intro v hv
      exact hh v hv
    exact (Submodule.mem_orthogonal' _ h).mpr (fun v hv => hs hv)

theorem closure_iff_annihilator (A : Set H) (x : H) :
    x ∈ closedSpan A ↔
      ∀ h : H, (∀ v ∈ A, inner ℝ h v = 0) → inner ℝ h x = 0 := by
  change x ∈ (Submodule.span ℝ A).topologicalClosure ↔ _
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  constructor
  · intro hx h hh
    exact (Submodule.mem_orthogonal _ x).mp hx h
      ((span_annihilator_iff A h).mpr hh)
  · intro hh
    exact (Submodule.mem_orthogonal _ x).mpr
      (fun h ha => hh h ((span_annihilator_iff A h).mp ha))

theorem closedSpan_annihilator_iff (A : Set H) (h : H) :
    h ∈ (closedSpan A)ᗮ ↔
      ∀ v ∈ A, inner ℝ h v = 0 := by
  constructor
  · intro hh v hv
    exact (Submodule.mem_orthogonal' _ h).mp hh v
      (Submodule.le_topologicalClosure _ (Submodule.subset_span hv))
  · intro hh
    exact (Submodule.mem_orthogonal' _ h).mpr
      (fun v hv => (closure_iff_annihilator A v).mp hv h hh)

/-- The competitor belongs to the full closed span, not merely the algebraic span. -/
theorem cauchy_certificate_bound (A : Set H) (x h v : H)
    (ha : ∀ u ∈ A, inner ℝ h u = 0) (hv : v ∈ closedSpan A) :
    (inner ℝ h x) ^ 2 ≤ ‖h‖ ^ 2 * ‖x - v‖ ^ 2 := by
  have hz : inner ℝ h v = 0 :=
    (closure_iff_annihilator A v).mp hv h ha
  have hc := real_inner_mul_inner_self_le h (x - v)
  rw [inner_sub_right, hz, sub_zero, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq] at hc
  simpa only [pow_two] using hc

def residual (A : Set H) (x : H) : H :=
  x - (closedSpan A).starProjection x

theorem residual_mem_orthogonal (A : Set H) (x : H) :
    residual A x ∈ (closedSpan A)ᗮ :=
  Submodule.sub_starProjection_mem_orthogonal x

/-- The exact signed pairing of the canonical residual with its target. -/
theorem residual_inner_target (A : Set H) (x : H) :
    inner ℝ (residual A x) x = ‖residual A x‖ ^ 2 := by
  have hz : inner ℝ (residual A x) ((closedSpan A).starProjection x) = 0 :=
    (Submodule.mem_orthogonal' _ _).mp (residual_mem_orthogonal A x) _
      ((closedSpan A).starProjection_apply_mem x)
  have hh : inner ℝ (residual A x) x -
      inner ℝ (residual A x) ((closedSpan A).starProjection x) =
        ‖residual A x‖ ^ 2 := by
    rw [← inner_sub_right]
    change inner ℝ (residual A x) (residual A x) = _
    exact real_inner_self_eq_norm_sq _
  simpa only [hz, sub_zero] using hh

/-- The canonical residual attains the Cauchy certificate at the nearest point. -/
theorem residual_attains_bound (A : Set H) (x : H) :
    (inner ℝ (residual A x) x) ^ 2 =
      ‖residual A x‖ ^ 2 *
        ‖x - (closedSpan A).starProjection x‖ ^ 2 := by
  rw [residual_inner_target]
  change (‖residual A x‖ ^ 2) ^ 2 =
    ‖residual A x‖ ^ 2 * ‖residual A x‖ ^ 2
  ring

/-- A canonical normalized separator realizes equality at the nearest point. -/
theorem normalized_separator_of_not_closure (A : Set H) (x : H)
    (hx : x ∉ closedSpan A) :
    ∃ h : H, (∀ v ∈ A, inner ℝ h v = 0) ∧
      inner ℝ h x = 1 ∧
      ‖h‖ ^ 2 * ‖x - (closedSpan A).starProjection x‖ ^ 2 = 1 := by
  let r : H := residual A x
  have hr : r ≠ 0 := by
    intro hh
    have he : x = (closedSpan A).starProjection x := sub_eq_zero.mp hh
    apply hx
    rw [he]
    exact (closedSpan A).starProjection_apply_mem x
  have hn : ‖r‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hr)
  have ha : ∀ v ∈ A, inner ℝ r v = 0 :=
    (closedSpan_annihilator_iff A r).mp (residual_mem_orthogonal A x)
  have hi : inner ℝ r x = ‖r‖ ^ 2 := residual_inner_target A x
  refine ⟨(‖r‖ ^ 2)⁻¹ • r, ?_, ?_, ?_⟩
  · intro v hv
    rw [real_inner_smul_left, ha v hv, mul_zero]
  · rw [real_inner_smul_left, hi, inv_mul_cancel₀ hn]
  · change ‖(‖r‖ ^ 2)⁻¹ • r‖ ^ 2 * ‖r‖ ^ 2 = 1
    calc
      _ = ((‖r‖ ^ 2)⁻¹ * ‖r‖ ^ 2) ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        ring
      _ = 1 := by rw [inv_mul_cancel₀ hn, one_pow]

end RiemannResearch.Analysis.HilbertAnnihilatorCertificate
