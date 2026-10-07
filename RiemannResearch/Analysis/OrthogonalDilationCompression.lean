import RiemannResearch.Analysis.FiniteProjectedDilationHierarchy
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Actual Hilbert compression behind the finite dilation hierarchy

Source: user-provided CRT and Four Improvements continuation, 6–7 October 2026.
The extensions retain complete signed identities and correction squares.


The residualized dilation, compression and initial source are constructed from
the continuous dilation, native orthogonal projections and its Hilbert adjoint.
Their pair, symmetry, positivity and source laws are proved from these
definitions. No compression pair law or source margin is supplied as a provider.
-/

noncomputable section
open scoped InnerProductSpace BigOperators
open RiemannResearch.Analysis.FiniteProjectedDilationHierarchy

namespace RiemannResearch.Analysis.OrthogonalDilationCompression

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (W U : Submodule ℝ H) [CompleteSpace W] [CompleteSpace U]

/-- The actual legal innovation `(I-P_U)D|_W`. -/
def residualizedDilation (D : H →L[ℝ] H) : W →L[ℝ] H :=
  D.comp W.subtypeL - U.starProjection.comp (D.comp W.subtypeL)

/-- The actual compression `p P_W D* P_U D|_W`. -/
def compression (D : H →L[ℝ] H) (p : ℝ) : W →L[ℝ] W :=
  p • (W.orthogonalProjectionOnto.comp
    (D.adjoint.comp (U.starProjection.comp (D.comp W.subtypeL))))

omit [CompleteSpace U] in
/-- The complete initial signed source `P_W D* r`. -/
def initialSource (D : H →L[ℝ] H) (r : H) : W :=
  W.orthogonalProjectionOnto (D.adjoint r)

theorem residualizedDilation_apply (D : H →L[ℝ] H) (x : W) :
    residualizedDilation W U D x = D (x : H) - U.starProjection (D (x : H)) := rfl

theorem compression_apply (D : H →L[ℝ] H) (p : ℝ) (x : W) :
    compression W U D p x =
      p • W.orthogonalProjectionOnto (D.adjoint (U.starProjection (D (x : H)))) := rfl

/-- Both compression pairings are the literal reprojection Gram form. -/
theorem compression_inner (D : H →L[ℝ] H) (p : ℝ) (x y : W) :
    ⟪x, compression W U D p y⟫_ℝ =
      p * ⟪U.starProjection (D (x : H)), U.starProjection (D (y : H))⟫_ℝ := by
  rw [compression_apply, real_inner_smul_right,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
    ContinuousLinearMap.adjoint_inner_right]
  have hcross := U.starProjection_inner_eq_zero (D (x : H))
    (U.starProjection (D (y : H))) (U.starProjection_apply_mem _)
  rw [inner_sub_left] at hcross
  rw [sub_eq_zero.mp hcross]

/-- The pair law needed by the hierarchy follows from physical scaling and
native projections, rather than being an independent application hypothesis. -/
theorem residualized_pair_identity (D : H →L[ℝ] H) (p : ℝ)
    (hscale : ∀ f g : H, p * ⟪D f, D g⟫_ℝ = ⟪f, g⟫_ℝ) (x y : W) :
    p * ⟪residualizedDilation W U D x, residualizedDilation W U D y⟫_ℝ =
      ⟪x, y - compression W U D p y⟫_ℝ := by
  exact projected_pair_identity
    (fun x : W => D (x : H)) U.starProjection (compression W U D p) p
    (fun x y => hscale (x : H) (y : H))
    (fun x y => U.starProjection_inner_eq_zero _ _ (U.starProjection_apply_mem _))
    (compression_inner W U D p) x y

/-- Symmetry of the constructed compression. -/
theorem compression_symmetric (D : H →L[ℝ] H) (p : ℝ) (x y : W) :
    ⟪compression W U D p x, y⟫_ℝ = ⟪x, compression W U D p y⟫_ℝ := by
  exact FiniteProjectedDilationHierarchy.compression_symmetric
    (fun x : W => D (x : H)) U.starProjection (compression W U D p) p
    (compression_inner W U D p) x y

/-- Positivity of the constructed compression is a retained projection square. -/
theorem compression_positive (D : H →L[ℝ] H) (p : ℝ) (hp : 0 ≤ p) (x : W) :
    0 ≤ ⟪x, compression W U D p x⟫_ℝ := by
  exact FiniteProjectedDilationHierarchy.compression_positive
    (fun x : W => D (x : H)) U.starProjection (compression W U D p) p hp
    (compression_inner W U D p) x

/-- Native adjoint projection supplies the complete initial signed source. -/
theorem residualized_initial_source (D : H →L[ℝ] H) (r : H)
    (horth : ∀ z ∈ U, ⟪r, z⟫_ℝ = 0) (y : W) :
    ⟪r, residualizedDilation W U D y⟫_ℝ = ⟪initialSource W D r, y⟫_ℝ := by
  rw [residualizedDilation_apply, inner_sub_right,
    horth _ (U.starProjection_apply_mem _), sub_zero]
  symm
  change ⟪W.orthogonalProjectionOnto (D.adjoint r), y⟫_ℝ = _
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    ContinuousLinearMap.adjoint_inner_left]

/-- Actual linear innovations lie in every legal space containing `U` and
the actual dilated source subspace. -/
theorem residualizedDilation_mem (D : H →L[ℝ] H) (S : Submodule ℝ H)
    (hU : U ≤ S) (hD : ∀ x : W, D (x : H) ∈ S) (x : W) :
    residualizedDilation W U D x ∈ S := by
  rw [residualizedDilation_apply]
  exact S.sub_mem (hD x) (hU (U.starProjection_apply_mem _))

/-- The finite native compression hierarchy has no structural pair or source
provider remaining: only physical scaling and old residual orthogonality enter. -/
theorem native_hierarchy_gain (D : H →L[ℝ] H) (p : ℝ) (r : H)
    (hscale : ∀ f g : H, p * ⟪D f, D g⟫_ℝ = ⟪f, g⟫_ℝ)
    (horth : ∀ z ∈ U, ⟪r, z⟫_ℝ = 0) (m : ℕ) :
    ‖r‖ ^ 2 -
      ‖residualIter (residualizedDilation W U D) (compression W U D p) p r
        (initialSource W D r) m‖ ^ 2 =
      p * ∑ k ∈ Finset.range m,
        (‖sourceIter (compression W U D p) (initialSource W D r) k‖ ^ 2 +
          ⟪sourceIter (compression W U D p) (initialSource W D r) k,
            compression W U D p
              (sourceIter (compression W U D p) (initialSource W D r) k)⟫_ℝ) := by
  exact residualIter_gain (residualizedDilation W U D) (compression W U D p) p r
    (initialSource W D r) (residualized_pair_identity W U D p hscale)
    (compression_symmetric W U D p) (residualized_initial_source W U D r horth) m

/-- Every finite native hierarchy keeps the full new-optimizer correction
square. The legal inclusions discharge membership of every native innovation. -/
theorem native_optimizer_hierarchy_gain (D : H →L[ℝ] H) (p : ℝ) (r rnew : H)
    (S : Submodule ℝ H) (hU : U ≤ S) (hD : ∀ x : W, D (x : H) ∈ S)
    (hnew : r - rnew ∈ S) (hneworth : ∀ z ∈ S, ⟪rnew, z⟫_ℝ = 0)
    (hscale : ∀ f g : H, p * ⟪D f, D g⟫_ℝ = ⟪f, g⟫_ℝ)
    (horth : ∀ z ∈ U, ⟪r, z⟫_ℝ = 0) (m : ℕ) :
    ‖r‖ ^ 2 - ‖rnew‖ ^ 2 =
      p * (∑ k ∈ Finset.range (2 * m),
        ⟪initialSource W D r,
          sourceIter (compression W U D p) (initialSource W D r) k⟫_ℝ) +
      ‖residualIter (residualizedDilation W U D) (compression W U D p) p r
        (initialSource W D r) m - rnew‖ ^ 2 := by
  exact hierarchy_optimizer_gain_of_legal_space S
    (residualizedDilation W U D) (compression W U D p) p r rnew (initialSource W D r)
    (residualizedDilation_mem W U D S hU hD) hnew hneworth
    (residualized_pair_identity W U D p hscale) (compression_symmetric W U D p)
    (residualized_initial_source W U D r horth) m

end RiemannResearch.Analysis.OrthogonalDilationCompression
