import RiemannResearch.Analysis.FiniteHeadSurjectivity
import RiemannResearch.RH.QDensityClosureTransfer
import RiemannResearch.RH.QDensityMetric
import RiemannResearch.RH.QDensityMetricInverse
import RiemannResearch.RH.QReciprocalMetric
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

noncomputable section

/-!
# Density coupling and its exact finite-head surjectivity criterion

Source: Christian Noack's mixed-complement discussion, 14 November 2026.
V is the actual full-conductor legal closure and W its Q-orthogonal complement.
C maps V into W; its adjoint maps W into V. The arithmetic density input is
the existing unconditional full reciprocal density theorem.

This module does not prove that C is surjective. It proves that surjectivity
is equivalent to a single finite head detecting every vector of W. The
existence of that head remains an Open arithmetic condition.
-/
namespace RiemannResearch.RH.QDensityCouplingSurjectivity
open ZetaTwoHilbert ZetaTwoProbability QDensityMetric QReciprocalMetric
open QFullResidueProjection QDensityClosureTransfer
open RiemannResearch.Analysis.FiniteHeadSurjectivity

abbrev V := QFullResidueProjection.closure
abbrev W := Vᗮ

def coupling : V →L[ℝ] W :=
  W.orthogonalProjectionOnto.comp (B.comp V.subtypeL)

def reverseCoupling : W →L[ℝ] V :=
  V.orthogonalProjectionOnto.comp (B.comp W.subtypeL)

/-- The coupling is exactly the existing density leakage on V. -/
theorem coupling_coe (v : V) :
    (coupling v : QHilbert) = B (v : QHilbert) - V.starProjection (B v) := by
  exact V.starProjection_orthogonal_val (B v)

theorem coupling_adjoint :
    coupling.adjoint = reverseCoupling := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff reverseCoupling coupling).mpr
  intro w v
  change inner ℝ (V.orthogonalProjectionOnto (B (w : QHilbert))) v =
    inner ℝ w (W.orthogonalProjectionOnto (B (v : QHilbert)))
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  exact B_symmetric _ _

/-- The identity part of B contributes nothing to the reverse coupling. -/
theorem reverseCoupling_eq_reciprocal (w : W) :
    reverseCoupling w = (1 / zetaTwo) • V.orthogonalProjectionOnto (D (w : QHilbert)) := by
  change V.orthogonalProjectionOnto ((1 / zetaTwo) • ((w : QHilbert) + D w)) = _
  rw [map_smul, map_add,
    Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal w.property, zero_add]

/-- Unconditional uniqueness, using full reciprocal density. -/
theorem reverseCoupling_zero (w : W) (hw : reverseCoupling w = 0) : w = 0 := by
  have hBw : B (w : QHilbert) ∈ W := by
    apply Submodule.orthogonalProjectionOnto_eq_zero_iff.mp
    exact hw
  let L : QHilbert →L[ℝ] ℝ := innerSL ℝ (w : QHilbert)
  have hs : legalSpan.map D.toLinearMap ≤ L.ker := by
    rintro _ ⟨v, hv, rfl⟩
    have hvV : v ∈ V := legalSpan.le_topologicalClosure hv
    have h0 : inner ℝ (w : QHilbert) v = 0 := by
      rw [real_inner_comm]
      exact Submodule.inner_right_of_mem_orthogonal hvV w.property
    have hB0 : inner ℝ (w : QHilbert) (B v) = 0 := by
      rw [← B_symmetric, real_inner_comm]
      exact Submodule.inner_right_of_mem_orthogonal hvV hBw
    change inner ℝ (w : QHilbert) (D v) = 0
    rw [QDensityMetricInverse.D_eq_density, inner_sub_right, inner_smul_right, hB0, h0]
    ring
  have hc := (legalSpan.map D.toLinearMap).topologicalClosure_minimal hs L.isClosed_ker
  rw [full_D_map_dense] at hc
  have he : inner ℝ (w : QHilbert) (w : QHilbert) = 0 := hc (by trivial)
  apply Subtype.ext
  apply norm_eq_zero.mp
  rw [real_inner_self_eq_norm_sq] at he
  nlinarith [norm_nonneg (w : QHilbert)]

theorem coupling_adjoint_injective : Function.Injective coupling.adjoint := by
  intro u v huv
  apply sub_eq_zero.mp
  apply reverseCoupling_zero
  rw [← coupling_adjoint, map_sub, huv, sub_self]

theorem coupling_dense_range : coupling.range.topologicalClosure = ⊤ := by
  have hk : coupling.adjoint.ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr coupling_adjoint_injective
  have h := coupling.adjoint.orthogonal_ker
  rw [hk, ContinuousLinearMap.adjoint_adjoint] at h
  simpa using h.symm

/-- Complete normalized coordinates, with no discarded tail. -/
def coordinates : W →ₗ[ℝ] (ℕ → ℝ) where
  toFun w n := (w : QHilbert) n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coupling_adjoint_tail_bound (N : ℕ) (w : W)
    (hw : ∀ n : ℕ, n < N → coordinates w n = 0) :
    ‖coupling.adjoint w‖ ≤ ((1 / zetaTwo) / ((N : ℝ) + 1)) * ‖w‖ := by
  have hZ : 0 ≤ 1 / zetaTwo := div_nonneg zero_le_one zetaTwo_pos.le
  calc
    ‖coupling.adjoint w‖ =
        (1 / zetaTwo) * ‖V.orthogonalProjectionOnto (D (w : QHilbert))‖ := by
      rw [coupling_adjoint, reverseCoupling_eq_reciprocal, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hZ]
    _ ≤ (1 / zetaTwo) * ‖D (w : QHilbert)‖ :=
      mul_le_mul_of_nonneg_left (V.norm_orthogonalProjectionOnto_apply_le _) hZ
    _ ≤ (1 / zetaTwo) * ((1 / ((N : ℝ) + 1)) * ‖(w : QHilbert)‖) :=
      mul_le_mul_of_nonneg_left (D_norm_le_of_head_zero N w hw) hZ
    _ = ((1 / zetaTwo) / ((N : ℝ) + 1)) * ‖w‖ := by
      change _ = ((1 / zetaTwo) / ((N : ℝ) + 1)) * ‖(w : QHilbert)‖
      ring

/-- This is the physical-site formulation used in the mathematical discussion. -/
def PhysicalHeadUnique (N : ℕ) : Prop :=
  ∀ w : W, (∀ k : ℕ, 1 ≤ k → k ≤ N → qSequence (w : QHilbert) k = 0) → w = 0

theorem physicalHeadUnique_iff (N : ℕ) :
    PhysicalHeadUnique N ↔ HeadUnique coordinates N := by
  constructor
  · intro h w hw
    apply h w
    intro k hk hkN
    cases k with
    | zero => omega
    | succ n =>
      rw [qSequence_succ]
      have hn : n < N := by omega
      change (w : QHilbert) n / Real.sqrt (qWeight n) = 0
      rw [show (w : QHilbert) n = 0 from hw n hn, zero_div]
  · intro h w hw
    apply h w
    intro n hn
    have he := hw (n + 1) (by omega) (by omega)
    rw [qSequence_succ] at he
    have hne : Real.sqrt (qWeight n) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (qWeight_pos n))
    have hz := (div_eq_iff hne).mp he
    change (w : QHilbert) n = 0
    simpa using hz

/-- Exact criterion, with no hypothesis asserting existence of a detecting head. -/
theorem coupling_surjective_iff_finite_head :
    Function.Surjective coupling ↔ ∃ N : ℕ, PhysicalHeadUnique N := by
  rw [surjective_iff_exists_headUnique coupling coupling_dense_range coordinates
    (1 / zetaTwo) coupling_adjoint_tail_bound]
  exact exists_congr (fun N => (physicalHeadUnique_iff N).symm)

/-- Finite-dimensionality is equivalent to surjectivity, not provided by density. -/
theorem coupling_surjective_iff_finiteDimensional :
    Function.Surjective coupling ↔ FiniteDimensional ℝ W := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := coupling_surjective_iff_finite_head.mp h
    exact finiteDimensional_of_headUnique coordinates N ((physicalHeadUnique_iff N).mp hN)
  · intro h
    let _ := h
    exact surjective_of_finiteDimensional coupling coupling_dense_range

/-- Conditional exact solvability: the arithmetic finite-head assertion stays explicit. -/
theorem coupling_surjective_of_finite_head (h : ∃ N : ℕ, PhysicalHeadUnique N) :
    Function.Surjective coupling :=
  coupling_surjective_iff_finite_head.mpr h


/-- If the target is infinite-dimensional, every head misses a unit vector.
Its adjoint image has the explicit reciprocal tail bound. -/
theorem exists_unit_head_zero_small_adjoint
    (hinf : ¬ FiniteDimensional ℝ W) (N : ℕ) :
    ∃ w : W, ‖w‖ = 1 ∧
      (∀ n : ℕ, n < N → coordinates w n = 0) ∧
      ‖coupling.adjoint w‖ ≤ (1 / zetaTwo) / ((N : ℝ) + 1) := by
  obtain ⟨w, hw, hne⟩ :
      ∃ w : W, (∀ n : ℕ, n < N → coordinates w n = 0) ∧ w ≠ 0 := by
    by_contra h
    apply hinf
    apply finiteDimensional_of_headUnique coordinates N
    intro w hw
    by_contra hne
    exact h ⟨w, hw, hne⟩
  have hp : 0 < ‖w‖ := norm_pos_iff.mpr hne
  let u : W := ‖w‖⁻¹ • w
  have hu : ‖u‖ = 1 := by
    change ‖(‖w‖⁻¹ : ℝ) • w‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']
  have hh : ∀ n : ℕ, n < N → coordinates u n = 0 := by
    intro n hn
    change coordinates (‖w‖⁻¹ • w) n = 0
    rw [map_smul]
    change ‖w‖⁻¹ * coordinates w n = 0
    rw [hw n hn, mul_zero]
  refine ⟨u, hu, hh, ?_⟩
  simpa only [hu, mul_one] using coupling_adjoint_tail_bound N u hh

theorem coupling_not_surjective_of_infiniteDimensional
    (hinf : ¬ FiniteDimensional ℝ W) : ¬ Function.Surjective coupling :=
  fun h => hinf (coupling_surjective_iff_finiteDimensional.mp h)

/-- Exact complete energy: the W-projected remainder is retained. -/
theorem coupling_adjoint_energy_identity (w : W) :
    zetaTwo ^ 2 * ‖coupling.adjoint w‖ ^ 2 +
      ‖W.orthogonalProjectionOnto (D (w : QHilbert))‖ ^ 2 =
      ∑' n : ℕ, ((w : QHilbert) n) ^ 2 / ((n : ℝ) + 1) ^ 2 := by
  have hnorm : zetaTwo ^ 2 * ‖coupling.adjoint w‖ ^ 2 =
      ‖V.orthogonalProjectionOnto (D (w : QHilbert))‖ ^ 2 := by
    rw [coupling_adjoint, reverseCoupling_eq_reciprocal, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (div_nonneg zero_le_one zetaTwo_pos.le), mul_pow]
    field_simp [ne_of_gt zetaTwo_pos]
  rw [hnorm, ← Submodule.norm_sq_eq_add_norm_sq_projection (D (w : QHilbert)) V]
  exact D_norm_sq (w : QHilbert)

/-- Reciprocal density excludes every nonzero reciprocal image from W.
It gives a regularity obstruction, not an upper bound on the dimension of W. -/
theorem eq_zero_of_reciprocal_mem_orthogonal (f : QHilbert)
    (hf : D f ∈ W) : f = 0 := by
  let L : QHilbert →L[ℝ] ℝ := innerSL ℝ f
  have hs : legalSpan.map D.toLinearMap ≤ L.ker := by
    rintro _ ⟨v, hv, rfl⟩
    change inner ℝ f (D v) = 0
    have hsym : inner ℝ f (D v) = inner ℝ (D f) v := by
      rw [QDensityMetricInverse.D_eq_density, QDensityMetricInverse.D_eq_density,
        inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, B_symmetric]
      simp
    rw [hsym, real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal
      (legalSpan.le_topologicalClosure hv) hf
  have hc := (legalSpan.map D.toLinearMap).topologicalClosure_minimal hs L.isClosed_ker
  rw [full_D_map_dense] at hc
  have he : inner ℝ f f = 0 := hc (by trivial)
  exact (inner_self_eq_zero).mp he


/-- Conditional detection: the uniform adjoint lower bound is an open input. -/
theorem physicalHeadUnique_of_adjoint_lower_bound
    (δ : ℝ) (hlower : ∀ w : W, δ * ‖w‖ ≤ ‖coupling.adjoint w‖)
    (N : ℕ) (hN : (1 / zetaTwo) / ((N : ℝ) + 1) < δ) :
    PhysicalHeadUnique N :=
  (physicalHeadUnique_iff N).mpr
    (headUnique_of_adjoint_lower_bound coupling coordinates (1 / zetaTwo) δ
      coupling_adjoint_tail_bound hlower N hN)

/-- A physical head of length N bounds the real dimension by N. -/
theorem finrank_le_of_physicalHeadUnique (N : ℕ) (hN : PhysicalHeadUnique N) :
    Module.finrank ℝ W ≤ N :=
  finrank_le_of_headUnique coordinates N ((physicalHeadUnique_iff N).mp hN)

/-- Exact coercivity criterion. Neither side is asserted unconditionally. -/
theorem finiteDimensional_iff_adjoint_lower_bound :
    FiniteDimensional ℝ W ↔
      ∃ δ > 0, ∀ w : W, δ * ‖w‖ ≤ ‖coupling.adjoint w‖ := by
  constructor
  · intro h
    obtain ⟨K, hK, hbound⟩ := adjoint_norm_bound_of_surjective coupling
      (coupling_surjective_iff_finiteDimensional.mpr h)
    refine ⟨K⁻¹, inv_pos.mpr hK, ?_⟩
    intro w
    have hh := mul_le_mul_of_nonneg_left (hbound w) (inv_nonneg.mpr hK.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hK.ne', one_mul] using hh
  · rintro ⟨δ, hδ, hlower⟩
    obtain ⟨N, hN⟩ := exists_nat_gt ((1 / zetaTwo) / δ)
    have hprod : 1 / zetaTwo < δ * ((N : ℝ) + 1) := by
      have ht := (div_lt_iff₀ hδ).mp hN
      nlinarith
    have hsmall : (1 / zetaTwo) / ((N : ℝ) + 1) < δ :=
      (div_lt_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)).mpr hprod
    exact finiteDimensional_of_headUnique coordinates N
      ((physicalHeadUnique_iff N).mp
        (physicalHeadUnique_of_adjoint_lower_bound δ hlower N hsmall))
/-- Conditional structural upper bound independent of assumptions on zeta zeros. -/
theorem finiteDimensional_and_finrank_le_of_adjoint_lower_bound
    (δ : ℝ) (hlower : ∀ w : W, δ * ‖w‖ ≤ ‖coupling.adjoint w‖)
    (N : ℕ) (hN : (1 / zetaTwo) / ((N : ℝ) + 1) < δ) :
    FiniteDimensional ℝ W ∧ Module.finrank ℝ W ≤ N := by
  have hh := physicalHeadUnique_of_adjoint_lower_bound δ hlower N hN
  exact ⟨finiteDimensional_of_headUnique coordinates N ((physicalHeadUnique_iff N).mp hh),
    finrank_le_of_physicalHeadUnique N hh⟩


#print axioms exists_unit_head_zero_small_adjoint
#print axioms coupling_adjoint_injective
#print axioms coupling_dense_range
#print axioms coupling_adjoint_tail_bound
#print axioms coupling_surjective_iff_finite_head
#print axioms coupling_surjective_iff_finiteDimensional

end RiemannResearch.RH.QDensityCouplingSurjectivity
