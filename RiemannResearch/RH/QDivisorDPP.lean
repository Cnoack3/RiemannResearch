import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import RiemannResearch.Analysis.ProjectionDPPKernel
import RiemannResearch.Probability.DeterminantalExistence
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ext

/-!
# The complete Q divisor basis and full occupation

Source: user-provided Q/DPP discussion, 13 October 2026. The complete
orthonormal divisor basis is unconditional. Its finite projections tend to
the identity. These are the full divisor basis, not the legal residue family.
Physical integer n+1 is counting coordinate n throughout.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology Classical BigOperators

namespace RiemannResearch.RH.QDivisorDPP
open ZetaTwoHilbert QDivisorHilbert
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.ProjectionDPP
open RiemannResearch.Probability.DPP

def basisIndex (n : ℕ) : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩

theorem basisIndex_surjective : Function.Surjective basisIndex := by
  intro r
  refine ⟨(r : ℕ) - 1, ?_⟩
  apply Subtype.ext
  change ((r : ℕ) - 1) + 1 = (r : ℕ)
  exact Nat.sub_add_cancel r.pos

def basisSpace (N : ℕ) : Submodule ℝ QHilbert :=
  walkSpan normalizedDivisorWavelet basisIndex N

instance basisSpace_finiteDimensional (N : ℕ) :
    FiniteDimensional ℝ (basisSpace N) := by
  unfold basisSpace
  infer_instance

theorem basisSpace_mono : Monotone basisSpace :=
  walkSpan_mono normalizedDivisorWavelet basisIndex

def countingBasis (n : ℕ) : QHilbert := lp.single 2 n (1 : ℝ)

theorem countingBasis_inner (i j : ℕ) :
    inner ℝ (countingBasis i) (countingBasis j) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [countingBasis, lp.inner_single_left]
  · simp [countingBasis, lp.inner_single_left, hij]

theorem countingBasis_norm_sq (i : ℕ) : ‖countingBasis i‖ ^ 2 = 1 := by
  rw [← real_inner_self_eq_norm_sq, countingBasis_inner]
  simp

def basisKernel (N i j : ℕ) : ℝ :=
  kernel (basisSpace N) countingBasis i j

theorem basisProjection_tendsto (f : QHilbert) :
    Tendsto (fun N => (basisSpace N).starProjection f) atTop (𝓝 f) := by
  have he : (dictionaryClosure normalizedDivisorWavelet).starProjection f = f := by
    apply Submodule.starProjection_eq_self_iff.mpr
    rw [dictionaryClosure, normalizedDivisorWavelet_span_dense]
    trivial
  simpa only [basisSpace, he] using
    walkProjection_tendsto normalizedDivisorWavelet basisIndex basisIndex_surjective f

/-- The unscaled full-basis kernel tends to the identity, unconditionally. -/
theorem basisKernel_tendsto (i j : ℕ) :
    Tendsto (fun N => basisKernel N i j) atTop
      (𝓝 (if i = j then (1 : ℝ) else 0)) := by
  simpa only [basisKernel, kernel, countingBasis_inner] using
    (basisProjection_tendsto (countingBasis i)).inner (𝕜 := ℝ)
      (basisProjection_tendsto (countingBasis j))

/-- Exact vacancy energy, before taking the limit. -/
theorem basisKernel_vacancy_energy (N i : ℕ) :
    1 - basisKernel N i i =
      ‖countingBasis i - (basisSpace N).starProjection (countingBasis i)‖ ^ 2 := by
  have h := holeKernel_diagonal (basisSpace N) countingBasis i
  rw [holeKernel_eq, real_inner_self_eq_norm_sq, countingBasis_norm_sq] at h
  exact h

def basisLaw (N : ℕ) : Measure (ℕ → Bool) :=
  contractionDPP (basisKernel N)
    (fun I => principal_posSemidef (basisSpace N) countingBasis (fun i : I => i.1))
    (fun I => by
      have h := identity_sub_principal_posSemidef (basisSpace N) countingBasis
        (fun i : I => i.1) (by intro i j; simp [countingBasis_inner])
      convert h using 1 <;> ext i j <;>
        simp [Matrix.sub_apply, Matrix.one_apply, basisKernel, kernel])

instance basisLaw_probability (N : ℕ) : IsProbabilityMeasure (basisLaw N) := by
  unfold basisLaw
  exact contractionDPP_probability _ _ _

theorem basisLaw_isDPP (N : ℕ) :
    IsDPP (basisLaw N) (fun x => {i | x i = true}) (basisKernel N) :=
  contractionDPP_isDPP _ _ _

theorem basisLaw_vacancy_energy (N i : ℕ) :
    (basisLaw N).real {x | x i = false} =
      ‖countingBasis i - (basisSpace N).starProjection (countingBasis i)‖ ^ 2 := by
  have h := (basisLaw_isDPP N).vacancy i
  simpa [basisKernel_vacancy_energy] using h

theorem basisLaw_occupation_tendsto (i : ℕ) :
    Tendsto (fun N => (basisLaw N).real {x | x i = true}) atTop (𝓝 1) := by
  have he (N : ℕ) : (basisLaw N).real {x | x i = true} = basisKernel N i i :=
    (basisLaw_isDPP N).occupation i
  simpa [he] using basisKernel_tendsto i i

/-- Every fixed finite list of distinct integers is filled in probability.
The window is fixed before dimension tends to infinity. -/
theorem basisLaw_finite_occupation_tendsto (m : ℕ) (e : Fin m ↪ ℕ) :
    Tendsto (fun N => (basisLaw N).real {x | ∀ i, x (e i) = true})
      atTop (𝓝 1) := by
  have hK : Tendsto (fun N => Matrix.of (fun i j : Fin m =>
      basisKernel N (e i) (e j))) atTop (𝓝 (1 : Matrix (Fin m) (Fin m) ℝ)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    simpa only [Matrix.of_apply, Matrix.one_apply, e.injective.eq_iff] using
      basisKernel_tendsto (e i) (e j)
  have hdet : Continuous (fun A : Matrix (Fin m) (Fin m) ℝ => A.det) :=
    continuous_id.matrix_det
  have h := (hdet.tendsto (1 : Matrix (Fin m) (Fin m) ℝ)).comp hK
  have hc (N : ℕ) : (basisLaw N).real {x | ∀ i, x (e i) = true} =
      (Matrix.of (fun i j : Fin m => basisKernel N (e i) (e j))).det :=
    (basisLaw_isDPP N).correlation m e
  simpa only [hc, Matrix.det_one, Function.comp_def] using h

theorem basisIndex_injective : Function.Injective basisIndex := by
  intro m n h
  have hv := congrArg (fun r : ℕ+ => r.val) h
  dsimp [basisIndex] at hv
  exact Nat.add_right_cancel hv

theorem basisPrefix_orthonormal (N : ℕ) :
    Orthonormal ℝ (fun r : Fin N => normalizedDivisorWavelet (basisIndex r)) := by
  rw [orthonormal_iff_ite]
  intro i j
  have h := (orthonormal_iff_ite.mp normalizedDivisorWavelet_orthonormal)
    (basisIndex i) (basisIndex j)
  have he : basisIndex (i : ℕ) = basisIndex (j : ℕ) ↔ i = j := by
    constructor
    · intro hij
      exact Fin.ext (basisIndex_injective hij)
    · intro hij
      subst j
      rfl
  simpa only [he] using h

/-- Exact finite sum in counting coordinates. Each normalized wavelet already
contains the square root of the physical Q mass. -/
theorem basisKernel_eq_sum (N i j : ℕ) :
    basisKernel N i j = ∑ r : Fin N,
      normalizedDivisorWavelet (basisIndex r) i *
        normalizedDivisorWavelet (basisIndex r) j := by
  let v : Fin N → QHilbert := fun r => normalizedDivisorWavelet (basisIndex r)
  have hv : Orthonormal ℝ v := basisPrefix_orthonormal N
  have hp (f : QHilbert) : (basisSpace N).starProjection f =
      ∑ r : Fin N, inner ℝ (v r) f • v r := by
    exact RiemannResearch.Analysis.FiniteHilbertGram.projection_eq_orthonormal_sum hv f
  have hc (r : Fin N) (k : ℕ) : inner ℝ (v r) (countingBasis k) = v r k := by
    rw [real_inner_comm]
    simp [countingBasis, lp.inner_single_left]
  unfold basisKernel kernel
  rw [hp (countingBasis i), hp (countingBasis j)]
  simpa only [sum_inner, real_inner_smul_left, hv.inner_right_fintype, hc, v]

end RiemannResearch.RH.QDivisorDPP
