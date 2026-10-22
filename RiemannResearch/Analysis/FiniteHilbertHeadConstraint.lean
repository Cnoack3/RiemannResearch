import RiemannResearch.Analysis.FiniteHilbertGramProjection
import Mathlib.Tactic.FieldSimp

/-!
# Exact finite corrections with one preserved observation

Source: independently assembled from the user's Pareto parity-closure handoff,
21 September 2026. This supplies the finite Hilbert minimization and refinement
identities needed when the even correction dictionary grows independently of
the arithmetic candidate. Every original inner product is retained.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteHilbertGram
variable {ι κ H : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def headProjection {v : ι → H} (hv : LinearIndependent ℝ v) (z : H) : H :=
  Fintype.linearCombination ℝ v (inverseCoeff hv z)

def headConstrainedCoeff {v : ι → H} (hv : LinearIndependent ℝ v) (f z : H) : ι → ℝ :=
  -inverseCoeff hv f -
    (inner ℝ (f - headProjection hv f) z / ‖headProjection hv z‖^2) • inverseCoeff hv z

def headConstrainedResidual {v : ι → H} (hv : LinearIndependent ℝ v) (f z : H) : H :=
  f + Fintype.linearCombination ℝ v (headConstrainedCoeff hv f z)

variable {v : ι → H}

theorem headProjection_inner (hv : LinearIndependent ℝ v) (z : H) :
    inner ℝ (headProjection hv z) z = ‖headProjection hv z‖^2 := by
  have h := residual_orthogonal hv z (inverseCoeff hv z)
  change inner ℝ (z - headProjection hv z) (headProjection hv z) = 0 at h
  rw [inner_sub_left, real_inner_self_eq_norm_sq, real_inner_comm] at h
  linarith

theorem headProjection_observation (hv : LinearIndependent ℝ v) (z : H) (c : ι → ℝ) :
    inner ℝ (Fintype.linearCombination ℝ v c) (headProjection hv z) =
      inner ℝ (Fintype.linearCombination ℝ v c) z := by
  rw [inner_synthesis_left, inner_synthesis_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [headProjection, inverseCoeff_normal]
  rfl

theorem headConstrainedResidual_eq (hv : LinearIndependent ℝ v) (f z : H) :
    headConstrainedResidual hv f z = f - headProjection hv f -
      (inner ℝ (f - headProjection hv f) z / ‖headProjection hv z‖^2) •
        headProjection hv z := by
  simp only [headConstrainedResidual, headConstrainedCoeff, map_sub, map_neg, map_smul]
  unfold headProjection
  abel

theorem headConstrainedResidual_observation (hv : LinearIndependent ℝ v) (f z : H)
    (hK : ‖headProjection hv z‖^2 ≠ 0) :
    inner ℝ (headConstrainedResidual hv f z) z = 0 := by
  rw [headConstrainedResidual_eq, inner_sub_left, real_inner_smul_left, headProjection_inner]
  exact sub_eq_zero.mpr (div_mul_cancel₀ _ hK).symm

theorem headConstrainedResidual_orthogonal (hv : LinearIndependent ℝ v) (f z : H)
    (c : ι → ℝ) (hc : inner ℝ (Fintype.linearCombination ℝ v c) z = 0) :
    inner ℝ (headConstrainedResidual hv f z) (Fintype.linearCombination ℝ v c) = 0 := by
  rw [headConstrainedResidual_eq, inner_sub_left, real_inner_smul_left]
  have h := residual_orthogonal hv f c
  change inner ℝ (f - headProjection hv f) (Fintype.linearCombination ℝ v c) = 0 at h
  rw [h, real_inner_comm (Fintype.linearCombination ℝ v c) (headProjection hv z),
    headProjection_observation, hc]
  ring

theorem headConstrainedResidual_energy (hv : LinearIndependent ℝ v) (f z : H)
    (hK : ‖headProjection hv z‖^2 ≠ 0) :
    ‖headConstrainedResidual hv f z‖^2 = ‖f - headProjection hv f‖^2 +
      (inner ℝ (f - headProjection hv f) z)^2 / ‖headProjection hv z‖^2 := by
  rw [headConstrainedResidual_eq, norm_sub_sq_real, inner_smul_right]
  have h := residual_orthogonal hv f (inverseCoeff hv z)
  change inner ℝ (f - headProjection hv f) (headProjection hv z) = 0 at h
  rw [h, mul_zero, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  field_simp [hK]
  <;> ring

theorem headConstrainedResidual_energy_completion (hv : LinearIndependent ℝ v)
    (f z : H) (hK : ‖headProjection hv z‖^2 ≠ 0) (c : ι → ℝ)
    (hc : inner ℝ (f + Fintype.linearCombination ℝ v c) z = 0) :
    ‖f + Fintype.linearCombination ℝ v c‖^2 = ‖headConstrainedResidual hv f z‖^2 +
      ‖Fintype.linearCombination ℝ v (c - headConstrainedCoeff hv f z)‖^2 := by
  have he : f + Fintype.linearCombination ℝ v c = headConstrainedResidual hv f z +
      Fintype.linearCombination ℝ v (c - headConstrainedCoeff hv f z) := by
    rw [headConstrainedResidual, map_sub]
    abel
  have hz := headConstrainedResidual_observation hv f z hK
  rw [he, inner_add_left, hz, zero_add] at hc
  rw [he, norm_add_sq_real, headConstrainedResidual_orthogonal hv f z _ hc]
  ring

theorem headConstrainedResidual_energy_le (hv : LinearIndependent ℝ v) (f z : H)
    (hK : ‖headProjection hv z‖^2 ≠ 0) (hf : inner ℝ f z = 0) :
    ‖headConstrainedResidual hv f z‖^2 ≤ ‖f‖^2 := by
  have h := headConstrainedResidual_energy_completion hv f z hK 0 (by simpa using hf)
  simp only [map_zero, add_zero] at h
  linarith [sq_nonneg ‖Fintype.linearCombination ℝ v (0 - headConstrainedCoeff hv f z)‖]

/-- Enlarging the correction space removes exactly the squared change in the optimizer. -/
theorem headConstrainedResidual_refinement {v : ι → H} {w : κ → H}
    (hv : LinearIndependent ℝ v) (hw : LinearIndependent ℝ w) (f z : H)
    (hvz : ‖headProjection hv z‖^2 ≠ 0) (hwz : ‖headProjection hw z‖^2 ≠ 0)
    (hvw : synthesisSpan v ≤ synthesisSpan w) :
    ‖headConstrainedResidual hv f z‖^2 = ‖headConstrainedResidual hw f z‖^2 +
      ‖headConstrainedResidual hv f z - headConstrainedResidual hw f z‖^2 := by
  have hm : headConstrainedResidual hv f z - headConstrainedResidual hw f z ∈
      synthesisSpan w := by
    have he : headConstrainedResidual hv f z - headConstrainedResidual hw f z =
        Fintype.linearCombination ℝ v (headConstrainedCoeff hv f z) -
          Fintype.linearCombination ℝ w (headConstrainedCoeff hw f z) := by
      unfold headConstrainedResidual
      abel
    rw [he]
    exact (synthesisSpan w).sub_mem (hvw (synthesis_mem v _)) (synthesis_mem w _)
  rw [synthesisSpan, ← Fintype.range_linearCombination] at hm
  obtain ⟨c, hc⟩ := hm
  have hz : inner ℝ (Fintype.linearCombination ℝ w c) z = 0 := by
    rw [hc, inner_sub_left, headConstrainedResidual_observation hv f z hvz,
      headConstrainedResidual_observation hw f z hwz, sub_self]
  have ho := headConstrainedResidual_orthogonal hw f z c hz
  rw [hc] at ho
  have he : headConstrainedResidual hv f z = headConstrainedResidual hw f z +
      (headConstrainedResidual hv f z - headConstrainedResidual hw f z) := by abel
  calc
    ‖headConstrainedResidual hv f z‖^2 = ‖headConstrainedResidual hw f z +
      (headConstrainedResidual hv f z - headConstrainedResidual hw f z)‖^2 := by rw [← he]
    _ = _ := by rw [norm_add_sq_real, ho]; ring

end RiemannResearch.Analysis.FiniteHilbertGram
