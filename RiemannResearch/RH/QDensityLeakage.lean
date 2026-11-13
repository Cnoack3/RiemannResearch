import RiemannResearch.RH.QDensityMetricInverse
import RiemannResearch.RH.QFullTargetTotality
import RiemannResearch.RH.QDensityParityApproximation
import RiemannResearch.RH.QFullResidueProjection
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Abel

/-!
# Exact density leakage and its parity diagnostic

Source: PQ_Density_Operators_and_RH_Agenda.pdf, agendas 4 and 5,
12 November 2026. The leakage is in the complete Q norm.
Zero leakage is characterized, never supplied as an arithmetic hypothesis.
-/

noncomputable section
namespace RiemannResearch.RH.QDensityLeakage
open ZetaTwoHilbert ZetaTwoProbability QFullResidueProjection
open QDensityMetric QReciprocalMetric QDensityMetricInverse

def leakage (f : QHilbert) : QHilbert :=
  B f - closure.starProjection (B f)

theorem reciprocal_leakage (f : QHilbert) (hf : f ∈ closure) :
    D f - closure.starProjection (D f) = zetaTwo • leakage f := by
  rw [D_eq_density, map_sub, map_smul, Submodule.starProjection_eq_self_iff.mpr hf]
  unfold leakage
  rw [smul_sub]
  abel

theorem leakage_eq_zero_iff (f : QHilbert) :
    leakage f = 0 ↔ B f ∈ closure := by
  unfold leakage
  rw [sub_eq_zero]
  exact eq_comm.trans Submodule.starProjection_eq_self_iff

theorem leakage_vanishes_iff_one_mem :
    (∀ f ∈ closure, leakage f = 0) ↔ qOne ∈ closure := by
  simp_rw [leakage_eq_zero_iff]
  exact QFullTargetTotality.one_mem_iff_density_invariant.symm

/-- An exact annihilator equation; the projected remainder is retained. -/
theorem orthogonal_pairing (u f : QHilbert) (hu : u ∈ closureᗮ) (hf : f ∈ closure) :
    inner ℝ u (D f) = zetaTwo * inner ℝ u (leakage f) := by
  have hp := Submodule.inner_right_of_mem_orthogonal
    (closure.starProjection_apply_mem (D f)) hu
  have he := congrArg (fun x : QHilbert => inner ℝ u x) (reciprocal_leakage f hf)
  have hp' : inner ℝ u (closure.starProjection (D f)) = 0 := by
    rw [real_inner_comm, hp]
  rw [inner_sub_right, inner_smul_right, hp', sub_zero] at he
  exact he

theorem parity_leakage_eq_zero_iff :
    leakage (qResidue 2) = 0 ↔ QDensityParityApproximation.oddReciprocal ∈ closure :=
  (leakage_eq_zero_iff _).trans QDensityParityApproximation.density_two_mem_closure_iff

/-- Saturation of the parity information is exactly vanishing of one leakage vector. -/
theorem parity_saturation_iff :
    Filter.Tendsto QDensityParityApproximation.targetInformation Filter.atTop
      (nhds (Real.pi ^ 2 / 64)) ↔ leakage (qResidue 2) = 0 :=
  QDensityParityApproximation.targetInformation_tendsto_pi_iff.trans
    (leakage_eq_zero_iff _).symm

end RiemannResearch.RH.QDensityLeakage
