import RiemannResearch.RH.QDensityMetricInverse
import RiemannResearch.RH.QFullTargetTotality
import RiemannResearch.RH.QDensityParityApproximation
import RiemannResearch.RH.QFullResidueProjection
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Abel
import RiemannResearch.RH.QDensityAugmentedSpan
import RiemannResearch.RH.QDensityMetric
import RiemannResearch.RH.QReciprocalMetric
import RiemannResearch.RH.QConductorEstimates
import RiemannResearch.RH.QOptimizerParityRH
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact density leakage and its parity diagnostic

Source: PQ_Density_Operators_and_RH_Agenda.pdf, agendas 4 and 5,
12 November 2026. The leakage is in the complete Q norm.
Zero leakage is characterized, never supplied as an arithmetic hypothesis.

Further source: the user's projected-generator question, 13 November 2026.
The residue-quotient approximants give an unconditional normalized leakage
limit and inverse-conductor bound. The limiting constant residual is retained;
its vanishing is the explicitly open arithmetic premise in the RH reduction.
-/

noncomputable section
open Filter
open scoped Topology
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

/-- Vanishing of every projected density atom is precisely the constant-target condition. -/
theorem residue_leakage_vanishes_iff_one_mem :
    (∀ k : ℕ, 2 ≤ k → leakage (qResidue k) = 0) ↔ qOne ∈ closure := by
  simp_rw [leakage_eq_zero_iff]
  exact QFullTargetTotality.one_mem_iff_all_density_generators.symm

/-- The scaled density leakage is exactly the residual of the residue-quotient approximant. -/
theorem scaled_residue_leakage_eq (k : ℕ) (hk : 2 ≤ k) :
    (zetaTwo * (k : ℝ)) • leakage (qResidue k) =
      approximation k - closure.starProjection (approximation k) := by
  have hg : qResidue k ∈ closure :=
    legalSpan.le_topologicalClosure (Submodule.subset_span
      ⟨k - 2, congrArg qResidue (Nat.sub_add_cancel hk)⟩)
  rw [approximation, map_smul, ← smul_sub, reciprocal_leakage (qResidue k) hg,
    smul_smul]
  congr 1
  ring

/-- Unconditional vector limit; the constant residual is retained. -/
theorem scaled_residue_leakage_tendsto :
    Tendsto (fun k : ℕ => (zetaTwo * (k : ℝ)) • leakage (qResidue k))
      atTop (𝓝 (qOne - closure.starProjection qOne)) := by
  have ht := approximation_tendsto.sub
    ((closure.starProjection.continuous.tendsto qOne).comp approximation_tendsto)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 2] with k hk
  exact (scaled_residue_leakage_eq k hk).symm

/-- An extra zero limit is equivalent to the unresolved constant-target membership. -/
theorem scaled_residue_leakage_tendsto_zero_iff :
    Tendsto (fun k : ℕ => (zetaTwo * (k : ℝ)) • leakage (qResidue k))
      atTop (𝓝 0) ↔ qOne ∈ closure := by
  constructor
  · intro h
    have he := tendsto_nhds_unique scaled_residue_leakage_tendsto h
    exact Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp he).symm
  · intro h
    simpa only [Submodule.starProjection_eq_self_iff.mpr h, sub_self] using
      scaled_residue_leakage_tendsto

/-- Conditional research reduction: the zero-limit hypothesis remains Open. -/
theorem riemannHypothesis_of_scaled_residue_leakage_tendsto_zero
    (h : Tendsto (fun k : ℕ => (zetaTwo * (k : ℝ)) • leakage (qResidue k))
      atTop (𝓝 0)) : RiemannHypothesis :=
  riemannHypothesis_of_qOne_mem_full_closure
    (scaled_residue_leakage_tendsto_zero_iff.mp h)

#print axioms scaled_residue_leakage_tendsto
#print axioms scaled_residue_leakage_tendsto_zero_iff
#print axioms riemannHypothesis_of_scaled_residue_leakage_tendsto_zero

/-- Exact signed error identity, with the complete orthogonal remainder. -/
theorem scaled_residue_leakage_error_eq (k : ℕ) (hk : 2 ≤ k) :
    (zetaTwo * (k : ℝ)) • leakage (qResidue k) -
        (qOne - closure.starProjection qOne) =
      closureᗮ.starProjection (approximation k - qOne) := by
  rw [scaled_residue_leakage_eq k hk, map_sub,
    Submodule.starProjection_orthogonal_val, Submodule.starProjection_orthogonal_val]

/-- Projection contracts the complete approximation error. -/
theorem scaled_residue_leakage_error_norm_le (k : ℕ) (hk : 2 ≤ k) :
    ‖(zetaTwo * (k : ℝ)) • leakage (qResidue k) -
        (qOne - closure.starProjection qOne)‖ ≤ ‖approximation k - qOne‖ := by
  rw [scaled_residue_leakage_error_eq k hk]
  exact closureᗮ.norm_starProjection_apply_le _

/-- Unconditional inverse-conductor bound; decay does not imply exact vanishing. -/
theorem residue_leakage_norm_le (k : ℕ) (hk : 2 ≤ k) :
    ‖leakage (qResidue k)‖ ≤ 1 / (zetaTwo * (k : ℝ)) := by
  have hk0 : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hZ := zetaTwo_pos
  have ha : ‖approximation k‖ ≤ 1 := by
    apply qNorm_le_of_physical_bound _ 1 zero_le_one
    intro n
    have hb := approximation_sequence_bounds k n hk0
    rw [abs_of_nonneg hb.1]
    exact hb.2
  have hp := (closureᗮ.norm_starProjection_apply_le (approximation k)).trans ha
  rw [Submodule.starProjection_orthogonal_val,
    ← scaled_residue_leakage_eq k hk, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < zetaTwo * (k : ℝ))] at hp
  apply (le_div_iff₀ (by positivity : 0 < zetaTwo * (k : ℝ))).mpr
  simpa only [mul_comm] using hp

/-- The normalized norms converge to the norm of the constant residual. -/
theorem scaled_residue_leakage_norm_tendsto :
    Tendsto (fun k : ℕ => (zetaTwo * (k : ℝ)) * ‖leakage (qResidue k)‖)
      atTop (𝓝 ‖qOne - closure.starProjection qOne‖) := by
  have hZ := zetaTwo_pos
  convert scaled_residue_leakage_tendsto.norm using 1
  ext k
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

#print axioms residue_leakage_norm_le
#print axioms scaled_residue_leakage_error_eq

end RiemannResearch.RH.QDensityLeakage
