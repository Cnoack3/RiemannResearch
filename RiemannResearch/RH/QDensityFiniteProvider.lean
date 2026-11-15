import RiemannResearch.RH.QFiniteBoundedLift
import RiemannResearch.RH.QDensityLeakageArithmetic
import RiemannResearch.RH.QDensityLeakage
import RiemannResearch.RH.QDensityAugmentedSpan
import RiemannResearch.RH.QDensityMetric
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QConductorEstimates
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Explicit finite density trials and their optimal asymptotic error

Source: independently developed continuation of the repository's
PQNormalizedLeakage Priority 1 finite-approximation provider, following
Christian Noack's request to prove repository obligations from easiest
to hardest, 14 November 2026. The inverse-Gram candidates and normalized
leakage limits are reused from their owning modules.

Let u_N be the complete-Q inverse-Gram projection of one onto conductors
2 through N+1. The finite trial is
  a_(k,N) = g_k / zetaTwo + u_N / (zetaTwo * k).
Its exact scaled error is
  zetaTwo * k * (B g_k - a_(k,N)) = k D g_k - u_N.
For independently cofinal k and N, this converges to the actual constant
residual r = one - Pi_V one. The resulting normalized norm limit is optimal
among all legal competitors having a normalized error limit.

The exact Pythagorean remainder is retained. The finite-approximation
provider exists with small-o(1/k) error exactly when one belongs to V; its
witness can always be the displayed trial with N=j. Existence of this
small-o rate remains Open. Neither the unconditional O(1/k) estimate nor
asymptotic optimality supplies the vanishing of r or an unconditional RH
proof. All norms include the infinite physical Q tail.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QDensityFiniteProvider
open ZetaTwoHilbert ZetaTwoProbability QFullResidueProjection QDensityMetric
open QDensityLeakage

/-- A finite inverse-Gram trial for the moving density atom. -/
def trial (k N : ℕ) : QHilbert :=
  (1 / zetaTwo) • qResidue k +
    (1 / (zetaTwo * (k : ℝ))) • candidate N

theorem trial_mem_legalSpan (k N : ℕ) (hk : 2 ≤ k) :
    trial k N ∈ legalSpan := by
  apply legalSpan.add_mem
  · apply legalSpan.smul_mem
    exact Submodule.subset_span
      ⟨k - 2, congrArg qResidue (Nat.sub_add_cancel hk)⟩
  · exact legalSpan.smul_mem _ (candidate_mem_legalSpan N)

theorem trial_error_identity (k N : ℕ) (hk : 0 < k) :
    (zetaTwo * (k : ℝ)) • (B (qResidue k) - trial k N) =
      approximation k - candidate N := by
  have hz : zetaTwo ≠ 0 := ne_of_gt zetaTwo_pos
  have hkr : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  rw [trial, smul_sub, smul_add, smul_smul, smul_smul,
    mul_one_div_cancel (mul_ne_zero hz hkr)]
  have he : zetaTwo * (k : ℝ) * (1 / zetaTwo) = (k : ℝ) := by
    field_simp
  rw [he, one_smul, approximation_eq_density_combination]
  module

theorem trial_scaled_error_tendsto (k N : ℕ → ℕ)
    (hk : Tendsto k atTop atTop) (hN : Tendsto N atTop atTop) :
    Tendsto (fun j => (zetaTwo * (k j : ℝ)) •
      (B (qResidue (k j)) - trial (k j) (N j))) atTop
      (𝓝 (qOne - closure.starProjection qOne)) := by
  have ht := (approximation_tendsto.comp hk).sub (candidate_tendsto_projection.comp hN)
  apply ht.congr'
  filter_upwards [hk.eventually (eventually_ge_atTop 1)] with j hj
  exact (trial_error_identity (k j) (N j) hj).symm

theorem trial_scaled_norm_tendsto (k N : ℕ → ℕ)
    (hk : Tendsto k atTop atTop) (hN : Tendsto N atTop atTop) :
    Tendsto (fun j => (zetaTwo * (k j : ℝ)) *
      ‖B (qResidue (k j)) - trial (k j) (N j)‖) atTop
      (𝓝 ‖qOne - closure.starProjection qOne‖) := by
  have hZ := zetaTwo_pos
  convert (trial_scaled_error_tendsto k N hk hN).norm using 1
  ext j
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem leakage_le_legal_error (k : ℕ) (a : QHilbert) (ha : a ∈ closure) :
    ‖leakage (qResidue k)‖ ≤ ‖B (qResidue k) - a‖ := by
  have hp := closureᗮ.norm_starProjection_apply_le (B (qResidue k) - a)
  simpa only [map_sub, Submodule.starProjection_orthogonal_apply_eq_zero ha,
    sub_zero, Submodule.starProjection_orthogonal_val, leakage] using hp

theorem legal_error_pythagoras (k : ℕ) (a : QHilbert) (ha : a ∈ closure) :
    ‖B (qResidue k) - a‖ ^ 2 =
      ‖leakage (qResidue k)‖ ^ 2 +
        ‖closure.starProjection (B (qResidue k)) - a‖ ^ 2 := by
  have ho := Submodule.inner_right_of_mem_orthogonal
    (closure.sub_mem (closure.starProjection_apply_mem (B (qResidue k))) ha)
    (Submodule.sub_starProjection_mem_orthogonal (K := closure) (B (qResidue k)))
  rw [real_inner_comm] at ho
  have he : B (qResidue k) - a =
      (B (qResidue k) - closure.starProjection (B (qResidue k))) +
        (closure.starProjection (B (qResidue k)) - a) := by module
  rw [he, norm_add_sq_real, ho]
  unfold leakage
  ring

theorem legal_error_lower_certificate (k : ℕ) (hk : 2 ≤ k)
    (a : QHilbert) (ha : a ∈ closure) :
    ‖qOne - closure.starProjection qOne‖ -
        Real.sqrt (1 / (zetaTwo * (k - 1 : ℕ))) ≤
      (zetaTwo * (k : ℝ)) * ‖B (qResidue k) - a‖ := by
  have hZ := zetaTwo_pos
  have he := Real.le_sqrt_of_sq_le
    (QDensityLeakageArithmetic.scaled_leakage_error_norm_sq_le k hk)
  have ht := norm_sub_norm_le
    (qOne - closure.starProjection qOne)
    ((zetaTwo * (k : ℝ)) • leakage (qResidue k))
  rw [norm_sub_rev (qOne - closure.starProjection qOne)
    ((zetaTwo * (k : ℝ)) • leakage (qResidue k))] at ht
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at ht
  have hb := mul_le_mul_of_nonneg_left (leakage_le_legal_error k a ha)
    (show 0 ≤ zetaTwo * (k : ℝ) by positivity)
  linarith

theorem trial_optimality_gap_tendsto (k N : ℕ → ℕ)
    (hk : Tendsto k atTop atTop) (hN : Tendsto N atTop atTop) :
    Tendsto (fun j => (zetaTwo * (k j : ℝ)) *
      (‖B (qResidue (k j)) - trial (k j) (N j)‖ -
        ‖leakage (qResidue (k j))‖)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, mul_sub, sub_self] using
    (trial_scaled_norm_tendsto k N hk hN).sub
      (scaled_residue_leakage_norm_tendsto.comp hk)

theorem one_mem_iff_finite_provider (k : ℕ → ℕ)
    (hk : Tendsto k atTop atTop) (hk2 : ∀ j, 2 ≤ k j) :
    qOne ∈ closure ↔ ∃ a : ℕ → QHilbert,
      (∀ j, a j ∈ legalSpan) ∧
      Tendsto (fun j => (k j : ℝ) * ‖B (qResidue (k j)) - a j‖)
        atTop (𝓝 0) := by
  constructor
  · intro hmem
    refine ⟨fun j => trial (k j) j,
      fun j => trial_mem_legalSpan (k j) j (hk2 j), ?_⟩
    have ht := trial_scaled_norm_tendsto k id hk tendsto_id
    have ht0 : Tendsto (fun j => (zetaTwo * (k j : ℝ)) *
      ‖B (qResidue (k j)) - trial (k j) j‖) atTop (𝓝 0) := by
      simpa only [id_eq, Submodule.starProjection_eq_self_iff.mpr hmem,
        sub_self, norm_zero] using ht
    have hscale := ht0.const_mul (1 / zetaTwo)
    have he : ∀ j, (1 / zetaTwo) * ((zetaTwo * (k j : ℝ)) *
      ‖B (qResidue (k j)) - trial (k j) j‖) =
      (k j : ℝ) * ‖B (qResidue (k j)) - trial (k j) j‖ := by
      intro j
      field_simp [ne_of_gt zetaTwo_pos]
    simpa only [he, mul_zero] using hscale
  · rintro ⟨a, ha, ht⟩
    have hlo : Tendsto (fun j => (k j : ℝ) *
      ‖leakage (qResidue (k j))‖) atTop (𝓝 0) :=
      squeeze_zero (fun _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
        (fun j => mul_le_mul_of_nonneg_left
          (leakage_le_legal_error (k j) (a j) (legalSpan.le_topologicalClosure (ha j)))
          (Nat.cast_nonneg _)) ht
    have hloZ : Tendsto (fun j => (zetaTwo * (k j : ℝ)) *
      ‖leakage (qResidue (k j))‖) atTop (𝓝 0) := by
      simpa only [mul_zero, mul_assoc] using hlo.const_mul zetaTwo
    have he := tendsto_nhds_unique
      (scaled_residue_leakage_norm_tendsto.comp hk) hloZ
    exact Submodule.starProjection_eq_self_iff.mp
      (sub_eq_zero.mp (norm_eq_zero.mp he)).symm


/-- A uniform complete-norm bound, valid without totality and at every stage. -/
theorem trial_error_norm_le (k N : ℕ) (hk : 0 < k) :
    ‖B (qResidue k) - trial k N‖ ≤ 2 / (zetaTwo * (k : ℝ)) := by
  have hZ := zetaTwo_pos
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have ha : ‖approximation k‖ ≤ 1 := by
    apply qNorm_le_of_physical_bound _ 1 zero_le_one
    intro n
    have hb := approximation_sequence_bounds k n hk
    rw [abs_of_nonneg hb.1]
    exact hb.2
  have hb := (norm_sub_le (approximation k) (candidate N)).trans
    (add_le_add ha (candidate_norm_le_one N))
  have hi := congrArg norm (trial_error_identity k N hk)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hZ hkR)] at hi
  apply (le_div_iff₀ (mul_pos hZ hkR)).mpr
  nlinarith

/-- The scaled discrepancy from the infinite best projection vanishes. -/
theorem trial_projection_gap_tendsto (k N : ℕ → ℕ)
    (hk : Tendsto k atTop atTop) (hN : Tendsto N atTop atTop) :
    Tendsto (fun j => (zetaTwo * (k j : ℝ)) •
      (closure.starProjection (B (qResidue (k j))) - trial (k j) (N j)))
      atTop (𝓝 0) := by
  have ht := (trial_scaled_error_tendsto k N hk hN).sub
    (scaled_residue_leakage_tendsto.comp hk)
  have he : ∀ j, (zetaTwo * (k j : ℝ)) •
      (B (qResidue (k j)) - trial (k j) (N j)) -
      (zetaTwo * (k j : ℝ)) • leakage (qResidue (k j)) =
      (zetaTwo * (k j : ℝ)) •
        (closure.starProjection (B (qResidue (k j))) - trial (k j) (N j)) := by
    intro j
    unfold leakage
    module
  simpa only [Function.comp_def, he, sub_self] using ht

/-- If the residual is nonzero, one common positive lower bound applies to
every legal competitor at all sufficiently large conductors. -/
theorem eventually_all_legal_error_lower (hne : qOne ∉ closure) :
    ∀ᶠ k : ℕ in atTop, ∀ a : QHilbert, a ∈ closure →
      ‖qOne - closure.starProjection qOne‖ / 2 ≤
        (zetaTwo * (k : ℝ)) * ‖B (qResidue k) - a‖ := by
  have hr : 0 < ‖qOne - closure.starProjection qOne‖ := by
    apply norm_pos_iff.mpr
    intro he
    exact hne (Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp he).symm)
  have ht := scaled_residue_leakage_norm_tendsto.eventually
    (lt_mem_nhds (show ‖qOne - closure.starProjection qOne‖ / 2 <
      ‖qOne - closure.starProjection qOne‖ by linarith))
  filter_upwards [ht] with k hk a ha
  have hZ := zetaTwo_pos
  exact hk.le.trans (mul_le_mul_of_nonneg_left
    (leakage_le_legal_error k a ha) (by positivity))

/-- No convergent normalized legal error can have a smaller limit. -/
theorem residual_norm_le_error_limit (k : ℕ → ℕ)
    (hk : Tendsto k atTop atTop) (a : ℕ → QHilbert)
    (ha : ∀ j, a j ∈ closure) (L : ℝ)
    (hlim : Tendsto (fun j => (zetaTwo * (k j : ℝ)) *
      ‖B (qResidue (k j)) - a j‖) atTop (𝓝 L)) :
    ‖qOne - closure.starProjection qOne‖ ≤ L := by
  have hZ := zetaTwo_pos
  exact le_of_tendsto_of_tendsto'
    (scaled_residue_leakage_norm_tendsto.comp hk) hlim
    (fun j => mul_le_mul_of_nonneg_left
      (leakage_le_legal_error (k j) (a j) (ha j)) (by positivity))

/-- info: 'RiemannResearch.RH.QDensityFiniteProvider.trial_error_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms trial_error_identity

/-- info: 'RiemannResearch.RH.QDensityFiniteProvider.trial_scaled_error_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms trial_scaled_error_tendsto

/-- info: 'RiemannResearch.RH.QDensityFiniteProvider.legal_error_pythagoras' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms legal_error_pythagoras

/-- info: 'RiemannResearch.RH.QDensityFiniteProvider.legal_error_lower_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms legal_error_lower_certificate

/-- info: 'RiemannResearch.RH.QDensityFiniteProvider.trial_optimality_gap_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms trial_optimality_gap_tendsto

/-- info: 'RiemannResearch.RH.QDensityFiniteProvider.one_mem_iff_finite_provider' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms one_mem_iff_finite_provider

/-- info: 'RiemannResearch.RH.QDensityFiniteProvider.trial_error_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms trial_error_norm_le

/-- info: 'RiemannResearch.RH.QDensityFiniteProvider.trial_projection_gap_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms trial_projection_gap_tendsto

/-- info: 'RiemannResearch.RH.QDensityFiniteProvider.eventually_all_legal_error_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eventually_all_legal_error_lower

/-- info: 'RiemannResearch.RH.QDensityFiniteProvider.residual_norm_le_error_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms residual_norm_le_error_limit

end RiemannResearch.RH.QDensityFiniteProvider
