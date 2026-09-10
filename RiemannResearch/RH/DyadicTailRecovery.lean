import RiemannResearch.RH.DyadicTailQuotient
import RiemannResearch.RH.ThresholdHilbertLegal

/-!
# Finite legal recovery in the actual dyadic tail quotient

Source: user-provided `DyadicRegularizedNormFormalization20260910(1).md`,
Recovery provider, and the September 10 continuation (N3)--(N4), Section 7.
The finite legal spaces and their full physical support are constructed here.
Recovery is conditional on scalar inner-product limits for the actual family;
this module does not provide the analytic Mellin limits or prove RH.
-/

namespace RiemannResearch.RH.Pareto

open scoped BigOperators
open Filter
noncomputable section

/-- Finite signed triadic combinations whose physical dilations are at least X. -/
def dyadicTailTriadicSpan (X : ℕ) : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ {f | ∃ m : ℕ, ∃ hm : 0 < m,
    X ≤ m ∧ f = hilbertDilation m hm (hilbertResidue 3 (by norm_num))}


/-- Every recovered raw lift belongs to the established physical legal space. -/
theorem dyadicTailTriadicSpan_le_hilbertLegalSubspace
    (X : ℕ) (A : Set ℕ) (h3 : 3 ∈ A) :
    dyadicTailTriadicSpan X ≤ hilbertLegalSubspace A := by
  apply Submodule.span_le.mpr
  rintro f ⟨m, hm, hXm, rfl⟩
  change hilbertSequence (hilbertDilation m hm (hilbertResidue 3 (by norm_num))) ∈
    legalSeedSpan A
  rw [hilbertDilation_sequence, hilbertResidue_sequence]
  exact dilation_generator_mem A h3 hm

/-- The actual projected finite legal space. A member retains a finite raw lift. -/
def dyadicTailProjectedTriadicSpan (X : ℕ) : Submodule ℝ ThresholdHilbert :=
  (dyadicTailTriadicSpan X).map (dyadicTailQuotientProjection X).toLinearMap

/-- Norm closure in the original weighted Hilbert space. -/
def dyadicTailProjectedTriadicClosure (X : ℕ) : Submodule ℝ ThresholdHilbert :=
  (dyadicTailProjectedTriadicSpan X).topologicalClosure

theorem dyadicTailTriadicSpan_le_physicalTail (X : ℕ) :
    dyadicTailTriadicSpan X ≤ dyadicPhysicalTail X := by
  apply Submodule.span_le.mpr
  rintro f ⟨m, hm, hXm, rfl⟩
  exact hilbertDilation_mem_dyadicPhysicalTail X m hm hXm _

theorem dyadicTailTriadicSpan_support (X : ℕ) (f : ThresholdHilbert)
    (hf : f ∈ dyadicTailTriadicSpan X) (k : ℕ) (hk : k < X) :
    hilbertSequence f k = 0 :=
  (mem_dyadicPhysicalTail_iff X f).mp
    (dyadicTailTriadicSpan_le_physicalTail X hf) k hk

theorem dyadicTailProjectedTriadicSpan_le_quotient (X : ℕ) :
    dyadicTailProjectedTriadicSpan X ≤ dyadicTailQuotientSubspace X := by
  rintro g ⟨f, hf, rfl⟩
  exact dyadicTailQuotientProjection_mem X f

theorem dyadicTailProjectedTriadicClosure_le_quotient (X : ℕ) :
    dyadicTailProjectedTriadicClosure X ≤ dyadicTailQuotientSubspace X := by
  exact (dyadicTailProjectedTriadicSpan X).topologicalClosure_minimal
    (dyadicTailProjectedTriadicSpan_le_quotient X)
    (Submodule.isClosed_orthogonal _)

theorem dyadicTailRegularizedTerm_mem_projectedTriadicSpan
    (X d : ℕ) (hd : 0 < d) (hXd : X ≤ d) (ε : ℝ) (p : ℕ × ℕ) :
    dyadicTailRegularizedTerm X d hd ε p ∈ dyadicTailProjectedTriadicSpan X := by
  apply (dyadicTailProjectedTriadicSpan X).smul_mem
  refine ⟨hilbertDilation (d * ((p.1 + 1) * 3 ^ p.2)) (by positivity)
    (hilbertResidue 3 (by norm_num)), ?_, rfl⟩
  apply Submodule.subset_span
  refine ⟨d * ((p.1 + 1) * 3 ^ p.2), by positivity, ?_, rfl⟩
  exact hXd.trans (Nat.le_mul_of_pos_right d (by positivity))

theorem dyadicTailRegularizedFamily_mem_projectedTriadicClosure
    (X d : ℕ) (hd : 0 < d) (hXd : X ≤ d) (ε : ℝ)
    (hs : Summable (dyadicTailRegularizedTerm X d hd ε)) :
    dyadicTailRegularizedFamily X d hd ε ∈ dyadicTailProjectedTriadicClosure X := by
  apply (dyadicTailProjectedTriadicClosure X).smul_mem
  apply (dyadicTailProjectedTriadicSpan X).isClosed_topologicalClosure.mem_of_tendsto
    hs.hasSum
  apply Filter.Eventually.of_forall
  intro s
  apply (dyadicTailProjectedTriadicClosure X).sum_mem
  intro p hp
  exact (dyadicTailProjectedTriadicSpan X).le_topologicalClosure
    (dyadicTailRegularizedTerm_mem_projectedTriadicSpan X d hd hXd ε p)

/-- Only the separating inner-product tests are required for legal recovery.
The analytic providers still have to prove these limits for the actual family. -/
theorem dyadicTail_target_mem_closure_of_inner_limits
    (X d : ℕ) (hd : 0 < d) (hXd : X ≤ d) (ε : ℕ → ℝ)
    (hs : ∀ n, Summable (dyadicTailRegularizedTerm X d hd (ε n)))
    (hlim : ∀ g ∈ (dyadicTailProjectedTriadicSpan X)ᗮ,
      Tendsto (fun n => inner ℝ g (dyadicTailRegularizedFamily X d hd (ε n)))
        atTop (nhds (inner ℝ g
          (dyadicTailQuotientProjection X (hilbertDilation d hd hilbertOne))))) :
    dyadicTailQuotientProjection X (hilbertDilation d hd hilbertOne) ∈
      dyadicTailProjectedTriadicClosure X := by
  rw [dyadicTailProjectedTriadicClosure,
    ← Submodule.orthogonal_orthogonal_eq_closure]
  apply (Submodule.mem_orthogonal _ _).mpr
  intro g hg
  have hz (n : ℕ) :
      inner ℝ g (dyadicTailRegularizedFamily X d hd (ε n)) = 0 := by
    have hm := dyadicTailRegularizedFamily_mem_projectedTriadicClosure
      X d hd hXd (ε n) (hs n)
    change _ ∈ (dyadicTailProjectedTriadicSpan X).topologicalClosure at hm
    rw [← Submodule.orthogonal_orthogonal_eq_closure] at hm
    exact (Submodule.mem_orthogonal _ _).mp hm g hg
  have ht : Tendsto (fun n => inner ℝ g
      (dyadicTailRegularizedFamily X d hd (ε n))) atTop (nhds 0) := by
    simp only [hz]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique (hlim g hg) ht

/-- Actual finite signed legal lifts follow from norm-closure membership.
Their full-space norms are not asserted to be small. -/
theorem dyadicTail_exists_finite_legal_lift
    (X : ℕ) (target : ThresholdHilbert)
    (htarget : target ∈ dyadicTailProjectedTriadicClosure X)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ f ∈ dyadicTailTriadicSpan X,
      (∀ k : ℕ, k < X → hilbertSequence f k = 0) ∧
      ‖target - dyadicTailQuotientProjection X f‖ < δ := by
  obtain ⟨g, hg, hclose⟩ := Metric.mem_closure_iff.mp htarget δ hδ
  obtain ⟨f, hf, rfl⟩ := hg
  exact ⟨f, hf, fun k hk => dyadicTailTriadicSpan_support X f hf k hk,
    by
      change dist target (dyadicTailQuotientProjection X f) < δ at hclose
      rw [dist_eq_norm] at hclose
      exact hclose⟩

/-- The projected integer steps generate the full actual tail quotient densely.
The input concerns the concrete step targets, not arbitrary vectors. -/
theorem dyadicTailProjectedTriadicClosure_eq_quotient_of_steps
    (X : ℕ) (hX : 0 < X)
    (hsteps : ∀ d (hd : 0 < d), X ≤ d →
      dyadicTailQuotientProjection X (hilbertDilation d hd hilbertOne) ∈
        dyadicTailProjectedTriadicClosure X) :
    dyadicTailProjectedTriadicClosure X = dyadicTailQuotientSubspace X := by
  apply le_antisymm (dyadicTailProjectedTriadicClosure_le_quotient X)
  intro f hf
  rw [dyadicTailProjectedTriadicClosure,
    ← Submodule.orthogonal_orthogonal_eq_closure]
  apply (Submodule.mem_orthogonal _ _).mpr
  intro g hg
  have hpair (d : ℕ) (hd : 0 < d) (hXd : X ≤ d) :
      inner ℝ (hilbertDilation d hd hilbertOne)
        (dyadicTailQuotientProjection X g) = 0 := by
    have hm := hsteps d hd hXd
    change _ ∈ (dyadicTailProjectedTriadicSpan X).topologicalClosure at hm
    rw [← Submodule.orthogonal_orthogonal_eq_closure] at hm
    have hz := (Submodule.mem_orthogonal _ _).mp hm g hg
    rw [real_inner_comm] at hz
    rwa [dyadicTailQuotientProjection_inner] at hz
  have hQg : dyadicTailQuotientProjection X g = 0 := by
    apply hilbertSequence_injective
    change hilbertSequenceLinear (dyadicTailQuotientProjection X g) = hilbertSequenceLinear 0
    rw [map_zero]
    funext k
    change hilbertSequence (dyadicTailQuotientProjection X g) k = 0
    by_cases hk : k < X
    · simpa using dyadicTailQuotientProjection_support X g k hk
    · have hXk : X ≤ k := Nat.le_of_not_gt hk
      have hkp : 0 < k := hX.trans_le hXk
      have ha := hilbertAtom_inner k hkp (dyadicTailQuotientProjection X g)
      rw [hilbertAtom, hilbertTail, hilbertTail, inner_sub_left,
        real_inner_smul_left, real_inner_smul_left,
        hpair k hkp hXk, hpair (k + 1) (by omega) (by omega)] at ha
      have hw : positiveWeight k ≠ 0 := by unfold positiveWeight; positivity
      have hz : hilbertSequence (dyadicTailQuotientProjection X g) k = 0 := by
        apply (mul_eq_zero.mp (show positiveWeight k *
          hilbertSequence (dyadicTailQuotientProjection X g) k = 0 by
            simpa using ha.symm)).resolve_left hw
      simpa using hz
  have hfix : dyadicTailQuotientProjection X f = f :=
    Submodule.starProjection_eq_self_iff.mpr hf
  rw [← hfix, ← dyadicTailQuotientProjection_inner, hQg, inner_zero_left]

/-- Recovery of the full quotient density statement from the actual family.
Series convergence and scalar limits remain explicit analytic hypotheses. -/
theorem dyadicTailProjectedTriadicClosure_eq_quotient_of_inner_limits
    (X : ℕ) (hX : 0 < X) (ε : ℕ → ℝ)
    (hs : ∀ d (hd : 0 < d), X ≤ d → ∀ n,
      Summable (dyadicTailRegularizedTerm X d hd (ε n)))
    (hlim : ∀ d (hd : 0 < d), X ≤ d →
      ∀ g ∈ (dyadicTailProjectedTriadicSpan X)ᗮ,
        Tendsto (fun n => inner ℝ g (dyadicTailRegularizedFamily X d hd (ε n)))
          atTop (nhds (inner ℝ g
            (dyadicTailQuotientProjection X (hilbertDilation d hd hilbertOne))))) :
    dyadicTailProjectedTriadicClosure X = dyadicTailQuotientSubspace X := by
  apply dyadicTailProjectedTriadicClosure_eq_quotient_of_steps X hX
  intro d hd hXd
  exact dyadicTail_target_mem_closure_of_inner_limits X d hd hXd ε
    (hs d hd hXd) (hlim d hd hXd)

/-- Exact accounting for the remaining full-energy obligation toward RH.
A small quotient error alone leaves the entire complementary lift energy. -/
theorem dyadicTail_finite_lift_error_pythagoras
    (X : ℕ) (target f : ThresholdHilbert)
    (htarget : target ∈ dyadicTailQuotientSubspace X) :
    ‖target - f‖ ^ 2 =
      ‖target - dyadicTailQuotientProjection X f‖ ^ 2 +
      ‖f - dyadicTailQuotientProjection X f‖ ^ 2 := by
  have hfix : dyadicTailQuotientProjection X target = target :=
    Submodule.starProjection_eq_self_iff.mpr htarget
  have hp := dyadicTailQuotientProjection_pythagoras X (target - f)
  rw [map_sub, hfix] at hp
  have he : target - f - (target - dyadicTailQuotientProjection X f) =
      -(f - dyadicTailQuotientProjection X f) := by abel
  simpa only [he, norm_neg] using hp

end
end RiemannResearch.RH.Pareto
