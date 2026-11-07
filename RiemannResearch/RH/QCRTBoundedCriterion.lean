import Mathlib.Tactic.Positivity
import RiemannResearch.RH.QCRTFiniteCollocation
import RiemannResearch.RH.QOptimizerParityRH
import RiemannResearch.RH.QDivisibilityDensity
import RiemannResearch.Analysis.HilbertWeakCompactness
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import RiemannResearch.RH.QFullResidueProjection
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Topology.Metrizable.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Bounded full-conductor CRT collocation forces the actual RH target

Source: user-provided CRT collocation handoff, Section 6. The extraction uses
the repository's Hilbert weak compactness theorem; totality is the checked
complete divisibility dictionary, not an assumption about legal residues.
Bagchi (2006), Theorem 1, explains the full-family RH interpretation.
The uniform bound on the actual collocation sequence remains Open.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QCRTBoundedCriterion
open ZetaTwoHilbert QDivisibilityDensity QCRTFiniteCollocation
open RiemannResearch.Analysis.HilbertWeakCompactness

instance fullClosure_completeSpace : CompleteSpace QFullResidueProjection.closure :=
  (show IsClosed (QFullResidueProjection.closure : Set QHilbert) from
    QFullResidueProjection.legalSpan.isClosed_topologicalClosure).completeSpace_coe

instance fullClosure_separableSpace :
    TopologicalSpace.SeparableSpace QFullResidueProjection.closure := by
  apply TopologicalSpace.IsSeparable.separableSpace
  change TopologicalSpace.IsSeparable
    ((Submodule.span ℝ (Set.range (fun n : ℕ => qResidue (n+2)))).topologicalClosure :
      Set QHilbert)
  rw [Submodule.topologicalClosure_coe]
  exact ((Set.countable_range (fun n : ℕ => qResidue (n+2))).isSeparable.span
    (R := ℝ)).closure

theorem trialSpace_le_legalSpan (L : ℕ) :
    trialSpace L ≤ QFullResidueProjection.legalSpan := by
  apply Submodule.span_le.mpr
  rintro f ⟨d, hd, rfl⟩
  have hdp := Nat.pos_of_mem_divisors hd
  by_cases hd1 : d = 1
  · simp [hd1]
  · apply Submodule.subset_span
    refine ⟨d-2, ?_⟩
    change qResidue (d-2+2) = qResidue d
    rw [Nat.sub_add_cancel (by omega : 2 ≤ d)]

theorem trialSpace_le_full (L : ℕ) :
    trialSpace L ≤ QFullResidueProjection.closure :=
  (trialSpace_le_legalSpan L).trans
    QFullResidueProjection.legalSpan.le_topologicalClosure

/-- Bounded legal vectors with the correct limiting divisibility moments
put one in the actual closed full residue span. -/
theorem qOne_mem_of_bounded_divisor_moments (F : ℕ → QHilbert) (C : ℝ)
    (hF : ∀ j, F j ∈ QFullResidueProjection.closure)
    (hC : ∀ j, ‖F j‖ ≤ C)
    (hm : ∀ d : ℕ, 0 < d →
      Tendsto (fun j => inner ℝ (F j) (qDivisor d)) atTop
        (𝓝 (inner ℝ qOne (qDivisor d)))) :
    qOne ∈ QFullResidueProjection.closure := by
  let G : ℕ → QFullResidueProjection.closure := fun j => ⟨F j, hF j⟩
  obtain ⟨f, _, φ, hφ, hw⟩ := exists_weak_subsequence_of_norm_le C G hC
  have hmatch (d : ℕ) (hd : 0 < d) :
      inner ℝ (f : QHilbert) (qDivisor d) = inner ℝ qOne (qDivisor d) := by
    let ℓ : QFullResidueProjection.closure →L[ℝ] ℝ :=
      (innerSL ℝ (qDivisor d)).comp QFullResidueProjection.closure.subtypeL
    have hc : Continuous (fun x : WeakSpace ℝ QFullResidueProjection.closure =>
        ℓ ((toWeakSpace ℝ QFullResidueProjection.closure).symm x)) :=
      WeakBilin.eval_continuous _ ℓ
    have ht := (hc.tendsto _).comp hw
    change Tendsto (fun j => inner ℝ (qDivisor d) (F (φ j))) atTop
      (𝓝 (inner ℝ (qDivisor d) (f : QHilbert))) at ht
    have ht' : Tendsto (fun j => inner ℝ (F (φ j)) (qDivisor d)) atTop
        (𝓝 (inner ℝ (f : QHilbert) (qDivisor d))) := by
      have hcomm (x : QHilbert) : inner ℝ (qDivisor d) x =
          inner ℝ x (qDivisor d) := real_inner_comm _ _
      simpa only [hcomm] using ht
    exact tendsto_nhds_unique ht' ((hm d hd).comp hφ.tendsto_atTop)
  have he : (f : QHilbert) - qOne = 0 := by
    apply eq_zero_of_orthogonal_qDivisor
    intro d hd
    rw [inner_sub_left, hmatch d hd, sub_self]
  exact (sub_eq_zero.mp he) ▸ f.property

/-- The conclusion is Mathlib's RH; no RH-to-density converse is assumed. -/
theorem riemannHypothesis_of_bounded_divisor_moments (F : ℕ → QHilbert) (C : ℝ)
    (hF : ∀ j, F j ∈ QFullResidueProjection.closure)
    (hC : ∀ j, ‖F j‖ ≤ C)
    (hm : ∀ d : ℕ, 0 < d →
      Tendsto (fun j => inner ℝ (F j) (qDivisor d)) atTop
        (𝓝 (inner ℝ qOne (qDivisor d)))) : RiemannHypothesis :=
  QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure
    (qOne_mem_of_bounded_divisor_moments F C hF hC hm)

/-- Divisor exhaustion and vanishing multiples mass give all fixed test limits. -/
theorem canonical_moments_tendsto (L : ℕ → ℕ) (hL : ∀ j, 2 ≤ L j)
    (hlarge : Tendsto L atTop atTop)
    (hexhaust : ∀ d : ℕ, 0 < d → ∀ᶠ j in atTop, d ∣ L j)
    (d : ℕ) (hd : 0 < d) :
    Tendsto (fun j => inner ℝ (canonical (L j) (hL j) : QHilbert) (qDivisor d))
      atTop (𝓝 (inner ℝ qOne (qDivisor d))) := by
  have hreal : Tendsto (fun j => (L j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hlarge
  have hmass : Tendsto (fun j => 1 / (L j : ℝ)^2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, one_div, inv_pow, zero_pow (by decide : 2 ≠ 0)] using
      (tendsto_inv_atTop_zero.comp hreal).pow 2
  rw [qOne_inner_qDivisor d hd]
  have ht := (tendsto_const_nhds (x := (1 / (d : ℝ)^2))).sub hmass
  apply (show Tendsto (fun j => 1 / (d : ℝ)^2 - 1 / (L j : ℝ)^2)
    atTop (𝓝 (1 / (d : ℝ)^2)) by simpa using ht).congr'
  filter_upwards [hexhaust d hd] with j hj
  exact (canonical_divisor_moment (L j) (hL j) d hd hj).symm

/-- Any cofinal divisor-exhausting bounded canonical family places one in V. -/
theorem qOne_mem_of_bounded_canonical (L : ℕ → ℕ) (hL : ∀ j, 2 ≤ L j)
    (hlarge : Tendsto L atTop atTop)
    (hexhaust : ∀ d : ℕ, 0 < d → ∀ᶠ j in atTop, d ∣ L j)
    (C : ℝ) (hbound : ∀ j, ‖(canonical (L j) (hL j) : QHilbert)‖ ≤ C) :
    qOne ∈ QFullResidueProjection.closure :=
  qOne_mem_of_bounded_divisor_moments _ C
    (fun j => trialSpace_le_full (L j) (canonical (L j) (hL j)).property)
    hbound (canonical_moments_tendsto L hL hlarge hexhaust)

theorem riemannHypothesis_of_bounded_canonical (L : ℕ → ℕ) (hL : ∀ j, 2 ≤ L j)
    (hlarge : Tendsto L atTop atTop)
    (hexhaust : ∀ d : ℕ, 0 < d → ∀ᶠ j in atTop, d ∣ L j)
    (C : ℝ) (hbound : ∀ j, ‖(canonical (L j) (hL j) : QHilbert)‖ ≤ C) :
    RiemannHypothesis :=
  QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure
    (qOne_mem_of_bounded_canonical L hL hlarge hexhaust C hbound)

/-- Bounded complete leakage is sufficient; convergence of each lift is not assumed. -/
theorem riemannHypothesis_of_bounded_leakage (L : ℕ → ℕ) (hL : ∀ j, 2 ≤ L j)
    (hlarge : Tendsto L atTop atTop)
    (hexhaust : ∀ d : ℕ, 0 < d → ∀ᶠ j in atTop, d ∣ L j)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ j, leakage (L j) (hL j) ≤ C) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_bounded_canonical L hL hlarge hexhaust (C+2)
  intro j
  have he := canonical_norm (L j) (hL j)
  have hb := hbound j
  have hn := norm_nonneg (canonical (L j) (hL j) : QHilbert)
  have hp : 0 ≤ 1 / (L j : ℝ)^2 := by positivity
  nlinarith

/-- The bounded-collocation hypothesis forces the existing optimal projections
to converge strongly to one in the complete Q norm. -/
theorem optimal_tendsto_one_of_bounded_canonical
    (L : ℕ → ℕ) (hL : ∀ j, 2 ≤ L j) (hlarge : Tendsto L atTop atTop)
    (hexhaust : ∀ d : ℕ, 0 < d → ∀ᶠ j in atTop, d ∣ L j)
    (C : ℝ) (hbound : ∀ j, ‖(canonical (L j) (hL j) : QHilbert)‖ ≤ C) :
    Tendsto QFullResidueProjection.candidate atTop (𝓝 qOne) :=
  QFullResidueProjection.candidate_tendsto_qOne
    (qOne_mem_of_bounded_canonical L hL hlarge hexhaust C hbound)

theorem positive_dvd_lcmUpto (d M : ℕ) (hd : 0 < d) (hdM : d ≤ M) :
    d ∣ Nat.lcmUpto M := by
  exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hd, hdM⟩)

theorem lcmUpto_large (M : ℕ) (hM : 2 ≤ M) : 2 ≤ Nat.lcmUpto M :=
  Nat.le_of_dvd (Nat.lcmUpto_pos M) (positive_dvd_lcmUpto 2 M (by omega) hM)

/-- The LCM tower and every cofinal subsequence discharge the cutoff hypotheses. -/
theorem riemannHypothesis_of_bounded_lcm_leakage
    (M : ℕ → ℕ) (hM : ∀ j, 2 ≤ M j) (hcofinal : Tendsto M atTop atTop)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ j, leakage (Nat.lcmUpto (M j)) (lcmUpto_large (M j) (hM j)) ≤ C) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_bounded_leakage
    (fun j => Nat.lcmUpto (M j)) (fun j => lcmUpto_large (M j) (hM j))
    ?_ ?_ C hC hbound
  · apply tendsto_atTop_mono (fun j => ?_) hcofinal
    exact Nat.le_of_dvd (Nat.lcmUpto_pos (M j))
      (positive_dvd_lcmUpto (M j) (M j) (by have := hM j; omega) le_rfl)
  · intro d hd
    filter_upwards [hcofinal.eventually (eventually_ge_atTop d)] with j hj
    exact positive_dvd_lcmUpto d (M j) hd hj

/-- The full LCM trial spaces increase, including all prime-power depths. -/
theorem lcm_trialSpace_mono :
    Monotone (fun M : ℕ => trialSpace (Nat.lcmUpto (M+2))) := by
  intro M N hMN
  have hdiv : Nat.lcmUpto (M+2) ∣ Nat.lcmUpto (N+2) := by
    apply Finset.lcm_dvd_iff.mpr
    intro d hd
    rcases Finset.mem_Icc.mp hd with ⟨hdp, hdM⟩
    exact positive_dvd_lcmUpto d (N+2) hdp (by omega)
  apply Submodule.span_mono
  rintro f ⟨d, hd, rfl⟩
  exact ⟨d, Nat.mem_divisors.mpr
    ⟨(Nat.dvd_of_mem_divisors hd).trans hdiv,
      ne_of_gt (Nat.lcmUpto_pos (N+2))⟩, rfl⟩

/-- Every full residue atom enters the LCM tower. -/
theorem iSup_lcm_trialSpace :
    (⨆ M : ℕ, trialSpace (Nat.lcmUpto (M+2))) =
      QFullResidueProjection.legalSpan := by
  apply le_antisymm
  · exact iSup_le (fun M => trialSpace_le_legalSpan _)
  · apply Submodule.span_le.mpr
    rintro f ⟨n, rfl⟩
    apply (le_iSup (fun M : ℕ => trialSpace (Nat.lcmUpto (M+2))) n)
    exact residue_mem_trial _ _ (Nat.lcmUpto_pos _)
      (positive_dvd_lcmUpto (n+2) (n+2) (by omega) le_rfl)

/-- Unconditional convergence is to the full legal projection. -/
theorem lcm_optimal_tendsto_projection :
    Tendsto (fun M : ℕ => (trialSpace (Nat.lcmUpto (M+2))).starProjection qOne)
      atTop (𝓝 (QFullResidueProjection.closure.starProjection qOne)) := by
  have h := Submodule.starProjection_tendsto_closure_iSup
    (fun M : ℕ => trialSpace (Nat.lcmUpto (M+2))) lcm_trialSpace_mono qOne
  simpa only [iSup_lcm_trialSpace, QFullResidueProjection.closure] using h

/-- The actual LCM optimal errors vanish under the same bounded canonical
hypothesis; the conclusion uses the full infinite Q norm. -/
theorem lcm_optimal_error_tendsto_zero_of_bounded_canonical
    (L : ℕ → ℕ) (hL : ∀ j, 2 ≤ L j) (hlarge : Tendsto L atTop atTop)
    (hexhaust : ∀ d : ℕ, 0 < d → ∀ᶠ j in atTop, d ∣ L j)
    (C : ℝ) (hbound : ∀ j, ‖(canonical (L j) (hL j) : QHilbert)‖ ≤ C) :
    Tendsto (fun M : ℕ =>
      ‖qOne - (trialSpace (Nat.lcmUpto (M+2))).starProjection qOne‖^2)
      atTop (𝓝 0) := by
  have hm := qOne_mem_of_bounded_canonical L hL hlarge hexhaust C hbound
  have hp := lcm_optimal_tendsto_projection
  rw [Submodule.starProjection_eq_self_iff.mpr hm] at hp
  simpa using ((tendsto_const_nhds (x := qOne)).sub hp).norm.pow 2

end RiemannResearch.RH.QCRTBoundedCriterion
