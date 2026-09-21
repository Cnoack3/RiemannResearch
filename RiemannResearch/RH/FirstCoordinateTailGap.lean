import RiemannResearch.RH.TailCapacityJointCorrections
import RiemannResearch.RH.CanonicalTailCapacityGeometry

/-!
# The exact first-coordinate tail gap

Source: user-provided argument,
`RH_Obstruction_Compact_Frequency_Rigidity_2026-09-21.md`, Sections 1--2,
for the gap and uniform coercivity statements. The finite minimum is the actual
full signed Hilbert Gram minimum. The RH converse is the classical
Nyman--Beurling--Baez-Duarte theorem (Bagchi, Theorem 1,
https://arxiv.org/pdf/math/0607733); its currently missing project provider is
kept explicit. No positive gap or disproof of RH is asserted.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.FiniteGramCapacity
open RiemannResearch.Analysis.FiniteHilbertConstraints
open RiemannResearch.Analysis.ExhaustiveWalk

/-- A single positive constant for every full signed finite tail combination. -/
def UniformTailCoercivity : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ (n : ℕ) (c : Fin n → ℝ),
    ε * (∑ i, c i * reciprocalSource n i) ^ 2 ≤
      ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖ ^ 2

/-- Infimum over all nonempty finite dictionaries; stage n contains g₂,...,g_(n+1). -/
def firstCoordinateTailGap : ℝ :=
  sInf (Set.range (fun n : ℕ => constrainedTailEnergy (n + 1)))

private theorem tailEnergyRange_bddBelow :
    BddBelow (Set.range (fun n : ℕ => constrainedTailEnergy (n + 1))) := by
  refine ⟨0, ?_⟩
  rintro x ⟨n, rfl⟩
  exact (one_div_pos.mpr (tailCapacity_pos (n + 1) (by omega))).le

theorem firstCoordinateTailGap_nonneg : 0 ≤ firstCoordinateTailGap := by
  apply le_csInf (Set.range_nonempty _)
  rintro x ⟨n, rfl⟩
  exact (one_div_pos.mpr (tailCapacity_pos (n + 1) (by omega))).le

theorem firstCoordinateTailGap_le (n : ℕ) :
    firstCoordinateTailGap ≤ constrainedTailEnergy (n + 1) :=
  csInf_le tailEnergyRange_bddBelow ⟨n, rfl⟩

/-- Strict positivity of the genuine finite-minimum infimum is exactly bounded capacity. -/
theorem firstCoordinateTailGap_pos_iff_capacity_bounded :
    0 < firstCoordinateTailGap ↔ ∃ B : ℝ, ∀ n : ℕ, tailCapacity n ≤ B := by
  constructor
  · intro hg
    refine ⟨1 / firstCoordinateTailGap, fun n => ?_⟩
    have hc := tailCapacity_pos (n + 1) (by omega)
    have h := (le_div_iff₀ hc).mp (firstCoordinateTailGap_le n)
    have hu : tailCapacity (n + 1) ≤ 1 / firstCoordinateTailGap :=
      (le_div_iff₀ hg).mpr (by nlinarith only [h])
    exact (tailCapacity_monotone (by omega : n ≤ n + 1)).trans hu
  · rintro ⟨B, hB⟩
    have hB0 : 0 ≤ B := (tailCapacity_nonneg 0).trans (hB 0)
    have hp : 0 < B + 1 := by linarith
    have hle : 1 / (B + 1) ≤ firstCoordinateTailGap := by
      apply le_csInf (Set.range_nonempty _)
      rintro x ⟨n, rfl⟩
      exact one_div_le_one_div_of_le (tailCapacity_pos (n + 1) (by omega))
        ((hB (n + 1)).trans (by linarith))
    exact (one_div_pos.mpr hp).trans_le hle

/-- Coercivity is tested against all coefficients, including all signed cross terms. -/
theorem uniformTailCoercivity_iff_capacity_bounded :
    UniformTailCoercivity ↔ ∃ B : ℝ, ∀ n : ℕ, tailCapacity n ≤ B := by
  constructor
  · rintro ⟨ε, hε, h⟩
    refine ⟨1 / ε, fun n => ?_⟩
    have ht := h n (inverseSource (finiteTailAtom_independent n) (reciprocalSource n))
    have he : ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
        (inverseSource (finiteTailAtom_independent n) (reciprocalSource n))‖ ^ 2 =
        tailCapacity n := tailMinimum_norm_sq n
    change ε * tailCapacity n ^ 2 ≤ _ at ht
    rw [he] at ht
    by_cases hz : tailCapacity n = 0
    · rw [hz]
      exact (one_div_pos.mpr hε).le
    · have hp : 0 < tailCapacity n :=
        lt_of_le_of_ne (tailCapacity_nonneg n) (Ne.symm hz)
      apply (le_div_iff₀ hε).mpr
      by_contra hbad
      have hlt : 1 < tailCapacity n * ε := lt_of_not_ge hbad
      have hm := mul_lt_mul_of_pos_right hlt hp
      nlinarith only [ht, hm]
  · rintro ⟨B, hB⟩
    have hB0 : 0 ≤ B := (tailCapacity_nonneg 0).trans (hB 0)
    have hp : 0 < B + 1 := by linarith
    refine ⟨(B + 1)⁻¹, inv_pos.mpr hp, fun n c => ?_⟩
    have h := source_sq_le_capacity_mul_energy
      (finiteTailAtom_independent n) (reciprocalSource n) c
    have hbound : (∑ i, c i * reciprocalSource n i) ^ 2 ≤
        (B + 1) *
          ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖ ^ 2 :=
      h.trans (mul_le_mul_of_nonneg_right ((hB n).trans (by linarith)) (sq_nonneg _))
    calc
      _ ≤ (B + 1)⁻¹ * ((B + 1) *
          ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hbound (inv_pos.mpr hp).le
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hp), one_mul]

theorem firstCoordinateTailGap_pos_iff_coercivity :
    0 < firstCoordinateTailGap ↔ UniformTailCoercivity :=
  firstCoordinateTailGap_pos_iff_capacity_bounded.trans
    uniformTailCoercivity_iff_capacity_bounded.symm

/-- The infimum itself is a valid coefficient-uniform constant, including
when it vanishes. -/
theorem firstCoordinateTailGap_controls_all (n : ℕ) (c : Fin n → ℝ) :
    firstCoordinateTailGap * (∑ i, c i * reciprocalSource n i) ^ 2 ≤
      ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖ ^ 2 := by
  have hg := (le_div_iff₀ (tailCapacity_pos (n + 1) (by omega))).mp
    (firstCoordinateTailGap_le n)
  have hs := source_sq_le_capacity_mul_energy
    (finiteTailAtom_independent n) (reciprocalSource n) c
  have hb := mul_le_mul_of_nonneg_right
    (tailCapacity_monotone (by omega : n ≤ n + 1))
    (sq_nonneg ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖)
  have hm := mul_le_mul_of_nonneg_left (hs.trans hb) firstCoordinateTailGap_nonneg
  have he := mul_le_mul_of_nonneg_right hg
    (sq_nonneg ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖)
  nlinarith only [hm, he]

/-- No constant larger than the infimum controls every signed finite combination. -/
theorem uniform_tail_constant_le_gap (ε : ℝ)
    (h : ∀ (n : ℕ) (c : Fin n → ℝ),
      ε * (∑ i, c i * reciprocalSource n i) ^ 2 ≤
        ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖ ^ 2) :
    ε ≤ firstCoordinateTailGap := by
  apply le_csInf (Set.range_nonempty _)
  rintro x ⟨n, rfl⟩
  let hv := finiteTailAtom_independent (n + 1)
  let b := reciprocalSource (n + 1)
  have hb : b ≠ 0 := reciprocalSource_ne_zero (n + 1) (by omega)
  have hs := normalized_source hv b hb
  have he : ‖Fintype.linearCombination ℝ (fun i : Fin (n + 1) => tailAtom i.val)
      ((capacity hv b)⁻¹ • inverseSource hv b)‖ ^ 2 = constrainedTailEnergy (n + 1) := by
    rw [map_smul]
    exact normalized_energy hv b hb
  have ht := h (n + 1) ((capacity hv b)⁻¹ • inverseSource hv b)
  rw [hs, one_pow, mul_one, he] at ht
  exact ht

theorem firstCoordinateTailGap_le_normalized_trial (n : ℕ) (c : Fin n → ℝ)
    (hc : (∑ i, c i * reciprocalSource n i) = 1) :
    firstCoordinateTailGap ≤
      ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖ ^ 2 := by
  simpa only [hc, one_pow, mul_one] using firstCoordinateTailGap_controls_all n c

theorem firstCoordinateTailGap_pos_iff_certificate :
    0 < firstCoordinateTailGap ↔ ∃ z : ThresholdHilbert, IsResidueTailCertificate z :=
  firstCoordinateTailGap_pos_iff_capacity_bounded.trans
    tailCapacity_bounded_iff_exists_certificate

/-- The established direction uses no RH-to-density provider. -/
theorem not_RH_firstCoordinateTailGap_pos (hRH : ¬ RiemannHypothesis) :
    0 < firstCoordinateTailGap := by
  apply firstCoordinateTailGap_pos_iff_certificate.mpr
  by_contra h
  exact hRH (riemannHypothesis_of_no_tailCertificate h)

theorem riemannHypothesis_of_firstCoordinateTailGap_zero
    (hgap : firstCoordinateTailGap = 0) : RiemannHypothesis := by
  by_contra hRH
  have h := not_RH_firstCoordinateTailGap_pos hRH
  rw [hgap] at h
  exact (lt_irrefl 0) h

/-- CONDITIONAL RESEARCH REDUCTION: the classical RH-to-density formalization
is an explicit argument, distinct from the open arithmetic gap itself. -/
theorem not_RH_iff_firstCoordinateTailGap_pos
    (hDensity : RiemannHypothesis → closedSpace = ⊤) :
    ¬ RiemannHypothesis ↔ 0 < firstCoordinateTailGap := by
  constructor
  · exact not_RH_firstCoordinateTailGap_pos
  · intro hg hRH
    obtain ⟨B, hB⟩ := firstCoordinateTailGap_pos_iff_capacity_bounded.mp hg
    have he : paretoPointHilbert 0 ∈ closedSpace := by simp [hDensity hRH]
    have herr : Tendsto pointError atTop (𝓝 0) :=
      (walkError_tendsto_zero_iff residueAtom id Function.surjective_id
        (paretoPointHilbert 0)).mpr he
    have hev := (tendsto_atTop.mp (tailCapacity_tendsto_iff.mpr herr)) (B + 1)
    obtain ⟨n, hn⟩ := eventually_atTop.mp hev
    linarith [hn n le_rfl, hB n]

theorem riemannHypothesis_iff_firstCoordinateTailGap_zero
    (hDensity : RiemannHypothesis → closedSpace = ⊤) :
    RiemannHypothesis ↔ firstCoordinateTailGap = 0 := by
  constructor
  · intro hRH
    apply le_antisymm _ firstCoordinateTailGap_nonneg
    by_contra h
    exact ((not_RH_iff_firstCoordinateTailGap_pos hDensity).mpr (lt_of_not_ge h)) hRH
  · exact riemannHypothesis_of_firstCoordinateTailGap_zero

/-- The original Pareto(1) uniform-capacity criterion. The classical Bagchi
RH-to-density direction remains an explicit argument, not a project axiom.
Source: user-provided Pareto capacity note (2026-09-21), Section 2. -/
theorem tailCapacity_bounded_iff_not_RH
    (hDensity : RiemannHypothesis → closedSpace = ⊤) :
    (∃ B : ℝ, ∀ n : ℕ, tailCapacity n ≤ B) ↔ ¬ RiemannHypothesis :=
  firstCoordinateTailGap_pos_iff_capacity_bounded.symm.trans
    (not_RH_iff_firstCoordinateTailGap_pos hDensity).symm

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
