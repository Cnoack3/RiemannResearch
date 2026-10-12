import RiemannResearch.RH.MultiRangeDivisorCorrections
import RiemannResearch.RH.ConditionalConductorExhaustion
import RiemannResearch.RH.CRTLegalCoordinates

/-!
# Completeness of balanced divisor-range corrections
Source: `RH_Multi_Range_Divisor_Corrections_2026-09-18.md`, Sections 2 and 4.
This proves that the finite anchored directions exhaust the legal exact-head
affine space. It supplies no uniform energy control.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative CRTBlock

/-- Recover normalized finite residue coefficients for every legal sequence. -/
theorem legal_exists_normalized_synthesis {F : ℕ → ℝ}
    (hF : F ∈ legalSeedSpan (Set.Ici 1)) :
    ∃ (s : Finset ℕ) (c : ℕ → ℝ),
      (∀ d ∈ s, 2 ≤ d) ∧ normalizedResidueSynthesis s c = F := by
  classical
  obtain ⟨D, hD⟩ := legal_mem_finiteResidueSubspace hF
  obtain ⟨c, hc⟩ := ConditionalFiniteMinimum.exists_synthesis_of_mem_finite hD
  let b : ℕ → ℝ := fun d => if hd : d ∈ Finset.Icc 2 D then (d : ℝ) * c ⟨d, hd⟩ else 0
  refine ⟨Finset.Icc 2 D, b, fun d hd => (Finset.mem_Icc.mp hd).1, ?_⟩
  rw [← hc]
  funext n
  unfold normalizedResidueSynthesis ConditionalFiniteMinimum.synthesis
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro d _
  have hd : (d.val : ℝ) ≠ 0 := by
    have := (Finset.mem_Icc.mp d.property).1
    positivity
  dsimp [b]
  rw [if_pos d.property]
  unfold residueFraction residue
  field_simp

/-- Vanishing initial values force all low coefficients to vanish. -/
theorem normalized_synthesis_zero_head_low (Y : ℕ) (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ d ∈ s, 2 ≤ d)
    (hh : ∀ n, 0 < n → n ≤ Y → normalizedResidueSynthesis s c n = 0)
    (d : ℕ) (hd : d ∈ s) (hdY : d ≤ Y) : c d = 0 := by
  have hd2 := hs d hd
  have hm := normalizedResidueSynthesis_mobiusDifference s c d (by omega)
  rw [if_pos hd] at hm
  have hz : mobiusDifference d (normalizedResidueSynthesis s c) = 0 := by
    unfold mobiusDifference
    apply Finset.sum_eq_zero
    intro k hk
    have hk0 := Nat.pos_of_mem_divisors hk
    have hkY := (Nat.le_of_dvd (by omega : 0 < d) (Nat.dvd_of_mem_divisors hk)).trans hdY
    have hprev : normalizedResidueSynthesis s c (k-1) = 0 := by
      by_cases hk1 : k = 1
      · simp [hk1, normalizedResidueSynthesis_zero]
      · exact hh (k-1) (by omega) (by omega)
    rw [hh k hk0 hkY, hprev]
    ring
  linarith

/-- Exact anchor reconstruction of any normalized zero-head legal combination. -/
theorem normalized_zero_head_range_representation (Y : ℕ) (hY : 0 < Y)
    (s : Finset ℕ) (c : ℕ → ℝ) (hs : ∀ d ∈ s, 2 ≤ d)
    (hh : ∀ n, 0 < n → n ≤ Y → normalizedResidueSynthesis s c n = 0) :
    ∃ (t : Finset ℕ) (x : ℕ → ℝ),
      (∀ d ∈ t, Y < d) ∧
      divisorRangeCorrection (Y+1) t x = normalizedResidueSynthesis s c := by
  classical
  let t := s.filter (fun d => Y < d)
  have hlow : ∀ d ∈ s, d ∉ t → c d = 0 := by
    intro d hd hdt
    have hn : ¬ Y < d := by
      intro h
      exact hdt (Finset.mem_filter.mpr ⟨hd,h⟩)
    exact normalized_synthesis_zero_head_low Y s c hs hh d hd (by omega)
  have hrec : (∑ d ∈ s, c d / (d : ℝ)) = 0 := by
    rw [← normalizedResidueSynthesis_one s c hs]
    exact hh 1 (by omega) hY
  have hrect : (∑ d ∈ t, c d / (d : ℝ)) = 0 := by
    calc
      _ = ∑ d ∈ s, c d / (d : ℝ) := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro d hd hdt
        rw [hlow d hd hdt, zero_div]
      _ = 0 := hrec
  have hsyn (n : ℕ) : (∑ d ∈ t, c d * residueFraction d n) =
      normalizedResidueSynthesis s c n := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hdt
    rw [hlow d hd hdt, zero_mul]
  refine ⟨t, fun d => -c d, fun d hd => (Finset.mem_filter.mp hd).2, ?_⟩
  funext n
  unfold divisorRangeCorrection divisorAnchorDirection
  calc
    _ = -((Y+1 : ℕ) : ℝ) * (∑ d ∈ t, c d / (d : ℝ)) * residueFraction (Y+1) n +
        ∑ d ∈ t, c d * residueFraction d n := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ = _ := by rw [hrect, mul_zero, zero_mul, zero_add, hsyn]

/-- Every legal exact head is the canonical witness plus finite divisor ranges. -/
theorem conditionalHeadClass_exists_divisor_ranges (Y : ℕ) (hY : 0 < Y)
    {F : ℕ → ℝ} (hF : F ∈ conditionalHeadClass Y) :
    ∃ (s : Finset ℕ) (x : ℕ → ℝ),
      (∀ d ∈ s, Y < d) ∧ correctedMobiusHead Y s x = F := by
  let H : ℕ → ℝ := F - canonicalMobiusHead Y
  have hH : H ∈ legalSeedSpan (Set.Ici 1) :=
    (legalSeedSpan _).sub_mem hF.1 (canonicalMobiusHead_mem_legal Y)
  obtain ⟨s,c,hs,hc⟩ := legal_exists_normalized_synthesis hH
  have hh : ∀ n, 0 < n → n ≤ Y → normalizedResidueSynthesis s c n = 0 := by
    intro n hn hnY
    rw [hc]
    change F n - canonicalMobiusHead Y n = 0
    rw [hF.2 n hn hnY, canonicalMobiusHead_exact Y n hn hnY, sub_self]
  obtain ⟨t,x,ht,hx⟩ := normalized_zero_head_range_representation Y hY s c hs hh
  refine ⟨t,x,ht,?_⟩
  funext n
  unfold correctedMobiusHead
  rw [hx,hc]
  dsimp [H]
  ring

end RiemannResearch.RH.Pareto
