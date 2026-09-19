import RiemannResearch.RH.MultiRangeRationalAnchorCertificate
import RiemannResearch.RH.MultiRangeFixedFamilyCertificates

/-! The rational certificates themselves converge for each fixed anchored
family. This does not assume any bound uniform in Y or the selected divisors. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiemannResearch.RH.Pareto
open Probability.ConditionalIID Analysis.Cesaro

theorem rationalAnchorCertificates_tendsto {D : ℕ} (Y : ℕ) (hY : 0 < Y)
    (d : Fin D → ℕ) (hd : ∀ i, Y+1 < d i) (hinj : Function.Injective d) :
    let Emin := conditionalMeanSquare (fun n => canonicalMobiusHead Y n +
      anchorSynthesis (Y+1) d (-anchorInverseCoeff (Y+1) d (by omega)
        (fun i => ⟨by have := hd i; omega, by have := hd i; omega⟩) hinj
        (canonicalMobiusHead Y)) n)
    Tendsto (fun N => (rationalPrefixEnergy (rationalAnchorCandidate Y d N) N : ℝ))
      atTop (𝓝 Emin) ∧
    Tendsto (fun N => (rationalUpperCertificate (rationalAnchorCandidate Y d N)
      (rationalAnchorMeanBound Y d N) N : ℝ)) atTop (𝓝 Emin) := by
  let F := canonicalMobiusHead Y
  let U := fun i => divisorAnchorDirection (Y+1) (d i)
  let L := (Y : ℝ) + ∑ i, (|finiteMeanOptimizer F U i|+1)*
    ((((Y+1 : ℕ) : ℝ)/(d i : ℝ)+1)/2)
  have hA : 0 < Y+1 := by omega
  have hd' : ∀ i, 1 < d i ∧ d i ≠ Y+1 := fun i =>
    ⟨by have := hd i; omega, by have := hd i; omega⟩
  have hU : ∀ i, U i ∈ legalSeedSpan (Set.Ici 1) := fun i =>
    divisorAnchorDirection_legal (Y+1) (d i) hA (by have := hd i; omega)
  have hdet : (finiteMeanGram U).det ≠ 0 := by
    rw [show finiteMeanGram U = anchorGram (Y+1) d from
      (anchorGram_eq_finiteMeanGram (Y+1) d).symm]
    exact (anchorGram_posDef (Y+1) d hA hd' hinj).det_pos.ne'
  have hfull := anchorFixedFamily_certificates_tendsto (Y+1) d hA hd' hinj F
    (canonicalMobiusHead_mem_legal Y) (Y : ℝ) (by positivity)
      (canonicalMobiusHead_mean_abs_le Y hY)
  dsimp only at hfull ⊢
  have hlo := hfull.1
  have hhi := hfull.2
  have hcast (N : ℕ) : (rationalAnchorMeanBound Y d N : ℝ) = (Y : ℝ) +
      ∑ i, |prefixMeanOptimizer F U N i| * ((((Y+1 : ℕ) : ℝ)/(d i : ℝ)+1)/2) := by
    simp [rationalAnchorMeanBound, F, U, mul_div_assoc]
  have hbound : ∀ᶠ N in atTop, (rationalAnchorMeanBound Y d N : ℝ) ≤ L := by
    filter_upwards [prefixMeanOptimizer_eventually_bounded F U
      (canonicalMobiusHead_mem_legal Y) hU hdet] with N hN
    rw [hcast]
    dsimp only [L]
    apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro i _
    have hh := mul_le_mul_of_nonneg_right (hN i)
      (by positivity : (0 : ℝ) ≤ (((Y+1 : ℕ) : ℝ)/(d i : ℝ)+1)/2)
    simpa only [mul_div_assoc] using hh
  have hlow : ∀ N,
      (rationalPrefixEnergy (rationalAnchorCandidate Y d N) N : ℝ) ≤
      (rationalUpperCertificate (rationalAnchorCandidate Y d N)
        (rationalAnchorMeanBound Y d N) N : ℝ) := by
    intro N
    rw [rationalPrefixEnergy_cast, rationalUpperCertificate_cast]
    unfold conditionalMeanUpperCertificate
    exact le_add_of_nonneg_right (by positivity)
  have hupp : ∀ᶠ N in atTop,
      (rationalUpperCertificate (rationalAnchorCandidate Y d N)
        (rationalAnchorMeanBound Y d N) N : ℝ) ≤
      conditionalMeanUpperCertificate (fun n => (rationalAnchorCandidate Y d N n : ℝ)) L N := by
    filter_upwards [hbound] with N hN
    rw [rationalUpperCertificate_cast]
    unfold conditionalMeanUpperCertificate
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hn : (0 : ℝ) ≤ (rationalAnchorMeanBound Y d N : ℝ) :=
      by exact_mod_cast rationalAnchorMeanBound_nonneg Y d N
    nlinarith
  constructor
  · simpa only [rationalPrefixEnergy_cast, rationalAnchorCandidate_cast, F, U] using hlo
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ ?_
      (Filter.Eventually.of_forall hlow) hupp
    · simpa only [rationalPrefixEnergy_cast, rationalAnchorCandidate_cast, F, U] using hlo
    · simpa only [rationalAnchorCandidate_cast, F, U, L] using hhi

end RiemannResearch.RH.Pareto
