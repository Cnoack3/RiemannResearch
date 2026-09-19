import RiemannResearch.RH.MultiRangeRationalAnchorCertificate
import RiemannResearch.RH.MultiRangePrefixOptimization

/-! Exact rational brackets for the attained infinite minimum, equation (7.3)
of RH_Multi_Range_Divisor_Corrections_2026-09-18.md. All feasibility,
nondegeneracy and minimization premises are discharged for distinct anchored
divisors at the explicit finite horizon. -/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open Probability.ConditionalIID Analysis.Cesaro

theorem rationalAnchorMinimum_certificate {D : ℕ} (Y : ℕ) (hY : 0 < Y)
    (d : Fin D → ℕ) (hd : ∀ i, Y+1 < d i) (hinj : Function.Injective d)
    (N : ℕ) (hN : ∀ i, d i ≤ N) :
    let Emin := conditionalMeanSquare (fun n => canonicalMobiusHead Y n +
      anchorSynthesis (Y+1) d (-anchorInverseCoeff (Y+1) d (by omega)
        (fun i => ⟨by have := hd i; omega, by have := hd i; omega⟩) hinj
        (canonicalMobiusHead Y)) n)
    (rationalPrefixEnergy (rationalAnchorCandidate Y d N) N : ℝ) ≤ Emin ∧
    Emin ≤ (rationalUpperCertificate (rationalAnchorCandidate Y d N)
      (rationalAnchorMeanBound Y d N) N : ℝ) := by
  dsimp only
  have hA : 0 < Y+1 := by omega
  have hd' : ∀ i, 1 < d i ∧ d i ≠ Y+1 := fun i =>
    ⟨by have := hd i; omega, by have := hd i; omega⟩
  let xstar := -anchorInverseCoeff (Y+1) d hA hd' hinj (canonicalMobiusHead Y)
  let xN := prefixMeanOptimizer (canonicalMobiusHead Y)
    (fun i => divisorAnchorDirection (Y+1) (d i)) N
  have hlegal := (anchor_affine_mem_class Y d (fun i => by have := hd i; omega) xstar).1
  have hlo := (legal_conditionalMeanSquare_summable (Set.Ici 1)
    (by intro a ha; exact ha) hlegal).sum_le_tsum (Finset.range N)
      (fun k _ => mul_nonneg (conditionalWeight_pos k).le (sq_nonneg _))
  have hmin := anchorPrefixOptimizer_minimizes (Y+1) d hd' hinj
    (canonicalMobiusHead Y) N hN xstar
  constructor
  · rw [rationalPrefixEnergy_cast]
    simpa only [rationalAnchorCandidate_cast, conditionalMeanSquare, xstar] using hmin.trans hlo
  · have hm := anchor_minimizes (Y+1) d hA hd' hinj (canonicalMobiusHead Y)
      (canonicalMobiusHead_mem_legal Y) xN
    have hu := (rationalAnchorCandidate_certificate Y hY d
      (fun i => by have := hd i; omega) N).2
    simp only [rationalAnchorCandidate_cast] at hu
    exact hm.trans hu

/-- The rational lower endpoint is monotone once the divisors fit the horizon. -/
theorem rationalAnchorMinimum_lower_monotone {D : ℕ} (Y : ℕ)
    (d : Fin D → ℕ) (hd : ∀ i, 1 < d i ∧ d i ≠ Y+1)
    (hinj : Function.Injective d) (N M : ℕ) (hN : ∀ i, d i ≤ N) (hNM : N ≤ M) :
    (rationalPrefixEnergy (rationalAnchorCandidate Y d N) N : ℝ) ≤
      (rationalPrefixEnergy (rationalAnchorCandidate Y d M) M : ℝ) := by
  let xM := prefixMeanOptimizer (canonicalMobiusHead Y)
    (fun i => divisorAnchorDirection (Y+1) (d i)) M
  have hm := anchorPrefixOptimizer_minimizes (Y+1) d hd hinj
    (canonicalMobiusHead Y) N hN xM
  have hmono := conditionalMeanPrefix_monotone
    (fun n => canonicalMobiusHead Y n + anchorSynthesis (Y+1) d xM n) hNM
  simpa only [rationalPrefixEnergy_cast,rationalAnchorCandidate_cast] using hm.trans hmono

end RiemannResearch.RH.Pareto
