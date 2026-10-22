import RiemannResearch.RH.SmoothWeilMatrix
import RiemannResearch.RH.NymanTailTransform
import RiemannResearch.RH.WeilSingleZeroTest

/-!
# The converse for the actual smooth arithmetic Weil form

The explicit formula, actual analytic multiplicities, compact interpolation,
and smooth spectral zero removal construct a negative test from any off-line
zero. This is a formal version of the classical Weil positivity criterion;
no mathematical novelty is claimed. The positivity itself remains open.

Background: A. Weil, Sur les formules explicites de la theorie des nombres
premiers (1952); J.-F. Burnol, arXiv:math/9809119.
-/

noncomputable section
open MeasureTheory MeasureTheory.BilateralLaplace RiemannResearch.Analysis
open scoped ComplexConjugate BigOperators

namespace RiemannResearch.RH.SignedWeilCorrelation
open WeilExplicitFormula

theorem arithmeticWeilPairing_of_single_zero {f g : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) (hg : SmoothSuperexponentialDecay g)
    (ρ : Zeta23.zetaZeroConfig.carrier)
    (hz : ∀ σ : Zeta23.zetaZeroConfig.carrier, σ ≠ ρ →
      centeredTransform g (σ : ℂ) = 0) :
    arithmeticWeilPairing f g = (Zeta23.zeroMult ρ : ℂ) *
      conj (centeredTransform f (1 - conj (ρ : ℂ))) * centeredTransform g (ρ : ℂ) := by
  rw [arithmeticWeilPairing_eq_zero_sum hf hg]
  exact tsum_eq_single ρ (fun σ hσ => by rw [hz σ hσ, mul_zero])

theorem arithmeticWeilPairing_negative_of_two_signatures {f : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) (ρ : Zeta23.zetaZeroConfig.carrier)
    (hne : actualZeroReflect ρ ≠ ρ)
    (hρ : centeredTransform f (ρ : ℂ) = 1)
    (hr : centeredTransform f (actualZeroReflect ρ : ℂ) = -1)
    (hz : ∀ σ : Zeta23.zetaZeroConfig.carrier,
      σ ≠ ρ → σ ≠ actualZeroReflect ρ → centeredTransform f (σ : ℂ) = 0) :
    arithmeticWeilPairing f f = -2 * (Zeta23.zeroMult ρ : ℂ) := by
  classical
  rw [arithmeticWeilPairing_eq_zero_sum hf hf]
  rw [tsum_eq_sum (s := {ρ, actualZeroReflect ρ})]
  · have hr' : centeredTransform f (1 - conj (ρ : ℂ)) = -1 := hr
    have hrr : 1 - conj (actualZeroReflect ρ : ℂ) = (ρ : ℂ) := by
      change 1 - conj (1 - conj (ρ : ℂ)) = (ρ : ℂ)
      simp
    rw [Finset.sum_pair hne.symm]
    rw [hr', hρ, zeroMult_actualZeroReflect, hrr, hρ, hr]
    norm_num
    ring
  · intro σ hσ
    have hσ' : σ ≠ ρ ∧ σ ≠ actualZeroReflect ρ := by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hσ
    rw [hz σ hσ'.1 hσ'.2, mul_zero]

/-- Any actual off-line zero supplies an admissible strictly negative test,
with exact value minus twice its actual analytic multiplicity. -/
theorem exists_smooth_negative_weil_of_off_line
    (ρ : Zeta23.zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) :
    ∃ f : ℝ → ℂ, SmoothSuperexponentialDecay f ∧
      arithmeticWeilPairing f f = -2 * (Zeta23.zeroMult ρ : ℂ) := by
  have hne : actualZeroReflect ρ ≠ ρ := by
    intro he
    have hr := congrArg (fun σ : Zeta23.zetaZeroConfig.carrier => (σ : ℂ).re) he
    change (1 - conj (ρ : ℂ)).re = (ρ : ℂ).re at hr
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hr
    exact hoff (by linarith)
  obtain ⟨f, hf, hfρ, hfz⟩ := exists_smooth_single_actual_zero_test ρ
  obtain ⟨g, hg, hgr, hgz⟩ := exists_smooth_single_actual_zero_test (actualZeroReflect ρ)
  refine ⟨f - g, hf.sub hg, arithmeticWeilPairing_negative_of_two_signatures
    (hf.sub hg) ρ hne ?_ ?_ ?_⟩
  · rw [centeredTransform_sub (hf.decay.hasExponentialMoments hf.1.continuous)
      (hg.decay.hasExponentialMoments hg.1.continuous), hfρ, hgz ρ hne.symm, sub_zero]
  · rw [centeredTransform_sub (hf.decay.hasExponentialMoments hf.1.continuous)
      (hg.decay.hasExponentialMoments hg.1.continuous), hfz _ hne, hgr, zero_sub]
  · intro σ hσ hσr
    rw [centeredTransform_sub (hf.decay.hasExponentialMoments hf.1.continuous)
      (hg.decay.hasExponentialMoments hg.1.continuous), hfz σ hσ, hgz σ hσr, sub_self]

/- Append inside `namespace RiemannResearch.RH.SignedWeilCorrelation`, after
the proved `exists_smooth_negative_weil_of_off_line` declaration.
This file has no hypothesis or axiom standing in for that witness theorem. -/

/-- The full actual arithmetic Weil form is nonnegative on its supported
smooth test class if and only if Mathlib's Riemann hypothesis holds. -/
theorem riemannHypothesis_iff_arithmeticWeilPairing_nonneg :
    RiemannHypothesis ↔
      ∀ f : ℝ → ℂ, SmoothSuperexponentialDecay f →
        0 ≤ (arithmeticWeilPairing f f).re := by
  constructor
  · intro hRH f hf
    exact arithmeticWeilPairing_self_re_nonneg_of_RH hRH hf
  · intro hpos
    apply riemannHypothesis_iff_strip_zeros_on_line.mpr
    intro ρ hz h0 h1
    by_contra hoff
    let z : Zeta23.zetaZeroConfig.carrier := ⟨ρ, hz, h0, h1⟩
    obtain ⟨f, hf, hneg⟩ := exists_smooth_negative_weil_of_off_line z hoff
    have hm : 1 ≤ Zeta23.zeroMult z :=
      Zeta23.zetaZeroConfig.one_le_mult z z.property
    have hmR : (1 : ℝ) ≤ (Zeta23.zeroMult z : ℝ) := by
      exact_mod_cast hm
    have hp := hpos f hf
    rw [hneg] at hp
    norm_num at hp
    nlinarith

/-- Two-test families already give the complete converse. Every entry here
is the actual arithmetic Weil pairing, including both poles and gamma term. -/
theorem riemannHypothesis_iff_smoothWeilMatrix_two_nonneg :
    RiemannHypothesis ↔
      ∀ f : Fin 2 → ℝ → ℂ,
        (∀ i, SmoothSuperexponentialDecay (f i)) →
          ∀ c : Fin 2 → ℂ, 0 ≤ (smoothWeilMatrixQuadratic f c).re := by
  constructor
  · intro hRH f hf c
    exact smoothWeilMatrix_quadratic_nonneg_of_RH hRH hf c
  · intro hpos
    apply riemannHypothesis_iff_arithmeticWeilPairing_nonneg.mpr
    intro f hf
    let c : Fin 2 → ℂ := fun i => if i = 0 then 1 else 0
    have hp := hpos (fun _ => f) (fun _ => hf) c
    simpa [smoothWeilMatrixQuadratic, smoothWeilMatrix, c,
      Fin.sum_univ_two] using hp

/-- Equivalently, every finite smooth arithmetic Weil matrix has a
nonnegative quadratic form. -/
theorem riemannHypothesis_iff_smoothWeilMatrix_nonneg :
    RiemannHypothesis ↔
      ∀ (n : ℕ) (f : Fin n → ℝ → ℂ),
        (∀ i, SmoothSuperexponentialDecay (f i)) →
          ∀ c : Fin n → ℂ, 0 ≤ (smoothWeilMatrixQuadratic f c).re := by
  constructor
  · intro hRH n f hf c
    exact smoothWeilMatrix_quadratic_nonneg_of_RH hRH hf c
  · intro hpos
    exact riemannHypothesis_iff_smoothWeilMatrix_two_nonneg.mpr (hpos 2)

/-- The exact arithmetic restriction on a reflected off-line pair has matrix
`[[0,m],[m,0]]`. Both tests are obtained without assuming simple zeros. -/
theorem exists_smooth_weil_reflection_block
    (ρ : Zeta23.zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) :
    ∃ f g : ℝ → ℂ,
      SmoothSuperexponentialDecay f ∧ SmoothSuperexponentialDecay g ∧
      arithmeticWeilPairing f f = 0 ∧
      arithmeticWeilPairing f g = (Zeta23.zeroMult ρ : ℂ) ∧
      arithmeticWeilPairing g f = (Zeta23.zeroMult ρ : ℂ) ∧
      arithmeticWeilPairing g g = 0 := by
  have hne : actualZeroReflect ρ ≠ ρ := by
    intro he
    have hr := congrArg (fun σ : Zeta23.zetaZeroConfig.carrier => (σ : ℂ).re) he
    change (1 - conj (ρ : ℂ)).re = (ρ : ℂ).re at hr
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hr
    exact hoff (by linarith)
  obtain ⟨f, hf, hfρ, hfz⟩ := exists_smooth_single_actual_zero_test ρ
  obtain ⟨g, hg, hgr, hgz⟩ := exists_smooth_single_actual_zero_test (actualZeroReflect ρ)
  have hρr : 1 - conj (ρ : ℂ) = (actualZeroReflect ρ : ℂ) := rfl
  have hrr : 1 - conj (actualZeroReflect ρ : ℂ) = (ρ : ℂ) := by
    change 1 - conj (1 - conj (ρ : ℂ)) = (ρ : ℂ)
    simp
  refine ⟨f, g, hf, hg, ?_, ?_, ?_, ?_⟩
  · rw [arithmeticWeilPairing_of_single_zero hf hf ρ hfz, hρr, hfz _ hne]
    simp
  · rw [arithmeticWeilPairing_of_single_zero hf hg (actualZeroReflect ρ) hgz,
      hrr, hfρ, hgr, zeroMult_actualZeroReflect]
    simp
  · rw [arithmeticWeilPairing_of_single_zero hg hf ρ hfz, hρr, hgr, hfρ]
    simp
  · rw [arithmeticWeilPairing_of_single_zero hg hg (actualZeroReflect ρ) hgz,
      hrr, hgz ρ hne.symm]
    simp

end RiemannResearch.RH.SignedWeilCorrelation
