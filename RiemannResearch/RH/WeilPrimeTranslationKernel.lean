import RiemannResearch.RH.WeilConverse
import RiemannResearch.Analysis.BilateralLaplaceTranslation
import RiemannResearch.Analysis.SuperexponentialTranslation

/-!
# Actual Weil reflection kernel under prime-log translations

Theorems apply the imported actual-zeta explicit formula and the proved
single-zero tests in `WeilConverse`. Specializing translations to logarithms
of divisors gives the finite prime/CRT matrix studied in the accompanying
research note. No off-line zero is asserted to exist.
Source: direct assembly of the repository's actual Weil pairing and zero
isolation theorems; the rank-two spectral calculation is recorded separately
as a paper consequence, not as a Lean declaration.
-/

noncomputable section
open MeasureTheory MeasureTheory.BilateralLaplace RiemannResearch.Analysis
open scoped ComplexConjugate BigOperators

namespace RiemannResearch.RH.SignedWeilCorrelation
open WeilExplicitFormula

private theorem centeredTransform_add_smooth {f g : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) (hg : SmoothSuperexponentialDecay g)
    (s : ℂ) :
    centeredTransform (f + g) s = centeredTransform f s + centeredTransform g s := by
  change (∫ y : ℝ, (f y + g y) * kernel (s - 1 / 2) y) = _
  simp only [add_mul]
  exact integral_add
    (integrable_integrand (hf.decay.hasExponentialMoments hf.1.continuous) (s - 1 / 2))
    (integrable_integrand (hg.decay.hasExponentialMoments hg.1.continuous) (s - 1 / 2))

/-- Exact actual arithmetic pairing of translates of a reflected two-zero test.
The right side has not omitted or bounded any prime, pole, or gamma term. -/
theorem arithmeticWeilPairing_translate_two_signatures
    {h : ℝ → ℂ} (hh : SmoothSuperexponentialDecay h)
    (ρ : Zeta23.zetaZeroConfig.carrier)
    (hne : actualZeroReflect ρ ≠ ρ)
    (hρ : centeredTransform h (ρ : ℂ) = 1)
    (hr : centeredTransform h (actualZeroReflect ρ : ℂ) = 1)
    (hz : ∀ σ : Zeta23.zetaZeroConfig.carrier,
      σ ≠ ρ → σ ≠ actualZeroReflect ρ → centeredTransform h (σ : ℂ) = 0)
    (t u : ℝ) :
    arithmeticWeilPairing (fun x => h (x - t)) (fun x => h (x - u)) =
      (Zeta23.zeroMult ρ : ℂ) *
        (conj (Complex.exp (-((actualZeroReflect ρ : ℂ) - 1 / 2) * (t : ℂ))) *
            Complex.exp (-((ρ : ℂ) - 1 / 2) * (u : ℂ)) +
          conj (Complex.exp (-((ρ : ℂ) - 1 / 2) * (t : ℂ))) *
            Complex.exp (-((actualZeroReflect ρ : ℂ) - 1 / 2) * (u : ℂ))) := by
  classical
  have hρr : 1 - conj (ρ : ℂ) = (actualZeroReflect ρ : ℂ) := rfl
  have hrr : 1 - conj (actualZeroReflect ρ : ℂ) = (ρ : ℂ) := by
    change 1 - conj (1 - conj (ρ : ℂ)) = (ρ : ℂ)
    simp
  rw [arithmeticWeilPairing_eq_zero_sum (hh.translate t) (hh.translate u)]
  rw [tsum_eq_sum (s := {ρ, actualZeroReflect ρ})]
  · rw [Finset.sum_pair hne.symm, zeroMult_actualZeroReflect, hρr, hrr]
    simp only [centeredTransform_translate, hρ, hr, mul_one]
    ring
  · intro σ hσ
    have hσ' : σ ≠ ρ ∧ σ ≠ actualZeroReflect ρ := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hσ
    simp only [centeredTransform_translate]
    rw [hz σ hσ'.1 hσ'.2, mul_zero, mul_zero]

/-- Actual smooth seed for the full translated reflection block, constructed
from the proved single-zero tests. Off-line existence remains explicit. -/
theorem exists_smooth_translated_reflection_kernel
    (ρ : Zeta23.zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) :
    ∃ h : ℝ → ℂ, SmoothSuperexponentialDecay h ∧
      ∀ t u : ℝ,
        arithmeticWeilPairing (fun x => h (x - t)) (fun x => h (x - u)) =
          (Zeta23.zeroMult ρ : ℂ) *
            (conj (Complex.exp (-((actualZeroReflect ρ : ℂ) - 1 / 2) * (t : ℂ))) *
                Complex.exp (-((ρ : ℂ) - 1 / 2) * (u : ℂ)) +
              conj (Complex.exp (-((ρ : ℂ) - 1 / 2) * (t : ℂ))) *
                Complex.exp (-((actualZeroReflect ρ : ℂ) - 1 / 2) * (u : ℂ))) := by
  have hne : actualZeroReflect ρ ≠ ρ := by
    intro he
    have hr := congrArg (fun σ : Zeta23.zetaZeroConfig.carrier => (σ : ℂ).re) he
    change (1 - conj (ρ : ℂ)).re = (ρ : ℂ).re at hr
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hr
    exact hoff (by linarith)
  obtain ⟨f, hf, hfρ, hfz⟩ := exists_smooth_single_actual_zero_test ρ
  obtain ⟨g, hg, hgr, hgz⟩ := exists_smooth_single_actual_zero_test (actualZeroReflect ρ)
  refine ⟨f + g, hf.add hg, ?_⟩
  intro t u
  apply arithmeticWeilPairing_translate_two_signatures (hf.add hg) ρ hne
  · rw [centeredTransform_add_smooth hf hg, hfρ, hgz ρ hne.symm, add_zero]
  · rw [centeredTransform_add_smooth hf hg, hfz _ hne, hgr, zero_add]
  · intro σ hσ hσr
    rw [centeredTransform_add_smooth hf hg, hfz σ hσ, hgz σ hσr, add_zero]

end RiemannResearch.RH.SignedWeilCorrelation
