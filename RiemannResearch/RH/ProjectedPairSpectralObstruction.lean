import RiemannResearch.Analysis.ZetaFactorObstruction
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual finite Boolean Mellin kernels and the G2 obstruction

Source: highest viability RH.pdf, equations (44), (45), (58) and agenda G2:
https://drive.google.com/file/d/1smLPEbJDfOV2Z5mMSMMQvFEd3_qRYopL/view
The kernel and prime signal are formalized literally. All finite atom values
and all finite corrections are allowed, a stronger scope than projected pairs.
Analyticity is proved, not supplied as an arithmetic hypothesis.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ProjectedPairSpectralObstruction
open RiemannResearch.Analysis.ZetaFactorObstruction
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def primeSignal (p : ι → ℕ) : ℝ := ∑ i, (Real.log (p i : ℝ)) ^ 2

def booleanKernel (p : ι → ℕ) (X : κ → ι → ℝ) (d : κ) (z : ℂ) : ℂ :=
  ∏ i, (1 + (Complex.exp ((Real.log (p i : ℝ) : ℂ) * z) - 1) /
    ((p i : ℂ) - 1) * (X d i : ℂ))

def haarMellin (p : ι → ℕ) (X : κ → ι → ℝ)
    (w φ : κ → ℝ) (z : ℂ) : ℂ :=
  ∑ d, ((w d * φ d : ℝ) : ℂ) * booleanKernel p X d z

theorem primeSignal_pos (p : ι → ℕ) (hp : ∃ i, 1 < p i) :
    0 < primeSignal p := by
  obtain ⟨i,hi⟩ := hp
  have hl : 0 < Real.log (p i : ℝ) := Real.log_pos (by exact_mod_cast hi)
  have hb : (Real.log (p i : ℝ)) ^ 2 ≤ primeSignal p :=
    Finset.single_le_sum (fun j _ => sq_nonneg (Real.log (p j : ℝ))) (Finset.mem_univ i)
  exact (sq_pos_of_pos hl).trans_le hb

omit [Fintype κ] in
theorem booleanKernel_entire (p : ι → ℕ) (X : κ → ι → ℝ) (d : κ) :
    Differentiable ℂ (booleanKernel p X d) := by
  unfold booleanKernel
  fun_prop

theorem haarMellin_entire (p : ι → ℕ) (X : κ → ι → ℝ) (w φ : κ → ℝ) :
    Differentiable ℂ (haarMellin p X w φ) := by
  unfold haarMellin booleanKernel
  fun_prop

theorem haarMellin_add (p : ι → ℕ) (X : κ → ι → ℝ)
    (w φ r : κ → ℝ) (z : ℂ) :
    haarMellin p X w (φ+r) z = haarMellin p X w φ z + haarMellin p X w r z := by
  simp [haarMellin, mul_add, add_mul, Finset.sum_add_distrib]

/-- Complete signed correction formula before any absolute-value estimate. -/
theorem numerator_correction (p : ι → ℕ) (X : κ → ι → ℝ)
    (w φ r : κ → ℝ) (z : ℂ) :
    numerator (primeSignal p : ℂ) (haarMellin p X w (φ+r)) z =
      numerator (primeSignal p : ℂ) (haarMellin p X w φ) z +
        riemannZeta (1-z) * haarMellin p X w r z := by
  rw [numerator, haarMellin_add, mul_add, numerator]
  ring

/-- Every finite-cube correction leaves positive continuous block energy.
No frame, moment, rank, or RH hypothesis is needed. -/
theorem finite_cube_block_pos (p : ι → ℕ) (hp : ∃ i, 1 < p i)
    (X : κ → ι → ℝ) (w φ r : κ → ℝ)
    (σ a b : ℝ) (hσ : 0 < σ) (hab : a < b) :
    0 < ∫ t in a..b,
      ‖numerator (primeSignal p : ℂ) (haarMellin p X w (φ+r)) (line σ t)‖ ^ 2 /
        (Real.pi * (t ^ 2 + 1/4)) := by
  apply mellin_block_pos _ _ _ (haarMellin_entire p X w (φ+r)) σ a b hσ hab
  exact_mod_cast (ne_of_gt (primeSignal_pos p hp))

end RiemannResearch.RH.ProjectedPairSpectralObstruction
