import RiemannResearch.RH.ParetoMellinGramOptimization
import RiemannResearch.RH.ParetoMellinNonsingular
import RiemannResearch.RH.RamanujanMellinOptimization
import RiemannResearch.Analysis.FiniteComplexPushforward
import Mathlib.Data.Fin.Embedding
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Complete finite Mellin-capacity enlargement

Source: the user's third ten-transfer program, 23 October 2026.
The finite complex pushforward keeps every coefficient, including coincident
images. The Mellin enlargement identity retains the complete Gram displacement.
No claim that a family of zeros exhausts the residual is made.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis.FiniteComplexPushforward
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem mellinCharge_pushforward (e : ι → κ) (s b : κ → ℂ) (c : ι → ℂ) :
    mellinCharge s b (pushforward e c) =
      mellinCharge (fun i => s (e i)) (fun i => b (e i)) c := by
  unfold mellinCharge
  rw [sum_conj_pushforward_mul]
  congr 1
  congr 1
  exact quadratic_pushforward e c (mellinCauchyGram s)

/-- Exact gain for arbitrary finite enlargement, including all signed Gram terms. -/
theorem mellinInverseCapacity_enlargement_exact [DecidableEq ι] [DecidableEq κ]
    (e : ι → κ) (s b : κ → ℂ)
    (hsmall : (mellinCauchyGram (fun i => s (e i))).det ≠ 0)
    (hlarge : (mellinCauchyGram s).det ≠ 0) :
    mellinInverseCapacity s b =
      mellinInverseCapacity (fun i => s (e i)) (fun i => b (e i)) +
        (mellinGramQuadratic s
          (pushforward e (mellinInverseCoefficients (fun i => s (e i))
            (fun i => b (e i))) - mellinInverseCoefficients s b)).re := by
  have h := mellinCharge_completion s b
    (pushforward e (mellinInverseCoefficients (fun i => s (e i))
      (fun i => b (e i)))) (mellinInverseCoefficients s b)
    (mellinInverseCoefficients_normal s b hlarge)
  rw [mellinCharge_inverse s b hlarge, mellinCharge_pushforward,
    mellinCharge_inverse _ _ hsmall] at h
  exact h

theorem mellinInverseCapacity_enlargement_mono [DecidableEq ι] [DecidableEq κ]
    (e : ι → κ) (s b : κ → ℂ)
    (hs : ∀ j, (1 / 2 : ℝ) < (s j).re)
    (hsmall : (mellinCauchyGram (fun i => s (e i))).det ≠ 0)
    (hlarge : (mellinCauchyGram s).det ≠ 0) :
    mellinInverseCapacity (fun i => s (e i)) (fun i => b (e i)) ≤
      mellinInverseCapacity s b := by
  rw [mellinInverseCapacity_enlargement_exact e s b hsmall hlarge]
  apply le_add_of_nonneg_right
  rw [← finiteMellinKernel_energy s _ hs]
  exact integral_nonneg (fun _ => sq_nonneg _)

theorem mellinInverseCapacity_enlargement_eq_iff [DecidableEq ι] [DecidableEq κ]
    (e : ι → κ) (s b : κ → ℂ)
    (hsmall : (mellinCauchyGram (fun i => s (e i))).det ≠ 0)
    (hlarge : (mellinCauchyGram s).det ≠ 0) :
    mellinInverseCapacity s b =
      mellinInverseCapacity (fun i => s (e i)) (fun i => b (e i)) ↔
        (mellinGramQuadratic s
          (pushforward e (mellinInverseCoefficients (fun i => s (e i))
            (fun i => b (e i))) - mellinInverseCoefficients s b)).re = 0 := by
  have h := mellinInverseCapacity_enlargement_exact e s b hsmall hlarge
  constructor <;> intro he <;> linarith

/-- Initial segments of arbitrary target signatures have nondecreasing capacity. -/
theorem mellinInverseCapacity_prefix_mono (s b : ℕ → ℂ)
    (hs : ∀ j, (1 / 2 : ℝ) < (s j).re)
    (hdet : ∀ n, (mellinCauchyGram (fun i : Fin n => s i.val)).det ≠ 0) :
    Monotone (fun n => mellinInverseCapacity (fun i : Fin n => s i.val)
      (fun i : Fin n => b i.val)) := by
  intro n m hnm
  simpa only [Fin.castLEEmb_apply, Fin.coe_castLE] using
    mellinInverseCapacity_enlargement_mono (Fin.castLEEmb hnm)
      (fun i : Fin m => s i.val) (fun i : Fin m => b i.val)
      (fun i => hs i.val) (by simpa using hdet n) (hdet m)

theorem mellinInverseCapacity_prefix_mono_of_injective (s b : ℕ → ℂ)
    (hs : ∀ j, (1 / 2 : ℝ) < (s j).re) (hinj : Function.Injective s) :
    Monotone (fun n => mellinInverseCapacity (fun i : Fin n => s i.val)
      (fun i : Fin n => b i.val)) := by
  have hdet : ∀ n, (mellinCauchyGram (fun i : Fin n => s i.val)).det ≠ 0 := by
    intro n
    have hi : Function.Injective (fun i : Fin n => s i.val) := by
      intro i j hij
      exact Fin.ext (hinj hij)
    exact (mellinCauchyGram_det_ne_zero_iff_injective
      (fun i : Fin n => s i.val) (fun i : Fin n => hs i.val)).mpr hi
  exact mellinInverseCapacity_prefix_mono s b hs hdet

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.RamanujanZeroCertificates
open Pareto Pareto.CoefficientStabilization RamanujanCanonicalOptimizer
open RiemannResearch.Analysis.FiniteComplexPushforward
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Enlarging the actual finite zero test retains its entire new obstruction. -/
theorem packet_zeroInverse_enlargement_exact [DecidableEq ι] [DecidableEq κ]
    (e : ι → κ) (z : κ → ℂ)
    (hzre : ∀ j, (1 / 2 : ℝ) < (z j).re)
    (hz1 : ∀ j, z j ≠ 1) (hzero : ∀ j, riemannZeta (z j) = 0)
    (hsmall : (mellinCauchyGram (fun i => z (e i))).det ≠ 0)
    (hlarge : (mellinCauchyGram z).det ≠ 0) (n : ℕ) :
    1 - packetMass n =
      mellinInverseCapacity (fun i => z (e i)) (fun i => 1 / z (e i)) +
        (mellinGramQuadratic z
          (pushforward e (mellinInverseCoefficients (fun i => z (e i))
            (fun i => 1 / z (e i))) -
              mellinInverseCoefficients z (fun i => 1 / z i))).re +
        ∫ x in Ioi (1 : ℝ),
          ‖mellinWeightedStep (hilbertOne - packetCandidate n) x -
            starRingEnd ℂ (finiteMellinKernel z
              (mellinInverseCoefficients z (fun i => 1 / z i)) x)‖ ^ 2 := by
  rw [packet_zeroInverse_energy_exact z hzre hz1 hzero hlarge n,
    mellinInverseCapacity_enlargement_exact e z (fun i => 1 / z i) hsmall hlarge]

end RiemannResearch.RH.RamanujanZeroCertificates
