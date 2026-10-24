import RiemannResearch.RH.ParetoMellinReindexing
import RiemannResearch.RH.ParetoMellinEnlargement
import RiemannResearch.RH.QRamanujanMellinCertificates

/-!
# Full Q Mellin enlargement certificates

Source: deductions from the verified Mellin Gram and Q metric identities,
24 October 2026. Arbitrary finite probe enlargements retain the signed Gram
gain, whole integral remainder, exact Q measure correction, and whole
competitor excess. No zero hypothesis is needed.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QRamanujanMellinCertificates
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QParetoMetric QMellinTransfer
open RiemannResearch.Analysis.FiniteComplexPushforward
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem qMellin_enlargement_completion (f : QHilbert) (e : ι → κ) (z : κ → ℂ)
    (hz : ∀ j, (1 / 2 : ℝ) < (z j).re)
    (hsmall : (mellinCauchyGram (z ∘ e)).det ≠ 0)
    (hlarge : Function.Injective z) :
    zetaTwo * ‖f‖ ^ 2 =
      mellinInverseCapacity (z ∘ e) (fun i => qMellin f (z (e i))) +
      (mellinGramQuadratic z
        (pushforward e (mellinInverseCoefficients (z ∘ e)
          (fun i => qMellin f (z (e i)))) -
          mellinInverseCoefficients z (fun j => qMellin f (z j)))).re +
      mellinProjectionRemainder (toPareto f) z + metricCorrection f := by
  have h := qMellin_inverse_capacity_completion f z hz hlarge
  rw [mellinInverseCapacity_enlargement_exact e z
    (fun j => qMellin f (z j)) hsmall
    ((mellinCauchyGram_det_ne_zero_iff_injective z hz).mpr hlarge)] at h
  exact h

theorem qPacket_enlargement_competitor_completion (e : ι → κ) (z : κ → ℂ)
    (hz : ∀ j, (1 / 2 : ℝ) < (z j).re)
    (hsmall : (mellinCauchyGram (z ∘ e)).det ≠ 0)
    (hlarge : Function.Injective z) (n : ℕ) (a : Fin n → ℝ) :
    zetaTwo * ‖qOne - Fintype.linearCombination ℝ
      (QRamanujanCanonicalOptimizer.packetFamily n) a‖ ^ 2 =
      mellinInverseCapacity (z ∘ e)
        (fun i => qMellin (qOne - QRamanujanCanonicalOptimizer.packetCandidate n) (z (e i))) +
      (mellinGramQuadratic z
        (pushforward e (mellinInverseCoefficients (z ∘ e)
          (fun i => qMellin (qOne - QRamanujanCanonicalOptimizer.packetCandidate n) (z (e i)))) -
        mellinInverseCoefficients z
          (fun j => qMellin (qOne - QRamanujanCanonicalOptimizer.packetCandidate n) (z j)))).re +
      mellinProjectionRemainder
        (toPareto (qOne - QRamanujanCanonicalOptimizer.packetCandidate n)) z +
      metricCorrection (qOne - QRamanujanCanonicalOptimizer.packetCandidate n) +
      zetaTwo * ‖Fintype.linearCombination ℝ
        (QRamanujanCanonicalOptimizer.packetFamily n)
        (a - QRamanujanCanonicalOptimizer.packetCoefficients n)‖ ^ 2 := by
  rw [QRamanujanCanonicalOptimizer.packet_completion, mul_add]
  have h := qMellin_enlargement_completion
    (qOne - QRamanujanCanonicalOptimizer.packetCandidate n) e z hz hsmall hlarge
  rw [QRamanujanCanonicalOptimizer.packet_error] at h
  rw [h]

end RiemannResearch.RH.QRamanujanMellinCertificates
