import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Arithmetic weighted Fourier tests

Source: the paper proof `FMZ_Haar_Poisson_Pareto_Paper_Proofs_20261011.md`.
This module proves deterministic infinite-series consequences of an explicitly
supplied mode remainder. It does not assert the Selberg density theorem or the
Landau formula for actual zeros. No RH hypothesis occurs.

For the application, `weight i = (1 + arithmeticHeight i)^(q+1)` and the
mode provider is the global power-remainder estimate established on paper.
The exact signed remainder is retained before its norm is bounded.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Fourier

def weightedFourierMass {ι : Type*} (c : ι → ℂ) (weight : ι → ℝ) : ℝ :=
  ∑' i, ‖c i‖ * weight i

def weightedFourierPairing {ι : Type*} (c z : ι → ℂ) : ℂ :=
  ∑' i, c i * z i

/-- An explicit mode bound gives absolute summability of its signed test remainder. -/
theorem summable_weightedFourierRemainder {ι : Type*}
    (c e : ι → ℂ) (weight : ι → ℝ) (C L : ℝ)
    (hw : Summable (fun i => ‖c i‖ * weight i))
    (hmode : ∀ i, ‖e i‖ ≤ (C / L) * weight i) :
    Summable (fun i => c i * e i) := by
  apply (hw.mul_left (C / L)).of_norm_bounded
  intro i
  rw [norm_mul]
  calc
    ‖c i‖ * ‖e i‖ ≤ ‖c i‖ * ((C / L) * weight i) :=
      mul_le_mul_of_nonneg_left (hmode i) (norm_nonneg _)
    _ = (C / L) * (‖c i‖ * weight i) := by ring

/-- Quantitative infinite-test bound, with no finiteness assumption on the mode set. -/
theorem weightedFourierRemainder_norm_le {ι : Type*}
    (c e : ι → ℂ) (weight : ι → ℝ) (C L : ℝ)
    (hw : Summable (fun i => ‖c i‖ * weight i))
    (hmode : ∀ i, ‖e i‖ ≤ (C / L) * weight i) :
    ‖∑' i, c i * e i‖ ≤ (C / L) * weightedFourierMass c weight := by
  apply tsum_of_norm_bounded ((hw.hasSum.mul_left (C / L)))
  intro i
  rw [norm_mul]
  calc
    ‖c i‖ * ‖e i‖ ≤ ‖c i‖ * ((C / L) * weight i) :=
      mul_le_mul_of_nonneg_left (hmode i) (norm_nonneg _)
    _ = (C / L) * (‖c i‖ * weight i) := by ring

/-- Complete equality for the test pairing: the signed infinite error is unchanged. -/
theorem weightedFourierPairing_exact_remainder {ι : Type*}
    (c z b : ι → ℂ)
    (hz : Summable (fun i => c i * z i))
    (hb : Summable (fun i => c i * b i)) :
    weightedFourierPairing c z - weightedFourierPairing c b =
      ∑' i, c i * (z i - b i) := by
  simp only [weightedFourierPairing, mul_sub]
  exact (hz.tsum_sub hb).symm

/-- The full-prime arithmetic Wiener bound follows once the explicit mode
provider is supplied. Both pairings and the complete signed remainder appear
in the statement; no limiting density is assumed. -/
theorem weightedFourierPairing_remainder_bound {ι : Type*}
    (c z b : ι → ℂ) (weight : ι → ℝ) (C L : ℝ)
    (hz : Summable (fun i => c i * z i))
    (hb : Summable (fun i => c i * b i))
    (hw : Summable (fun i => ‖c i‖ * weight i))
    (hmode : ∀ i, ‖z i - b i‖ ≤ (C / L) * weight i) :
    ‖weightedFourierPairing c z - weightedFourierPairing c b‖ ≤
      (C / L) * weightedFourierMass c weight := by
  rw [weightedFourierPairing_exact_remainder c z b hz hb]
  exact weightedFourierRemainder_norm_le c (fun i => z i - b i) weight C L hw hmode

/-- The norm bound itself supplies the missing empirical pairing summability. -/
theorem weightedFourierPairing_remainder_bound_of_limit_summable {ι : Type*}
    (c z b : ι → ℂ) (weight : ι → ℝ) (C L : ℝ)
    (hb : Summable (fun i => c i * b i))
    (hw : Summable (fun i => ‖c i‖ * weight i))
    (hmode : ∀ i, ‖z i - b i‖ ≤ (C / L) * weight i) :
    Summable (fun i => c i * z i) ∧
      ‖weightedFourierPairing c z - weightedFourierPairing c b‖ ≤
        (C / L) * weightedFourierMass c weight := by
  have he := summable_weightedFourierRemainder c (fun i => z i - b i)
    weight C L hw hmode
  have hz : Summable (fun i => c i * z i) := by
    convert he.add hb using 1
    ext i
    ring
  exact ⟨hz, weightedFourierPairing_remainder_bound c z b weight C L hz hb hw hmode⟩

end RiemannResearch.Fourier
