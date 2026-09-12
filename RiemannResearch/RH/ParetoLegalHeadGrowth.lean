import RiemannResearch.RH.ParetoMellinHeadObstruction
import RiemannResearch.RH.RHFalseEnergyConsequences
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Full-energy growth of legal exact-head witnesses

Source: user-provided canonical-correlation and RH-contradiction research,
September 12, 2026 (research direction). The quantitative estimate is derived
from the established actual Mellin head-tail inequality.

A right-half-plane zeta zero forces polynomial growth in the complete squared
norm of every legal vector equal to one through N. Thus exact-head legal
witnesses with subpolynomial complete squared norm imply Mathlib's actual RH.
The zero obstruction and divergence are proved implications. The final RH
criterion is a CONDITIONAL RESEARCH REDUCTION: witnesses meeting both the
exact-head and full-energy requirements have not been constructed here.
-/

open Filter

namespace RiemannResearch.RH.Pareto
theorem legal_exactHead_power_lower_of_zeta
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) {f : ThresholdHilbert}
    (hf : f ∈ hilbertLegalClosure A) {N : ℕ} (hN : 3 ≤ N)
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1) :
    ((2 * s.re - 1) / (4 * ‖s‖ ^ 2)) *
      ((N : ℝ) + 1) ^ (2 * s.re - 1) ≤ ‖f‖ ^ 2 :=
  paretoMellin_exact_head_power_lower hN hhead s hs
    (paretoMellin_zero_on_legalClosure_of_zeta A hA s hs hs1 hz hf)

theorem legal_exactHead_energy_tendsto_atTop_of_zeta
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) (F : ℕ → ThresholdHilbert)
    (hlegal : ∀ N, F N ∈ hilbertLegalClosure A)
    (hhead : ∀ N k, 0 < k → k ≤ N → hilbertSequence (F N) k = 1) :
    Tendsto (fun N => ‖F N‖ ^ 2) atTop atTop := by
  have hd : 0 < 2 * s.re - 1 := by linarith
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hc : 0 < (2 * s.re - 1) / (4 * ‖s‖ ^ 2) := by positivity
  have ht : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun N => by linarith) tendsto_natCast_atTop_atTop
  have hp : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ (2 * s.re - 1)) atTop atTop :=
    (tendsto_rpow_atTop hd).comp ht
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [eventually_ge_atTop (3 : ℕ),
    hp.eventually (eventually_ge_atTop (B / ((2 * s.re - 1) / (4 * ‖s‖ ^ 2))))]
    with N hN hB
  have hb := legal_exactHead_power_lower_of_zeta A hA s hs hs1 hz (hlegal N) hN (hhead N)
  have hB' := (div_le_iff₀ hc).mp hB
  nlinarith

/-- Conditional research reduction. The actual exact-head witnesses and their
subpolynomial full squared norms are substantive, unproved inputs. -/
theorem riemannHypothesis_of_legal_exactHead_subpower
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (F : ℕ → ThresholdHilbert)
    (hlegal : ∀ N, F N ∈ hilbertLegalClosure A)
    (hhead : ∀ N k, 0 < k → k ≤ N → hilbertSequence (F N) k = 1)
    (hsubpower : ∀ p : ℝ, 0 < p →
      Tendsto (fun N => ‖F N‖ ^ 2 / ((N : ℝ) + 1) ^ p) atTop (nhds 0)) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨s, hz, hs, hs1⟩ := RiemannResearch.RH.exists_right_zero_of_not_RH hRH
  have hd : 0 < 2 * s.re - 1 := by linarith
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hsne : s ≠ 1 := by intro he; simp [he] at hs1
  have hc : 0 < (2 * s.re - 1) / (4 * ‖s‖ ^ 2) := by positivity
  have hev := (hsubpower (2 * s.re - 1) hd).eventually_lt_const hc
  obtain ⟨N, hN, hsmall⟩ := ((eventually_ge_atTop (3 : ℕ)).and hev).exists
  have hb := legal_exactHead_power_lower_of_zeta A hA s hs hsne hz (hlegal N) hN (hhead N)
  have hp : 0 < ((N : ℝ) + 1) ^ (2 * s.re - 1) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hr := (le_div_iff₀ hp).mpr hb
  exact (not_lt_of_ge hr) hsmall
end RiemannResearch.RH.Pareto
