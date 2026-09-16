import RiemannResearch.RH.CoupledResidualCorrections
import RiemannResearch.Analysis.InterscaleResidualConstraints
import RiemannResearch.Analysis.SharpLogarithmicResidualBarrier

/-!
# Finite dyadic budgets for the actual Pareto residual

Source: user-provided `RH_Coupled_Residual_Corrections_2026-09-16.md`,
Sections 4 and 7. The finite source bounds below specialize the checked
actual Pareto interscale estimate. The sharp logarithmic result remains
conditional on the explicitly stated distance lower envelope.
-/
noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.CoupledResidual
open RiemannResearch.Analysis.InterscaleResidualConstraints

theorem dyadic_binary_source_sq (j : ℕ) :
    (source (2^(j+1)) 2 (by omega))^2 ≤
      2*(distance (2^j)-distance (2^(j+1)))*
        (distance (2^(j+1))-distance (2^(j+2))) := by
  have h := interscale_source_sq (2^(j+1)) 2 (by omega)
  have hp : (2^(j+1) : ℕ) = 2*2^j := by
    rw [pow_succ]
    omega
  have hdiv₁ : (2^(j+1) : ℕ)/2 = 2^j := by omega
  have hdiv₂ : (2*2^(j+1) : ℕ)/2 = 2^(j+1) := by omega
  have hnext : (2*2^(j+1) : ℕ) = 2^(j+2) := by
    rw [show j+2 = (j+1)+1 by omega, pow_succ]
    omega
  rw [priorGain, gain, hdiv₁, hdiv₂, hnext] at h
  simpa only [Nat.cast_ofNat] using h

theorem dyadic_distance_antitone (J : ℕ) :
    Antitone (fun j => distance (2^(J+j))) := by
  intro i j hij
  apply distance_antitone
  exact Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.add_le_add_left hij J)

theorem dyadic_binary_source_budget (J N : ℕ) :
    (∑ j ∈ Finset.range N,
      (source (2^(J+j+1)) 2 (by omega))^2 /
        (2*(distance (2^(J+j))-distance (2^(J+j+1))))) ≤
      distance (2^(J+1))-distance (2^(J+N+1)) := by
  have h := sum_source_quotients_le
    (fun j => distance (2^(J+j)))
    (fun j => source (2^(J+j+1)) 2 (by omega))
    (dyadic_distance_antitone J)
    (fun j => by simpa only [Nat.add_assoc] using dyadic_binary_source_sq (J+j)) N
  simpa only [Nat.add_assoc] using h

theorem dyadic_binary_absolute_budget (J N : ℕ) :
    (∑ j ∈ Finset.range N, |source (2^(J+j+1)) 2 (by omega)|)^2 ≤
      2*(distance (2^J)-distance (2^(J+N)))*
        (distance (2^(J+1))-distance (2^(J+N+1))) := by
  have h := sum_abs_sources_sq_le
    (fun j => distance (2^(J+j)))
    (fun j => source (2^(J+j+1)) 2 (by omega))
    (dyadic_distance_antitone J)
    (fun j => by simpa only [Nat.add_assoc] using dyadic_binary_source_sq (J+j)) N
  simpa only [Nat.add_assoc, Nat.add_zero] using h

/-- Absolute summability of the actual binary signed correlations over
all later dyadic scales, without any RH or Burnol hypothesis. -/
theorem dyadic_binary_source_absolutely_summable (J : ℕ) :
    Summable (fun j => |source (2^(J+j+1)) 2 (by omega)|) := by
  exact summable_abs_sources
    (fun j => distance (2^(J+j)))
    (fun j => source (2^(J+j+1)) 2 (by omega))
    (dyadic_distance_antitone J) (fun j => (distance_pos _).le)
    (fun j => by simpa only [Nat.add_assoc] using dyadic_binary_source_sq (J+j))

theorem dyadic_binary_weighted_sources_summable (J : ℕ) :
    Summable (fun j =>
      (source (2^(J+j+1)) 2 (by omega))^2 /
        (2*(distance (2^(J+j))-distance (2^(J+j+1))))) := by
  have h := summable_source_quotients
    (fun j => distance (2^(J+j)))
    (fun j => source (2^(J+j+1)) 2 (by omega))
    (dyadic_distance_antitone J) (fun j => (distance_pos _).le)
    (fun j => by simpa only [Nat.add_assoc] using dyadic_binary_source_sq (J+j))
  simpa only [Nat.add_assoc] using h

/-- Conditional research reduction: the eventual lower envelope must
still be supplied from the Nyman--Beurling/Burnol comparison. -/
theorem conditional_dyadic_sharp_gain
    (c : ℝ) (hc : 0 < c) (N₀ : ℕ)
    (hlower : ∀ n, N₀ ≤ n → c/((n : ℝ)+1) ≤ distance (2^n))
    (a : ℝ) (ha : 1 < a) (J : ℕ) :
    ∃ j, J ≤ j ∧ ((j : ℝ)+1)*(gain (2^j)/distance (2^j)) < a := by
  have h := RiemannResearch.Analysis.LogarithmicResidualBarrier.exists_late_scaled_gain_lt_of_distance_lower
    (fun j => distance (2^j)) (fun j => distance_pos _) c hc N₀ hlower a ha J
  simpa only [RiemannResearch.Analysis.LogarithmicResidualBarrier.relativeGain,
    gain, pow_succ, Nat.mul_comm] using h

end RiemannResearch.RH.Pareto.CoupledResidual
