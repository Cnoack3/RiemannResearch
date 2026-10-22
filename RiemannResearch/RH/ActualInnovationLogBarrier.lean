import RiemannResearch.Analysis.InnovationLogBarrier
import RiemannResearch.RH.BurnolParetoTransfer
import RiemannResearch.RH.OptimalDilationInnovation
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Logarithmic obstruction for the actual two-dilation innovations

Source: user-requested audit, 13 October 2026. The scalar argument is
independently derived; the external analytic input is Burnol, Advances
in Mathematics 170 (2002), 56--70, Theorem 1.3,
https://arxiv.org/pdf/math/0103058.
The lower envelope stays explicit; no analytic theorem or innovation
lower bound is postulated.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.OptimalDilationInnovation
open RiemannResearch.Analysis.InnovationLogBarrier
open RiemannResearch.RH.Pareto.BurnolTransfer

set_option backward.isDefEq.respectTransparency false

theorem geometricStage_mono (n : ℕ) : Monotone (geometricStage n) :=
  monotone_nat_of_le_succ (fun k => le_tripleStage (geometricStage n k))

theorem index_le_geometricStage (n k : ℕ) : k ≤ geometricStage n k := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [geometricStage, tripleStage]
    omega

theorem geometricStage_tendsto (n : ℕ) : Tendsto (geometricStage n) atTop atTop :=
  tendsto_atTop_mono (index_le_geometricStage n) tendsto_id

theorem geometric_energy_pos_of_envelope (n : ℕ) (c : ℝ) (hc : 0 < c)
    (K : ℕ) (hl : ∀ k, K ≤ k →
      c / ((k : ℝ) + 1) ≤ energy (geometricStage n k)) (k : ℕ) :
    0 < energy (geometricStage n k) := by
  have h := hl (max k K) (le_max_right _ _)
  exact lt_of_lt_of_le
    (lt_of_lt_of_le (div_pos hc (by positivity)) h)
    (energy_antitone (geometricStage_mono n (le_max_left _ _)))

theorem geometric_source_adjacent (n k : ℕ) :
    twoSource (geometricStage n (k + 1)) ≤
      2 * (energy (geometricStage n k) - energy (geometricStage n (k + 1))) *
        (energy (geometricStage n (k + 1)) - energy (geometricStage n (k + 2))) := by
  simpa only [show k + 2 = (k + 1) + 1 by omega, geometricStage] using
    twoSource_adjacent_gain (geometricStage n k)

/-- Sharp parameterized late quartic cap: letting a decrease to one and r
increase to one yields the liminf constant 2/c^2. -/
theorem late_actual_quartic_cap (n : ℕ) (c : ℝ) (hc : 0 < c) (K : ℕ)
    (hl : ∀ k, K ≤ k → c / ((k : ℝ) + 1) ≤ energy (geometricStage n k))
    (a r : ℝ) (ha : 1 < a) (hr : 0 < r) (hr1 : r < 1) (J : ℕ) :
    ∃ j, J ≤ j ∧ twoSource (geometricStage n (2 * j + 1)) * c ^ 2 * r ^ 4 ≤
      2 * a ^ 2 * (energy (geometricStage n (2 * j + 1))) ^ 4 := by
  apply late_quartic_bound (fun k => energy (geometricStage n k))
    (fun k => twoSource (geometricStage n k))
    (geometric_energy_pos_of_envelope n c hc K hl)
    (energy_antitone.comp_monotone (geometricStage_mono n))
    (fun k => by unfold twoSource; positivity)
    (geometric_source_adjacent n) c hc K hl a r ha hr hr1 J

/-- Every eventually uniform real exponent 0 < p < 4 is incompatible
with the explicit logarithmic lower envelope. No RH assumption is used. -/
theorem no_eventual_subquartic_source (n : ℕ) (c : ℝ) (hc : 0 < c) (K : ℕ)
    (hl : ∀ k, K ≤ k → c / ((k : ℝ) + 1) ≤ energy (geometricStage n k))
    (p η : ℝ) (hp0 : 0 < p) (hp : p < 4) (hη : 0 < η) (J : ℕ)
    (hsource : ∀ k, J ≤ k →
      η * (energy (geometricStage n k)) ^ p ≤ twoSource (geometricStage n k)) :
    False := by
  exact no_subquartic_of_limit (fun k => energy (geometricStage n k))
    (fun k => twoSource (geometricStage n k))
    (geometric_energy_pos_of_envelope n c hc K hl)
    (energy_antitone.comp_monotone (geometricStage_mono n))
    (fun k => by unfold twoSource; positivity)
    (geometric_source_adjacent n) c hc K hl limitEnergy
    (energy_tendsto.comp (geometricStage_tendsto n)) p η hp0 hp hη J hsource

/-- The originally proposed every-stage quadratic lower bound is impossible
conditional only on the stated residual envelope. -/
theorem no_eventual_quadratic_source (n : ℕ) (c : ℝ) (hc : 0 < c) (K : ℕ)
    (hl : ∀ k, K ≤ k → c / ((k : ℝ) + 1) ≤ energy (geometricStage n k))
    (η : ℝ) (hη : 0 < η) (J : ℕ)
    (hsource : ∀ k, J ≤ k →
      η * (energy (geometricStage n k)) ^ 2 ≤ twoSource (geometricStage n k)) :
    False := by
  apply no_eventual_subquartic_source n c hc K hl 2 η (by norm_num)
    (by norm_num) hη J
  simpa only [Real.rpow_two] using hsource

/-- Selected quadratic stages have a finite logarithmic counting budget. -/
theorem quadratic_stage_count (n N : ℕ) (c : ℝ) (hc : 0 < c) (K : ℕ)
    (hl : ∀ k, K ≤ k → c / ((k : ℝ) + 1) ≤ energy (geometricStage n k))
    (hKN : K ≤ N) (η : ℝ) (hη : 0 < η)
    (S : Finset ℕ) (hS : S ⊆ Finset.range N)
    (hsource : ∀ j ∈ S, η * (energy (geometricStage n (j + 1))) ^ 2 ≤
      twoSource (geometricStage n (j + 1))) :
    (S.card : ℝ) * (-Real.log (2 / (η + 2))) ≤
      Real.log (energy n / c) + Real.log ((N : ℝ) + 1) := by
  have h := contraction_count_budget (fun k => energy (geometricStage n k))
    (geometric_energy_pos_of_envelope n c hc K hl)
    (energy_antitone.comp_monotone (geometricStage_mono n)) N S hS
    (2 / (η + 2)) c hc (hl N hKN)
    (fun j hj => previous_stage_contraction (geometricStage n j) η hη (hsource j hj))
  simpa only [geometricStage] using h

/-- The real continuous lower envelope transfers to every fixed geometric ray.
The loss in the constant handles the initial conductor uniformly. -/
theorem geometric_envelope_of_continuous (n : ℕ) (c : ℝ) (hc : 0 < c) (K : ℕ)
    (h : ∀ N : ℕ, K ≤ N → 2 ≤ N →
      ContinuousCutoffLowerBound N (c / Real.log N)) :
    ∃ c' : ℝ, 0 < c' ∧ ∃ K' : ℕ, ∀ k, K' ≤ k →
      c' / ((k : ℝ) + 1) ≤ energy (geometricStage n k) := by
  let B : ℝ := Real.log 3 + Real.log (n + 1 : ℕ)
  have hb : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hlb : 0 ≤ Real.log (n + 1 : ℕ) := Real.log_nonneg hb
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hB : 0 < B := by dsimp [B]; linarith
  refine ⟨c / B, div_pos hc hB, max K 1, ?_⟩
  intro k hk
  have hge := index_le_geometricStage n k
  have hN2 : 2 ≤ geometricStage n k + 1 := by omega
  have hNK : K ≤ geometricStage n k + 1 := by omega
  have hlow := energy_log_envelope c K h (geometricStage n k) hNK hN2
  have hlogpos : 0 < Real.log (geometricStage n k + 1 : ℕ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < geometricStage n k + 1 by omega)
  have he : Real.log (geometricStage n k + 1 : ℕ) =
      (k : ℝ) * Real.log 3 + Real.log (n + 1 : ℕ) := by
    rw [geometricStage_conductor, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hden : Real.log (geometricStage n k + 1 : ℕ) ≤ B * ((k : ℝ) + 1) := by
    rw [he]
    dsimp [B]
    nlinarith [mul_nonneg (Nat.cast_nonneg k) hlb]
  calc
    (c / B) / ((k : ℝ) + 1) = c / (B * ((k : ℝ) + 1)) := div_div _ _ _
    _ ≤ c / Real.log (geometricStage n k + 1 : ℕ) := by
      apply (div_le_div_iff₀ (mul_pos hB (by positivity)) hlogpos).mpr
      exact mul_le_mul_of_nonneg_left hden hc.le
    _ ≤ _ := hlow


/-- Sharp constant restriction for a uniform quartic estimate of the actual source. -/
theorem actual_quartic_coefficient_cap (n : ℕ) (c : ℝ) (hc : 0 < c) (K : ℕ)
    (hl : ∀ k, K ≤ k → c / ((k : ℝ) + 1) ≤ energy (geometricStage n k))
    (η : ℝ) (J : ℕ) (hsource : ∀ k, J ≤ k →
      η * (energy (geometricStage n k)) ^ 4 ≤ twoSource (geometricStage n k)) :
    η * c ^ 2 ≤ 2 := by
  exact quartic_coefficient_cap (fun k => energy (geometricStage n k))
    (fun k => twoSource (geometricStage n k))
    (geometric_energy_pos_of_envelope n c hc K hl)
    (energy_antitone.comp_monotone (geometricStage_mono n))
    (fun k => by unfold twoSource; positivity)
    (geometric_source_adjacent n) c hc K hl η J hsource

/-- Linear lower bounds fail even on an arbitrarily sparse geometric subsequence. -/
theorem no_cofinal_actual_linear_source (n : ℕ)
    (hpos : ∀ k, 0 < energy (geometricStage n k)) (η : ℝ) (hη : 0 < η)
    (hsource : ∀ B, ∃ k, B ≤ k ∧ η * energy (geometricStage n (k + 1)) ≤
      twoSource (geometricStage n (k + 1))) : False := by
  exact no_cofinal_linear_source (fun k => energy (geometricStage n k))
    (fun k => twoSource (geometricStage n k)) hpos
    (energy_antitone.comp_monotone (geometricStage_mono n))
    (geometric_source_adjacent n) limitEnergy
    (energy_tendsto.comp (geometricStage_tendsto n)) η hη hsource

/-- Complete assembly: the remaining input is stated on the literal
continuous fractional-part functions, not on the Pareto optimizer. -/
theorem no_subquartic_of_continuous_lower_bound (n : ℕ)
    (c : ℝ) (hc : 0 < c) (K : ℕ)
    (hBurnol : ∀ N : ℕ, K ≤ N → 2 ≤ N →
      ContinuousCutoffLowerBound N (c / Real.log N))
    (p η : ℝ) (hp0 : 0 < p) (hp : p < 4) (hη : 0 < η) (J : ℕ)
    (hsource : ∀ k, J ≤ k →
      η * (energy (geometricStage n k)) ^ p ≤ twoSource (geometricStage n k)) :
    False := by
  obtain ⟨c', hc', K', hl⟩ := geometric_envelope_of_continuous n c hc K hBurnol
  exact no_eventual_subquartic_source n c' hc' K' hl p η hp0 hp hη J hsource
end RiemannResearch.RH.Pareto.CoefficientStabilization.OptimalDilationInnovation
