import RiemannResearch.RH.CoupledResidualCauchyHead
import RiemannResearch.RH.CoupledResidualDyadicAccounting
import RiemannResearch.RH.DyadicGainEndpoint
import RiemannResearch.RH.LogarithmicCorrectionTarget
import RiemannResearch.Analysis.ResidualGainProduct
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Finite signed-head criteria on the actual dyadic residual sequence

Source: user-provided signed-head detection catalog, 14 November 2026.
Fixed-budget convergence gives stage-dependent cutoffs, including a common
choice of cutoff function. The logarithmic complete-source and finite-head
bounds are equivalent after enlarging the constant. Both remain OPEN
arithmetic obligations. The final theorems are conditional reductions to
Mathlib's RiemannHypothesis; a cofinal scale alone is never substituted for
nonsummability of the relative-loss schedule.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.CoupledResidual

theorem finiteSourceSquare_nonneg (M K : ℕ) : 0 ≤ finiteSourceSquare M K :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem sourceSquare_nonneg (M : ℕ) : 0 ≤ sourceSquare M :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem combinedSourceSquare_le_sourceSquare (M K : ℕ) :
    combinedSourceSquare M K ≤ sourceSquare M :=
  max_le (headSourceSquare_le_sourceSquare M) (finiteSourceSquare_le_sourceSquare M K)

/-- Any strict fraction of the complete two-source square is captured finitely.
Zero source is included; no uniform or computable cutoff is asserted. -/
theorem exists_finiteSourceSquare_ge_fraction (M : ℕ) (θ : ℝ) (hθ : θ < 1) :
    ∃ K, θ * sourceSquare M ≤ finiteSourceSquare M K := by
  by_cases hs : 0 < sourceSquare M
  · have hh : θ * sourceSquare M < sourceSquare M := by nlinarith
    obtain ⟨K, hK⟩ := Filter.Eventually.exists
      ((finiteSourceSquare_tendsto M).eventually (lt_mem_nhds hh))
    exact ⟨K, hK.le⟩
  · have hz : sourceSquare M = 0 := le_antisymm (le_of_not_gt hs) (sourceSquare_nonneg M)
    refine ⟨0, ?_⟩
    rw [hz, mul_zero]
    exact finiteSourceSquare_nonneg M 0

/-- A single stage-indexed choice captures the same fraction at every budget. -/
theorem exists_cutoffs_capture_sourceSquare (θ : ℝ) (hθ : θ < 1) :
    ∃ K : ℕ → ℕ, ∀ M, θ * sourceSquare M ≤ finiteSourceSquare M (K M) :=
  ⟨fun M => Classical.choose (exists_finiteSourceSquare_ge_fraction M θ hθ),
    fun M => Classical.choose_spec (exists_finiteSourceSquare_ge_fraction M θ hθ)⟩

/-- OPEN arithmetic provider for the complete two-source square. -/
def CompleteSourceLogBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → 1 ≤ M →
    0 < trace M ∧ distance M * trace M ≤ C * Real.log (2*(M:ℝ)) * sourceSquare M

/-- OPEN finite-head provider, exactly with a cutoff at every late budget. -/
def FiniteHeadLogBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → 1 ≤ M →
    0 < trace M ∧ ∃ K : ℕ,
      distance M * trace M ≤ C * Real.log (2*(M:ℝ)) * combinedSourceSquare M K

/-- Complete-source control transfers with every strictly larger constant. -/
theorem finite_head_bound_of_complete_source (M : ℕ) (C D L : ℝ)
    (hC : 0 < C) (hCD : C < D) (hL : 1 < L)
    (h : distance M * trace M ≤ C * Real.log L * sourceSquare M) :
    ∃ K, distance M * trace M ≤ D * Real.log L * finiteSourceSquare M K := by
  have hD : 0 < D := hC.trans hCD
  have hθ : C / D < 1 := (div_lt_one hD).mpr hCD
  obtain ⟨K, hK⟩ := exists_finiteSourceSquare_ge_fraction M (C/D) hθ
  refine ⟨K, h.trans ?_⟩
  have hm := mul_le_mul_of_nonneg_left hK (mul_pos hD (Real.log_pos hL)).le
  have he : D * Real.log L * (C / D * sourceSquare M) =
      C * Real.log L * sourceSquare M := by
    field_simp
  rwa [he] at hm

theorem finiteHeadLogBound_iff_completeSourceLogBound :
    FiniteHeadLogBound ↔ CompleteSourceLogBound := by
  constructor
  · rintro ⟨C, hC, M₀, h⟩
    refine ⟨C, hC, M₀, fun M hM hp => ?_⟩
    obtain ⟨ht, K, hK⟩ := h M hM hp
    have hm : (1:ℝ) ≤ M := by exact_mod_cast hp
    have hl : 0 ≤ C * Real.log (2*(M:ℝ)) :=
      (mul_pos hC (Real.log_pos (by linarith))).le
    exact ⟨ht, hK.trans (mul_le_mul_of_nonneg_left
      (combinedSourceSquare_le_sourceSquare M K) hl)⟩
  · rintro ⟨C, hC, M₀, h⟩
    refine ⟨2*C, by positivity, M₀, fun M hM hp => ?_⟩
    obtain ⟨ht, hb⟩ := h M hM hp
    have hm : (1:ℝ) ≤ M := by exact_mod_cast hp
    have hL : 1 < 2*(M:ℝ) := by linarith
    obtain ⟨K, hK⟩ := finite_head_bound_of_complete_source M C (2*C) _
      hC (by linarith) hL hb
    refine ⟨ht, K, hK.trans ?_⟩
    exact mul_le_mul_of_nonneg_left (le_max_right _ _)
      (mul_pos (by positivity : 0 < 2*C) (Real.log_pos hL)).le

/-- Conditional RH reduction; the complete-source bound is the open input. -/
theorem riemannHypothesis_of_completeSourceLogBound (h : CompleteSourceLogBound) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_logarithmicGainBound
  obtain ⟨C, hC, M₀, h⟩ := h
  refine ⟨C, hC, M₀, fun M hM hp => ?_⟩
  obtain ⟨ht, hs⟩ := h M hM hp
  have hm : (1:ℝ) ≤ M := by exact_mod_cast hp
  have hscale := mul_pos hC (Real.log_pos (show 1 < 2*(M:ℝ) by linarith))
  have hg : sourceSquare M ≤ trace M * gain M := by
    have hh := trace_gain M ht
    have hh' := (div_le_iff₀ ht).mp hh
    simpa only [mul_comm] using hh'
  apply le_of_mul_le_mul_right ?_ ht
  calc
    distance M * trace M ≤ C * Real.log (2*(M:ℝ)) * sourceSquare M := hs
    _ ≤ C * Real.log (2*(M:ℝ)) * (trace M * gain M) :=
      mul_le_mul_of_nonneg_left hg hscale.le
    _ = (C * Real.log (2*(M:ℝ)) * gain M) * trace M := by ring

theorem riemannHypothesis_of_finiteHeadLogBound (h : FiniteHeadLogBound) :
    RiemannHypothesis :=
  riemannHypothesis_of_completeSourceLogBound
    (finiteHeadLogBound_iff_completeSourceLogBound.mp h)

/-- The sharper Cauchy certificate supplies the same complete-source consumer. -/
theorem riemannHypothesis_of_cauchyHeadLogBound (C : ℝ) (hC : 0 < C) (M₀ : ℕ)
    (h : ∀ M : ℕ, M₀ ≤ M → 1 ≤ M → 0 < trace M ∧
      ∃ K, distance M * trace M ≤ C * Real.log (2*(M:ℝ)) * cauchySourceSquare M K) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_completeSourceLogBound
  refine ⟨C, hC, M₀, fun M hM hp => ?_⟩
  obtain ⟨ht, K, hK⟩ := h M hM hp
  have hm : (1:ℝ) ≤ M := by exact_mod_cast hp
  exact ⟨ht, hK.trans (mul_le_mul_of_nonneg_left
    (cauchySourceSquare_le_sourceSquare M K)
    (mul_pos hC (Real.log_pos (by linarith))).le)⟩

/-- General schedule criterion on the actual dyadic chain. Every stage is
quantified, and nonsummability is required explicitly. -/
theorem riemannHypothesis_of_nonsummable_cauchyHead
    (J : ℕ) (K : ℕ → ℕ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hns : ¬ Summable a)
    (ht : ∀ j, 0 < trace (2^(J+j)))
    (hcert : ∀ j, a j * distance (2^(J+j)) * trace (2^(J+j)) ≤
      cauchySourceSquare (2^(J+j)) (K j)) : RiemannHypothesis := by
  let d : ℕ → ℝ := fun j => distance (2^(J+j))
  let r : ℕ → ℝ := fun j => gain (2^(J+j)) / d j
  have hd (j : ℕ) : 0 < d j := distance_pos _
  have hr0 (j : ℕ) : 0 ≤ r j := div_nonneg (gain_nonneg _) (hd j).le
  have hr1 (j : ℕ) : r j < 1 := by
    apply (div_lt_one (hd j)).mpr
    dsimp only [d, gain]
    linarith only [distance_pos (2*2^(J+j))]
  have har (j : ℕ) : a j ≤ r j := by
    apply (le_div_iff₀ (hd j)).mpr
    apply le_of_mul_le_mul_right ?_ (ht j)
    calc
      a j * d j * trace (2^(J+j)) ≤ cauchySourceSquare (2^(J+j)) (K j) := hcert j
      _ ≤ trace (2^(J+j)) * gain (2^(J+j)) := cauchySourceSquare_le_trace_gain _ _
      _ = gain (2^(J+j)) * trace (2^(J+j)) := mul_comm _ _
  have hnr : ¬ Summable r := fun hs => hns (Summable.of_nonneg_of_le ha har hs)
  have hrec (j : ℕ) : d (j+1) = d j * (1-r j) := by
    have he : 2*2^(J+j) = 2^(J+(j+1)) := by
      rw [show J+(j+1) = (J+j)+1 by omega, pow_succ]
      omega
    dsimp only [d, r, gain]
    rw [← he]
    field_simp [ne_of_gt (distance_pos (2^(J+j)))]
    <;> ring
  exact riemannHypothesis_of_distance_convergence (fun j => 2^(J+j))
    ((RiemannResearch.Analysis.ResidualGain.residual_tendsto_zero_iff_not_summable
      (hd 0) hr0 hr1 hrec).mpr hnr)

/-- Complete normalized detection. Lean's zero division sets it to zero at zero-trace stages. -/
def normalizedSourceSquare (M : ℕ) : ℝ :=
  sourceSquare M / (distance M * trace M)

/-- Normalized detection is nonnegative even at a degenerate stage. -/
theorem normalizedSourceSquare_nonneg (M : ℕ) :
    0 ≤ normalizedSourceSquare M :=
  div_nonneg (sourceSquare_nonneg M)
    (mul_nonneg (distance_pos M).le (trace_nonneg M))

/-- A zero-trace stage contributes zero normalized detection. -/
theorem normalizedSourceSquare_of_zero_trace (M : ℕ) (ht : trace M = 0) :
    normalizedSourceSquare M = 0 := by
  simp [normalizedSourceSquare, ht]

/-- The relative-gain comparison requires no separate trace-positivity hypothesis. -/
theorem normalizedSourceSquare_le_relativeGain (M : ℕ) :
    normalizedSourceSquare M ≤ gain M / distance M := by
  have hh := div_le_div_of_nonneg_right
    (sourceSquare_div_trace_le_gain M) (distance_pos M).le
  simpa only [normalizedSourceSquare, div_div, mul_comm] using hh

/-- Conditional RH reduction. Divergence of the actual normalized sources remains open. -/
theorem riemannHypothesis_of_nonsummable_normalizedSource (J : ℕ)
    (hns : ¬ Summable (fun j => normalizedSourceSquare (2 ^ (J + j)))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_dyadic_gain_divergence J
  intro hs
  exact hns (Summable.of_nonneg_of_le
    (fun j => normalizedSourceSquare_nonneg _)
    (fun j => normalizedSourceSquare_le_relativeGain _) hs)

/-- Finite-head normalized detection, again zero at zero-trace stages. -/
def normalizedCauchySquare (M K : ℕ) : ℝ :=
  cauchySourceSquare M K / (distance M * trace M)

/-- The finite-head normalized certificate is nonnegative. -/
theorem normalizedCauchySquare_nonneg (M K : ℕ) :
    0 ≤ normalizedCauchySquare M K := by
  apply div_nonneg _ (mul_nonneg (distance_pos M).le (trace_nonneg M))
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- Every finite-head certificate lies below the complete normalized source square. -/
theorem normalizedCauchySquare_le_source (M K : ℕ) :
    normalizedCauchySquare M K ≤ normalizedSourceSquare M :=
  div_le_div_of_nonneg_right (cauchySourceSquare_le_sourceSquare M K)
    (mul_nonneg (distance_pos M).le (trace_nonneg M))

/-- Conditional RH reduction allowing arbitrary zero-trace stages. -/
theorem riemannHypothesis_of_nonsummable_normalizedCauchy (J : ℕ) (K : ℕ → ℕ)
    (hns : ¬ Summable (fun j => normalizedCauchySquare (2 ^ (J + j)) (K j))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_nonsummable_normalizedSource J
  intro hs
  exact hns (Summable.of_nonneg_of_le
    (fun j => normalizedCauchySquare_nonneg _ _)
    (fun j => normalizedCauchySquare_le_source _ _) hs)

/-- Conditional RH reduction: only selected stages need a certificate.
The selected nonnegative weights must be nonsummable; cofinality alone does not suffice. -/
theorem riemannHypothesis_of_masked_cauchySchedule
    (J : ℕ) (K : ℕ → ℕ) (a : ℕ → ℝ) (good : Set ℕ)
    (ha : ∀ j, 0 ≤ a j) (hns : ¬ Summable (good.indicator a))
    (ht : ∀ j ∈ good, 0 < trace (2 ^ (J + j)))
    (hcert : ∀ j ∈ good,
      a j * distance (2 ^ (J + j)) * trace (2 ^ (J + j)) ≤
        cauchySourceSquare (2 ^ (J + j)) (K j)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_nonsummable_normalizedCauchy J K
  intro hs
  apply hns
  apply Summable.of_nonneg_of_le _ _ hs
  · intro j
    exact Set.indicator_nonneg (fun i hi => ha i) j
  · intro j
    by_cases hj : j ∈ good
    · rw [Set.indicator_of_mem hj]
      apply (le_div_iff₀ (mul_pos (distance_pos _) (ht j hj))).mpr
      simpa only [mul_assoc] using hcert j hj
    · rw [Set.indicator_of_notMem hj]
      exact normalizedCauchySquare_nonneg _ _

end RiemannResearch.RH.Pareto.CoupledResidual
