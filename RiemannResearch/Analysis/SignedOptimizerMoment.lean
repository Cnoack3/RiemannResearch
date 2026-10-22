import RiemannResearch.LinearAlgebra.FiniteHilbertSchur
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith

/-!
# Exact signed cancellation between a weighted optimum and screening

Source: user-provided `Exact_Optimizer_Cancellation_20261008.tex`, Sections on
the fixed second moment and the signed correction. The proof uses the finite
normal-equation completion already checked in `FiniteHilbertSchur`.

Every finite-stage quantity below is an actual Hilbert-space norm. The
weighted optimum is formed from `D x` and the transformed atoms `D (z i)`;
screening is the ordinary orthogonal projection of `D r` onto the original
atoms. Both positive norm squares survive in the signed correction.
Normal equations exist even for a redundant finite dictionary.

The final limit theorem is a conditional analytic reduction: smallness of the
weighted optimum divided by the original residual energy remains an explicit
input. No arithmetic provider or RH theorem is asserted here.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.SignedOptimizerMoment

open RiemannResearch.LinearAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {ι : Type*} [Fintype ι]

private theorem map_finiteSchurCombination (D : H →ₗ[ℝ] H)
    (z : ι → H) (c : ι → ℝ) :
    D (finiteSchurCombination z c) =
      finiteSchurCombination (fun i => D (z i)) c := by
  simp [finiteSchurCombination]

private theorem map_finiteSchurResidual (D : H →ₗ[ℝ] H)
    (x : H) (z : ι → H) (c : ι → ℝ) :
    D (finiteSchurResidual x z c) =
      finiteSchurResidual (D x) (fun i => D (z i)) c := by
  simp [finiteSchurResidual, map_finiteSchurCombination]

/-- The complete weighted optimum energy; for the second moment `D` is
the reciprocal-coordinate multiplier. -/
def weightedOptimizerFloor (x : H) (z : ι → H)
    (D : H →ₗ[ℝ] H) (cD : ι → ℝ) : ℝ :=
  ‖finiteSchurResidual (D x) (fun i => D (z i)) cD‖ ^ 2

/-- The weighted distance between the original and weighted optimizers. -/
def weightedOptimizerMismatch (z : ι → H) (D : H →ₗ[ℝ] H)
    (c cD : ι → ℝ) : ℝ :=
  ‖finiteSchurCombination (fun i => D (z i)) c -
      finiteSchurCombination (fun i => D (z i)) cD‖ ^ 2

/-- The actual ordinary projection energy removed from `D r`. -/
def screeningEnergy (z : ι → H) (b : ι → ℝ) : ℝ :=
  ‖finiteSchurCombination z b‖ ^ 2

/-- The full signed quantity: weighted optimizer mismatch minus screening. -/
def signedOptimizerCorrection (z : ι → H) (D : H →ₗ[ℝ] H)
    (c cD b : ι → ℝ) : ℝ :=
  weightedOptimizerMismatch z D c cD - screeningEnergy z b

/-- The squared norm of the compressed weighted residual. -/
def screenedWeightedMomentEnergy (x : H) (z : ι → H)
    (D : H →ₗ[ℝ] H) (c b : ι → ℝ) : ℝ :=
  ‖finiteSchurResidual (D (finiteSchurResidual x z c)) z b‖ ^ 2

theorem weightedOptimizerFloor_nonneg (x : H) (z : ι → H)
    (D : H →ₗ[ℝ] H) (cD : ι → ℝ) :
    0 ≤ weightedOptimizerFloor x z D cD := sq_nonneg _

theorem weightedOptimizerMismatch_nonneg (z : ι → H)
    (D : H →ₗ[ℝ] H) (c cD : ι → ℝ) :
    0 ≤ weightedOptimizerMismatch z D c cD := sq_nonneg _

theorem screeningEnergy_nonneg (z : ι → H) (b : ι → ℝ) :
    0 ≤ screeningEnergy z b := sq_nonneg _

theorem screenedWeightedMomentEnergy_nonneg (x : H) (z : ι → H)
    (D : H →ₗ[ℝ] H) (c b : ι → ℝ) :
    0 ≤ screenedWeightedMomentEnergy x z D c b := sq_nonneg _

/-- `h₂ = ε₂ + δ₂`: the complete weighted error of the original optimizer
equals the actual weighted optimum plus the full optimizer mismatch. -/
theorem weightedResidual_eq_floor_add_mismatch (x : H) (z : ι → H)
    (D : H →ₗ[ℝ] H) (c cD : ι → ℝ)
    (hcD : ∀ i, inner ℝ (D (z i))
      (finiteSchurCombination (fun j => D (z j)) cD) =
        inner ℝ (D (z i)) (D x)) :
    ‖D (finiteSchurResidual x z c)‖ ^ 2 =
      weightedOptimizerFloor x z D cD +
        weightedOptimizerMismatch z D c cD := by
  rw [map_finiteSchurResidual]
  exact finiteSchurResidual_completion (D x) (fun i => D (z i)) c cD hcD

private theorem normal_combination_norm_sq (h : H) (z : ι → H)
    (b : ι → ℝ)
    (hb : ∀ i, inner ℝ (z i) (finiteSchurCombination z b) = inner ℝ (z i) h) :
    ‖finiteSchurCombination z b‖ ^ 2 = ∑ i, b i * inner ℝ (z i) h := by
  rw [← real_inner_self_eq_norm_sq]
  conv_lhs => arg 2; unfold finiteSchurCombination
  simp only [sum_inner, real_inner_smul_left, hb]

/-- Exact screening identity `e m₂ = ε₂ + Γ`, with
`Γ = δ₂ − screeningEnergy`; no norm square is dropped. -/
theorem screenedWeightedMomentEnergy_eq_floor_add_signedCorrection
    (x : H) (z : ι → H) (D : H →ₗ[ℝ] H) (c cD b : ι → ℝ)
    (hcD : ∀ i, inner ℝ (D (z i))
      (finiteSchurCombination (fun j => D (z j)) cD) =
        inner ℝ (D (z i)) (D x))
    (hb : ∀ i, inner ℝ (z i) (finiteSchurCombination z b) =
      inner ℝ (z i) (D (finiteSchurResidual x z c))) :
    screenedWeightedMomentEnergy x z D c b =
      weightedOptimizerFloor x z D cD + signedOptimizerCorrection z D c cD b := by
  unfold screenedWeightedMomentEnergy
  rw [finiteSchurResidual_norm_sq _ z b hb,
    ← normal_combination_norm_sq _ z b hb,
    weightedResidual_eq_floor_add_mismatch x z D c cD hcD]
  unfold signedOptimizerCorrection screeningEnergy
  ring

/-- The negative signed correction is controlled by the actual weighted floor. -/
theorem signedOptimizerCorrection_ge_neg_floor
    (x : H) (z : ι → H) (D : H →ₗ[ℝ] H) (c cD b : ι → ℝ)
    (hcD : ∀ i, inner ℝ (D (z i))
      (finiteSchurCombination (fun j => D (z j)) cD) =
        inner ℝ (D (z i)) (D x))
    (hb : ∀ i, inner ℝ (z i) (finiteSchurCombination z b) =
      inner ℝ (z i) (D (finiteSchurResidual x z c))) :
    -weightedOptimizerFloor x z D cD ≤ signedOptimizerCorrection z D c cD b := by
  have he := screenedWeightedMomentEnergy_eq_floor_add_signedCorrection
    x z D c cD b hcD hb
  have hn := screenedWeightedMomentEnergy_nonneg x z D c b
  linarith

/-- Both optimizers used by the exact signed decomposition exist
unconditionally for every finite dictionary, including singular designs. -/
theorem exists_exact_signed_decomposition (x : H) (z : ι → H)
    (D : H →ₗ[ℝ] H) (c : ι → ℝ) :
    ∃ cD b : ι → ℝ,
      (∀ i, inner ℝ (D (z i))
        (finiteSchurCombination (fun j => D (z j)) cD) =
          inner ℝ (D (z i)) (D x)) ∧
      (∀ i, inner ℝ (z i) (finiteSchurCombination z b) =
        inner ℝ (z i) (D (finiteSchurResidual x z c))) ∧
      screenedWeightedMomentEnergy x z D c b =
        weightedOptimizerFloor x z D cD +
          signedOptimizerCorrection z D c cD b := by
  obtain ⟨cD, hcD⟩ := finiteSchur_exists_normal (D x) (fun i => D (z i))
  obtain ⟨b, hb⟩ := finiteSchur_exists_normal (D (finiteSchurResidual x z c)) z
  exact ⟨cD, b, hcD, hb,
    screenedWeightedMomentEnergy_eq_floor_add_signedCorrection x z D c cD b hcD hb⟩

private theorem normal_residual_inner_combination_zero (x : H) (z : ι → H)
    (c b : ι → ℝ)
    (hc : ∀ i, inner ℝ (z i) (finiteSchurCombination z c) = inner ℝ (z i) x) :
    inner ℝ (finiteSchurResidual x z c) (finiteSchurCombination z b) = 0 := by
  have ho (i : ι) : inner ℝ (finiteSchurResidual x z c) (z i) = 0 := by
    rw [real_inner_comm]
    exact finiteSchurResidual_orthogonal x z c hc i
  simp [finiteSchurCombination, inner_sum, real_inner_smul_right, ho]

/-- In the original optimizer's orthogonal complement, screening a test
vector changes none of its pairing with that optimizer's residual. -/
theorem originalResidual_inner_screened (x y : H) (z : ι → H) (c b : ι → ℝ)
    (hc : ∀ i, inner ℝ (z i) (finiteSchurCombination z c) = inner ℝ (z i) x) :
    inner ℝ (finiteSchurResidual x z c) (finiteSchurResidual y z b) =
      inner ℝ (finiteSchurResidual x z c) y := by
  unfold finiteSchurResidual
  rw [inner_sub_right]
  change inner ℝ (finiteSchurResidual x z c) y -
    inner ℝ (finiteSchurResidual x z c) (finiteSchurCombination z b) = _
  rw [normal_residual_inner_combination_zero x z c b hc, sub_zero]
  rfl

private theorem normal_residual_pairing (h : H) (z : ι → H) (b : ι → ℝ)
    (hb : ∀ i, inner ℝ (z i) (finiteSchurCombination z b) = inner ℝ (z i) h) :
    inner ℝ h (finiteSchurResidual h z b) = ‖finiteSchurResidual h z b‖ ^ 2 := by
  have ho : inner ℝ (finiteSchurCombination z b) (finiteSchurResidual h z b) = 0 := by
    rw [real_inner_comm]
    exact normal_residual_inner_combination_zero h z b b hb
  have he : h = finiteSchurResidual h z b + finiteSchurCombination z b := by
    unfold finiteSchurResidual
    abel
  calc
    inner ℝ h (finiteSchurResidual h z b) =
        inner ℝ (finiteSchurResidual h z b + finiteSchurCombination z b)
          (finiteSchurResidual h z b) :=
      congrArg (fun v => inner ℝ v (finiteSchurResidual h z b)) he
    _ = ‖finiteSchurResidual h z b‖ ^ 2 := by
      rw [inner_add_left, ho, add_zero, real_inner_self_eq_norm_sq]

/-- For a symmetric multiplier, the second compressed operator moment is
the actual screened norm square. The second screening coefficients may be
arbitrary, since the original optimizer residual is orthogonal to the atoms. -/
theorem screenedSecondMoment_eq_energy
    (x : H) (z : ι → H) (D : H →ₗ[ℝ] H) (c b b₂ : ι → ℝ)
    (hD : ∀ u v, inner ℝ u (D v) = inner ℝ (D u) v)
    (hc : ∀ i, inner ℝ (z i) (finiteSchurCombination z c) = inner ℝ (z i) x)
    (hb : ∀ i, inner ℝ (z i) (finiteSchurCombination z b) =
      inner ℝ (z i) (D (finiteSchurResidual x z c))) :
    inner ℝ (finiteSchurResidual x z c)
      (finiteSchurResidual
        (D (finiteSchurResidual (D (finiteSchurResidual x z c)) z b)) z b₂) =
      screenedWeightedMomentEnergy x z D c b := by
  rw [originalResidual_inner_screened x _ z c b₂ hc, hD,
    normal_residual_pairing _ z b hb]
  rfl

/-- The complete second compressed moment equals `ε₂ + δ₂ − screen`. -/
theorem screenedSecondMoment_eq_floor_add_signedCorrection
    (x : H) (z : ι → H) (D : H →ₗ[ℝ] H) (c cD b b₂ : ι → ℝ)
    (hD : ∀ u v, inner ℝ u (D v) = inner ℝ (D u) v)
    (hc : ∀ i, inner ℝ (z i) (finiteSchurCombination z c) = inner ℝ (z i) x)
    (hcD : ∀ i, inner ℝ (D (z i))
      (finiteSchurCombination (fun j => D (z j)) cD) =
        inner ℝ (D (z i)) (D x))
    (hb : ∀ i, inner ℝ (z i) (finiteSchurCombination z b) =
      inner ℝ (z i) (D (finiteSchurResidual x z c))) :
    inner ℝ (finiteSchurResidual x z c)
      (finiteSchurResidual
        (D (finiteSchurResidual (D (finiteSchurResidual x z c)) z b)) z b₂) =
      weightedOptimizerFloor x z D cD + signedOptimizerCorrection z D c cD b := by
  rw [screenedSecondMoment_eq_energy x z D c b b₂ hD hc hb]
  exact screenedWeightedMomentEnergy_eq_floor_add_signedCorrection x z D c cD b hcD hb

section ScalarLimits

variable {e ε Γ M : ℕ → ℝ}

/-- Pointwise exact signed decomposition implies `Γ₊ / e ≤ M / e`. -/
theorem positiveCorrection_ratio_le_moment_ratio
    (he : ∀ n, 0 < e n) (hε : ∀ n, 0 ≤ ε n) (hM : ∀ n, 0 ≤ M n)
    (hidentity : ∀ n, M n = ε n + Γ n) (n : ℕ) :
    max (Γ n) 0 / e n ≤ M n / e n := by
  apply div_le_div_of_nonneg_right _ (he n).le
  apply max_le
  · linarith [hε n, hidentity n]
  · exact hM n

/-- Converse upper control retains the weighted floor exactly. -/
theorem moment_ratio_le_floor_add_positiveCorrection_ratio
    (he : ∀ n, 0 < e n) (hidentity : ∀ n, M n = ε n + Γ n) (n : ℕ) :
    M n / e n ≤ ε n / e n + max (Γ n) 0 / e n := by
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (he n).le
  linarith [hidentity n, le_max_left (Γ n) (0 : ℝ)]

/-- `Γ₋ / e ≤ ε / e`; this isolates the part already solved by a floor estimate. -/
theorem negativeCorrection_ratio_le_floor_ratio
    (he : ∀ n, 0 < e n) (hε : ∀ n, 0 ≤ ε n) (hM : ∀ n, 0 ≤ M n)
    (hidentity : ∀ n, M n = ε n + Γ n) (n : ℕ) :
    max (-Γ n) 0 / e n ≤ ε n / e n := by
  apply div_le_div_of_nonneg_right _ (he n).le
  apply max_le
  · linarith [hM n, hidentity n]
  · exact hε n

/-- Exact reduction to the positive signed correction. The substantive
weighted-floor smallness input is displayed rather than silently assumed. -/
theorem normalizedMoment_tendsto_zero_iff_positiveCorrection
    (he : ∀ n, 0 < e n) (hε : ∀ n, 0 ≤ ε n) (hM : ∀ n, 0 ≤ M n)
    (hidentity : ∀ n, M n = ε n + Γ n)
    (hfloor : Tendsto (fun n => ε n / e n) atTop (𝓝 0)) :
    Tendsto (fun n => M n / e n) atTop (𝓝 0) ↔
      Tendsto (fun n => max (Γ n) 0 / e n) atTop (𝓝 0) := by
  constructor
  · intro hlim
    exact squeeze_zero
      (fun n => div_nonneg (le_max_right (Γ n) (0 : ℝ)) (he n).le)
      (positiveCorrection_ratio_le_moment_ratio he hε hM hidentity) hlim
  · intro hlim
    have hsum : Tendsto
        (fun n => ε n / e n + max (Γ n) 0 / e n) atTop (𝓝 0) := by
      simpa using hfloor.add hlim
    exact squeeze_zero
      (fun n => div_nonneg (hM n) (he n).le)
      (moment_ratio_le_floor_add_positiveCorrection_ratio he hidentity) hsum

/-- The full negative correction vanishes after the same normalization. -/
theorem normalizedNegativeCorrection_tendsto_zero
    (he : ∀ n, 0 < e n) (hε : ∀ n, 0 ≤ ε n) (hM : ∀ n, 0 ≤ M n)
    (hidentity : ∀ n, M n = ε n + Γ n)
    (hfloor : Tendsto (fun n => ε n / e n) atTop (𝓝 0)) :
    Tendsto (fun n => max (-Γ n) 0 / e n) atTop (𝓝 0) :=
  squeeze_zero
    (fun n => div_nonneg (le_max_right (-Γ n) (0 : ℝ)) (he n).le)
    (negativeCorrection_ratio_le_floor_ratio he hε hM hidentity) hfloor

/-- The exact signed correction itself has the same normalized zero limit
once the floor does. This algebraic equivalence needs no positivity input. -/
theorem normalizedMoment_tendsto_zero_iff_signedCorrection
    (hidentity : ∀ n, M n = ε n + Γ n)
    (hfloor : Tendsto (fun n => ε n / e n) atTop (𝓝 0)) :
    Tendsto (fun n => M n / e n) atTop (𝓝 0) ↔
      Tendsto (fun n => Γ n / e n) atTop (𝓝 0) := by
  constructor
  · intro hlim
    have heq : (fun n => Γ n / e n) =
        (fun n => M n / e n - ε n / e n) := by
      funext n
      rw [← sub_div]
      congr 1
      linarith [hidentity n]
    rw [heq]
    simpa using hlim.sub hfloor
  · intro hlim
    have heq : (fun n => M n / e n) =
        (fun n => ε n / e n + Γ n / e n) := by
      funext n
      rw [← add_div, hidentity n]
    rw [heq]
    simpa using hfloor.add hlim

end ScalarLimits

/-- A varying finite dictionary is allowed. The input floor is the actual
weighted optimum, and the output correction is the actual signed difference
of two complete Hilbert-space norm squares. -/
theorem screenedWeightedMoment_normalized_tendsto_iff
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (x : H) (z : ∀ n, ι n → H) (D : H →ₗ[ℝ] H)
    (c cD b : ∀ n, ι n → ℝ) (e : ℕ → ℝ) (he : ∀ n, 0 < e n)
    (hcD : ∀ n i, inner ℝ (D (z n i))
      (finiteSchurCombination (fun j => D (z n j)) (cD n)) =
        inner ℝ (D (z n i)) (D x))
    (hb : ∀ n i, inner ℝ (z n i) (finiteSchurCombination (z n) (b n)) =
      inner ℝ (z n i) (D (finiteSchurResidual x (z n) (c n))))
    (hfloor : Tendsto
      (fun n => weightedOptimizerFloor x (z n) D (cD n) / e n) atTop (𝓝 0)) :
    Tendsto
      (fun n => screenedWeightedMomentEnergy x (z n) D (c n) (b n) / e n)
      atTop (𝓝 0) ↔
    Tendsto
      (fun n => max (signedOptimizerCorrection (z n) D (c n) (cD n) (b n)) 0 / e n)
      atTop (𝓝 0) := by
  apply normalizedMoment_tendsto_zero_iff_positiveCorrection he
    (fun n => weightedOptimizerFloor_nonneg x (z n) D (cD n))
    (fun n => screenedWeightedMomentEnergy_nonneg x (z n) D (c n) (b n))
    (fun n => screenedWeightedMomentEnergy_eq_floor_add_signedCorrection
      x (z n) D (c n) (cD n) (b n) (hcD n) (hb n)) hfloor

end RiemannResearch.Analysis.SignedOptimizerMoment
