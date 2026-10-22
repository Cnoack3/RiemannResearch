/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteGramCapacity
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import RiemannResearch.Analysis.SignalNormalizationStability
import RiemannResearch.Analysis.FiniteSamplingDiagonal
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Sampling a signal in the actual inverse-Gram metric

Source: the user-directed Ramanujan/zero-equidistribution argument,
21 October 2026. The inverse is the existing actual Hilbert Gram inverse,
constructed from linear independence. The inverse metric is represented
isometrically by the minimum-observation vector, so no diagonal or
independent-phase replacement of the original Gram form occurs.

The exact mixed remainder precedes the relative-error bound. The final
diagonal selection needs only fixed-stage coordinate convergence; no
uniform bound on growing inverse Gram operators is assumed.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.FiniteGramSignalStability
open FiniteHilbertGram FiniteHilbertConstraints FiniteGramCapacity
open SignalNormalizationStability

variable {ι H : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The Riesz realization of the actual inverse Gram map. -/
def sourceLinear {v : ι → H} (hv : LinearIndependent ℝ v) :
    (ι → ℝ) →ₗ[ℝ] H :=
  (Fintype.linearCombination ℝ v).comp (gramEquiv hv).symm.toLinearMap

@[simp] theorem sourceLinear_apply {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) : sourceLinear hv b = minimumVector hv b := rfl

theorem minimumVector_sub {v : ι → H} (hv : LinearIndependent ℝ v)
    (b c : ι → ℝ) :
    minimumVector hv (b - c) = minimumVector hv b - minimumVector hv c :=
  (sourceLinear hv).map_sub b c

/-- Exactly bᵀ H⁻¹ c, retaining every signed mixed term. -/
def inversePair {v : ι → H} (hv : LinearIndependent ℝ v)
    (b c : ι → ℝ) : ℝ :=
  inner ℝ (minimumVector hv b) (minimumVector hv c)

/-- Exactly the H⁻¹ norm of the source vector. -/
def inverseNorm {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) : ℝ := ‖minimumVector hv b‖

theorem inversePair_eq {v : ι → H} (hv : LinearIndependent ℝ v)
    (b c : ι → ℝ) :
    inversePair hv b c = ∑ i, inverseSource hv b i * c i := by
  change inner ℝ (Fintype.linearCombination ℝ v (inverseSource hv b))
    (minimumVector hv c) = _
  exact inner_synthesis_minimumVector hv c (inverseSource hv b)

theorem inversePair_self {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) : inversePair hv b b = capacity hv b := by
  rw [inversePair, real_inner_self_eq_norm_sq, ← capacity_eq_norm_sq]

theorem inverseNorm_sq {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) : inverseNorm hv b ^ 2 = capacity hv b :=
  (capacity_eq_norm_sq hv b).symm

/-- Exact normalization uses the true source b, not its sampled estimate z. -/
def normalizedCoefficients {v : ι → H} (hv : LinearIndependent ℝ v)
    (b z : ι → ℝ) : ι → ℝ :=
  (inversePair hv b z)⁻¹ • inverseSource hv z

theorem synthesis_normalizedCoefficients {v : ι → H}
    (hv : LinearIndependent ℝ v) (b z : ι → ℝ) :
    Fintype.linearCombination ℝ v (normalizedCoefficients hv b z) =
      normalized (minimumVector hv b) (minimumVector hv z) := by
  rw [normalizedCoefficients, map_smul]
  rfl

theorem normalizedCoefficients_signal {v : ι → H}
    (hv : LinearIndependent ℝ v) (b z : ι → ℝ)
    (hd : inversePair hv b z ≠ 0) :
    (∑ i, normalizedCoefficients hv b z i * b i) = 1 := by
  have hp : (∑ i, inverseSource hv z i * b i) = inversePair hv b z := by
    rw [← inversePair_eq]
    exact real_inner_comm (minimumVector hv b) (minimumVector hv z)
  simp only [normalizedCoefficients, Pi.smul_apply, smul_eq_mul, mul_assoc,
    ← Finset.mul_sum, hp, inv_mul_cancel₀ hd]

theorem normalized_energy_exact {v : ι → H}
    (hv : LinearIndependent ℝ v) (b z : ι → ℝ)
    (hb : b ≠ 0) (hd : inversePair hv b z ≠ 0) :
    ‖Fintype.linearCombination ℝ v (normalizedCoefficients hv b z)‖ ^ 2 =
      1 / capacity hv b +
        ‖Fintype.linearCombination ℝ v
          (normalizedCoefficients hv b z - normalizedCoefficients hv b b)‖ ^ 2 := by
  rw [map_sub, synthesis_normalizedCoefficients, synthesis_normalizedCoefficients]
  simpa only [capacity_eq_norm_sq] using
    normalized_pythagoras (minimumVector hv b) (minimumVector hv z)
      (by simpa only [← capacity_eq_norm_sq] using capacity_pos hv b hb) hd

/-- Exact inverse-metric Gram-determinant remainder. -/
theorem normalized_error_exact {v : ι → H}
    (hv : LinearIndependent ℝ v) (b z : ι → ℝ)
    (hb : b ≠ 0) (hd : inversePair hv b z ≠ 0) :
    ‖Fintype.linearCombination ℝ v
      (normalizedCoefficients hv b z - normalizedCoefficients hv b b)‖ ^ 2 =
      (capacity hv b * capacity hv (z - b) - inversePair hv b (z - b) ^ 2) /
        (capacity hv b * inversePair hv b z ^ 2) := by
  have he : minimumVector hv b + minimumVector hv (z - b) =
      minimumVector hv z := by
    rw [minimumVector_sub]
    abel
  have hd' : inner ℝ (minimumVector hv b)
      (minimumVector hv b + minimumVector hv (z - b)) ≠ 0 := by
    rw [he]
    exact hd
  have h := SignalNormalizationStability.normalized_error_exact
    (minimumVector hv b) (minimumVector hv (z - b))
    (by simpa only [← capacity_eq_norm_sq] using capacity_pos hv b hb) hd'
  rw [map_sub, synthesis_normalizedCoefficients, synthesis_normalizedCoefficients]
  simpa only [he, capacity_eq_norm_sq, inversePair] using h

theorem normalized_pairing_pos {v : ι → H}
    (hv : LinearIndependent ℝ v) (b z : ι → ℝ) (hb : b ≠ 0)
    {ε : ℝ} (hε : ε < 1)
    (he : inverseNorm hv (z - b) ≤ ε * inverseNorm hv b) :
    0 < inversePair hv b z := by
  have h := pairing_pos (minimumVector hv b)
    (minimumVector hv z - minimumVector hv b)
    (by simpa only [← capacity_eq_norm_sq] using capacity_pos hv b hb) hε
    (by simpa only [inverseNorm, minimumVector_sub] using he)
  simpa only [add_sub_cancel, inversePair] using h

/-- A dimension-free quadratic stability bound in the actual inverse metric. -/
theorem normalized_error_le {v : ι → H}
    (hv : LinearIndependent ℝ v) (b z : ι → ℝ) (hb : b ≠ 0)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1)
    (he : inverseNorm hv (z - b) ≤ ε * inverseNorm hv b) :
    ‖Fintype.linearCombination ℝ v
      (normalizedCoefficients hv b z - normalizedCoefficients hv b b)‖ ^ 2 ≤
      ε ^ 2 / (capacity hv b * (1 - ε) ^ 2) := by
  have h := SignalNormalizationStability.normalized_error_le
    (minimumVector hv b) (minimumVector hv z - minimumVector hv b)
    (by simpa only [← capacity_eq_norm_sq] using capacity_pos hv b hb)
    hε0 hε (by simpa only [inverseNorm, minimumVector_sub] using he)
  rw [map_sub, synthesis_normalizedCoefficients, synthesis_normalizedCoefficients]
  simpa only [add_sub_cancel, capacity_eq_norm_sq] using h

theorem minimumVector_tendsto {v : ι → H} (hv : LinearIndependent ℝ v)
    {α : Type*} {l : Filter α} (b : ι → ℝ) (z : α → ι → ℝ)
    (hz : ∀ i, Tendsto (fun t => z t i) l (𝓝 (b i))) :
    Tendsto (fun t => minimumVector hv (z t)) l (𝓝 (minimumVector hv b)) := by
  have h := ((sourceLinear hv).continuous_of_finiteDimensional.tendsto b).comp
    (tendsto_pi_nhds.2 hz)
  exact h

/-- Finite coordinate convergence implies convergence in H⁻¹, with no
hypothesis controlling the inverse uniformly across different stages. -/
theorem inverseNorm_error_tendsto {v : ι → H} (hv : LinearIndependent ℝ v)
    {α : Type*} {l : Filter α} (b : ι → ℝ) (z : α → ι → ℝ)
    (hz : ∀ i, Tendsto (fun t => z t i) l (𝓝 (b i))) :
    Tendsto (fun t => inverseNorm hv (z t - b)) l (𝓝 0) := by
  have h := (minimumVector_tendsto hv b z hz).sub
    (tendsto_const_nhds : Tendsto (fun _ : α => minimumVector hv b)
      l (𝓝 (minimumVector hv b)))
  have h' : Tendsto (fun t => minimumVector hv (z t - b)) l (𝓝 0) := by
    simpa only [minimumVector_sub, sub_self] using h
  simpa only [inverseNorm, norm_zero] using h'.norm

theorem normalizedCoefficients_tendsto {v : ι → H}
    (hv : LinearIndependent ℝ v) {α : Type*} {l : Filter α}
    (b : ι → ℝ) (hb : b ≠ 0) (z : α → ι → ℝ)
    (hz : ∀ i, Tendsto (fun t => z t i) l (𝓝 (b i))) :
    Tendsto (fun t => normalizedCoefficients hv b (z t)) l
      (𝓝 (normalizedCoefficients hv b b)) := by
  have hz' := tendsto_pi_nhds.2 hz
  have hs : Tendsto (fun t => inverseSource hv (z t)) l
      (𝓝 (inverseSource hv b)) :=
    (((gramEquiv hv).symm.toLinearMap.continuous_of_finiteDimensional).tendsto b).comp hz'
  have hd : Tendsto (fun t => inversePair hv b (z t)) l
      (𝓝 (inversePair hv b b)) :=
    tendsto_const_nhds.inner (minimumVector_tendsto hv b z hz)
  have hn : inversePair hv b b ≠ 0 := by
    rw [inversePair_self]
    exact ne_of_gt (capacity_pos hv b hb)
  have hc := (tendsto_const_nhds :
    Tendsto (fun _ : α => (1 : ℝ)) l (𝓝 1)).div hd hn
  simpa only [normalizedCoefficients, Pi.div_apply, one_div] using hc.smul hs

/-- Growing finite inverse metrics allow arbitrarily accurate increasing
sample cutoffs. Fixed-stage convergence suffices, without a uniform rate. -/
theorem exists_strictMono_diagonal_relative_error
    {J : ℕ → Type*} [∀ j, Fintype (J j)]
    (v : (j : ℕ) → J j → H) (hv : ∀ j, LinearIndependent ℝ (v j))
    (b : (j : ℕ) → J j → ℝ) (hb : ∀ j, b j ≠ 0)
    (z : (j : ℕ) → ℕ → J j → ℝ) (ε : ℕ → ℝ)
    (hε : ∀ j, 0 < ε j)
    (hz : ∀ j i, Tendsto (fun n => z j n i) atTop (𝓝 (b j i))) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ (∀ j, j ≤ τ j) ∧
      ∀ j, inverseNorm (hv j) (z j (τ j) - b j) ≤
        ε j * inverseNorm (hv j) (b j) := by
  have hp : ∀ j, 0 < inverseNorm (hv j) (b j) := by
    intro j
    have h := capacity_pos (hv j) (b j) (hb j)
    rw [← inverseNorm_sq] at h
    have hn : 0 ≤ inverseNorm (hv j) (b j) := norm_nonneg _
    nlinarith
  obtain ⟨τ, hτ, hi, he⟩ :=
    FiniteSamplingDiagonal.exists_strictMono_diagonal_abs_le
      (fun j n => inverseNorm (hv j) (z j n - b j))
      (fun j => ε j * inverseNorm (hv j) (b j))
      (fun j => inverseNorm_error_tendsto (hv j) (b j) (z j) (hz j))
      (fun j => mul_pos (hε j) (hp j))
  refine ⟨τ, hτ, hi, fun j => ?_⟩
  exact (le_abs_self _).trans (he j)

/-- The true source is the observation vector of a unit target. -/
theorem capacity_le_one {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (target : H) (ht : ‖target‖ ^ 2 = 1)
    (hobs : ∀ i, inner ℝ (v i) target = b i) :
    capacity hv b ≤ 1 := by
  have he : inverseCoeff hv target = inverseSource hv b := by
    unfold inverseCoeff inverseSource
    congr 1
    funext i
    exact hobs i
  have hn := sq_nonneg
    ‖target - Fintype.linearCombination ℝ v (inverseCoeff hv target)‖
  rw [residual_schur_value, ht, he] at hn
  simp only [cross, hobs] at hn
  change 0 ≤ 1 - capacity hv b at hn
  linarith

/-- Exact target error, including the entire sampled-optimizer displacement. -/
theorem normalized_target_error_exact {v : ι → H}
    (hv : LinearIndependent ℝ v) (b z : ι → ℝ)
    (hb : b ≠ 0) (hd : inversePair hv b z ≠ 0)
    (target : H) (ht : ‖target‖ ^ 2 = 1)
    (hobs : ∀ i, inner ℝ (v i) target = b i) :
    ‖target - Fintype.linearCombination ℝ v (normalizedCoefficients hv b z)‖ ^ 2 =
      1 / capacity hv b - 1 +
        ‖Fintype.linearCombination ℝ v
          (normalizedCoefficients hv b z - normalizedCoefficients hv b b)‖ ^ 2 := by
  have hm : inner ℝ target
      (Fintype.linearCombination ℝ v (normalizedCoefficients hv b z)) = 1 := by
    rw [real_inner_comm, inner_synthesis_left]
    simp_rw [hobs]
    exact normalizedCoefficients_signal hv b z hd
  rw [norm_sub_sq_real, ht, hm, normalized_energy_exact hv b z hb hd]
  ring

theorem normalized_target_error_le {v : ι → H}
    (hv : LinearIndependent ℝ v) (b z : ι → ℝ) (hb : b ≠ 0)
    (target : H) (ht : ‖target‖ ^ 2 = 1)
    (hobs : ∀ i, inner ℝ (v i) target = b i)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1)
    (he : inverseNorm hv (z - b) ≤ ε * inverseNorm hv b) :
    ‖target - Fintype.linearCombination ℝ v (normalizedCoefficients hv b z)‖ ^ 2 ≤
      1 / capacity hv b - 1 +
        ε ^ 2 / (capacity hv b * (1 - ε) ^ 2) := by
  rw [normalized_target_error_exact hv b z hb
    (ne_of_gt (normalized_pairing_pos hv b z hb hε he)) target ht hobs]
  linarith [normalized_error_le hv b z hb hε0 hε he]

/-- Literal inverse-matrix interpretation of the complete dual pairing. -/
theorem inversePair_eq_matrix [DecidableEq ι] {v : ι → H}
    (hv : LinearIndependent ℝ v) (b c : ι → ℝ) :
    inversePair hv b c =
      dotProduct b ((FiniteHilbertGram.gramMatrix v)⁻¹.mulVec c) := by
  calc
    inversePair hv b c = inversePair hv c b :=
      real_inner_comm (minimumVector hv c) (minimumVector hv b)
    _ = ∑ i, inverseSource hv c i * b i := inversePair_eq hv c b
    _ = _ := by
      rw [FiniteHilbertGram.gramMatrix_inverseSource hv]
      unfold dotProduct
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem inverseNorm_sq_eq_matrix [DecidableEq ι] {v : ι → H}
    (hv : LinearIndependent ℝ v) (b : ι → ℝ) :
    inverseNorm hv b ^ 2 =
      dotProduct b ((FiniteHilbertGram.gramMatrix v)⁻¹.mulVec b) := by
  rw [inverseNorm_sq, ← inversePair_self, inversePair_eq_matrix]

/-- The coefficient formula is precisely H⁻¹ z / (bᵀ H⁻¹ z). -/
theorem normalizedCoefficients_eq_inverseMatrix [DecidableEq ι] {v : ι → H}
    (hv : LinearIndependent ℝ v) (b z : ι → ℝ) :
    normalizedCoefficients hv b z =
      (dotProduct b ((FiniteHilbertGram.gramMatrix v)⁻¹.mulVec z))⁻¹ •
        (FiniteHilbertGram.gramMatrix v)⁻¹.mulVec z := by
  rw [normalizedCoefficients, inversePair_eq_matrix,
    FiniteHilbertGram.gramMatrix_inverseSource hv]

/-- Anisotropic entrywise sampling budgets certify the actual H⁻¹ error.
No mixed inverse entry is discarded before taking its absolute majorant. -/
theorem inverseNorm_sq_le_entrywise [DecidableEq ι] {v : ι → H}
    (hv : LinearIndependent ℝ v) (e η : ι → ℝ)
    (hη : ∀ i, 0 ≤ η i) (he : ∀ i, |e i| ≤ η i) :
    inverseNorm hv e ^ 2 ≤
      ∑ i, ∑ j, |(gramMatrix v)⁻¹ i j| * η i * η j := by
  rw [inverseNorm_sq_eq_matrix]
  let A : Matrix ι ι ℝ := (gramMatrix v)⁻¹
  change (∑ i, e i * (∑ j, A i j * e j)) ≤
    ∑ i, ∑ j, |A i j| * η i * η j
  simp_rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  calc
    e i * ((gramMatrix v)⁻¹ i j * e j) ≤
        |e i * ((gramMatrix v)⁻¹ i j * e j)| := le_abs_self _
    _ = |(gramMatrix v)⁻¹ i j| * (|e i| * |e j|) := by
      rw [abs_mul, abs_mul]
      ring
    _ ≤ |(gramMatrix v)⁻¹ i j| * (η i * η j) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (he i) (he j) (abs_nonneg _) (hη i)) (abs_nonneg _)
    _ = _ := by ring

/-- Remove exactly the component parallel to the signal in the true dual metric. -/
def screenedSource {v : ι → H} (hv : LinearIndependent ℝ v)
    (b z : ι → ℝ) : ι → ℝ :=
  z - (inversePair hv b z / capacity hv b) • b

theorem minimumVector_screenedSource {v : ι → H}
    (hv : LinearIndependent ℝ v) (b z : ι → ℝ) :
    minimumVector hv (screenedSource hv b z) =
      orthogonalError (minimumVector hv b) (minimumVector hv z) := by
  change sourceLinear hv (z - (inversePair hv b z / capacity hv b) • b) = _
  rw [map_sub, map_smul, sourceLinear_apply, sourceLinear_apply]
  simp only [orthogonalError, inversePair, capacity_eq_norm_sq]

theorem inversePair_screenedSource {v : ι → H}
    (hv : LinearIndependent ℝ v) (b z : ι → ℝ) (hb : b ≠ 0) :
    inversePair hv b (screenedSource hv b z) = 0 := by
  unfold inversePair
  rw [minimumVector_screenedSource]
  exact orthogonalError_pairing _ _
    (by simpa only [← capacity_eq_norm_sq] using capacity_pos hv b hb)

/-- Complete signed rank-one correction, with no entrywise absolute values. -/
theorem inverseNorm_screenedSource_sq {v : ι → H}
    (hv : LinearIndependent ℝ v) (b z : ι → ℝ) (hb : b ≠ 0) :
    inverseNorm hv (screenedSource hv b z) ^ 2 =
      inverseNorm hv z ^ 2 - inversePair hv b z ^ 2 / capacity hv b := by
  have hp : 0 < ‖minimumVector hv b‖ ^ 2 := by
    simpa only [← capacity_eq_norm_sq] using capacity_pos hv b hb
  rw [inverseNorm, minimumVector_screenedSource,
    orthogonalError_norm_sq _ _ hp]
  simp only [inverseNorm, inversePair, capacity_eq_norm_sq]
  have hn : ‖minimumVector hv b‖ ≠ 0 := by
    intro h
    rw [h] at hp
    norm_num at hp
  field_simp [hn]

/-- Exact normalized error depends only on the screened source. -/
theorem normalized_error_screenedSource {v : ι → H}
    (hv : LinearIndependent ℝ v) (b z : ι → ℝ)
    (hd : inversePair hv b z ≠ 0) :
    ‖Fintype.linearCombination ℝ v
      (normalizedCoefficients hv b z - normalizedCoefficients hv b b)‖ ^ 2 =
      inverseNorm hv (screenedSource hv b z) ^ 2 / inversePair hv b z ^ 2 := by
  rw [map_sub, synthesis_normalizedCoefficients, synthesis_normalizedCoefficients,
    normalized_error_screened _ _ hd]
  rw [inverseNorm, minimumVector_screenedSource]
  rfl

theorem normalized_target_error_screenedSource {v : ι → H}
    (hv : LinearIndependent ℝ v) (b z : ι → ℝ)
    (hb : b ≠ 0) (hd : inversePair hv b z ≠ 0)
    (target : H) (ht : ‖target‖ ^ 2 = 1)
    (hobs : ∀ i, inner ℝ (v i) target = b i) :
    ‖target - Fintype.linearCombination ℝ v (normalizedCoefficients hv b z)‖ ^ 2 =
      1 / capacity hv b - 1 +
        inverseNorm hv (screenedSource hv b z) ^ 2 / inversePair hv b z ^ 2 := by
  rw [normalized_target_error_exact hv b z hb hd target ht hobs,
    normalized_error_screenedSource hv b z hd]

/-- A screened relative budget suffices; radial signal error can be arbitrary. -/
theorem normalized_target_error_le_of_screenedSource {v : ι → H}
    (hv : LinearIndependent ℝ v) (b z : ι → ℝ)
    (hb : b ≠ 0) (hd : inversePair hv b z ≠ 0)
    (target : H) (ht : ‖target‖ ^ 2 = 1)
    (hobs : ∀ i, inner ℝ (v i) target = b i)
    (η : ℝ) (hη : 0 ≤ η)
    (he : inverseNorm hv (screenedSource hv b z) ≤ η * |inversePair hv b z|) :
    ‖target - Fintype.linearCombination ℝ v (normalizedCoefficients hv b z)‖ ^ 2 ≤
      1 / capacity hv b - 1 + η ^ 2 := by
  rw [normalized_target_error_screenedSource hv b z hb hd target ht hobs]
  apply add_le_add le_rfl
  apply (div_le_iff₀ (sq_pos_of_ne_zero hd)).mpr
  have hsq := (sq_le_sq₀ (norm_nonneg (minimumVector hv (screenedSource hv b z)))
    (mul_nonneg hη (abs_nonneg _))).mpr he
  simpa only [mul_pow, sq_abs, inverseNorm] using hsq

theorem inverseNorm_sq_add {v : ι → H} (hv : LinearIndependent ℝ v)
    (x y : ι → ℝ) :
    inverseNorm hv (x + y) ^ 2 =
      inverseNorm hv x ^ 2 + 2 * inversePair hv x y + inverseNorm hv y ^ 2 := by
  change ‖sourceLinear hv (x + y)‖ ^ 2 = _
  rw [map_add, sourceLinear_apply, sourceLinear_apply, norm_add_sq_real]
  rfl


theorem normalized_error_screenedSource_norm {v : ι → H}
    (hv : LinearIndependent ℝ v) (b z : ι → ℝ)
    (hd : inversePair hv b z ≠ 0) :
    ‖Fintype.linearCombination ℝ v
      (normalizedCoefficients hv b z - normalizedCoefficients hv b b)‖ =
      inverseNorm hv (screenedSource hv b z) / |inversePair hv b z| := by
  rw [map_sub, synthesis_normalizedCoefficients, synthesis_normalizedCoefficients,
    normalized_sub_eq_smul_orthogonalError _ _ hd,
    norm_smul, Real.norm_eq_abs, abs_inv, inverseNorm, minimumVector_screenedSource]
  unfold inversePair
  ring


/-- Literal full inverse-matrix formula for the screened energy. -/
theorem inverseNorm_screenedSource_sq_eq_matrix [DecidableEq ι] {v : ι → H}
    (hv : LinearIndependent ℝ v) (b z : ι → ℝ) (hb : b ≠ 0) :
    inverseNorm hv (screenedSource hv b z) ^ 2 =
      dotProduct z ((gramMatrix v)⁻¹.mulVec z) -
        (dotProduct b ((gramMatrix v)⁻¹.mulVec z)) ^ 2 /
          dotProduct b ((gramMatrix v)⁻¹.mulVec b) := by
  have hc : capacity hv b = dotProduct b ((gramMatrix v)⁻¹.mulVec b) := by
    rw [← inversePair_self hv b, inversePair_eq_matrix]
  rw [inverseNorm_screenedSource_sq hv b z hb, inverseNorm_sq_eq_matrix,
    inversePair_eq_matrix, hc]

/-- Projective convergence in the actual inverse metric is exactly sufficient
for convergence of the normalized synthesis. -/
theorem normalized_synthesis_tendsto_iff_screenedRatio {v : ι → H}
    (hv : LinearIndependent ℝ v) {α : Type*} {l : Filter α}
    (b : ι → ℝ) (z : α → ι → ℝ)
    (hd : ∀ᶠ t in l, inversePair hv b (z t) ≠ 0) :
    Tendsto (fun t => Fintype.linearCombination ℝ v (normalizedCoefficients hv b (z t))) l
      (𝓝 (Fintype.linearCombination ℝ v (normalizedCoefficients hv b b))) ↔
    Tendsto (fun t => inverseNorm hv (screenedSource hv b (z t)) /
      |inversePair hv b (z t)|) l (𝓝 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply tendsto_congr'
  filter_upwards [hd] with t ht
  rw [← map_sub, normalized_error_screenedSource_norm hv b (z t) ht]

/-- Growing families need capacity saturation and vanishing screened ratios.
There is no uniform inverse-condition-number or radial-error assumption. -/
theorem target_tendsto_of_capacity_screenedRatio
    {J : ℕ → Type*} [∀ j, Fintype (J j)]
    (v : (j : ℕ) → J j → H) (hv : ∀ j, LinearIndependent ℝ (v j))
    (b z : (j : ℕ) → J j → ℝ) (hb : ∀ j, b j ≠ 0)
    (hd : ∀ j, inversePair (hv j) (b j) (z j) ≠ 0)
    (target : H) (ht : ‖target‖ ^ 2 = 1)
    (hobs : ∀ j i, inner ℝ (v j i) target = b j i)
    (hcap : Tendsto (fun j => capacity (hv j) (b j)) atTop (𝓝 1))
    (hratio : Tendsto (fun j =>
      inverseNorm (hv j) (screenedSource (hv j) (b j) (z j)) /
        |inversePair (hv j) (b j) (z j)|) atTop (𝓝 0)) :
    Tendsto (fun j => Fintype.linearCombination ℝ (v j)
      (normalizedCoefficients (hv j) (b j) (z j))) atTop (𝓝 target) := by
  have hlim : Tendsto (fun j => 1 / capacity (hv j) (b j) - 1 +
      (inverseNorm (hv j) (screenedSource (hv j) (b j) (z j)) /
        |inversePair (hv j) (b j) (z j)|) ^ 2) atTop (𝓝 0) := by
    have hc := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
      atTop (𝓝 1)).div hcap (by norm_num)
    simpa using (hc.sub_const 1).add (hratio.pow 2)
  have hsq : Tendsto (fun j => ‖target - Fintype.linearCombination ℝ (v j)
      (normalizedCoefficients (hv j) (b j) (z j))‖ ^ 2) atTop (𝓝 0) := by
    apply hlim.congr'
    apply Eventually.of_forall
    intro j
    dsimp only
    rw [normalized_target_error_screenedSource (hv j) (b j) (z j) (hb j)
      (hd j) target ht (hobs j), div_pow, sq_abs]
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm,
    Real.sqrt_zero, norm_sub_rev] using hn


theorem inversePair_add_right {v : ι → H} (hv : LinearIndependent ℝ v)
    (b x y : ι → ℝ) :
    inversePair hv b (x + y) = inversePair hv b x + inversePair hv b y := by
  simp only [inversePair, ← sourceLinear_apply, map_add, inner_add_right]

theorem inversePair_sub_right {v : ι → H} (hv : LinearIndependent ℝ v)
    (b x y : ι → ℝ) :
    inversePair hv b (x - y) = inversePair hv b x - inversePair hv b y := by
  simp only [inversePair, ← sourceLinear_apply, map_sub, inner_sub_right]

theorem inversePair_smul_right {v : ι → H} (hv : LinearIndependent ℝ v)
    (b x : ι → ℝ) (c : ℝ) :
    inversePair hv b (c • x) = c * inversePair hv b x := by
  simp only [inversePair, ← sourceLinear_apply, map_smul, real_inner_smul_right]

theorem inverseNorm_add_le {v : ι → H} (hv : LinearIndependent ℝ v)
    (x y : ι → ℝ) :
    inverseNorm hv (x + y) ≤ inverseNorm hv x + inverseNorm hv y := by
  change ‖sourceLinear hv (x + y)‖ ≤ ‖sourceLinear hv x‖ + ‖sourceLinear hv y‖
  rw [map_add]
  exact norm_add_le _ _

theorem screenedSource_add {v : ι → H} (hv : LinearIndependent ℝ v)
    (b x y : ι → ℝ) :
    screenedSource hv b (x + y) = screenedSource hv b x + screenedSource hv b y := by
  unfold screenedSource
  rw [inversePair_add_right, add_div, add_smul]
  abel

theorem screenedSource_sub {v : ι → H} (hv : LinearIndependent ℝ v)
    (b x y : ι → ℝ) :
    screenedSource hv b (x - y) = screenedSource hv b x - screenedSource hv b y := by
  unfold screenedSource
  rw [inversePair_sub_right, sub_div, sub_smul]
  abel

theorem screenedSource_smul {v : ι → H} (hv : LinearIndependent ℝ v)
    (b x : ι → ℝ) (c : ℝ) :
    screenedSource hv b (c • x) = c • screenedSource hv b x := by
  simp only [screenedSource, inversePair_smul_right, smul_sub, smul_smul, mul_div_assoc]

theorem screenedSource_self {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (hb : b ≠ 0) : screenedSource hv b b = 0 := by
  rw [screenedSource, inversePair_self,
    div_self (ne_of_gt (capacity_pos hv b hb)), one_smul, sub_self]

theorem screenedSource_sub_smul_self {v : ι → H} (hv : LinearIndependent ℝ v)
    (b z : ι → ℝ) (hb : b ≠ 0) (c : ℝ) :
    screenedSource hv b (z - c • b) = screenedSource hv b z := by
  rw [screenedSource_sub, screenedSource_smul, screenedSource_self hv b hb,
    smul_zero, sub_zero]

theorem inverseNorm_screenedSource_le {v : ι → H} (hv : LinearIndependent ℝ v)
    (b z : ι → ℝ) (hb : b ≠ 0) :
    inverseNorm hv (screenedSource hv b z) ≤ inverseNorm hv z := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change inverseNorm hv (screenedSource hv b z) ^ 2 ≤ inverseNorm hv z ^ 2
  rw [inverseNorm_screenedSource_sq hv b z hb]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (capacity_pos hv b hb).le)

/-- Any radial correction may be removed before bounding the density defect. -/
theorem inverseNorm_screenedSource_le_sub_smul {v : ι → H}
    (hv : LinearIndependent ℝ v) (b z : ι → ℝ) (hb : b ≠ 0) (c : ℝ) :
    inverseNorm hv (screenedSource hv b z) ≤ inverseNorm hv (z - c • b) := by
  have h := inverseNorm_screenedSource_le hv b (z - c • b) hb
  simpa only [screenedSource_sub_smul_self hv b z hb c] using h

/-- Exact signed interaction survives after radial screening. -/
theorem inverseNorm_screenedSource_sq_add {v : ι → H}
    (hv : LinearIndependent ℝ v) (b x y : ι → ℝ) :
    inverseNorm hv (screenedSource hv b (x + y)) ^ 2 =
      inverseNorm hv (screenedSource hv b x) ^ 2 +
      2 * inversePair hv (screenedSource hv b x) (screenedSource hv b y) +
      inverseNorm hv (screenedSource hv b y) ^ 2 := by
  rw [screenedSource_add, inverseNorm_sq_add]

/-- Exact least-squares split over every radial correction. -/
theorem inverseNorm_sub_smul_sq_eq_screened {v : ι → H}
    (hv : LinearIndependent ℝ v) (b z : ι → ℝ) (hb : b ≠ 0) (c : ℝ) :
    inverseNorm hv (z - c • b) ^ 2 =
      inverseNorm hv (screenedSource hv b z) ^ 2 +
        capacity hv b * (c - inversePair hv b z / capacity hv b) ^ 2 := by
  have hm : minimumVector hv (z - c • b) =
      minimumVector hv z - c • minimumVector hv b := by
    change sourceLinear hv (z - c • b) = _
    rw [map_sub, map_smul, sourceLinear_apply, sourceLinear_apply]
  have hx : inverseNorm hv (z - c • b) ^ 2 =
      inverseNorm hv z ^ 2 - 2 * c * inversePair hv b z + c ^ 2 * capacity hv b := by
    rw [inverseNorm, hm, norm_sub_sq_real, real_inner_smul_right,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_comm (minimumVector hv b) (minimumVector hv z)]
    simp only [inverseNorm, inversePair, capacity_eq_norm_sq]
    ring
  rw [hx, inverseNorm_screenedSource_sq hv b z hb]
  field_simp [ne_of_gt (capacity_pos hv b hb)]
  ring

/-- The actual inverse Gram form with its signal direction removed. -/
def screenedInverseMatrix [DecidableEq ι] {v : ι → H}
    (hv : LinearIndependent ℝ v) (b : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => (gramMatrix v)⁻¹ i j -
    inverseSource hv b i * inverseSource hv b j / capacity hv b

theorem inverseNorm_screenedSource_sq_eq_screenedMatrix [DecidableEq ι]
    {v : ι → H} (hv : LinearIndependent ℝ v) (b z : ι → ℝ) (hb : b ≠ 0) :
    inverseNorm hv (screenedSource hv b z) ^ 2 =
      ∑ i, ∑ j, screenedInverseMatrix hv b i j * z i * z j := by
  rw [inverseNorm_screenedSource_sq hv b z hb, inverseNorm_sq_eq_matrix,
    inversePair_eq]
  simp only [dotProduct, Matrix.mulVec, screenedInverseMatrix]
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem inverseNorm_screenedSource_sq_le_entrywise [DecidableEq ι]
    {v : ι → H} (hv : LinearIndependent ℝ v) (b e η : ι → ℝ) (hb : b ≠ 0)
    (hη : ∀ i, 0 ≤ η i) (he : ∀ i, |e i| ≤ η i) :
    inverseNorm hv (screenedSource hv b e) ^ 2 ≤
      ∑ i, ∑ j, |screenedInverseMatrix hv b i j| * η i * η j := by
  rw [inverseNorm_screenedSource_sq_eq_screenedMatrix hv b e hb]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  calc
    screenedInverseMatrix hv b i j * e i * e j ≤
        |screenedInverseMatrix hv b i j * e i * e j| := le_abs_self _
    _ = |screenedInverseMatrix hv b i j| * (|e i| * |e j|) := by
      rw [abs_mul, abs_mul]
      ring
    _ ≤ |screenedInverseMatrix hv b i j| * (η i * η j) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (he i) (he j) (abs_nonneg _) (hη i)) (abs_nonneg _)
    _ = _ := by ring

end RiemannResearch.Analysis.FiniteGramSignalStability
