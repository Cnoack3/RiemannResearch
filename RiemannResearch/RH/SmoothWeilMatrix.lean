import RiemannResearch.RH.WeilPositiveDiagonal
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Finite matrices of the complete smooth arithmetic Weil pairing

Source: user-provided `AnthropicRHBridges20260928.md`, section 2. This is a
finite-dimensional assembly of the established scalar explicit formula in
`WeilSpectralPairing`; no converse Weil criterion is asserted. The entries
retain all prime powers, both poles and the complete gamma term. The spectral
side uses actual zeta zeros with their actual analytic multiplicities.

Hermitian symmetry and completed-Nyman nullity are unconditional. Positivity
below has an explicit RH hypothesis. In particular, the completed Nyman
matrix is not a positive definite replacement for the Pareto Gram matrix.
-/

open MeasureTheory
open MeasureTheory.BilateralLaplace
open RiemannResearch.Analysis
open scoped ComplexConjugate BigOperators

namespace RiemannResearch.RH.SignedWeilCorrelation

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The entries are the complete arithmetic pairing, rather than a truncation. -/
def smoothWeilMatrix (f : ι → ℝ → ℂ) : Matrix ι ι ℂ :=
  fun i j => arithmeticWeilPairing (f i) (f j)

/-- The transform of a finite coefficient vector, written directly as a finite sum. -/
def smoothWeilTransform (f : ι → ℝ → ℂ) (c : ι → ℂ) (s : ℂ) : ℂ :=
  ∑ i, c i * centeredTransform (f i) s

/-- The conjugate-linear-first-variable quadratic value. -/
def smoothWeilMatrixQuadratic (f : ι → ℝ → ℂ) (c : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, conj (c i) * smoothWeilMatrix f i j * c j

theorem smoothWeilMatrix_hermitian {f : ι → ℝ → ℂ}
    (hf : ∀ i, SmoothSuperexponentialDecay (f i)) :
    (smoothWeilMatrix f).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  exact (arithmeticWeilPairing_hermitian (hf i) (hf j)).symm

private theorem finite_sum_tsum {α β : Type*} (s : Finset α) (a : α → β → ℂ)
    (ha : ∀ i ∈ s, Summable (a i)) :
    Summable (fun x => ∑ i ∈ s, a i x) ∧
      (∑ i ∈ s, ∑' x, a i x) = ∑' x, ∑ i ∈ s, a i x := by
  classical
  revert ha
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simp
  | @insert i s hi ih =>
      intro ha
      have hsi := ha i (Finset.mem_insert_self i s)
      obtain ⟨hs, heq⟩ := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      constructor
      · simpa only [Finset.sum_insert hi] using hsi.add hs
      · simp only [Finset.sum_insert hi]
        rw [heq, hsi.tsum_add hs]

private theorem finite_zero_factor (f : ι → ℝ → ℂ) (c : ι → ℂ)
    (ρ : Zeta23.zetaZeroConfig.carrier) :
    (∑ i, ∑ j, conj (c i) *
      ((Zeta23.zeroMult ρ : ℂ) * conj (centeredTransform (f i) (1 - conj (ρ : ℂ))) *
        centeredTransform (f j) (ρ : ℂ)) * c j) =
    (Zeta23.zeroMult ρ : ℂ) *
      conj (smoothWeilTransform f c (1 - conj (ρ : ℂ))) *
        smoothWeilTransform f c (ρ : ℂ) := by
  classical
  unfold smoothWeilTransform
  calc
    _ = ∑ i, ((Zeta23.zeroMult ρ : ℂ) *
        conj (c i * centeredTransform (f i) (1 - conj (ρ : ℂ)))) *
          (∑ j, c j * centeredTransform (f j) (ρ : ℂ)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_mul]
      ring
    _ = (∑ i, (Zeta23.zeroMult ρ : ℂ) *
        conj (c i * centeredTransform (f i) (1 - conj (ρ : ℂ)))) *
          (∑ j, c j * centeredTransform (f j) (ρ : ℂ)) := by
      rw [Finset.sum_mul]
    _ = _ := by rw [← Finset.mul_sum, ← map_sum]

/-- Finite summation and the actual absolutely summable scalar zero series commute. -/
theorem smoothWeilMatrix_spectral_data {f : ι → ℝ → ℂ}
    (hf : ∀ i, SmoothSuperexponentialDecay (f i)) (c : ι → ℂ) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier =>
      (Zeta23.zeroMult ρ : ℂ) *
        conj (smoothWeilTransform f c (1 - conj (ρ : ℂ))) *
          smoothWeilTransform f c (ρ : ℂ)) ∧
    smoothWeilMatrixQuadratic f c =
      ∑' ρ : Zeta23.zetaZeroConfig.carrier,
        (Zeta23.zeroMult ρ : ℂ) *
          conj (smoothWeilTransform f c (1 - conj (ρ : ℂ))) *
            smoothWeilTransform f c (ρ : ℂ) := by
  classical
  let a : ι → ι → Zeta23.zetaZeroConfig.carrier → ℂ := fun i j ρ =>
    conj (c i) *
      ((Zeta23.zeroMult ρ : ℂ) * conj (centeredTransform (f i) (1 - conj (ρ : ℂ))) *
        centeredTransform (f j) (ρ : ℂ)) * c j
  have ha (i j : ι) : Summable (a i j) :=
    (((summable_norm_arithmeticWeilPairing_zero_terms (hf i) (hf j)).of_norm).mul_left
      (conj (c i))).mul_right (c j)
  have hrow (i : ι) := finite_sum_tsum Finset.univ (a i) (fun j _ => ha i j)
  have hall := finite_sum_tsum Finset.univ (fun i ρ => ∑ j, a i j ρ)
    (fun i _ => (hrow i).1)
  constructor
  · exact hall.1.congr (finite_zero_factor f c)
  · calc
      smoothWeilMatrixQuadratic f c = ∑ i, ∑ j, ∑' ρ, a i j ρ := by
        unfold smoothWeilMatrixQuadratic smoothWeilMatrix
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [arithmeticWeilPairing_eq_zero_sum (hf i) (hf j)]
        simp only [a, tsum_mul_right, tsum_mul_left]
      _ = ∑ i, ∑' ρ, ∑ j, a i j ρ := by
        apply Finset.sum_congr rfl
        intro i _
        exact (hrow i).2
      _ = ∑' ρ, ∑ i, ∑ j, a i j ρ := hall.2
      _ = _ := tsum_congr (finite_zero_factor f c)

theorem smoothWeilMatrix_quadratic_zero_sum {f : ι → ℝ → ℂ}
    (hf : ∀ i, SmoothSuperexponentialDecay (f i)) (c : ι → ℂ) :
    smoothWeilMatrixQuadratic f c =
      ∑' ρ : Zeta23.zetaZeroConfig.carrier,
        (Zeta23.zeroMult ρ : ℂ) *
          conj (smoothWeilTransform f c (1 - conj (ρ : ℂ))) *
            smoothWeilTransform f c (ρ : ℂ) :=
  (smoothWeilMatrix_spectral_data hf c).2

private theorem actual_zero_reflection_fixed_of_RH (hRH : RiemannHypothesis)
    (ρ : Zeta23.zetaZeroConfig.carrier) : 1 - conj (ρ : ℂ) = (ρ : ℂ) := by
  have hline : (ρ : ℂ).re = 1 / 2 :=
    (riemannHypothesis_iff_strip_zeros_on_line.mp hRH) ρ
      ρ.property.1 ρ.property.2.1 ρ.property.2.2
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  · simp

private theorem weighted_normSq (m : ℕ) (z : ℂ) :
    (m : ℂ) * conj z * z = ((m : ℝ) * Complex.normSq z : ℝ) := by
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.natCast_re,
      Complex.natCast_im, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply] <;> ring

/-- Under explicit RH the entire quadratic form is an actual nonnegative zero sum. -/
theorem smoothWeilMatrix_quadratic_eq_norm_sum_of_RH (hRH : RiemannHypothesis)
    {f : ι → ℝ → ℂ} (hf : ∀ i, SmoothSuperexponentialDecay (f i)) (c : ι → ℂ) :
    smoothWeilMatrixQuadratic f c =
      ∑' ρ : Zeta23.zetaZeroConfig.carrier,
        (((Zeta23.zeroMult ρ : ℝ) *
          Complex.normSq (smoothWeilTransform f c (ρ : ℂ)) : ℝ) : ℂ) := by
  rw [smoothWeilMatrix_quadratic_zero_sum hf c]
  apply tsum_congr
  intro ρ
  rw [actual_zero_reflection_fixed_of_RH hRH ρ]
  exact weighted_normSq _ _

theorem smoothWeilMatrix_quadratic_nonneg_of_RH (hRH : RiemannHypothesis)
    {f : ι → ℝ → ℂ} (hf : ∀ i, SmoothSuperexponentialDecay (f i)) (c : ι → ℂ) :
    0 ≤ (smoothWeilMatrixQuadratic f c).re := by
  obtain ⟨hs, heq⟩ := smoothWeilMatrix_spectral_data hf c
  rw [heq]
  change 0 ≤ Complex.reCLM _
  rw [Complex.reCLM.map_tsum hs]
  apply tsum_nonneg
  intro ρ
  rw [actual_zero_reflection_fixed_of_RH hRH ρ, weighted_normSq]
  change 0 ≤ (Zeta23.zeroMult ρ : ℝ) *
    Complex.normSq (smoothWeilTransform f c (ρ : ℂ))
  exact mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)

/-- Any smooth family whose transforms vanish on all actual zeros is a null matrix. -/
theorem smoothWeilMatrix_eq_zero_of_zero_transform {f : ι → ℝ → ℂ}
    (hf : ∀ i, SmoothSuperexponentialDecay (f i))
    (hz : ∀ i (ρ : Zeta23.zetaZeroConfig.carrier), centeredTransform (f i) (ρ : ℂ) = 0) :
    smoothWeilMatrix f = 0 := by
  ext i j
  change arithmeticWeilPairing (f i) (f j) = 0
  rw [arithmeticWeilPairing_eq_zero_sum (hf i) (hf j)]
  simp only [hz, mul_zero, tsum_zero]

/-- The actual completed Nyman tests yield an identically zero Weil matrix, without RH. -/
theorem smoothWeilMatrix_completed_nyman_eq_zero
    (n M : ι → ℕ) (hn : ∀ i, 2 ≤ n i) (v : ι → ℝ → ℂ) (a b : ι → ℝ)
    (hv : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (v i))
    (ha : ∀ i x, x < a i → v i x = 0) (hb : ∀ i x, b i < x → v i x = 0) :
    smoothWeilMatrix (fun i => nymanCompletedTest (n i) (M i) (hn i) (v i)) = 0 := by
  apply smoothWeilMatrix_eq_zero_of_zero_transform
  · intro i
    exact smoothSuperexponentialDecay_nymanCompletedTest (n i) (M i) (hn i)
      (hv i) (ha i) (hb i)
  · intro i ρ
    have hne : (ρ : ℂ) ≠ 1 := by
      intro h
      have ht := ρ.property.2.2
      rw [h] at ht
      norm_num at ht
    exact centeredTransform_nymanCompletedTest_zero (n i) (M i) (hn i)
      (hv i) (ha i) (hb i) hne ρ.property.1

/-- A nonempty null family has a nonzero coefficient vector with zero quadratic value. -/
theorem smoothWeilMatrix_not_strictly_positive_of_eq_zero [Nonempty ι]
    {f : ι → ℝ → ℂ} (hzero : smoothWeilMatrix f = 0) :
    ¬ (∀ c : ι → ℂ, c ≠ 0 → 0 < (smoothWeilMatrixQuadratic f c).re) := by
  intro hpos
  have hc : (fun _ : ι => (1 : ℂ)) ≠ 0 := by
    intro h
    have := congrFun h (Classical.arbitrary ι)
    norm_num at this
  have hp := hpos (fun _ => 1) hc
  simp [smoothWeilMatrixQuadratic, hzero] at hp

end

end RiemannResearch.RH.SignedWeilCorrelation
