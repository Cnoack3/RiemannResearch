import RiemannResearch.Analysis.FrequencySensitiveGramBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Exact frequency dispersion of a finite convolution

Finite signed convolution coefficients are bounded after equal products have
been grouped. The grouping preserves all three weighted frequency moments.
The variance of a product dictionary is additive, retaining the subtracted
square and improving the centered product bound from a factor 6 to a factor 4.

These are finite algebraic statements. Analytic remainder bounds for actual
zero ordinates remain explicit inputs to the existing Fourier Gram theorem.
-/

open scoped BigOperators

namespace RiemannResearch.Fourier

variable {ι κ κ₂ : Type*}

/-- Total mass of a product dictionary, without sign restrictions. -/
theorem finiteProductWeight_mass (s : Finset ι) (t : Finset κ)
    (w : ι → ℝ) (v : κ → ℝ) :
    (∑ p ∈ s.product t, w p.1 * v p.2) =
      (∑ i ∈ s, w i) * (∑ j ∈ t, v j) := by
  calc
    _ = ∑ i ∈ s, ∑ j ∈ t, w i * v j :=
      Finset.sum_product' s t (fun i j => w i * v j)
    _ = _ := (Finset.sum_mul_sum s t w v).symm

/-- First additive-frequency moment of a product dictionary. -/
theorem finiteProductWeight_firstMoment (s : Finset ι) (t : Finset κ)
    (w u : ι → ℝ) (v z : κ → ℝ) :
    (∑ p ∈ s.product t, (w p.1 * v p.2) * (u p.1 + z p.2)) =
      (∑ i ∈ s, w i * u i) * (∑ j ∈ t, v j) +
        (∑ i ∈ s, w i) * (∑ j ∈ t, v j * z j) := by
  calc
    _ = ∑ i ∈ s, ∑ j ∈ t, (w i * v j) * (u i + z j) :=
      Finset.sum_product' s t (fun i j => (w i * v j) * (u i + z j))
    _ = ∑ i ∈ s, ∑ j ∈ t,
        ((w i * u i) * v j + w i * (v j * z j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]
      rw [← Finset.sum_mul_sum, ← Finset.sum_mul_sum]

/-- Second additive-frequency moment of a product dictionary. -/
theorem finiteProductWeight_secondMoment (s : Finset ι) (t : Finset κ)
    (w u : ι → ℝ) (v z : κ → ℝ) :
    (∑ p ∈ s.product t, (w p.1 * v p.2) * (u p.1 + z p.2) ^ 2) =
      (∑ i ∈ s, w i * u i ^ 2) * (∑ j ∈ t, v j) +
        (∑ i ∈ s, w i) * (∑ j ∈ t, v j * z j ^ 2) +
        2 * (∑ i ∈ s, w i * u i) * (∑ j ∈ t, v j * z j) := by
  calc
    _ = ∑ i ∈ s, ∑ j ∈ t, (w i * v j) * (u i + z j) ^ 2 :=
      Finset.sum_product' s t (fun i j => (w i * v j) * (u i + z j) ^ 2)
    _ = ∑ i ∈ s, ∑ j ∈ t,
        ((w i * u i ^ 2) * v j + w i * (v j * z j ^ 2) +
          (2 * (w i * u i)) * (v j * z j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]
      rw [← Finset.sum_mul_sum, ← Finset.sum_mul_sum, ← Finset.sum_mul_sum]
      rw [← Finset.mul_sum]

/-- Exact variance additivity, including both negative squares.
The real weights may be signed. -/
theorem weightedFrequencySpread_product (s : Finset ι) (t : Finset κ)
    (w u : ι → ℝ) (v z : κ → ℝ) :
    weightedFrequencySpread (s.product t) (fun p => w p.1 * v p.2)
        (fun p => u p.1 + z p.2) =
      (∑ j ∈ t, v j) ^ 2 * weightedFrequencySpread s w u +
        (∑ i ∈ s, w i) ^ 2 * weightedFrequencySpread t v z := by
  simp only [weightedFrequencySpread_eq]
  rw [finiteProductWeight_mass, finiteProductWeight_secondMoment,
    finiteProductWeight_firstMoment]
  ring

/-- Squaring a dictionary doubles its variance and squares its mass. -/
theorem weightedFrequencySpread_square (s : Finset ι) (w u : ι → ℝ) :
    weightedFrequencySpread (s.product s) (fun p => w p.1 * w p.2)
        (fun p => u p.1 + u p.2) =
      2 * (∑ i ∈ s, w i) ^ 2 * weightedFrequencySpread s w u := by
  rw [weightedFrequencySpread_product]
  ring

/-- Exact square-dictionary dispersion in terms of the original moments. -/
theorem weightedFrequencySpread_square_moments (s : Finset ι) (w u : ι → ℝ) :
    weightedFrequencySpread (s.product s) (fun p => w p.1 * w p.2)
        (fun p => u p.1 + u p.2) =
      4 * (∑ i ∈ s, w i) ^ 3 * (∑ i ∈ s, w i * u i ^ 2) -
        4 * (∑ i ∈ s, w i) ^ 2 * (∑ i ∈ s, w i * u i) ^ 2 := by
  rw [weightedFrequencySpread_square, weightedFrequencySpread_eq]
  ring

/-- The exact product identity gives the sharper centered upper bound. -/
theorem weightedFrequencySpread_square_le_centered
    (s : Finset ι) (w u : ι → ℝ) (c : ℝ) :
    weightedFrequencySpread (s.product s) (fun p => w p.1 * w p.2)
        (fun p => u p.1 + u p.2) ≤
      4 * (∑ i ∈ s, w i) ^ 3 * (∑ i ∈ s, w i * (u i - c) ^ 2) := by
  rw [weightedFrequencySpread_square]
  calc
    _ ≤ 2 * (∑ i ∈ s, w i) ^ 2 *
        (2 * (∑ i ∈ s, w i) * (∑ i ∈ s, w i * (u i - c) ^ 2)) := by
      exact mul_le_mul_of_nonneg_left
        (weightedFrequencySpread_le_centered s w u c)
        (mul_nonneg (by norm_num) (sq_nonneg _))
    _ = _ := by ring

/-- Nonnegative pointwise domination preserves pairwise dispersion. -/
theorem weightedFrequencySpread_mono (s : Finset ι) (w v u : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hdom : ∀ i ∈ s, w i ≤ v i) :
    weightedFrequencySpread s w u ≤ weightedFrequencySpread s v u := by
  unfold weightedFrequencySpread
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  calc
    w i * w j ≤ v i * w j :=
      mul_le_mul_of_nonneg_right (hdom i hi) (hw j hj)
    _ ≤ v i * v j :=
      mul_le_mul_of_nonneg_left (hdom j hj) ((hw i hi).trans (hdom i hi))

/-- Only the frequencies on the finite support matter. -/
theorem weightedFrequencySpread_congr_frequency (s : Finset ι) (w u v : ι → ℝ)
    (h : ∀ i ∈ s, u i = v i) :
    weightedFrequencySpread s w u = weightedFrequencySpread s w v := by
  unfold weightedFrequencySpread
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [h i hi, h j hj]

section Fibers

variable [DecidableEq κ]

/-- Weight after grouping all source indices with the same image. -/
def finiteFiberWeight (s : Finset ι) (f : ι → κ) (w : ι → ℝ) (j : κ) : ℝ :=
  ∑ i ∈ s.filter (fun i => f i = j), w i

/-- Signed complex coefficient obtained by grouping a finite family. -/
def finiteFiberCoefficient (s : Finset ι) (f : ι → κ) (a : ι → ℂ) (j : κ) : ℂ :=
  ∑ i ∈ s.filter (fun i => f i = j), a i

/-- The coefficient domination used below follows from the triangle inequality. -/
theorem finiteFiberCoefficient_norm_le (s : Finset ι) (f : ι → κ)
    (a : ι → ℂ) (w : ι → ℝ) (ha : ∀ i ∈ s, ‖a i‖ ≤ w i) (j : κ) :
    ‖finiteFiberCoefficient s f a j‖ ≤ finiteFiberWeight s f w j := by
  unfold finiteFiberCoefficient finiteFiberWeight
  calc
    _ ≤ ∑ i ∈ s.filter (fun i => f i = j), ‖a i‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum (fun i hi => ha i (Finset.mem_filter.mp hi).1)

/-- Finite fiber grouping preserves mass. -/
theorem finiteFiberWeight_mass (s : Finset ι) (t : Finset κ)
    (f : ι → κ) (w : ι → ℝ) (hmap : ∀ i ∈ s, f i ∈ t) :
    (∑ j ∈ t, finiteFiberWeight s f w j) = ∑ i ∈ s, w i := by
  exact Finset.sum_fiberwise_of_maps_to hmap w

/-- Finite fiber grouping preserves every linear weighted moment. -/
theorem finiteFiberWeight_moment (s : Finset ι) (t : Finset κ)
    (f : ι → κ) (w : ι → ℝ) (v : κ → ℝ) (hmap : ∀ i ∈ s, f i ∈ t) :
    (∑ j ∈ t, finiteFiberWeight s f w j * v j) =
      ∑ i ∈ s, w i * v (f i) := by
  unfold finiteFiberWeight
  calc
    _ = ∑ j ∈ t, ∑ i ∈ s.filter (fun i => f i = j), w i * v j := by
      simp_rw [Finset.sum_mul]
    _ = ∑ j ∈ t, ∑ i ∈ s.filter (fun i => f i = j), w i * v (f i) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to hmap (fun i => w i * v (f i))

/-- Finite fiber grouping preserves the exact quadratic dispersion. -/
theorem finiteFiberWeight_spread (s : Finset ι) (t : Finset κ)
    (f : ι → κ) (w : ι → ℝ) (v : κ → ℝ) (hmap : ∀ i ∈ s, f i ∈ t) :
    weightedFrequencySpread t (finiteFiberWeight s f w) v =
      weightedFrequencySpread s w (fun i => v (f i)) := by
  simp only [weightedFrequencySpread_eq]
  rw [finiteFiberWeight_mass s t f w hmap,
    finiteFiberWeight_moment s t f w (fun j => v j ^ 2) hmap,
    finiteFiberWeight_moment s t f w v hmap]

/-- A signed coefficient after grouping is controlled by its absolute
factorization weights, with no injectivity assumption on the grouping map. -/
theorem finiteFiberWeight_norm_mass_le (s : Finset ι) (t : Finset κ)
    (f : ι → κ) (w : ι → ℝ) (a : κ → ℂ)
    (hmap : ∀ i ∈ s, f i ∈ t)
    (ha : ∀ j ∈ t, ‖a j‖ ≤ finiteFiberWeight s f w j) :
    (∑ j ∈ t, ‖a j‖) ≤ ∑ i ∈ s, w i := by
  calc
    _ ≤ ∑ j ∈ t, finiteFiberWeight s f w j := Finset.sum_le_sum ha
    _ = _ := finiteFiberWeight_mass s t f w hmap

/-- Absolute coefficient domination after grouping controls dispersion. -/
theorem finiteFiberWeight_norm_spread_le (s : Finset ι) (t : Finset κ)
    (f : ι → κ) (w : ι → ℝ) (a : κ → ℂ) (v : κ → ℝ)
    (hmap : ∀ i ∈ s, f i ∈ t)
    (ha : ∀ j ∈ t, ‖a j‖ ≤ finiteFiberWeight s f w j) :
    weightedFrequencySpread t (fun j => ‖a j‖) v ≤
      weightedFrequencySpread s w (fun i => v (f i)) := by
  calc
    _ ≤ weightedFrequencySpread t (finiteFiberWeight s f w) v :=
      weightedFrequencySpread_mono t (fun j => ‖a j‖)
        (finiteFiberWeight s f w) v (fun _ _ => norm_nonneg _) ha
    _ = _ := finiteFiberWeight_spread s t f w v hmap

end Fibers

/-- Exact signed product coefficients grouped by an arbitrary finite map. -/
def finiteProductCoefficient [DecidableEq κ₂]
    (s : Finset ι) (t : Finset κ) (f : ι × κ → κ₂)
    (a : ι → ℂ) (b : κ → ℂ) (k : κ₂) : ℂ :=
  finiteFiberCoefficient (s.product t) f (fun p => a p.1 * b p.2) k

/-- Signed finite products satisfy their factorization-weight domination. -/
theorem finiteProductCoefficient_norm_le [DecidableEq κ₂]
    (s : Finset ι) (t : Finset κ) (f : ι × κ → κ₂)
    (a : ι → ℂ) (b : κ → ℂ) (w : ι → ℝ) (v : κ → ℝ)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ w i) (hb : ∀ j ∈ t, ‖b j‖ ≤ v j) (k : κ₂) :
    ‖finiteProductCoefficient s t f a b k‖ ≤
      finiteFiberWeight (s.product t) f (fun p => w p.1 * v p.2) k := by
  apply finiteFiberCoefficient_norm_le
  intro p hp
  have hp' := Finset.mem_product.mp hp
  rw [norm_mul]
  exact mul_le_mul (ha p.1 hp'.1) (hb p.2 hp'.2)
    (norm_nonneg _) ((norm_nonneg _).trans (ha p.1 hp'.1))

/-- The absolute coefficient sum of a signed finite product is at most the
product of its original absolute coefficient sums. -/
theorem finiteProductCoefficient_norm_mass_le [DecidableEq κ₂]
    (s : Finset ι) (t : Finset κ) (r : Finset κ₂) (f : ι × κ → κ₂)
    (a : ι → ℂ) (b : κ → ℂ) (w : ι → ℝ) (v : κ → ℝ)
    (hmap : ∀ p ∈ s.product t, f p ∈ r)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ w i) (hb : ∀ j ∈ t, ‖b j‖ ≤ v j) :
    (∑ k ∈ r, ‖finiteProductCoefficient s t f a b k‖) ≤
      (∑ i ∈ s, w i) * (∑ j ∈ t, v j) := by
  calc
    _ ≤ ∑ p ∈ s.product t, w p.1 * v p.2 :=
      finiteFiberWeight_norm_mass_le (s.product t) r f
        (fun p => w p.1 * v p.2) (finiteProductCoefficient s t f a b) hmap
        (fun k _ => finiteProductCoefficient_norm_le s t f a b w v ha hb k)
    _ = _ := finiteProductWeight_mass s t w v

/-- A signed finite product has at most the additive product dispersion.
This is a proved coefficient estimate, with no additional domination provider. -/
theorem finiteProductCoefficient_norm_spread_le [DecidableEq κ₂]
    (s : Finset ι) (t : Finset κ) (r : Finset κ₂) (f : ι × κ → κ₂)
    (a : ι → ℂ) (b : κ → ℂ) (w u : ι → ℝ) (v z : κ → ℝ) (q : κ₂ → ℝ)
    (hmap : ∀ p ∈ s.product t, f p ∈ r)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ w i) (hb : ∀ j ∈ t, ‖b j‖ ≤ v j)
    (hfreq : ∀ p ∈ s.product t, q (f p) = u p.1 + z p.2) :
    weightedFrequencySpread r (fun k => ‖finiteProductCoefficient s t f a b k‖) q ≤
      (∑ j ∈ t, v j) ^ 2 * weightedFrequencySpread s w u +
        (∑ i ∈ s, w i) ^ 2 * weightedFrequencySpread t v z := by
  calc
    _ ≤ weightedFrequencySpread (s.product t) (fun p => w p.1 * v p.2)
        (fun p => q (f p)) :=
      finiteFiberWeight_norm_spread_le (s.product t) r f
        (fun p => w p.1 * v p.2) (finiteProductCoefficient s t f a b) q hmap
        (fun k _ => finiteProductCoefficient_norm_le s t f a b w v ha hb k)
    _ = weightedFrequencySpread (s.product t) (fun p => w p.1 * v p.2)
        (fun p => u p.1 + z p.2) :=
      weightedFrequencySpread_congr_frequency (s.product t)
        (fun p => w p.1 * v p.2) (fun p => q (f p))
        (fun p => u p.1 + z p.2) hfreq
    _ = _ := weightedFrequencySpread_product s t w u v z

/-- Convolution dispersion is bounded by the exact product variance.
The coefficient inequality is the elementary triangle inequality on fibers;
the frequency identity is logarithm additivity for ordinary Dirichlet products. -/
theorem finiteConvolution_norm_spread_le [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (f : ι × ι → κ)
    (w u : ι → ℝ) (a : κ → ℂ) (v : κ → ℝ)
    (hmap : ∀ p ∈ s.product s, f p ∈ t)
    (ha : ∀ j ∈ t, ‖a j‖ ≤
      finiteFiberWeight (s.product s) f (fun p => w p.1 * w p.2) j)
    (hfreq : ∀ p ∈ s.product s, v (f p) = u p.1 + u p.2) :
    weightedFrequencySpread t (fun j => ‖a j‖) v ≤
      2 * (∑ i ∈ s, w i) ^ 2 * weightedFrequencySpread s w u := by
  calc
    _ ≤ weightedFrequencySpread (s.product s) (fun p => w p.1 * w p.2)
        (fun p => v (f p)) :=
      finiteFiberWeight_norm_spread_le (s.product s) t f
        (fun p => w p.1 * w p.2) a v hmap ha
    _ = weightedFrequencySpread (s.product s) (fun p => w p.1 * w p.2)
        (fun p => u p.1 + u p.2) :=
      weightedFrequencySpread_congr_frequency (s.product s)
        (fun p => w p.1 * w p.2) (fun p => v (f p))
        (fun p => u p.1 + u p.2) hfreq
    _ = _ := weightedFrequencySpread_square s w u

/-- Centering gives a factor 4, without using an independent first-moment bound. -/
theorem finiteConvolution_norm_spread_le_centered [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (f : ι × ι → κ)
    (w u : ι → ℝ) (a : κ → ℂ) (v : κ → ℝ) (c : ℝ)
    (hmap : ∀ p ∈ s.product s, f p ∈ t)
    (ha : ∀ j ∈ t, ‖a j‖ ≤
      finiteFiberWeight (s.product s) f (fun p => w p.1 * w p.2) j)
    (hfreq : ∀ p ∈ s.product s, v (f p) = u p.1 + u p.2) :
    weightedFrequencySpread t (fun j => ‖a j‖) v ≤
      4 * (∑ i ∈ s, w i) ^ 3 * (∑ i ∈ s, w i * (u i - c) ^ 2) := by
  calc
    _ ≤ 2 * (∑ i ∈ s, w i) ^ 2 * weightedFrequencySpread s w u :=
      finiteConvolution_norm_spread_le s t f w u a v hmap ha hfreq
    _ ≤ _ := by
      rw [← weightedFrequencySpread_square s w u]
      exact weightedFrequencySpread_square_le_centered s w u c

/-- The entrywise analytic remainder for a signed finite convolution inherits
the exact additive product variance and fourth-power mass budget. -/
theorem finiteConvolutionGramError_bound [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (f : ι × ι → κ)
    (w u : ι → ℝ) (a : κ → ℂ) (v : κ → ℝ) (R : κ → κ → ℂ) (η ν : ℝ)
    (hη : 0 ≤ η) (hν : 0 ≤ ν)
    (hmap : ∀ p ∈ s.product s, f p ∈ t)
    (ha : ∀ j ∈ t, ‖a j‖ ≤
      finiteFiberWeight (s.product s) f (fun p => w p.1 * w p.2) j)
    (hfreq : ∀ p ∈ s.product s, v (f p) = u p.1 + u p.2)
    (hR : ∀ i ∈ t, ∀ j ∈ t, ‖R i j‖ ≤ η + ν * (v i - v j) ^ 2) :
    ‖finiteGramErrorPairing t a R‖ ≤
      η * (∑ i ∈ s, w i) ^ 4 +
        2 * ν * (∑ i ∈ s, w i) ^ 2 * weightedFrequencySpread s w u := by
  have hmass : (∑ j ∈ t, ‖a j‖) ≤ (∑ i ∈ s, w i) ^ 2 := by
    calc
      _ ≤ ∑ p ∈ s.product s, w p.1 * w p.2 :=
        finiteFiberWeight_norm_mass_le (s.product s) t f
          (fun p => w p.1 * w p.2) a hmap ha
      _ = _ := by rw [finiteProductWeight_mass, pow_two]
  have hmass2 : (∑ j ∈ t, ‖a j‖) ^ 2 ≤ ((∑ i ∈ s, w i) ^ 2) ^ 2 :=
    pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hmass 2
  have hspread := finiteConvolution_norm_spread_le s t f w u a v hmap ha hfreq
  calc
    _ ≤ η * (∑ j ∈ t, ‖a j‖) ^ 2 +
        ν * weightedFrequencySpread t (fun j => ‖a j‖) v :=
      finiteGramErrorPairing_norm_le_frequencySpread t a R v η ν hR
    _ ≤ η * ((∑ i ∈ s, w i) ^ 2) ^ 2 +
        ν * (2 * (∑ i ∈ s, w i) ^ 2 * weightedFrequencySpread s w u) :=
      add_le_add (mul_le_mul_of_nonneg_left hmass2 hη)
        (mul_le_mul_of_nonneg_left hspread hν)
    _ = _ := by ring

/-- The preceding analytic budget retains the full negative first-moment square. -/
theorem finiteConvolutionGramError_variance_bound [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (f : ι × ι → κ)
    (w u : ι → ℝ) (a : κ → ℂ) (v : κ → ℝ) (R : κ → κ → ℂ) (η ν : ℝ)
    (hη : 0 ≤ η) (hν : 0 ≤ ν)
    (hmap : ∀ p ∈ s.product s, f p ∈ t)
    (ha : ∀ j ∈ t, ‖a j‖ ≤
      finiteFiberWeight (s.product s) f (fun p => w p.1 * w p.2) j)
    (hfreq : ∀ p ∈ s.product s, v (f p) = u p.1 + u p.2)
    (hR : ∀ i ∈ t, ∀ j ∈ t, ‖R i j‖ ≤ η + ν * (v i - v j) ^ 2) :
    ‖finiteGramErrorPairing t a R‖ ≤ η * (∑ i ∈ s, w i) ^ 4 +
      ν * (4 * (∑ i ∈ s, w i) ^ 3 * (∑ i ∈ s, w i * u i ^ 2) -
        4 * (∑ i ∈ s, w i) ^ 2 * (∑ i ∈ s, w i * u i) ^ 2) := by
  have h := finiteConvolutionGramError_bound s t f w u a v R η ν
    hη hν hmap ha hfreq hR
  rw [weightedFrequencySpread_eq] at h
  convert h using 1
  ring

end RiemannResearch.Fourier
