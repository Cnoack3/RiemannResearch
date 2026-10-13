import Mathlib.Tactic.Positivity
import RiemannResearch.RH.PrimeValuationIndependence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Prime-power orthogonal coordinates for the actual zeta(2) measure

Source: user-provided inverse-Gram research argument. The prime-power
coordinate at exponent `a+1` is the difference of two scaled valuation tails.
Unlike squarefree divisibility alone, these coordinates retain all prime
exponents. Finite tensor orthogonality is proved for the actual measure `Q`.
Completeness of the infinite family and any RH approximation estimate are
not asserted in this module.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RiemannResearch.RH.ZetaTwoProbability

def valuationIndicator (p a : ℕ) (k : ℕ+) : ℝ :=
  if a ≤ primeValuation p k then 1 else 0

def scaledValuationTail (p a : ℕ) (k : ℕ+) : ℝ :=
  ((p : ℝ) ^ a) ^ 2 * valuationIndicator p a k

theorem valuationIndicator_mul (p a b : ℕ) (k : ℕ+) :
    valuationIndicator p a k * valuationIndicator p b k =
      valuationIndicator p (max a b) k := by
  by_cases ha : a ≤ primeValuation p k <;>
    by_cases hb : b ≤ primeValuation p k <;>
    simp [valuationIndicator, max_le_iff, ha, hb]

theorem integrable_valuationIndicator (p a : ℕ) :
    Integrable (valuationIndicator p a) Q := by
  have hpoint : valuationIndicator p a =
      {k : ℕ+ | a ≤ primeValuation p k}.indicator (fun _ => (1 : ℝ)) := by
    funext k
    simp [valuationIndicator, Set.indicator]
  rw [hpoint]
  exact (integrable_const (μ := Q) (1 : ℝ)).indicator
    ((Set.to_countable {k : ℕ+ | a ≤ primeValuation p k}).measurableSet)

theorem integral_valuationIndicator (p a : ℕ) (hp : p.Prime) :
    (∫ k : ℕ+, valuationIndicator p a k ∂Q) = 1 / ((p : ℝ) ^ a) ^ 2 := by
  have hpoint : valuationIndicator p a =
      {k : ℕ+ | a ≤ primeValuation p k}.indicator (fun _ => (1 : ℝ)) := by
    funext k
    simp [valuationIndicator, Set.indicator]
  rw [hpoint, integral_indicator_const 1
    ((Set.to_countable {k : ℕ+ | a ≤ primeValuation p k}).measurableSet),
    measureReal_def, measure_primeValuation_ge p a hp,
    ENNReal.toReal_ofReal (by positivity)]
  simp

theorem integrable_scaledValuationTail (p a : ℕ) :
    Integrable (scaledValuationTail p a) Q :=
  (integrable_valuationIndicator p a).const_mul _

theorem integral_scaledValuationTail (p a : ℕ) (hp : p.Prime) :
    (∫ k : ℕ+, scaledValuationTail p a k ∂Q) = 1 := by
  change (∫ k : ℕ+, ((p : ℝ) ^ a) ^ 2 * valuationIndicator p a k ∂Q) = 1
  rw [integral_const_mul, integral_valuationIndicator p a hp]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp [hp0]

theorem scaledValuationTail_mul (p a b : ℕ) (k : ℕ+) :
    scaledValuationTail p a k * scaledValuationTail p b k =
      (((p : ℝ) ^ a) ^ 2 * ((p : ℝ) ^ b) ^ 2) *
        valuationIndicator p (max a b) k := by
  unfold scaledValuationTail
  rw [← valuationIndicator_mul]
  ring

theorem integrable_scaledValuationTail_mul (p a b : ℕ) :
    Integrable (fun k => scaledValuationTail p a k * scaledValuationTail p b k) Q := by
  simp_rw [scaledValuationTail_mul]
  exact (integrable_valuationIndicator p (max a b)).const_mul _

/-- The nested-tail Gram kernel is an exact minimum-exponent kernel. -/
theorem integral_scaledValuationTail_mul (p a b : ℕ) (hp : p.Prime) :
    (∫ k : ℕ+, scaledValuationTail p a k * scaledValuationTail p b k ∂Q) =
      ((p : ℝ) ^ (min a b)) ^ 2 := by
  simp_rw [scaledValuationTail_mul]
  rw [integral_const_mul, integral_valuationIndicator p (max a b) hp]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rcases le_total a b with h | h
  · rw [max_eq_right h, min_eq_left h]
    field_simp [hp0] <;> ring
  · rw [max_eq_left h, min_eq_right h]
    field_simp [hp0] <;> ring

/-- The local polynomial in the actual valuation; exponent zero is constant. -/
def geometricWavelet (p : ℕ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | a + 1, v => ((p : ℝ) ^ (a + 1)) ^ 2 * (if a + 1 ≤ v then 1 else 0) -
      ((p : ℝ) ^ a) ^ 2 * (if a ≤ v then 1 else 0)

def valuationWavelet (p a : ℕ) (k : ℕ+) : ℝ :=
  geometricWavelet p a (primeValuation p k)

def valuationWaveletWeight (p : ℕ) : ℕ → ℝ
  | 0 => 1
  | a + 1 => ((p : ℝ) ^ (a + 1)) ^ 2 - ((p : ℝ) ^ a) ^ 2

@[simp] theorem valuationWavelet_zero (p : ℕ) (k : ℕ+) :
    valuationWavelet p 0 k = 1 := rfl

theorem valuationWavelet_succ (p a : ℕ) (k : ℕ+) :
    valuationWavelet p (a + 1) k =
      scaledValuationTail p (a + 1) k - scaledValuationTail p a k := rfl

/-- Every scaled divisibility tail is an exact finite sum of wavelets. -/
theorem sum_valuationWavelet (p a : ℕ) (k : ℕ+) :
    (∑ j ∈ Finset.range (a + 1), valuationWavelet p j k) =
      scaledValuationTail p a k := by
  induction a with
  | zero => simp [scaledValuationTail, valuationIndicator]
  | succ a ih =>
    rw [Finset.sum_range_succ, ih, valuationWavelet_succ]
    ring

/-- Exact finite inversion recovers each prime-power divisibility indicator. -/
theorem valuationIndicator_eq_wavelet_sum (p a : ℕ) (hp : p.Prime) (k : ℕ+) :
    valuationIndicator p a k =
      (1 / ((p : ℝ) ^ a) ^ 2) *
        (∑ j ∈ Finset.range (a + 1), valuationWavelet p j k) := by
  rw [sum_valuationWavelet, scaledValuationTail]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp [hp0]

theorem valuationWaveletWeight_succ (p a : ℕ) :
    valuationWaveletWeight p (a + 1) =
      ((p : ℝ) ^ a) ^ 2 * ((p : ℝ) ^ 2 - 1) := by
  simp only [valuationWaveletWeight, pow_succ]
  ring

theorem integrable_valuationWavelet (p a : ℕ) :
    Integrable (valuationWavelet p a) Q := by
  cases a with
  | zero =>
    change Integrable (fun _ : ℕ+ => (1 : ℝ)) Q
    exact integrable_const 1
  | succ a =>
    exact (integrable_scaledValuationTail p (a + 1)).sub
      (integrable_scaledValuationTail p a)

/-- Every nonconstant prime-power coordinate has exact mean zero. -/
theorem integral_valuationWavelet_succ (p a : ℕ) (hp : p.Prime) :
    (∫ k : ℕ+, valuationWavelet p (a + 1) k ∂Q) = 0 := by
  simp_rw [valuationWavelet_succ]
  rw [integral_sub (integrable_scaledValuationTail p (a + 1))
    (integrable_scaledValuationTail p a),
    integral_scaledValuationTail p (a + 1) hp,
    integral_scaledValuationTail p a hp, sub_self]

/-- The complete signed four-term identity is retained before orthogonality. -/
theorem integral_valuationWavelet_succ_mul (p a b : ℕ) (hp : p.Prime) :
    (∫ k : ℕ+, valuationWavelet p (a + 1) k * valuationWavelet p (b + 1) k ∂Q) =
      (((p : ℝ) ^ (min (a + 1) (b + 1))) ^ 2 -
        ((p : ℝ) ^ (min (a + 1) b)) ^ 2) -
      (((p : ℝ) ^ (min a (b + 1))) ^ 2 - ((p : ℝ) ^ (min a b)) ^ 2) := by
  have hpoint :
      (fun k => valuationWavelet p (a + 1) k * valuationWavelet p (b + 1) k) =
      (fun k =>
        (scaledValuationTail p (a + 1) k * scaledValuationTail p (b + 1) k -
          scaledValuationTail p (a + 1) k * scaledValuationTail p b k) -
        (scaledValuationTail p a k * scaledValuationTail p (b + 1) k -
          scaledValuationTail p a k * scaledValuationTail p b k)) := by
    funext k
    simp only [valuationWavelet_succ]
    ring
  rw [hpoint]
  have houter := integral_sub
    ((integrable_scaledValuationTail_mul p (a + 1) (b + 1)).sub
      (integrable_scaledValuationTail_mul p (a + 1) b))
    ((integrable_scaledValuationTail_mul p a (b + 1)).sub
      (integrable_scaledValuationTail_mul p a b))
  simp only [Pi.sub_apply] at houter
  rw [houter]
  rw [integral_sub (integrable_scaledValuationTail_mul p (a + 1) (b + 1))
    (integrable_scaledValuationTail_mul p (a + 1) b),
    integral_sub (integrable_scaledValuationTail_mul p a (b + 1))
      (integrable_scaledValuationTail_mul p a b)]
  rw [integral_scaledValuationTail_mul p (a + 1) (b + 1) hp,
    integral_scaledValuationTail_mul p (a + 1) b hp,
    integral_scaledValuationTail_mul p a (b + 1) hp,
    integral_scaledValuationTail_mul p a b hp]

/-- Orthogonality of every pair of exponents for one actual prime. -/
theorem integral_valuationWavelet_mul (p a b : ℕ) (hp : p.Prime) :
    (∫ k : ℕ+, valuationWavelet p a k * valuationWavelet p b k ∂Q) =
      if a = b then valuationWaveletWeight p a else 0 := by
  cases a with
  | zero =>
    cases b with
    | zero => simp [valuationWavelet_zero, valuationWaveletWeight]
    | succ b =>
      simpa [valuationWavelet_zero] using
        integral_valuationWavelet_succ p b hp
  | succ a =>
    cases b with
    | zero =>
      simpa [valuationWavelet_zero] using
        integral_valuationWavelet_succ p a hp
    | succ b =>
      rw [integral_valuationWavelet_succ_mul p a b hp]
      rcases lt_trichotomy a b with h | h | h
      · have h1 : a + 1 ≤ b := h
        have h2 : a ≤ b := Nat.le_of_lt h
        have h3 : a + 1 ≤ b + 1 := Nat.add_le_add_right h2 1
        have h4 : a ≤ b + 1 := h2.trans (Nat.le_succ b)
        have hne : a ≠ b := ne_of_lt h
        simp [min_eq_left h1, min_eq_left h2, min_eq_left h3, min_eq_left h4, hne]
      · subst b
        simp [valuationWaveletWeight]
      · have h1 : b + 1 ≤ a := h
        have h2 : b ≤ a := Nat.le_of_lt h
        have h3 : b + 1 ≤ a + 1 := Nat.add_le_add_right h2 1
        have h4 : b ≤ a + 1 := h2.trans (Nat.le_succ a)
        have hne : a ≠ b := ne_of_gt h
        simp [min_eq_right h1, min_eq_right h2, min_eq_right h3, min_eq_right h4, hne]

section FiniteTensor
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)

/-- A finite product of prime-power coordinates, including zero exponents. -/
def primePowerTensor (a : ι → ℕ) (k : ℕ+) : ℝ :=
  ∏ i, valuationWavelet (p i) (a i) k

include hp hinj

/-- Factorization is derived from the actual independence of prime valuations. -/
theorem integral_primePowerTensor_mul_factor (a b : ι → ℕ) :
    (∫ k : ℕ+, primePowerTensor p a k * primePowerTensor p b k ∂Q) =
      ∏ i, (if a i = b i then valuationWaveletWeight (p i) (a i) else 0) := by
  have hind : iIndepFun
      (fun i k => valuationWavelet (p i) (a i) k * valuationWavelet (p i) (b i) k) Q := by
    exact (iIndepFun_primeValuation p hp hinj).comp
      (fun i v => geometricWavelet (p i) (a i) v * geometricWavelet (p i) (b i) v)
      (fun _ => measurable_of_countable _)
  have hpoint :
      (fun k => primePowerTensor p a k * primePowerTensor p b k) =
      (fun k => ∏ i, valuationWavelet (p i) (a i) k * valuationWavelet (p i) (b i) k) := by
    funext k
    simp only [primePowerTensor, Finset.prod_mul_distrib]
  rw [hpoint, hind.integral_fun_prod_eq_prod_integral
    (fun _ => StronglyMeasurable.of_discrete.aestronglyMeasurable)]
  simp_rw [integral_valuationWavelet_mul _ _ _ (hp _)]

/-- Full finite exponent-family Gram identity under the actual measure `Q`. -/
theorem integral_primePowerTensor_mul (a b : ι → ℕ) :
    (∫ k : ℕ+, primePowerTensor p a k * primePowerTensor p b k ∂Q) =
      if a = b then ∏ i, valuationWaveletWeight (p i) (a i) else 0 := by
  classical
  rw [integral_primePowerTensor_mul_factor p hp hinj a b]
  by_cases hab : a = b
  · subst b
    simp
  · rw [if_neg hab]
    have hex : ∃ i, a i ≠ b i := by
      by_contra! h
      exact hab (funext h)
    obtain ⟨i, hi⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

end FiniteTensor
end RiemannResearch.RH.ZetaTwoProbability
