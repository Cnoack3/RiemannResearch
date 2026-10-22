import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Card
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Deterministic empirical reciprocal transfer

This module isolates the complete L² × L² → L¹ passage needed for growing
Dirichlet polynomials.  It has no random-law, RH, or zeta-approximation input.
The analytic inputs are two explicit iterated tail budgets and fixed-product
budgets; fixed products are NOT assumed to converge to one for each fixed J.
The normed ring can be a compact continuous-function algebra.
-/

open Filter

namespace RiemannResearch.Analysis.EmpiricalReciprocalTransfer

attribute [local instance] Classical.propDecidable

variable {ι E : Type*}

noncomputable def finiteMean (s : Finset ι) (f : ι → ℝ) : ℝ :=
  (∑ i ∈ s, f i) / (s.card : ℝ)

theorem finiteMean_nonneg (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ finiteMean s f := by
  exact div_nonneg (Finset.sum_nonneg hf) (Nat.cast_nonneg _)

theorem finiteMean_mono (s : Finset ι) (f g : ι → ℝ)
    (hfg : ∀ i ∈ s, f i ≤ g i) : finiteMean s f ≤ finiteMean s g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum hfg) (Nat.cast_nonneg _)

theorem finiteMean_add (s : Finset ι) (f g : ι → ℝ) :
    finiteMean s (fun i => f i + g i) = finiteMean s f + finiteMean s g := by
  simp [finiteMean, Finset.sum_add_distrib, add_div]

theorem finiteMean_smul (s : Finset ι) (c : ℝ) (f : ι → ℝ) :
    finiteMean s (fun i => c * f i) = c * finiteMean s f := by
  simp only [finiteMean, ← Finset.mul_sum]
  ring

theorem finiteMean_div (s : Finset ι) (c : ℝ) (f : ι → ℝ) :
    finiteMean s (fun i => f i / c) = finiteMean s f / c := by
  simp only [finiteMean, ← Finset.sum_div]
  ring

theorem density_le_mean_of_one_le (s : Finset ι) (P : ι → Prop) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hP : ∀ i ∈ s, P i → 1 ≤ f i) :
    ((s.filter P).card : ℝ) / (s.card : ℝ) ≤ finiteMean s f := by
  classical
  have hsum : ((s.filter P).card : ℝ) ≤ ∑ i ∈ s, f i := by
    calc
      ((s.filter P).card : ℝ) = ∑ i ∈ s.filter P, (1 : ℝ) := by simp
      _ ≤ ∑ i ∈ s.filter P, f i := by
        apply Finset.sum_le_sum
        intro i hi
        exact hP i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2
      _ ≤ ∑ i ∈ s, f i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i hi _ => hf i hi)
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)

/-- Normalization preserves the exact finite Cauchy–Schwarz inequality. -/
theorem finiteMean_mul_sq_le (s : Finset ι) (f g : ι → ℝ) :
    (finiteMean s (fun i => f i * g i)) ^ 2 ≤
      finiteMean s (fun i => f i ^ 2) * finiteMean s (fun i => g i ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s f g
  simpa [finiteMean, div_pow, div_mul_div_comm, pow_two] using
    (div_le_div_of_nonneg_right h (sq_nonneg (s.card : ℝ)))

theorem finiteMean_mul_le_sqrt (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) :
    finiteMean s (fun i => f i * g i) ≤
      Real.sqrt (finiteMean s (fun i => f i ^ 2)) *
        Real.sqrt (finiteMean s (fun i => g i ^ 2)) := by
  have hxy : 0 ≤ finiteMean s (fun i => f i * g i) :=
    finiteMean_nonneg _ _ (fun i hi => mul_nonneg (hf i hi) (hg i hi))
  have hf₂ : 0 ≤ finiteMean s (fun i => f i ^ 2) :=
    finiteMean_nonneg _ _ (fun _ _ => sq_nonneg _)
  have hg₂ : 0 ≤ finiteMean s (fun i => g i ^ 2) :=
    finiteMean_nonneg _ _ (fun _ _ => sq_nonneg _)
  rw [← Real.sqrt_mul hf₂]
  exact (Real.le_sqrt hxy (mul_nonneg hf₂ hg₂)).2 (finiteMean_mul_sq_le _ _ _)

/-- Parameterized Young inequality.  Its parameter can first make the moment
term small, after which the L² truncation tails are chosen small. -/
theorem young_parameter (x y q : ℝ) (hq : 0 < q) :
    x * y ≤ q * x ^ 2 + y ^ 2 / (4 * q) := by
  calc
    x * y ≤ (4 * q ^ 2 * x ^ 2 + y ^ 2) / (4 * q) := by
      apply (le_div_iff₀ (by positivity : 0 < 4 * q)).2
      nlinarith [sq_nonneg (2 * q * x - y)]
    _ = q * x ^ 2 + y ^ 2 / (4 * q) := by
      field_simp [ne_of_gt hq]

section Ring

variable [NormedRing E]

theorem product_error_decomposition (a b a₀ b₀ : E) :
    a * b - 1 = (a - a₀) * b + a₀ * (b - b₀) + (a₀ * b₀ - 1) := by
  noncomm_ring

theorem norm_product_error_le (a b a₀ b₀ : E) :
    ‖a * b - 1‖ ≤
      ‖a - a₀‖ * ‖b‖ + ‖a₀‖ * ‖b - b₀‖ + ‖a₀ * b₀ - 1‖ := by
  rw [product_error_decomposition]
  calc
    ‖(a - a₀) * b + a₀ * (b - b₀) + (a₀ * b₀ - 1)‖ ≤
        ‖(a - a₀) * b‖ + ‖a₀ * (b - b₀)‖ + ‖a₀ * b₀ - 1‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖a - a₀‖ * ‖b‖ + ‖a₀‖ * ‖b - b₀‖ + ‖a₀ * b₀ - 1‖ := by
      gcongr
      · exact norm_mul_le _ _
      · exact norm_mul_le _ _

/-- Complete finite empirical estimate, with both moment factors retained. -/
theorem finiteMean_product_error_le (s : Finset ι) (a b a₀ b₀ : ι → E)
    (q : ℝ) (hq : 0 < q) :
    finiteMean s (fun i => ‖a i * b i - 1‖) ≤
      q * (finiteMean s (fun i => ‖a i - a₀ i‖ ^ 2) +
        finiteMean s (fun i => ‖b i - b₀ i‖ ^ 2)) +
      (finiteMean s (fun i => ‖b i‖ ^ 2) +
        finiteMean s (fun i => ‖a₀ i‖ ^ 2)) / (4 * q) +
      finiteMean s (fun i => ‖a₀ i * b₀ i - 1‖) := by
  calc
    finiteMean s (fun i => ‖a i * b i - 1‖) ≤
        finiteMean s (fun i =>
          q * (‖a i - a₀ i‖ ^ 2 + ‖b i - b₀ i‖ ^ 2) +
          (‖b i‖ ^ 2 + ‖a₀ i‖ ^ 2) / (4 * q) + ‖a₀ i * b₀ i - 1‖) := by
      apply finiteMean_mono
      intro i hi
      have h₁ := young_parameter ‖a i - a₀ i‖ ‖b i‖ q hq
      have h₂ := young_parameter ‖b i - b₀ i‖ ‖a₀ i‖ q hq
      have h₃ := norm_product_error_le (a i) (b i) (a₀ i) (b₀ i)
      rw [add_div]
      rw [mul_comm ‖b i - b₀ i‖ ‖a₀ i‖] at h₂
      nlinarith
    _ = _ := by
      simp only [finiteMean_add, finiteMean_smul, finiteMean_div]

/-- Sharp Cauchy–Schwarz version.  This supports explicit analytic rates;
the asymptotic theorem below uses Young only to simplify its epsilon proof. -/
theorem finiteMean_product_error_le_sqrt (s : Finset ι) (a b a₀ b₀ : ι → E) :
    finiteMean s (fun i => ‖a i * b i - 1‖) ≤
      Real.sqrt (finiteMean s (fun i => ‖a i - a₀ i‖ ^ 2)) *
        Real.sqrt (finiteMean s (fun i => ‖b i‖ ^ 2)) +
      Real.sqrt (finiteMean s (fun i => ‖a₀ i‖ ^ 2)) *
        Real.sqrt (finiteMean s (fun i => ‖b i - b₀ i‖ ^ 2)) +
      finiteMean s (fun i => ‖a₀ i * b₀ i - 1‖) := by
  have h₁ := finiteMean_mul_le_sqrt s
    (fun i => ‖a i - a₀ i‖) (fun i => ‖b i‖)
    (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
  have h₂ := finiteMean_mul_le_sqrt s
    (fun i => ‖a₀ i‖) (fun i => ‖b i - b₀ i‖)
    (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
  calc
    finiteMean s (fun i => ‖a i * b i - 1‖) ≤
        finiteMean s (fun i =>
          ‖a i - a₀ i‖ * ‖b i‖ + ‖a₀ i‖ * ‖b i - b₀ i‖ +
            ‖a₀ i * b₀ i - 1‖) :=
      finiteMean_mono _ _ _ (fun i _ => norm_product_error_le _ _ _ _)
    _ = finiteMean s (fun i => ‖a i - a₀ i‖ * ‖b i‖) +
        finiteMean s (fun i => ‖a₀ i‖ * ‖b i - b₀ i‖) +
        finiteMean s (fun i => ‖a₀ i * b₀ i - 1‖) := by
      simp only [finiteMean_add]
    _ ≤ _ := by linarith

/-- The exact order of limits is explicit: first the sample stage n tends to
infinity with J fixed, then the truncation budget J tends to infinity. -/
theorem product_error_tendsto_zero
    (s : ℕ → Finset ι) (a b : ℕ → ι → E)
    (a₀ b₀ : ℕ → ℕ → ι → E) (C : ℝ) (hC : 0 ≤ C)
    (d p : ℕ → ℝ)
    (hd : Tendsto d atTop (nhds 0)) (hp : Tendsto p atTop (nhds 0))
    (hb : ∀ᶠ n in atTop, finiteMean (s n) (fun i => ‖b n i‖ ^ 2) ≤ C)
    (ha₀ : ∀ J, ∀ᶠ n in atTop,
      finiteMean (s n) (fun i => ‖a₀ J n i‖ ^ 2) ≤ C)
    (hatail : ∀ J η, 0 < η → ∀ᶠ n in atTop,
      finiteMean (s n) (fun i => ‖a n i - a₀ J n i‖ ^ 2) ≤ d J + η)
    (hbtail : ∀ J η, 0 < η → ∀ᶠ n in atTop,
      finiteMean (s n) (fun i => ‖b n i - b₀ J n i‖ ^ 2) ≤ d J + η)
    (hfixed : ∀ J η, 0 < η → ∀ᶠ n in atTop,
      finiteMean (s n) (fun i => ‖a₀ J n i * b₀ J n i - 1‖) ≤ p J + η) :
    Tendsto (fun n => finiteMean (s n) (fun i => ‖a n i * b n i - 1‖))
      atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let q : ℝ := (C + 1) / ε
  have hq : 0 < q := by dsimp [q]; positivity
  let δ : ℝ := ε / (8 * q)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hdsmall := (Metric.tendsto_nhds.1 hd) (δ / 2) (by positivity)
  have hpsmall := (Metric.tendsto_nhds.1 hp) (ε / 8) (by positivity)
  obtain ⟨J, hJ⟩ := (hdsmall.and hpsmall).exists
  have hdJ : d J < δ / 2 :=
    (abs_lt.mp (by simpa [Real.dist_eq] using hJ.1)).2
  have hpJ : p J < ε / 8 :=
    (abs_lt.mp (by simpa [Real.dist_eq] using hJ.2)).2
  have hqε : q * ε = C + 1 := by
    dsimp [q]
    exact div_mul_cancel₀ _ (ne_of_gt hε)
  have hδeq : q * (δ + δ) = ε / 4 := by
    dsimp [δ]
    field_simp [ne_of_gt hq]
    ring
  have hmoment : (C + C) / (4 * q) < ε / 2 := by
    apply (div_lt_iff₀ (by positivity : 0 < 4 * q)).2
    nlinarith [hqε]
  filter_upwards [hb, ha₀ J, hatail J (δ / 2) (by positivity),
    hbtail J (δ / 2) (by positivity), hfixed J (ε / 8) (by positivity)] with n hnB hnA hnTa hnTb hnP
  have hTa : finiteMean (s n) (fun i => ‖a n i - a₀ J n i‖ ^ 2) ≤ δ := by
    linarith
  have hTb : finiteMean (s n) (fun i => ‖b n i - b₀ J n i‖ ^ 2) ≤ δ := by
    linarith
  have hP : finiteMean (s n) (fun i => ‖a₀ J n i * b₀ J n i - 1‖) ≤ ε / 4 := by
    linarith
  have hbound : finiteMean (s n) (fun i => ‖a n i * b n i - 1‖) < ε := by
    calc
      finiteMean (s n) (fun i => ‖a n i * b n i - 1‖) ≤
          q * (finiteMean (s n) (fun i => ‖a n i - a₀ J n i‖ ^ 2) +
            finiteMean (s n) (fun i => ‖b n i - b₀ J n i‖ ^ 2)) +
          (finiteMean (s n) (fun i => ‖b n i‖ ^ 2) +
            finiteMean (s n) (fun i => ‖a₀ J n i‖ ^ 2)) / (4 * q) +
          finiteMean (s n) (fun i => ‖a₀ J n i * b₀ J n i - 1‖) :=
        finiteMean_product_error_le _ _ _ _ _ q hq
      _ ≤ q * (δ + δ) + (C + C) / (4 * q) + ε / 4 := by gcongr
      _ < ε := by rw [hδeq]; linarith
  have hnonneg : 0 ≤ finiteMean (s n) (fun i => ‖a n i * b n i - 1‖) :=
    finiteMean_nonneg _ _ (fun _ _ => norm_nonneg _)
  simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hbound

/-- Finite Markov inequality, counting multiplicity through distinct sample
indices.  Empty samples have mean and density zero by the field convention. -/
theorem bad_density_le (s : Finset ι) (a b : ι → E)
    (P : ι → Prop) (ε : ℝ) (hε : 0 < ε)
    (hP : ∀ i ∈ s, P i → ε ≤ ‖a i * b i - 1‖) :
    ((s.filter P).card : ℝ) / (s.card : ℝ) ≤
      finiteMean s (fun i => ‖a i * b i - 1‖) / ε := by
  classical
  have hsum : ε * ((s.filter P).card : ℝ) ≤
      ∑ i ∈ s, ‖a i * b i - 1‖ := by
    calc
      ε * ((s.filter P).card : ℝ) = ∑ i ∈ s.filter P, ε := by simp [mul_comm]
      _ ≤ ∑ i ∈ s.filter P, ‖a i * b i - 1‖ := by
        apply Finset.sum_le_sum
        intro i hi
        exact hP i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2
      _ ≤ ∑ i ∈ s, ‖a i * b i - 1‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => norm_nonneg _)
  apply (le_div_iff₀ hε).2
  calc
    ((s.filter P).card : ℝ) / (s.card : ℝ) * ε =
        (ε * ((s.filter P).card : ℝ)) / (s.card : ℝ) := by ring
    _ ≤ finiteMean s (fun i => ‖a i * b i - 1‖) :=
      div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)

theorem bad_density_tendsto_zero (s : ℕ → Finset ι) (a b : ℕ → ι → E)
    (P : ℕ → ι → Prop) (ε : ℝ) (hε : 0 < ε)
    (hP : ∀ n i, i ∈ s n → P n i → ε ≤ ‖a n i * b n i - 1‖)
    (hmean : Tendsto (fun n => finiteMean (s n) (fun i => ‖a n i * b n i - 1‖))
      atTop (nhds 0)) :
    Tendsto (fun n => (((s n).filter (P n)).card : ℝ) / ((s n).card : ℝ))
      atTop (nhds 0) := by
  classical
  apply squeeze_zero
    (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (fun n => bad_density_le (s n) (a n) (b n) (P n) ε hε (hP n))
  simpa using hmean.div_const ε

end Ring

section CompactFunctions

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- A zero of either continuous function anywhere in the compact domain forces
a unit-sized uniform product error.  This includes the equality threshold. -/
theorem zero_on_compact_forces_product_error (a b : C(X, ℂ))
    (hzero : ∃ x, a x = 0 ∨ b x = 0) : 1 ≤ ‖a * b - 1‖ := by
  obtain ⟨x, hx⟩ := hzero
  have heval : (a * b - 1) x = (-1 : ℂ) := by
    rcases hx with ha | hb
    · simp [ha]
    · simp [hb]
  calc
    (1 : ℝ) = ‖(a * b - 1) x‖ := by simp [heval]
    _ ≤ ‖a * b - 1‖ := ContinuousMap.norm_coe_le_norm _ _

/-- The actual compact zero-event density consequence, with zeros allowed
anywhere in the compact rather than only at selected evaluation points. -/
theorem zero_on_compact_density_tendsto_zero
    (s : ℕ → Finset ι) (a b : ℕ → ι → C(X, ℂ))
    (hmean : Tendsto
      (fun n => finiteMean (s n) (fun i => ‖a n i * b n i - 1‖))
      atTop (nhds 0)) :
    Tendsto
      (fun n => (((s n).filter (fun i => ∃ x, a n i x = 0 ∨ b n i x = 0)).card : ℝ) /
        ((s n).card : ℝ)) atTop (nhds 0) := by
  apply bad_density_tendsto_zero s a b
    (fun n i => ∃ x, a n i x = 0 ∨ b n i x = 0) 1 (by norm_num)
    (fun n i _ => zero_on_compact_forces_product_error (a n i) (b n i)) hmean

/-- Uniformly small values, rather than only exact zeros, satisfy a finite
quadratic density estimate.  The reciprocal partner's second moment is the
only extra term. -/
theorem small_value_density_le
    (s : Finset ι) (a b : ι → C(X, ℂ)) (η : ℝ) (hη : 0 ≤ η) :
    ((s.filter (fun i => ∃ x, ‖a i x‖ ≤ η)).card : ℝ) / (s.card : ℝ) ≤
      2 * finiteMean s (fun i => ‖a i * b i - 1‖) +
        η ^ 2 * finiteMean s (fun i => ‖b i‖ ^ 2) := by
  calc
    ((s.filter (fun i => ∃ x, ‖a i x‖ ≤ η)).card : ℝ) / (s.card : ℝ) ≤
        finiteMean s (fun i => 2 * ‖a i * b i - 1‖ + η ^ 2 * ‖b i‖ ^ 2) := by
      apply density_le_mean_of_one_le
      · intro i hi
        positivity
      · intro i hi hsmall
        obtain ⟨x, hx⟩ := hsmall
        have hid : (a i * b i - 1) x - (a i * b i) x = (-1 : ℂ) := by
          simp only [ContinuousMap.sub_apply, ContinuousMap.mul_apply,
            ContinuousMap.one_apply]
          ring
        have herr : ‖(a i * b i - 1) x‖ ≤ ‖a i * b i - 1‖ :=
          ContinuousMap.norm_coe_le_norm _ _
        have hmul : ‖(a i * b i) x‖ ≤ η * ‖b i‖ := by
          calc
            ‖(a i * b i) x‖ ≤ ‖a i x‖ * ‖b i x‖ := by
              exact norm_mul_le _ _
            _ ≤ η * ‖b i‖ :=
              mul_le_mul hx (ContinuousMap.norm_coe_le_norm _ _) (norm_nonneg _) hη
        have hsrc : (1 : ℝ) ≤ ‖a i * b i - 1‖ + η * ‖b i‖ := by
          have htri := norm_sub_le ((a i * b i - 1) x) ((a i * b i) x)
          rw [hid] at htri
          simp only [norm_neg, norm_one] at htri
          linarith
        nlinarith [sq_nonneg (η * ‖b i‖ - 1)]
    _ = _ := by simp only [finiteMean_add, finiteMean_smul]

/-- Explicit asymptotic form: with reciprocal second moments at most C,
the eventual proportion of samples taking a value of size ≤η anywhere in
the compact is at most Cη² plus any prescribed positive error. -/
theorem small_value_density_eventually_le
    (s : ℕ → Finset ι) (a b : ℕ → ι → C(X, ℂ))
    (C : ℝ)
    (hb : ∀ᶠ n in atTop, finiteMean (s n) (fun i => ‖b n i‖ ^ 2) ≤ C)
    (hmean : Tendsto
      (fun n => finiteMean (s n) (fun i => ‖a n i * b n i - 1‖))
      atTop (nhds 0))
    (η : ℝ) (hη : 0 ≤ η) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop,
      (((s n).filter (fun i => ∃ x, ‖a n i x‖ ≤ η)).card : ℝ) / ((s n).card : ℝ) ≤
        C * η ^ 2 + δ := by
  have he := (Metric.tendsto_nhds.1 hmean) (δ / 2) (by positivity)
  filter_upwards [hb, he] with n hnB hnE
  have hE : 2 * finiteMean (s n) (fun i => ‖a n i * b n i - 1‖) < δ := by
    have hEabs : |finiteMean (s n) (fun i => ‖a n i * b n i - 1‖)| < δ / 2 := by
      simpa [Real.dist_eq] using hnE
    have hEupper := (abs_lt.mp hEabs).2
    linarith
  have hmoment := mul_le_mul_of_nonneg_left hnB (sq_nonneg η)
  have hfinite := small_value_density_le (s n) (a n) (b n) η hη
  nlinarith

end CompactFunctions

end RiemannResearch.Analysis.EmpiricalReciprocalTransfer
