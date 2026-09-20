import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Minimum multiplicative occupation statistics

Source: user-provided damped determinant argument, 2026-09-20. With weights
strictly between zero and one, the multiplicative statistic reaches its
minimum exactly at full occupation. The integral statement is for an actual
probability measure; it makes no independence assumption and is suitable for
finite weighted DPP determinants. Infinite Fredholm existence is separate.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace RiemannResearch.Probability.Occupancy

variable {ι : Type*} [Fintype ι]

def product (a : ι → ℝ) (x : ι → Bool) : ℝ :=
  ∏ i, if x i = true then 1 - a i else 1

def benchmark (a : ι → ℝ) : ℝ := ∏ i, (1 - a i)

theorem product_bounds (a : ι → ℝ) (ha : ∀ i, 0 < a i ∧ a i < 1) (x : ι → Bool) :
    0 < benchmark a ∧ benchmark a ≤ product a x ∧ product a x ≤ 1 := by
  have hb : ∀ i, 0 < 1 - a i := fun i => by linarith [(ha i).2]
  refine ⟨Finset.prod_pos (fun i _ => hb i), ?_, ?_⟩
  · exact Finset.prod_le_prod (fun i _ => (hb i).le)
      (fun i _ => by split_ifs <;> linarith [(ha i).1])
  · exact Finset.prod_le_one (fun i _ => by split_ifs <;> linarith [hb i])
      (fun i _ => by split_ifs <;> linarith [(ha i).1])

theorem product_eq_benchmark_iff (a : ι → ℝ)
    (ha : ∀ i, 0 < a i ∧ a i < 1) (x : ι → Bool) :
    product a x = benchmark a ↔ ∀ i, x i = true := by
  constructor
  · intro he
    by_contra hn
    obtain ⟨i, hi⟩ := not_forall.mp hn
    have hlt : benchmark a < product a x := by
      apply Finset.prod_lt_prod
      · intro j _
        linarith [(ha j).2]
      · intro j _
        split_ifs <;> linarith [(ha j).1]
      · refine ⟨i, Finset.mem_univ i, ?_⟩
        simp only [if_neg hi]
        linarith [(ha i).1]
    linarith
  · intro h
    simp [product, benchmark, h]

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- A measurable finite observation of any point process. -/
theorem product_integrable (a : ι → ℝ) (ha : ∀ i, 0 < a i ∧ a i < 1)
    (f : Ω → ι → Bool) (hf : Measurable f) :
    Integrable (fun ω => product a (f ω)) μ := by
  have hm : Measurable (fun ω => product a (f ω)) :=
    (measurable_of_finite (product a)).comp hf
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [] with ω
  have hb := product_bounds a ha (f ω)
  rw [Real.norm_eq_abs, abs_of_nonneg (hb.1.le.trans hb.2.1)]
  exact hb.2.2

/-- Equality at the minimum means every observed site is occupied almost surely. -/
theorem integral_product_eq_benchmark_iff (a : ι → ℝ)
    (ha : ∀ i, 0 < a i ∧ a i < 1) (f : Ω → ι → Bool) (hf : Measurable f) :
    (∫ ω, product a (f ω) ∂μ) = benchmark a ↔
      ∀ᵐ ω ∂μ, ∀ i, f ω i = true := by
  have hint := product_integrable μ a ha f hf
  have hnonneg : 0 ≤ (fun ω => product a (f ω) - benchmark a) := by
    intro ω
    exact sub_nonneg.mpr (product_bounds a ha (f ω)).2.1
  have hz := integral_eq_zero_iff_of_nonneg hnonneg
    (hint.sub (integrable_const (benchmark a)))
  rw [integral_sub hint (integrable_const (benchmark a))] at hz
  simp only [integral_const, probReal_univ, one_smul, sub_eq_zero] at hz
  exact hz.trans (Filter.eventually_congr (Filter.Eventually.of_forall
    (fun ω => by simpa only [Pi.zero_apply, sub_eq_zero] using
      product_eq_benchmark_iff a ha (f ω))))

end RiemannResearch.Probability.Occupancy
