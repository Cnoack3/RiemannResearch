import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.Analysis.IntegratedCountingPairing

/-!
# Abel integration for the actual multiplicity-weighted zeta zeros

The right-continuous count is the repository's actual `Zeta23.Ncount 0 t`.
Its Abel pairing is proved equal to the genuine finite zero sum. The proof
expands the count as a finite sum of step functions, integrates each step,
and applies the fundamental theorem of calculus. No zero-count asymptotic,
density hypothesis, RH, or S₁ mean-square estimate is assumed.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
open Zeta23
open RiemannResearch.Analysis.IntegratedCountingPairing

namespace RiemannResearch.Analysis.ActualZeroAbelPairing
open ActualZeroOrdinate

theorem cutoff_eq_filter {t T : ℝ} (ht : t ≤ T) :
    cutoff t = (cutoff T).filter (fun ρ => ρ.im ≤ t) := by
  classical
  ext ρ
  simp only [mem_cutoff, Finset.mem_filter]
  constructor
  · intro h
    exact ⟨⟨h.1, h.2.1, h.2.2.trans ht⟩, h.2.2⟩
  · intro h
    exact ⟨h.1.1, h.1.2.1, h.2⟩

/-- The count on a fixed compact interval is a finite sum of actual jumps. -/
theorem count_eq_finite_steps {t T : ℝ} (ht : t ≤ T) :
    (Ncount 0 t : ℂ) =
      ∑ ρ ∈ cutoff T, if ρ.im ≤ t then (zeroMult ρ : ℂ) else 0 := by
  classical
  rw [count_eq_sum, cutoff_eq_filter ht]
  simp only [Nat.cast_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ρ hρ
  split_ifs <;> simp

private theorem step_eq_indicator (y : ℝ) (w : ℂ) (g : ℝ → ℂ) :
    (fun t => (if y ≤ t then w else 0) * g t) =
      fun t => w * (Set.Ici y).indicator g t := by
  funext t
  by_cases ht : y ≤ t <;> simp [Set.indicator, ht]

private theorem intervalIntegrable_step {T : ℝ} (hT : 0 ≤ T)
    {g : ℝ → ℂ} (hg : IntervalIntegrable g volume 0 T) (y : ℝ) (w : ℂ) :
    IntervalIntegrable (fun t => (if y ≤ t then w else 0) * g t) volume 0 T := by
  rw [step_eq_indicator]
  apply IntervalIntegrable.const_mul
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hg).indicator
    measurableSet_Ici

private theorem integral_step {y T : ℝ} (hy : 0 < y) (hyT : y ≤ T)
    (w : ℂ) {F F₁ : ℝ → ℂ}
    (hF : ∀ t ∈ Set.uIcc 0 T, HasDerivAt F (F₁ t) t)
    (hF₁ : IntervalIntegrable F₁ volume 0 T) :
    (∫ t in 0..T, (if y ≤ t then w else 0) * F₁ t) = w * (F T - F y) := by
  have hT : 0 ≤ T := hy.le.trans hyT
  have hset : Set.Ici y ∩ Set.Ioc 0 T = Set.Icc y T := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioc, Set.mem_Icc]
    constructor
    · exact fun h => ⟨h.1, h.2.2⟩
    · exact fun h => ⟨h.1, hy.trans_le h.1, h.2⟩
  have hsub : Set.uIcc y T ⊆ Set.uIcc 0 T := by
    rw [Set.uIcc_of_le hyT, Set.uIcc_of_le hT]
    exact Set.Icc_subset_Icc hy.le le_rfl
  rw [step_eq_indicator, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_of_le hT, integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici, hset,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hyT]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hF t (hsub ht)) (hF₁.mono_set hsub)]

/-- Integrability is discharged from the actual finite-step representation. -/
theorem count_mul_intervalIntegrable {T : ℝ} (hT : 0 ≤ T)
    {g : ℝ → ℂ} (hg : IntervalIntegrable g volume 0 T) :
    IntervalIntegrable (fun t => (Ncount 0 t : ℂ) * g t) volume 0 T := by
  classical
  have hs : IntervalIntegrable
      (fun t => ∑ ρ ∈ cutoff T, (if ρ.im ≤ t then (zeroMult ρ : ℂ) else 0) * g t)
      volume 0 T := by
    have hs₀ := IntervalIntegrable.sum (cutoff T)
      (fun ρ _ => intervalIntegrable_step hT hg ρ.im (zeroMult ρ))
    have heq : (∑ ρ ∈ cutoff T, fun t =>
        (if ρ.im ≤ t then (zeroMult ρ : ℂ) else 0) * g t) =
        (fun t => ∑ ρ ∈ cutoff T,
          (if ρ.im ≤ t then (zeroMult ρ : ℂ) else 0) * g t) := by
      funext t
      simp only [Finset.sum_apply]
    rw [heq] at hs₀
    exact hs₀
  apply hs.congr
  intro t ht
  have htT : t ≤ T := by
    rw [Set.uIoc_of_le hT] at ht
    exact ht.2
  dsimp only
  rw [count_eq_finite_steps htT, Finset.sum_mul]

/-- Exact Abel formula for all actual zeros up to T, including zeros at T
with full multiplicity, as required by the right-continuous convention. -/
theorem abelPairing_count_eq_actual_sum {T : ℝ} (hT : 0 ≤ T)
    {F F₁ : ℝ → ℂ}
    (hF : ∀ t ∈ Set.uIcc 0 T, HasDerivAt F (F₁ t) t)
    (hF₁ : IntervalIntegrable F₁ volume 0 T) :
    abelPairing (fun t => (Ncount 0 t : ℂ)) F F₁ 0 T =
      ActualZeroOrdinate.sum T (fun ρ => F ρ.im) := by
  classical
  have hi : (∫ t in 0..T, (Ncount 0 t : ℂ) * F₁ t) =
      ∑ ρ ∈ cutoff T, (zeroMult ρ : ℂ) * (F T - F ρ.im) := by
    calc
      _ = ∫ t in 0..T, ∑ ρ ∈ cutoff T,
          (if ρ.im ≤ t then (zeroMult ρ : ℂ) else 0) * F₁ t := by
        apply intervalIntegral.integral_congr
        intro t ht
        have htT : t ≤ T := by
          rw [Set.uIcc_of_le hT] at ht
          exact ht.2
        dsimp only
        rw [count_eq_finite_steps htT, Finset.sum_mul]
      _ = ∑ ρ ∈ cutoff T, ∫ t in 0..T,
          (if ρ.im ≤ t then (zeroMult ρ : ℂ) else 0) * F₁ t := by
        apply intervalIntegral.integral_finsetSum
        intro ρ hρ
        exact intervalIntegrable_step hT hF₁ ρ.im (zeroMult ρ)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro ρ hρ
        exact integral_step (mem_cutoff.mp hρ).2.1 (mem_cutoff.mp hρ).2.2
          (zeroMult ρ) hF hF₁
  have hz : cutoff 0 = ∅ := by
    ext ρ
    constructor
    · intro hρ
      exfalso
      have h := mem_cutoff.mp hρ
      exact (not_lt_of_ge h.2.2) h.2.1
    · intro hρ
      simp at hρ
  have hn : Ncount 0 0 = 0 := by rw [count_eq_sum, hz]; simp
  dsimp only [abelPairing, ActualZeroOrdinate.sum]
  rw [hn, Nat.cast_zero, zero_mul, sub_zero, hi, count_eq_sum]
  simp only [Nat.cast_sum]
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ρ hρ
  ring

/-- Exact finite-window Abel formula. The difference of actual zero sums
counts precisely a < Im(ρ) ≤ b, retaining full multiplicity at b. -/
theorem abelPairing_count_eq_actual_sum_sub
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {F F₁ : ℝ → ℂ}
    (hF : ∀ t ∈ Set.uIcc 0 b, HasDerivAt F (F₁ t) t)
    (hF₁ : IntervalIntegrable F₁ volume 0 b) :
    abelPairing (fun t => (Ncount 0 t : ℂ)) F F₁ a b =
      ActualZeroOrdinate.sum b (fun ρ => F ρ.im) -
        ActualZeroOrdinate.sum a (fun ρ => F ρ.im) := by
  have hb : 0 ≤ b := ha.trans hab
  have h0a : Set.uIcc 0 a ⊆ Set.uIcc 0 b := by
    rw [Set.uIcc_of_le ha, Set.uIcc_of_le hb]
    exact Set.Icc_subset_Icc le_rfl hab
  have hab0 : Set.uIcc a b ⊆ Set.uIcc 0 b := by
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le hb]
    exact Set.Icc_subset_Icc ha le_rfl
  have hN := count_mul_intervalIntegrable hb hF₁
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (hN.mono_set h0a) (hN.mono_set hab0)
  rw [← abelPairing_count_eq_actual_sum hb hF hF₁,
    ← abelPairing_count_eq_actual_sum ha (fun t ht => hF t (h0a ht))
      (hF₁.mono_set h0a)]
  dsimp only [abelPairing]
  rw [← hi]
  ring

end RiemannResearch.Analysis.ActualZeroAbelPairing
