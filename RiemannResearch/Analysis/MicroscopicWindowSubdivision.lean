import RiemannResearch.Analysis.ZeroDPPWindowLattice
import RiemannResearch.Analysis.ZeroDPPRankVacancy
import RiemannResearch.Analysis.MontgomeryMesoscopicGapCount
import Mathlib.MeasureTheory.Group.Integral

/-! Subdivision of a long translated zero-count window into shorter windows.
Only the integer-valued count and translation invariance of Lebesgue measure
enter the factorial-moment estimate. All occurrence labels are retained. -/

noncomputable section
open MeasureTheory Set Zeta23
open scoped BigOperators
namespace RiemannResearch.Analysis.MicroscopicWindowSubdivision

open ActualZeroOrdinate ActualZeroWindowVariance OrdinateWindowVariance
open ZeroDPPCorrelation ZeroDPPRankVacancy MontgomeryPositiveGap

private theorem pulse_split {x T t a b : ℝ} (hx : x ≤ T) (ha : 0 ≤ a) :
    windowPulse T (a + b) x t ≤ windowPulse T a x t + windowPulse T b x (t + a) := by
  simp only [windowPulse, pulse, Set.indicator, mem_Ioc, max_lt_iff, le_min_iff]
  split_ifs <;> try norm_num <;> grind

/-- Subdivision works with the original endpoint convention and clipping
to (0,T]. The shifted short windows can also pick up origins outside the
long window's support, which explains the one-sided bound. -/
theorem actualWindowCount_le_subdivided (T t : ℝ) {h : ℝ} (hh : 0 ≤ h) (k : ℕ) :
    actualWindowCount T ((k : ℝ) * h) t ≤
      ∑ i ∈ Finset.range k, actualWindowCount T h (t + (i : ℝ) * h) := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, Finset.range_zero, Finset.sum_empty]
    apply le_of_eq
    unfold actualWindowCount windowCount
    apply Finset.sum_eq_zero
    intro c _
    simp only [windowPulse, pulse, Set.indicator, sub_zero, mem_Ioc, max_lt_iff, le_min_iff]
    split_ifs with hc
    · exact False.elim ((not_lt_of_ge hc.2.2) hc.1.2)
    · rfl
  | succ k ih =>
    rw [Nat.cast_succ, add_mul, one_mul, Finset.sum_range_succ]
    apply le_trans _ (add_le_add ih (le_refl _))
    unfold actualWindowCount windowCount
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun c _ => pulse_split (mem_cutoff.mp c.1.2).2.2
      (mul_nonneg (Nat.cast_nonneg _) hh))

private theorem factorial_dominates (n : ℕ) :
    (max ((n : ℝ) - 1) 0)^2 ≤ (n : ℝ) * (n - 1) := by
  cases n with
  | zero => norm_num
  | succ n =>
    rw [Nat.cast_succ, add_sub_cancel_right, max_eq_left (Nat.cast_nonneg _)]
    nlinarith only [Nat.cast_nonneg (α := ℝ) n]

private theorem pointwise_subdivision (T t : ℝ) {h : ℝ} (hh : 0 ≤ h) (k : ℕ) :
    (if (2 * (k : ℝ)) < actualWindowCount T ((k : ℝ)*h) t
      then (actualWindowCount T ((k : ℝ)*h) t)^2 else 0) ≤
      (4 * (k : ℝ)) * ∑ i ∈ Finset.range k,
        (actualWindowCount T h (t + (i : ℝ)*h)) * (actualWindowCount T h (t + (i : ℝ)*h) - 1) := by
  let K := actualWindowCount T ((k : ℝ)*h) t
  let y := fun i : ℕ => actualWindowCount T h (t + (i : ℝ)*h)
  let e := fun i : ℕ => max (y i - 1) 0
  have he (i : ℕ) : (e i)^2 ≤ y i * (y i - 1) := by
    dsimp only [e,y]
    rw [actualWindowCount_eq_card]
    exact factorial_dominates _
  have hS := Finset.sum_le_sum (s := Finset.range k) (fun i _ => he i)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range k) (fun _ => (1 : ℝ)) e
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hcs
  change (if 2 * (k : ℝ) < K then K^2 else 0) ≤
    (4 * (k : ℝ)) * ∑ i ∈ Finset.range k, y i * (y i - 1)
  by_cases hK : 2 * (k : ℝ) < K
  · rw [if_pos hK]
    have hsub := actualWindowCount_le_subdivided T t hh k
    change K ≤ ∑ i ∈ Finset.range k, y i at hsub
    have hu : (∑ i ∈ Finset.range k, y i) ≤ ∑ i ∈ Finset.range k, (e i + 1) :=
      Finset.sum_le_sum (fun i _ => by
        have h := le_max_left (y i - 1) 0
        dsimp only [e]
        linarith only [h])
    rw [Finset.sum_add_distrib] at hu
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hu
    have h0 : 0 ≤ K := (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) (Nat.cast_nonneg _)).trans hK.le
    have hl : K ≤ 2 * ∑ i ∈ Finset.range k, e i := by linarith only [hK,hsub,hu]
    have hsquared := mul_self_le_mul_self h0 hl
    have hcs' := hcs.trans (mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg _))
    nlinarith only [hsquared,hcs']
  · rw [if_neg hK]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => (sq_nonneg _).trans (he i)))

/-- A tail of the long-window second moment is controlled by a factorial
second moment at one k-th of its width, without any moment hypothesis. -/
theorem truncatedWindowSecondMoment_subdivision {T Q : ℝ} (hT : 1 < T) (hQ : 0 ≤ Q)
    {k : ℕ} (hk : 0 < k) :
    truncatedWindowSecondMoment T Q (2*k) ≤ 4*(k : ℝ)^2 *
      ((∫ t : ℝ, let K := actualWindowCount T ((Q / k) / unfoldingScale T) t; K*(K-1)) / T) := by
  let h := (Q/k) / unfoldingScale T
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hL : 0 < unfoldingScale T := div_pos (Real.log_pos hT) (by positivity)
  have hh : 0 ≤ h := div_nonneg (div_nonneg hQ hk'.le) hL.le
  have hkh : (k : ℝ)*h = Q / (Real.log T / (2*Real.pi)) := by
    dsimp only [h, unfoldingScale]
    field_simp [hk'.ne', (Real.log_pos hT).ne', Real.pi_ne_zero]
  let f := fun t : ℝ => actualWindowCount T h t * (actualWindowCount T h t - 1)
  have hf : Integrable f := by
    have h2 := windowCount_sq_integrable (Finset.univ : Finset (Copies T)) (fun c => c.1.1.im) T h
    have h1 := windowCount_integrable (Finset.univ : Finset (Copies T)) (fun c => c.1.1.im) T h
    convert h2.sub h1 using 1
    funext t
    dsimp only [f, actualWindowCount, Pi.sub_apply]
    ring
  have hfi (i : ℕ) : Integrable (fun t => f (t + (i : ℝ)*h)) := hf.comp_add_right _
  have hsum := integrable_finsetSum (Finset.range k) (fun i _ => hfi i)
  have hi := truncatedSquare_integrable (fun c : Copies T => c.1.1.im) T ((k : ℝ)*h) (2*k)
  change Integrable (fun t : ℝ => if ((2*k : ℕ) : ℝ) < actualWindowCount T ((k : ℝ)*h) t
    then (actualWindowCount T ((k : ℝ)*h) t)^2 else 0) at hi
  have hbound := integral_mono hi (hsum.const_mul (4*(k : ℝ))) (fun t => by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, f] using pointwise_subdivision T t hh k)
  rw [integral_const_mul, integral_finsetSum (Finset.range k) (fun i _ => hfi i)] at hbound
  simp_rw [integral_add_right_eq_self f] at hbound
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hbound
  unfold truncatedWindowSecondMoment
  rw [← hkh]
  change (∫ t : ℝ, if ((2*k : ℕ) : ℝ) < actualWindowCount T ((k : ℝ)*h) t
    then (actualWindowCount T ((k : ℝ)*h) t)^2 else 0) / T ≤ 4*(k : ℝ)^2 * ((∫ t : ℝ, f t)/T)
  calc
    _ ≤ (4*(k : ℝ)*((k : ℝ)*(∫ t : ℝ, f t)))/T :=
      div_le_div_of_nonneg_right hbound (zero_lt_one.trans hT).le
    _ = _ := by ring

end RiemannResearch.Analysis.MicroscopicWindowSubdivision
