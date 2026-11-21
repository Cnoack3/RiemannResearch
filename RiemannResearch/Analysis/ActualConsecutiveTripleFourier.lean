/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ActualConsecutivePhase
import RiemannResearch.Analysis.ActualZeroLoglogRate
import Mathlib.Tactic.LinearCombination

/-!
# Signed rational Fourier modes on consecutive zeta-zero triples

Ford, Meng and Zaharescu, https://doi.org/10.1112/blms.12001, study the
one-ordinate distribution. The mixed increment below transfers its fixed
nonzero rational modes to three genuine consecutive copies. The sole analytic
premise of this transfer is sublinear squared-gap energy, supplied on paper
by Fujii, Theorem 1, https://doi.org/10.3792/pja/1195518466. The one-point
rational mode is already proved in the project without a density premise.
-/

noncomputable section
open Filter Zeta23
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ZeroOrdinate

/-- Product of the two outer phase increments about the middle ordinate. -/
def tripleIncrement (a b c x y z : ℝ) : ℂ :=
  (phase a x - phase a y) * phase b y * (phase c z - phase c y)

theorem triple_phase_split (a b c x y z : ℝ) :
    phase a x * phase b y * phase c z = phase a x * phase (b+c) y +
      (phase (a+b) y * phase c z - phase (a+b+c) y) + tripleIncrement a b c x y z := by
  simp only [tripleIncrement, phase_add]
  ring

/-- Count every genuine consecutive triple once, including coincident ordinates. -/
def interiorTriplePhaseSum (T a b c : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (Ncount 0 T-2),
    phase a (cutoffOrdinate T j) * phase b (cutoffOrdinate T (j+1)) *
      phase c (cutoffOrdinate T (j+2))

private theorem sum_shift (f : ℕ → ℂ) (n : ℕ) :
    (∑ j ∈ Finset.range n, f (j+1)) = (∑ j ∈ Finset.range n, f j) + (f n - f 0) := by
  linear_combination Finset.sum_range_succ f n - Finset.sum_range_succ' f n

/-- The exact signed identity before the final two padded terms are removed. -/
theorem paddedTriple_phase_identity (T a b c : ℝ) :
    (∑ j ∈ Finset.range (Ncount 0 T), phase a (cutoffOrdinate T j) *
      phase b (cutoffOrdinate T (j+1)) * phase c (cutoffOrdinate T (j+2))) =
      cutoffPairSum T a (b+c) + (cutoffPairSum T (a+b) c - ordinateSum T (a+b+c)) +
      (phase (a+b+c) (cutoffOrdinate T 0) -
        phase (a+b) (cutoffOrdinate T 0) * phase c (cutoffOrdinate T 1)) +
      ∑ j ∈ Finset.range (Ncount 0 T), tripleIncrement a b c
        (cutoffOrdinate T j) (cutoffOrdinate T (j+1)) (cutoffOrdinate T (j+2)) := by
  let f (j : ℕ) := phase (a+b) (cutoffOrdinate T j) * phase c (cutoffOrdinate T (j+1)) -
      phase (a+b+c) (cutoffOrdinate T j)
  have hf : f (Ncount 0 T) = 0 := by
    simp only [f, cutoffOrdinate_at_count, cutoffOrdinate_of_count_le (Nat.le_succ _), phase_add]
    ring
  have hs := sum_shift f (Ncount 0 T)
  rw [hf] at hs
  simp only [f, Finset.sum_sub_distrib, cutoffOrdinate_phase_sum] at hs
  simp only [triple_phase_split a b c, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  unfold cutoffPairSum
  linear_combination hs

private theorem norm_increment_sum_le (T a b c : ℝ) :
    ‖∑ j ∈ Finset.range (Ncount 0 T), tripleIncrement a b c
        (cutoffOrdinate T j) (cutoffOrdinate T (j+1)) (cutoffOrdinate T (j+2))‖ ≤
      |a| * |c| * cutoffGapEnergy T := by
  let g := cutoffGap T
  let n := Ncount 0 T
  have hs (u x y : ℝ) : ‖phase u x - phase u y‖ ≤ |u| * |x-y| := by
    simpa only [OrdinateLagEquidistribution.lagPhase_eq_zeroOrdinatePhase] using
      OrdinateLagPhase.phase_norm_sub_le u x y
  have step (j : ℕ) : ‖tripleIncrement a b c (cutoffOrdinate T j)
      (cutoffOrdinate T (j+1)) (cutoffOrdinate T (j+2))‖ ≤
        (|a| * |c|/2)*(g j^2+g (j+1)^2) := by
    have h₁ := hs a (cutoffOrdinate T j) (cutoffOrdinate T (j+1))
    rw [abs_sub_comm] at h₁
    have h₂ := hs c (cutoffOrdinate T (j+2)) (cutoffOrdinate T (j+1))
    change _ ≤ |a| * |g j| at h₁
    change _ ≤ |c| * |g (j+1)| at h₂
    rw [abs_of_nonneg (cutoffGap_nonneg T j)] at h₁
    rw [abs_of_nonneg (cutoffGap_nonneg T (j+1))] at h₂
    rw [tripleIncrement, norm_mul, norm_mul, phase_norm, mul_one]
    have h := mul_le_mul h₁ h₂ (norm_nonneg _) (mul_nonneg (abs_nonneg _) (cutoffGap_nonneg T j))
    have hh := mul_nonneg (mul_nonneg (abs_nonneg a) (abs_nonneg c)) (sq_nonneg (g j-g (j+1)))
    linarith only [h, hh]
  have hz : g n = 0 := by
    simp only [g, n, cutoffGap, cutoffOrdinate_at_count,
      cutoffOrdinate_of_count_le (Nat.le_succ _), sub_self]
  have hshift : (∑ j ∈ Finset.range n, (g (j+1))^2) ≤ ∑ j ∈ Finset.range n, (g j)^2 := by
    have h₀ := Finset.sum_range_succ (fun k => (g k)^2) n
    have h₁ := Finset.sum_range_succ' (fun k => (g k)^2) n
    simp only [hz, zero_pow (by decide : 2 ≠ 0), add_zero] at h₀
    linarith only [h₀, h₁, sq_nonneg (g 0)]
  calc
    _ ≤ _ := _root_.norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range n, (|a| * |c|/2)*(g j^2+g (j+1)^2) :=
      Finset.sum_le_sum fun j _ => step j
    _ ≤ _ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      have h := mul_le_mul_of_nonneg_left hshift (show 0 ≤ |a| * |c|/2 by positivity)
      change _ ≤ |a| * |c| * (∑ j ∈ Finset.range n, (g j)^2)
      linarith only [h]

private theorem trim_norm_le (f : ℕ → ℂ) (hf : ∀ j, ‖f j‖ ≤ 1) (N m : ℕ) :
    ‖(∑ j ∈ Finset.range (N-m), f j) - ∑ j ∈ Finset.range N, f j‖ ≤ (m : ℝ) := by
  let n := N-m
  let k := N-n
  have he : n+k=N := by dsimp [n,k]; omega
  have hk : (k : ℝ) ≤ m := by exact_mod_cast (show k ≤ m by dsimp [k,n]; omega)
  have ht := Finset.sum_range_add f n k
  rw [he] at ht
  have hdiff : (∑ j ∈ Finset.range n, f j) - (∑ j ∈ Finset.range N, f j) =
      -(∑ j ∈ Finset.range k, f (n+j)) := by rw [ht]; abel
  change ‖(∑ j ∈ Finset.range n, f j) - _‖ ≤ (m : ℝ)
  rw [hdiff, norm_neg]
  calc
    _ ≤ _ := _root_.norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range k, (1:ℝ) := Finset.sum_le_sum fun j _ => hf _
    _ = (k : ℝ) := by simp
    _ ≤ _ := hk

/-- At height normalization, the boundary costs at most four and the mixed
increment costs at most |ac| times the squared-gap energy. -/
theorem interiorTriple_two_pair_bound (T a b c : ℝ) :
    ‖interiorTriplePhaseSum T a b c - (cutoffPairSum T a (b+c) +
      (cutoffPairSum T (a+b) c - ordinateSum T (a+b+c)))‖ ≤
      4 + |a| * |c| * cutoffGapEnergy T := by
  let f (j : ℕ) := phase a (cutoffOrdinate T j) * phase b (cutoffOrdinate T (j+1)) *
      phase c (cutoffOrdinate T (j+2))
  let S := ∑ j ∈ Finset.range (Ncount 0 T), f j
  let A := cutoffPairSum T a (b+c) + (cutoffPairSum T (a+b) c - ordinateSum T (a+b+c))
  let B := phase (a+b+c) (cutoffOrdinate T 0) -
      phase (a+b) (cutoffOrdinate T 0) * phase c (cutoffOrdinate T 1)
  let R := ∑ j ∈ Finset.range (Ncount 0 T), tripleIncrement a b c
        (cutoffOrdinate T j) (cutoffOrdinate T (j+1)) (cutoffOrdinate T (j+2))
  have he : S = A+B+R := paddedTriple_phase_identity T a b c
  have ht : ‖interiorTriplePhaseSum T a b c-S‖ ≤ 2 :=
    by
      simpa only [interiorTriplePhaseSum, S, f, Nat.cast_ofNat] using
        trim_norm_le f (fun j => by simp [f]) (Ncount 0 T) 2
  have hB : ‖B‖ ≤ 2 := (norm_sub_le _ _).trans (by norm_num)
  have hR : ‖R‖ ≤ _ := norm_increment_sum_le T a b c
  change ‖interiorTriplePhaseSum T a b c-A‖ ≤ _
  rw [show interiorTriplePhaseSum T a b c-A = (interiorTriplePhaseSum T a b c-S)+(B+R) by
    rw [he]; ring]
  linarith only [norm_add_le (interiorTriplePhaseSum T a b c-S) (B+R),
    norm_add_le B R, ht, hB, hR]

/-- Three genuine consecutive ordinates retain the height-normalized FMZ main
term at every fixed nonconstant rational mode under Fujii's squared-gap input. -/
theorem tendsto_interiorTriple_rational_of_gap {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hnm : n ≠ m) (a b c : ℝ) (hf : a + b + c = Real.log ((n : ℝ) / m))
    (hgap : VanishingCutoffGapEnergy) :
    Tendsto (fun T : ℝ => interiorTriplePhaseSum T a b c / (T : ℂ)) atTop
      (𝓝 (rationalFMZMain n m)) := by
  let d := a+b+c
  have hd : d ≠ 0 := by
    change a+b+c ≠ 0
    rw [hf, Real.log_div (by positivity) (by positivity)]
    apply sub_ne_zero.mpr
    intro h
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have he : (n : ℝ) = m := Real.log_injOn_pos hn' hm' h
    exact hnm (by exact_mod_cast he)
  have hab : a+(b+c)=d := by dsimp [d]; ring
  have h₁ := cutoffPair_difference_div_tendsto_zero a (b+c) ((b+c)/d)
    (by rw [hab]; field_simp [hd]) hgap
  rw [hab] at h₁
  have h₂ := cutoffPair_difference_div_tendsto_zero (a+b) c (c/d)
    (by change c = c/d*d; field_simp [hd]) hgap
  have hmode := tendsto_centeredRationalOrdinate_div hn hm
  simp only [centeredRationalOrdinate, if_neg hnm, sub_zero, ← hf] at hmode
  let E (T : ℝ) := interiorTriplePhaseSum T a b c - (cutoffPairSum T a (b+c) +
      (cutoffPairSum T (a+b) c-ordinateSum T d))
  have hz : Tendsto (fun T : ℝ => (E T)/(T:ℂ)) atTop (𝓝 0) := by
    have h₄ : Tendsto (fun T : ℝ => (4:ℝ)/T) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hmajor : Tendsto (fun T : ℝ => (4+|a| * |c| * cutoffGapEnergy T)/T) atTop (𝓝 0) := by
      simpa only [add_div, mul_div_assoc, mul_zero, add_zero] using
        h₄.add (hgap.const_mul (|a| * |c|))
    apply squeeze_zero_norm' _ hmajor
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
    exact div_le_div_of_nonneg_right (interiorTriple_two_pair_bound T a b c) hT.le
  have H := ((hz.add h₁).add h₂).add hmode
  simp only [zero_add] at H
  apply H.congr'
  exact Eventually.of_forall (fun T => by dsimp only [E, d]; ring)

/-- The signed two-ordinate sum with both indices in the true cutoff. -/
def interiorPairPhaseSum (T a b : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (Ncount 0 T - 1),
    phase a (cutoffOrdinate T j) * phase b (cutoffOrdinate T (j+1))

/-- Zeroing the third frequency and restoring the last pair costs at most one. -/
theorem tendsto_interiorPair_rational_of_gap {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hnm : n ≠ m) (a b : ℝ) (hf : a + b = Real.log ((n : ℝ) / m))
    (hgap : VanishingCutoffGapEnergy) :
    Tendsto (fun T : ℝ => interiorPairPhaseSum T a b / (T : ℂ)) atTop
      (𝓝 (rationalFMZMain n m)) := by
  have h₃ := tendsto_interiorTriple_rational_of_gap hn hm hnm a b 0 (by simpa using hf) hgap
  have htail (T : ℝ) : ‖interiorPairPhaseSum T a b - interiorTriplePhaseSum T a b 0‖ ≤ 1 := by
    let f (j : ℕ) := phase a (cutoffOrdinate T j) * phase b (cutoffOrdinate T (j+1))
    have h := trim_norm_le f (fun j => by simp [f]) (Ncount 0 T - 1) 1
    have hi : Ncount 0 T - 1 - 1 = Ncount 0 T - 2 := by omega
    rw [norm_sub_rev]
    simpa only [interiorTriplePhaseSum, interiorPairPhaseSum, phase_zero, mul_one, hi,
      f, Nat.cast_one] using h
  have hz : Tendsto (fun T : ℝ => (interiorPairPhaseSum T a b - interiorTriplePhaseSum T a b 0) /
      (T : ℂ)) atTop (𝓝 0) := by
    have hmj : Tendsto (fun T : ℝ => (1 : ℝ) / T) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    apply squeeze_zero_norm' _ hmj
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
    exact div_le_div_of_nonneg_right (htail T) hT.le
  simpa only [← add_div, sub_add_cancel, zero_add] using hz.add h₃

/-- Every fixed pair of different primes, including twins, has zero rational
FMZ coefficient. This also covers the conjugate mode. -/
theorem rationalFMZMain_distinct_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    rationalFMZMain q p = 0 := by
  have h₁ : ¬ p ∣ q := fun h => hne ((Nat.dvd_prime hq).mp h |>.resolve_left hp.ne_one)
  have h₂ : ¬ q ∣ p := fun h => hne.symm ((Nat.dvd_prime hp).mp h |>.resolve_left hq.ne_one)
  rcases lt_or_gt_of_ne hne with hl | hl
  · simp [rationalFMZMain, hl, rationalLandauMain_eq_vonMangoldt_div_sqrt hp.one_le hl, h₁]
  · simp [rationalFMZMain, hl, not_lt.mpr hl.le,
      rationalLandauMain_eq_vonMangoldt_div_sqrt hq.one_le hl, h₂]

theorem tendsto_offDiagonal_prime_ordinate {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    Tendsto (fun T : ℝ => ordinateSum T (Real.log ((q : ℝ)/p)) / (T : ℂ)) atTop (𝓝 0) := by
  simpa only [centeredRationalOrdinate, if_neg hne.symm, sub_zero,
    rationalFMZMain_distinct_primes hp hq hne] using
    tendsto_centeredRationalOrdinate_div hq.one_le hp.one_le

/-- A finite weighted off-diagonal prime sum cancels on the height scale.
The cutoff and the complex weights are fixed before taking the limit. -/
theorem tendsto_finite_offDiagonal_prime_ordinate (P : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℂ)
    (hP : ∀ k ∈ P, k.1.Prime ∧ k.2.Prime ∧ k.1 ≠ k.2) :
    Tendsto (fun T : ℝ => (∑ k ∈ P, w k * ordinateSum T (Real.log ((k.2 : ℝ) / k.1))) /
      (T : ℂ)) atTop (𝓝 0) := by
  have h := tendsto_finsetSum P fun k hk =>
    (tendsto_offDiagonal_prime_ordinate (hP k hk).1 (hP k hk).2.1 (hP k hk).2.2).const_mul (w k)
  simpa only [Finset.sum_div, mul_div_assoc, mul_zero, Finset.sum_const_zero] using h

theorem tendsto_offDiagonal_prime_triple_of_gap {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (a b c : ℝ) (hf : a + b + c = Real.log ((q : ℝ) / p))
    (hgap : VanishingCutoffGapEnergy) :
    Tendsto (fun T : ℝ => interiorTriplePhaseSum T a b c / (T : ℂ)) atTop (𝓝 0) := by
  simpa only [rationalFMZMain_distinct_primes hp hq hne] using
    tendsto_interiorTriple_rational_of_gap hq.one_le hp.one_le hne.symm a b c hf hgap

end RiemannResearch.Analysis.ActualZeroOrdinate
