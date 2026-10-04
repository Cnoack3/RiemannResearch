import RiemannResearch.RH.ParetoInverseGramDual
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Polynomial conditioning of the complete physical residue dictionary

Source: user-provided `Prime_Phases_Agenda_Proof_Attempts.tex`, equation
`full-inverse-polynomial-bound` and its finite Möbius-convolution proof.
The coefficient estimate below applies to every legal conductor, including
composites. No coercivity or inverse-growth provider is assumed.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.Analysis.FiniteHilbertGram

def cutoffHarmonic (R : ℕ) : ℝ := ∑ q ∈ Finset.Icc 1 R, 1 / (q : ℝ)

def cutoffDivisorTransform (R : ℕ) (a : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 R,
    (if q ∣ d then (ArithmeticFunction.moebius q : ℝ) * a (d / q) else 0) /
      (q : ℝ)

theorem cutoffHarmonic_nonneg (R : ℕ) : 0 ≤ cutoffHarmonic R := by
  unfold cutoffHarmonic
  apply Finset.sum_nonneg
  intro q hq
  positivity

private theorem moebius_real_sq_le_one (q : ℕ) :
    (ArithmeticFunction.moebius q : ℝ) ^ 2 ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or q with h | h | h <;>
    simp [h]

private theorem sum_le_sum_of_injOn_local
    {ι κ : Type*} [DecidableEq κ] {f : ι → ℝ} {g : κ → ℝ}
    {s : Finset ι} {t : Finset κ} (e : ι → κ)
    (he : Set.InjOn e (↑s : Set ι)) (ht : s.image e ⊆ t)
    (h : ∀ i ∈ s, f i ≤ g (e i))
    (hg : ∀ j ∈ t, j ∉ s.image e → 0 ≤ g j) :
    (∑ i ∈ s, f i) ≤ ∑ j ∈ t, g j := by
  calc
    _ ≤ ∑ i ∈ s, g (e i) := Finset.sum_le_sum h
    _ = ∑ j ∈ s.image e, g j := (Finset.sum_image he).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg ht hg

private theorem cutoff_transform_pointwise (R d : ℕ) (a : ℕ → ℝ) :
    cutoffDivisorTransform R a d ^ 2 ≤ cutoffHarmonic R *
      ∑ q ∈ Finset.Icc 1 R, (if q ∣ d then a (d / q) ^ 2 else 0) / (q : ℝ) := by
  let b : ℕ → ℝ := fun q =>
    if q ∣ d then (ArithmeticFunction.moebius q : ℝ) * a (d / q) else 0
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.Icc 1 R)
    (r := fun q => b q / (q : ℝ)) (f := fun q => 1 / (q : ℝ))
    (g := fun q => b q ^ 2 / (q : ℝ))
    (by intro q hq; positivity)
    (by intro q hq; positivity)
    (by intro q hq; exact le_of_eq (by ring))
  change cutoffDivisorTransform R a d ^ 2 ≤ cutoffHarmonic R *
    ∑ q ∈ Finset.Icc 1 R, b q ^ 2 / (q : ℝ) at hcs
  apply hcs.trans
  apply mul_le_mul_of_nonneg_left _ (cutoffHarmonic_nonneg R)
  apply Finset.sum_le_sum
  intro q hq
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg q)
  by_cases hqd : q ∣ d
  · simp only [b, if_pos hqd, mul_pow]
    have hm := moebius_real_sq_le_one q
    nlinarith [sq_nonneg (a (d / q))]
  · simp [b, hqd]

private theorem cutoff_dilation_energy_le (R q : ℕ) (hq : 0 < q) (a : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 R, if q ∣ d then a (d / q) ^ 2 else 0) ≤
      ∑ k ∈ Finset.Icc 1 R, a k ^ 2 := by
  classical
  rw [← Finset.sum_filter]
  apply sum_le_sum_of_injOn_local (fun d => d / q)
  · intro d hd e he hde
    change d / q = e / q at hde
    have hqd := (Finset.mem_filter.mp hd).2
    have hqe := (Finset.mem_filter.mp he).2
    calc
      d = (d / q) * q := (Nat.div_mul_cancel hqd).symm
      _ = (e / q) * q := by rw [hde]
      _ = e := Nat.div_mul_cancel hqe
  · intro k hk
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hk
    rcases Finset.mem_filter.mp hd with ⟨hdR, hqd⟩
    rcases Finset.mem_Icc.mp hdR with ⟨hd1, hdR⟩
    have hdq : 0 < d / q :=
      Nat.div_pos (Nat.le_of_dvd (by omega : 0 < d) hqd) hq
    exact Finset.mem_Icc.mpr ⟨by omega, (Nat.div_le_self d q).trans hdR⟩
  · intro d hd
    exact le_rfl
  · intro k hk hki
    exact sq_nonneg _

/-- Finite unweighted ℓ² Möbius convolution has norm at most `H_R`. -/
theorem cutoffDivisorTransform_energy_le (R : ℕ) (a : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 R, cutoffDivisorTransform R a d ^ 2) ≤
      cutoffHarmonic R ^ 2 * ∑ k ∈ Finset.Icc 1 R, a k ^ 2 := by
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 R, cutoffHarmonic R *
        ∑ q ∈ Finset.Icc 1 R,
          (if q ∣ d then a (d / q) ^ 2 else 0) / (q : ℝ) := by
      exact Finset.sum_le_sum fun d hd => cutoff_transform_pointwise R d a
    _ = cutoffHarmonic R * ∑ q ∈ Finset.Icc 1 R,
        (∑ d ∈ Finset.Icc 1 R, if q ∣ d then a (d / q) ^ 2 else 0) / (q : ℝ) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.sum_div]
    _ ≤ cutoffHarmonic R * ∑ q ∈ Finset.Icc 1 R,
        (∑ k ∈ Finset.Icc 1 R, a k ^ 2) / (q : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (cutoffHarmonic_nonneg R)
      apply Finset.sum_le_sum
      intro q hq
      exact div_le_div_of_nonneg_right
        (cutoff_dilation_energy_le R q (by have := (Finset.mem_Icc.mp hq).1; omega) a)
        (Nat.cast_nonneg q)
    _ = _ := by
      simp only [div_eq_mul_inv, ← Finset.mul_sum, cutoffHarmonic]
      ring

def normalizedDifference (F : ThresholdHilbert) (k : ℕ) : ℝ :=
  (hilbertSequence F k - hilbertSequence F (k - 1)) / (k : ℝ)

private theorem sum_Icc_one_eq_range (R : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 R, f k) = ∑ k ∈ Finset.range R, f (k + 1) := by
  classical
  symm
  apply Finset.sum_bij (fun k hk => k + 1)
  · intro k hk
    exact Finset.mem_Icc.mpr ⟨by omega, by have := Finset.mem_range.mp hk; omega⟩
  · intro k hk l hl hkl
    omega
  · intro k hk
    rcases Finset.mem_Icc.mp hk with ⟨hk1, hkR⟩
    exact ⟨k - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro k hk
    rfl

private theorem shifted_head_energy_le (R : ℕ) (F : ThresholdHilbert) :
    (∑ k ∈ Finset.range R, hilbertSequence F k ^ 2 / ((k : ℝ) + 1) ^ 2) ≤
      ∑ k ∈ Finset.range R, hilbertSequence F (k + 1) ^ 2 / ((k : ℝ) + 2) ^ 2 := by
  induction R with
  | zero => simp
  | succ R ih =>
    have he :
        (∑ k ∈ Finset.range (R + 1), hilbertSequence F k ^ 2 / ((k : ℝ) + 1) ^ 2) =
          ∑ k ∈ Finset.range R, hilbertSequence F (k + 1) ^ 2 / ((k : ℝ) + 2) ^ 2 := by
      rw [Finset.sum_range_succ']
      simp only [hilbertSequence_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div,
        add_zero, Nat.cast_add, Nat.cast_one]
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      ring
    rw [he, Finset.sum_range_succ]
    have hp : 0 ≤ hilbertSequence F (R + 1) ^ 2 / ((R : ℝ) + 2) ^ 2 := by positivity
    linarith

private theorem physical_difference_weight (k : ℕ) :
    2 / ((k : ℝ) + 1) ^ 2 + 2 / ((k : ℝ) + 2) ^ 2 ≤
      5 * positiveWeight (k + 1) := by
  rw [positiveWeight_succ]
  unfold paretoWeight
  have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  field_simp
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

/-- The constant five is valid on the actual infinite Pareto Hilbert space. -/
theorem normalizedDifference_energy_le (R : ℕ) (F : ThresholdHilbert) :
    (∑ k ∈ Finset.Icc 1 R, normalizedDifference F k ^ 2) ≤ 5 * ‖F‖ ^ 2 := by
  rw [sum_Icc_one_eq_range]
  have hp (k : ℕ) : normalizedDifference F (k + 1) ^ 2 ≤
      2 * hilbertSequence F (k + 1) ^ 2 / ((k : ℝ) + 1) ^ 2 +
      2 * hilbertSequence F k ^ 2 / ((k : ℝ) + 1) ^ 2 := by
    simp only [normalizedDifference, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, div_pow]
    rw [← add_div]
    apply (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < ((k : ℝ) + 1) ^ 2)).mpr
    nlinarith [sq_nonneg (hilbertSequence F (k + 1) + hilbertSequence F k)]
  calc
    _ ≤ ∑ k ∈ Finset.range R,
        (2 * hilbertSequence F (k + 1) ^ 2 / ((k : ℝ) + 1) ^ 2 +
          2 * hilbertSequence F k ^ 2 / ((k : ℝ) + 1) ^ 2) :=
      Finset.sum_le_sum fun k hk => hp k
    _ ≤ ∑ k ∈ Finset.range R,
        (2 * hilbertSequence F (k + 1) ^ 2 / ((k : ℝ) + 1) ^ 2 +
          2 * hilbertSequence F (k + 1) ^ 2 / ((k : ℝ) + 2) ^ 2) := by
      simp_rw [Finset.sum_add_distrib, mul_div_assoc, ← Finset.mul_sum]
      have hshift :
          2 * (∑ k ∈ Finset.range R, hilbertSequence F k ^ 2 / ((k : ℝ) + 1) ^ 2) ≤
            2 * ∑ k ∈ Finset.range R, hilbertSequence F (k + 1) ^ 2 / ((k : ℝ) + 2) ^ 2 :=
        mul_le_mul_of_nonneg_left (shifted_head_energy_le R F) (by norm_num : (0 : ℝ) ≤ 2)
      exact add_le_add le_rfl hshift
    _ ≤ ∑ k ∈ Finset.range R,
        5 * (positiveWeight (k + 1) * hilbertSequence F (k + 1) ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      have h := mul_le_mul_of_nonneg_right (physical_difference_weight k)
        (sq_nonneg (hilbertSequence F (k + 1)))
      convert h using 1 <;> ring
    _ = 5 * ∑ k ∈ Finset.range R, positiveWeight (k + 1) * hilbertSequence F (k + 1) ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ 5 * ‖F‖ ^ 2 := by
      rw [← sum_Icc_one_eq_range R
        (fun k => positiveWeight k * hilbertSequence F k ^ 2), hilbert_norm_weighted_sq]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (hilbertSequence_square_summable F).sum_le_tsum _ (by
        intro k hk
        unfold positiveWeight
        positivity)

theorem cutoffDivisorTransform_normalizedDifference (R d : ℕ)
    (hd : 0 < d) (hdR : d ≤ R) (F : ThresholdHilbert) :
    cutoffDivisorTransform R (normalizedDifference F) d =
      mobiusDifferenceCLM d F / (d : ℝ) := by
  classical
  have hsub : d.divisors ⊆ Finset.Icc 1 R := by
    intro q hq
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hq,
      (Nat.le_of_dvd hd (Nat.mem_divisors.mp hq).1).trans hdR⟩
  have he :
      (∑ q ∈ d.divisors,
        (if q ∣ d then (ArithmeticFunction.moebius q : ℝ) * normalizedDifference F (d / q)
          else 0) / (q : ℝ)) = cutoffDivisorTransform R (normalizedDifference F) d := by
    unfold cutoffDivisorTransform
    apply Finset.sum_subset hsub
    intro q hqR hqd
    have hnd : ¬ q ∣ d := by
      intro hq
      exact hqd (Nat.mem_divisors.mpr ⟨hq, ne_of_gt hd⟩)
    simp [hnd]
  rw [← he]
  calc
    _ = ∑ q ∈ d.divisors,
        (ArithmeticFunction.moebius q : ℝ) * normalizedDifference F (d / q) / (q : ℝ) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [if_pos (Nat.mem_divisors.mp hq).1]
    _ = ∑ k ∈ d.divisors,
        (ArithmeticFunction.moebius (d / k) : ℝ) * normalizedDifference F k / ((d / k : ℕ) : ℝ) := by
      exact (Nat.sum_divisorsAntidiagonal (n := d)
        (fun q k => (ArithmeticFunction.moebius q : ℝ) * normalizedDifference F k / (q : ℝ))).symm.trans
        (Nat.sum_divisorsAntidiagonal' (n := d)
          (fun q k => (ArithmeticFunction.moebius q : ℝ) * normalizedDifference F k / (q : ℝ)))
    _ = (∑ k ∈ d.divisors, (ArithmeticFunction.moebius (d / k) : ℝ) *
        (hilbertSequence F k - hilbertSequence F (k - 1))) / (d : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k hk
      have hk0 : (k : ℝ) ≠ 0 := by
        exact_mod_cast ne_of_gt (Nat.pos_of_mem_divisors hk)
      have hprod : ((d / k : ℕ) : ℝ) * (k : ℝ) = (d : ℝ) := by
        exact_mod_cast Nat.div_mul_cancel (Nat.mem_divisors.mp hk).1
      rw [normalizedDifference, ← hprod]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [mobiusDifferenceCLM_apply, mobiusDifference]

/-- Weighted ℓ² coefficient recovery for every finite legal conductor. -/
theorem mobiusDifferenceCLM_weighted_energy_le (R : ℕ) (F : ThresholdHilbert) :
    (∑ d ∈ Finset.Icc 1 R, (mobiusDifferenceCLM d F / (d : ℝ)) ^ 2) ≤
      5 * cutoffHarmonic R ^ 2 * ‖F‖ ^ 2 := by
  have he :
      (∑ d ∈ Finset.Icc 1 R, (mobiusDifferenceCLM d F / (d : ℝ)) ^ 2) =
        ∑ d ∈ Finset.Icc 1 R, cutoffDivisorTransform R (normalizedDifference F) d ^ 2 := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [cutoffDivisorTransform_normalizedDifference R d
      (by have := (Finset.mem_Icc.mp hd).1; omega) (Finset.mem_Icc.mp hd).2]
  rw [he]
  have h1 := cutoffDivisorTransform_energy_le R (normalizedDifference F)
  have h2 := mul_le_mul_of_nonneg_left (normalizedDifference_energy_le R F)
    (sq_nonneg (cutoffHarmonic R))
  nlinarith

def residueSynthesis (n : ℕ) (v : Fin n → ℝ) : ThresholdHilbert :=
  ∑ i, v i • residueAtom i.val

theorem completeResidue_weighted_coefficient_bound (n : ℕ) (v : Fin n → ℝ) :
    (∑ i, (v i / ((i.val + 2 : ℕ) : ℝ)) ^ 2) ≤
      5 * cutoffHarmonic (n + 1) ^ 2 * ‖residueSynthesis n v‖ ^ 2 := by
  have hex (i : Fin n) : coefficientCLM (i.val + 2) (residueSynthesis n v) = v i :=
    coefficient_finite_sum n v i
  have hsum :
      (∑ i, (v i / ((i.val + 2 : ℕ) : ℝ)) ^ 2) ≤
        ∑ d ∈ Finset.Icc 1 (n + 1),
          (mobiusDifferenceCLM d (residueSynthesis n v) / (d : ℝ)) ^ 2 := by
    apply sum_le_sum_of_injOn_local (fun i : Fin n => i.val + 2)
    · intro i hi j hj hij
      change i.val + 2 = j.val + 2 at hij
      apply Fin.ext
      omega
    · intro d hd
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
      exact Finset.mem_Icc.mpr ⟨by omega, by have := i.isLt; omega⟩
    · intro i hi
      have h := hex i
      change -(mobiusDifferenceCLM (i.val + 2) (residueSynthesis n v)) = v i at h
      rw [← h]
      simp only [neg_div, neg_sq]
      exact le_rfl
    · intro d hd hdi
      exact sq_nonneg _
  exact hsum.trans (mobiusDifferenceCLM_weighted_energy_le (n + 1) _)

/-- The smallest Gram eigenvalue is at least `1/(5 R² H_R²)`.
Equivalently, this is the quadratic-form conditioning estimate for the full
dictionary, with `R=n+1`. Restricting `v` to composites retains the same bound. -/
theorem completeResidue_coefficient_bound (n : ℕ) (v : Fin n → ℝ) :
    (∑ i, v i ^ 2) ≤
      5 * ((n + 1 : ℕ) : ℝ) ^ 2 * cutoffHarmonic (n + 1) ^ 2 *
        ‖residueSynthesis n v‖ ^ 2 := by
  have hweight := completeResidue_weighted_coefficient_bound n v
  have hpoint (i : Fin n) : v i ^ 2 ≤
      ((n + 1 : ℕ) : ℝ) ^ 2 * (v i / ((i.val + 2 : ℕ) : ℝ)) ^ 2 := by
    have hle : ((i.val + 2 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show i.val + 2 ≤ n + 1 by have := i.isLt; omega)
    have hi0 : (0 : ℝ) < ((i.val + 2 : ℕ) : ℝ) := by positivity
    have hR0 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
    have hsq : ((i.val + 2 : ℕ) : ℝ) ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
      nlinarith
    rw [div_pow, ← mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos hi0)).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsq (sq_nonneg (v i))
  have hs : (∑ i, v i ^ 2) ≤
      ∑ i, ((n + 1 : ℕ) : ℝ) ^ 2 * (v i / ((i.val + 2 : ℕ) : ℝ)) ^ 2 :=
    Finset.sum_le_sum fun i hi => hpoint i
  rw [← Finset.mul_sum] at hs
  have hlast := mul_le_mul_of_nonneg_left hweight
    (sq_nonneg (((n + 1 : ℕ) : ℝ)))
  calc
    _ ≤ _ := hs
    _ ≤ _ := by nlinarith

private theorem inverse_quadratic_le_of_coercive
    {ι : Type*} [Fintype ι] {v : ι → ThresholdHilbert}
    (hv : LinearIndependent ℝ v) (C : ℝ) (hC : 0 ≤ C)
    (hcoercive : ∀ c : ι → ℝ,
      (∑ i, c i ^ 2) ≤ C * ‖Fintype.linearCombination ℝ v c‖ ^ 2)
    (a : ι → ℝ) :
    (∑ i, (gramEquiv hv).symm a i * a i) ≤ C * ∑ i, a i ^ 2 := by
  let c := (gramEquiv hv).symm a
  let Q := ‖Fintype.linearCombination ℝ v c‖ ^ 2
  have hq : Q = ∑ i, c i * a i := by
    dsimp only [Q]
    rw [gram_quadratic]
    have he : gram v c = a := (gramEquiv hv).apply_symm_apply a
    rw [he]
  have hsq := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c a
  rw [← hq] at hsq
  have hx := hcoercive c
  change (∑ i, c i ^ 2) ≤ C * Q at hx
  have ha0 : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun i hi => sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hx ha0
  have hQ : 0 ≤ Q := sq_nonneg _
  change (∑ i, c i * a i) ≤ C * ∑ i, a i ^ 2
  rw [← hq]
  by_cases hQ0 : Q = 0
  · rw [hQ0]
    exact mul_nonneg hC ha0
  · have hpos : 0 < Q := lt_of_le_of_ne hQ (Ne.symm hQ0)
    nlinarith

/-- Quadratic-form version of the complete inverse operator-norm bound.
The inverse is the actual Gram equivalence of all conductors `2,...,n+1`. -/
theorem completeResidue_inverse_quadratic_bound (n : ℕ) (a : Fin n → ℝ) :
    (∑ i, (gramEquiv (finiteResidue_independent n)).symm a i * a i) ≤
      5 * ((n + 1 : ℕ) : ℝ) ^ 2 * cutoffHarmonic (n + 1) ^ 2 *
        ∑ i, a i ^ 2 := by
  apply inverse_quadratic_le_of_coercive (finiteResidue_independent n)
    (5 * ((n + 1 : ℕ) : ℝ) ^ 2 * cutoffHarmonic (n + 1) ^ 2)
    (by positivity)
  intro c
  simpa only [Fintype.linearCombination_apply, residueSynthesis] using
    completeResidue_coefficient_bound n c

/-- Any actual subdictionary has the same cutoff conditioning. This includes
the full composite block, without deleting any composite below the cutoff. -/
theorem residueSubdictionary_coefficient_bound
    {ι : Type*} [Fintype ι] (n : ℕ) (e : ι → Fin n) (he : Function.Injective e)
    (v : ι → ℝ) :
    (∑ i, v i ^ 2) ≤
      5 * ((n + 1 : ℕ) : ℝ) ^ 2 * cutoffHarmonic (n + 1) ^ 2 *
        ‖Fintype.linearCombination ℝ (fun i => residueAtom (e i).val) v‖ ^ 2 := by
  classical
  let w : Fin n → ℝ := fun j => if h : ∃ i, e i = j then v (Classical.choose h) else 0
  have hw (i : ι) : w (e i) = v i := by
    have hex : ∃ j, e j = e i := ⟨i, rfl⟩
    change (if h : ∃ j, e j = e i then v (Classical.choose h) else 0) = v i
    rw [dif_pos hex]
    exact congrArg v (he (Classical.choose_spec hex))
  have hout (j : Fin n) (hj : j ∉ Finset.univ.image e) : w j = 0 := by
    have hne : ¬ ∃ i, e i = j := by
      simpa only [Finset.mem_image, Finset.mem_univ, true_and] using hj
    simp [w, hne]
  have hs : residueSynthesis n w =
      Fintype.linearCombination ℝ (fun i => residueAtom (e i).val) v := by
    unfold residueSynthesis
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)) (by
      intro j hj hje
      rw [hout j hje, zero_smul])]
    rw [Finset.sum_image (fun i hi j hj hij => he hij)]
    simp only [hw, Fintype.linearCombination_apply]
  have hm : (∑ i, v i ^ 2) = ∑ j, w j ^ 2 := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)) (by
      intro j hj hje
      rw [hout j hje]
      norm_num)]
    rw [Finset.sum_image (fun i hi j hj hij => he hij)]
    simp only [hw]
  rw [hm, ← hs]
  exact completeResidue_coefficient_bound n w

theorem residueSubdictionary_inverse_quadratic_bound
    {ι : Type*} [Fintype ι] (n : ℕ) (e : ι → Fin n) (he : Function.Injective e)
    (a : ι → ℝ) :
    (∑ i, (gramEquiv ((finiteResidue_independent n).comp e he)).symm a i * a i) ≤
      5 * ((n + 1 : ℕ) : ℝ) ^ 2 * cutoffHarmonic (n + 1) ^ 2 * ∑ i, a i ^ 2 := by
  apply inverse_quadratic_le_of_coercive ((finiteResidue_independent n).comp e he)
    (5 * ((n + 1 : ℕ) : ℝ) ^ 2 * cutoffHarmonic (n + 1) ^ 2)
    (by positivity)
  exact residueSubdictionary_coefficient_bound n e he

/-- Every nonprime legal conductor at the cutoff occurs in this index type. -/
def CompleteCompositeIndex (n : ℕ) := {i : Fin n // ¬ Nat.Prime (i.val + 2)}

instance (n : ℕ) : Fintype (CompleteCompositeIndex n) := by
  unfold CompleteCompositeIndex
  infer_instance

theorem completeComposite_independent (n : ℕ) :
    LinearIndependent ℝ
      (fun i : CompleteCompositeIndex n => residueAtom i.val.val) :=
  (finiteResidue_independent n).comp Subtype.val Subtype.val_injective

/-- The inverse of the entire composite screening block has the same explicit
polynomial bound. No conductor in `2,...,n+1` that is composite is omitted. -/
theorem completeComposite_inverse_quadratic_bound (n : ℕ)
    (a : CompleteCompositeIndex n → ℝ) :
    (∑ i, (gramEquiv (completeComposite_independent n)).symm a i * a i) ≤
      5 * ((n + 1 : ℕ) : ℝ) ^ 2 * cutoffHarmonic (n + 1) ^ 2 * ∑ i, a i ^ 2 :=
  residueSubdictionary_inverse_quadratic_bound n Subtype.val Subtype.val_injective a

end RiemannResearch.RH.Pareto.CoefficientStabilization
