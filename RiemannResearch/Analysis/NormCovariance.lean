import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact finite covariance corrections for physical Pareto blocks

Source: user-provided CRT and Four Improvements continuation, 6–7 October 2026.
The extensions retain complete signed identities and correction squares.


The finite correction is retained as an equality when using reverse Chebyshev.
Strict opposite monotonicity gives a strict loss. The actual Pareto-site
application is supplied by `RH/ParetoAtomPhysicalNorm.lean`.
-/

noncomputable section

noncomputable section

open scoped BigOperators

namespace RiemannResearch.Analysis.NormCovariance

variable {ι : Type*}

/-- The unnormalized pairwise covariance identity, including all mixed signs. -/
theorem pair_covariance_sum (s : Finset ι) (x w : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, (x i - x j) * (w i - w j)) =
      2 * ((s.card : ℝ) * (∑ i ∈ s, x i * w i) -
        (∑ i ∈ s, x i) * (∑ i ∈ s, w i)) := by
  have hrow (i : ι) :
      (∑ j ∈ s, (x i - x j) * (w i - w j)) =
        (s.card : ℝ) * (x i * w i) -
          x i * (∑ j ∈ s, w j) - (∑ j ∈ s, x j) * w i +
          (∑ j ∈ s, x j * w j) := by
    calc
      _ = ∑ j ∈ s, (x i * w i - x i * w j - x j * w i + x j * w j) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_const, ← Finset.mul_sum, ← Finset.sum_mul,
          nsmul_eq_mul]
  simp_rw [hrow]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, ← Finset.mul_sum, ← Finset.sum_mul,
    nsmul_eq_mul]
  ring

/-- A reverse-Chebyshev loss expressed as its exact pairwise correction. -/
def covarianceCorrection (s : Finset ι) (x w : ι → ℝ) : ℝ :=
  -(∑ i ∈ s, ∑ j ∈ s, (x i - x j) * (w i - w j)) /
    (2 * (s.card : ℝ))

theorem weighted_sum_eq_mean_sub_covariance (s : Finset ι)
    (hs : s.Nonempty) (x w : ι → ℝ) :
    (∑ i ∈ s, x i * w i) =
      ((∑ i ∈ s, x i) / (s.card : ℝ)) * (∑ i ∈ s, w i) -
        covarianceCorrection s x w := by
  have hcard : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hs
  unfold covarianceCorrection
  rw [pair_covariance_sum]
  field_simp
  <;> ring

theorem covarianceCorrection_nonneg (s : Finset ι) (x w : ι → ℝ)
    (hpair : ∀ i ∈ s, ∀ j ∈ s,
      (x i - x j) * (w i - w j) ≤ 0) :
    0 ≤ covarianceCorrection s x w := by
  have hd : (∑ i ∈ s, ∑ j ∈ s, (x i - x j) * (w i - w j)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    exact Finset.sum_nonpos (fun j hj => hpair i hi j hj)
  unfold covarianceCorrection
  exact div_nonneg (neg_nonneg.mpr hd) (by positivity)

/-- One strict mixed pair gives a strictly positive covariance loss. -/
theorem covarianceCorrection_pos (s : Finset ι) (x w : ι → ℝ)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, (x i - x j) * (w i - w j) ≤ 0)
    (hstrict : ∃ i ∈ s, ∃ j ∈ s, (x i - x j) * (w i - w j) < 0) :
    0 < covarianceCorrection s x w := by
  obtain ⟨i, hi, j, hj, hij⟩ := hstrict
  have hs : s.Nonempty := ⟨i, hi⟩
  have hsum : 0 < ∑ a ∈ s, ∑ b ∈ s, -((x a - x b) * (w a - w b)) := by
    apply Finset.sum_pos'
    · intro a ha
      exact Finset.sum_nonneg (fun b hb => neg_nonneg.mpr (hpair a ha b hb))
    · refine ⟨i, hi, ?_⟩
      apply Finset.sum_pos'
      · intro b hb
        exact neg_nonneg.mpr (hpair i hi b hb)
      · exact ⟨j, hj, neg_pos.mpr hij⟩
  have hcard : 0 < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hs
  unfold covarianceCorrection
  rw [← Finset.sum_neg_distrib]
  simp_rw [← Finset.sum_neg_distrib]
  exact div_pos hsum (by positivity)

theorem weighted_sum_le_mean_of_pair_nonpos (s : Finset ι)
    (hs : s.Nonempty) (x w : ι → ℝ)
    (hpair : ∀ i ∈ s, ∀ j ∈ s,
      (x i - x j) * (w i - w j) ≤ 0) :
    (∑ i ∈ s, x i * w i) ≤
      ((∑ i ∈ s, x i) / (s.card : ℝ)) * (∑ i ∈ s, w i) := by
  rw [weighted_sum_eq_mean_sub_covariance s hs x w]
  exact sub_le_self _ (covarianceCorrection_nonneg s x w hpair)

theorem opposite_monotonicity_pair_nonpos
    {α : Type*} [LinearOrder α] (x w : α → ℝ)
    (hx : Monotone x) (hw : Antitone w) (i j : α) :
    (x i - x j) * (w i - w j) ≤ 0 := by
  rcases le_total i j with hij | hji
  · exact mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (hx hij)) (sub_nonneg.mpr (hw hij))
  · exact mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr (hx hji)) (sub_nonpos.mpr (hw hji))

def residueSquare (p : ℝ) (r : ℕ) : ℝ := (r : ℝ) ^ 2 / p ^ 2

def physicalWeight (a : ℝ) (r : ℕ) : ℝ :=
  1 / ((a + (r : ℝ)) * (a + (r : ℝ) + 1))

theorem residueSquare_monotone (p : ℝ) : Monotone (residueSquare p) := by
  intro r s hrs
  have hrs' : (r : ℝ) ≤ (s : ℝ) := by exact_mod_cast hrs
  have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hs0 : 0 ≤ (s : ℝ) := Nat.cast_nonneg s
  have hsq : (r : ℝ) ^ 2 ≤ (s : ℝ) ^ 2 := by
    have hmul := mul_nonneg (sub_nonneg.mpr hrs') (add_nonneg hs0 hr0)
    nlinarith only [hmul]
  exact div_le_div_of_nonneg_right hsq (sq_nonneg p)

theorem physicalWeight_antitone (a : ℝ) (ha : 0 < a) :
    Antitone (physicalWeight a) := by
  intro r s hrs
  have hrs' : (r : ℝ) ≤ (s : ℝ) := by exact_mod_cast hrs
  have har : 0 < a + (r : ℝ) := by positivity
  have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hs0 : 0 ≤ (s : ℝ) := Nat.cast_nonneg s
  have hden : (a + (r : ℝ)) * (a + (r : ℝ) + 1) ≤
      (a + (s : ℝ)) * (a + (s : ℝ) + 1) := by
    have hmul : 0 ≤ ((s : ℝ) - (r : ℝ)) * (2 * a + (r : ℝ) + (s : ℝ) + 1) :=
      mul_nonneg (sub_nonneg.mpr hrs') (by linarith)
    nlinarith only [hmul]
  exact one_div_le_one_div_of_le (by positivity) hden

/-- Telescoping the literal complete physical cells, at any positive real start. -/
theorem physicalWeight_sum (a : ℝ) (ha : 0 < a) (p : ℕ) :
    (∑ r ∈ Finset.range p, physicalWeight a r) =
      1 / a - 1 / (a + (p : ℝ)) := by
  induction p with
  | zero => simp [physicalWeight]
  | succ p ih =>
      rw [Finset.sum_range_succ, ih]
      unfold physicalWeight
      have ha0 : a ≠ 0 := ne_of_gt ha
      have hap : a + (p : ℝ) ≠ 0 := ne_of_gt (by positivity)
      have hap1 : a + (p : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
      simp only [Nat.cast_add, Nat.cast_one, ← add_assoc]
      field_simp [ha0, hap, hap1]
      <;> ring

theorem sum_range_real_sq (p : ℕ) :
    (∑ r ∈ Finset.range p, (r : ℝ) ^ 2) =
      (p : ℝ) * ((p : ℝ) - 1) * (2 * (p : ℝ) - 1) / 6 := by
  induction p with
  | zero => simp
  | succ p ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

theorem residueSquare_mean (p : ℕ) (hp : 0 < p) :
    (∑ r ∈ Finset.range p, residueSquare (p : ℝ) r) / (p : ℝ) =
      ((p : ℝ) - 1) * (2 * (p : ℝ) - 1) / (6 * (p : ℝ) ^ 2) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hp
  unfold residueSquare
  rw [← Finset.sum_div, sum_range_real_sq]
  field_simp
  <;> ring

def blockCorrection (p k : ℕ) : ℝ :=
  covarianceCorrection (Finset.range p) (residueSquare (p : ℝ))
    (physicalWeight ((k : ℝ) * (p : ℝ)))

theorem blockCorrection_nonneg (p k : ℕ) (hp : 0 < p) (hk : 0 < k) :
    0 ≤ blockCorrection p k := by
  unfold blockCorrection
  apply covarianceCorrection_nonneg
  intro i hi j hj
  exact opposite_monotonicity_pair_nonpos _ _
    (residueSquare_monotone _) (physicalWeight_antitone _ (by positivity)) i j

/-- The physical loss is strict for every genuine atom and positive tail block. -/
theorem blockCorrection_pos (p k : ℕ) (hp : 1 < p) (hk : 0 < k) :
    0 < blockCorrection p k := by
  unfold blockCorrection
  apply covarianceCorrection_pos
  · intro i hi j hj
    exact opposite_monotonicity_pair_nonpos _ _
      (residueSquare_monotone _) (physicalWeight_antitone _ (by positivity)) i j
  · refine ⟨1, Finset.mem_range.mpr hp, 0, Finset.mem_range.mpr (by omega), ?_⟩
    have hpR : 0 < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
    have ha : 0 < (k : ℝ) * (p : ℝ) := by positivity
    have hx : 0 < residueSquare (p : ℝ) 1 - residueSquare (p : ℝ) 0 := by
      simpa [residueSquare] using (one_div_pos.mpr (sq_pos_of_pos hpR))
    have hw : physicalWeight ((k : ℝ) * (p : ℝ)) 1 -
        physicalWeight ((k : ℝ) * (p : ℝ)) 0 < 0 := by
      apply sub_neg.mpr
      unfold physicalWeight
      simp only [Nat.cast_one, Nat.cast_zero, add_zero]
      apply one_div_lt_one_div_of_lt (by positivity)
      nlinarith
    exact mul_neg_of_pos_of_neg hx hw

/-- The exact physical-tail-block identity. The covariance correction is retained. -/
theorem physical_block_eq_uniform_sub_correction (p k : ℕ)
    (hp : 0 < p) (hk : 0 < k) :
    (∑ r ∈ Finset.range p,
      residueSquare (p : ℝ) r * physicalWeight ((k : ℝ) * (p : ℝ)) r) =
      (((p : ℝ) - 1) * (2 * (p : ℝ) - 1) / (6 * (p : ℝ) ^ 2)) *
        (1 / ((k : ℝ) * (p : ℝ)) -
          1 / ((k : ℝ) * (p : ℝ) + (p : ℝ))) - blockCorrection p k := by
  have hs : (Finset.range p).Nonempty :=
    Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hp)
  rw [weighted_sum_eq_mean_sub_covariance (Finset.range p) hs]
  simp only [Finset.card_range]
  rw [residueSquare_mean p hp, physicalWeight_sum _ (by positivity)]
  rfl

theorem physical_block_le_uniform (p k : ℕ) (hp : 0 < p) (hk : 0 < k) :
    (∑ r ∈ Finset.range p,
      residueSquare (p : ℝ) r * physicalWeight ((k : ℝ) * (p : ℝ)) r) ≤
      (((p : ℝ) - 1) * (2 * (p : ℝ) - 1) / (6 * (p : ℝ) ^ 2)) *
        (1 / ((k : ℝ) * (p : ℝ)) -
          1 / ((k : ℝ) * (p : ℝ) + (p : ℝ))) := by
  rw [physical_block_eq_uniform_sub_correction p k hp hk]
  exact sub_le_self _ (blockCorrection_nonneg p k hp hk)

theorem physical_block_lt_uniform (p k : ℕ) (hp : 1 < p) (hk : 0 < k) :
    (∑ r ∈ Finset.range p,
      residueSquare (p : ℝ) r * physicalWeight ((k : ℝ) * (p : ℝ)) r) <
      (((p : ℝ) - 1) * (2 * (p : ℝ) - 1) / (6 * (p : ℝ) ^ 2)) *
        (1 / ((k : ℝ) * (p : ℝ)) -
          1 / ((k : ℝ) * (p : ℝ) + (p : ℝ))) := by
  rw [physical_block_eq_uniform_sub_correction p k (by omega) hk]
  exact sub_lt_self _ (blockCorrection_pos p k hp hk)

end RiemannResearch.Analysis.NormCovariance
