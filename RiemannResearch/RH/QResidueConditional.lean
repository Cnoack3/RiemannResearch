/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoPolygammaResidues
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QResidueRefinement
import RiemannResearch.RH.QSquarefreeLatticePackets
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Complete Q residue conditioning and legal carry coordinates

Source: user-provided Squarefree_Profinite_Lattice_Q_Geometry_and_Research_Agenda_
2026-10-16, Sections 9--10 and Targets 1 and 5, and Q_Conditional_Carries_Energy_
Bounds_and_Research_Agenda_2026-10-18, Sections 3 and 5.

All progression weights retain the infinite physical tail. Residues are represented
by 1,...,L, so L represents residue zero. Conditional values are literal normalized
Q sums. No Haar replacement or trigamma convergence estimate is used. The exact
earlier-stage legality obstruction is proved; no bounded-energy RH provider follows.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QResidueConditional
open ZetaTwoProbability ZetaTwoHilbert ArithmeticCumulative

def carry (d p : ℕ) : QHilbert :=
  (p : ℝ) • qResidue (d * p) - qResidue d

theorem carry_sequence (d p n : ℕ) (hd : 0 < d) (hp : 0 < p) :
    qSequence (carry d p) n = ((n / d) % p : ℕ) := by
  change qSequenceLinear ((p : ℝ) • qResidue (d * p) - qResidue d) n = _
  simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  change (p : ℝ) * qSequence (qResidue (d * p)) n - qSequence (qResidue d) n = _
  simp only [qSequence_qResidue]
  rw [Nat.mul_comm d p, QResidueRefinement.residueFraction_refinement p d n hp hd]
  unfold residueFraction
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hp)
  field_simp [hpR]
  ring

theorem residuePowerWeight_refine (L p a : ℕ)
    (hL : 0 < L) (hp : 0 < p) (ha : 0 < a) :
    residuePowerWeight 0 L a =
      ∑ k : Fin p, residuePowerWeight 0 (L * p) (a + L * k.val) := by
  cases p with
  | zero => omega
  | succ p =>
    have hs := residuePowerWeight_summable 0
      (show (0 : ℝ) < L by exact_mod_cast hL)
      (show (0 : ℝ) < a by exact_mod_cast ha)
    calc
      residuePowerWeight 0 L a =
          ∑ k : Fin (p + 1), ∑' j : ℕ,
            1 / (zetaTwo * ((a : ℝ) +
              ((k.val + (p + 1) * j : ℕ) : ℝ) * (L : ℝ)) ^ (2 : ℕ)) :=
        Nat.sumByResidueClasses hs (p + 1)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        apply tsum_congr
        intro j
        push_cast
        congr 3
        ring

def fiberSum (L a : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑' j : ℕ, positiveQWeight (a + L * j) * f (a + L * j)

theorem fiber_terms_summable (L a : ℕ) (hL : 0 < L) (ha : 0 < a)
    (f : ℕ → ℝ) {C : ℝ} (hf : ∀ n, |f n| ≤ C) :
    Summable (fun j : ℕ => positiveQWeight (a + L * j) * f (a + L * j)) := by
  have hw : Summable (fun j : ℕ => positiveQWeight (a + L * j)) := by
    convert residuePowerWeight_summable 0
      (show (0 : ℝ) < L by exact_mod_cast hL)
      (show (0 : ℝ) < a by exact_mod_cast ha) using 1
    simp only [positiveQWeight, Nat.cast_add, Nat.cast_mul, Nat.zero_add, mul_comm]
  apply (hw.mul_right C).of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (positiveQWeight_nonneg _)]
  exact mul_le_mul_of_nonneg_left (hf _) (positiveQWeight_nonneg _)

theorem fiberSum_refine (L p a : ℕ)
    (hL : 0 < L) (hp : 0 < p) (ha : 0 < a)
    (f : ℕ → ℝ) {C : ℝ} (hf : ∀ n, |f n| ≤ C) :
    fiberSum L a f = ∑ k : Fin p, fiberSum (L * p) (a + L * k.val) f := by
  cases p with
  | zero => omega
  | succ p =>
    calc
      fiberSum L a f =
          ∑ k : Fin (p + 1), ∑' j : ℕ,
            positiveQWeight (a + L * (k.val + (p + 1) * j)) *
              f (a + L * (k.val + (p + 1) * j)) :=
        Nat.sumByResidueClasses (fiber_terms_summable L a hL ha f hf) (p + 1)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        apply tsum_congr
        intro j
        rw [show a + L * (k.val + (p + 1) * j) =
          a + L * k.val + L * (p + 1) * j by ring]

theorem fiberSum_of_periodic (L a : ℕ)
    (f : ℕ → ℝ) (hf : ∀ n, f (n + L) = f n) :
    fiberSum L a f = residuePowerWeight 0 L a * f a := by
  unfold fiberSum
  simp_rw [Pareto.periodic_add_mul L f hf]
  rw [tsum_mul_right]
  congr 1
  unfold residuePowerWeight
  apply tsum_congr
  intro j
  simp only [positiveQWeight, Nat.cast_add, Nat.cast_mul, Nat.zero_add, mul_comm]

def conditionalValue (L a : ℕ) (f : ℕ → ℝ) : ℝ :=
  fiberSum L a f / residuePowerWeight 0 L a

theorem conditionalValue_finite (L p a : ℕ)
    (hL : 0 < L) (hp : 0 < p) (ha : 0 < a)
    (f : ℕ → ℝ) {C : ℝ} (hf : ∀ n, |f n| ≤ C)
    (hperiod : ∀ n, f (n + L * p) = f n) :
    conditionalValue L a f =
      (∑ k : Fin p, residuePowerWeight 0 (L * p) (a + L * k.val) *
        f (a + L * k.val)) / residuePowerWeight 0 L a := by
  unfold conditionalValue
  rw [fiberSum_refine L p a hL hp ha f hf]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simpa only [Nat.cast_add, Nat.cast_mul] using
    fiberSum_of_periodic (L * p) (a + L * k.val) f hperiod


/-- Positive representatives 1,...,L retain the zero residue as L. -/
def alpha (L p a : ℕ) (k : Fin p) : ℝ :=
  residuePowerWeight 0 (L * p) (a + L * k.val) / residuePowerWeight 0 L a

theorem alpha_pos (L p a : ℕ) (hL : 0 < L) (hp : 0 < p) (ha : 0 < a)
    (k : Fin p) : 0 < alpha L p a k := by
  apply div_pos
  · apply residuePowerWeight_pos
    · exact_mod_cast Nat.mul_pos hL hp
    · exact_mod_cast (show 0 < a + L * k.val by omega)
  · exact residuePowerWeight_pos 0 (by exact_mod_cast hL) (by exact_mod_cast ha)

theorem alpha_sum (L p a : ℕ) (hL : 0 < L) (hp : 0 < p) (ha : 0 < a) :
    (∑ k : Fin p, alpha L p a k) = 1 := by
  simp only [alpha, ← Finset.sum_div]
  rw [← residuePowerWeight_refine L p a hL hp ha]
  exact div_self (ne_of_gt (residuePowerWeight_pos 0
    (by exact_mod_cast hL) (by exact_mod_cast ha)))

theorem conditionalValue_eq_alpha (L p a : ℕ)
    (hL : 0 < L) (hp : 0 < p) (ha : 0 < a)
    (f : ℕ → ℝ) {C : ℝ} (hf : ∀ n, |f n| ≤ C)
    (hperiod : ∀ n, f (n + L * p) = f n) :
    conditionalValue L a f = ∑ k : Fin p, alpha L p a k * f (a + L * k.val) := by
  rw [conditionalValue_finite L p a hL hp ha f hf hperiod, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  unfold alpha
  ring

private theorem residue_bound (d n : ℕ) : |residueFraction d n| ≤ 1 := by
  by_cases hd : d = 0
  · simp [hd, residueFraction]
  have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  unfold residueFraction
  rw [abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ hdR).mpr
  simpa using (show ((n % d : ℕ) : ℝ) ≤ d by
    exact_mod_cast (Nat.mod_lt n (Nat.pos_of_ne_zero hd)).le)

/-- Simultaneous formula for every new conductor, at the old modulus L. -/
theorem conditionalValue_new_residue (L p e a : ℕ)
    (hL : 0 < L) (hp : 0 < p) (ha : 0 < a) (heL : e ∣ L) :
    conditionalValue L a (residueFraction (e * p)) =
      ∑ k : Fin p, alpha L p a k * residueFraction (e * p) (a + L * k.val) := by
  apply conditionalValue_eq_alpha L p a hL hp ha _ (residue_bound _)
  intro n
  have hd : e * p ∣ L * p := Nat.mul_dvd_mul heL (dvd_refl p)
  simp [residueFraction, Nat.add_mod, Nat.mod_eq_zero_of_dvd hd]

theorem residuePowerWeight_zeroClass (L : ℕ) :
    residuePowerWeight 0 L L = 1 / (L : ℝ)^2 := by
  have hs : (∑' j : ℕ, 1 / (zetaTwo * ((j : ℝ) + 1)^2)) = 1 := by
    have h := positiveQWeight_tsum
    rw [positiveQWeight_summable.tsum_eq_zero_add] at h
    simpa [positiveQWeight, Nat.cast_add, Nat.cast_one] using h
  have ht (j : ℕ) :
      1 / (zetaTwo * ((L : ℝ) + (j : ℝ) * L)^2) =
        (1 / (L : ℝ)^2) * (1 / (zetaTwo * ((j : ℝ) + 1)^2)) := by
    rw [show (L : ℝ) + (j : ℝ) * L = (L : ℝ) * ((j : ℝ) + 1) by ring, mul_pow]
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  simp only [residuePowerWeight, Nat.zero_add, ht, tsum_mul_left, hs, mul_one]

/-- Conditional on a positive multiple of L, the quotient has exactly law Q. -/
theorem conditionalValue_multiples (L : ℕ) (hL : 0 < L) (f : ℕ → ℝ) :
    conditionalValue L L f = inversePowerMean 0 (fun n => f (L * n)) := by
  unfold conditionalValue fiberSum
  rw [residuePowerWeight_zeroClass L, ← tsum_div_const]
  unfold inversePowerMean
  apply tsum_congr
  intro j
  rw [show L + L * j = L * (j + 1) by ring]
  unfold positiveQWeight
  push_cast
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
  field_simp [hLR]


/-- The old divisor stage contains this legal carry at the enlarged period. -/
theorem carry_mem_divisorStage (L d p : ℕ) (hdL : d ∣ L) :
    carry d p ∈ QSquarefreeLatticePackets.divisorStage (L * p) := by
  apply (QSquarefreeLatticePackets.divisorStage (L * p)).sub_mem
  · exact (QSquarefreeLatticePackets.divisorStage (L * p)).smul_mem _
      (Submodule.subset_span ⟨d * p, Nat.mul_dvd_mul hdL (dvd_refl p), rfl⟩)
  · exact Submodule.subset_span ⟨d, hdL.trans (dvd_mul_right L p), rfl⟩

theorem residueFraction_scale (L p n : ℕ) (hL : 0 < L) :
    residueFraction (L * p) (L * n) = residueFraction p n := by
  unfold residueFraction
  rw [Nat.mul_mod_mul_left]
  push_cast
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
  field_simp [hLR]

/-- The zero fiber is retained and its conditional value is the Q mean. -/
theorem conditionalValue_zero_residue (L p : ℕ) (hL : 0 < L) :
    conditionalValue L L (residueFraction (L * p)) =
      inversePowerMean 0 (residueFraction p) := by
  rw [conditionalValue_multiples L hL]
  unfold inversePowerMean
  apply tsum_congr
  intro j
  dsimp only
  rw [residueFraction_scale L p (j + 1) hL]

theorem residue_mean_pos (p : ℕ) (hp : 1 < p) :
    0 < inversePowerMean 0 (residueFraction p) := by
  unfold inversePowerMean
  refine (inversePowerMean_summable_of_bounded 0 _ (residue_bound p)).tsum_pos
    (fun n => ?_) 0 ?_
  · have hZ := zetaTwo_pos
    unfold residueFraction
    positivity
  · simp only [Nat.zero_add, residueFraction, Nat.mod_eq_of_lt hp, Nat.cast_one,
      one_pow, mul_one]
    have hZ := zetaTwo_pos
    have hpR : (0 : ℝ) < p := by exact_mod_cast (lt_trans Nat.zero_lt_one hp)
    positivity

theorem divisorStage_zero (L : ℕ) (f : QHilbert)
    (hf : f ∈ QSquarefreeLatticePackets.divisorStage L) :
    qSequence f L = 0 := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨d, hd, rfl⟩ := hf
      simp [qSequence_qResidue, residueFraction, Nat.mod_eq_zero_of_dvd hd]
  | zero =>
      change qSequenceLinear 0 L = 0
      simp
  | add f g hf hg ihf ihg =>
      change qSequenceLinear (f + g) L = 0
      simp only [map_add, Pi.add_apply]
      change qSequence f L + qSequence g L = 0
      rw [ihf, ihg, zero_add]
  | smul a f hf ih =>
      change qSequenceLinear (a • f) L = 0
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      change a * qSequence f L = 0
      rw [ih, mul_zero]

/-- Exact obstruction to preserving the earlier legal stage under conditioning. -/
theorem conditionalValue_not_old_legal (L p : ℕ) (hL : 0 < L) (hp : 1 < p)
    (f : QHilbert) (hf : f ∈ QSquarefreeLatticePackets.divisorStage L) :
    qSequence f L < conditionalValue L L (residueFraction (L * p)) := by
  rw [divisorStage_zero L f hf, conditionalValue_zero_residue L p hL]
  exact residue_mean_pos p hp


/-- Conditional means preserve finite signed scalar differences. -/
theorem conditionalValue_smul_sub (L a : ℕ) (hL : 0 < L) (ha : 0 < a)
    (t : ℝ) (f g : ℕ → ℝ) {C D : ℝ}
    (hf : ∀ n, |f n| ≤ C) (hg : ∀ n, |g n| ≤ D) :
    conditionalValue L a (fun n => t * f n - g n) =
      t * conditionalValue L a f - conditionalValue L a g := by
  have hs := fiber_terms_summable L a hL ha f hf
  have ht := fiber_terms_summable L a hL ha g hg
  have he : fiberSum L a (fun n => t * f n - g n) =
      t * fiberSum L a f - fiberSum L a g := by
    unfold fiberSum
    have hterm (j : ℕ) :
        positiveQWeight (a + L * j) * (t * f (a + L * j) - g (a + L * j)) =
          t * (positiveQWeight (a + L * j) * f (a + L * j)) -
            positiveQWeight (a + L * j) * g (a + L * j) := by ring
    simp_rw [hterm]
    rw [(hs.mul_left t).tsum_sub ht, tsum_mul_left]
  unfold conditionalValue
  rw [he]
  ring

/-- Conditioning an old-period observable returns its original value. -/
theorem conditionalValue_of_periodic (L a : ℕ) (hL : 0 < L) (ha : 0 < a)
    (f : ℕ → ℝ) (hf : ∀ n, f (n + L) = f n) :
    conditionalValue L a f = f a := by
  unfold conditionalValue
  rw [fiberSum_of_periodic L a f hf]
  have hw : residuePowerWeight 0 L a ≠ 0 :=
    ne_of_gt (residuePowerWeight_pos 0 (by exact_mod_cast hL) (by exact_mod_cast ha))
  field_simp [hw]

/-- Exact finite conditional mean of the integer one-step carry, at the old modulus. -/
theorem conditionalValue_step_carry (L p e a : ℕ)
    (hL : 0 < L) (hp : 0 < p) (ha : 0 < a) (heL : e ∣ L) :
    conditionalValue L a (qSequence (carry e p)) =
      (p : ℝ) * (∑ k : Fin p, alpha L p a k *
        residueFraction (e * p) (a + L * k.val)) - residueFraction e a := by
  have he : qSequence (carry e p) =
      fun n => (p : ℝ) * residueFraction (e * p) n - residueFraction e n := by
    funext n
    change qSequenceLinear ((p : ℝ) • qResidue (e * p) - qResidue e) n = _
    simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    change (p : ℝ) * qSequence (qResidue (e * p)) n -
      qSequence (qResidue e) n = _
    simp only [qSequence_qResidue]
  rw [he, conditionalValue_smul_sub L a hL ha _ _ _ (residue_bound _) (residue_bound _)]
  rw [conditionalValue_new_residue L p e a hL hp ha heL]
  rw [conditionalValue_of_periodic L a hL ha _ (by
    intro n
    simp [residueFraction, Nat.add_mod, Nat.mod_eq_zero_of_dvd heL])]

/-- The unnormalized conditional sum also has an exact finite formula. -/
theorem fiberSum_finite (L p a : ℕ)
    (hL : 0 < L) (hp : 0 < p) (ha : 0 < a)
    (f : ℕ → ℝ) {C : ℝ} (hf : ∀ n, |f n| ≤ C)
    (hperiod : ∀ n, f (n + L * p) = f n) :
    fiberSum L a f =
      ∑ k : Fin p, residuePowerWeight 0 (L * p) (a + L * k.val) *
        f (a + L * k.val) := by
  rw [fiberSum_refine L p a hL hp ha f hf]
  apply Finset.sum_congr rfl
  intro k _
  simpa only [Nat.cast_add, Nat.cast_mul] using
    fiberSum_of_periodic (L * p) (a + L * k.val) f hperiod

private theorem weighted_covariance {ι : Type*} [Fintype ι]
    (w x y : ι → ℝ) (W m n : ℝ)
    (hw : (∑ i, w i) = W) (hx : (∑ i, w i * x i) = W * m)
    (hy : (∑ i, w i * y i) = W * n) :
    (∑ i, w i * (x i * y i)) =
      W * m * n + ∑ i, w i * (x i - m) * (y i - n) := by
  have he : (∑ i, w i * (x i - m) * (y i - n)) =
      (∑ i, w i * (x i * y i)) - n * (∑ i, w i * x i) -
        m * (∑ i, w i * y i) + (m * n) * (∑ i, w i) := by
    calc
      _ = ∑ i, (w i * (x i * y i) - n * (w i * x i) -
          m * (w i * y i) + (m * n) * w i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum]
  rw [he, hw, hx, hy]
  ring

/-- Exact coarse/innovation split on each fiber, including all signed terms. -/
theorem fiberSum_conditional_covariance (L p a : ℕ)
    (hL : 0 < L) (hp : 0 < p) (ha : 0 < a)
    (f g : ℕ → ℝ) {C D : ℝ} (hf : ∀ n, |f n| ≤ C) (hg : ∀ n, |g n| ≤ D)
    (hpf : ∀ n, f (n + L * p) = f n) (hpg : ∀ n, g (n + L * p) = g n) :
    fiberSum L a (fun n => f n * g n) =
      residuePowerWeight 0 L a * conditionalValue L a f * conditionalValue L a g +
      ∑ k : Fin p, residuePowerWeight 0 (L * p) (a + L * k.val) *
        (f (a + L * k.val) - conditionalValue L a f) *
        (g (a + L * k.val) - conditionalValue L a g) := by
  have hw : residuePowerWeight 0 L a ≠ 0 :=
    ne_of_gt (residuePowerWeight_pos 0 (by exact_mod_cast hL) (by exact_mod_cast ha))
  rw [fiberSum_finite L p a hL hp ha _ (Pareto.bounded_product hf hg)
    (by intro n; rw [hpf, hpg])]
  apply weighted_covariance
  · exact (residuePowerWeight_refine L p a hL hp ha).symm
  · rw [conditionalValue_finite L p a hL hp ha f hf hpf]
    field_simp [hw]
  · rw [conditionalValue_finite L p a hL hp ha g hg hpg]
    field_simp [hw]

/-- The complete physical Q mean is the sum of all coarse fibers. -/
theorem inversePowerMean_eq_sum_fiber (L : ℕ) (hL : 0 < L)
    (f : ℕ → ℝ) {C : ℝ} (hf : ∀ n, |f n| ≤ C) :
    inversePowerMean 0 f = ∑ a : Fin L, fiberSum L (a.val + 1) f := by
  cases L with
  | zero => omega
  | succ L =>
    let v : ℕ → ℝ := fun k => f (k + 1) / (zetaTwo * ((k + 1 : ℕ) : ℝ)^2)
    have hs : Summable v := inversePowerMean_summable_of_bounded 0 f hf
    calc
      inversePowerMean 0 f =
        ∑ a : Fin (L + 1), ∑' j : ℕ, v (a.val + (L + 1) * j) :=
          Nat.sumByResidueClasses hs (L + 1)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a _
        apply tsum_congr
        intro j
        unfold v positiveQWeight
        rw [show a.val + (L + 1) * j + 1 = a.val + 1 + (L + 1) * j by omega]
        ring

/-- Complete Q Gram decomposition into conditional means and innovations. -/
theorem periodic_conditional_gram (L p : ℕ) (hL : 0 < L) (hp : 0 < p)
    (f g : ℕ → ℝ) {C D : ℝ} (hf : ∀ n, |f n| ≤ C) (hg : ∀ n, |g n| ≤ D)
    (hpf : ∀ n, f (n + L * p) = f n) (hpg : ∀ n, g (n + L * p) = g n) :
    inversePowerMean 0 (fun n => f n * g n) =
      ∑ a : Fin L, (residuePowerWeight 0 L (a.val + 1) *
        conditionalValue L (a.val + 1) f * conditionalValue L (a.val + 1) g +
        ∑ k : Fin p, residuePowerWeight 0 (L * p) (a.val + 1 + L * k.val) *
          (f (a.val + 1 + L * k.val) - conditionalValue L (a.val + 1) f) *
          (g (a.val + 1 + L * k.val) - conditionalValue L (a.val + 1) g)) := by
  rw [inversePowerMean_eq_sum_fiber L hL _ (Pareto.bounded_product hf hg)]
  apply Finset.sum_congr rfl
  intro a _
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_mul] using
    fiberSum_conditional_covariance L p (a.val + 1) hL hp (Nat.succ_pos a.val)
      f g hf hg hpf hpg


/-- Quantitative leakage against every old legal vector, retaining residue zero. -/
theorem conditional_leakage_floor (L p : ℕ) (hL : 0 < L)
    (f : QHilbert) (hf : f ∈ QSquarefreeLatticePackets.divisorStage L) :
    (inversePowerMean 0 (residueFraction p))^2 / (L : ℝ)^2 ≤
      ∑ a : Fin L, residuePowerWeight 0 L (a.val + 1) *
        (conditionalValue L (a.val + 1) (residueFraction (L * p)) -
          qSequence f (a.val + 1))^2 := by
  let last : Fin L := ⟨L - 1, Nat.sub_lt hL Nat.zero_lt_one⟩
  have he : last.val + 1 = L := by dsimp [last]; omega
  have heR : (last.val : ℝ) + 1 = (L : ℝ) := by exact_mod_cast he
  have hs := Finset.single_le_sum
    (s := Finset.univ) (a := last)
    (f := fun a : Fin L => residuePowerWeight 0 L (a.val + 1) *
      (conditionalValue L (a.val + 1) (residueFraction (L * p)) -
        qSequence f (a.val + 1))^2)
    (fun a _ => mul_nonneg (le_of_lt (residuePowerWeight_pos 0
      (by exact_mod_cast hL) (by positivity))) (sq_nonneg _))
    (Finset.mem_univ last)
  simpa only [he, Nat.cast_add, Nat.cast_one, heR, residuePowerWeight_zeroClass,
    conditionalValue_zero_residue L p hL, divisorStage_zero L f hf, sub_zero,
    div_eq_mul_inv, one_mul, mul_one, mul_comm] using hs


end RiemannResearch.RH.QResidueConditional
