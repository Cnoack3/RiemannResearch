import RiemannResearch.Analysis.FirstMomentTails
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Summable dyadic tails: the complete regularity upgrade

Source: user-provided RH_Two_Seed_Tail_Rigidity_Continuation_20260911,
Section 2 (statement). This proof uses discrete dyadic block averages in place
of the proposed Fourier/Sobolev argument.

For c(n)=n*A(n), summability of A makes block averages tend to zero.
Finite difference energy makes the differences of c square summable.
Exact dyadic scaling and disjoint blocks then give
c(n)^2 <= (1/2) * sum_{j >= 2*n} (c(j+1)-c(j))^2.
Decay of this tail and invariance along a dyadic orbit force c(n)=0.
The resulting weighted square-summability theorem discharges the coefficient
form of the global H1 upgrade, without a Fourier-regularity hypothesis.
-/
open scoped BigOperators
namespace RiemannResearch.Analysis.DyadicBlockRigidity
noncomputable section

def blockAverage (c : ℕ → ℝ) (n K : ℕ) : ℝ :=
  ((2 : ℝ)^K)⁻¹ * ∑ r ∈ Finset.Ico (2^K*n) (2^K*(n+1)), c r

lemma sum_range_double (f : ℕ → ℝ) (N : ℕ) :
    (∑ r ∈ Finset.range (2*N), f r) =
      ∑ r ∈ Finset.range N, (f (2*r) + f (2*r+1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hn : 2 * (N+1) = (2*N+1)+1 := by omega
    rw [hn, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ih]
    ring

lemma sum_Ico_double (f : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    (∑ r ∈ Finset.Ico (2*a) (2*b), f r) =
      ∑ r ∈ Finset.Ico a b, (f (2*r) + f (2*r+1)) := by
  rw [Finset.sum_Ico_eq_sub _ (by omega),
    Finset.sum_Ico_eq_sub _ hab, sum_range_double, sum_range_double]

theorem blockAverage_succ_sub (c : ℕ → ℝ)
    (hc : ∀ r, c (2*r) = c r) (n K : ℕ) :
    blockAverage c n (K+1) - blockAverage c n K =
      ((2:ℝ)^(K+1))⁻¹ *
        ∑ r ∈ Finset.Ico (2^K*n) (2^K*(n+1)), (c (2*r+1)-c (2*r)) := by
  have ha : 2^(K+1)*n = 2*(2^K*n) := by rw [pow_succ]; ring
  have hb : 2^(K+1)*(n+1) = 2*(2^K*(n+1)) := by rw [pow_succ]; ring
  unfold blockAverage
  rw [ha, hb, sum_Ico_double _ _ _ (Nat.mul_le_mul_left _ (Nat.le_succ n))]
  simp_rw [hc]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, pow_succ]
  have hp : (2:ℝ)^K ≠ 0 := by positivity
  field_simp
  ring

theorem blockAverage_sub_eq_sum (c : ℕ → ℝ)
    (hc : ∀ r, c (2*r) = c r) (n K : ℕ) :
    blockAverage c n K - c n =
      ∑ k ∈ Finset.range K, ((2:ℝ)^(k+1))⁻¹ *
        ∑ r ∈ Finset.Ico (2^k*n) (2^k*(n+1)), (c (2*r+1)-c (2*r)) := by
  induction K with
  | zero => simp [blockAverage]
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have hs := blockAverage_succ_sub c hc n K
    linarith

end
end RiemannResearch.Analysis.DyadicBlockRigidity

namespace RiemannResearch.Analysis.DyadicBlockRigidity
noncomputable section
-- Append within namespace RiemannResearch.Analysis.DyadicBlockRigidity.

lemma dyadic_weight_mass (K : ℕ) :
    (∑ k ∈ Finset.range K, (2:ℝ)^k * (((2:ℝ)^(k+1))⁻¹)^2) =
      (1 - ((2:ℝ)^K)⁻¹) / 2 := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    rw [pow_succ]
    have hp : (2:ℝ)^K ≠ 0 := by positivity
    field_simp
    ring

theorem blockAverage_sub_sq_le_block_energy (c : ℕ → ℝ)
    (hc : ∀ r, c (2*r) = c r) (n K : ℕ) :
    (blockAverage c n K - c n)^2 ≤
      (1/2:ℝ) * ∑ k ∈ Finset.range K,
        ∑ r ∈ Finset.Ico (2^k*n) (2^k*(n+1)), (c (2*r+1)-c (2*r))^2 := by
  classical
  let s : Finset (Σ _ : ℕ, ℕ) := (Finset.range K).sigma
    (fun k => Finset.Ico (2^k*n) (2^k*(n+1)))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun p => ((2:ℝ)^(p.1+1))⁻¹)
    (fun p => c (2*p.2+1)-c (2*p.2))
  have hmass :
      (∑ p ∈ s, (((2:ℝ)^(p.1+1))⁻¹)^2) =
        (1 - ((2:ℝ)^K)⁻¹) / 2 := by
    dsimp [s]
    rw [Finset.sum_sigma]
    convert dyadic_weight_mass K using 1
    apply Finset.sum_congr rfl
    intro k hk
    simp [Nat.mul_add, nsmul_eq_mul]
  have hmass_le : (1 - ((2:ℝ)^K)⁻¹) / 2 ≤ (1/2:ℝ) := by
    have hp : 0 ≤ ((2:ℝ)^K)⁻¹ := by positivity
    linarith
  rw [hmass] at hcs
  have henergy_nonneg : 0 ≤ ∑ p ∈ s, (c (2*p.2+1)-c (2*p.2))^2 := by
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hbound := le_trans hcs (mul_le_mul_of_nonneg_right hmass_le henergy_nonneg)
  dsimp [s] at hbound
  simp only [Finset.sum_sigma, ← Finset.mul_sum] at hbound
  rw [blockAverage_sub_eq_sum c hc]
  exact hbound

end
end RiemannResearch.Analysis.DyadicBlockRigidity



namespace RiemannResearch.Analysis.DyadicBlockRigidity
open Filter
theorem blockAverage_weighted_bound {A : ℕ → ℝ} (hA : Summable A) (n K : ℕ) :
    |blockAverage (fun j => (j : ℝ)*A j) n K| ≤
      ((n : ℝ)+1)*(∑' j, |A (j+2^K*n)|) := by
  let s := Finset.Ico (2^K*n) (2^K*(n+1))
  have hinv : 0 ≤ ((2 : ℝ)^K)⁻¹ := by positivity
  have hp : 0 < (2 : ℝ)^K := by positivity
  have htail : (∑ r ∈ s, |A r|) ≤ ∑' j, |A (j+2^K*n)| := by
    dsimp [s]
    rw [Finset.sum_Ico_eq_sum_range]
    have hs := (summable_nat_add_iff (2^K*n)).mpr hA.abs
    simpa only [Nat.add_comm (2^K*n)] using
      hs.sum_le_tsum (Finset.range (2^K*(n+1)-2^K*n))
        (fun j _ => abs_nonneg (A (j+2^K*n)))
  calc
    _ = ((2 : ℝ)^K)⁻¹ * |∑ r ∈ s, (r : ℝ)*A r| := by
      rw [blockAverage, abs_mul, abs_of_nonneg hinv]
    _ ≤ ((2 : ℝ)^K)⁻¹ * ∑ r ∈ s, |(r : ℝ)*A r| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hinv
    _ = ∑ r ∈ s, ((2 : ℝ)^K)⁻¹ * |(r : ℝ)*A r| := by rw [Finset.mul_sum]
    _ ≤ ∑ r ∈ s, ((n : ℝ)+1)*|A r| := by
      apply Finset.sum_le_sum
      intro r hr
      have hr' : (r : ℝ) ≤ (2 : ℝ)^K*((n : ℝ)+1) := by
        exact_mod_cast (Finset.mem_Ico.mp hr).2.le
      have hb : ((2 : ℝ)^K)⁻¹ * (r : ℝ) ≤ (n : ℝ)+1 := by
        have hx := mul_le_mul_of_nonneg_left hr' hinv
        simpa only [← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul] using hx
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg r), ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    _ = ((n : ℝ)+1)*∑ r ∈ s, |A r| := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left htail (by positivity)

theorem blockAverage_weighted_tendsto_zero {A : ℕ → ℝ} (hA : Summable A)
    {n : ℕ} (hn : 0 < n) :
    Tendsto (blockAverage (fun j => (j : ℝ)*A j) n) atTop (nhds 0) := by
  have hpow : Tendsto (fun K : ℕ => 2^K) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hidx : Tendsto (fun K : ℕ => 2^K*n) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact ((tendsto_atTop.1 hpow) b).mono fun K hK => by
      have : 1 ≤ n := hn
      nlinarith
  have ht := (RiemannResearch.Analysis.rawTail_tendsto_zero hA.abs).comp hidx
  have hlim : Tendsto (fun K : ℕ => ((n : ℝ)+1)*(∑' j, |A (j+2^K*n)|))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (n : ℝ)+1) atTop
        (nhds ((n : ℝ)+1))).mul ht)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using
    squeeze_zero (fun K => abs_nonneg _)
      (fun K => blockAverage_weighted_bound hA n K) hlim
end RiemannResearch.Analysis.DyadicBlockRigidity


namespace RiemannResearch.Analysis.DyadicBlockRigidity
theorem square_summable_of_summable {A : ℕ → ℝ} (hA : Summable A) :
    Summable (fun n => (A n)^2) := by
  apply (hA.abs.mul_left (∑' j, |A j|)).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hn := hA.abs.le_tsum n (fun j _ => abs_nonneg (A j))
  have ht := mul_le_mul_of_nonneg_right hn (abs_nonneg (A n))
  nlinarith [sq_abs (A n)]

theorem weighted_difference_summable {A : ℕ → ℝ} (hA : Summable A)
    (hE : Summable (fun n : ℕ =>
      (n : ℝ)*((n : ℝ)+1)*(A n-A (n+1))^2)) :
    Summable (fun n : ℕ => (((n : ℝ)+1)*A (n+1)-(n : ℝ)*A n)^2) := by
  have hsq : Summable (fun n => A (n+1)^2) :=
    (summable_nat_add_iff 1).mpr (square_summable_of_summable hA)
  apply ((hE.mul_left 2).add (hsq.mul_left 2)).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [sq_nonneg ((n : ℝ)*(A n-A (n+1))+A (n+1)),
    mul_nonneg hn (sq_nonneg (A n-A (n+1)))]
end RiemannResearch.Analysis.DyadicBlockRigidity
namespace RiemannResearch.Analysis.DyadicBlockRigidity
noncomputable section
-- Append within namespace RiemannResearch.Analysis.DyadicBlockRigidity.

lemma dyadic_blocks_ordered {n k l r s : ℕ} (hn : 1 ≤ n) (hkl : k < l)
    (hr : r ∈ Finset.Ico (2^k*n) (2^k*(n+1)))
    (hs : s ∈ Finset.Ico (2^l*n) (2^l*(n+1))) : r < s := by
  have hr' := (Finset.mem_Ico.mp hr).2
  have hs' := (Finset.mem_Ico.mp hs).1
  have hp : 2^(k+1) ≤ 2^l := Nat.pow_le_pow_right (by omega) (by omega)
  have hstep : 2^k*(n+1) ≤ 2^(k+1)*n := by
    rw [pow_succ]
    nlinarith
  have hmul := Nat.mul_le_mul_right n hp
  omega

theorem dyadic_block_energy_le_Ico (d : ℕ → ℝ) (n K : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.range K,
      ∑ r ∈ Finset.Ico (2^k*n) (2^k*(n+1)), (d (2*r))^2) ≤
    ∑ j ∈ Finset.Ico (2*n) (2^(K+1)*(n+1)), (d j)^2 := by
  classical
  let s : Finset (Σ _ : ℕ, ℕ) := (Finset.range K).sigma
    (fun k => Finset.Ico (2^k*n) (2^k*(n+1)))
  have hinj : Set.InjOn (fun p : Σ _ : ℕ, ℕ => 2*p.2) (↑s : Set (Σ _ : ℕ, ℕ)) := by
    intro p hp q hq heq
    have hp' := Finset.mem_sigma.mp hp
    have hq' := Finset.mem_sigma.mp hq
    have he : p.2 = q.2 := by
      exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) heq
    have hk : p.1 = q.1 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hh := dyadic_blocks_ordered hn hlt hp'.2 hq'.2
        omega
      · have hh := dyadic_blocks_ordered hn hgt hq'.2 hp'.2
        omega
    cases p with
    | mk pk pr =>
      cases q with
      | mk qk qr =>
        simp only at he hk
        subst qk
        subst qr
        rfl
  have hsub : s.image (fun p => 2*p.2) ⊆ Finset.Ico (2*n) (2^(K+1)*(n+1)) := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨p, hp, rfl⟩
    have hp' := Finset.mem_sigma.mp hp
    have hk : p.1 < K := Finset.mem_range.mp hp'.1
    have hr := Finset.mem_Ico.mp hp'.2
    have hpow : 1 ≤ 2^p.1 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
    have hpowK : 2^p.1 ≤ 2^K := Nat.pow_le_pow_right (by omega) (by omega)
    have hlo : n ≤ p.2 := by nlinarith [hr.1]
    have hhi : p.2 < 2^K*(n+1) := lt_of_lt_of_le hr.2 (Nat.mul_le_mul_right (n+1) hpowK)
    apply Finset.mem_Ico.mpr
    constructor
    · omega
    · rw [pow_succ]
      nlinarith
  calc
    _ = ∑ p ∈ s, (d (2*p.2))^2 := by simp [s, Finset.sum_sigma]
    _ = ∑ j ∈ s.image (fun p => 2*p.2), (d j)^2 := by rw [Finset.sum_image hinj]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)

theorem blockAverage_sub_sq_le_Ico_energy (c : ℕ → ℝ)
    (hc : ∀ r, c (2*r) = c r) (n K : ℕ) (hn : 1 ≤ n) :
    (blockAverage c n K - c n)^2 ≤
      (1/2:ℝ) * ∑ j ∈ Finset.Ico (2*n) (2^(K+1)*(n+1)), (c (j+1)-c j)^2 := by
  exact (blockAverage_sub_sq_le_block_energy c hc n K).trans
    (mul_le_mul_of_nonneg_left
      (dyadic_block_energy_le_Ico (fun j => c (j+1)-c j) n K hn) (by norm_num))

end
end RiemannResearch.Analysis.DyadicBlockRigidity

namespace RiemannResearch.Analysis.DyadicBlockRigidity
open Filter
theorem blockAverage_sub_sq_le_tail_energy (c : ℕ → ℝ)
    (hc : ∀ r, c (2*r) = c r)
    (hd : Summable (fun j => (c (j+1)-c j)^2))
    {n : ℕ} (hn : 0 < n) (K : ℕ) :
    (blockAverage c n K-c n)^2 ≤
      (1/2 : ℝ)*(∑' j, (c (j+2*n+1)-c (j+2*n))^2) := by
  apply (blockAverage_sub_sq_le_Ico_energy c hc n K hn).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [Finset.sum_Ico_eq_sum_range]
  have hs : Summable (fun j => (c (j+2*n+1)-c (j+2*n))^2) :=
    (summable_nat_add_iff (2*n)).mpr hd
  simpa only [Nat.add_comm (2*n)] using
    hs.sum_le_tsum (Finset.range (2^(K+1)*(n+1)-2*n))
      (fun j _ => sq_nonneg _)

theorem square_le_tail_energy_of_average_decay (c : ℕ → ℝ)
    (hc : ∀ r, c (2*r) = c r)
    (hd : Summable (fun j => (c (j+1)-c j)^2))
    {n : ℕ} (hn : 0 < n)
    (hav : Tendsto (blockAverage c n) atTop (nhds 0)) :
    (c n)^2 ≤ (1/2 : ℝ)*(∑' j, (c (j+2*n+1)-c (j+2*n))^2) := by
  have ht := (hav.sub_const (c n)).pow 2
  have hb := le_of_tendsto ht
    (Filter.Eventually.of_forall (fun K => blockAverage_sub_sq_le_tail_energy c hc hd hn K))
  simpa only [zero_sub, neg_sq] using hb

theorem eq_zero_of_dyadic_of_average_decay (c : ℕ → ℝ)
    (hc : ∀ r, c (2*r) = c r)
    (hd : Summable (fun j => (c (j+1)-c j)^2))
    (hav : ∀ n, 0 < n → Tendsto (blockAverage c n) atTop (nhds 0))
    {n : ℕ} (hn : 0 < n) : c n = 0 := by
  have horbit : ∀ k : ℕ, c (2^k*n) = c n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2^(k+1)*n = 2*(2^k*n) by rw [pow_succ]; ring, hc, ih]
  have hpow : Tendsto (fun K : ℕ => 2^K) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hidx : Tendsto (fun K : ℕ => 2*(2^K*n)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact ((tendsto_atTop.1 hpow) b).mono fun K hK => by
      have : 1 ≤ n := hn
      nlinarith
  have ht := (RiemannResearch.Analysis.rawTail_tendsto_zero hd).comp hidx
  have hlim : Tendsto (fun K : ℕ => (1/2 : ℝ)*
      (∑' j, (c (j+2*(2^K*n)+1)-c (j+2*(2^K*n)))^2))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1/2 : ℝ)) atTop
        (nhds (1/2 : ℝ))).mul ht)
  have hb : ∀ K : ℕ, (c n)^2 ≤ (1/2 : ℝ)*
      (∑' j, (c (j+2*(2^K*n)+1)-c (j+2*(2^K*n)))^2) := by
    intro K
    have hp : 0 < 2^K*n := Nat.mul_pos (by positivity) hn
    simpa only [horbit] using square_le_tail_energy_of_average_decay c hc hd hp
      (hav _ hp)
  have hzero : (c n)^2 ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Filter.Eventually.of_forall hb)
  nlinarith [sq_nonneg (c n)]

/-- The complete missing implication, proved by discrete dyadic averaging. -/
theorem eq_zero_of_summable_of_difference_energy
    {A : ℕ → ℝ} (hA : Summable A)
    (hE : Summable (fun n : ℕ =>
      (n : ℝ)*((n : ℝ)+1)*(A n-A (n+1))^2))
    (hscale : ∀ n, A (2*n) = A n/2)
    {n : ℕ} (hn : 0 < n) : A n = 0 := by
  have hc : ∀ r : ℕ, ((2*r : ℕ) : ℝ)*A (2*r) = (r : ℝ)*A r := by
    intro r
    rw [hscale, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hd : Summable (fun j : ℕ =>
      (((j+1 : ℕ) : ℝ)*A (j+1)-(j : ℝ)*A j)^2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using weighted_difference_summable hA hE
  have hz := eq_zero_of_dyadic_of_average_decay (fun j => (j : ℝ)*A j) hc hd
    (fun j hj => blockAverage_weighted_tendsto_zero hA hj) hn
  exact (mul_eq_zero.mp hz).resolve_left (by positivity)

/-- Coefficient form of the Fourier H1 upgrade, with no regularity provider. -/
theorem weighted_square_summable_of_difference_energy
    {A : ℕ → ℝ} (hA : Summable A)
    (hE : Summable (fun n : ℕ =>
      (n : ℝ)*((n : ℝ)+1)*(A n-A (n+1))^2))
    (hscale : ∀ n, A (2*n) = A n/2) :
    Summable (fun n : ℕ => ((n : ℝ)*A n)^2) := by
  have hz : (fun n : ℕ => ((n : ℝ)*A n)^2) = 0 := by
    funext n
    by_cases hn : n = 0
    · subst n
      simp
    · rw [eq_zero_of_summable_of_difference_energy hA hE hscale
        (Nat.pos_of_ne_zero hn)]
      simp
  rw [hz]
  exact summable_zero
end RiemannResearch.Analysis.DyadicBlockRigidity
