/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QRationalPeriodRefinement
import RiemannResearch.RH.QRationalWeightComparison
import RiemannResearch.RH.QRationalCoprimeTail
import RiemannResearch.RH.ZetaTwoPolygammaResidues
import RiemannResearch.RH.QResiduePowerRefinement
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Lean.Elab.Tactic.Omega

/-!
# Quartic control of complete rational-metric refinement

Source: user-directed continuation of
`RH_CRT_Lean_Continuation_Agenda_2026-10-20`, 20 October 2026.
The proof refines the existing exact midpoint-defect identity by a cubic
telescoping bound for its complete quartic tail. It uses reciprocal series;
no special-function convergence estimate is assumed. Every refined residue
fiber is retained. The `20/(3*k)` estimate applies to arbitrary periodic
residuals, including moving legal optimizers. It controls the discrepancy of
the surrogate metric, not the complete-Q limiting defect. No RH assumption
or closure conclusion is introduced.
-/

noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiemannResearch.RH.QRationalCoprimeTail
open ZetaTwoProbability

/-- Exact positive remainder in the cubic telescope controlling a quartic tail. -/
private theorem reciprocal_cubic_step_exact {L x : ℝ} (hL : 0 < L) (hx : 0 < x) :
    1 / x^3 - 1 / (x + L)^3 - 3 * L / (x + L)^4 =
      L^2 * (L^2 + 4 * L * x + 6 * x^2) / (x^3 * (x + L)^4) := by
  have hxp : x + L ≠ 0 := ne_of_gt (by positivity : 0 < x + L)
  field_simp [ne_of_gt hx, hxp]
  ring

private theorem reciprocal_quartic_step {L x : ℝ} (hL : 0 < L) (hx : 0 < x) :
    3 * L / (x + L)^4 ≤ 1 / x^3 - 1 / (x + L)^3 := by
  have he := reciprocal_cubic_step_exact hL hx
  have hn : 0 ≤ L^2 * (L^2 + 4 * L * x + 6 * x^2) /
      (x^3 * (x + L)^4) := by positivity
  linarith

private theorem reciprocal_progression_summable (s : ℕ) {L a : ℝ}
    (hL : 0 < L) (ha : 0 < a) :
    Summable (fun j : ℕ => 1 / (a + (j : ℝ) * L)^(s+2)) := by
  have h := (residuePowerWeight_summable s hL ha).mul_left zetaTwo
  exact h.congr (fun j => by field_simp [ne_of_gt zetaTwo_pos])

private theorem unnormalized_residue (s : ℕ) (L a : ℝ) :
    (∑' j : ℕ, 1 / (a + (j : ℝ) * L)^(s+2)) =
      zetaTwo * residuePowerWeight s L a := by
  unfold residuePowerWeight
  rw [← tsum_mul_left]
  apply tsum_congr
  intro j
  field_simp [ne_of_gt zetaTwo_pos]

/-- The full quartic progression tail is bounded by an elementary telescope. -/
private theorem residue_quartic_tail_le {L a : ℝ} (hL : 0 < L) (ha : 0 < a) :
    zetaTwo * residuePowerWeight 2 L (a + L) ≤ 1 / (3 * L * a^3) := by
  have hpartial (N : ℕ) :
      3 * L * (∑ j ∈ Finset.range N, 1 / (a + ((j : ℝ) + 1) * L)^4) +
        1 / (a + (N : ℝ) * L)^3 ≤ 1 / a^3 := by
    induction N with
    | zero => simp
    | succ N ih =>
      have hx : 0 < a + (N : ℝ) * L := by positivity
      have hh := reciprocal_quartic_step hL hx
      rw [Finset.sum_range_succ]
      push_cast
      rw [show a + (N : ℝ) * L + L = a + ((N : ℝ) + 1) * L by ring] at hh
      simp only [div_eq_mul_inv] at hh ih ⊢
      nlinarith
  have hs : Summable (fun j : ℕ => 1 / (a + ((j : ℝ) + 1) * L)^4) := by
    convert reciprocal_progression_summable 2 hL (show 0 < a + L by positivity) using 1
    ext j
    congr 2
    ring
  have hb (N : ℕ) :
      (∑ j ∈ Finset.range N, 1 / (a + ((j : ℝ) + 1) * L)^4) ≤
        1 / (3 * L * a^3) := by
    have hh := hpartial N
    have hn : 0 ≤ 1 / (a + (N : ℝ) * L)^3 := by positivity
    have haux : (∑ j ∈ Finset.range N, 1 / (a + ((j : ℝ) + 1) * L)^4) ≤
        (1 / a^3) / (3 * L) := by
      apply (le_div_iff₀ (by positivity : 0 < 3 * L)).mpr
      nlinarith
    convert haux using 1
    field_simp
  have hh := le_of_tendsto hs.hasSum.tendsto_sum_nat (Eventually.of_forall hb)
  have he : (∑' j : ℕ, 1 / (a + ((j : ℝ) + 1) * L)^4) =
      zetaTwo * residuePowerWeight 2 L (a + L) := by
    rw [← unnormalized_residue]
    apply tsum_congr
    intro j
    congr 2
    ring
  rwa [he] at hh

theorem midpointDefect_le_quartic {L x : ℝ} (hL : 0 < L) (hx : L < x) :
    midpointDefect L x ≤ (L^2 / 3) * (1 / x^4) := by
  have hx0 : 0 < x := hL.trans hx
  have hs : L^2 ≤ x^2 := by nlinarith
  have hd : 0 < 4 * x^2 - L^2 := by nlinarith
  unfold midpointDefect
  calc
    L^2 / (x^2 * (4 * x^2 - L^2)) ≤ L^2 / (3 * x^4) := by
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg x)]
    _ = _ := by ring

theorem midpointBoundary_tendsto_zero {L a : ℝ} (hL : 0 < L) :
    Tendsto (midpointBoundary L a) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hd : Tendsto (fun n : ℕ => L * (2*a + (2*(n:ℝ)+1)*L)) atTop atTop := by
    have hh := tendsto_atTop_add_const_right atTop (L*(2*a+L))
      (Tendsto.const_mul_atTop (by positivity : 0 < 2*L^2) hn)
    apply hh.congr'
    filter_upwards [] with n
    ring
  exact hd.const_div_atTop 2

end RiemannResearch.RH.QRationalCoprimeTail


namespace RiemannResearch.RH.QRationalCoprimeTail
open ZetaTwoProbability

private theorem unnormalized_shift_residue (s : ℕ) (L a : ℝ) :
    (∑' j : ℕ, 1 / (a + ((j : ℝ)+1)*L)^(s+2)) =
      zetaTwo * residuePowerWeight s L (a+L) := by
  rw [← unnormalized_residue]
  apply tsum_congr
  intro j
  congr 2
  ring

/-- Complete gap upper bound obtained from the retained exact midpoint defects. -/
theorem real_weight_gap_le_quartic {L a : ℝ} (hL : 0 < L) (ha : 0 < a) :
    1/a^2 + 2/(L*(2*a+L)) - zetaTwo * residuePowerWeight 0 L a ≤
      (L^2/3) * (zetaTwo * residuePowerWeight 2 L (a+L)) := by
  have hs (s : ℕ) : Summable (fun j : ℕ => 1/(a+((j:ℝ)+1)*L)^(s+2)) := by
    convert reciprocal_progression_summable s hL (show 0 < a+L by positivity) using 1
    ext j
    congr 2
    ring
  have ht (s : ℕ) : Tendsto
      (fun N : ℕ => ∑ j ∈ Finset.range N, 1/(a+((j:ℝ)+1)*L)^(s+2))
      atTop (𝓝 (zetaTwo * residuePowerWeight s L (a+L))) := by
    have hh := (hs s).hasSum.tendsto_sum_nat
    rwa [unnormalized_shift_residue] at hh
  have hp (N : ℕ) : midpointBoundary L a 0 ≤
      (∑ j ∈ Finset.range N, 1/(a+((j:ℝ)+1)*L)^2) + midpointBoundary L a N +
      (L^2/3) * (∑ j ∈ Finset.range N, 1/(a+((j:ℝ)+1)*L)^4) := by
    have he := midpoint_partial_exact hL ha N
    have hd : (∑ j ∈ Finset.range N, midpointDefect L (a+((j:ℝ)+1)*L)) ≤
        (L^2/3) * (∑ j ∈ Finset.range N, 1/(a+((j:ℝ)+1)*L)^4) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      apply midpointDefect_le_quartic hL
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith
    linarith
  have ht' := ((ht 0).add (midpointBoundary_tendsto_zero (a := a) hL)).add
    ((ht 2).const_mul (L^2/3))
  have hb := ge_of_tendsto ht' (Eventually.of_forall hp)
  rw [residuePowerWeight_shift 0 hL ha, mul_add zetaTwo]
  have hc : zetaTwo * (1 / (zetaTwo * a^(0+2))) = 1/a^2 := by
    field_simp [ne_of_gt zetaTwo_pos]
  rw [hc]
  simp only [midpointBoundary, Nat.cast_zero, mul_zero, zero_add, one_mul, add_zero] at hb
  linarith

/-- The coefficient comparison behind the uniform factor `20/(3*k)`. -/
theorem quartic_refinement_coefficient {L a k : ℝ} (hL : 0 < L)
    (ha : 0 < a) (haL : a ≤ L) (hk : 2 ≤ k) :
    k^2 * L / (9 * (a+(k-1)*L)^3) ≤
      (20/(3*k)) * midpointDefect L (a+L) := by
  have hk0 : 0 < k := by linarith
  have hX : 0 < a+L := by positivity
  have hY : k*(a+L)/2 ≤ a+(k-1)*L := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ k-2) (sub_nonneg.mpr haL)]
  have hY0 : 0 < a+(k-1)*L := lt_of_lt_of_le (by positivity) hY
  have hd : 0 < 4*(a+L)^2-L^2 := by nlinarith [sq_pos_of_pos hL]
  have hpoly : a*L*8+a^2*4+L^2*3 ≠ 0 := by positivity
  have hshape : 8*(4*(a+L)^2-L^2) ≤ 60*L*(a+L) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr haL) (show 0 ≤ L+8*(a+L) by positivity)]
  have hc : 8*(4*(a+L)^2-L^2)/(3*L*(a+L)) ≤ 20 := by
    apply (div_le_iff₀ (by positivity : 0 < 3*L*(a+L))).mpr
    linarith
  calc
    k^2*L/(9*(a+(k-1)*L)^3) ≤ k^2*L/(9*(k*(a+L)/2)^3) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      gcongr
    _ = 8*L/(9*k*(a+L)^3) := by field_simp; ring
    _ = ((8*(4*(a+L)^2-L^2)/(3*L*(a+L)))/(3*k)) *
        midpointDefect L (a+L) := by
      unfold midpointDefect
      rw [show 4*(a+L)^2-L^2 = a*L*8+a^2*4+L^2*3 by ring]
      field_simp [ne_of_gt hd, ne_of_gt hX, ne_of_gt hL, ne_of_gt hk0, hpoly]
      ring
    _ ≤ (20/(3*k)) * midpointDefect L (a+L) := by
      apply mul_le_mul_of_nonneg_right
      · exact div_le_div_of_nonneg_right hc (by positivity)
      · exact midpointDefect_nonneg hL (by linarith)

/-- A complete refined fiber gap, with every infinite tail retained. -/
theorem refined_weight_gap_le_quartic (L k a : ℕ) (hL : 0 < L)
    (hk : 2 ≤ k) (ha : 0 < a) (haL : a ≤ L) :
    (∑ j : Fin k, (weight (L*k) (a+L*j.val) -
      zetaTwo * residuePowerWeight 0 (L*k : ℕ) (a+L*j.val : ℕ))) ≤
        (20/(3*(k:ℝ))) * (weight L a - zetaTwo * residuePowerWeight 0 L a) := by
  have hk0 : 0 < k := by omega
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have haLR : (a : ℝ) ≤ L := by exact_mod_cast haL
  have hk1 : 0 < (k : ℝ)-1 := by linarith
  have hY : 0 < (a : ℝ) + ((k : ℝ)-1)*L := add_pos haR (mul_pos hk1 hLR)
  have hre := residuePowerWeight_refine_order 2 L k (a+L*k) hL hk0
    (by omega : 0 < a+L*k)
  have hb : (∑ j : Fin k, (weight (L*k) (a+L*j.val) -
        zetaTwo * residuePowerWeight 0 (L*k : ℕ) (a+L*j.val : ℕ))) ≤
      (((L*k : ℕ) : ℝ)^2/3) *
        (zetaTwo * residuePowerWeight 2 L (a+L*k : ℕ)) := by
    rw [hre, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hi := real_weight_gap_le_quartic
      (show (0 : ℝ) < (L*k : ℕ) by exact_mod_cast Nat.mul_pos hL hk0)
      (show (0 : ℝ) < (a+L*j.val : ℕ) by exact_mod_cast (show 0 < a+L*j.val by omega))
    have he : ((a+L*j.val : ℕ) : ℝ) + ((L*k : ℕ) : ℝ) =
        ((a+L*k+L*j.val : ℕ) : ℝ) := by push_cast; ring
    rw [he] at hi
    simpa only [weight] using hi
  have hq := residue_quartic_tail_le hLR hY
  rw [show (a : ℝ)+((k : ℝ)-1)*L+L = ((a+L*k : ℕ) : ℝ) by push_cast; ring] at hq
  calc
    _ ≤ (((L*k : ℕ) : ℝ)^2/3) *
        (zetaTwo * residuePowerWeight 2 L (a+L*k : ℕ)) := hb
    _ ≤ (((L*k : ℕ) : ℝ)^2/3) *
        (1/(3*(L:ℝ)*((a:ℝ)+((k:ℝ)-1)*L)^3)) :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    _ = (k:ℝ)^2 * L / (9*((a:ℝ)+((k:ℝ)-1)*L)^3) := by
      push_cast
      field_simp [ne_of_gt hLR]
      ring
    _ ≤ (20/(3*(k:ℝ))) * midpointDefect L ((a:ℝ)+L) :=
      quartic_refinement_coefficient hLR haR haLR hkR
    _ ≤ (20/(3*(k:ℝ))) * (weight L a - zetaTwo * residuePowerWeight 0 L a) :=
      mul_le_mul_of_nonneg_left (midpointDefect_le_weight_gap L a ha haL) (by positivity)

private theorem positive_sites_range (L : ℕ) (f : ℕ → ℝ) :
    (∑ a ∈ sites L, f a) = ∑ a ∈ Finset.range L, f (a+1) := by
  rw [sum_positive_representatives]
  exact Fin.sum_univ_eq_sum_range (fun a : ℕ => f (a+1)) L

private theorem positive_sites_blocks (L k : ℕ) (f : ℕ → ℝ) :
    (∑ a ∈ sites (L*k), f a) =
      ∑ a ∈ sites L, ∑ j : Fin k, f (a+L*j.val) := by
  have hr (g : ℕ → ℝ) (q : ℕ) :
      (∑ r ∈ Finset.range (L*q), g r) =
        ∑ j ∈ Finset.range q, ∑ a ∈ Finset.range L, g (L*j+a) := by
    induction q with
    | zero => simp
    | succ q ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
  rw [positive_sites_range, positive_sites_range, hr]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => f (a+1+L*j)) k]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  omega

/-- Uniform coefficient-independent refinement, improving `120/k` to `20/(3*k)`. -/
theorem rationalGap_mul_le_quartic (L k : ℕ) (hL : 0 < L) (hk : 2 ≤ k)
    (f : ℕ → ℝ) (hp : ∀ n, f (n + L) = f n) :
    rationalGap (L*k) f ≤ (20/(3*(k:ℝ))) * rationalGap L f := by
  have hperiod (j a : ℕ) : f (a+L*j) = f a := by
    induction j with
    | zero => simp
    | succ j ih => rw [Nat.mul_succ, ← Nat.add_assoc, hp, ih]
  unfold rationalGap
  rw [positive_sites_blocks]
  calc
    (∑ a ∈ sites L, ∑ j : Fin k,
      (weight (L*k) (a+L*j.val) - zetaTwo*residuePowerWeight 0 (L*k : ℕ) (a+L*j.val : ℕ)) *
        (1-f (a+L*j.val))^2) =
        ∑ a ∈ sites L, (∑ j : Fin k,
          (weight (L*k) (a+L*j.val) - zetaTwo*residuePowerWeight 0 (L*k : ℕ) (a+L*j.val : ℕ))) *
            (1-f a)^2 := by simp_rw [hperiod, Finset.sum_mul]
    _ ≤ ∑ a ∈ sites L, ((20/(3*(k:ℝ))) *
        (weight L a - zetaTwo*residuePowerWeight 0 L a)) * (1-f a)^2 := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨ha1, haL⟩ := Finset.mem_Icc.mp ha
      exact mul_le_mul_of_nonneg_right
        (refined_weight_gap_le_quartic L k a hL hk (by omega) haL) (sq_nonneg _)
    _ = (20/(3*(k:ℝ))) *
        ∑ a ∈ sites L, (weight L a - zetaTwo*residuePowerWeight 0 L a)*(1-f a)^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring

theorem rationalGap_mul_le_self_quartic (L k : ℕ) (hL : 0 < L) (hk : 7 ≤ k)
    (f : ℕ → ℝ) (hp : ∀ n, f (n + L) = f n) :
    rationalGap (L*k) f ≤ rationalGap L f := by
  have hkR : (7 : ℝ) ≤ k := by exact_mod_cast hk
  have hc : 20/(3*(k:ℝ)) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hg : 0 ≤ rationalGap L f := by
    unfold rationalGap
    apply Finset.sum_nonneg
    intro a ha
    obtain ⟨ha1, haL⟩ := Finset.mem_Icc.mp ha
    exact mul_nonneg (weight_gap_bounds L a (by omega) haL).1 (sq_nonneg _)
  exact (rationalGap_mul_le_quartic L k hL (by omega) f hp).trans
    (by simpa using mul_le_mul_of_nonneg_right hc hg)

theorem rationalGap_mul_le_half_quartic (L k : ℕ) (hL : 0 < L) (hk : 14 ≤ k)
    (f : ℕ → ℝ) (hp : ∀ n, f (n + L) = f n) :
    rationalGap (L*k) f ≤ rationalGap L f / 2 := by
  have hkR : (14 : ℝ) ≤ k := by exact_mod_cast hk
  have hc : 20/(3*(k:ℝ)) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 3*(k:ℝ))).mpr
    linarith
  have hg : 0 ≤ rationalGap L f := by
    unfold rationalGap
    apply Finset.sum_nonneg
    intro a ha
    obtain ⟨ha1, haL⟩ := Finset.mem_Icc.mp ha
    exact mul_nonneg (weight_gap_bounds L a (by omega) haL).1 (sq_nonneg _)
  exact (rationalGap_mul_le_quartic L k hL (by omega) f hp).trans
    (by nlinarith [mul_le_mul_of_nonneg_right hc hg])

end RiemannResearch.RH.QRationalCoprimeTail
