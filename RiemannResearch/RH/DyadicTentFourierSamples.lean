/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.DyadicTentFourierReconstruction
import RiemannResearch.RH.DyadicBoundaryTents

/-!
# Fourier reconstruction of every actual integer boundary sample

Source: continuation of the user-provided
`FourierBridgeLeanVerification20260910(1).md`, September 10, 2026.
The real multiplicative periodization is genuinely summable, has at most one
nonzero scale, and agrees with every actual positive-integer dyadic boundary
coordinate. This identifies the deterministic scalar Fourier reconstruction
with the existing Hilbert-space coordinates and extends it to arbitrary finite
signed packets. Uniform arithmetic cutoff domination and the infinite signed
arithmetic Fourier bridge remain separate obligations.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis

/-- The multiplicative form of the real log-periodic tent extension. -/
def dyadicTentPeriodization (a x : ℝ) : ℝ :=
  ∑' k : ℤ, rootTent a (x / (2 : ℝ)^k)

/-- No second dyadic scale contributes when one scaled point lies in the closed tent. -/
theorem rootTent_other_scale_zero {a x : ℝ} (ha : 2 ≤ a) (j k : ℤ)
    (hl : a ≤ x / (2 : ℝ)^j) (hu : x / (2 : ℝ)^j ≤ a+2)
    (hkj : k ≠ j) : rootTent a (x / (2 : ℝ)^k) = 0 := by
  have hjp : 0 < (2 : ℝ)^j := zpow_pos (by norm_num) _
  have hkp : 0 < (2 : ℝ)^k := zpow_pos (by norm_num) _
  have hxl : a * (2 : ℝ)^j ≤ x := (le_div_iff₀ hjp).mp hl
  have hxu : x ≤ (a+2) * (2 : ℝ)^j := (div_le_iff₀ hjp).mp hu
  rcases lt_or_gt_of_ne hkj with hlt | hgt
  · have he : (2 : ℝ)^k * 2 ≤ (2 : ℝ)^j := by
      have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (show k+1 ≤ j by omega)
      simpa only [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one] using h
    apply rootTent_eq_zero_of_ge
    apply (le_div_iff₀ hkp).mpr
    have h1 := mul_le_mul_of_nonneg_left he (show 0 ≤ a by linarith)
    have h2 := mul_nonneg (show 0 ≤ a-2 by linarith) hkp.le
    nlinarith
  · have he : (2 : ℝ)^j * 2 ≤ (2 : ℝ)^k := by
      have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (show j+1 ≤ k by omega)
      simpa only [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one] using h
    apply rootTent_eq_zero_of_le
    apply (div_le_iff₀ hkp).mpr
    have h1 := mul_le_mul_of_nonneg_left he (show 0 ≤ a by linarith)
    have h2 := mul_nonneg (show 0 ≤ a-2 by linarith) hjp.le
    nlinarith

/-- Exact collapse of the full integer periodization to its sole possible tent. -/
theorem rootTent_periodization_eq_of_mem {a x : ℝ} (ha : 2 ≤ a) (j : ℤ)
    (hl : a ≤ x / (2 : ℝ)^j) (hu : x / (2 : ℝ)^j ≤ a+2) :
    dyadicTentPeriodization a x = rootTent a (x / (2 : ℝ)^j) := by
  exact tsum_eq_single j (fun k hk => rootTent_other_scale_zero ha j k hl hu hk)

/-- The full periodization is bounded without any convergence or arithmetic premise. -/
theorem dyadicTentPeriodization_mem_unit {a : ℝ} (ha : 2 ≤ a) (x : ℝ) :
    0 ≤ dyadicTentPeriodization a x ∧ dyadicTentPeriodization a x ≤ 1 := by
  classical
  by_cases h : ∃ j : ℤ, rootTent a (x / (2 : ℝ)^j) ≠ 0
  · obtain ⟨j, hj⟩ := h
    have hp : 0 < rootTent a (x / (2 : ℝ)^j) :=
      lt_of_le_of_ne (rootTent_nonneg _ _) (Ne.symm hj)
    obtain ⟨hl, hu⟩ := (rootTent_pos_iff _ _).mp hp
    rw [rootTent_periodization_eq_of_mem ha j hl.le hu.le]
    exact ⟨rootTent_nonneg _ _, rootTent_le_one _ _⟩
  · have hz : ∀ j : ℤ, rootTent a (x / (2 : ℝ)^j) = 0 := by
      simpa only [not_exists, not_not] using h
    simp only [dyadicTentPeriodization, hz, tsum_zero]
    norm_num

/-- Multiplying the physical input by two merely reindexes the full extension. -/
theorem dyadicTentPeriodization_double (a x : ℝ) :
    dyadicTentPeriodization a (2*x) = dyadicTentPeriodization a x := by
  unfold dyadicTentPeriodization
  rw [← (Equiv.addRight (1 : ℤ)).tsum_eq (fun k : ℤ =>
    rootTent a ((2*x) / (2 : ℝ)^k))]
  apply tsum_congr
  intro k
  change rootTent a ((2*x) / (2 : ℝ)^(k+1)) = rootTent a (x / (2 : ℝ)^k)
  congr 1
  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  field_simp


/-- The infinite scale sum has at most one nonzero term, hence is genuinely summable. -/
theorem summable_rootTent_dyadic_scales {a : ℝ} (ha : 2 ≤ a) (x : ℝ) :
    Summable (fun j : ℤ => rootTent a (x / (2 : ℝ)^j)) := by
  classical
  by_cases h : ∃ j : ℤ, rootTent a (x / (2 : ℝ)^j) ≠ 0
  · obtain ⟨j, hj⟩ := h
    have hp : 0 < rootTent a (x / (2 : ℝ)^j) :=
      lt_of_le_of_ne (rootTent_nonneg _ _) (Ne.symm hj)
    obtain ⟨hl, hu⟩ := (rootTent_pos_iff _ _).mp hp
    apply summable_of_ne_finset_zero (s := {j})
    intro k hk
    exact rootTent_other_scale_zero ha j k hl.le hu.le (by simpa using hk)
  · have hz : ∀ j : ℤ, rootTent a (x / (2 : ℝ)^j) = 0 := by
      simpa only [not_exists, not_not] using h
    simp only [hz]
    exact summable_zero

/-- The exact change from normalized logarithmic translates to physical dyadic scales. -/
theorem rootTent_normalized_log_atom (a t : ℝ) (n : ℤ) :
    rootTent a (Real.exp (Real.log 2 * (t+(n:ℝ)))) =
      rootTent a (Real.exp (Real.log 2*t) / (2 : ℝ)^(-n)) := by
  have hn : Real.exp (Real.log 2 * (n:ℝ)) = (2 : ℝ)^n := by
    rw [← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_intCast]
  rw [mul_add, Real.exp_add, hn, zpow_neg, div_inv_eq_mul]

/-- The circle-of-length-one convention and the physical periodization are identical. -/
theorem rootTent_normalized_log_periodization (a t : ℝ) :
    (∑' n : ℤ, rootTent a (Real.exp (Real.log 2 * (t+(n:ℝ))))) =
      dyadicTentPeriodization a (Real.exp (Real.log 2*t)) := by
  simp_rw [rootTent_normalized_log_atom]
  let e : ℤ ≃ ℤ := ⟨Neg.neg, Neg.neg, neg_neg, neg_neg⟩
  exact e.tsum_eq (fun k : ℤ => rootTent a (Real.exp (Real.log 2*t) / (2 : ℝ)^k))

/-- Logarithmic evaluation at any positive physical point recovers that point exactly. -/
theorem rootTent_normalized_log_periodization_at_log (a : ℝ) {x : ℝ} (hx : 0 < x) :
    (∑' n : ℤ, rootTent a
      (Real.exp (Real.log 2 * (Real.log x / Real.log 2 + (n:ℝ))))) =
      dyadicTentPeriodization a x := by
  rw [rootTent_normalized_log_periodization]
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have he : Real.log 2 * (Real.log x / Real.log 2) = Real.log x := by field_simp
  rw [he, Real.exp_log hx]

end RiemannResearch.Analysis

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis

/-- On every ascending tent sector, the full extension equals the actual boundary coordinate. -/
theorem dyadicTentPeriodization_integer_rising (i h r : ℕ) (hr : r ≤ 2^h) :
    dyadicTentPeriodization (2*((i:ℝ)+1))
      ((2^h*(2*(i+1))+r : ℕ) : ℝ) =
    dyadicBoundaryCoordinate
      (dyadicProjectedStep (2^h*(2*(i+1))+r) (by positivity)) i := by
  have hp : 0 < (2 : ℝ)^h := pow_pos (by norm_num) _
  have hrc : (r : ℝ) ≤ (2 : ℝ)^h := by exact_mod_cast hr
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hx : ((2^h*(2*(i+1))+r : ℕ) : ℝ) / (2 : ℝ)^(h : ℤ) =
      2*((i:ℝ)+1) + (r:ℝ)/(2:ℝ)^h := by
    push_cast
    simp only [zpow_natCast]
    field_simp
  have hq0 : 0 ≤ (r:ℝ)/(2:ℝ)^h := div_nonneg hr0 hp.le
  have hq1 : (r:ℝ)/(2:ℝ)^h ≤ 1 := (div_le_one hp).mpr hrc
  rw [rootTent_periodization_eq_of_mem (by nlinarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)] : 2 ≤ 2*((i:ℝ)+1))
    (h : ℤ) (by rw [hx]; linarith) (by rw [hx]; linarith), hx,
    rootTent_eq_left (by linarith) (by linarith),
    dyadicBoundaryCoordinate_step_tent_rising i h r hr]
  ring

/-- On every descending tent sector, the full extension equals the actual boundary coordinate. -/
theorem dyadicTentPeriodization_integer_falling (i h r : ℕ) (hr : r ≤ 2^h) :
    dyadicTentPeriodization (2*((i:ℝ)+1))
      ((2^h*(2*(i+1)+1)+r : ℕ) : ℝ) =
    dyadicBoundaryCoordinate
      (dyadicProjectedStep (2^h*(2*(i+1)+1)+r) (by positivity)) i := by
  have hp : 0 < (2 : ℝ)^h := pow_pos (by norm_num) _
  have hrc : (r : ℝ) ≤ (2 : ℝ)^h := by exact_mod_cast hr
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hx : ((2^h*(2*(i+1)+1)+r : ℕ) : ℝ) / (2 : ℝ)^(h : ℤ) =
      2*((i:ℝ)+1)+1 + (r:ℝ)/(2:ℝ)^h := by
    push_cast
    simp only [zpow_natCast]
    field_simp
  have hq0 : 0 ≤ (r:ℝ)/(2:ℝ)^h := div_nonneg hr0 hp.le
  have hq1 : (r:ℝ)/(2:ℝ)^h ≤ 1 := (div_le_one hp).mpr hrc
  rw [rootTent_periodization_eq_of_mem (by nlinarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)] : 2 ≤ 2*((i:ℝ)+1))
    (h : ℤ) (by rw [hx]; linarith) (by rw [hx]; linarith), hx,
    rootTent_eq_right (by linarith) (by linarith),
    dyadicBoundaryCoordinate_step_tent_falling i h r hr]
  ring

end RiemannResearch.RH.Pareto


namespace RiemannResearch.Analysis

/-- The complete scale sum vanishes throughout the closed gap between adjacent tents. -/
theorem dyadicTentPeriodization_zero_gap {a x : ℝ} (ha : 2 ≤ a) (j : ℤ)
    (hl : a+2 ≤ x / (2 : ℝ)^j) (hu : x / (2 : ℝ)^j ≤ 2*a) :
    dyadicTentPeriodization a x = 0 := by
  suffices hz : ∀ k : ℤ, rootTent a (x / (2 : ℝ)^k) = 0 by
    simp [dyadicTentPeriodization, hz]
  intro k
  have hjp : 0 < (2 : ℝ)^j := zpow_pos (by norm_num) _
  have hkp : 0 < (2 : ℝ)^k := zpow_pos (by norm_num) _
  have hxl : (a+2) * (2 : ℝ)^j ≤ x := (le_div_iff₀ hjp).mp hl
  have hxu : x ≤ (2*a) * (2 : ℝ)^j := (div_le_iff₀ hjp).mp hu
  by_cases hkj : k ≤ j
  · have he : (2 : ℝ)^k ≤ (2 : ℝ)^j :=
      zpow_le_zpow_right₀ (by norm_num) hkj
    apply rootTent_eq_zero_of_ge
    apply (le_div_iff₀ hkp).mpr
    exact (mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ a+2)).trans hxl
  · have he : (2 : ℝ)^j * 2 ≤ (2 : ℝ)^k := by
      have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (show j+1 ≤ k by omega)
      simpa only [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one] using h
    apply rootTent_eq_zero_of_le
    apply (div_le_iff₀ hkp).mpr
    have h1 := mul_le_mul_of_nonneg_left he (show 0 ≤ a by linarith)
    nlinarith

end RiemannResearch.Analysis

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis

/-- Beyond the apex, the initial integer gap contains only zero boundary coordinates. -/
theorem dyadicBoundaryCoordinate_step_zero_gap (i m : ℕ)
    (hl : 2*(i+1)+2 ≤ m) (hu : m ≤ 4*(i+1)) :
    dyadicBoundaryCoordinate (dyadicProjectedStep m (by omega)) i = 0 := by
  have hm2 : 2 ≤ m := by omega
  have hd : 0 < m/2 := Nat.div_pos_iff.mpr ⟨by norm_num, hm2⟩
  have hmod := Nat.mod_lt m (by norm_num : 0 < 2)
  have hdecomp := Nat.mod_add_div m 2
  by_cases he : m % 2 = 0
  · have hmform : m = 2*(m/2) := by omega
    have hv : dyadicProjectedStep m (by omega) = dyadicProjectedStep (m/2) hd := by
      simpa only [← hmform] using dyadicProjectedStep_double (m/2) hd
    rw [hv]
    exact dyadicBoundaryCoordinate_step_zero (m/2) hd i (by omega)
  · have hmform : m = 2*(m/2)+1 := by omega
    have hv := dyadicBoundaryCoordinate_step_odd (m/2) hd i
    have hi : i+1 ≠ m/2 := by omega
    rw [if_neg hi,
      dyadicBoundaryCoordinate_step_zero (m/2) hd i (by omega),
      dyadicBoundaryCoordinate_step_zero (m/2+1) (by positivity) i (by omega)] at hv
    simpa only [← hmform, add_zero, mul_zero] using hv

/-- Every dyadic subdivision of an initial zero gap retains the exact actual sample equality. -/
theorem dyadicTentPeriodization_integer_gap (i q h r : ℕ)
    (hql : 2*(i+1)+2 ≤ q) (hqu : q+1 ≤ 4*(i+1)) (hr : r ≤ 2^h) :
    dyadicTentPeriodization (2*((i:ℝ)+1)) ((2^h*q+r : ℕ) : ℝ) =
    dyadicBoundaryCoordinate (dyadicProjectedStep (2^h*q+r) (by
        have hqp : 0 < q := by omega
        positivity)) i := by
  have hp : 0 < (2 : ℝ)^h := pow_pos (by norm_num) _
  have hrc : (r : ℝ) ≤ (2 : ℝ)^h := by exact_mod_cast hr
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hx : ((2^h*q+r : ℕ) : ℝ) / (2 : ℝ)^(h : ℤ) =
      (q:ℝ) + (r:ℝ)/(2:ℝ)^h := by
    push_cast
    simp only [zpow_natCast]
    field_simp
  have hq0 : 0 ≤ (r:ℝ)/(2:ℝ)^h := div_nonneg hr0 hp.le
  have hq1 : (r:ℝ)/(2:ℝ)^h ≤ 1 := (div_le_one hp).mpr hrc
  have hqlr : 2*((i:ℝ)+1)+2 ≤ q := by exact_mod_cast hql
  have hqur : (q:ℝ)+1 ≤ 4*((i:ℝ)+1) := by exact_mod_cast hqu
  rw [dyadicTentPeriodization_zero_gap
    (by nlinarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)] : 2 ≤ 2*((i:ℝ)+1))
    (h : ℤ) (by rw [hx]; linarith) (by rw [hx]; linarith)]
  have hi := dyadicBoundaryCoordinate_step_interpolation i q h r (by omega) hr
  rw [dyadicBoundaryCoordinate_step_zero_gap i q hql (by omega),
    dyadicBoundaryCoordinate_step_zero_gap i (q+1) (by omega) hqu,
    mul_zero, mul_zero, zero_add] at hi
  exact (mul_eq_zero.mp hi).resolve_left hp.ne' |>.symm

end RiemannResearch.RH.Pareto


namespace RiemannResearch.Analysis

/-- Every natural point above a positive base belongs to an exact dyadic annulus. -/
theorem exists_nat_dyadic_annulus (a m : ℕ) (ha : 0 < a) (hm : a ≤ m) :
    ∃ h : ℕ, a*2^h ≤ m ∧ m < 2*a*2^h := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hu : m < 2*a
    · exact ⟨0, by simpa using hm, by simpa using hu⟩
    · have hm2 : 2 ≤ m := by omega
      have hd : a ≤ m/2 := by omega
      obtain ⟨h, hl, hh⟩ := ih (m/2) (by omega) hd
      have hmod := Nat.mod_lt m (by norm_num : 0 < 2)
      have heq := Nat.mod_add_div m 2
      refine ⟨h+1, ?_, ?_⟩
      · calc
          a*2^(h+1) = 2*(a*2^h) := by rw [pow_succ]; ring
          _ ≤ 2*(m/2) := Nat.mul_le_mul_left 2 hl
          _ ≤ m := by omega
      · rw [pow_succ]
        nlinarith

end RiemannResearch.Analysis

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis

/-- Small integer samples vanish even though the real extension has negative scales. -/
theorem dyadicTentPeriodization_integer_below (i m : ℕ) (hm : m ≤ 2*(i+1)) :
    dyadicTentPeriodization (2*((i:ℝ)+1)) (m:ℝ) = 0 := by
  suffices hz : ∀ k : ℤ, rootTent (2*((i:ℝ)+1)) ((m:ℝ) / (2 : ℝ)^k) = 0 by
    simp [dyadicTentPeriodization, hz]
  intro k
  cases k with
  | ofNat n =>
      apply rootTent_eq_zero_of_le
      apply (div_le_iff₀ (pow_pos (by norm_num : (0:ℝ)<2) n)).mpr
      have hm' : (m:ℝ) ≤ 2*((i:ℝ)+1) := by exact_mod_cast hm
      have hp : (1:ℝ) ≤ (2:ℝ)^n := by
        induction n with
        | zero => norm_num
        | succ n ih => rw [pow_succ]; nlinarith
      have ha : (0:ℝ) ≤ 2*((i:ℝ)+1) := by positivity
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hp)]
  | negSucc n =>
      have he : (m:ℝ) / (2:ℝ)^(Int.negSucc n) =
          2*((m*2^n : ℕ):ℝ) := by
        simp only [Int.negSucc_eq, zpow_neg, div_inv_eq_mul]
        push_cast
        rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one, zpow_natCast]
        ring
      rw [he]
      simpa only [Nat.cast_add, Nat.cast_one] using
        rootTent_even_nat (i+1) (m*2^n)

/-- The full real extension agrees with every actual positive-integer boundary sample. -/
theorem dyadicTentPeriodization_integer (i m : ℕ) (hm : 0 < m) :
    dyadicTentPeriodization (2*((i:ℝ)+1)) (m:ℝ) =
      dyadicBoundaryCoordinate (dyadicProjectedStep m hm) i := by
  by_cases hsmall : m ≤ 2*(i+1)
  · rw [dyadicTentPeriodization_integer_below i m hsmall,
      dyadicBoundaryCoordinate_step_zero m hm i hsmall]
  · obtain ⟨h, hl, hu⟩ := exists_nat_dyadic_annulus (2*(i+1)) m
      (by positivity) (by omega)
    let q := m / 2^h
    let r := m % 2^h
    have hp : 0 < 2^h := by positivity
    have hr : r < 2^h := Nat.mod_lt _ hp
    have he : 2^h*q+r = m := by
      dsimp [q, r]
      have hh := Nat.mod_add_div m (2^h)
      omega
    have hql : 2*(i+1) ≤ q := by
      by_contra hq
      have hq' : q+1 ≤ 2*(i+1) := by omega
      have hc := Nat.mul_le_mul_left (2^h) hq'
      nlinarith
    have hqu : q+1 ≤ 4*(i+1) := by
      by_contra hq
      have hq' : 4*(i+1) ≤ q := by omega
      have hc := Nat.mul_le_mul_left (2^h) hq'
      nlinarith
    by_cases hq0 : q = 2*(i+1)
    · have ht := dyadicTentPeriodization_integer_rising i h r hr.le
      simpa only [← hq0, he] using ht
    · by_cases hq1 : q = 2*(i+1)+1
      · have ht := dyadicTentPeriodization_integer_falling i h r hr.le
        simpa only [← hq1, he] using ht
      · have ht := dyadicTentPeriodization_integer_gap i q h r
          (by omega) hqu hr.le
        simpa only [he] using ht

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis

/-- The normalized complex periodization and the real physical scale sum are identical. -/
theorem dyadicLogTentPeriodization_eq_physical (i : ℕ) (t : ℝ) :
    dyadicLogTentPeriodization i t =
      (dyadicTentPeriodization (2*((i:ℝ)+1)) (Real.exp (Real.log 2*t)) : ℂ) := by
  unfold dyadicLogTentPeriodization dyadicLogTent
  rw [← Complex.ofReal_tsum, rootTent_normalized_log_periodization]

/-- The actual continuous log-periodic extension recovers every positive-integer sample. -/
theorem dyadicLogTentPeriodization_at_integer_log (i m : ℕ) (hm : 0 < m) :
    dyadicLogTentPeriodization i (Real.log (m:ℝ) / Real.log 2) =
      (dyadicBoundaryCoordinate (dyadicProjectedStep m hm) i : ℂ) := by
  unfold dyadicLogTentPeriodization dyadicLogTent
  rw [← Complex.ofReal_tsum,
    rootTent_normalized_log_periodization_at_log _ (by exact_mod_cast hm),
    dyadicTentPeriodization_integer i m hm]

/-- Unconditional Fourier `HasSum` identity for every actual integer boundary step. -/
theorem dyadicBoundaryCoordinate_step_hasSum_fourier (i m : ℕ) (hm : 0 < m) :
    HasSum (fun h : ℤ => dyadicTentMellinCoefficient i h *
      fourier h ((Real.log (m:ℝ) / Real.log 2 : ℝ) : UnitAddCircle))
      (dyadicBoundaryCoordinate (dyadicProjectedStep m hm) i : ℂ) := by
  simpa only [dyadicLogTentPeriodization_at_integer_log i m hm] using
    dyadicLogTentPeriodization_hasSum_fourier i (Real.log (m:ℝ) / Real.log 2)

/-- Every finite signed arithmetic packet has the exact actual Fourier expansion.
All weights and mixed frequency contributions remain signed; no norm inequality
or limiting exchange is used in this identity. -/
theorem dyadicBoundaryCoordinate_finite_signed_packet_hasSum_fourier
    (i : ℕ) (s : Finset ℕ) (w : ℕ → ℝ) :
    HasSum (fun h : ℤ => dyadicTentMellinCoefficient i h *
      ∑ m ∈ s, (w m : ℂ) *
        fourier h ((Real.log ((m+1:ℕ):ℝ) / Real.log 2 : ℝ) : UnitAddCircle))
      (∑ m ∈ s, (w m : ℂ) *
        (dyadicBoundaryCoordinate (dyadicProjectedStep (m+1) (by positivity)) i : ℂ)) := by
  have hs := hasSum_sum (s := s) (fun m _ =>
    HasSum.mul_left (w m : ℂ)
      (dyadicBoundaryCoordinate_step_hasSum_fourier i (m+1) (by positivity)))
  have hf : (fun h : ℤ => ∑ m ∈ s, (w m : ℂ) *
      (dyadicTentMellinCoefficient i h *
        fourier h ((Real.log ((m+1:ℕ):ℝ) / Real.log 2 : ℝ) : UnitAddCircle))) =
      (fun h : ℤ => dyadicTentMellinCoefficient i h *
        ∑ m ∈ s, (w m : ℂ) *
          fourier h ((Real.log ((m+1:ℕ):ℝ) / Real.log 2 : ℝ) : UnitAddCircle)) := by
    funext h
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  simpa only [hf] using hs

end RiemannResearch.RH.Pareto
