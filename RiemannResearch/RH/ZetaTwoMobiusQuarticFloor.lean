import RiemannResearch.RH.CanonicalMobiusConditionalHead
import RiemannResearch.NumberTheory.FiniteFloorTail
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Source: user-provided exact optimizer cancellation manuscript (8 October 2026),
for the finite Möbius trial and the quartic floor bound. The classical finite
floor convolution is supplied by `finite_mobius_floor_sum`; the inverse-cube
majorant is proved directly, without an arithmetic cancellation hypothesis.
This module does not assert the remaining signed optimizer cancellation.
-/

noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiemannResearch.RH.Pareto.ZetaTwoMobiusFloor
open RiemannResearch.RH.Pareto
open RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.RH.ZetaTwoProbability

/-- Complete residual of the legal trial `-∑ μ(d)g_d`; the d=1 atom is zero. -/
def residual (N k : ℕ) : ℝ :=
  1 + ∑ d ∈ Finset.Icc 1 N,
    (ArithmeticFunction.moebius d : ℝ) * residueFraction d k

/-- The full signed floor tail, including every conductor after N. -/
def floorTail (N k : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc (N+1) k,
    (ArithmeticFunction.moebius d : ℝ) * ((k/d : ℕ) : ℝ)

/-- Inclusive ordinary summatory Möbius function at an integer. -/
def mobiusSummatory (k : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 k, (ArithmeticFunction.moebius d : ℝ)

/-- Exact quotient-level hyperbola identity for the entire signed floor tail. -/
theorem floorTail_eq_summatory_differences (N k : ℕ) :
    floorTail N k = ∑ j ∈ Finset.Icc 1 (k/(N+1)),
      (mobiusSummatory (k/j) - mobiusSummatory N) := by
  rw [floorTail, RiemannResearch.NumberTheory.finite_floor_tail_swap]
  apply Finset.sum_congr rfl
  intro j hj
  have hj0 : 0 < j := (Finset.mem_Icc.mp hj).1
  have hNj : N ≤ k/j := by
    apply (Nat.le_div_iff_mul_le hj0).mpr
    have hh := (Nat.le_div_iff_mul_le (Nat.succ_pos N)).mp (Finset.mem_Icc.mp hj).2
    nlinarith
  have hs := RiemannResearch.NumberTheory.positive_prefix_split_at
    (fun d => (ArithmeticFunction.moebius d : ℝ)) N (k/j) hNj
  unfold mobiusSummatory
  linarith

theorem residual_floor_expansion (N k : ℕ) :
    residual N k = (k : ℝ) * mobiusReciprocalSum N + 1 -
      ∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) * ((k/d : ℕ) : ℝ) := by
  unfold residual mobiusReciprocalSum
  have he : (∑ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius d : ℝ) * residueFraction d k) =
      ∑ d ∈ Finset.Icc 1 N,
        ((k : ℝ) * ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) -
          (ArithmeticFunction.moebius d : ℝ) * ((k/d : ℕ) : ℝ)) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [residueFraction_eq_div_sub_floor d k (Finset.mem_Icc.mp hd).1]
    ring
  rw [he, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- Exact head identity, before estimating any arithmetic quantity. -/
theorem residual_head (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N) :
    residual N k = (k : ℝ) * mobiusReciprocalSum N := by
  rw [residual_floor_expansion, finite_mobius_floor_sum N k hk hkN]
  ring

/-- Exact residual identity with its entire signed floor tail. -/
theorem residual_eq_head_add_floorTail (N k : ℕ) (hk : 0 < k) :
    residual N k = (k : ℝ) * mobiusReciprocalSum N + floorTail N k := by
  rw [residual_floor_expansion]
  by_cases hNk : N ≤ k
  · have hs := RiemannResearch.NumberTheory.positive_prefix_split_at
      (fun d => (ArithmeticFunction.moebius d : ℝ) * ((k/d : ℕ) : ℝ)) N k hNk
    rw [finite_mobius_floor_sum k k hk le_rfl] at hs
    unfold floorTail
    linarith
  · have hkN : k ≤ N := by omega
    have ht : Finset.Icc (N+1) k = ∅ := by
      apply Finset.Icc_eq_empty_of_lt
      omega
    rw [finite_mobius_floor_sum N k hk hkN]
    simp [floorTail, ht]

private theorem moebius_real_abs_le_one (d : ℕ) :
    |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)

/-- Unconditional complete-coordinate bound, including the far tail. -/
theorem residual_abs_le (N k : ℕ) (hN : 0 < N) : |residual N k| ≤ (N : ℝ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hN)
  induction n with
  | zero => simp [residual, residueFraction, Nat.mod_one]
  | succ n ih =>
    have he : residual (n+1+1) k = residual (n+1) k +
        (ArithmeticFunction.moebius (n+1+1) : ℝ) * residueFraction (n+1+1) k := by
      unfold residual
      rw [Finset.sum_Icc_succ_top (by omega)]
      ring
    rw [show n.succ.succ = n+1+1 by omega, he]
    calc
      _ ≤ |residual (n+1) k| +
          |(ArithmeticFunction.moebius (n+1+1) : ℝ) * residueFraction (n+1+1) k| :=
        abs_add_le _ _
      _ ≤ ((n+1 : ℕ) : ℝ) + 1 := by
        apply add_le_add (ih (Nat.succ_pos n))
        rw [abs_mul]
        have hm := moebius_real_abs_le_one (n+1+1)
        have hg := residueFraction_abs_le_one (n+1+1) k (by omega)
        exact (mul_le_mul hm hg (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).trans_eq
          (by norm_num)
      _ = _ := by push_cast; ring

private theorem quartic_le_cube_difference {x : ℝ} (hx : 0 < x) :
    1 / (x+1)^4 ≤ 1 / (3*x^3) - 1 / (3*(x+1)^3) := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hx1 : x+1 ≠ 0 := by positivity
  have he : 1 / (3*x^3) - 1 / (3*(x+1)^3) =
      (3*x^2+3*x+1) / (3*x^3*(x+1)^3) := by
    field_simp [hx0, hx1]
    ring
  rw [he]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (x+1)^4)
    (by positivity : (0 : ℝ) < 3*x^3*(x+1)^3)).2
  have hpoly : 0 ≤ (x+1)^3*(6*x^2+4*x+1) := by positivity
  nlinarith [hpoly]

/-- A telescoping bound with the terminal term retained exactly. -/
theorem quartic_tail_partial_le (N M : ℕ) (hN : 0 < N) :
    (∑ j ∈ Finset.range M, 1 / ((j+N+1 : ℕ) : ℝ)^4) ≤
      1/(3*(N : ℝ)^3) - 1/(3*((N+M : ℕ) : ℝ)^3) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have hNM : (0 : ℝ) < ((N+M : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N+M)
    have hsingle := quartic_le_cube_difference hNM
    have hj : ((M+N+1 : ℕ) : ℝ) = ((N+M : ℕ) : ℝ)+1 := by push_cast; ring
    have he : ((N+M.succ : ℕ) : ℝ) = ((N+M : ℕ) : ℝ)+1 := by push_cast; ring
    rw [hj, he]
    linarith

/-- The complete quartic tail is bounded without dropping its final boundary term
in the finite precursor. -/
theorem quartic_tail_tsum_le (N : ℕ) (hN : 0 < N) :
    (∑' j : ℕ, 1 / ((j+N+1 : ℕ) : ℝ)^4) ≤ 1/(3*(N : ℝ)^3) := by
  have hs0 : Summable (fun j : ℕ => 1 / (j : ℝ)^4) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (4 : ℕ))
  have hs : Summable (fun j : ℕ => 1 / ((j+N+1 : ℕ) : ℝ)^4) := by
    simpa only [Nat.add_assoc] using (summable_nat_add_iff (N+1)).mpr hs0
  apply le_of_tendsto hs.hasSum.tendsto_sum_nat
  apply Filter.Eventually.of_forall
  intro M
  exact (quartic_tail_partial_le N M hN).trans (sub_le_self _ (by positivity))

/-- Literal quartic weighted error summand; the zero coordinate has weight zero. -/
def quarticEnergyTerm (f : ℕ → ℝ) (k : ℕ) : ℝ :=
  (f k)^2 / (zetaTwo * (k : ℝ)^4)

def quarticEnergy (f : ℕ → ℝ) : ℝ := ∑' k, quarticEnergyTerm f k

theorem quarticEnergyTerm_nonneg (f : ℕ → ℝ) (k : ℕ) :
    0 ≤ quarticEnergyTerm f k := by
  exact div_nonneg (sq_nonneg _) (mul_nonneg zetaTwo_pos.le (by positivity))

theorem residual_quartic_summable (N : ℕ) (hN : 0 < N) :
    Summable (quarticEnergyTerm (residual N)) := by
  have hZ := zetaTwo_pos
  have hs : Summable (fun k : ℕ => ((N : ℝ)^2 / zetaTwo) * (1 / (k : ℝ)^4)) :=
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (4 : ℕ))).mul_left _
  apply Summable.of_nonneg_of_le (quarticEnergyTerm_nonneg _) _ hs
  intro k
  have hr : (residual N k)^2 ≤ (N : ℝ)^2 := by
    have hb := mul_self_le_mul_self (abs_nonneg _) (residual_abs_le N k hN)
    simpa only [← pow_two, sq_abs] using hb
  unfold quarticEnergyTerm
  calc
    _ ≤ (N : ℝ)^2 / (zetaTwo * (k : ℝ)^4) :=
      div_le_div_of_nonneg_right hr (by positivity)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev, one_mul]; ring

theorem residual_quartic_head_eq (N k : ℕ) (hkN : k ≤ N) :
    quarticEnergyTerm (residual N) k =
      (mobiusReciprocalSum N)^2 / zetaTwo * (1/(k : ℝ)^2) := by
  by_cases hk : k = 0
  · simp [hk, quarticEnergyTerm]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    rw [quarticEnergyTerm, residual_head N k hkpos hkN]
    field_simp [hkR, ne_of_gt zetaTwo_pos]

theorem residual_quartic_head_le (N : ℕ) :
    (∑ k ∈ Finset.range (N+1), quarticEnergyTerm (residual N) k) ≤
      (mobiusReciprocalSum N)^2 := by
  have hZ := zetaTwo_pos
  have hs2 : Summable (fun k : ℕ => 1/(k : ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))
  have hweights : (∑ k ∈ Finset.range (N+1), 1/(k : ℝ)^2) ≤ zetaTwo := by
    rw [zetaTwo_eq_nat_sum]
    exact Summable.sum_le_tsum _ (fun k _ => by positivity) hs2
  calc
    _ = ((mobiusReciprocalSum N)^2 / zetaTwo) *
        ∑ k ∈ Finset.range (N+1), 1/(k : ℝ)^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      exact residual_quartic_head_eq N k (by have := Finset.mem_range.mp hk; omega)
    _ ≤ ((mobiusReciprocalSum N)^2 / zetaTwo) * zetaTwo :=
      mul_le_mul_of_nonneg_left hweights (by positivity)
    _ = _ := div_mul_cancel₀ _ (ne_of_gt zetaTwo_pos)

theorem residual_quartic_tail_le (N : ℕ) (hN : 0 < N) :
    (∑' j : ℕ, quarticEnergyTerm (residual N) (j+N+1)) ≤
      1 / (3*zetaTwo*(N : ℝ)) := by
  have hZ := zetaTwo_pos
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  have hsE := (summable_nat_add_iff (N+1)).mpr (residual_quartic_summable N hN)
  have hs40 : Summable (fun k : ℕ => 1/(k : ℝ)^4) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (4 : ℕ))
  have hs4 : Summable (fun j : ℕ => 1/((j+N+1 : ℕ) : ℝ)^4) := by
    simpa only [Nat.add_assoc] using (summable_nat_add_iff (N+1)).mpr hs40
  have hsE' : Summable (fun j : ℕ => quarticEnergyTerm (residual N) (j+N+1)) := by
    simpa only [Nat.add_assoc] using hsE
  calc
    _ ≤ ∑' j : ℕ, ((N : ℝ)^2 / zetaTwo) * (1/((j+N+1 : ℕ) : ℝ)^4) := by
      apply Summable.tsum_le_tsum _ hsE' (hs4.mul_left _)
      intro j
      have hr : (residual N (j+N+1))^2 ≤ (N : ℝ)^2 := by
        have hb := mul_self_le_mul_self (abs_nonneg (residual N (j+N+1)))
          (residual_abs_le N (j+N+1) hN)
        simpa only [← pow_two, sq_abs] using hb
      unfold quarticEnergyTerm
      calc
        _ ≤ (N : ℝ)^2 / (zetaTwo*((j+N+1 : ℕ) : ℝ)^4) :=
          div_le_div_of_nonneg_right hr (by positivity)
        _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev, one_mul]; ring
    _ = ((N : ℝ)^2 / zetaTwo) *
        ∑' j : ℕ, 1/((j+N+1 : ℕ) : ℝ)^4 := by rw [tsum_mul_left]
    _ ≤ ((N : ℝ)^2 / zetaTwo) * (1/(3*(N : ℝ)^3)) :=
      mul_le_mul_of_nonneg_left (quartic_tail_tsum_le N hN) (by positivity)
    _ = _ := by field_simp [hN0, ne_of_gt zetaTwo_pos]

/-- Full unconditional Möbius trial floor bound. Both the exact head charge and
the complete quartic tail are present. No PNT or RH hypothesis occurs. -/
theorem residual_quarticEnergy_le (N : ℕ) (hN : 0 < N) :
    quarticEnergy (residual N) ≤
      (mobiusReciprocalSum N)^2 + 1/(3*zetaTwo*(N : ℝ)) := by
  have hs := residual_quartic_summable N hN
  have he := hs.sum_add_tsum_nat_add (N+1)
  have hh := residual_quartic_head_le N
  have ht := residual_quartic_tail_le N hN
  simp only [← Nat.add_assoc] at he
  unfold quarticEnergy
  linarith

/-- A finite coefficient error in the original squarefree atom dictionary.
The d=1 atom is zero, so including it does not enlarge the trial space. -/
def coefficientResidual (N : ℕ) (c : ℕ → ℝ) (k : ℕ) : ℝ :=
  1 - ∑ d ∈ Finset.Icc 1 N, c d * residueFraction d k

/-- Variational quartic floor over squarefree coefficients at stage N. -/
def squarefreeQuarticFloor (N : ℕ) : ℝ :=
  sInf {E : ℝ | ∃ c : ℕ → ℝ,
    (∀ d, ¬ Squarefree d → c d = 0) ∧ E = quarticEnergy (coefficientResidual N c)}

theorem squarefreeQuarticFloor_nonneg (N : ℕ) : 0 ≤ squarefreeQuarticFloor N := by
  apply le_csInf
  · refine ⟨quarticEnergy (coefficientResidual N (fun _ => 0)), ?_⟩
    exact ⟨(fun _ => 0), (by simp), rfl⟩
  · rintro E ⟨c, hc, rfl⟩
    exact tsum_nonneg (quarticEnergyTerm_nonneg _)

/-- The genuine Möbius trial is admissible in the original squarefree space. -/
theorem squarefreeQuarticFloor_le_trialEnergy (N : ℕ) :
    squarefreeQuarticFloor N ≤ quarticEnergy (residual N) := by
  have htrial : coefficientResidual N (fun d => -(ArithmeticFunction.moebius d : ℝ)) =
      residual N := by
    funext k
    simp only [coefficientResidual, residual, neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add]
  have hbd : BddBelow {E : ℝ | ∃ c : ℕ → ℝ,
      (∀ d, ¬ Squarefree d → c d = 0) ∧ E = quarticEnergy (coefficientResidual N c)} := by
    refine ⟨0, ?_⟩
    rintro E ⟨c, hc, rfl⟩
    exact tsum_nonneg (quarticEnergyTerm_nonneg _)
  have hmem : quarticEnergy (residual N) ∈ {E : ℝ | ∃ c : ℕ → ℝ,
      (∀ d, ¬ Squarefree d → c d = 0) ∧ E = quarticEnergy (coefficientResidual N c)} := by
    refine ⟨(fun d => -(ArithmeticFunction.moebius d : ℝ)), ?_, ?_⟩
    · intro d hd
      simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd]
    · rw [htrial]
  exact csInf_le hbd hmem

/-- Concrete specialization of the trial bound to the actual squarefree
variational floor. Möbius coefficients vanish on every nonsquarefree conductor. -/
theorem squarefreeQuarticFloor_le (N : ℕ) (hN : 0 < N) :
    squarefreeQuarticFloor N ≤
      (mobiusReciprocalSum N)^2 + 1/(3*zetaTwo*(N : ℝ)) :=
  (squarefreeQuarticFloor_le_trialEnergy N).trans (residual_quarticEnergy_le N hN)

end RiemannResearch.RH.Pareto.ZetaTwoMobiusFloor
