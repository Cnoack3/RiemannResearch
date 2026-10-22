/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.RH.QDivisorDPPArithmeticWindows
import RiemannResearch.RH.QDivisorDPP
import RiemannResearch.RH.QDivisorDPPWindows
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QDivisorWaveletBounds
import RiemannResearch.Probability.DeterminantalWindowBudgets
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
/-!
# Arithmetic occupation bounds and far moving windows of the Q divisor DPP

Source: user-provided moving-window analysis, Sections 3 and 5.
The exact diagonal, rough-sector identity, and Möbius mass identity precede
their inequalities and limits. The distant-window limit assumes only its
explicit geometric budget. No RH or sine-limit provider is assumed.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QDivisorDPP
open ZetaTwoHilbert ZetaTwoProbability QDivisorHilbert
theorem basisKernel_arithmetic_diagonal (N i : ℕ) :
    basisKernel N i i = qWeight i * ∑ r : Fin N,
      qDivisorWavelet (basisIndex r : ℕ) (i + 1) ^ 2 / qJordanTwo (basisIndex r : ℕ) := by
  rw [basisKernel_arithmetic_sum, ← pow_two, Real.sq_sqrt (qWeight_pos i).le]
  simp only [pow_two]
theorem basisKernel_diagonal_le (N i : ℕ) :
    basisKernel N i i ≤ qWeight i * ((N : ℝ) * (N + 1) * (2 * N + 1) / 6) := by
  have hex : basisKernel N i i = qWeight i *
      ∑ r : Fin N, qDivisorWavelet (basisIndex r : ℕ) (i + 1) ^ 2 /
        qJordanTwo (basisIndex r : ℕ) := by
    rw [basisKernel_arithmetic_sum]
    rw [← pow_two, Real.sq_sqrt (qWeight_pos i).le]
    simp only [pow_two]
  rw [hex]
  apply mul_le_mul_of_nonneg_left _ (qWeight_pos i).le
  calc
    _ ≤ ∑ r : Fin N, ((r : ℝ) + 1) ^ 2 := by
      apply Finset.sum_le_sum
      intro r _
      simpa [basisIndex, Nat.cast_add, Nat.cast_one] using
        qDivisorWavelet_energy_le_sq (basisIndex r : ℕ)
          (ne_of_gt (basisIndex r).pos) ⟨i + 1, Nat.succ_pos i⟩
    _ = _ := by
      rw [Fin.sum_univ_eq_sum_range (fun r : ℕ => ((r : ℝ) + 1) ^ 2) N]
      clear hex
      induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        ring


theorem basisKernel_same_signature_one (N i : ℕ)
    (h : sameDivisorSignature N (i + 1) 1) :
    basisKernel N i i = basisKernel N 0 0 / ((i + 1 : ℕ) : ℝ) ^ 2 := by
  have he (r : Fin N) : qDivisorWavelet (basisIndex r : ℕ) (i + 1) =
      qDivisorWavelet (basisIndex r : ℕ) 1 :=
    qDivisorWavelet_eq_of_same_signature h (basisIndex r).pos
      (by change (r : ℕ) + 1 ≤ N; exact Nat.succ_le_of_lt r.isLt)
  rw [basisKernel_arithmetic_diagonal N i, basisKernel_arithmetic_diagonal N 0]
  simp only [zero_add]
  simp_rw [he]
  have hZ : zetaTwo ≠ 0 := ne_of_gt zetaTwo_pos
  have hn : ((i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold qWeight positiveQWeight
  norm_num
  field_simp [hZ, hn]
theorem basisKernel_rough_le (N i : ℕ)
    (h : sameDivisorSignature N (i + 1) 1) :
    basisKernel N i i ≤ 1 / ((i + 1 : ℕ) : ℝ) ^ 2 := by
  rw [basisKernel_same_signature_one N i h]
  exact div_le_div_of_nonneg_right ((basisLaw_isDPP N).diagonal_bounds 0).2 (sq_nonneg _)
theorem prime_same_signature_one (N p : ℕ) (hp : p.Prime) (hNp : N < p) :
    sameDivisorSignature N p 1 := by
  intro d hdpos hdN
  constructor
  · intro hd
    rcases hp.eq_one_or_self_of_dvd d hd with rfl | rfl
    · exact dvd_refl 1
    · omega
  · intro hd
    have he := Nat.eq_one_of_dvd_one hd
    subst d
    exact one_dvd p
theorem basisKernel_prime_above_le (N p : ℕ) (hp : p.Prime) (hNp : N < p) :
    basisKernel N (p - 1) (p - 1) ≤ 1 / (p : ℝ) ^ 2 := by
  have hn : p - 1 + 1 = p := Nat.sub_add_cancel hp.pos
  simpa only [hn] using basisKernel_rough_le N (p - 1)
    (by rw [hn]; exact prime_same_signature_one N p hp hNp)
theorem qDivisorWavelet_one_value (r : ℕ) (hr : r ≠ 0) :
    qDivisorWavelet r 1 = (ArithmeticFunction.moebius r : ℝ) := by
  unfold qDivisorWavelet qScaledDivisibilitySum
  rw [Finset.sum_eq_single 1]
  · simp
  · intro d hd hdne
    have hn : ¬d ∣ 1 := fun h => hdne (Nat.eq_one_of_dvd_one h)
    simp [hn]
  · intro h
    exact (h (Nat.one_mem_divisors.mpr hr)).elim
def roughConductorMass (N : ℕ) : ℝ :=
  ∑ r : Fin N, (ArithmeticFunction.moebius (basisIndex r : ℕ) : ℝ) ^ 2 /
    qJordanTwo (basisIndex r : ℕ)
theorem roughConductorMass_eq (N : ℕ) :
    roughConductorMass N = zetaTwo * basisKernel N 0 0 := by
  rw [basisKernel_arithmetic_diagonal]
  simp only [zero_add]
  simp_rw [qDivisorWavelet_one_value _ (ne_of_gt (basisIndex _).pos)]
  unfold roughConductorMass qWeight positiveQWeight
  norm_num
  field_simp [ne_of_gt zetaTwo_pos]
theorem roughConductorMass_tendsto :
    Tendsto roughConductorMass atTop (𝓝 zetaTwo) := by
  have ht := (basisKernel_tendsto 0 0).const_mul zetaTwo
  simpa [← roughConductorMass_eq] using ht

theorem qWeight_le_of_location (i : ℕ) (x : ℝ) (hx : 0 < x)
    (hxi : x ≤ ((i + 1 : ℕ) : ℝ)) :
    qWeight i ≤ 1 / (zetaTwo * x ^ 2) := by
  have hn : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
  have hs : x ^ 2 ≤ (((i + 1 : ℕ) : ℝ)) ^ 2 :=
    (sq_le_sq₀ hx.le hn.le).mpr hxi
  unfold qWeight positiveQWeight
  exact one_div_le_one_div_of_le (mul_pos zetaTwo_pos (sq_pos_of_pos hx))
    (mul_le_mul_of_nonneg_left hs zetaTwo_pos.le)
theorem basisKernel_window_sum_le (N m : ℕ) (e : Fin m → ℕ) (x : ℝ)
    (hx : 0 < x) (hxe : ∀ i, x ≤ ((e i + 1 : ℕ) : ℝ)) :
    (∑ i, basisKernel N (e i) (e i)) ≤
      (m : ℝ) * ((N : ℝ) * (N + 1) * (2 * N + 1) / 6) / (zetaTwo * x ^ 2) := by
  have hC : 0 ≤ ((N : ℝ) * (N + 1) * (2 * N + 1) / 6) := by positivity
  calc
    _ ≤ ∑ i : Fin m, (1 / (zetaTwo * x ^ 2)) * ((N : ℝ) * (N + 1) * (2 * N + 1) / 6) := by
      apply Finset.sum_le_sum
      intro i _
      exact (basisKernel_diagonal_le N (e i)).trans
        (mul_le_mul_of_nonneg_right (qWeight_le_of_location (e i) x hx (hxe i)) hC)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]; ring
theorem conductor_square_budget_le_cube (N : ℕ) :
    ((N : ℝ) * (N + 1) * (2 * N + 1) / 6) ≤ (N : ℝ) ^ 3 := by
  by_cases hN : N = 0
  · subst N
    norm_num
  · have hn : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
    have hp : 0 ≤ (N : ℝ) * ((N : ℝ) - 1) * (4 * (N : ℝ) + 1) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (by positivity)
    nlinarith
theorem basisLaw_far_window_gap_tendsto (m : ℕ → ℕ)
    (e : (N : ℕ) → Fin (m N) ↪ ℕ) (x : ℕ → ℝ)
    (hx : ∀ N, 0 < x N)
    (hxe : ∀ N i, x N ≤ ((e N i + 1 : ℕ) : ℝ))
    (hb : Tendsto (fun N => (m N : ℝ) * (N : ℝ) ^ 3 / (x N) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun N => (basisLaw N).real {ω | ∀ i, ω (e N i) = false})
      atTop (𝓝 1) := by
  have hk : Tendsto (fun N => ∑ i, basisKernel N (e N i) (e N i)) atTop (𝓝 0) := by
    have ht : Tendsto (fun N => ((m N : ℝ) * (N : ℝ) ^ 3 / (x N) ^ 2) / zetaTwo)
        atTop (𝓝 0) := by simpa using hb.div_const zetaTwo
    apply squeeze_zero _ _ ht
    · intro N
      exact Finset.sum_nonneg (fun i _ => ((basisLaw_isDPP N).diagonal_bounds (e N i)).1)
    · intro N
      calc
        _ ≤ (m N : ℝ) * ((N : ℝ) * (N + 1) * (2 * N + 1) / 6) / (zetaTwo * (x N) ^ 2) :=
          basisKernel_window_sum_le N (m N) (e N) (x N) (hx N) (hxe N)
        _ ≤ (m N : ℝ) * (N : ℝ) ^ 3 / (zetaTwo * (x N) ^ 2) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (conductor_square_budget_le_cube N) (Nat.cast_nonneg _))
            (mul_nonneg zetaTwo_pos.le (sq_nonneg _))
        _ = _ := by ring
  have h := RiemannResearch.Probability.DPP.moving_window_gap_tendsto
    basisLaw (fun _ ω => {i | ω i = true}) basisKernel basisLaw_isDPP m (fun N => e N) hk
  simpa using h
end RiemannResearch.RH.QDivisorDPP
