/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.EuclideanHilbertSchmidt
import RiemannResearch.Analysis.ActualLandauOperatorResidual
import RiemannResearch.Analysis.ActualHyperbolicGramLowerBounds
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual Landau residual: finite Hilbert--Schmidt assembly

The complete signed actual residual retains its arithmetic main. The existing
unconditional rational Landau provider is assembled through squared-entry
certificates, improving support to the leading budget d^3/((T+3)*log(T+3))->0.
The exact complex entry partition precedes all norm estimates. No analytic
density premise is introduced. Proof: independent finite assembly of the
repository's actual rational contour provider; see
`../RH/LandauHilbertSchmidt20261005.md` for provenance and scope.
-/
noncomputable section
open Complex Zeta23
open scoped BigOperators InnerProductSpace Matrix



namespace RiemannResearch.Analysis.LandauHilbertSchmidt

def entryEnvelopePart (z : ℂ) (a b c : ℝ) : ℂ :=
  z * ((a / (a + b + c) : ℝ) : ℂ)

theorem norm_entryEnvelopePart_le (z : ℂ) (a b c K : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hz : ‖z‖ ≤ K * (a + b + c)) :
    ‖entryEnvelopePart z a b c‖ ≤ K * a := by
  by_cases hs : a + b + c = 0
  · simp only [entryEnvelopePart, hs, div_zero, Complex.ofReal_zero, mul_zero, norm_zero]
    exact mul_nonneg hK ha
  · have hspos : 0 < a + b + c := lt_of_le_of_ne (by linarith) (Ne.symm hs)
    have hratio : 0 ≤ a / (a + b + c) := div_nonneg ha hspos.le
    rw [entryEnvelopePart, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hratio]
    calc
      _ ≤ (K * (a + b + c)) * (a / (a + b + c)) :=
        mul_le_mul_of_nonneg_right hz hratio
      _ = _ := by field_simp [hs]

theorem entryEnvelopePart_three_eq (z : ℂ) (a b c K : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hz : ‖z‖ ≤ K * (a + b + c)) :
    entryEnvelopePart z a b c + entryEnvelopePart z b a c +
        entryEnvelopePart z c a b = z := by
  by_cases hs : a + b + c = 0
  · have hz0 : z = 0 := norm_eq_zero.mp (le_antisymm (by simpa [hs] using hz) (norm_nonneg _))
    simp [entryEnvelopePart, hz0]
  · have hsC : ((a + b + c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
    push_cast at hsC
    unfold entryEnvelopePart
    push_cast
    have hba : (b : ℂ) + a + c = (a : ℂ) + b + c := by ring
    have hca : (c : ℂ) + a + b = (a : ℂ) + b + c := by ring
    rw [hba, hca]
    field_simp [hsC]

/-- A telescoping finite upper bound, avoiding an infinite zeta-series provider. -/
theorem sum_range_inverse_cube_le (d : ℕ) :
    (∑ m ∈ Finset.range d, (1 : ℝ) / ((m : ℝ) + 1) ^ 3) ≤
      2 - 1 / ((d : ℝ) + 1) := by
  induction d with
  | zero => norm_num
  | succ d ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst d
      norm_num
    · have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have hd1 : (d : ℝ) + 1 ≠ 0 := by positivity
      have hd2 : (d : ℝ) + 2 ≠ 0 := by positivity
      have hstep : (1 : ℝ) / ((d : ℝ) + 1) ^ 3 ≤
          1 / ((d : ℝ) + 1) - 1 / ((d : ℝ) + 2) := by
        have hden : (d : ℝ) + 2 ≤ ((d : ℝ) + 1) ^ 2 := by
          nlinarith [sq_nonneg (d : ℝ)]
        have hden' : ((d : ℝ) + 1) * ((d : ℝ) + 2) ≤
            ((d : ℝ) + 1) ^ 3 := by
          have h := mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ (d : ℝ) + 1)
          nlinarith only [h]
        calc
          _ ≤ 1 / (((d : ℝ) + 1) * ((d : ℝ) + 2)) :=
            one_div_le_one_div_of_le (by positivity) hden'
          _ = _ := by field_simp [hd1, hd2]; ring
      push_cast
      rw [show (d : ℝ) + 1 + 1 = (d : ℝ) + 2 by ring]
      linarith

theorem sum_fin_inverse_cube_le_two (d : ℕ) :
    (∑ m : Fin d, (1 : ℝ) / ((m.val : ℝ) + 1) ^ 3) ≤ 2 := by
  change (∑ m : Fin d, (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1) ^ 3) m.val) ≤ 2
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1) ^ 3) d]
  have h := sum_range_inverse_cube_le d
  have hi : (0 : ℝ) ≤ 1 / ((d : ℝ) + 1) := by positivity
  linarith

theorem sum_fin_pow_le_card_pow (d k : ℕ) :
    (∑ n : Fin d, ((n.val : ℝ) + 1) ^ k) ≤ (d : ℝ) ^ (k + 1) := by
  have hentry (n : Fin d) : ((n.val : ℝ) + 1) ^ k ≤ (d : ℝ) ^ k := by
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast Nat.succ_le_of_lt n.isLt
  calc
    _ ≤ ∑ _n : Fin d, (d : ℝ) ^ k :=
      Finset.sum_le_sum (fun n _ => hentry n)
    _ = _ := by simp [pow_succ, mul_comm]

theorem sum_fin_pow_div_cube_le (d k : ℕ) :
    (∑ n : Fin d, ∑ m : Fin d,
      ((n.val : ℝ) + 1) ^ k / ((m.val : ℝ) + 1) ^ 3) ≤
      2 * (d : ℝ) ^ (k + 1) := by
  have hpow := sum_fin_pow_le_card_pow d k
  have hinv := sum_fin_inverse_cube_le_two d
  have hpow0 : (0 : ℝ) ≤ ∑ n : Fin d, ((n.val : ℝ) + 1) ^ k := by positivity
  calc
    _ = (∑ n : Fin d, ((n.val : ℝ) + 1) ^ k) *
        (∑ m : Fin d, (1 : ℝ) / ((m.val : ℝ) + 1) ^ 3) := by
      symm
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ ≤ (∑ n : Fin d, ((n.val : ℝ) + 1) ^ k) * 2 :=
      mul_le_mul_of_nonneg_left hinv hpow0
    _ ≤ (d : ℝ) ^ (k + 1) * 2 :=
      mul_le_mul_of_nonneg_right hpow (by norm_num)
    _ = _ := by ring

theorem sum_sq_le_sym_power_certificate {d k : ℕ}
    (M : Matrix (Fin d) (Fin d) ℂ)
    (hM : ∀ n m, ‖M n m‖ ^ 2 ≤
      ((n.val : ℝ) + 1) ^ k / ((m.val : ℝ) + 1) ^ 3 +
      ((m.val : ℝ) + 1) ^ k / ((n.val : ℝ) + 1) ^ 3) :
    (∑ n, ∑ m, ‖M n m‖ ^ 2) ≤ 4 * (d : ℝ) ^ (k + 1) := by
  have hbase := sum_fin_pow_div_cube_le d k
  have hbaseSwap : (∑ n : Fin d, ∑ m : Fin d,
      ((m.val : ℝ) + 1) ^ k / ((n.val : ℝ) + 1) ^ 3) ≤
      2 * (d : ℝ) ^ (k + 1) := by
    rw [Finset.sum_comm]
    exact hbase
  calc
    _ ≤ ∑ n : Fin d, ∑ m : Fin d,
        (((n.val : ℝ) + 1) ^ k / ((m.val : ℝ) + 1) ^ 3 +
          ((m.val : ℝ) + 1) ^ k / ((n.val : ℝ) + 1) ^ 3) := by
      apply Finset.sum_le_sum
      intro n hn
      exact Finset.sum_le_sum (fun m _ => hM n m)
    _ = (∑ n : Fin d, ∑ m : Fin d,
        ((n.val : ℝ) + 1) ^ k / ((m.val : ℝ) + 1) ^ 3) +
        (∑ n : Fin d, ∑ m : Fin d,
          ((m.val : ℝ) + 1) ^ k / ((n.val : ℝ) + 1) ^ 3) := by
      simp only [Finset.sum_add_distrib]
    _ ≤ _ := by linarith only [hbase, hbaseSwap]

theorem norm_le_two_card_cube_of_sym_fifth_sq {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℂ)
    (hM : ∀ n m, ‖M n m‖ ^ 2 ≤
      ((n.val : ℝ) + 1) ^ 5 / ((m.val : ℝ) + 1) ^ 3 +
      ((m.val : ℝ) + 1) ^ 5 / ((n.val : ℝ) + 1) ^ 3) :
    ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M‖ ≤ 2 * (d : ℝ) ^ 3 := by
  apply ContinuousLinearMap.norm_toEuclideanCLM_le_of_sum_sq_le M _ (by positivity)
  have h := sum_sq_le_sym_power_certificate M hM
  norm_num at h
  nlinarith only [h]

theorem norm_le_two_card_sq_of_sym_cube_sq {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℂ)
    (hM : ∀ n m, ‖M n m‖ ^ 2 ≤
      ((n.val : ℝ) + 1) ^ 3 / ((m.val : ℝ) + 1) ^ 3 +
      ((m.val : ℝ) + 1) ^ 3 / ((n.val : ℝ) + 1) ^ 3) :
    ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M‖ ≤ 2 * (d : ℝ) ^ 2 := by
  apply ContinuousLinearMap.norm_toEuclideanCLM_le_of_sum_sq_le M _ (by positivity)
  have h := sum_sq_le_sym_power_certificate M hM
  norm_num at h
  nlinarith only [h]

/-- Three positive envelope proportions of an arbitrary complex matrix.
Only the finite entry bound is consumed; no phase, sign, or conductor is removed.
The last term uses the existing crude entry bound, already sufficient for 1/3. -/
theorem norm_three_envelope_assembly {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℂ)
    (A B D : Fin d → Fin d → ℝ) (K L : ℝ)
    (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hA : ∀ n m, 0 ≤ A n m) (hB : ∀ n m, 0 ≤ B n m)
    (hD : ∀ n m, 0 ≤ D n m)
    (hAsq : (∑ n, ∑ m, A n m ^ 2) ≤ (2 * (d : ℝ) ^ 3) ^ 2)
    (hBsq : (∑ n, ∑ m, B n m ^ 2) ≤ (2 * (d : ℝ) ^ 2) ^ 2)
    (hDle : ∀ n m, D n m ≤ 3 * (d : ℝ))
    (hM : ∀ n m, ‖M n m‖ ≤ K * (A n m + L ^ 2 * B n m + L * D n m)) :
    ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M‖ ≤
      K * (2 * (d : ℝ) ^ 3 + 2 * (d : ℝ) ^ 2 * L ^ 2 +
        3 * (d : ℝ) ^ 2 * L) := by
  let MA : Matrix (Fin d) (Fin d) ℂ := fun n m =>
    entryEnvelopePart (M n m) (A n m) (L ^ 2 * B n m) (L * D n m)
  let MB : Matrix (Fin d) (Fin d) ℂ := fun n m =>
    entryEnvelopePart (M n m) (L ^ 2 * B n m) (A n m) (L * D n m)
  let MD : Matrix (Fin d) (Fin d) ℂ := fun n m =>
    entryEnvelopePart (M n m) (L * D n m) (A n m) (L ^ 2 * B n m)
  have hMA (n m : Fin d) : ‖MA n m‖ ≤ K * A n m :=
    norm_entryEnvelopePart_le _ _ _ _ _ (hA n m)
      (mul_nonneg (sq_nonneg L) (hB n m)) (mul_nonneg hL (hD n m)) hK (hM n m)
  have hMB (n m : Fin d) : ‖MB n m‖ ≤ (K * L ^ 2) * B n m := by
    have hm : ‖M n m‖ ≤ K * (L ^ 2 * B n m + A n m + L * D n m) := by
      nlinarith only [hM n m]
    have hb := norm_entryEnvelopePart_le (M n m) (L ^ 2 * B n m)
      (A n m) (L * D n m) K (mul_nonneg (sq_nonneg L) (hB n m)) (hA n m)
      (mul_nonneg hL (hD n m)) hK hm
    dsimp [MB]
    nlinarith only [hb]
  have hMD (n m : Fin d) : ‖MD n m‖ ≤ K * L * (3 * (d : ℝ)) := by
    have hm : ‖M n m‖ ≤ K * (L * D n m + A n m + L ^ 2 * B n m) := by
      nlinarith only [hM n m]
    have hd := norm_entryEnvelopePart_le (M n m) (L * D n m)
      (A n m) (L ^ 2 * B n m) K (mul_nonneg hL (hD n m))
      (hA n m) (mul_nonneg (sq_nonneg L) (hB n m)) hK hm
    have hd' := mul_le_mul_of_nonneg_left (hDle n m) (mul_nonneg hK hL)
    dsimp [MD]
    nlinarith only [hd, hd']
  have hdecomp : M = MA + MB + MD := by
    ext n m
    exact (entryEnvelopePart_three_eq (M n m) (A n m)
      (L ^ 2 * B n m) (L * D n m) K (hA n m)
      (mul_nonneg (sq_nonneg L) (hB n m)) (mul_nonneg hL (hD n m)) (hM n m)).symm
  have hNA := ContinuousLinearMap.norm_toEuclideanCLM_le_scaled_envelope
    MA A K (2 * (d : ℝ) ^ 3) hK (by positivity) hA hMA hAsq
  have hNB := ContinuousLinearMap.norm_toEuclideanCLM_le_scaled_envelope
    MB B (K * L ^ 2) (2 * (d : ℝ) ^ 2) (by positivity) (by positivity) hB hMB hBsq
  have hND := ContinuousLinearMap.norm_toEuclideanCLM_le_card_mul
    MD (K * L * (3 * (d : ℝ))) (by positivity) hMD
  rw [hdecomp, map_add, map_add]
  have h1 := norm_add_le
    (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) MA)
    (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) MB)
  have h2 := norm_add_le
    (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) MA +
      Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) MB)
    (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) MD)
  nlinarith only [hNA, hNB, hND, h1, h2]

def reflectUpper {d : ℕ} (U : ℕ → ℕ → ℝ) (n m : Fin d) : ℝ :=
  if m.val < n.val then U (n.val + 1) (m.val + 1)
  else if n.val < m.val then U (m.val + 1) (n.val + 1) else 0

theorem reflectUpper_nonneg {d : ℕ} (U : ℕ → ℕ → ℝ)
    (hU : ∀ n m, 0 ≤ U n m) (n m : Fin d) : 0 ≤ reflectUpper U n m := by
  unfold reflectUpper
  split_ifs <;> first | exact hU _ _ | rfl

theorem reflectUpper_symm {d : ℕ} (U : ℕ → ℕ → ℝ) (n m : Fin d) :
    reflectUpper U n m = reflectUpper U m n := by
  unfold reflectUpper
  split_ifs <;> try omega
  all_goals rfl

def upperPowerEnvelope (k n m : ℕ) : ℝ := Real.sqrt ((n : ℝ) ^ k / (m : ℝ) ^ 3)

theorem upperPowerEnvelope_nonneg (k n m : ℕ) : 0 ≤ upperPowerEnvelope k n m :=
  Real.sqrt_nonneg _

theorem reflectedPowerEnvelope_sq {d : ℕ} (k : ℕ) (n m : Fin d) :
    reflectUpper (upperPowerEnvelope k) n m ^ 2 ≤
      ((n.val : ℝ) + 1) ^ k / ((m.val : ℝ) + 1) ^ 3 +
      ((m.val : ℝ) + 1) ^ k / ((n.val : ℝ) + 1) ^ 3 := by
  unfold reflectUpper upperPowerEnvelope
  split_ifs
  · rw [Real.sq_sqrt (by positivity)]
    push_cast
    have h : (0 : ℝ) ≤ ((m.val : ℝ) + 1) ^ k / ((n.val : ℝ) + 1) ^ 3 := by positivity
    linarith
  · rw [Real.sq_sqrt (by positivity)]
    push_cast
    have h : (0 : ℝ) ≤ ((n.val : ℝ) + 1) ^ k / ((m.val : ℝ) + 1) ^ 3 := by positivity
    linarith
  · norm_num only [zero_pow] <;> positivity

theorem reflectedPowerEnvelope_sum_sq {d : ℕ} (k : ℕ) :
    (∑ n : Fin d, ∑ m : Fin d, reflectUpper (upperPowerEnvelope k) n m ^ 2) ≤
      4 * (d : ℝ) ^ (k + 1) := by
  have h := sum_sq_le_sym_power_certificate
    (fun n m : Fin d => (reflectUpper (upperPowerEnvelope k) n m : ℂ))
    (fun n m => by
      simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using
        reflectedPowerEnvelope_sq k n m)
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

def upperGapEnvelope (n m : ℕ) : ℝ := 1 + 1 / |Real.log ((n : ℝ) / (m : ℝ))|

theorem upperGapEnvelope_nonneg (n m : ℕ) : 0 ≤ upperGapEnvelope n m := by
  unfold upperGapEnvelope
  positivity

theorem reflectUpper_gap_le_card {d : ℕ} (n m : Fin d) :
    reflectUpper upperGapEnvelope n m ≤ 3 * (d : ℝ) := by
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_of_lt n.isLt
  unfold reflectUpper
  split_ifs with hmn hnm
  · obtain ⟨hu, _, hinv, _⟩ :=
      RiemannResearch.Analysis.ActualZeroOrdinate.rational_frequency_bounds
        (m := m.val + 1) (n := n.val + 1) (by omega) (by omega)
        (X := (d : ℝ)) (by exact_mod_cast Nat.succ_le_of_lt n.isLt)
    unfold upperGapEnvelope
    rw [abs_of_pos hu]
    linarith
  · obtain ⟨hu, _, hinv, _⟩ :=
      RiemannResearch.Analysis.ActualZeroOrdinate.rational_frequency_bounds
        (m := n.val + 1) (n := m.val + 1) (by omega) (by omega)
        (X := (d : ℝ)) (by exact_mod_cast Nat.succ_le_of_lt m.isLt)
    unfold upperGapEnvelope
    rw [abs_of_pos hu]
    linarith
  · positivity

theorem exp_three_half_log_sq {x : ℝ} (hx : 0 < x) :
    (Real.exp (3 * Real.log x / 2)) ^ 2 = x ^ 3 := by
  calc
    _ = Real.exp (3 * Real.log x / 2 + 3 * Real.log x / 2) := by
      rw [Real.exp_add]
      ring
    _ = Real.exp (3 * Real.log x) := by congr 1; ring
    _ = Real.exp (Real.log x) ^ 3 := by
      simpa only [Nat.cast_ofNat] using Real.exp_nat_mul (Real.log x) 3
    _ = _ := by rw [Real.exp_log hx]

theorem upperPowerEnvelope_cube_eq_exp {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    upperPowerEnvelope 3 n m =
      Real.exp (3 * Real.log ((n : ℝ) / (m : ℝ)) / 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  apply (sq_eq_sq₀ (upperPowerEnvelope_nonneg 3 n m) (Real.exp_pos _).le).mp
  rw [upperPowerEnvelope, Real.sq_sqrt (by positivity),
    exp_three_half_log_sq (div_pos hnR hmR), div_pow]

theorem upperPowerEnvelope_fifth_eq_exp_mul {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    upperPowerEnvelope 5 n m =
      Real.exp (3 * Real.log ((n : ℝ) / (m : ℝ)) / 2) * (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  apply (sq_eq_sq₀ (upperPowerEnvelope_nonneg 5 n m) (by positivity)).mp
  rw [upperPowerEnvelope, Real.sq_sqrt (by positivity), mul_pow,
    exp_three_half_log_sq (div_pos hnR hmR), div_pow]
  ring

end RiemannResearch.Analysis.LandauHilbertSchmidt

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open ActualZeroOrdinate ZeroOrdinate RiemannResearch.Analysis.LandauHilbertSchmidt
open ContinuousLinearMap

/-- Improved finite actual signed residual bound, from the already proved
nonmaxed actual rational Landau provider. Every matrix entry is retained. -/
theorem exists_actualLandauResidual_hilbertSchmidt_norm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ) (d : ℕ),
      9 ≤ T → 0 < Zeta23.Ncount 0 T →
      ‖actualLandauResidual T d‖ ≤ C / (Zeta23.Ncount 0 T : ℝ) *
        (2 * (d : ℝ) ^ 3 + 2 * (d : ℝ) ^ 2 * Real.log (T + 3) ^ 2 +
          3 * (d : ℝ) ^ 2 * Real.log (T + 3)) := by
  obtain ⟨C, hC, hscalar⟩ := exists_uniform_rational_landau_bound
  refine ⟨C, hC, ?_⟩
  intro T d hT hN
  let A : Fin d → Fin d → ℝ := reflectUpper (upperPowerEnvelope 5)
  let B : Fin d → Fin d → ℝ := reflectUpper (upperPowerEnvelope 3)
  let D : Fin d → Fin d → ℝ := reflectUpper upperGapEnvelope
  let L : ℝ := Real.log (T + 3)
  let K : ℝ := C / (Zeta23.Ncount 0 T : ℝ)
  let M : Matrix (Fin d) (Fin d) ℂ := fun n m => euclideanEntry (actualLandauResidual T d) n m
  have hNr : (0 : ℝ) < Zeta23.Ncount 0 T := by exact_mod_cast hN
  have hL : 0 ≤ L := Real.log_nonneg (by linarith)
  have hK : 0 ≤ K := div_nonneg hC.le hNr.le
  have hupper (n m : Fin d) (hmn : m.val < n.val) :
      ‖M n m‖ ≤ K * (A n m + L ^ 2 * B n m + L * D n m) := by
    have hb := hscalar T (n.val + 1) (m.val + 1) hT (by omega) (by omega)
    have hu := (rational_frequency_bounds (m := m.val + 1) (n := n.val + 1)
      (by omega) (by omega) (le_refl ((n.val + 1 : ℕ) : ℝ))).1
    dsimp [M]
    rw [actualLandauResidual_entry_of_lt T d hN n m hmn,
      norm_mul, norm_inv, Complex.norm_natCast]
    have hm : ¬ n.val < m.val := by omega
    dsimp [A, B, D]
    simp only [reflectUpper, if_pos hmn]
    rw [upperPowerEnvelope_fifth_eq_exp_mul (by omega) (by omega),
      upperPowerEnvelope_cube_eq_exp (by omega) (by omega)]
    unfold upperGapEnvelope
    rw [abs_of_pos hu]
    dsimp [K, L]
    have hs := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (Zeta23.Ncount 0 T : ℝ)⁻¹)
    calc
      _ ≤ _ := hs
      _ = _ := by ring
  have hentry (n m : Fin d) :
      ‖M n m‖ ≤ K * (A n m + L ^ 2 * B n m + L * D n m) := by
    rcases lt_trichotomy m.val n.val with hmn | heq | hnm
    · exact hupper n m hmn
    · have h : n = m := Fin.ext heq.symm
      subst n
      simp [M, actualLandauResidual_entry_diag T d hN, A, B, D, reflectUpper]
    · have hsymA : A n m = A m n := reflectUpper_symm _ _ _
      have hsymB : B n m = B m n := reflectUpper_symm _ _ _
      have hsymD : D n m = D m n := reflectUpper_symm _ _ _
      dsimp [M]
      rw [actualLandauResidual_entry_star T d n m, norm_star, hsymA, hsymB, hsymD]
      exact hupper m n hnm
  have hAsq : (∑ n, ∑ m, A n m ^ 2) ≤ (2 * (d : ℝ) ^ 3) ^ 2 := by
    have hs := reflectedPowerEnvelope_sum_sq (d := d) 5
    norm_num at hs
    dsimp [A]
    nlinarith only [hs]
  have hBsq : (∑ n, ∑ m, B n m ^ 2) ≤ (2 * (d : ℝ) ^ 2) ^ 2 := by
    have hs := reflectedPowerEnvelope_sum_sq (d := d) 3
    norm_num at hs
    dsimp [B]
    nlinarith only [hs]
  have hbound := norm_three_envelope_assembly M A B D K L hK hL
    (reflectUpper_nonneg _ (upperPowerEnvelope_nonneg 5))
    (reflectUpper_nonneg _ (upperPowerEnvelope_nonneg 3))
    (reflectUpper_nonneg _ upperGapEnvelope_nonneg) hAsq hBsq
    reflectUpper_gap_le_card hentry
  have hrealize : actualLandauResidual T d = Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M := by
    apply euclideanEntry_ext
    intro n m
    exact (euclideanEntry_toEuclideanCLM M n m).symm
  rw [hrealize]
  exact hbound

end RiemannResearch.Analysis.ActualZeroPhaseMoments

namespace RiemannResearch.Analysis.LandauHilbertSchmidt
open Filter

def normalizedHSEnvelope (L ell : ℝ) : ℝ :=
  2 * Real.exp (3 * ell - L) / L +
    2 * L * Real.exp (2 * ell - L) + 3 * Real.exp (2 * ell - L)

theorem normalizedHSEnvelope_mono {L a b : ℝ} (hL : 0 < L) (hab : a ≤ b) :
    normalizedHSEnvelope L a ≤ normalizedHSEnvelope L b := by
  unfold normalizedHSEnvelope
  have h3 : Real.exp (3 * a - L) ≤ Real.exp (3 * b - L) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (2 * a - L) ≤ Real.exp (2 * b - L) :=
    Real.exp_le_exp.mpr (by linarith)
  gcongr

theorem normalizedHSEnvelope_critical_eq (a : ℝ) {L : ℝ} (hL : 0 < L) :
    normalizedHSEnvelope L (a + L / 3) =
      (2 * Real.exp (3 * a)) / L +
        (2 * Real.exp (2 * a)) * (L * Real.exp (-L / 3)) +
        (3 * Real.exp (2 * a)) * Real.exp (-L / 3) := by
  unfold normalizedHSEnvelope
  rw [show 3 * (a + L / 3) - L = 3 * a by ring,
    show 2 * (a + L / 3) - L = 2 * a + (-L / 3) by ring,
    Real.exp_add]
  ring

theorem normalizedHSEnvelope_critical_tendsto_zero (a : ℝ) :
    Tendsto (fun L : ℝ => normalizedHSEnvelope L (a + L / 3))
      atTop (nhds 0) := by
  have hinv : Tendsto (fun L : ℝ => (2 * Real.exp (3 * a)) / L)
      atTop (nhds 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hscale : Tendsto (fun L : ℝ => L / 3) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num)
  have hp₁ := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale).const_mul (3 : ℝ)
  have h₁ : Tendsto (fun L : ℝ => L * Real.exp (-L / 3)) atTop (nhds 0) := by
    convert hp₁ using 1
    · funext L
      change L * Real.exp (-L / 3) = 3 * ((L / 3) ^ 1 * Real.exp (-(L / 3)))
      simp only [pow_one]
      rw [show -(L / 3) = -L / 3 by ring]
      ring
    · norm_num
  have hp₀ := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp hscale
  have h₀ : Tendsto (fun L : ℝ => Real.exp (-L / 3)) atTop (nhds 0) := by
    convert hp₀ using 1
    funext L
    simp only [pow_zero, one_mul]
    congr 1
    ring
  have hsum := (hinv.add (h₁.const_mul (2 * Real.exp (2 * a)))).add
    (h₀.const_mul (3 * Real.exp (2 * a)))
  norm_num at hsum
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  exact (normalizedHSEnvelope_critical_eq a hL).symm

theorem normalizedHSEnvelope_eq {Y d : ℝ} (hY : 0 < Y) (hd : 0 < d)
    (hL : 0 < Real.log Y) :
    normalizedHSEnvelope (Real.log Y) (Real.log d) =
      (2 * d ^ 3 + 2 * d ^ 2 * (Real.log Y) ^ 2 + 3 * d ^ 2 * Real.log Y) /
        (Y * Real.log Y) := by
  have he3 : Real.exp (3 * Real.log d) = d ^ 3 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hd] using Real.exp_nat_mul (Real.log d) 3
  have he2 : Real.exp (2 * Real.log d) = d ^ 2 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hd] using Real.exp_nat_mul (Real.log d) 2
  unfold normalizedHSEnvelope
  rw [Real.exp_sub, Real.exp_sub, he3, he2, Real.exp_log hY]
  field_simp [hY.ne', hL.ne']

end RiemannResearch.Analysis.LandauHilbertSchmidt

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open Filter Zeta23 ActualZeroOrdinate RiemannResearch.Analysis.LandauHilbertSchmidt

/-- Unconditional 1/3 endpoint support for the complete actual signed residual. -/
theorem actualLandauResidual_norm_tendsto_zero_one_third_support
    (d : ℝ → ℕ) (a : ℝ)
    (hsupport : ∀ᶠ T : ℝ in atTop,
      1 ≤ d T ∧ Real.log (d T : ℝ) ≤ a + Real.log (T + 3) / 3) :
    Tendsto (fun T : ℝ => ‖actualLandauResidual T (d T)‖) atTop (nhds 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_actualLandauResidual_hilbertSchmidt_norm_bound
  let q : ℝ := 1 / (64 * Real.pi)
  have hq : 0 < q := by dsimp [q]; positivity
  have hplus : Tendsto (fun T : ℝ => T + 3) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with T hT
    linarith
  have hlog := Real.tendsto_log_atTop.comp hplus
  have hmajor : Tendsto (fun T : ℝ => (C / q) *
      normalizedHSEnvelope (Real.log (T + 3)) (a + Real.log (T + 3) / 3))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((normalizedHSEnvelope_critical_tendsto_zero a).const_mul (C / q)).comp hlog
  apply squeeze_zero'
  · exact Eventually.of_forall (fun T => norm_nonneg _)
  · filter_upwards [eventually_count_ge_height_add_three_log,
      eventually_ge_atTop (9 : ℝ), hsupport] with T hNheight hT hs
    have hY : 0 < T + 3 := by linarith
    have hLpos : 0 < Real.log (T + 3) := Real.log_pos (by linarith)
    change q * (T + 3) * Real.log (T + 3) ≤ (Ncount 0 T : ℝ) at hNheight
    have hNr : (0 : ℝ) < (Ncount 0 T : ℝ) := lt_of_lt_of_le (by positivity) hNheight
    have hN : 0 < Ncount 0 T := by exact_mod_cast hNr
    have hd : (0 : ℝ) < (d T : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hs.1)
    have henv : 0 ≤ 2 * (d T : ℝ) ^ 3 + 2 * (d T : ℝ) ^ 2 * Real.log (T + 3) ^ 2 +
        3 * (d T : ℝ) ^ 2 * Real.log (T + 3) := by positivity
    calc
      _ ≤ _ := hbound T (d T) hT hN
      _ = C * (2 * (d T : ℝ) ^ 3 + 2 * (d T : ℝ) ^ 2 * Real.log (T + 3) ^ 2 +
          3 * (d T : ℝ) ^ 2 * Real.log (T + 3)) / (Ncount 0 T : ℝ) := by ring
      _ ≤ C * (2 * (d T : ℝ) ^ 3 + 2 * (d T : ℝ) ^ 2 * Real.log (T + 3) ^ 2 +
          3 * (d T : ℝ) ^ 2 * Real.log (T + 3)) /
          (q * (T + 3) * Real.log (T + 3)) :=
        div_le_div_of_nonneg_left (mul_nonneg hC.le henv) (by positivity) hNheight
      _ = (C / q) * normalizedHSEnvelope (Real.log (T + 3)) (Real.log (d T : ℝ)) := by
        rw [normalizedHSEnvelope_eq hY hd hLpos]
        field_simp [hq.ne', hY.ne', hLpos.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left (normalizedHSEnvelope_mono hLpos hs.2) (by positivity)
  · exact hmajor

end RiemannResearch.Analysis.ActualZeroPhaseMoments

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open Filter ActualZeroOrdinate ZeroOrdinate
local instance hsCopiesDecidableEq (T : ℝ) : DecidableEq (Copies T) := Classical.decEq _

/-- The full actual hyperbolic Gram has every lower coefficient h<1-theta
at support theta<=1/3. The complete signed arithmetic main is retained. -/
theorem eventually_landauGram_lower_power_support_one_third
    (d : ℝ → ℕ) (a θ h : ℝ) (hθ : 0 ≤ θ) (hθmax : θ ≤ 1/3)
    (hh : h < 1-θ)
    (hsupport : ∀ᶠ T : ℝ in atTop,
      1 ≤ d T ∧ Real.log (d T : ℝ) ≤ a+θ*Real.log (T+3)) :
    ∀ᶠ T : ℝ in atTop, ∀ f : Space (d T),
      h*‖f‖^2 ≤ (inner ℂ f (landauGram T (d T) f)).re := by
  let η : ℝ := 1-θ-h
  have hη : 0 < η := by dsimp [η]; linarith
  let r : ℝ := 1+η/(2*(θ+1))
  have hθone : 0 < θ+1 := by linarith
  have hr : 1 < r := by
    have hp : 0 < η/(2*(θ+1)) := div_pos hη (by positivity)
    dsimp [r]
    linarith
  have hr0 : 0 < r := by linarith
  have hrθ : r*θ ≤ θ+η/2 := by
    have heq : (r-1)*(2*(θ+1)) = η := by
      dsimp [r]
      field_simp [hθone.ne']
      <;> ring
    nlinarith
  let c : ℝ := 1/((2*Real.pi)*r)
  have hc : 0 < c := by dsimp [c]; positivity
  have hcupper : c < 1/(2*Real.pi) := by
    dsimp [c]
    exact one_div_lt_one_div_of_lt (by positivity)
      (by nlinarith [Real.pi_pos])
  let B : ℝ := a+θ*Real.log 4+Real.log 4+4
  have hscrit : ∀ᶠ T : ℝ in atTop,
      1 ≤ d T ∧ Real.log (d T : ℝ) ≤ a+Real.log (T+3)/3 := by
    filter_upwards [hsupport, eventually_ge_atTop (1:ℝ)] with T hs hT
    refine ⟨hs.1, hs.2.trans ?_⟩
    have hL : 0 ≤ Real.log (T+3) := Real.log_nonneg (by linarith)
    nlinarith
  have hE := actualLandauResidual_norm_tendsto_zero_one_third_support d a hscrit
  have hEsmall : ∀ᶠ T : ℝ in atTop, ‖actualLandauResidual T (d T)‖ < η/4 :=
    hE.eventually (gt_mem_nhds (by positivity : (0:ℝ) < η/4))
  filter_upwards [hsupport, eventually_count_ge_log_of_lt hcupper, hEsmall,
    eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (4*r*|B|/η)]
    with T hs hN hEs hT hLlarge
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  have hNr : (0:ℝ) < (Zeta23.Ncount 0 T : ℝ) :=
    lt_of_lt_of_le (by positivity) hN
  have hshift : Real.log (T+3) ≤ Real.log T+Real.log 4 := by
    calc
      _ ≤ Real.log (T*4) := Real.log_le_log (by linarith) (by linarith)
      _ = _ := Real.log_mul hT0.ne' (by norm_num)
  have hK : Real.log (d T : ℝ)+Real.log 4+4 ≤ θ*Real.log T+|B| := by
    have hθshift := mul_le_mul_of_nonneg_left hshift hθ
    have hB := le_abs_self B
    dsimp [B] at hB
    linarith
  have hK0 : 0 ≤ Real.log (d T : ℝ)+Real.log 4+4 := by
    have hdR : (1:ℝ) ≤ d T := by exact_mod_cast hs.1
    have := Real.log_nonneg hdR
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
    positivity
  have hτ : T/((2*Real.pi)*(Zeta23.Ncount 0 T : ℝ)) ≤ r/Real.log T := by
    calc
      _ ≤ T/((2*Real.pi)*(c*T*Real.log T)) :=
        div_le_div_of_nonneg_left hT0.le (by positivity)
          (mul_le_mul_of_nonneg_left hN (by positivity))
      _ = _ := by
        dsimp [c]
        field_simp [Real.pi_ne_zero, hr0.ne', hT0.ne', hL.ne']
  have hbudget : (r/Real.log T) *
      (Real.log (d T : ℝ)+Real.log 4+4) ≤ r*θ+η/4 := by
    have hb : r*|B|/Real.log T ≤ η/4 := by
      have hz := (div_le_iff₀ hη).mp hLlarge
      apply (div_le_iff₀ hL).mpr
      nlinarith
    calc
      _ ≤ (r/Real.log T)*(θ*Real.log T+|B|) :=
        mul_le_mul_of_nonneg_left hK (by positivity)
      _ = r*θ+r*|B|/Real.log T := by field_simp [hL.ne']
      _ ≤ _ := by linarith
  have hmain : (T/((2*Real.pi)*(Zeta23.Ncount 0 T : ℝ))) *
      (Real.log (d T : ℝ)+Real.log 4+4) ≤ r*θ+η/4 :=
    (mul_le_mul_of_nonneg_right hτ hK0).trans hbudget
  have hcoef : h ≤ actualHyperbolicLower T (d T) := by
    unfold actualHyperbolicLower
    dsimp [η] at hrθ hmain hEs
    linarith
  intro f
  exact (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)).trans
    (landauGram_form_lower T (d T) hT0.le f)

/-- Explicit endpoint lower bound, retaining the exact negative sinh square,
original complex convention, every zero copy, and every integer frequency. -/
theorem eventually_actualHyperbolic_rows_lower_one_third
    (d : ℝ → ℕ) (a h : ℝ) (hh : h < 2/3)
    (hsupport : ∀ᶠ T : ℝ in atTop,
      1 ≤ d T ∧ Real.log (d T : ℝ) ≤ a+Real.log (T+3)/3) :
    ∀ᶠ T : ℝ in atTop, ∀ f : Space (d T),
      h*‖f‖^2 ≤
        ‖CenteredHyperbolicFrames.cosineAnalysis (actualPhaseRow T (d T))
          (actualShift T) (centeredFrequency (d T)) f‖^2-
        ‖CenteredHyperbolicFrames.sineAnalysis (actualPhaseRow T (d T))
          (actualShift T) (centeredFrequency (d T)) f‖^2 := by
  have hs : ∀ᶠ T : ℝ in atTop,
      1 ≤ d T ∧ Real.log (d T : ℝ) ≤ a+(1/3:ℝ)*Real.log (T+3) := by
    simpa only [one_div_mul_eq_div] using hsupport
  have hform := eventually_landauGram_lower_power_support_one_third
    d a (1/3) h (by norm_num) (by norm_num) (by linarith) hs
  filter_upwards [hform] with T hT
  intro f
  rw [actualHyperbolic_rows_eq]
  exact hT f

end RiemannResearch.Analysis.ActualZeroPhaseMoments



/-! The complete leading-budget criterion and logarithmic support gain. -/
noncomputable section
open Filter Zeta23
open scoped BigOperators InnerProductSpace

namespace RiemannResearch.Analysis.LandauHilbertSchmidt
open LandauGrowth

/-- The exact leading budget of the complete normalized HS envelope.
This concerns a nonnegative majorant, not necessity for the signed residual. -/
theorem normalizedHSEnvelope_tendsto_zero_of_leading_budget
    {α : Type*} (F : Filter α) (L ell : α → ℝ)
    (hL : Tendsto L F atTop)
    (hleading : Tendsto (fun t => Real.exp (3 * ell t - L t) / L t)
      F (nhds 0)) :
    Tendsto (fun t => normalizedHSEnvelope (L t) (ell t)) F (nhds 0) := by
  have hsupport : ∀ᶠ t in F, ell t ≤ 5 * L t / 12 := by
    filter_upwards [hL.eventually_ge_atTop 144,
      hleading.eventually_le_const (by norm_num : (0 : ℝ) < 1)] with t hlarge hsmall
    have hpos : 0 < L t := by linarith
    have he : Real.exp (3 * ell t - L t) ≤ L t := (div_le_one hpos).mp hsmall
    have hlog := Real.log_le_log (Real.exp_pos _) he
    rw [Real.log_exp] at hlog
    have hh := log_le_one_sixth_of_large hlarge
    linarith
  have hscale : Tendsto (fun t => L t / 6) F atTop :=
    hL.atTop_div_const (by norm_num)
  have hp₁ := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale).const_mul (6 : ℝ)
  have h₁ : Tendsto (fun t => L t * Real.exp (-L t / 6)) F (nhds 0) := by
    convert hp₁ using 1
    · funext t
      change L t * Real.exp (-L t / 6) =
        6 * ((L t / 6) ^ 1 * Real.exp (-(L t / 6)))
      simp only [pow_one]
      rw [show -(L t / 6) = -L t / 6 by ring]
      ring
    · norm_num
  have hp₀ := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp hscale
  have h₀ : Tendsto (fun t => Real.exp (-L t / 6)) F (nhds 0) := by
    convert hp₀ using 1
    funext t
    change Real.exp (-L t / 6) = (L t / 6) ^ 0 * Real.exp (-(L t / 6))
    simp only [pow_zero, one_mul]
    congr 1
    ring
  have hmajor : Tendsto (fun t =>
      2 * (Real.exp (3 * ell t - L t) / L t) +
      2 * (L t * Real.exp (-L t / 6)) + 3 * Real.exp (-L t / 6)) F (nhds 0) := by
    simpa only [mul_zero, add_zero] using
      ((hleading.const_mul 2).add (h₁.const_mul 2)).add (h₀.const_mul 3)
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [hL.eventually_gt_atTop 0] with t ht
    unfold normalizedHSEnvelope
    positivity
  · filter_upwards [hsupport, hL.eventually_gt_atTop 0] with t hs ht
    have he : Real.exp (2 * ell t - L t) ≤ Real.exp (-L t / 6) :=
      Real.exp_le_exp.mpr (by linarith)
    unfold normalizedHSEnvelope
    have hm := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2 * L t)
    have hn := mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 3)
    simp only [mul_div_assoc]
    nlinarith only [hm, hn]

theorem normalizedHSEnvelope_tendsto_zero_iff_leading_budget
    {α : Type*} (F : Filter α) (L ell : α → ℝ)
    (hL : Tendsto L F atTop) :
    Tendsto (fun t => normalizedHSEnvelope (L t) (ell t)) F (nhds 0) ↔
      Tendsto (fun t => Real.exp (3 * ell t - L t) / L t) F (nhds 0) := by
  constructor
  · intro hm
    refine squeeze_zero' ?_ ?_ hm
    · filter_upwards [hL.eventually_gt_atTop 0] with t ht
      exact div_nonneg (Real.exp_pos _).le ht.le
    · filter_upwards [hL.eventually_gt_atTop 0] with t ht
      have h₀ : 0 ≤ Real.exp (3 * ell t - L t) / L t := by positivity
      have h₁ : 0 ≤ 2 * L t * Real.exp (2 * ell t - L t) := by positivity
      have h₂ : 0 ≤ 3 * Real.exp (2 * ell t - L t) := by positivity
      unfold normalizedHSEnvelope
      simp only [mul_div_assoc]
      nlinarith only [h₀, h₁, h₂]
  · exact normalizedHSEnvelope_tendsto_zero_of_leading_budget F L ell hL

/-- A support logarithmic gain b<1/3 makes the new leading budget vanish.
The hypotheses are purely elementary support growth conditions. -/
theorem hs_leading_budget_tendsto_zero_log_support
    {α : Type*} (F : Filter α) (L ell : α → ℝ) (a b : ℝ)
    (hL : Tendsto L F atTop) (hb : b < 1/3)
    (hsupport : ∀ᶠ t in F, ell t ≤ a + L t/3 + b * Real.log (L t)) :
    Tendsto (fun t => Real.exp (3 * ell t - L t) / L t) F (nhds 0) := by
  let g : ℝ := 1-3*b
  have hg : 0 < g := by dsimp [g]; linarith
  have hlog := Real.tendsto_log_atTop.comp hL
  have hscale₀ : Tendsto (fun t => Real.log (L t) / (1/g)) F atTop :=
    hlog.atTop_div_const (by positivity)
  have hscale : Tendsto (fun t => g * Real.log (L t)) F atTop := by
    convert hscale₀ using 1
    funext t
    field_simp [hg.ne']
  have hp := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp hscale
  have hdecay : Tendsto (fun t => Real.exp (-g * Real.log (L t))) F (nhds 0) := by
    convert hp using 1
    funext t
    change Real.exp (-g * Real.log (L t)) =
      (g * Real.log (L t)) ^ 0 * Real.exp (-(g * Real.log (L t)))
    simp only [pow_zero, one_mul]
    congr 1
    ring
  have hmajor : Tendsto (fun t => Real.exp (3*a) * Real.exp (-g * Real.log (L t)))
      F (nhds 0) := by
    simpa only [mul_zero] using hdecay.const_mul (Real.exp (3*a))
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [hL.eventually_gt_atTop 0] with t ht
    exact div_nonneg (Real.exp_pos _).le ht.le
  · filter_upwards [hsupport, hL.eventually_gt_atTop 0] with t hs ht
    calc
      _ = Real.exp (3 * ell t - L t - Real.log (L t)) := by
        conv_rhs => rw [Real.exp_sub, Real.exp_log ht]
      _ ≤ Real.exp (3*a + (-g * Real.log (L t))) := by
        apply Real.exp_le_exp.mpr
        dsimp [g]
        nlinarith
      _ = _ := Real.exp_add _ _

end RiemannResearch.Analysis.LandauHilbertSchmidt

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open ActualZeroOrdinate RiemannResearch.Analysis.LandauHilbertSchmidt

/-- Complete actual signed residual convergence under the improved leading budget.
This premise is only a support rate; no zero density or RH hypothesis is added. -/
theorem actualLandauResidual_norm_tendsto_zero_of_hs_leading_budget
    (d : ℝ → ℕ)
    (hd : ∀ᶠ T : ℝ in atTop, 1 ≤ d T)
    (hleading : Tendsto (fun T : ℝ =>
      (d T : ℝ)^3 / ((T+3)*Real.log (T+3))) atTop (nhds 0)) :
    Tendsto (fun T : ℝ => ‖actualLandauResidual T (d T)‖) atTop (nhds 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_actualLandauResidual_hilbertSchmidt_norm_bound
  let q : ℝ := 1/(64*Real.pi)
  have hq : 0 < q := by dsimp [q]; positivity
  have hplus : Tendsto (fun T : ℝ => T+3) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with T hT
    linarith
  have hlog := Real.tendsto_log_atTop.comp hplus
  have hlead : Tendsto (fun T : ℝ =>
      Real.exp (3 * Real.log (d T : ℝ) - Real.log (T+3)) / Real.log (T+3))
      atTop (nhds 0) := by
    apply hleading.congr'
    filter_upwards [hd, eventually_ge_atTop (9 : ℝ)] with T hdT hT
    have hdpos : (0 : ℝ) < (d T : ℝ) :=
      by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hdT)
    have hY : 0 < T+3 := by linarith
    have he3 : Real.exp (3 * Real.log (d T : ℝ)) = (d T : ℝ)^3 := by
      simpa only [Nat.cast_ofNat, Real.exp_log hdpos] using
        Real.exp_nat_mul (Real.log (d T : ℝ)) 3
    rw [Real.exp_sub, he3, Real.exp_log hY, div_div]
  have hmatrix := normalizedHSEnvelope_tendsto_zero_of_leading_budget atTop
    (fun T : ℝ => Real.log (T+3)) (fun T : ℝ => Real.log (d T : ℝ)) hlog hlead
  have hmajor : Tendsto (fun T : ℝ => (C/q) *
      normalizedHSEnvelope (Real.log (T+3)) (Real.log (d T : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using hmatrix.const_mul (C/q)
  refine squeeze_zero' ?_ ?_ hmajor
  · exact Eventually.of_forall (fun T => norm_nonneg _)
  · filter_upwards [eventually_count_ge_height_add_three_log,
      eventually_ge_atTop (9 : ℝ), hd] with T hNheight hT hdT
    have hY : 0 < T+3 := by linarith
    have hLpos : 0 < Real.log (T+3) := Real.log_pos (by linarith)
    change q*(T+3)*Real.log (T+3) ≤ (Ncount 0 T : ℝ) at hNheight
    have hNr : (0 : ℝ) < (Ncount 0 T : ℝ) := lt_of_lt_of_le (by positivity) hNheight
    have hN : 0 < Ncount 0 T := by exact_mod_cast hNr
    have hdpos : (0 : ℝ) < (d T : ℝ) :=
      by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hdT)
    have henv : 0 ≤ 2*(d T : ℝ)^3 + 2*(d T : ℝ)^2*Real.log (T+3)^2 +
        3*(d T : ℝ)^2*Real.log (T+3) := by positivity
    calc
      _ ≤ _ := hbound T (d T) hT hN
      _ = C*(2*(d T : ℝ)^3 + 2*(d T : ℝ)^2*Real.log (T+3)^2 +
          3*(d T : ℝ)^2*Real.log (T+3)) / (Ncount 0 T : ℝ) := by ring
      _ ≤ C*(2*(d T : ℝ)^3 + 2*(d T : ℝ)^2*Real.log (T+3)^2 +
          3*(d T : ℝ)^2*Real.log (T+3)) / (q*(T+3)*Real.log (T+3)) :=
        div_le_div_of_nonneg_left (mul_nonneg hC.le henv) (by positivity) hNheight
      _ = _ := by
        rw [normalizedHSEnvelope_eq hY hdpos hLpos]
        field_simp [hq.ne', hY.ne', hLpos.ne']

/-- Log-enlarged 1/3 support for the complete actual signed residual. -/
theorem actualLandauResidual_norm_tendsto_zero_hs_log_power_support
    (d : ℝ → ℕ) (a b : ℝ) (hb : b < 1/3)
    (hsupport : ∀ᶠ T : ℝ in atTop,
      1 ≤ d T ∧ Real.log (d T : ℝ) ≤
        a+Real.log (T+3)/3+b*Real.log (Real.log (T+3))) :
    Tendsto (fun T : ℝ => ‖actualLandauResidual T (d T)‖) atTop (nhds 0) := by
  have hd := hsupport.mono (fun _ h => h.1)
  have hs := hsupport.mono (fun _ h => h.2)
  have hplus : Tendsto (fun T : ℝ => T+3) atTop atTop := by
    apply tendsto_atTop.2
    intro c
    filter_upwards [eventually_ge_atTop c] with T hT
    linarith
  have hlog := Real.tendsto_log_atTop.comp hplus
  have hlead := hs_leading_budget_tendsto_zero_log_support atTop
    (fun T : ℝ => Real.log (T+3)) (fun T : ℝ => Real.log (d T : ℝ)) a b hlog hb hs
  have hbudget : Tendsto (fun T : ℝ =>
      (d T : ℝ)^3 / ((T+3)*Real.log (T+3))) atTop (nhds 0) := by
    apply hlead.congr'
    filter_upwards [hd, eventually_ge_atTop (9 : ℝ)] with T hdT hT
    have hdpos : (0 : ℝ) < (d T : ℝ) :=
      by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hdT)
    have hY : 0 < T+3 := by linarith
    have he3 : Real.exp (3 * Real.log (d T : ℝ)) = (d T : ℝ)^3 := by
      simpa only [Nat.cast_ofNat, Real.exp_log hdpos] using
        Real.exp_nat_mul (Real.log (d T : ℝ)) 3
    rw [Real.exp_sub, he3, Real.exp_log hY, div_div]
  exact actualLandauResidual_norm_tendsto_zero_of_hs_leading_budget d hd hbudget

end RiemannResearch.Analysis.ActualZeroPhaseMoments
