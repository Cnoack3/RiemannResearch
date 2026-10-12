import RiemannResearch.RH.ParetoDilation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Linarith

/-!
# Exact nearby-dilation Gram decomposition

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Section 3. The complete infinite Pareto tail is retained. This module does
not assert the logarithmic asymptotic or a uniform arithmetic energy bound.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- The difference `T_(n+1) φ - T_n φ` with the original scaled dilations. -/
def nearbyDilationPacket (φ : ℕ → ℝ) (n k : ℕ) : ℝ :=
  ((n : ℝ) + 1) * φ (k / (n + 1)) - (n : ℝ) * φ (k / n)

theorem nearbyDilationPacket_eq_dilation (φ : ℕ → ℝ) (n : ℕ) :
    nearbyDilationPacket φ n = dilation (n + 1) φ - dilation n φ := by
  funext k
  simp [nearbyDilationPacket, dilation]

theorem nearbyDilationPacket_below {φ : ℕ → ℝ} (hφ : φ 0 = 0)
    {n k : ℕ} (hk : k < n) : nearbyDilationPacket φ n k = 0 := by
  simp [nearbyDilationPacket, Nat.div_eq_of_lt hk,
    Nat.div_eq_of_lt (show k < n + 1 by omega), hφ]

theorem nearbyDilationPacket_at {φ : ℕ → ℝ} (hφ : φ 0 = 0)
    {n : ℕ} (hn : 0 < n) : nearbyDilationPacket φ n n = -(n : ℝ) * φ 1 := by
  simp [nearbyDilationPacket, Nat.div_self hn,
    Nat.div_eq_of_lt (Nat.lt_succ_self n), hφ]

theorem nearbyDilationPacket_abs_le {φ : ℕ → ℝ} {C : ℝ}
    (hφ : ∀ k, |φ k| ≤ C) (n k : ℕ) :
    |nearbyDilationPacket φ n k| ≤ (2 * (n : ℝ) + 1) * C := by
  have h₁ := dilation_abs_le hφ (n + 1) k
  have h₂ := dilation_abs_le hφ n k
  have htriangle : |dilation (n+1) φ k - dilation n φ k| ≤
      |dilation (n+1) φ k| + |dilation n φ k| := by
    simpa only [sub_zero, zero_sub, abs_neg] using
      abs_sub_le (dilation (n+1) φ k) 0 (dilation n φ k)
  rw [nearbyDilationPacket_eq_dilation]
  change |dilation (n+1) φ k - dilation n φ k| ≤ _
  push_cast at h₁
  nlinarith

/-- Exact finite prefix mass, with zero coordinate of mass zero. -/
theorem positiveWeight_sum_range (M : ℕ) (hM : 0 < M) :
    (∑ k ∈ Finset.range M, positiveWeight k) = 1 - 1 / (M : ℝ) := by
  rw [Finset.sum_range_eq_add_Ico positiveWeight hM,
    positiveWeight_interval 1 M (by omega) hM]
  norm_num [positiveWeight]

/-- The full tail mass, not an approximation by a finite cutoff. -/
theorem positiveWeight_tail_tsum (M : ℕ) (hM : 0 < M) :
    (∑' k : ℕ, positiveWeight (k + M)) = 1 / (M : ℝ) := by
  have h := positiveWeight_summable.sum_add_tsum_nat_add M
  rw [positiveWeight_sum_range M hM, positiveWeight_tsum] at h
  linarith

def nearbyDilationGramTail (φ ψ : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑' k : ℕ, positiveWeight (k + n * (n + 1)) *
    (nearbyDilationPacket φ n (k + n * (n + 1)) *
      nearbyDilationPacket ψ n (k + n * (n + 1)))

theorem nearbyDilationGram_summable {φ ψ : ℕ → ℝ} {C D : ℝ}
    (hφ : ∀ k, |φ k| ≤ C) (hψ : ∀ k, |ψ k| ≤ D) (n : ℕ) :
    Summable (fun k => positiveWeight k *
      (nearbyDilationPacket φ n k * nearbyDilationPacket ψ n k)) := by
  exact weighted_summable_of_bounded
    (bounded_product (nearbyDilationPacket_abs_le hφ n)
      (nearbyDilationPacket_abs_le hψ n))

/-- Prefix plus the entire infinite tail, preserving every mixed term. -/
theorem nearbyDilationGram_exact_tail {φ ψ : ℕ → ℝ} {C D : ℝ}
    (hφ : ∀ k, |φ k| ≤ C) (hψ : ∀ k, |ψ k| ≤ D) (n : ℕ) :
    paretoInner (nearbyDilationPacket φ n) (nearbyDilationPacket ψ n) =
      (∑ k ∈ Finset.range (n * (n + 1)), positiveWeight k *
        (nearbyDilationPacket φ n k * nearbyDilationPacket ψ n k)) +
      nearbyDilationGramTail φ ψ n := by
  exact ((nearbyDilationGram_summable hφ hψ n).sum_add_tsum_nat_add
    (n * (n + 1))).symm

theorem nearbyDilationGramTail_self_nonneg (φ : ℕ → ℝ) (n : ℕ) :
    0 ≤ nearbyDilationGramTail φ φ n := by
  apply tsum_nonneg
  intro k
  exact mul_nonneg (positiveWeight_nonneg _) (mul_self_nonneg _)

theorem nearbyDilationGramTail_abs_le {φ ψ : ℕ → ℝ} {C D : ℝ}
    (hφ : ∀ k, |φ k| ≤ C) (hψ : ∀ k, |ψ k| ≤ D)
    (n : ℕ) (hn : 0 < n) :
    |nearbyDilationGramTail φ ψ n| ≤
      (2 * (n : ℝ) + 1)^2 / ((n : ℝ) * ((n : ℝ) + 1)) * C * D := by
  let M := n * (n+1)
  have hM : 0 < M := Nat.mul_pos hn (by omega)
  have hprod := bounded_product (nearbyDilationPacket_abs_le hφ n)
    (nearbyDilationPacket_abs_le hψ n)
  have hs := (summable_nat_add_iff M).mpr (nearbyDilationGram_summable hφ hψ n)
  have hw := (summable_nat_add_iff M).mpr positiveWeight_summable
  have hb (k : ℕ) : |positiveWeight (k+M) *
      (nearbyDilationPacket φ n (k+M) * nearbyDilationPacket ψ n (k+M))| ≤
      positiveWeight (k+M) *
        (((2*(n:ℝ)+1)*C) * ((2*(n:ℝ)+1)*D)) := by
    rw [abs_mul, abs_of_nonneg (positiveWeight_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hprod _) (positiveWeight_nonneg _)
  calc
    _ ≤ ∑' k : ℕ, |positiveWeight (k+M) *
        (nearbyDilationPacket φ n (k+M) * nearbyDilationPacket ψ n (k+M))| :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' k : ℕ, positiveWeight (k+M) *
        (((2*(n:ℝ)+1)*C) * ((2*(n:ℝ)+1)*D)) :=
      hs.abs.tsum_le_tsum hb (hw.mul_right _)
    _ = _ := by
      rw [hw.tsum_mul_right, positiveWeight_tail_tsum M hM]
      dsimp [M]
      push_cast
      ring

theorem nearbyDilationGramTail_abs_le_uniform {φ ψ : ℕ → ℝ} {C D : ℝ}
    (hφ : ∀ k, |φ k| ≤ C) (hψ : ∀ k, |ψ k| ≤ D)
    (n : ℕ) (hn : 0 < n) :
    |nearbyDilationGramTail φ ψ n| ≤ (9 / 2 : ℝ) * C * D := by
  have hC : 0 ≤ C := (abs_nonneg (φ 0)).trans (hφ 0)
  have hD : 0 ≤ D := (abs_nonneg (ψ 0)).trans (hψ 0)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < (n:ℝ) * ((n:ℝ)+1) := by positivity
  have hratio : (2*(n:ℝ)+1)^2 / ((n:ℝ)*((n:ℝ)+1)) ≤ (9/2:ℝ) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  exact (nearbyDilationGramTail_abs_le hφ hψ n hn).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hratio hC) hD)

theorem nearbyDilationPacket_jump_interval (φ : ℕ → ℝ)
    {n j k : ℕ} (hj : j < n)
    (hlo : (j+1)*n ≤ k) (hhi : k < (j+1)*(n+1)) :
    nearbyDilationPacket φ n k =
      -(n:ℝ) * (φ (j+1) - φ j) + φ j := by
  have hdiv : k / n = j+1 := Nat.div_eq_of_lt_le hlo (by nlinarith)
  have hdiv' : k / (n+1) = j := Nat.div_eq_of_lt_le (by nlinarith) hhi
  simp only [nearbyDilationPacket, hdiv, hdiv']
  ring

theorem nearbyDilationPacket_plateau_interval (φ : ℕ → ℝ)
    {n j k : ℕ}
    (hlo : (j+1)*(n+1) ≤ k) (hhi : k < (j+2)*n) :
    nearbyDilationPacket φ n k = φ (j+1) := by
  have hdiv : k / n = j+1 := Nat.div_eq_of_lt_le (by nlinarith) (by omega)
  have hdiv' : k / (n+1) = j+1 := Nat.div_eq_of_lt_le hlo (by nlinarith)
  simp only [nearbyDilationPacket, hdiv, hdiv']
  ring

def nearbyDilationJumpTerm (φ ψ : ℕ → ℝ) (n j : ℕ) : ℝ :=
  (-(n:ℝ)*(φ (j+1)-φ j)+φ j) * (-(n:ℝ)*(ψ (j+1)-ψ j)+ψ j) /
    (((j:ℝ)+1)*(n:ℝ)*((n:ℝ)+1))

def nearbyDilationPlateauTerm (φ ψ : ℕ → ℝ) (n j : ℕ) : ℝ :=
  φ (j+1) * ψ (j+1) *
    (1 / (((j:ℝ)+1)*((n:ℝ)+1)) - 1 / (((j:ℝ)+2)*(n:ℝ)))

theorem nearbyDilationGram_jump_interval (φ ψ : ℕ → ℝ)
    {n j : ℕ} (hj : j < n) :
    (∑ k ∈ Finset.Ico ((j+1)*n) ((j+1)*(n+1)), positiveWeight k *
      (nearbyDilationPacket φ n k * nearbyDilationPacket ψ n k)) =
        nearbyDilationJumpTerm φ ψ n j := by
  have hn : 0 < n := by omega
  calc
    _ = (∑ k ∈ Finset.Ico ((j+1)*n) ((j+1)*(n+1)), positiveWeight k) *
        ((-(n:ℝ)*(φ (j+1)-φ j)+φ j) * (-(n:ℝ)*(ψ (j+1)-ψ j)+ψ j)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [nearbyDilationPacket_jump_interval φ hj (Finset.mem_Ico.mp hk).1
        (Finset.mem_Ico.mp hk).2,
        nearbyDilationPacket_jump_interval ψ hj (Finset.mem_Ico.mp hk).1
        (Finset.mem_Ico.mp hk).2]
    _ = _ := by
      rw [positiveWeight_interval _ _ (Nat.mul_pos (by omega) hn) (by nlinarith)]
      unfold nearbyDilationJumpTerm
      push_cast
      have hn0 : (n:ℝ) ≠ 0 := by positivity
      have hn1 : (n:ℝ)+1 ≠ 0 := by positivity
      have hj1 : (j:ℝ)+1 ≠ 0 := by positivity
      field_simp
      <;> ring

theorem nearbyDilationGram_plateau_interval (φ ψ : ℕ → ℝ)
    {n j : ℕ} (hj : j < n) :
    (∑ k ∈ Finset.Ico ((j+1)*(n+1)) ((j+2)*n), positiveWeight k *
      (nearbyDilationPacket φ n k * nearbyDilationPacket ψ n k)) =
        nearbyDilationPlateauTerm φ ψ n j := by
  calc
    _ = (∑ k ∈ Finset.Ico ((j+1)*(n+1)) ((j+2)*n), positiveWeight k) *
        (φ (j+1)*ψ (j+1)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [nearbyDilationPacket_plateau_interval φ (Finset.mem_Ico.mp hk).1
        (Finset.mem_Ico.mp hk).2,
        nearbyDilationPacket_plateau_interval ψ (Finset.mem_Ico.mp hk).1
        (Finset.mem_Ico.mp hk).2]
    _ = _ := by
      rw [positiveWeight_interval _ _ (Nat.mul_pos (by omega) (by omega)) (by nlinarith)]
      unfold nearbyDilationPlateauTerm
      push_cast
      ring

theorem nearbyDilationGram_block (φ ψ : ℕ → ℝ)
    {n j : ℕ} (hj : j < n) :
    (∑ k ∈ Finset.Ico ((j+1)*n) ((j+2)*n), positiveWeight k *
      (nearbyDilationPacket φ n k * nearbyDilationPacket ψ n k)) =
        nearbyDilationJumpTerm φ ψ n j + nearbyDilationPlateauTerm φ ψ n j := by
  rw [← Finset.sum_Ico_consecutive _ (show (j+1)*n ≤ (j+1)*(n+1) by nlinarith)
    (show (j+1)*(n+1) ≤ (j+2)*n by nlinarith)]
  rw [nearbyDilationGram_jump_interval φ ψ hj,
    nearbyDilationGram_plateau_interval φ ψ hj]

theorem nearbyDilationGram_prefix {φ ψ : ℕ → ℝ}
    (hφ0 : φ 0 = 0) (hψ0 : ψ 0 = 0) (n : ℕ) :
    (∑ k ∈ Finset.range (n*(n+1)), positiveWeight k *
      (nearbyDilationPacket φ n k * nearbyDilationPacket ψ n k)) =
      (∑ j ∈ Finset.range n, nearbyDilationJumpTerm φ ψ n j) +
      (∑ j ∈ Finset.range n, nearbyDilationPlateauTerm φ ψ n j) := by
  let f := fun k => positiveWeight k *
    (nearbyDilationPacket φ n k * nearbyDilationPacket ψ n k)
  have hblocks (K : ℕ) (hK : K ≤ n) :
      (∑ k ∈ Finset.range ((K+1)*n), f k) =
        ∑ j ∈ Finset.range K,
          (nearbyDilationJumpTerm φ ψ n j + nearbyDilationPlateauTerm φ ψ n j) := by
    induction K with
    | zero =>
      simp only [zero_add, one_mul, Finset.range_zero, Finset.sum_empty]
      apply Finset.sum_eq_zero
      intro k hk
      dsimp [f]
      rw [nearbyDilationPacket_below hφ0 (Finset.mem_range.mp hk)]
      ring
    | succ K ih =>
      have hKn : K < n := by omega
      have hi := ih (by omega)
      have hb := nearbyDilationGram_block φ ψ hKn
      rw [Finset.sum_Ico_eq_sub _ (show (K+1)*n ≤ (K+2)*n by nlinarith)] at hb
      rw [Finset.sum_range_succ]
      change (∑ k ∈ Finset.range ((K+2)*n), f k) = _
      change (∑ k ∈ Finset.range ((K+2)*n), f k) -
        (∑ k ∈ Finset.range ((K+1)*n), f k) = _ at hb
      linarith
  simpa only [Nat.mul_comm (n+1) n, Finset.sum_add_distrib] using hblocks n le_rfl

/-- The exact mixed Gram identity in Section 3, with a zero last plateau term.
No periodicity assumption is needed for this finite partition plus tail. -/
theorem nearbyDilationGram_exact {φ ψ : ℕ → ℝ} {C D : ℝ}
    (hφ : ∀ k, |φ k| ≤ C) (hψ : ∀ k, |ψ k| ≤ D)
    (hφ0 : φ 0 = 0) (hψ0 : ψ 0 = 0) (n : ℕ) :
    paretoInner (nearbyDilationPacket φ n) (nearbyDilationPacket ψ n) =
      (∑ j ∈ Finset.range n, nearbyDilationJumpTerm φ ψ n j) +
      (∑ j ∈ Finset.range n, nearbyDilationPlateauTerm φ ψ n j) +
      nearbyDilationGramTail φ ψ n := by
  rw [nearbyDilationGram_exact_tail hφ hψ n,
    nearbyDilationGram_prefix hφ0 hψ0 n]

/-- Exact extraction of the harmonic main term. The mixed first-order term
and the lower-order product are retained, prior to any limiting argument. -/
theorem nearbyDilationJumpTerm_expansion (φ ψ : ℕ → ℝ)
    (n j : ℕ) (hn : 0 < n) :
    nearbyDilationJumpTerm φ ψ n j =
      (n:ℝ) / ((n:ℝ)+1) *
        ((φ (j+1)-φ j)*(ψ (j+1)-ψ j) / ((j:ℝ)+1)) -
      ((φ (j+1)-φ j)*ψ j + φ j*(ψ (j+1)-ψ j)) /
        (((j:ℝ)+1)*((n:ℝ)+1)) +
      φ j*ψ j / (((j:ℝ)+1)*(n:ℝ)*((n:ℝ)+1)) := by
  unfold nearbyDilationJumpTerm
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  have hn1 : (n:ℝ)+1 ≠ 0 := by positivity
  have hj1 : (j:ℝ)+1 ≠ 0 := by positivity
  field_simp
  <;> ring

def nearbyDilationHarmonicMain (φ ψ : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, (φ (j+1)-φ j)*(ψ (j+1)-ψ j) / ((j:ℝ)+1)

theorem nearbyDilationJumpTerm_error_bound {φ ψ : ℕ → ℝ} {C D : ℝ}
    (hφ : ∀ k, |φ k| ≤ C) (hψ : ∀ k, |ψ k| ≤ D)
    (n j : ℕ) (hn : 0 < n) :
    |nearbyDilationJumpTerm φ ψ n j -
      (φ (j+1)-φ j)*(ψ (j+1)-ψ j) / ((j:ℝ)+1)| ≤
      9*C*D/((n:ℝ)+1) := by
  have hC : 0 ≤ C := (abs_nonneg (φ 0)).trans (hφ 0)
  have hD : 0 ≤ D := (abs_nonneg (ψ 0)).trans (hψ 0)
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hj' : (1:ℝ) ≤ (j:ℝ)+1 := by linarith [show (0:ℝ) ≤ j by positivity]
  have hdφ : |φ (j+1)-φ j| ≤ 2*C := by
    have ht := abs_sub_le (φ (j+1)) 0 (φ j)
    simp only [sub_zero, zero_sub, abs_neg] at ht
    linarith [hφ (j+1), hφ j]
  have hdψ : |ψ (j+1)-ψ j| ≤ 2*D := by
    have ht := abs_sub_le (ψ (j+1)) 0 (ψ j)
    simp only [sub_zero, zero_sub, abs_neg] at ht
    linarith [hψ (j+1), hψ j]
  have hb₁ : |(φ (j+1)-φ j)*(ψ (j+1)-ψ j)| ≤ 4*C*D := by
    rw [abs_mul]
    nlinarith [mul_le_mul hdφ hdψ (abs_nonneg _) (by positivity : 0 ≤ 2*C)]
  have hb₂ : |(φ (j+1)-φ j)*ψ j| ≤ 2*C*D := by
    rw [abs_mul]
    nlinarith [mul_le_mul hdφ (hψ j) (abs_nonneg _) (by positivity : 0 ≤ 2*C)]
  have hb₃ : |φ j*(ψ (j+1)-ψ j)| ≤ 2*C*D := by
    rw [abs_mul]
    nlinarith [mul_le_mul (hφ j) hdψ (abs_nonneg _) hC]
  have hb₄ : |φ j*ψ j| ≤ C*D := by
    rw [abs_mul]
    exact mul_le_mul (hφ j) (hψ j) (abs_nonneg _) hC
  let A := (φ (j+1)-φ j)*(ψ (j+1)-ψ j)
  let B := (φ (j+1)-φ j)*ψ j + φ j*(ψ (j+1)-ψ j)
  let Z := φ j*ψ j
  have hB : |B| ≤ 4*C*D := by
    exact (abs_add_le _ _).trans (by linarith)
  have hnum : |-(n:ℝ)*A - (n:ℝ)*B + Z| ≤ 9*(n:ℝ)*C*D := by
    have ht₁ := abs_add_le (-(n:ℝ)*A - (n:ℝ)*B) Z
    have ht₂ : |-(n:ℝ)*A - (n:ℝ)*B| ≤ (n:ℝ)*|A|+(n:ℝ)*|B| := by
      have ht := abs_sub_le (-(n:ℝ)*A) 0 ((n:ℝ)*B)
      simpa only [sub_zero, zero_sub, abs_neg, abs_mul,
        abs_of_nonneg (show (0:ℝ) ≤ n from Nat.cast_nonneg n)] using ht
    have hnC : C*D ≤ (n:ℝ)*(C*D) := by nlinarith [mul_nonneg hC hD]
    have ha := mul_le_mul_of_nonneg_left hb₁ (Nat.cast_nonneg n)
    have hb := mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg n)
    dsimp [A, Z] at *
    nlinarith
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  have hn1 : (n:ℝ)+1 ≠ 0 := by positivity
  have hj1 : (j:ℝ)+1 ≠ 0 := by positivity
  have he : nearbyDilationJumpTerm φ ψ n j - A/((j:ℝ)+1) =
      (-(n:ℝ)*A - (n:ℝ)*B + Z) / (((j:ℝ)+1)*(n:ℝ)*((n:ℝ)+1)) := by
    dsimp [nearbyDilationJumpTerm, A, B, Z]
    field_simp
    <;> ring
  rw [he, abs_div, abs_of_pos (show 0 < ((j:ℝ)+1)*(n:ℝ)*((n:ℝ)+1) by positivity)]
  calc
    _ ≤ (9*(n:ℝ)*C*D) / (((j:ℝ)+1)*(n:ℝ)*((n:ℝ)+1)) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ _ := by
      apply (div_le_div_iff₀ (by positivity : 0 < ((j:ℝ)+1)*(n:ℝ)*((n:ℝ)+1))
        (by positivity : 0 < (n:ℝ)+1)).mpr
      have h := mul_nonneg (show 0 ≤ (j:ℝ) by positivity)
        (show 0 ≤ 9*(n:ℝ)*C*D*((n:ℝ)+1) by positivity)
      nlinarith

theorem nearbyDilationPlateauTerm_bound {φ ψ : ℕ → ℝ} {C D : ℝ}
    (hφ : ∀ k, |φ k| ≤ C) (hψ : ∀ k, |ψ k| ≤ D)
    (n j : ℕ) (hj : j < n) :
    |nearbyDilationPlateauTerm φ ψ n j| ≤ C*D/((n:ℝ)+1) := by
  have hC : 0 ≤ C := (abs_nonneg (φ 0)).trans (hφ 0)
  have hD : 0 ≤ D := (abs_nonneg (ψ 0)).trans (hψ 0)
  have hn : 0 < n := by omega
  have hjn : (j:ℝ)+1 ≤ n := by exact_mod_cast hj
  let w := 1 / (((j:ℝ)+1)*((n:ℝ)+1)) - 1 / (((j:ℝ)+2)*(n:ℝ))
  have hw0 : 0 ≤ w := by
    dsimp [w]
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hw : w ≤ 1 / ((n:ℝ)+1) := by
    dsimp [w]
    calc
      _ ≤ 1 / (((j:ℝ)+1)*((n:ℝ)+1)) := sub_le_self _ (by positivity)
      _ ≤ _ := by
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith [show (0:ℝ) ≤ j from Nat.cast_nonneg j,
          show (0:ℝ) ≤ n from Nat.cast_nonneg n]
  have hprod : |φ (j+1)*ψ (j+1)| ≤ C*D := by
    rw [abs_mul]
    exact mul_le_mul (hφ _) (hψ _) (abs_nonneg _) hC
  change |(φ (j+1)*ψ (j+1))*w| ≤ _
  rw [abs_mul, abs_of_nonneg hw0]
  calc
    _ ≤ C*D*w := mul_le_mul_of_nonneg_right hprod hw0
    _ ≤ C*D*(1/((n:ℝ)+1)) := mul_le_mul_of_nonneg_left hw (mul_nonneg hC hD)
    _ = _ := by ring

/-- The sharper complete plateau estimate appearing in the research note. -/
theorem nearbyDilationPlateauSum_abs_le {φ ψ : ℕ → ℝ} {C D : ℝ}
    (hφ : ∀ k, |φ k| ≤ C) (hψ : ∀ k, |ψ k| ≤ D)
    (n : ℕ) (hn : 0 < n) :
    |∑ j ∈ Finset.range n, nearbyDilationPlateauTerm φ ψ n j| ≤ C*D/(n:ℝ) := by
  have hC : 0 ≤ C := (abs_nonneg (φ 0)).trans (hφ 0)
  have hD : 0 ≤ D := (abs_nonneg (ψ 0)).trans (hψ 0)
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  have hterm (j : ℕ) (hj : j < n) :
      |nearbyDilationPlateauTerm φ ψ n j| ≤ (C*D/(n:ℝ))*positiveWeight (j+1) := by
    let w := 1/(((j:ℝ)+1)*((n:ℝ)+1)) - 1/(((j:ℝ)+2)*(n:ℝ))
    have hjn : (j:ℝ)+1 ≤ n := by exact_mod_cast hj
    have hw0 : 0 ≤ w := by
      dsimp [w]
      apply sub_nonneg.mpr
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have hw : w ≤ positiveWeight (j+1)/(n:ℝ) := by
      have hi : 1/(((j:ℝ)+1)*((n:ℝ)+1)) ≤ 1/(((j:ℝ)+1)*(n:ℝ)) := by
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith [show (0:ℝ) ≤ j by positivity]
      calc
        _ ≤ 1/(((j:ℝ)+1)*(n:ℝ)) - 1/(((j:ℝ)+2)*(n:ℝ)) :=
          by dsimp [w]; linarith
        _ = _ := by
          unfold positiveWeight
          push_cast
          have hj1 : (j:ℝ)+1 ≠ 0 := by positivity
          have hj2 : (j:ℝ)+2 ≠ 0 := by positivity
          field_simp
          <;> ring
    have hprod : |φ (j+1)*ψ (j+1)| ≤ C*D := by
      rw [abs_mul]
      exact mul_le_mul (hφ _) (hψ _) (abs_nonneg _) hC
    change |(φ (j+1)*ψ (j+1))*w| ≤ _
    rw [abs_mul, abs_of_nonneg hw0]
    calc
      _ ≤ C*D*w := mul_le_mul_of_nonneg_right hprod hw0
      _ ≤ C*D*(positiveWeight (j+1)/(n:ℝ)) :=
        mul_le_mul_of_nonneg_left hw (mul_nonneg hC hD)
      _ = _ := by ring
  have hmass : (∑ j ∈ Finset.range n, positiveWeight (j+1)) ≤ 1 := by
    have h := positiveWeight_interval 1 (n+1) (by omega) (by omega)
    rw [Finset.sum_Ico_eq_sum_range] at h
    simp only [Nat.add_sub_cancel, Nat.add_comm 1, Nat.cast_add, Nat.cast_one,
      one_div_one] at h
    linarith [show (0:ℝ) ≤ 1/((n:ℝ)+1) by positivity]
  calc
    _ ≤ ∑ j ∈ Finset.range n, |nearbyDilationPlateauTerm φ ψ n j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range n, (C*D/(n:ℝ))*positiveWeight (j+1) :=
      Finset.sum_le_sum (fun j hj => hterm j (Finset.mem_range.mp hj))
    _ = (C*D/(n:ℝ))*(∑ j ∈ Finset.range n, positiveWeight (j+1)) := by
      rw [Finset.mul_sum]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hmass (show 0 ≤ C*D/(n:ℝ) by positivity)
      simpa only [mul_one] using h

/-- A uniform bounded remainder after extracting the harmonic jump sum.
The exact identity is established first; no mixed term is omitted. -/
theorem nearbyDilationGram_harmonic_error_bound {φ ψ : ℕ → ℝ} {C D : ℝ}
    (hφ : ∀ k, |φ k| ≤ C) (hψ : ∀ k, |ψ k| ≤ D)
    (hφ0 : φ 0 = 0) (hψ0 : ψ 0 = 0) (n : ℕ) (hn : 0 < n) :
    |paretoInner (nearbyDilationPacket φ n) (nearbyDilationPacket ψ n) -
      nearbyDilationHarmonicMain φ ψ n| ≤ 15*C*D := by
  have hC : 0 ≤ C := (abs_nonneg (φ 0)).trans (hφ 0)
  have hD : 0 ≤ D := (abs_nonneg (ψ 0)).trans (hψ 0)
  have hmain : |(∑ j ∈ Finset.range n, nearbyDilationJumpTerm φ ψ n j) -
      nearbyDilationHarmonicMain φ ψ n| ≤ 9*C*D := by
    unfold nearbyDilationHarmonicMain
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j ∈ Finset.range n, |nearbyDilationJumpTerm φ ψ n j -
          (φ (j+1)-φ j)*(ψ (j+1)-ψ j)/((j:ℝ)+1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range n, 9*C*D/((n:ℝ)+1) :=
        Finset.sum_le_sum (fun j _ => nearbyDilationJumpTerm_error_bound hφ hψ n j hn)
      _ ≤ 9*C*D := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by positivity : 0 < (n:ℝ)+1)).mpr
        nlinarith [mul_nonneg hC hD]
  have hplateau : |∑ j ∈ Finset.range n, nearbyDilationPlateauTerm φ ψ n j| ≤ C*D := by
    calc
      _ ≤ ∑ j ∈ Finset.range n, |nearbyDilationPlateauTerm φ ψ n j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range n, C*D/((n:ℝ)+1) := by
        apply Finset.sum_le_sum
        intro j hj
        exact nearbyDilationPlateauTerm_bound hφ hψ n j (Finset.mem_range.mp hj)
      _ ≤ C*D := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by positivity : 0 < (n:ℝ)+1)).mpr
        nlinarith [mul_nonneg hC hD]
  have htail := nearbyDilationGramTail_abs_le_uniform hφ hψ n hn
  rw [nearbyDilationGram_exact hφ hψ hφ0 hψ0 n]
  have he : (∑ j ∈ Finset.range n, nearbyDilationJumpTerm φ ψ n j) +
      (∑ j ∈ Finset.range n, nearbyDilationPlateauTerm φ ψ n j) +
      nearbyDilationGramTail φ ψ n - nearbyDilationHarmonicMain φ ψ n =
      ((∑ j ∈ Finset.range n, nearbyDilationJumpTerm φ ψ n j) -
        nearbyDilationHarmonicMain φ ψ n) +
      (∑ j ∈ Finset.range n, nearbyDilationPlateauTerm φ ψ n j) +
      nearbyDilationGramTail φ ψ n := by ring
  rw [he]
  have ht₁ := abs_add_le
    (((∑ j ∈ Finset.range n, nearbyDilationJumpTerm φ ψ n j) -
      nearbyDilationHarmonicMain φ ψ n) +
      (∑ j ∈ Finset.range n, nearbyDilationPlateauTerm φ ψ n j))
    (nearbyDilationGramTail φ ψ n)
  have ht₂ := abs_add_le
    ((∑ j ∈ Finset.range n, nearbyDilationJumpTerm φ ψ n j) -
      nearbyDilationHarmonicMain φ ψ n)
    (∑ j ∈ Finset.range n, nearbyDilationPlateauTerm φ ψ n j)
  nlinarith [mul_nonneg hC hD]

end
end RiemannResearch.RH.Pareto
