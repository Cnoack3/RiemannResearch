/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.PositiveTestMoments
import Mathlib.Tactic.Positivity
import RiemannResearch.Analysis.PrimeResidueMoments
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Bertrand

/-!
# Finite prime residue tests for a signed charge

A local single-prime test and a clipped mixture of balanced prime remainders give two estimates retaining the complete absolute tail.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis

/-- A single balanced residue probe controls both signs of a localized pairing.
The charge is measured at the given cutoff `X`, while a bounded defect only
needs a small linear majorant through the shorter cutoff `Y`. -/
theorem pairing_le_local_residue_head (b D : ℕ → ℝ) (X Y p : ℕ) (m δ K : ℝ)
    (hYX : Y ≤ X) (hp : Y < p) (hδ : 0 ≤ δ) (hb : Summable b)
    (hm : HasSum (fun n => b n * D n) m)
    (hz : HasSum (fun n : ℕ => b n * ((n % p : ℕ) : ℝ)) 0)
    (hD : ∀ n : ℕ, n ≤ Y → |D n| ≤ δ * n)
    (hK : ∀ n : ℕ, Y < n → |D n| ≤ K) :
    |m| ≤ 2 * δ * (∑ n ∈ Finset.range (X + 1), max (b n) 0 * (n : ℝ)) + (δ * (p : ℝ)) * (∑' n, if X < n then |b n| else 0) + K * (∑' n, if Y < n then |b n| else 0) := by
  classical
  let L := fun n : ℕ => if n ≤ Y then D n else 0
  let T := fun n : ℕ => δ * ((n % p : ℕ) : ℝ)
  have hLs : Summable (fun n => b n * L n) := by
    apply summable_of_ne_finset_zero (s := Finset.range (Y + 1))
    intro n hn
    have h : ¬ n ≤ Y := by simp only [Finset.mem_range] at hn; omega
    simp [L, h]
  have hT : HasSum (fun n => b n * T n) 0 := by
    have hs := hz.mul_left δ
    rw [mul_zero] at hs
    apply hs.congr_fun
    intro n
    dsimp [T]
    ring
  have hTpos (n : ℕ) : 0 ≤ T n := mul_nonneg hδ (Nat.cast_nonneg _)
  have hnear := pairing_le_one_sided_prefix_and_tail b L T (Finset.range (X + 1))
    _ δ (δ * (p : ℝ)) 0 hb hLs.hasSum hT
    (fun n _ => by
      by_cases hn : n ≤ Y
      · simpa only [L, if_pos hn, T, Nat.mod_eq_of_lt (lt_of_le_of_lt hn hp)] using hD n hn
      · simpa only [L, if_neg hn, abs_zero] using hTpos n)
    (fun n _ => mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.mod_le n p) hδ)
    (fun n _ => by
      rw [abs_of_nonneg (hTpos n)]
      exact mul_le_mul_of_nonneg_left
        (by exact_mod_cast (Nat.mod_lt n (lt_of_le_of_lt (Nat.zero_le _) hp)).le) hδ)
    (fun n hn => by
      have h : ¬ n ≤ Y := by simp only [Finset.mem_range] at hn; omega
      simp [L, h])
  have htailEq : (∑' n, if n ∈ Finset.range (X + 1) then 0 else |b n|) =
      ∑' n, if X < n then |b n| else 0 := by
    apply tsum_congr
    intro n
    by_cases hn : X < n <;> simp [Finset.mem_range, show n < X + 1 ↔ ¬ X < n by omega, hn]
  rw [add_zero, htailEq] at hnear
  let A := fun n : ℕ => if Y < n then |b n| else 0
  have hA : Summable A := by
    apply Summable.of_nonneg_of_le _ _ hb.abs
    · intro n
      by_cases hn : Y < n <;> simp [A, hn, abs_nonneg]
    · intro n
      by_cases hn : Y < n <;> simp [A, hn, abs_nonneg]
  have hrem (n : ℕ) : |b n * D n - b n * L n| ≤ K * A n := by
    by_cases hn : n ≤ Y
    · simp [L, A, hn, not_lt.mpr hn]
    · have hy : Y < n := Nat.lt_of_not_ge hn
      simp only [L, if_neg hn, mul_zero, sub_zero, abs_mul, A, if_pos hy]
      rw [mul_comm K]
      exact mul_le_mul_of_nonneg_left (hK n hy) (abs_nonneg _)
  have he := hm.sub hLs.hasSum
  have hfar : |m - ∑' n, b n * L n| ≤ K * ∑' n, A n := by
    apply abs_le.mpr
    constructor
    · have hl := hasSum_le (fun n => (neg_le_abs (b n * D n - b n * L n)).trans (hrem n))
          he.neg (hA.hasSum.mul_left K)
      linarith
    · exact hasSum_le (fun n => (le_abs_self _).trans (hrem n)) he (hA.hasSum.mul_left K)
  calc
    |m| = |(∑' n, b n * L n) + (m - ∑' n, b n * L n)| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hnear hfar)

end RiemannResearch.Analysis

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis
open PrimeResidueMixture

/-- Control a bounded defect with small global slope using one-sided mass at
any given (possibly sparse) cutoff. The clipped weight `min δ (K / n)`
produces a Stieltjes mixture with a uniform harmonic upper bound. -/
theorem pairing_le_clipped_residue_mixture (b D : ℕ → ℝ) (X : ℕ) (m δ K : ℝ)
    (hδ : 0 ≤ δ) (hb : Summable b) (hm : HasSum (fun n => b n * D n) m)
    (hz : ∀ p : ℕ, p.Prime → HasSum (fun n : ℕ => b n * ((n % p : ℕ) : ℝ)) 0)
    (hD : ∀ n : ℕ, |D n| ≤ δ * n) (hK : ∀ n : ℕ, |D n| ≤ K) :
    |m| ≤ 2 * δ * (∑ n ∈ Finset.range (X + 1), max (b n) 0 * (n : ℝ)) + (2 * (K * (harmonic (X + 1) : ℝ)) + K) * (∑' n, if X < n then |b n| else 0) := by
  classical
  let h := fun j : ℕ => min δ (K / ((j + 1 : ℕ) : ℝ))
  have hK0 := (abs_nonneg _).trans (hK 0)
  have hh : Antitone h := by
    intro i j hij
    apply min_le_min_left
    exact div_le_div_of_nonneg_left hK0 (by positivity) (by exact_mod_cast Nat.succ_le_succ hij)
  have h₀ (j : ℕ) : 0 ≤ h j := le_min hδ (div_nonneg hK0 (Nat.cast_nonneg _))
  choose p hprime hlo hhi using fun j : ℕ =>
    Nat.exists_prime_lt_and_le_two_mul (j + 1) (Nat.succ_ne_zero j)
  let T := fun J n : ℕ => cutMix h (fun j => ((n % p j : ℕ) : ℝ)) J
  have hTpos (J n : ℕ) : 0 ≤ T J n := by
    unfold T cutMix
    exact add_nonneg (Finset.sum_nonneg fun j _ =>
      mul_nonneg (sub_nonneg.mpr (hh (Nat.le_succ j))) (Nat.cast_nonneg _))
      (mul_nonneg (h₀ J) (Nat.cast_nonneg _))
  have hTzero (J : ℕ) : HasSum (fun n => b n * T J n) 0 := by
    induction J with
    | zero =>
      have hs := (hz (p 0) (hprime 0)).mul_left (h 0)
      rw [mul_zero] at hs
      apply hs.congr_fun
      intro n
      simp only [T, cutMix, Finset.range_zero, Finset.sum_empty, zero_add]
      ring
    | succ J ih =>
      have hd := (hz (p (J + 1)) (hprime (J + 1))).sub (hz (p J) (hprime J))
      have hs := ih.add (hd.mul_left (h (J + 1)))
      simp only [sub_zero, mul_zero, add_zero] at hs
      apply hs.congr_fun
      intro n
      dsimp only [T]
      rw [cutMix_succ]
      ring
  have hdom (n : ℕ) (hn : n ≤ X) : |D n| ≤ T X n := by
    cases n with
    | zero => exact (by simpa only [Nat.cast_zero, mul_zero] using hD 0 : |D 0| ≤ 0).trans (hTpos X 0)
    | succ i =>
      have hi : |D (i + 1)| ≤ h i * ((i + 1 : ℕ) : ℝ) := by
        by_cases hv : δ ≤ K / ((i + 1 : ℕ) : ℝ)
        · simpa only [h, min_eq_left hv] using hD (i + 1)
        · rw [show h i = K / ((i + 1 : ℕ) : ℝ) from min_eq_right (le_of_not_ge hv),
            div_mul_cancel₀ _ (by positivity)]
          exact hK (i + 1)
      exact hi.trans (residue_head_lower h p hh hlo i X (by omega))
  have hconst (x : ℝ) (J : ℕ) : cutMix h (fun _ => x) J = h 0 * x := by
    induction J with
    | zero => simp [cutMix]
    | succ J ih => rw [cutMix_succ, ih]; simp
  have hlin (n : ℕ) : T X n ≤ δ * n := by
    calc
      T X n ≤ cutMix h (fun _ => (n : ℝ)) X := cutMix_mono h _ _ hh h₀
        (fun j => by exact_mod_cast Nat.mod_le n (p j)) X
      _ = _ := hconst _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg n)
  have hind (J : ℕ) : cutMix h (fun j => ((j + 1 : ℕ) : ℝ)) J =
      ∑ j ∈ Finset.range (J + 1), h j := by
    induction J with
    | zero => simp [cutMix]
    | succ J ih =>
      rw [cutMix_succ, ih, Finset.sum_range_succ _ (J + 1)]
      push_cast
      ring
  have hharm : (∑ j ∈ Finset.range (X + 1), h j) ≤ K * (harmonic (X + 1) : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (X + 1), K / ((j + 1 : ℕ) : ℝ) :=
        Finset.sum_le_sum (fun j _ => min_le_right _ _)
      _ = _ := by simp [harmonic, div_eq_mul_inv, Finset.mul_sum]
  have hcap (n : ℕ) : T X n ≤ 2 * (K * (harmonic (X + 1) : ℝ)) := by
    calc
      T X n ≤ cutMix h (fun j => 2 * ((j + 1 : ℕ) : ℝ)) X :=
        cutMix_mono h _ _ hh h₀ (fun j => by exact_mod_cast
          ((Nat.mod_lt n (hprime j).pos).le.trans (hhi j))) X
      _ = 2 * (∑ j ∈ Finset.range (X + 1), h j) := by rw [cutMix_const_mul, hind]
      _ ≤ _ := mul_le_mul_of_nonneg_left hharm zero_le_two
  have hp := pairing_le_one_sided_prefix_and_tail b D (T X) (Finset.range (X + 1))
    m δ (2 * (K * (harmonic (X + 1) : ℝ))) K hb hm (hTzero X)
    (fun n hn => hdom n (by simpa using hn)) (fun n _ => hlin n)
    (fun n _ => by simpa only [abs_of_nonneg (hTpos X n)] using hcap n) (fun n _ => hK n)
  have htail : (∑' n, if n ∈ Finset.range (X + 1) then 0 else |b n|) =
      ∑' n, if X < n then |b n| else 0 := by
    apply tsum_congr
    intro n
    by_cases hn : X < n <;> simp [Finset.mem_range, show n < X + 1 ↔ ¬ X<n by omega, hn]
  simpa only [htail] using hp

end RiemannResearch.Analysis
