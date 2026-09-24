import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-!
# Uniform square bounds for quotient windows

Source: Michel Balazard, arXiv:1812.04309, Proposition 5, proof strategy.
This is the alpha=2 estimate used in Proposition 6 and the reciprocal
Mobius charge identity of Proposition 7. The split below is at d(d+1)=N,
so no real square-root or asymptotic notation is needed.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.NumberTheory.QuotientWindow

def window (N d : ℕ) : Finset ℕ := Finset.Ioc (N / (d + 1)) (N / d)

theorem mem_window_bounds {N d n : ℕ} (hd : 0 < d) (hn : n ∈ window N d) :
    0 < n ∧ n ≤ N ∧ d * n ≤ N ∧ N < (d + 1) * n := by
  have hn' : N / (d + 1) < n ∧ n ≤ N / d := by
    simpa only [window, Finset.mem_Ioc] using hn
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn'.1
  have hdn : n * d ≤ N := (Nat.le_div_iff_mul_le hd).mp hn'.2
  have hnd : N < n * (d + 1) :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < d + 1)).mp hn'.1
  refine ⟨hn0, ?_, ?_, ?_⟩ <;> nlinarith

theorem quotient_of_mem_window {N d n : ℕ} (hd : 0 < d)
    (hn : n ∈ window N d) : N / n = d := by
  obtain ⟨hn0, _, hlo, hhi⟩ := mem_window_bounds hd hn
  have hlow : d ≤ N / n := (Nat.le_div_iff_mul_le hn0).mpr hlo
  have hhigh : N / n < d + 1 := (Nat.div_lt_iff_lt_mul hn0).mpr hhi
  omega

theorem window_subset {N d : ℕ} (hd : 0 < d) :
    window N d ⊆ Finset.Icc 1 N := by
  intro n hn
  obtain ⟨hn0, hnN, _, _⟩ := mem_window_bounds hd hn
  exact Finset.mem_Icc.mpr ⟨hn0, hnN⟩

theorem pairwise_disjoint (N : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.Icc 1 N) : Set ℕ) (window N) := by
  intro d hd e he hde
  apply Finset.disjoint_left.mpr
  intro n hnd hne
  have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
  have he0 : 0 < e := (Finset.mem_Icc.mp he).1
  exact hde ((quotient_of_mem_window hd0 hnd).symm.trans
    (quotient_of_mem_window he0 hne))

/-- Above the diagonal, each quotient window contains at most one integer. -/
theorem window_subsingleton {N d : ℕ} (hd : 0 < d) (hN : N < d * (d + 1)) :
    (window N d : Set ℕ).Subsingleton := by
  intro n hn m hm
  obtain ⟨_, _, hdn, hNn⟩ := mem_window_bounds hd hn
  obtain ⟨_, _, hdm, hNm⟩ := mem_window_bounds hd hm
  have hnD : n ≤ d := by nlinarith
  have hmD : m ≤ d := by nlinarith
  rcases lt_trichotomy n m with h | h | h
  · have hh : n + 1 ≤ m := h
    nlinarith
  · exact h
  · have hh : m + 1 ≤ n := h
    nlinarith

/-- Below the diagonal, a full harmonic window has an exact elementary bound. -/
theorem harmonic_window_le {N d : ℕ} (hd : 0 < d) (hN : d * (d + 1) ≤ N) :
    (∑ n ∈ window N d, 1 / (n : ℝ)) ≤ 2 / (d : ℝ) := by
  let a := N / (d + 1)
  let b := N / d
  have ha : d ≤ a := (Nat.le_div_iff_mul_le (by omega : 0 < d + 1)).mpr hN
  have hbN : b * d ≤ N := Nat.div_mul_le_self N d
  have haN : a * (d + 1) ≤ N := Nat.div_mul_le_self N (d + 1)
  have hab : a ≤ b := (Nat.le_div_iff_mul_le hd).mpr (by nlinarith)
  have hNlt : N < (a + 1) * (d + 1) := by
    have hm := Nat.mod_lt N (by omega : 0 < d + 1)
    have he := Nat.mod_add_div N (d + 1)
    dsimp [a]
    nlinarith
  have hsub : b - a + a = b := Nat.sub_add_cancel hab
  have hc : d * (b - a) ≤ 2 * (a + 1) := by nlinarith
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have haR : 0 < (a : ℝ) + 1 := by positivity
  calc
    (∑ n ∈ window N d, 1 / (n : ℝ)) ≤
        ∑ _n ∈ window N d, 1 / ((a : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' : a < n := (Finset.mem_Ioc.mp hn).1
      have hnR : (a : ℝ) + 1 ≤ (n : ℝ) := by
        exact_mod_cast (show a + 1 ≤ n from hn')
      exact one_div_le_one_div_of_le haR hnR
    _ = ((b - a : ℕ) : ℝ) / ((a : ℝ) + 1) := by
      simp [window, a, b, Nat.card_Ioc, nsmul_eq_mul, div_eq_mul_inv]
    _ ≤ 2 / (d : ℝ) := by
      apply (div_le_div_iff₀ haR hdR).mpr
      have hcR : (d : ℝ) * ((b - a : ℕ) : ℝ) ≤ 2 * ((a : ℝ) + 1) := by
        exact_mod_cast hc
      nlinarith

theorem window_sum_sq_le (η : ℕ → ℝ) (hη : ∀ n, 0 < n → |η n| ≤ 1 / (n : ℝ))
    {N d : ℕ} (hd : 0 < d) :
    (∑ n ∈ window N d, η n) ^ 2 ≤
      4 / (d : ℝ) ^ 2 + ∑ n ∈ window N d, 1 / (n : ℝ) ^ 2 := by
  by_cases hN : d * (d + 1) ≤ N
  · have hs : |∑ n ∈ window N d, η n| ≤ 2 / (d : ℝ) := by
      calc
        _ ≤ ∑ n ∈ window N d, |η n| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ n ∈ window N d, 1 / (n : ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          exact hη n (mem_window_bounds hd hn).1
        _ ≤ _ := harmonic_window_le hd hN
    have hq : (∑ n ∈ window N d, η n) ^ 2 ≤ 4 / (d : ℝ) ^ 2 := by
      have ht := sq_le_sq₀ (abs_nonneg (∑ n ∈ window N d, η n))
        (by positivity : (0 : ℝ) ≤ 2 / (d : ℝ))
      have hh := ht.mpr hs
      simpa only [sq_abs, div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using hh
    exact hq.trans (le_add_of_nonneg_right (Finset.sum_nonneg fun n _ => by positivity))
  · have hsub := window_subsingleton hd (by omega : N < d * (d + 1))
    have hq : (∑ n ∈ window N d, η n) ^ 2 ≤
        ∑ n ∈ window N d, 1 / (n : ℝ) ^ 2 := by
      by_cases he : (window N d).Nonempty
      · obtain ⟨n, hn⟩ := he
        have hw : window N d = {n} := Finset.eq_singleton_iff_unique_mem.mpr
          ⟨hn, fun m hm => hsub hm hn⟩
        rw [hw]
        simp only [Finset.sum_singleton]
        have hh := hη n (mem_window_bounds hd hn).1
        have ht := (sq_le_sq₀ (abs_nonneg (η n)) (by positivity : 0 ≤ 1 / (n : ℝ))).mpr hh
        simpa [sq_abs, div_pow] using ht
      · simp [Finset.not_nonempty_iff_eq_empty.mp he]
    exact hq.trans (le_add_of_nonneg_left (by positivity))

/-- A telescoping majorant avoids any appeal to an evaluated zeta value. -/
theorem reciprocal_square_sum_le_two (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ) ^ 2) ≤ 2 := by
  have htel (M : ℕ) :
      (∑ n ∈ Finset.Icc 1 M, (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))) =
        1 - 1 / ((M : ℝ) + 1) := by
    induction M with
    | zero => norm_num
    | succ M ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      push_cast
      ring
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, 2 * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hn0 : (0 : ℝ) < n := by linarith
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      apply le_of_sub_nonneg
      have he : 2 * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) -
          1 / (n : ℝ) ^ 2 =
          ((n : ℝ) - 1) / ((n : ℝ) ^ 2 * ((n : ℝ) + 1)) := by
        field_simp
        ring
      rw [he]
      exact div_nonneg (sub_nonneg.mpr hnR) (by positivity)
    _ = 2 * (1 - 1 / ((N : ℝ) + 1)) := by rw [← Finset.mul_sum, htel]
    _ ≤ 2 := by
      have hi : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
      linarith

/-- An explicit uniform form of Balazard's Proposition 5 at exponent two. -/
theorem sum_window_sq_le_ten (η : ℕ → ℝ)
    (hη : ∀ n, 0 < n → |η n| ≤ 1 / (n : ℝ)) (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, (∑ n ∈ window N d, η n) ^ 2) ≤ 10 := by
  have hsecond : (∑ d ∈ Finset.Icc 1 N, ∑ n ∈ window N d, 1 / (n : ℝ) ^ 2) ≤ 2 := by
    calc
      _ = ∑ n ∈ (Finset.Icc 1 N).biUnion (window N), 1 / (n : ℝ) ^ 2 := by
        rw [Finset.sum_biUnion (pairwise_disjoint N)]
      _ ≤ ∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          obtain ⟨d, hd, hn⟩ := Finset.mem_biUnion.mp hn
          exact window_subset (Finset.mem_Icc.mp hd).1 hn
        · intro n _ _
          positivity
      _ ≤ 2 := reciprocal_square_sum_le_two N
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 N,
        (4 / (d : ℝ) ^ 2 + ∑ n ∈ window N d, 1 / (n : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro d hd
      exact window_sum_sq_le η hη (Finset.mem_Icc.mp hd).1
    _ = 4 * (∑ d ∈ Finset.Icc 1 N, 1 / (d : ℝ) ^ 2) +
        (∑ d ∈ Finset.Icc 1 N, ∑ n ∈ window N d, 1 / (n : ℝ) ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ 10 := by nlinarith [reciprocal_square_sum_le_two N]

end RiemannResearch.NumberTheory.QuotientWindow
