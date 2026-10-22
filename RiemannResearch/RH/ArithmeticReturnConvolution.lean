import RiemannResearch.RH.ArithmeticReturnSupport
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Field

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Dirichlet convolution is actual arithmetic-return composition

Source: user-provided argument, equation (9.6).  The proof regroups a finite
set of actual translated-function values on each bounded observation window.
It does not assume a convolution or synthesis identity.
-/

open scoped BigOperators Topology

namespace Nat

/-- Regroup finite divisor antidiagonals as a product-bounded rectangular sum. -/
theorem sum_divisorsAntidiagonal_range {A : Type*} [AddCommMonoid A]
    (N : ℕ) (F : ℕ → ℕ → A)
    (hF0 : ∀ k, F 0 k = 0) (hF1 : ∀ k, F k 0 = 0) :
    (∑ m ∈ Finset.range (N + 1), ∑ p ∈ m.divisorsAntidiagonal, F p.1 p.2) =
      ∑ k ∈ Finset.range (N + 1), ∑ l ∈ Finset.range (N + 1),
        if k * l ≤ N then F k l else 0 := by
  classical
  let S := ((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1))).filter
    (fun p : ℕ × ℕ => p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 * p.2 ≤ N)
  have hsum :
      (∑ z ∈ (Finset.range (N + 1)).sigma (fun m => m.divisorsAntidiagonal),
        F z.2.1 z.2.2) = ∑ p ∈ S, F p.1 p.2 := by
    refine Finset.sum_bij (fun z _ => z.2) ?_ ?_ ?_ ?_
    · intro z hz
      rcases Finset.mem_sigma.mp hz with ⟨hm, hp⟩
      rcases Nat.mem_divisorsAntidiagonal.mp hp with ⟨hprod, hm0⟩
      have hprod0 : z.2.1 * z.2.2 ≠ 0 := by rw [hprod]; exact hm0
      have hp0 : z.2.1 ≠ 0 ∧ z.2.2 ≠ 0 := mul_ne_zero_iff.mp hprod0
      have hmN : z.1 ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
      have h1prod : z.2.1 ≤ z.2.1 * z.2.2 := by
        simpa only [Nat.mul_one] using
          Nat.mul_le_mul_left z.2.1 (Nat.one_le_iff_ne_zero.mpr hp0.2)
      have h2prod : z.2.2 ≤ z.2.1 * z.2.2 := by
        simpa only [Nat.one_mul] using
          Nat.mul_le_mul_right z.2.2 (Nat.one_le_iff_ne_zero.mpr hp0.1)
      have h1N : z.2.1 ≤ N := h1prod.trans (by simpa only [hprod] using hmN)
      have h2N : z.2.2 ≤ N := h2prod.trans (by simpa only [hprod] using hmN)
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hp0.1, hp0.2, ?_⟩
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le h1N)
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le h2N)
      · simpa only [hprod] using hmN
    · intro z hz w hw heq
      have hzmul := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hz).2).1
      have hwmul := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hw).2).1
      have hfst : z.1 = w.1 := by rw [← hzmul, ← hwmul, heq]
      exact Sigma.ext hfst (heq_of_eq heq)
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpR, hp0, hp1, hpN⟩
      refine ⟨⟨p.1 * p.2, p⟩, ?_, rfl⟩
      apply Finset.mem_sigma.mpr
      exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hpN),
        Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, mul_ne_zero hp0 hp1⟩⟩
    · intro z hz
      rfl
  calc
    _ = ∑ p ∈ S, F p.1 p.2 := by
      simpa only [Finset.sum_sigma'] using hsum
    _ = ∑ k ∈ Finset.range (N + 1), ∑ l ∈ Finset.range (N + 1),
        if k * l ≤ N then F k l else 0 := by
      dsimp [S]
      rw [Finset.sum_filter, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      by_cases hk0 : k = 0
      · simp [hk0, hF0]
      by_cases hl0 : l = 0
      · simp [hl0, hF1]
      simp [hk0, hl0]

end Nat

namespace RiemannResearch.RH

private theorem arithmeticReturn_weight_product (c d : ArithmeticFunction ℝ)
    (u : ℝ → ℂ) (y : ℝ) {k l : ℕ} (hk : k ≠ 0) (hl : l ≠ 0) :
    ((c k * d l) / Real.sqrt (k * l : ℕ) : ℝ) •
        u (y - Real.log (k * l : ℕ)) =
      (c k / Real.sqrt k : ℝ) •
        ((d l / Real.sqrt l : ℝ) • u ((y - Real.log k) - Real.log l)) := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hl0 : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hl
  rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg k),
    Real.log_mul hk0 hl0, smul_smul, div_mul_div_comm]
  congr 2
  ring

/-- The actual function-level convolution identity. Both infinite returns are
proved locally finite from the lower support bound of the original test. -/
theorem arithmeticReturn_mul (c d : ArithmeticFunction ℝ)
    {u : ℝ → ℂ} {a : ℝ} (hu : ∀ x < a, u x = 0) :
    arithmeticReturn (c * d) u = arithmeticReturn c (arithmeticReturn d u) := by
  funext y
  obtain ⟨N, hN0⟩ := exists_nat_gt (Real.exp (y - a))
  have hN : Real.exp (y - a) < (N + 1 : ℕ) :=
    lt_trans hN0 (by exact_mod_cast Nat.lt_succ_self N)
  let F : ℕ → ℕ → ℂ := fun k l => (c k / Real.sqrt k : ℝ) •
    ((d l / Real.sqrt l : ℝ) • u ((y - Real.log k) - Real.log l))
  have hF0 : ∀ k, F 0 k = 0 := by intro k; simp [F]
  have hF1 : ∀ k, F k 0 = 0 := by intro k; simp [F]
  have hfar : ∀ k l, ¬ k * l ≤ N → F k l = 0 := by
    intro k l hkl
    have hk : k ≠ 0 := by intro hk; simp [hk] at hkl
    have hl : l ≠ 0 := by intro hl; simp [hl] at hkl
    have hprodpos : (0 : ℝ) < (k * l : ℕ) := by positivity
    have hNk : N + 1 ≤ k * l := by omega
    have he : Real.exp (y - a) < (k * l : ℕ) :=
      lt_of_lt_of_le hN (by exact_mod_cast hNk)
    have hx : y - a < Real.log (k * l : ℕ) :=
      (Real.lt_log_iff_exp_lt hprodpos).mpr he
    have hlog : Real.log (k * l : ℕ) = Real.log k + Real.log l := by
      rw [Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr hk) (Nat.cast_ne_zero.mpr hl)]
    rw [hlog] at hx
    have hu0 : u ((y - Real.log k) - Real.log l) = 0 := hu _ (by linarith)
    simp [F, hu0]
  calc
    arithmeticReturn (c * d) u y =
        ∑ m ∈ Finset.range (N + 1),
          ((c * d) m / Real.sqrt m : ℝ) • u (y - Real.log m) :=
      arithmeticReturn_eq_sum _ hu le_rfl hN
    _ = ∑ m ∈ Finset.range (N + 1),
        ∑ p ∈ m.divisorsAntidiagonal, F p.1 p.2 := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [ArithmeticFunction.mul_apply, Finset.sum_div, Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro p hp
      rcases Nat.mem_divisorsAntidiagonal.mp hp with ⟨hprod, hm0⟩
      have hp0 : p.1 ≠ 0 ∧ p.2 ≠ 0 := mul_ne_zero_iff.mp (by rw [hprod]; exact hm0)
      rw [← hprod]
      exact arithmeticReturn_weight_product c d u y hp0.1 hp0.2
    _ = ∑ k ∈ Finset.range (N + 1), ∑ l ∈ Finset.range (N + 1),
        if k * l ≤ N then F k l else 0 :=
      Nat.sum_divisorsAntidiagonal_range N F hF0 hF1
    _ = ∑ k ∈ Finset.range (N + 1), ∑ l ∈ Finset.range (N + 1), F k l := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      by_cases hkl : k * l ≤ N
      · rw [if_pos hkl]
      · rw [if_neg hkl, hfar k l hkl]
    _ = ∑ k ∈ Finset.range (N + 1), (c k / Real.sqrt k : ℝ) •
        arithmeticReturn d u (y - Real.log k) := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hk0 : k = 0
      · simp [hk0, F]
      have hyk : y - Real.log k ≤ y := by
        have := Real.log_nonneg (show (1 : ℝ) ≤ k by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0)
        linarith
      rw [arithmeticReturn_eq_sum d hu hyk hN, Finset.smul_sum]
    _ = arithmeticReturn c (arithmeticReturn d u) y := by
      symm
      exact arithmeticReturn_eq_sum c
        (fun x hx => arithmeticReturn_zero_below d hu hx) le_rfl hN

theorem arithmeticReturn_one (u : ℝ → ℂ) : arithmeticReturn 1 u = u := by
  funext y
  simp [arithmeticReturn, ArithmeticFunction.one_apply, ite_div, ite_smul]

theorem arithmeticReturn_sub (c d : ArithmeticFunction ℝ)
    {u : ℝ → ℂ} {a : ℝ} (hu : ∀ x < a, u x = 0) :
    arithmeticReturn (c - d) u = arithmeticReturn c u - arithmeticReturn d u := by
  funext y
  change (∑' k : ℕ, ((c k - d k) / Real.sqrt k : ℝ) • u (y - Real.log k)) =
    (∑' k : ℕ, (c k / Real.sqrt k : ℝ) • u (y - Real.log k)) -
      ∑' k : ℕ, (d k / Real.sqrt k : ℝ) • u (y - Real.log k)
  simp only [sub_div, sub_smul]
  exact (arithmeticReturn_summable c (y := y) hu).tsum_sub
    (arithmeticReturn_summable d (y := y) hu)

/-- Exact synthesis of the completed potential by the true nested full return. -/
theorem nymanFullReturn_inversePotential (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a : ℝ} (hv : ∀ x < a, v x = 0) :
    nymanFullReturn n (nymanInversePotential n M hn v) =
      v + nymanArithmeticTailPotential n M hn v := by
  rw [nymanFullReturn, nymanInversePotential_eq_return, ← arithmeticReturn_mul _ _ hv]
  rw [nymanArithmeticTailPotential, arithmeticReturn_sub _ _ hv, arithmeticReturn_one]
  abel

/-- The support conclusion now concerns the actual nested arithmetic return,
not only a coefficient-defined surrogate. -/
theorem nymanFullReturn_inversePotential_tsupport (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a : ℝ} (hv : ∀ x < a, v x = 0) :
    tsupport (nymanFullReturn n (nymanInversePotential n M hn v) - v) ⊆
      Set.Ici (a + Real.log (M + 1 : ℕ)) := by
  rw [nymanFullReturn_inversePotential n M hn hv, add_sub_cancel_left]
  exact nymanArithmeticTailPotential_tsupport n M hn hv

end RiemannResearch.RH
