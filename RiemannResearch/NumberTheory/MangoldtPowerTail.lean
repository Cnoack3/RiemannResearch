import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Explicit von Mangoldt power and logarithmic tails

Abel summation retains both endpoint terms exactly. The unconditional
Chebyshev estimate psi(x) <= (log 4 + 4)x gives a uniform finite tail
bound, then monotonicity of log supplies the extra factor 1/log N.
These arithmetic estimates have no RH hypothesis.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace RiemannResearch.NumberTheory.MangoldtPowerTail

def chebyshevConstant : ℝ := Real.log 4 + 4

theorem chebyshevConstant_pos : 0 < chebyshevConstant := by
  have h := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
  dsimp [chebyshevConstant]
  linarith

theorem psi_nat_sum (N : ℕ) :
    (∑ k ∈ Finset.Icc 0 N, ArithmeticFunction.vonMangoldt k) = Chebyshev.psi (N:ℝ) := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]

theorem rpow_continuousOn {N M : ℕ} (hN : 0 < N) (p : ℝ) :
    ContinuousOn (fun x : ℝ => x^p) (Icc (N:ℝ) (M:ℝ)) := by
  apply continuousOn_id.rpow_const
  intro x hx
  exact Or.inl (ne_of_gt ((Nat.cast_pos.mpr hN).trans_le hx.1))

theorem power_abel (s : ℝ) {N M : ℕ} (hN : 0 < N) (hNM : N ≤ M) :
    (∑ k ∈ Finset.Ioc N M, ArithmeticFunction.vonMangoldt k * (k:ℝ)^(-s)) =
      Chebyshev.psi (M:ℝ) * (M:ℝ)^(-s) -
      Chebyshev.psi (N:ℝ) * (N:ℝ)^(-s) +
      s * ∫ t in Ioc (N:ℝ) (M:ℝ), Chebyshev.psi t * t^(-s-1) := by
  have hd (x : ℝ) (hx : x ∈ Icc (N:ℝ) (M:ℝ)) :
      HasDerivAt (fun t : ℝ => t^(-s)) (-s*x^(-s-1)) x :=
    Real.hasDerivAt_rpow_const
      (Or.inl (ne_of_gt ((Nat.cast_pos.mpr hN).trans_le hx.1)))
  have hi : IntegrableOn (deriv (fun t : ℝ => t^(-s))) (Icc (N:ℝ) (M:ℝ)) := by
    apply ((rpow_continuousOn hN (-s-1)).const_mul (-s)).integrableOn_Icc.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact (hd x hx).deriv.symm
  have hab := sum_mul_eq_sub_sub_integral_mul' ArithmeticFunction.vonMangoldt hNM
    (fun x hx => (hd x hx).differentiableAt) hi
  have hint :
      (∫ t in Ioc (N:ℝ) (M:ℝ), deriv (fun x : ℝ => x^(-s)) t *
          ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt k) =
      -s * ∫ t in Ioc (N:ℝ) (M:ℝ), Chebyshev.psi t * t^(-s-1) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [(hd t ⟨ht.1.le, ht.2⟩).deriv, ← Chebyshev.psi_eq_sum_Icc]
    ring
  rw [psi_nat_sum, psi_nat_sum, hint] at hab
  calc
    _ = ∑ k ∈ Finset.Ioc N M, (k:ℝ)^(-s) * ArithmeticFunction.vonMangoldt k := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = _ := by rw [hab]; ring

theorem psi_power_integrable {N M : ℕ} (hN : 0 < N) (s : ℝ) :
    IntegrableOn (fun t : ℝ => Chebyshev.psi t * t^(-s-1)) (Ioc (N:ℝ) (M:ℝ)) := by
  have h := integrableOn_mul_sum_Icc ArithmeticFunction.vonMangoldt
    (m := 0) (Nat.cast_nonneg N) ((rpow_continuousOn (M:=M) hN (-s-1)).integrableOn_Icc)
  simp_rw [← Chebyshev.psi_eq_sum_Icc, mul_comm] at h
  exact h.mono_set Ioc_subset_Icc_self

theorem power_tail_finite_bound {s : ℝ} (hs : 1 < s) {N M : ℕ}
    (hN : 0 < N) (hNM : N ≤ M) :
    (∑ k ∈ Finset.Ioc N M, ArithmeticFunction.vonMangoldt k * (k:ℝ)^(-s)) ≤
      chebyshevConstant * (1+s/(s-1)) * (N:ℝ)^(1-s) := by
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hm : (0:ℝ) < M := lt_of_lt_of_le hn (Nat.cast_le.mpr hNM)
  have hr : ∀ x : ℝ, 0 < x → x*x^(-s-1) = x^(-s) := by
    intro x hx
    calc
      _ = x^(1:ℝ)*x^(-s-1) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hx]; congr 1; ring
  have hb : ∀ x : ℝ, 0 < x →
      Chebyshev.psi x * x^(-s-1) ≤ chebyshevConstant*x^(-s) := by
    intro x hx
    calc
      _ ≤ (chebyshevConstant*x)*x^(-s-1) :=
        mul_le_mul_of_nonneg_right (Chebyshev.psi_le_const_mul_self hx.le)
          (Real.rpow_nonneg hx.le _)
      _ = _ := by rw [mul_assoc, hr x hx]
  have hp := integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) hn
  have hps : IntegrableOn (fun x : ℝ => chebyshevConstant*x^(-s)) (Ioi (N:ℝ)) :=
    hp.const_mul chebyshevConstant
  have hle := setIntegral_mono_on (psi_power_integrable hN s)
    (hps.mono_set (show Ioc (N:ℝ) (M:ℝ) ⊆ Ioi (N:ℝ) from fun _ hx => hx.1))
    measurableSet_Ioc (fun x hx => hb x (hn.trans hx.1))
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (N:ℝ))]
      (fun x : ℝ => chebyshevConstant*x^(-s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg chebyshevConstant_pos.le (Real.rpow_nonneg (hn.trans hx).le _)
  have hle2 := setIntegral_mono_set hps hnonneg
    (Filter.Eventually.of_forall (show ∀ x, x ∈ Ioc (N:ℝ) (M:ℝ) → x ∈ Ioi (N:ℝ)
      from fun _ hx => hx.1))
  have hint : (∫ x in Ioi (N:ℝ), chebyshevConstant*x^(-s)) =
      chebyshevConstant * (N:ℝ)^(1-s)/(s-1) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -s < -1) hn]
    rw [show -s+1=1-s by ring]
    rw [show 1-s = -(s-1) by ring, div_neg, neg_div, neg_neg]
    ring
  rw [hint] at hle2
  have hbound := hle.trans hle2
  have hend : Chebyshev.psi (M:ℝ)*(M:ℝ)^(-s) ≤
      chebyshevConstant*(N:ℝ)^(1-s) := by
    calc
      _ ≤ (chebyshevConstant*(M:ℝ))*(M:ℝ)^(-s) :=
        mul_le_mul_of_nonneg_right (Chebyshev.psi_le_const_mul_self hm.le)
          (Real.rpow_nonneg hm.le _)
      _ = chebyshevConstant*(M:ℝ)^(1-s) := by
        rw [mul_assoc]
        congr 1
        calc
          _ = (M:ℝ)^(1:ℝ)*(M:ℝ)^(-s) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hm]; congr 1
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hn (Nat.cast_le.mpr hNM) (by linarith))
        chebyshevConstant_pos.le
  rw [power_abel s hN hNM]
  have hstart : 0 ≤ Chebyshev.psi (N:ℝ)*(N:ℝ)^(-s) :=
    mul_nonneg (Chebyshev.psi_nonneg _) (Real.rpow_nonneg hn.le _)
  have hmul := mul_le_mul_of_nonneg_left hbound (by linarith : 0 ≤ s)
  calc
    _ ≤ chebyshevConstant*(N:ℝ)^(1-s) +
        s*(chebyshevConstant*(N:ℝ)^(1-s)/(s-1)) := by linarith
    _ = _ := by ring

theorem log_power_tail_finite_bound {s : ℝ} (hs : 1 < s) {N M : ℕ}
    (hN : 2 ≤ N) (hNM : N ≤ M) :
    (∑ k ∈ Finset.Ioc N M,
      ArithmeticFunction.vonMangoldt k / Real.log (k:ℝ) * (k:ℝ)^(-s)) ≤
      chebyshevConstant * (1+s/(s-1)) * (N:ℝ)^(1-s) / Real.log (N:ℝ) := by
  have hn : (1:ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hl : 0 < Real.log (N:ℝ) := Real.log_pos hn
  calc
    _ ≤ ∑ k ∈ Finset.Ioc N M,
        (ArithmeticFunction.vonMangoldt k * (k:ℝ)^(-s)) / Real.log (N:ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      have hnk : (N:ℝ) ≤ k := Nat.cast_le.mpr (Finset.mem_Ioc.mp hk).1.le
      have hlog := Real.log_le_log (by linarith : (0:ℝ) < N) hnk
      calc
        _ ≤ (ArithmeticFunction.vonMangoldt k / Real.log (N:ℝ)) * (k:ℝ)^(-s) :=
          mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg hl hlog)
            (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ = _ := by ring
    _ = (∑ k ∈ Finset.Ioc N M, ArithmeticFunction.vonMangoldt k * (k:ℝ)^(-s)) /
        Real.log (N:ℝ) := by rw [Finset.sum_div]
    _ ≤ _ := div_le_div_of_nonneg_right
      (power_tail_finite_bound hs (by omega) hNM) hl.le

end RiemannResearch.NumberTheory.MangoldtPowerTail
