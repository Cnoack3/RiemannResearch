/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ArithmeticFloorHyperbola
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Signed hyperbola bounds with independent real exponents

This abstracts the classical exact hyperbola decomposition already formalized
in `ArithmeticFloorHyperbola`. All signed arithmetic estimates are hypotheses.
Integral comparison supplies the absolute finite residue-head bound; the
critical profile wrappers retain additional logarithmic or other savings.
-/

open scoped BigOperators
open RiemannResearch.Analysis MeasureTheory

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Integral comparison with the singular value at zero omitted. -/
theorem sum_nat_succ_neg_rpow_le {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (N : ℕ) :
    (∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) ^ (-a)) ≤
      (N : ℝ) ^ (1-a) / (1-a) := by
  have hp : 0 < 1-a := by linarith
  cases N with
  | zero => simp [Real.zero_rpow (ne_of_gt hp)]
  | succ n =>
    have hanti : AntitoneOn (fun x : ℝ => x ^ (-a))
        (Set.Icc 1 (1 + (n : ℝ))) := by
      intro x hx y hy hxy
      exact Real.rpow_le_rpow_of_nonpos
        (lt_of_lt_of_le zero_lt_one hx.1) hxy (neg_nonpos.mpr ha)
    have hsum := AntitoneOn.sum_le_integral (x₀ := 1) (a := n) hanti
    rw [integral_rpow (Or.inl (show -1 < -a by linarith))] at hsum
    have he : -a + 1 = 1-a := by ring
    rw [he, Real.one_rpow] at hsum
    have hs : (∑ k ∈ Finset.range n, ((k+1+1 : ℕ) : ℝ)^(-a)) ≤
        (((n+1 : ℕ) : ℝ)^(1-a)-1)/(1-a) := by
      simpa only [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc]
        using hsum
    rw [Finset.sum_range_succ']
    simp only [zero_add, Nat.cast_one, Real.one_rpow]
    calc
      _ ≤ (((n+1 : ℕ) : ℝ)^(1-a)-1)/(1-a) + 1 := by linarith
      _ ≤ ((n+1 : ℕ) : ℝ)^(1-a)/(1-a) := by
        apply (le_div_iff₀ hp).mpr
        rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hp), one_mul]
        linarith

private theorem rpow_nat_div_le (N k : ℕ) (hk : 0 < k)
    {a : ℝ} (ha : 0 ≤ a) :
    ((N/k : ℕ) : ℝ)^a ≤ (N : ℝ)^a / (k : ℝ)^a := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hquot : ((N/k : ℕ) : ℝ) ≤ (N : ℝ)/(k : ℝ) := by
    apply (le_div_iff₀ hkR).mpr
    exact_mod_cast Nat.div_mul_le_self N k
  calc
    _ ≤ ((N : ℝ)/(k : ℝ))^a :=
      Real.rpow_le_rpow (by positivity) hquot ha
    _ = _ := Real.div_rpow (by positivity) (by positivity) a

private theorem power_cross_identity {x y a : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x^a * (x/y)^(1-a) = x * y^(a-1) := by
  rw [Real.div_rpow hx.le hy.le, ← mul_div_assoc,
    ← Real.rpow_add hx]
  have he : a + (1-a) = 1 := by ring
  rw [he, Real.rpow_one]
  have he' : a-1 = -(1-a) := by ring
  rw [he', Real.rpow_neg hy.le, div_eq_mul_inv]

private theorem power_residue_sum_abs_le (w : ℕ → ℝ) (hw0 : w 0 = 0)
    {W ε : ℝ} (hW : 0 ≤ W) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hw : ∀ d : ℕ, 0 < d → |w d| ≤ W * (d : ℝ)^(-ε)) (N y : ℕ) :
    |∑ d ∈ Finset.range (y+1), (w d / (d : ℝ)) * residue d N| ≤
      (W/(1-ε)) * (y : ℝ)^(1-ε) := by
  rw [Finset.sum_range_succ']
  simp only [hw0, Nat.cast_zero, div_zero, zero_mul, add_zero]
  calc
    _ ≤ ∑ d ∈ Finset.range y,
        |(w (d+1) / ((d+1 : ℕ) : ℝ)) * residue (d+1) N| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.range y, W * ((d+1 : ℕ) : ℝ)^(-ε) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdR : (0 : ℝ) < ((d+1 : ℕ) : ℝ) := by positivity
      have hr0 : 0 ≤ residue (d+1) N := by unfold residue; positivity
      have hr : residue (d+1) N ≤ ((d+1 : ℕ) : ℝ) := by
        unfold residue
        exact_mod_cast (Nat.mod_lt N (by omega : 0 < d+1)).le
      rw [abs_mul, abs_div, abs_of_pos hdR, abs_of_nonneg hr0]
      calc
        _ ≤ (|w (d+1)| / ((d+1 : ℕ) : ℝ)) * ((d+1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hr (by positivity)
        _ = |w (d+1)| := div_mul_cancel₀ _ (ne_of_gt hdR)
        _ ≤ _ := hw (d+1) (by omega)
    _ = W * ∑ d ∈ Finset.range y, ((d+1 : ℕ) : ℝ)^(-ε) := by
      rw [Finset.mul_sum]
    _ ≤ W * ((y : ℝ)^(1-ε)/(1-ε)) :=
      mul_le_mul_of_nonneg_left (sum_nat_succ_neg_rpow_le hε hε1 y) hW
    _ = _ := by ring

/-- General signed-prefix/density-tail hyperbola bound. The prefix is
estimated before the square: its exponent is independent of the absolute
weight exponent. Every arithmetic cancellation assumption is explicit. -/
theorem arithmeticFloorPrefix_centered_hyperbola_power_bound
    (w : ℕ → ℝ) (hw0 : w 0 = 0) (C : ℝ)
    {N y : ℕ} (hy : 0 < y) (hyN : y ≤ N)
    {W B D ε a r : ℝ} (hW : 0 ≤ W) (hB : 0 ≤ B)
    (hε : 0 ≤ ε) (hε1 : ε < 1) (ha : 0 ≤ a) (ha1 : a < 1)
    (hw : ∀ d : ℕ, 0 < d → |w d| ≤ W * (d : ℝ)^(-ε))
    (hP : ∀ t : ℕ, y ≤ t → |positiveArithmeticPrefix w t| ≤ B*(t : ℝ)^a)
    (hD : |C - ∑ d ∈ Finset.range (y+1), w d/(d : ℝ)| ≤ D*(y : ℝ)^(-r)) :
    |arithmeticFloorPrefix w N - (N : ℝ)*C| ≤
      (W/(1-ε))*(y : ℝ)^(1-ε) +
      (B*(1 + 1/(1-a)))*(N : ℝ)*(y : ℝ)^(a-1) +
      D*(N : ℝ)*(y : ℝ)^(-r) := by
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hNR : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le hy hyN
  have ha1p : 0 < 1-a := by linarith
  have hmiddle : |∑ k ∈ Finset.range (N/y),
      positiveArithmeticPrefix w (N/(k+1))| ≤
      (B/(1-a))*(N : ℝ)*(y : ℝ)^(a-1) := by
    calc
      _ ≤ ∑ k ∈ Finset.range (N/y), |positiveArithmeticPrefix w (N/(k+1))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (N/y),
          (B*(N : ℝ)^a) * ((k+1 : ℕ) : ℝ)^(-a) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkq : k+1 ≤ N/y := Finset.mem_range.mp hk
        have ht : y ≤ N/(k+1) := by
          apply (Nat.le_div_iff_mul_le (by omega : 0 < k+1)).mpr
          simpa [mul_comm] using (Nat.le_div_iff_mul_le hy).mp hkq
        calc
          _ ≤ B*((N/(k+1) : ℕ) : ℝ)^a := hP _ ht
          _ ≤ B*((N : ℝ)^a / ((k+1 : ℕ) : ℝ)^a) :=
            mul_le_mul_of_nonneg_left (rpow_nat_div_le N (k+1) (by omega) ha) hB
          _ = _ := by rw [Real.rpow_neg (by positivity)]; ring
      _ = (B*(N : ℝ)^a) *
          (∑ k ∈ Finset.range (N/y), ((k+1 : ℕ) : ℝ)^(-a)) := by
        rw [Finset.mul_sum]
      _ ≤ (B*(N : ℝ)^a) * (((N/y : ℕ) : ℝ)^(1-a)/(1-a)) :=
        mul_le_mul_of_nonneg_left (sum_nat_succ_neg_rpow_le ha ha1 (N/y))
          (by positivity)
      _ ≤ (B*(N : ℝ)^a) * (((N : ℝ)/(y : ℝ))^(1-a)/(1-a)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply div_le_div_of_nonneg_right _ ha1p.le
        apply Real.rpow_le_rpow (by positivity) _ ha1p.le
        apply (le_div_iff₀ hyR).mpr
        exact_mod_cast Nat.div_mul_le_self N y
      _ = _ := by
        calc
          _ = (B/(1-a))*((N : ℝ)^a*((N : ℝ)/(y : ℝ))^(1-a)) := by ring
          _ = _ := by rw [power_cross_identity hNR hyR]; ring
  have hend : |(N/y : ℕ)*positiveArithmeticPrefix w y| ≤
      B*(N : ℝ)*(y : ℝ)^(a-1) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N/y : ℕ))]
    calc
      _ ≤ (N/y : ℕ)*(B*(y : ℝ)^a) :=
        mul_le_mul_of_nonneg_left (hP y le_rfl) (by positivity)
      _ ≤ ((N : ℝ)/(y : ℝ))*(B*(y : ℝ)^a) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply (le_div_iff₀ hyR).mpr
        exact_mod_cast Nat.div_mul_le_self N y
      _ = _ := by rw [Real.rpow_sub_one (ne_of_gt hyR)]; ring
  have htail : |(N : ℝ)*(C - ∑ d ∈ Finset.range (y+1), w d/(d : ℝ))| ≤
      D*(N : ℝ)*(y : ℝ)^(-r) := by
    rw [abs_mul, abs_of_pos hNR]
    calc
      _ ≤ (N : ℝ)*(D*(y : ℝ)^(-r)) := mul_le_mul_of_nonneg_left hD hNR.le
      _ = _ := by ring
  rw [arithmeticFloorPrefix_centered_hyperbola w hw0 C hy hyN]
  have htri := abs_sub_le
    (-(∑ d ∈ Finset.range (y+1), (w d/(d : ℝ))*residue d N) +
      (∑ k ∈ Finset.range (N/y), positiveArithmeticPrefix w (N/(k+1))) -
      (N/y : ℕ)*positiveArithmeticPrefix w y)
    0 ((N : ℝ)*(C - ∑ d ∈ Finset.range (y+1), w d/(d : ℝ)))
  have htri2 := abs_sub_le
    (-(∑ d ∈ Finset.range (y+1), (w d/(d : ℝ))*residue d N) +
      (∑ k ∈ Finset.range (N/y), positiveArithmeticPrefix w (N/(k+1))))
    0 ((N/y : ℕ)*positiveArithmeticPrefix w y)
  simp only [sub_zero, zero_sub, abs_neg] at htri htri2
  have htri3 := abs_add_le
    (-(∑ d ∈ Finset.range (y+1), (w d/(d : ℝ))*residue d N))
    (∑ k ∈ Finset.range (N/y), positiveArithmeticPrefix w (N/(k+1)))
  rw [abs_neg] at htri3
  have hh := power_residue_sum_abs_le w hw0 hW hε hε1 hw N y
  calc
    _ ≤ (W/(1-ε))*(y : ℝ)^(1-ε) +
        (B/(1-a))*(N : ℝ)*(y : ℝ)^(a-1) +
        B*(N : ℝ)*(y : ℝ)^(a-1) +
        D*(N : ℝ)*(y : ℝ)^(-r) := by linarith
    _ = _ := by ring

end
end RiemannResearch.RH.Pareto

open scoped BigOperators
open RiemannResearch.Analysis

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- At the critical power boundary, any common extra factor `Q` in the
signed prefix and density tail survives in the second hyperbola term.
This is the precise input for logarithmic endpoint optimization. -/
theorem arithmeticFloorPrefix_centered_hyperbola_critical_profile_bound
    (w : ℕ → ℝ) (hw0 : w 0 = 0) (C : ℝ)
    {N y : ℕ} (hy : 0 < y) (hyN : y ≤ N)
    {W B D ε Q : ℝ} (hW : 0 ≤ W) (hB : 0 ≤ B) (hQ : 0 < Q)
    (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hw : ∀ d : ℕ, 0 < d → |w d| ≤ W * (d : ℝ)^(-ε))
    (hP : ∀ t : ℕ, y ≤ t →
      |positiveArithmeticPrefix w t| ≤ B*(t : ℝ)^ε/Q)
    (hD : |C - ∑ d ∈ Finset.range (y+1), w d/(d : ℝ)| ≤
      D/((y : ℝ)^(1-ε)*Q)) :
    |arithmeticFloorPrefix w N - (N : ℝ)*C| ≤
      (W/(1-ε))*(y : ℝ)^(1-ε) +
      (B*(1 + 1/(1-ε))+D)*(N : ℝ)/((y : ℝ)^(1-ε)*Q) := by
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hPa : ∀ t : ℕ, y ≤ t →
      |positiveArithmeticPrefix w t| ≤ (B/Q)*(t : ℝ)^ε := by
    intro t ht
    simpa only [div_mul_eq_mul_div] using hP t ht
  have hDa : |C - ∑ d ∈ Finset.range (y+1), w d/(d : ℝ)| ≤
      (D/Q)*(y : ℝ)^(-(1-ε)) := by
    convert hD using 1
    rw [Real.rpow_neg hyR.le]
    ring
  have h := arithmeticFloorPrefix_centered_hyperbola_power_bound
    w hw0 C hy hyN hW (div_nonneg hB hQ.le) hε hε1 hε hε1 hw hPa hDa
  convert h using 1
  rw [show ε-1 = -(1-ε) by ring, Real.rpow_neg hyR.le]
  ring

/-- A monotone profile can be frozen at the hyperbola cutoff without
discarding the signed prefix cancellation. For instance `Q(t)=log(t+2)^b`.
No assertion that the actual arithmetic satisfies these hypotheses is made. -/
theorem arithmeticFloorPrefix_centered_hyperbola_monotone_profile_bound
    (w : ℕ → ℝ) (hw0 : w 0 = 0) (C : ℝ) (Q : ℕ → ℝ)
    {N y : ℕ} (hy : 0 < y) (hyN : y ≤ N)
    {W B D ε : ℝ} (hW : 0 ≤ W) (hB : 0 ≤ B)
    (hQ : 0 < Q y) (hQmono : Monotone Q)
    (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hw : ∀ d : ℕ, 0 < d → |w d| ≤ W * (d : ℝ)^(-ε))
    (hP : ∀ t : ℕ, y ≤ t →
      |positiveArithmeticPrefix w t| ≤ B*(t : ℝ)^ε/Q t)
    (hD : |C - ∑ d ∈ Finset.range (y+1), w d/(d : ℝ)| ≤
      D/((y : ℝ)^(1-ε)*Q y)) :
    |arithmeticFloorPrefix w N - (N : ℝ)*C| ≤
      (W/(1-ε))*(y : ℝ)^(1-ε) +
      (B*(1 + 1/(1-ε))+D)*(N : ℝ)/((y : ℝ)^(1-ε)*Q y) := by
  apply arithmeticFloorPrefix_centered_hyperbola_critical_profile_bound
    w hw0 C hy hyN hW hB hQ hε hε1 hw _ hD
  intro t ht
  exact (hP t ht).trans
    (div_le_div_of_nonneg_left (by positivity) hQ (hQmono ht))

/-- Exact cutoff comparison: balancing the two terms need only be proved
up to constants, and can be separated from the arithmetic theorem. -/
theorem arithmeticFloorPrefix_centered_hyperbola_critical_profile_envelope
    (w : ℕ → ℝ) (hw0 : w 0 = 0) (C : ℝ)
    {N y : ℕ} (hy : 0 < y) (hyN : y ≤ N)
    {W B D ε Q A : ℝ} (hW : 0 ≤ W) (hB : 0 ≤ B) (hD0 : 0 ≤ D)
    (hQ : 0 < Q) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hw : ∀ d : ℕ, 0 < d → |w d| ≤ W*(d : ℝ)^(-ε))
    (hP : ∀ t : ℕ, y ≤ t →
      |positiveArithmeticPrefix w t| ≤ B*(t : ℝ)^ε/Q)
    (hD : |C - ∑ d ∈ Finset.range (y+1), w d/(d : ℝ)| ≤
      D/((y : ℝ)^(1-ε)*Q))
    (hupper : (y : ℝ)^(1-ε) ≤ A)
    (hlower : (N : ℝ) ≤ A*(y : ℝ)^(1-ε)*Q) :
    |arithmeticFloorPrefix w N - (N : ℝ)*C| ≤
      (W/(1-ε)+B*(1+1/(1-ε))+D)*A := by
  have hp : 0 < 1-ε := by linarith
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hden : 0 < (y : ℝ)^(1-ε)*Q :=
    mul_pos (Real.rpow_pos_of_pos hyR _) hQ
  have hquot : (N : ℝ)/((y : ℝ)^(1-ε)*Q) ≤ A := by
    apply (div_le_iff₀ hden).mpr
    simpa only [mul_assoc] using hlower
  have hK : 0 ≤ B*(1+1/(1-ε))+D := by positivity
  calc
    _ ≤ (W/(1-ε))*(y : ℝ)^(1-ε) +
        (B*(1+1/(1-ε))+D)*(N : ℝ)/((y : ℝ)^(1-ε)*Q) :=
      arithmeticFloorPrefix_centered_hyperbola_critical_profile_bound
        w hw0 C hy hyN hW hB hQ hε hε1 hw hP hD
    _ ≤ (W/(1-ε))*A + (B*(1+1/(1-ε))+D)*A := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hupper (div_nonneg hW hp.le)
      · rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left hquot hK
    _ = _ := by ring

end
end RiemannResearch.RH.Pareto
