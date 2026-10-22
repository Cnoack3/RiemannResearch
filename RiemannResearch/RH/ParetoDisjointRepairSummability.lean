import RiemannResearch.RH.ParetoRepairSummability

/-!
# Telescoping control for disjoint small-gap repairs

Source: the adjacent-scale replacement argument in
`ParetoCovarianceRepairReport_Advanced_2026-09-08.md`.

The already proved complete-variance modulus admits a weaker but telescoping
upper bound. As a result, individual variances are summable for every ordered
family of disjoint scale intervals of multiplicative width at most two.
No prime-gap estimate or smooth-number spacing theorem is used.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- An elementary telescoping majorant for the full variance of an actual repair. -/
theorem arithmeticRepair_binary_variance_sqrt_telescope (n h : ℕ)
    (hh0 : 0 < h) (hhn : h ≤ n) :
    paretoVariance (arithmeticRepair 2 n (n + h)) ≤
      64 * (1 / Real.sqrt (n : ℝ) - 1 / Real.sqrt ((n + h : ℕ) : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hh0 hhn)
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh0
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh0
  have hhnR : (h : ℝ) ≤ n := by exact_mod_cast hhn
  have hN : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hQ : 0 < Real.sqrt ((n : ℝ) + h) := Real.sqrt_pos.mpr (by positivity)
  have hNsq := Real.sq_sqrt hnR.le
  have hQsq := Real.sq_sqrt (show 0 ≤ (n : ℝ) + h by positivity)
  have hH : Real.sqrt (h : ℝ) ≤ h := Real.sqrt_le_self_iff.mpr (Or.inr hh1)
  have hNQ : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) + h) :=
    Real.sqrt_le_sqrt (by linarith)
  have hQ2 : Real.sqrt ((n : ℝ) + h) ≤ 2 * Real.sqrt (n : ℝ) := by
    nlinarith
  have hprod : Real.sqrt ((n : ℝ) + h) *
      (Real.sqrt (n : ℝ) + Real.sqrt ((n : ℝ) + h)) ≤ 4 * n := by
    have hm := mul_le_mul_of_nonneg_left hQ2 hN.le
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hprod (sub_nonneg.mpr hNQ)
  have hgap : (h : ℝ) * Real.sqrt ((n : ℝ) + h) ≤
      4 * n * (Real.sqrt ((n : ℝ) + h) - Real.sqrt (n : ℝ)) := by
    have he : Real.sqrt ((n : ℝ) + h) *
        (Real.sqrt (n : ℝ) + Real.sqrt ((n : ℝ) + h)) *
        (Real.sqrt ((n : ℝ) + h) - Real.sqrt (n : ℝ)) =
        (h : ℝ) * Real.sqrt ((n : ℝ) + h) := by
      calc
        _ = Real.sqrt ((n : ℝ) + h) *
            ((Real.sqrt ((n : ℝ) + h))^2 - (Real.sqrt (n : ℝ))^2) := by ring
        _ = _ := by rw [hQsq, hNsq]; ring
    rw [he] at hmul
    exact hmul
  have hfrac : (h : ℝ) / n ≤
      4 * (Real.sqrt ((n : ℝ) + h) - Real.sqrt (n : ℝ)) /
        Real.sqrt ((n : ℝ) + h) := by
    apply (div_le_div_iff₀ hnR hQ).mpr
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hfrac
    (show 0 ≤ 16 / Real.sqrt (n : ℝ) by positivity)
  have hrewrite : (16 / Real.sqrt (n : ℝ)) *
      (4 * (Real.sqrt ((n : ℝ) + h) - Real.sqrt (n : ℝ)) /
        Real.sqrt ((n : ℝ) + h)) =
      64 * (1 / Real.sqrt (n : ℝ) - 1 / Real.sqrt ((n : ℝ) + h)) := by
    field_simp [ne_of_gt hN, ne_of_gt hQ]
    ring
  rw [hrewrite] at hscaled
  calc
    _ ≤ 16 * Real.sqrt ((h : ℝ) / n) / n :=
      arithmeticRepair_binary_variance_sqrt_bound n h hh0 hhn
    _ = 16 * (Real.sqrt (h : ℝ) / Real.sqrt (n : ℝ)) / n := by
      rw [Real.sqrt_div hhR.le]
    _ ≤ 16 * ((h : ℝ) / Real.sqrt (n : ℝ)) / n := by
      gcongr
    _ = (16 / Real.sqrt (n : ℝ)) * ((h : ℝ) / n) := by ring
    _ ≤ 64 * (1 / Real.sqrt (n : ℝ) - 1 / Real.sqrt ((n : ℝ) + h)) := hscaled
    _ = _ := by push_cast; rfl

/-- Each disjoint interval is charged to the decrease of one common potential. -/
theorem ordered_arithmeticRepair_variance_le_potential_drop
    (p q : ℕ → ℕ) (hp : ∀ i, 0 < p i)
    (hpq : ∀ i, p i < q i) (hwidth : ∀ i, q i ≤ 2 * p i)
    (hdisjoint : ∀ i, q i ≤ p (i + 1)) (i : ℕ) :
    paretoVariance (arithmeticRepair 2 (p i) (q i)) ≤
      64 * (1 / Real.sqrt (p i : ℝ) - 1 / Real.sqrt (p (i + 1) : ℝ)) := by
  have hi : p i < q i := hpq i
  have he : p i + (q i - p i) = q i := by omega
  have hb := arithmeticRepair_binary_variance_sqrt_telescope
    (p i) (q i - p i) (by omega) (by have := hwidth i; omega)
  rw [he] at hb
  have hqR : (0 : ℝ) < q i := by exact_mod_cast (lt_trans (hp i) (hpq i))
  have hle : (q i : ℝ) ≤ p (i + 1) := by exact_mod_cast hdisjoint i
  have hs := one_div_le_one_div_of_le (Real.sqrt_pos.mpr hqR)
    (Real.sqrt_le_sqrt hle)
  linarith

/-- The finite accumulated full variance has an explicit telescoping bound. -/
theorem ordered_arithmeticRepair_variance_sum_le
    (p q : ℕ → ℕ) (hp : ∀ i, 0 < p i)
    (hpq : ∀ i, p i < q i) (hwidth : ∀ i, q i ≤ 2 * p i)
    (hdisjoint : ∀ i, q i ≤ p (i + 1)) (N : ℕ) :
    (∑ i ∈ Finset.range N, paretoVariance (arithmeticRepair 2 (p i) (q i))) ≤
      64 * (1 / Real.sqrt (p 0 : ℝ) - 1 / Real.sqrt (p N : ℝ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hb := ordered_arithmeticRepair_variance_le_potential_drop
      p q hp hpq hwidth hdisjoint N
    linarith

/-- Every ordered disjoint small-gap repair family has summable full variances. -/
theorem summable_ordered_disjoint_arithmeticRepair_variance
    (p q : ℕ → ℕ) (hp : ∀ i, 0 < p i)
    (hpq : ∀ i, p i < q i) (hwidth : ∀ i, q i ≤ 2 * p i)
    (hdisjoint : ∀ i, q i ≤ p (i + 1)) :
    Summable (fun i => paretoVariance (arithmeticRepair 2 (p i) (q i))) := by
  apply summable_of_sum_range_le (fun _ => paretoVariance_nonneg _)
    (c := 64 / Real.sqrt (p 0 : ℝ))
  intro N
  have hb := ordered_arithmeticRepair_variance_sum_le p q hp hpq hwidth hdisjoint N
  have hn : 0 ≤ 1 / Real.sqrt (p N : ℝ) := by positivity
  rw [show 64 / Real.sqrt (p 0 : ℝ) =
    64 * (1 / Real.sqrt (p 0 : ℝ)) by ring]
  nlinarith

end
end RiemannResearch.RH.Pareto
