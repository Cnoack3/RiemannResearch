import RiemannResearch.RH.ParetoRepairModulus

/-!
# Exact cancellation of a shared repair anchor

Source: repair of user-provided
RH_Noise_Signal_Arithmetic_Repair_2026-09-07.pdf, §8.

The invalid uniform Bessel bound cannot be recovered by dropping covariances.
Two repairs with the same old scale have an exact change of basis.
The common anchor cancels, leaving a near-neighbor repair and transferring its
second defect to that neighbor. A finite cluster retains one explicit collective
anchor term. No claim of infinite convergence or RH is made here.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Shared-scale cancellation without division by either new scale. -/
theorem arithmeticRepair_common_anchor_weighted (b p q E k : ℕ)
    (hp : 0 < p) (hq : 0 < q) :
    (p : ℝ) * arithmeticRepair b p E k -
      (q : ℝ) * arithmeticRepair b q E k =
      (p : ℝ) * arithmeticRepair b p q k := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hp)
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  simp only [arithmeticRepair_eq_dilation]
  field_simp [hp0, hq0]
  ring

/-- The shared anchor is replaced by the second new scale, exactly. -/
theorem arithmeticRepair_common_anchor_cancel (b p q E k : ℕ)
    (hp : 0 < p) (hq : 0 < q) :
    arithmeticRepair b p E k -
      ((q : ℝ) / (p : ℝ)) * arithmeticRepair b q E k =
      arithmeticRepair b p q k := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hp)
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  simp only [arithmeticRepair_eq_dilation]
  field_simp [hp0, hq0]
  ring

/-- Pointwise triangular change of basis for a finite same-anchor cluster.
The last summand is the exact collective anchor and must be retained. -/
theorem arithmeticRepair_common_anchor_sum (b q E : ℕ) (s : Finset ℕ)
    (a : ℕ → ℝ) (hq : 0 < q) (hp : ∀ p ∈ s, 0 < p) (k : ℕ) :
    (∑ p ∈ s, a p * arithmeticRepair b p E k) =
      (∑ p ∈ s, a p * arithmeticRepair b p q k) +
      (∑ p ∈ s, a p * ((q : ℝ) / (p : ℝ))) *
        arithmeticRepair b q E k := by
  calc
    _ = ∑ p ∈ s, (a p * arithmeticRepair b p q k +
        (a p * ((q : ℝ) / (p : ℝ))) * arithmeticRepair b q E k) := by
      apply Finset.sum_congr rfl
      intro p hps
      have h := arithmeticRepair_common_anchor_cancel b p q E k (hp p hps) hq
      calc
        _ = a p * (arithmeticRepair b p q k +
            ((q : ℝ) / (p : ℝ)) * arithmeticRepair b q E k) := by
          congr 1
          linarith
        _ = _ := by ring
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_mul]

/-- Exactly balanced coefficients remove the collective anchor. -/
theorem arithmeticRepair_common_anchor_sum_of_balance
    (b q E : ℕ) (s : Finset ℕ) (a : ℕ → ℝ)
    (hq : 0 < q) (hp : ∀ p ∈ s, 0 < p)
    (ha : ∑ p ∈ s, a p * ((q : ℝ) / (p : ℝ)) = 0) (k : ℕ) :
    (∑ p ∈ s, a p * arithmeticRepair b p E k) =
      ∑ p ∈ s, a p * arithmeticRepair b p q k := by
  rw [arithmeticRepair_common_anchor_sum b q E s a hq hp k, ha]
  simp

/-- The actual anchor-cancellation condition is reciprocal-weighted balance. -/
theorem arithmeticRepair_common_anchor_sum_of_reciprocal_balance
    (b q E : ℕ) (s : Finset ℕ) (a : ℕ → ℝ)
    (hq : 0 < q) (hp : ∀ p ∈ s, 0 < p)
    (ha : ∑ p ∈ s, a p / (p : ℝ) = 0) (k : ℕ) :
    (∑ p ∈ s, a p * arithmeticRepair b p E k) =
      ∑ p ∈ s, a p * arithmeticRepair b p q k := by
  apply arithmeticRepair_common_anchor_sum_of_balance b q E s a hq hp ?_ k
  calc
    _ = (q : ℝ) * ∑ p ∈ s, a p / (p : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = 0 := by rw [ha, mul_zero]

/-- Cancellation against a later repair preserves every earlier point value. -/
theorem arithmeticRepair_common_anchor_head (b p q E k : ℕ)
    (hb : 1 ≤ b) (hp : 0 < p) (hpq : p ≤ q) (hk : k < p) :
    arithmeticRepair b p E k -
      ((q : ℝ) / (p : ℝ)) * arithmeticRepair b q E k = 0 := by
  rw [arithmeticRepair_common_anchor_cancel b p q E k hp (lt_of_lt_of_le hp hpq)]
  exact arithmeticRepair_head_zero b p q k hb hpq hk

/-- The new prime's defect is unchanged by the common-anchor cancellation. -/
theorem arithmeticRepair_common_anchor_new_defect (b p q E : ℕ)
    (hb : 1 < b) (hp : 1 < p) (hpq : p < q) :
    mobiusDifference p (fun k => arithmeticRepair b p E k -
      ((q : ℝ) / (p : ℝ)) * arithmeticRepair b q E k) = -1 := by
  have heq : (fun k => arithmeticRepair b p E k -
      ((q : ℝ) / (p : ℝ)) * arithmeticRepair b q E k) =
      arithmeticRepair b p q := by
    funext k
    exact arithmeticRepair_common_anchor_cancel b p q E k (by omega) (by omega)
  rw [heq]
  apply arithmeticRepair_new_defect b p q hp
  · have hmul := Nat.mul_le_mul_right p (show 2 ≤ b by omega)
    nlinarith
  · omega
  · have hmul := Nat.mul_le_mul_right q (show 2 ≤ b by omega)
    nlinarith

/-- Cancellation moves the compensating defect to the neighbor `q`.
It does not make that compensating term disappear. -/
theorem arithmeticRepair_binary_neighbor_defect (p q : ℕ)
    (hpq : p < q) (hqp : q < 2 * p) :
    mobiusDifference q (arithmeticRepair 2 p q) = (q : ℝ) / (p : ℝ) := by
  rw [mobiusDifference_arithmeticRepair q 2 p q (by omega)]
  have hqp0 : q ≠ p := by omega
  have hq2p : q ≠ 2 * p := by omega
  have hq2q : q ≠ 2 * q := by omega
  simp only [if_neg hqp0, if_neg hq2p, if_neg hq2q, ite_true]
  ring

/-- The cancellation remains exactly mean zero for the complete Pareto law. -/
theorem arithmeticRepair_common_anchor_mean_zero (b p q E : ℕ)
    (hb : 0 < b) (hp : 0 < p) (hq : 0 < q) :
    paretoMean (fun k => arithmeticRepair b p E k -
      ((q : ℝ) / (p : ℝ)) * arithmeticRepair b q E k) = 0 := by
  have heq : (fun k => arithmeticRepair b p E k -
      ((q : ℝ) / (p : ℝ)) * arithmeticRepair b q E k) =
      arithmeticRepair b p q := by
    funext k
    exact arithmeticRepair_common_anchor_cancel b p q E k hp hq
  rw [heq]
  exact arithmeticRepair_mean_zero b p q hb hp hq

/-- The repaired difference is controlled by the neighbor gap, independently
of the original shared anchor. The bound concerns the full Pareto variance. -/
theorem arithmeticRepair_common_anchor_variance_bound (p h E : ℕ)
    (hh : 0 < h) (hhp : h ≤ p) :
    paretoVariance (fun k => arithmeticRepair 2 p E k -
      (((p + h : ℕ) : ℝ) / (p : ℝ)) * arithmeticRepair 2 (p + h) E k) ≤
      8 * ((h : ℝ) / (p : ℝ)^2) * (1 + Real.log ((p : ℝ) / h)) := by
  have heq : (fun k => arithmeticRepair 2 p E k -
      (((p + h : ℕ) : ℝ) / (p : ℝ)) * arithmeticRepair 2 (p + h) E k) =
      arithmeticRepair 2 p (p + h) := by
    funext k
    exact arithmeticRepair_common_anchor_cancel 2 p (p + h) E k (by omega) (by omega)
  rw [heq]
  exact arithmeticRepair_binary_variance_log_bound p h hh hhp

/-- Reciprocal-weighted cumulative coefficients for an ordered repair family. -/
def repairCumulativeCoefficient (a : ℕ → ℝ) (p : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, a i / (p i : ℝ)

theorem repairCumulativeCoefficient_zero (a : ℕ → ℝ) (p : ℕ → ℕ) :
    repairCumulativeCoefficient a p 0 = 0 := by
  simp [repairCumulativeCoefficient]

theorem repairCumulativeCoefficient_succ (a : ℕ → ℝ) (p : ℕ → ℕ) (n : ℕ) :
    repairCumulativeCoefficient a p (n + 1) =
      repairCumulativeCoefficient a p n + a n / (p n : ℝ) := by
  simp only [repairCumulativeCoefficient, Finset.sum_range_succ]

private theorem scalar_cumulative_transport
    (c A x : ℕ → ℝ) (y : ℝ) (hzero : A 0 = 0)
    (hstep : ∀ i, A (i + 1) = A i + c i) (n : ℕ) :
    (∑ i ∈ Finset.range n, c i * (y - x i)) =
      (∑ i ∈ Finset.range n, A (i + 1) * (x (i + 1) - x i)) +
      A n * (y - x n) := by
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, hstep n]
    ring

/-- Exact adjacent-scale decomposition. The endpoint `p n` is retained, with
its cumulative coefficient. Ordering is needed only for head and gap estimates,
not for this algebraic identity. -/
theorem arithmeticRepair_adjacent_chain (b E n : ℕ) (p : ℕ → ℕ)
    (a : ℕ → ℝ) (hp : ∀ i ≤ n, 0 < p i) (k : ℕ) :
    (∑ i ∈ Finset.range n, a i * arithmeticRepair b (p i) E k) =
      (∑ i ∈ Finset.range n,
        (p i : ℝ) * repairCumulativeCoefficient a p (i + 1) *
          arithmeticRepair b (p i) (p (i + 1)) k) +
      (p n : ℝ) * repairCumulativeCoefficient a p n *
        arithmeticRepair b (p n) E k := by
  calc
    _ = ∑ i ∈ Finset.range n, (a i / (p i : ℝ)) *
        (dilation E (residue b) k - dilation (p i) (residue b) k) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [arithmeticRepair_eq_dilation]
      ring
    _ = (∑ i ∈ Finset.range n, repairCumulativeCoefficient a p (i + 1) *
        (dilation (p (i + 1)) (residue b) k - dilation (p i) (residue b) k)) +
        repairCumulativeCoefficient a p n *
          (dilation E (residue b) k - dilation (p n) (residue b) k) := by
      exact scalar_cumulative_transport (fun i => a i / (p i : ℝ))
        (repairCumulativeCoefficient a p)
        (fun i => dilation (p i) (residue b) k) (dilation E (residue b) k)
        (repairCumulativeCoefficient_zero a p)
        (repairCumulativeCoefficient_succ a p) n
    _ = _ := by
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        have hp0 : (p i : ℝ) ≠ 0 := by
          exact_mod_cast (ne_of_gt (hp i (Nat.le_of_lt (Finset.mem_range.mp hi))))
        rw [arithmeticRepair_eq_dilation]
        field_simp [hp0]
      · have hp0 : (p n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (hp n le_rfl))
        rw [arithmeticRepair_eq_dilation]
        field_simp [hp0]

/-- Only zero terminal reciprocal mass permits removal of the endpoint repair. -/
theorem arithmeticRepair_adjacent_chain_of_balance (b E n : ℕ) (p : ℕ → ℕ)
    (a : ℕ → ℝ) (hp : ∀ i ≤ n, 0 < p i)
    (ha : repairCumulativeCoefficient a p n = 0) (k : ℕ) :
    (∑ i ∈ Finset.range n, a i * arithmeticRepair b (p i) E k) =
      ∑ i ∈ Finset.range n,
        (p i : ℝ) * repairCumulativeCoefficient a p (i + 1) *
          arithmeticRepair b (p i) (p (i + 1)) k := by
  rw [arithmeticRepair_adjacent_chain b E n p a hp k, ha]
  simp

end
end RiemannResearch.RH.Pareto
