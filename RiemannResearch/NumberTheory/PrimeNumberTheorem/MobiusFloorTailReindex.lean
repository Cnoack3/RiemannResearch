import RiemannResearch.NumberTheory.PrimeNumberTheorem.Consequences

/-!
# Exact quotient-level reindexing of Möbius floor tails

Source: the finite missing-divisor identity in HardyEndpointCompactness20260924.md.
The proof retains the full interval before estimating its summatory increments.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset

namespace RiemannResearch.NumberTheory.PrimeNumberTheorem

/-- Count the full floor tail by its positive quotient levels. -/
theorem floor_tail_reindex (f : ℕ → ℝ) (N K : ℕ) (hN : 0 < N) (hK : 0 < K) :
    (∑ n ∈ Finset.Ioc N (N*K), f n * (((N*K)/n : ℕ) : ℝ)) =
      ∑ j ∈ Finset.Ico 1 K, ∑ n ∈ Finset.Ioc N ((N*K)/j), f n := by
  classical
  have hrow (n : ℕ) (hn : n ∈ Finset.Ioc N (N*K)) :
      f n * (((N*K)/n : ℕ) : ℝ) =
        ∑ j ∈ Finset.Ico 1 K, if j ≤ (N*K)/n then f n else 0 := by
    have hnn : N < n := (Finset.mem_Ioc.mp hn).1
    have hn0 : 0 < n := by omega
    have hq : (N*K)/n < K := by
      apply (Nat.div_lt_iff_lt_mul hn0).mpr
      nlinarith
    have hf : (Finset.Ico 1 K).filter (fun j => j ≤ (N*K)/n) =
        Finset.Icc 1 ((N*K)/n) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [← Finset.sum_filter, hf]
    simp [mul_comm]
  have hcolumn (j : ℕ) (hj : j ∈ Finset.Ico 1 K) :
      (Finset.Ioc N (N*K)).filter (fun n => j ≤ (N*K)/n) =
        Finset.Ioc N ((N*K)/j) := by
    have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have hj0 : 0 < j := by omega
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hNn, hnX⟩, hjq⟩
      have hn0 : 0 < n := by omega
      refine ⟨hNn, (Nat.le_div_iff_mul_le hj0).mpr ?_⟩
      simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hn0).mp hjq
    · rintro ⟨hNn, hnq⟩
      have hn0 : 0 < n := by omega
      have hp : n*j ≤ N*K := (Nat.le_div_iff_mul_le hj0).mp hnq
      have hnj : n ≤ n*j := by nlinarith
      refine ⟨⟨hNn, hnj.trans hp⟩, (Nat.le_div_iff_mul_le hn0).mpr ?_⟩
      simpa only [Nat.mul_comm] using hp
  calc
    (∑ n ∈ Finset.Ioc N (N*K), f n * (((N*K)/n : ℕ) : ℝ)) =
        ∑ n ∈ Finset.Ioc N (N*K), ∑ j ∈ Finset.Ico 1 K,
          if j ≤ (N*K)/n then f n else 0 := Finset.sum_congr rfl hrow
    _ = ∑ j ∈ Finset.Ico 1 K, ∑ n ∈ Finset.Ioc N (N*K),
          if j ≤ (N*K)/n then f n else 0 := Finset.sum_comm
    _ = ∑ j ∈ Finset.Ico 1 K, ∑ n ∈ Finset.Ioc N ((N*K)/j), f n := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_filter, hcolumn j hj]

/-- An exact inclusive-summatory-function difference over a finite interval. -/
theorem M_nat_difference (N A : ℕ) (hNA : N ≤ A) :
    M (A : ℝ) - M (N : ℝ) =
      ∑ n ∈ Finset.Ioc N A, (ArithmeticFunction.moebius n : ℝ) := by
  classical
  have hd : Disjoint (Finset.Iic N) (Finset.Ioc N A) := by
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    simp only [Finset.mem_Iic, Finset.mem_Ioc] at hn hn'
    omega
  have hu : Finset.Iic N ∪ Finset.Ioc N A = Finset.Iic A := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Iic, Finset.mem_Ioc]
    omega
  have hs : (∑ n ∈ Finset.Iic A, (ArithmeticFunction.moebius n : ℝ)) =
      (∑ n ∈ Finset.Iic N, (ArithmeticFunction.moebius n : ℝ)) +
      ∑ n ∈ Finset.Ioc N A, (ArithmeticFunction.moebius n : ℝ) := by
    rw [← hu, Finset.sum_union hd]
  unfold M
  simp only [Nat.floor_natCast]
  linarith

/-- Exact floor-tail formula in terms of the genuine summatory Möbius function. -/
theorem mobius_floor_tail_eq_M_sum (N K : ℕ) (hN : 0 < N) (hK : 0 < K) :
    (∑ n ∈ Finset.Ioc N (N*K), (ArithmeticFunction.moebius n : ℝ) *
      (((N*K)/n : ℕ) : ℝ)) =
      ∑ j ∈ Finset.Ico 1 K, (M (((N*K : ℕ) : ℝ)/(j : ℝ)) - M (N : ℝ)) := by
  rw [floor_tail_reindex _ N K hN hK]
  apply Finset.sum_congr rfl
  intro j hj
  have hj0 : 0 < j := (Finset.mem_Ico.mp hj).1
  have hjK : j ≤ K := le_of_lt (Finset.mem_Ico.mp hj).2
  have hNj : N ≤ (N*K)/j := (Nat.le_div_iff_mul_le hj0).mpr
    (Nat.mul_le_mul_left N hjK)
  have hf : M (((N*K : ℕ) : ℝ)/(j : ℝ)) = M (((N*K)/j : ℕ) : ℝ) := by
    unfold M
    rw [Nat.floor_div_natCast]
    simp only [Nat.floor_natCast]
  rw [hf, M_nat_difference N ((N*K)/j) hNj]

/-- Triangle bound retaining all signed summatory increments before estimation. -/
theorem mobius_floor_tail_abs_le_M_sum (N K : ℕ) (hN : 0 < N) (hK : 0 < K) :
    |∑ n ∈ Finset.Ioc N (N*K), (ArithmeticFunction.moebius n : ℝ) *
      (((N*K)/n : ℕ) : ℝ)| ≤
      ∑ j ∈ Finset.Ico 1 K,
        (|M (((N*K : ℕ) : ℝ)/(j : ℝ))| + |M (N : ℝ)|) := by
  rw [mobius_floor_tail_eq_M_sum N K hN hK]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  apply Finset.sum_le_sum
  intro j hj
  simpa only [sub_zero, zero_sub, abs_neg] using
    abs_sub_le (M (((N*K : ℕ) : ℝ)/(j : ℝ))) 0 (M (N : ℝ))


/-- A uniform linear bound on M above N controls the complete floor tail
by its finite harmonic quotient sum. -/
theorem mobius_floor_tail_abs_le_of_M_bound (N K : ℕ)
    (hN : 0 < N) (hK : 0 < K) (A : ℝ) (hA : 0 ≤ A)
    (hM : ∀ y : ℝ, (N : ℝ) ≤ y → |M y| ≤ A*y) :
    |∑ n ∈ Finset.Ioc N (N*K), (ArithmeticFunction.moebius n : ℝ) *
      (((N*K)/n : ℕ) : ℝ)| ≤
      A * ((N*K : ℕ) : ℝ) * ((∑ j ∈ Finset.Ico 1 K, 1/(j : ℝ)) + 1) := by
  have hcard : ((Finset.Ico 1 K).card : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast (show (Finset.Ico 1 K).card ≤ K by simp)
  calc
    |∑ n ∈ Finset.Ioc N (N*K), (ArithmeticFunction.moebius n : ℝ) *
        (((N*K)/n : ℕ) : ℝ)| ≤
        ∑ j ∈ Finset.Ico 1 K,
          (|M (((N*K : ℕ) : ℝ)/(j : ℝ))| + |M (N : ℝ)|) :=
      mobius_floor_tail_abs_le_M_sum N K hN hK
    _ ≤ ∑ j ∈ Finset.Ico 1 K,
          (A * (((N*K : ℕ) : ℝ)/(j : ℝ)) + A*(N : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj0 : (0 : ℝ) < j := by
        exact_mod_cast (show 0 < j from (Finset.mem_Ico.mp hj).1)
      have hjK : j ≤ K := le_of_lt (Finset.mem_Ico.mp hj).2
      have hy : (N : ℝ) ≤ ((N*K : ℕ) : ℝ)/(j : ℝ) := by
        apply (le_div_iff₀ hj0).mpr
        exact_mod_cast Nat.mul_le_mul_left N hjK
      exact add_le_add (hM _ hy) (hM _ le_rfl)
    _ = A * ((N*K : ℕ) : ℝ) * (∑ j ∈ Finset.Ico 1 K, 1/(j : ℝ)) +
        ((Finset.Ico 1 K).card : ℝ) * (A*(N : ℝ)) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ A * ((N*K : ℕ) : ℝ) * (∑ j ∈ Finset.Ico 1 K, 1/(j : ℝ)) +
        (K : ℝ) * (A*(N : ℝ)) := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_right hcard (mul_nonneg hA (Nat.cast_nonneg N))) _
    _ = A * ((N*K : ℕ) : ℝ) * ((∑ j ∈ Finset.Ico 1 K, 1/(j : ℝ)) + 1) := by
      push_cast
      ring

end RiemannResearch.NumberTheory.PrimeNumberTheorem
