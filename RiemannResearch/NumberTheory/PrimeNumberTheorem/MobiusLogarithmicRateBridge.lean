import RiemannResearch.NumberTheory.PrimeNumberTheorem.Consequences

/-!
# Finite logarithmic kernel and quantitative Möbius bridge

This module retains the quantitative input explicitly. A bound on the
absolute dilated Chebyshev remainder implies a logarithmic Mertens bound.
The finite kernel estimate below is designed to discharge that input from
an inverse-square-logarithm error estimate, itself weaker than MediumPNT.
-/

noncomputable section
open Filter Finset Asymptotics Real
open scoped BigOperators ArithmeticFunction.Moebius
namespace RiemannResearch.NumberTheory.PrimeNumberTheorem

theorem reciprocal_square_log_step {x k : ℝ} (hk : 1 ≤ k) (hx : k+1 ≤ x) :
    1 / (k * (1 + Real.log (x/k))^2) ≤
      2 * (1 / (1 + Real.log (x/(k+1))) - 1 / (1 + Real.log (x/k))) := by
  have hkpos : 0 < k := by linarith
  have hxpos : 0 < x := by linarith
  let A := 1 + Real.log (x/k)
  let B := 1 + Real.log (x/(k+1))
  have hB : 1 ≤ B := by
    dsimp [B]
    have hq : 1 ≤ x/(k+1) := (le_div_iff₀ (by positivity)).2 (by linarith)
    linarith [Real.log_nonneg hq]
  have hdelta : 1/(k+1) ≤ A-B := by
    have h := Real.log_le_sub_one_of_pos (div_pos hkpos (by positivity : 0 < k+1))
    rw [Real.log_div hkpos.ne' (by positivity : k+1 ≠ 0)] at h
    have he : k/(k+1)-1 = -(1/(k+1)) := by
      field_simp [show k+1 ≠ 0 by positivity] <;> ring
    rw [he] at h
    dsimp [A, B]
    rw [Real.log_div hxpos.ne' hkpos.ne',
      Real.log_div hxpos.ne' (by positivity : k+1 ≠ 0)]
    linarith
  have hAB : B ≤ A := by linarith [le_of_lt (one_div_pos.mpr (by positivity : 0 < k+1))]
  have hApos : 0 < A := by linarith
  have hBpos : 0 < B := by linarith
  have hmul : 1 ≤ (A-B)*(k+1) :=
    (div_le_iff₀ (by positivity : 0 < k+1)).mp hdelta
  have hbig : 1 ≤ 2*k*(A-B) := by nlinarith
  have hbigA := mul_le_mul_of_nonneg_right hbig hApos.le
  change 1/(k*A^2) ≤ 2*(1/B-1/A)
  have he : 2*(1/B-1/A) = 2*(A-B)/(A*B) := by
    field_simp [hApos.ne', hBpos.ne'] <;> ring
  rw [he, div_le_div_iff₀ (mul_pos hkpos (sq_pos_of_pos hApos))
    (mul_pos hApos hBpos)]
  have hm : B ≤ 2*k*(A-B)*A := by nlinarith
  have hmA := mul_le_mul_of_nonneg_left hm hApos.le
  nlinarith

/-- A finite telescoping estimate; no integration is needed. -/
theorem finite_reciprocal_square_log_sum_le (x : ℝ) (N : ℕ)
    (hN : 0 < N) (hNx : (N : ℝ) ≤ x) :
    (∑ k ∈ Finset.range N,
      1 / (((k : ℝ)+1) * (1 + Real.log (x/((k : ℝ)+1)))^2)) ≤ 3 := by
  have hx : 1 ≤ x := le_trans (by exact_mod_cast hN) hNx
  let A : ℕ → ℝ := fun k => 1 + Real.log (x/((k : ℝ)+1))
  have hA (k : ℕ) (hk : k < N) : 1 ≤ A k := by
    have hkn : (k : ℝ)+1 ≤ x := by
      have : k+1 ≤ N := by omega
      exact le_trans (by exact_mod_cast this) hNx
    have hq : 1 ≤ x/((k : ℝ)+1) :=
      (le_div_iff₀ (by positivity)).2 (by linarith)
    dsimp [A]
    linarith [Real.log_nonneg hq]
  have htel : ∀ n : ℕ, n < N →
      (∑ k ∈ Finset.range n, 1/(((k : ℝ)+1) * (A k)^2)) ≤
        2*(1/(A n)-1/(A 0)) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hi := ih (by omega)
      have hstep := reciprocal_square_log_step (x := x) (k := (n : ℝ)+1)
        (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (by
          have hle : n+2 ≤ N := by omega
          have hr : (n : ℝ)+1+1 ≤ (N : ℝ) := by exact_mod_cast hle
          linarith)
      have hstep' : 1/(((n : ℝ)+1) * (A n)^2) ≤
          2*(1/(A (n+1))-1/(A n)) := by
        simpa only [A, Nat.cast_add, Nat.cast_one] using hstep
      rw [Finset.sum_range_succ]
      linarith
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  have ht := htel n (by omega)
  have ha := hA n (by omega)
  have ha0 := hA 0 (by omega)
  have hapos : 0 < A n := by linarith
  have hlast : 1/(((n : ℝ)+1) * (A n)^2) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [sq_nonneg (A n-1),
      mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sq_nonneg (A n))]
  have hinv : 1/(A n) ≤ 1 := (div_le_iff₀ (by linarith)).2 (by linarith)
  have hnonneg : 0 ≤ 1/(A 0) := one_div_nonneg.mpr (by linarith)
  change (∑ k ∈ Finset.range (n+1), 1/(((k : ℝ)+1) * (A k)^2)) ≤ 3
  rw [Finset.sum_range_succ]
  linarith

/-- Exact arithmetic consequence of a globally controlled Chebyshev remainder. -/
theorem sum_abs_R_le_of_log_square_bound {C : ℝ} (hC : 0 ≤ C)
    (hR : ∀ y : ℝ, 1 ≤ y → |R y| ≤ C*y/(1+Real.log y)^2)
    (x : ℝ) (hx : 1 ≤ x) :
    (∑ k ∈ Finset.Iic ⌊x⌋₊, |R (x/k)|) ≤ 3*C*x := by
  have hN : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr hx
  have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hkbound (k : ℕ) (hk : k < ⌊x⌋₊) :
      |R (x/((k : ℝ)+1))| ≤
        C*x * (1/(((k : ℝ)+1)*(1+Real.log (x/((k : ℝ)+1)))^2)) := by
    have hkn : (k : ℝ)+1 ≤ x := by
      have : k+1 ≤ ⌊x⌋₊ := by omega
      exact le_trans (by exact_mod_cast this) hNx
    have hq : 1 ≤ x/((k : ℝ)+1) :=
      (le_div_iff₀ (by positivity)).2 (by linarith)
    convert hR _ hq using 1
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hs := Finset.sum_le_sum (fun k hk => hkbound k (Finset.mem_range.mp hk))
  rw [← Finset.mul_sum] at hs
  have hs' := mul_le_mul_of_nonneg_left (finite_reciprocal_square_log_sum_le x ⌊x⌋₊ hN hNx)
    (mul_nonneg hC (by linarith : 0 ≤ x))
  have hsum : (∑ k ∈ Finset.Iic ⌊x⌋₊, |R (x/k)|) =
      ∑ k ∈ Finset.range ⌊x⌋₊, |R (x/((k : ℝ)+1))| := by
    rw [show Finset.Iic ⌊x⌋₊ = Finset.range (⌊x⌋₊+1) by ext; simp <;> omega,
      Finset.sum_range_succ']
    simp [R, Psi, Chebyshev.psi_eq_sum_Icc]
  rw [hsum]
  nlinarith

/-- The only quantitative premise is the stated absolute dilated remainder
bound. Existing Möbius identities then gain a full logarithm for M(x). -/
theorem M_mul_log_isBigO_of_sum_abs_R_isBigO
    (hRsum : (fun x : ℝ => ∑ k ∈ Finset.Iic ⌊x⌋₊, |R (x/k)|) =O[atTop] id) :
    (fun x : ℝ => M x * Real.log x) =O[atTop] id := by
  have hterm1 : (fun x : ℝ => ∑ k ∈ Finset.Iic ⌊x⌋₊,
      (ArithmeticFunction.moebius k : ℝ) * Real.log (x/k)) =O[atTop] id := by
    refine (Asymptotics.IsBigO.of_bound 1 ?_).trans sum_log_div_isBigO
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    simp only [Real.norm_eq_abs, one_mul]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply le_trans (Finset.sum_le_sum ?_) (le_abs_self _)
    intro k hk
    have hmu : |(ArithmeticFunction.moebius k : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k)
    have hlog : 0 ≤ Real.log (x/k) := by
      by_cases hk0 : k = 0
      · simp [hk0]
      · apply Real.log_nonneg
        apply (le_div_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0))).2
        simp only [one_mul]
        exact (Nat.cast_le.mpr (Finset.mem_Iic.mp hk)).trans (Nat.floor_le (by linarith))
    rw [abs_mul, abs_of_nonneg hlog]
    exact mul_le_of_le_one_left hlog hmu
  have hterm3 : (fun x : ℝ => ∑ k ∈ Finset.Iic ⌊x⌋₊,
      (ArithmeticFunction.moebius k : ℝ) * R (x/k)) =O[atTop] id := by
    refine (Asymptotics.IsBigO.of_bound 1 ?_).trans hRsum
    filter_upwards [] with x
    simp only [Real.norm_eq_abs, one_mul]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply le_trans (Finset.sum_le_sum ?_) (le_abs_self _)
    intro k hk
    rw [abs_mul]
    apply mul_le_of_le_one_left (abs_nonneg _)
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k)
  have hc := (hterm1.sub sum_mobius_div_isBigO).sub hterm3
  rcases Asymptotics.isBigO_iff.mp hc with ⟨c, hc⟩
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨c, ?_⟩
  filter_upwards [hc, eventually_ge_atTop (1 : ℝ)] with x hcx hx
  have he :
      (∑ k ∈ Finset.Iic ⌊x⌋₊, (ArithmeticFunction.moebius k : ℝ) * Real.log (x/k)) -
      (∑ k ∈ Finset.Iic ⌊x⌋₊, (ArithmeticFunction.moebius k : ℝ) * (x/k)) -
      (∑ k ∈ Finset.Iic ⌊x⌋₊, (ArithmeticFunction.moebius k : ℝ) * R (x/k)) =
        M x * Real.log x := by
    rw [M_log_identity x hx]
    simp only [R, Finset.sum_sub_distrib, mul_sub]
    ring
  simpa only [Pi.sub_apply, he] using hcx

end RiemannResearch.NumberTheory.PrimeNumberTheorem
