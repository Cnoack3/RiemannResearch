/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.DirichletCoefficientTailAbel
import RiemannResearch.NumberTheory.PrimeNumberTheorem.CoprimeMobiusLogDecay
import RiemannResearch.NumberTheory.PrimeNumberTheorem.CoprimeMobiusWeightMean
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Uniform logarithmic summation for coprime Möbius deletions

The decreasing kernel 1/(t (2 + log X - log t)²) has the explicit
primitive 1/(2 + log X - log t). Finite Abel summation therefore transfers a
linear prefix bound for the squared prime-deletion factors to a uniform
harmonic bound for the actual coprime reciprocal Möbius sums.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace RiemannResearch.NumberTheory.PrimeNumberTheorem.FixedPrimeCylinder
open RiemannResearch.Analysis.DirichletMeanSquare

private def relLog (X t : ℝ) : ℝ := 2 + Real.log X - Real.log t
private def logKernel (X t : ℝ) : ℝ := (t * relLog X t ^ 2)⁻¹

private theorem relLog_two_le {X t : ℝ} (ht : 0 < t) (htX : t ≤ X) :
    2 ≤ relLog X t := by
  unfold relLog
  linarith [Real.log_le_log ht htX]

private theorem relLog_deriv (X : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (relLog X) (-t⁻¹) t := by
  change HasDerivAt (fun y : ℝ => (2+Real.log X) - Real.log y) (-t⁻¹) t
  simpa only [Pi.sub_def, zero_sub] using
    (hasDerivAt_const t (2+Real.log X)).sub (Real.hasDerivAt_log ht.ne')

private theorem denom_deriv (X : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun y => y * relLog X y ^ 2) (relLog X t * (relLog X t-2)) t := by
  rw [show relLog X t * (relLog X t-2) =
      1 * relLog X t ^ 2 + t * ((2:ℝ) * relLog X t ^ (1:ℕ) * (-t⁻¹)) by
    field_simp [ht.ne']
    <;> ring]
  exact (hasDerivAt_id t).mul ((relLog_deriv X ht).pow 2)

private theorem logKernel_antitone {X : ℝ} :
    AntitoneOn (logKernel X) (Icc 1 X) := by
  have hx {x : ℝ} (h : x ∈ Icc 1 X) : 0 < x := lt_of_lt_of_le zero_lt_one h.1
  have hm : MonotoneOn (fun y => y * relLog X y ^ 2) (Icc 1 X) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun x h => (denom_deriv X (hx h)).continuousAt.continuousWithinAt
    · intro x h
      exact (denom_deriv X (hx (interior_subset h))).differentiableAt.differentiableWithinAt
    · intro x h
      have hh := interior_subset h
      rw [(denom_deriv X (hx hh)).deriv]
      have hl := relLog_two_le (hx hh) hh.2
      exact mul_nonneg (by linarith) (by linarith)
  intro x h y hy hxy
  exact (inv_le_inv₀ (mul_pos (hx hy) (sq_pos_of_pos (by linarith [relLog_two_le (hx hy) hy.2])))
    (mul_pos (hx h) (sq_pos_of_pos (by linarith [relLog_two_le (hx h) h.2])))).mpr (hm h hy hxy)

private theorem logKernel_integral {X : ℝ} (hX : 1 ≤ X) :
    ∫ t in (1:ℝ)..X, logKernel X t = (relLog X X)⁻¹ - (relLog X 1)⁻¹ := by
  have hprim (t : ℝ) (h : t ∈ uIcc 1 X) :
      HasDerivAt (fun y => (relLog X y)⁻¹) (logKernel X t) t := by
    rw [uIcc_of_le hX] at h
    have ht := lt_of_lt_of_le zero_lt_one h.1
    have hl : 0 < relLog X t := by linarith [relLog_two_le ht h.2]
    convert (relLog_deriv X ht).inv hl.ne' using 1 <;>
      first | rfl | (dsimp only [logKernel]; field_simp [ht.ne',hl.ne'])
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt hprim
  apply ContinuousOn.intervalIntegrable
  intro t h
  rw [uIcc_of_le hX] at h
  have ht := lt_of_lt_of_le zero_lt_one h.1
  have hl : 0 < relLog X t := by linarith [relLog_two_le ht h.2]
  have hn := mul_ne_zero ht.ne' (pow_ne_zero 2 hl.ne')
  exact ((denom_deriv X ht).continuousAt.inv₀ hn).continuousWithinAt

private theorem sum_succ_eq_Icc (f : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, f (i+1)) = ∑ k ∈ Finset.Icc 1 N, f k := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ih]

private theorem logKernel_sum (X : ℕ) :
    (∑ k ∈ Finset.Icc 1 X, logKernel X k) ≤ 2 := by
  cases X with
  | zero => simp
  | succ N =>
    let X : ℝ := (N:ℝ)+1
    have hX : 1 ≤ X := by dsimp [X]; linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]
    have hanti : AntitoneOn (logKernel X) (Icc (1:ℝ) (1+(N:ℝ))) := by
      simpa only [X,add_comm] using (logKernel_antitone (X:=X))
    have hsum := hanti.sum_le_integral
    have hin : (∫ t in (1:ℝ)..1+(N:ℝ), logKernel X t) =
        (relLog X X)⁻¹-(relLog X 1)⁻¹ := by
      simpa only [X,add_comm] using logKernel_integral hX
    rw [hin] at hsum
    have h1 : (logKernel X 1) ≤ 1 := by
      have hl := relLog_two_le (by norm_num : (0:ℝ)<1) hX
      unfold logKernel
      rw [one_mul]
      exact (inv_le_one_of_one_le₀ (by nlinarith : 1 ≤ relLog X 1 ^ 2))
    have hprimitive : (relLog X X)⁻¹ = 1/2 := by simp [relLog]
    have hpos : 0 ≤ (relLog X 1)⁻¹ :=
      inv_nonneg.mpr (by linarith [relLog_two_le (by norm_num : (0:ℝ)<1) hX])
    rw [hprimitive] at hsum
    rw [← sum_succ_eq_Icc, Finset.sum_range_succ']
    have hconv : (∑ i ∈ Finset.range N, logKernel X ((i+1+1:ℕ):ℝ)) =
        ∑ i ∈ Finset.range N, logKernel X (1+((i+1:ℕ):ℝ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      norm_cast
      omega
    simp only [Nat.zero_add, Nat.cast_one] at *
    rw [show ((N+1 : ℕ):ℝ) = X by exact Nat.cast_add_one N]
    change (∑ i ∈ Finset.range N, logKernel X ((i+1+1:ℕ):ℝ)) + logKernel X 1 ≤ 2
    rw [hconv]
    linarith

private theorem logKernel_weighted_sum {a : ℕ → ℝ} {D : ℝ}
    (hD : 0 ≤ D) (hp : ∀ n : ℕ, (∑ k ∈ Finset.Icc 1 n, a k) ≤ D*n) (X : ℕ) :
    (∑ k ∈ Finset.Icc 1 X, a k * logKernel X k) ≤ 2*D := by
  rcases Nat.eq_zero_or_pos X with rfl | hX
  · simpa using mul_nonneg (by norm_num : (0:ℝ)≤2) hD
  let w (n : ℕ) := logKernel X ((min (n+1) X : ℕ) : ℝ)
  have hp' (n : ℕ) : (∑ k ∈ Finset.range n, a (k+1)) ≤ D*(0+(n:ℝ)) := by
    simpa only [sum_succ_eq_Icc,zero_add] using hp n
  have hpos (n : ℕ) : 0 < min (n+1) X := lt_min (by omega) hX
  have hw (n : ℕ) : 0 ≤ w n := by
    unfold w logKernel
    exact inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  have hmem (n : ℕ) : (↑(min (n+1) X):ℝ) ∈ Icc (1:ℝ) X := by
    constructor
    · exact_mod_cast hpos n
    · exact_mod_cast min_le_right (n+1) X
  have hd : Antitone w := fun i j hij =>
    logKernel_antitone (hmem i) (hmem j)
      (by exact_mod_cast min_le_min_right X (Nat.succ_le_succ hij))
  have hraw := coefficient_prefix_weighted_le (fun n => a (n+1)) w D 0 hp' hw hd X
  have he (n : ℕ) (hn : n ∈ Finset.range X) : w n = logKernel X (n+1 : ℕ) := by
    change logKernel X ((min (n+1) X : ℕ) : ℝ) = _
    rw [min_eq_left (Nat.succ_le_of_lt (Finset.mem_range.mp hn))]
  simp only [mul_zero, zero_mul, zero_add] at hraw
  rw [← sum_succ_eq_Icc (fun k => a k * logKernel X k) X]
  calc
    _ = ∑ n ∈ Finset.range X, a (n+1)*w n :=
      Finset.sum_congr rfl (fun n hn => by rw [he n hn])
    _ ≤ D*∑ n ∈ Finset.range X, w n := hraw
    _ = D*∑ k ∈ Finset.Icc 1 X, logKernel X k := by
      rw [← sum_succ_eq_Icc (fun k => logKernel X k) X]
      congr 1
      exact Finset.sum_congr rfl he
    _ ≤ 2*D := by simpa only [mul_comm] using mul_le_mul_of_nonneg_left (logKernel_sum X) hD

/-- A linear prefix estimate for the squared deletion factors controls the
full harmonic sum of the actual Möbius sums, uniformly in the cutoff. -/
theorem roughReciprocal_harmonic_prefix_of_product_mean {D : ℝ} (hD : 0 ≤ D)
    (hmean : ∀ n : ℕ, (∑ k ∈ Finset.Icc 1 n,
      (∏ p ∈ k.primeFactors, (1-(Real.sqrt (p:ℝ))⁻¹)⁻¹)^2) ≤ D*n) :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℕ,
      (∑ k ∈ Finset.Icc 1 X, (roughReciprocal k.primeFactors (X/k))^2 / (k:ℝ)) ≤ K := by
  obtain ⟨C,hC,hrough⟩ := roughReciprocal_log_product_bound
  let b (k : ℕ) := ∏ p ∈ k.primeFactors, (1-(Real.sqrt (p:ℝ))⁻¹)⁻¹
  refine ⟨2*D*C^2+1,by positivity,?_⟩
  intro X
  have hpoint (k : ℕ) (hk : k ∈ Finset.Icc 1 X) :
      (roughReciprocal k.primeFactors (X/k))^2 / (k:ℝ) ≤ C^2 * (b k ^ 2 * logKernel X k) := by
    obtain ⟨hk1,hkX⟩ := Finset.mem_Icc.mp hk
    have hkR : 0 < (k:ℝ) := by exact_mod_cast hk1
    have hkXR : (k:ℝ) ≤ X := by exact_mod_cast hkX
    have hN : X < k*(X/k+1) := by
      rw [Nat.mul_add,Nat.mul_one]
      have := Nat.mod_add_div X k
      have := Nat.mod_lt X (by omega : 0 < k)
      omega
    have hNR : (X:ℝ) ≤ (k:ℝ)*(((X/k:ℕ):ℝ)+1) := by exact_mod_cast hN.le
    have hlog := Real.log_le_log (hkR.trans_le hkXR) hNR
    rw [Real.log_mul hkR.ne' (by positivity : (((X/k:ℕ):ℝ)+1) ≠ 0)] at hlog
    have hlrel : relLog X k ≤ roughLogWeight (X/k) := by
      unfold relLog roughLogWeight
      linarith
    have hl : 0 < relLog X k := by linarith [relLog_two_le hkR hkXR]
    let r := roughReciprocal k.primeFactors (X/k)
    have habs : |r| * relLog X k ≤ C*b k :=
      (mul_le_mul_of_nonneg_left hlrel (abs_nonneg r)).trans
        (hrough k.primeFactors (fun p h => Nat.prime_of_mem_primeFactors h) (X/k))
    have hs := pow_le_pow_left₀ (mul_nonneg (abs_nonneg r) hl.le) habs 2
    simp only [mul_pow,sq_abs] at hs
    calc
      _ = (r^2 * relLog X k ^ 2) * logKernel X k := by
        unfold logKernel
        change r^2/(k:ℝ) = _
        field_simp [hkR.ne',hl.ne']
      _ ≤ (C^2 * b k ^ 2) * logKernel X k :=
        mul_le_mul_of_nonneg_right hs (inv_nonneg.mpr (mul_nonneg hkR.le (sq_nonneg _)))
      _ = _ := by ring
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 X, C^2 * (b k ^ 2 * logKernel X k) := Finset.sum_le_sum hpoint
    _ = C^2 * ∑ k ∈ Finset.Icc 1 X, b k ^ 2 * logKernel X k := (Finset.mul_sum ..).symm
    _ ≤ C^2 * (2*D) := mul_le_mul_of_nonneg_left (logKernel_weighted_sum hD hmean X) (sq_nonneg _)
    _ ≤ _ := by nlinarith

/-- Uniform complete harmonic bound for all truncated coprime Möbius sums. -/
theorem exists_roughReciprocal_harmonic_prefix_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℕ,
      (∑ k ∈ Finset.Icc 1 X, (roughReciprocal k.primeFactors (X/k))^2 / (k:ℝ)) ≤ K := by
  obtain ⟨D,hD,hm⟩ := exists_coprimeMobiusWeight_sq_prefix_bound
  exact roughReciprocal_harmonic_prefix_of_product_mean hD.le
    (by simpa only [coprimeMobiusWeight] using hm)

end RiemannResearch.NumberTheory.PrimeNumberTheorem.FixedPrimeCylinder
