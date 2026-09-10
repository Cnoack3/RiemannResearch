import RiemannResearch.RH.DyadicBoundaryAnnulusMass
import RiemannResearch.RH.DyadicBoundaryLocality

/-!
# A finite logarithmic-count cutoff for the actual dyadic Gram kernel

Source: user-provided `DyadicRegularizedVerificationContinuation20260910 (2).md`,
Appendix §2, September 10, 2026. Physical coefficient mass and exact geometric
locality give the Gram bound with no assumed tent formula or Gram provider.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

private theorem two_pow_mono {a b : ℕ} (h : a ≤ b) : (2 : ℕ)^a ≤ 2^b := by
  have he : b = a+(b-a) := by omega
  rw [he, pow_add]
  have hp : 0 < (2 : ℕ)^(b-a) := by positivity
  have hh : 1 ≤ (2 : ℕ)^(b-a) := hp
  simpa only [mul_one] using Nat.mul_le_mul_left (2^a) hh

/-- A separated pair of normalized steps has zero mixed boundary contribution
at every dyadic level at or above the separation cutoff. -/
theorem dyadicBoundaryCoordinate_step_product_zero_above_cutoff
    (M N m n R : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmlo : 2^M ≤ m) (hmhi : m ≤ 2^(M+1))
    (hnlo : 2^N ≤ n) (hnhi : n ≤ 2^(N+1))
    (hsep : 1/(2 : ℝ)^R ≤ |(m : ℝ)/(2 : ℝ)^M - (n : ℝ)/(2 : ℝ)^N|)
    (r i : ℕ) (hR : R ≤ r)
    (hi : i ∈ Finset.Ico (2^r-1) (2^(r+1)-1)) :
    dyadicBoundaryCoordinate (dyadicProjectedStep m hm) i *
      dyadicBoundaryCoordinate (dyadicProjectedStep n hn) i = 0 := by
  have hp : 0 < (2 : ℕ)^r := by positivity
  have hL : 2^r ≤ i+1 := by
    have h := (Finset.mem_Ico.mp hi).1
    omega
  have hL2 : i+1 < 2*(2^r) := by
    have h := (Finset.mem_Ico.mp hi).2
    rw [pow_succ'] at h
    omega
  by_cases hM : M ≤ r
  · have hpow : (2 : ℕ)^(M+1) ≤ 2*2^r := by
      simpa only [pow_succ'] using two_pow_mono (show M+1 ≤ r+1 by omega)
    have hmz : m ≤ 2*(i+1) := by
      omega
    rw [dyadicBoundaryCoordinate_step_zero m hm i hmz, zero_mul]
  by_cases hN : N ≤ r
  · have hpow : (2 : ℕ)^(N+1) ≤ 2*2^r := by
      simpa only [pow_succ'] using two_pow_mono (show N+1 ≤ r+1 by omega)
    have hnz : n ≤ 2*(i+1) := by
      omega
    rw [dyadicBoundaryCoordinate_step_zero n hn i hnz, mul_zero]
  have hrM : r ≤ M := by omega
  have hrN : r ≤ N := by omega
  have hdM : (2 : ℕ)^(M-r)*2^r = 2^M := by
    rw [← pow_add, Nat.sub_add_cancel hrM]
  have hdN : (2 : ℕ)^(N-r)*2^r = 2^N := by
    rw [← pow_add, Nat.sub_add_cancel hrN]
  have huM : (2 : ℕ)^(M-r)*(2*2^r) = 2^(M+1) := by
    rw [pow_succ']
    nlinarith [hdM]
  have huN : (2 : ℕ)^(N-r)*(2*2^r) = 2^(N+1) := by
    rw [pow_succ']
    nlinarith [hdN]
  by_contra hprod
  have hmn := mul_ne_zero_iff.mp hprod
  have hlocal := dyadicBoundaryCoordinate_common_support_normalized_separation
    (2^r) (i+1) hp hL hL2 (M-r) (N-r) m n hm hn
    (by simpa only [hdM] using hmlo) (by simpa only [huM] using hmhi)
    (by simpa only [hdN] using hnlo) (by simpa only [huN] using hnhi)
    (by simpa only [Nat.add_sub_cancel] using hmn.1)
    (by simpa only [Nat.add_sub_cancel] using hmn.2)
  have hdMR : (2 : ℝ)^(M-r)*((2 : ℕ)^r : ℝ) = (2 : ℝ)^M := by
    exact_mod_cast hdM
  have hdNR : (2 : ℝ)^(N-r)*((2 : ℕ)^r : ℝ) = (2 : ℝ)^N := by
    exact_mod_cast hdN
  push_cast at hlocal hdMR hdNR
  rw [hdMR, hdNR] at hlocal
  have hrecip : 1/(2 : ℝ)^r ≤ 1/(2 : ℝ)^R := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast two_pow_mono hR
  linarith

/-- The complete actual Gram kernel is bounded by the number of dyadic
levels allowed by the normalized separation. -/
theorem dyadicProjectedStep_inner_le_of_mantissa_separation
    (M N m n R : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmlo : 2^M ≤ m) (hmhi : m ≤ 2^(M+1))
    (hnlo : 2^N ≤ n) (hnhi : n ≤ 2^(N+1))
    (hsep : 1/(2 : ℝ)^R ≤ |(m : ℝ)/(2 : ℝ)^M - (n : ℝ)/(2 : ℝ)^N|) :
    inner ℝ (dyadicProjectedStep m hm) (dyadicProjectedStep n hn) ≤
      1+(R : ℝ)/4 := by
  have hprefix (K : ℕ) :
      (∑ i ∈ Finset.range (2^K-1),
        dyadicBoundaryCoordinate (dyadicProjectedStep m hm) i *
          dyadicBoundaryCoordinate (dyadicProjectedStep n hn) i) ≤ (R : ℝ) := by
    induction K with
    | zero => simp
    | succ K ih =>
      by_cases hKR : K < R
      · exact (dyadicBoundaryCoordinate_step_dyadic_prefix_product_sum_le
          (K+1) m n hm hn).trans (by exact_mod_cast (show K+1 ≤ R by omega))
      · have hp : 0 < (2 : ℕ)^K := by positivity
        have hab : 2^K-1 ≤ 2^(K+1)-1 := by
          rw [pow_succ']
          omega
        have hu : Finset.range (2^(K+1)-1) =
            Finset.range (2^K-1) ∪ Finset.Ico (2^K-1) (2^(K+1)-1) := by
          ext i
          simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
          omega
        have hd : Disjoint (Finset.range (2^K-1))
            (Finset.Ico (2^K-1) (2^(K+1)-1)) := by
          apply Finset.disjoint_left.mpr
          intro i hi hj
          have hi' := Finset.mem_range.mp hi
          have hj' := (Finset.mem_Ico.mp hj).1
          omega
        have hz : (∑ i ∈ Finset.Ico (2^K-1) (2^(K+1)-1),
            dyadicBoundaryCoordinate (dyadicProjectedStep m hm) i *
              dyadicBoundaryCoordinate (dyadicProjectedStep n hn) i) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          exact dyadicBoundaryCoordinate_step_product_zero_above_cutoff
            M N m n R hm hn hmlo hmhi hnlo hnhi hsep K i (by omega) hi
        rw [hu, Finset.sum_union hd, hz, add_zero]
        exact ih
  have hp : 0 < (2 : ℕ)^(M+N) := by positivity
  have hmc : m ≤ 2*((2 : ℕ)^(M+N)-1+1) := by
    have hpow : (2 : ℕ)^(M+1) ≤ 2*2^(M+N) := by
      simpa only [pow_succ'] using two_pow_mono (show M+1 ≤ M+N+1 by omega)
    omega
  have hnc : n ≤ 2*((2 : ℕ)^(M+N)-1+1) := by
    have hpow : (2 : ℕ)^(N+1) ≤ 2*2^(M+N) := by
      simpa only [pow_succ'] using two_pow_mono (show N+1 ≤ M+N+1 by omega)
    omega
  rw [dyadicProjectedStep_finite_boundary_inner m n hm hn (2^(M+N)-1) hmc hnc]
  have h := hprefix (M+N)
  linarith

end
end RiemannResearch.RH.Pareto
