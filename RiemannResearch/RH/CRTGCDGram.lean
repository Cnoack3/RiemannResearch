import Mathlib.Algebra.BigOperators.Field
import RiemannResearch.RH.CRTSparseEnergy

/-!
# Exact GCD reference form for sparse CRT packets

The finite incidence expansion retains every signed mixed term.
Background for the classical GCD kernel: C. Aistleitner, I. Berkes, K. Seip,
"GCD sums from Poisson integrals and systems of dilated functions",
J. Eur. Math. Soc. 17 (2015), 1517–1546, Section 4,
https://doi.org/10.4171/JEMS/537.
This reference supports the kernel terminology and context. The proofs here
derive the identities directly from simultaneous divisibility and summation.
No novelty claim is made for the GCD matrix.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CRTSparseEnergy
open RiemannResearch.RH.Pareto

def zetaTwoSeries : ℝ := ∑' n : ℕ, 1/(n : ℝ)^2

/-- Exact reciprocal-square mass of a divisibility class. -/
theorem inverseSquare_multiples (L : ℕ) (hL : 0 < L) :
    (∑' n : ℕ, if L ∣ n then 1/(n : ℝ)^2 else 0) =
      zetaTwoSeries/(L : ℝ)^2 := by
  have he : (∑' n : ℕ, if L ∣ n then 1/(n : ℝ)^2 else 0) =
      ∑' a : ℕ, (1/(L : ℝ)^2)*(1/(a : ℝ)^2) := by
    apply tsum_eq_tsum_of_ne_zero_bij
      (fun a : Function.support (fun a : ℕ => (1/(L : ℝ)^2)*(1/(a : ℝ)^2)) =>
        L*a.val)
    · intro a b hab
      exact Subtype.ext (Nat.eq_of_mul_eq_mul_left hL hab)
    · intro n hn
      have hdiv : L ∣ n := by
        by_contra hh
        simpa only [Function.mem_support, if_neg hh, ne_eq, not_true_eq_false] using hn
      have hnz : n ≠ 0 := by
        intro hh
        subst n
        simpa [Function.mem_support] using hn
      obtain ⟨a, rfl⟩ := hdiv
      have ha : 0 < a := by
        by_contra hh
        have hz : a=0 := Nat.eq_zero_of_not_pos hh
        simp [hz] at hnz
      refine ⟨⟨a, ?_⟩, rfl⟩
      change (1/(L : ℝ)^2)*(1/(a : ℝ)^2) ≠ 0
      positivity
    · intro a
      rw [if_pos (dvd_mul_right L a.val)]
      push_cast
      simp only [mul_pow, one_div, mul_inv]
  rw [he, tsum_mul_left]
  unfold zetaTwoSeries
  ring

def gcdReferenceKernel (d e : ℕ) : ℝ :=
  ∑' n : ℕ, if d ∣ n ∧ e ∣ n then (d : ℝ)*(e : ℝ)/(n : ℝ)^2 else 0

/-- The exact CRT/GCD Gram entry, initially in its lcm normalization. -/
theorem gcdReferenceKernel_lcm (d e : ℕ) (hL : 0 < Nat.lcm d e) :
    gcdReferenceKernel d e =
      zetaTwoSeries * ((d : ℝ)*(e : ℝ)/(Nat.lcm d e : ℝ)^2) := by
  have ht (n : ℕ) :
      (if d ∣ n ∧ e ∣ n then (d : ℝ)*(e : ℝ)/(n : ℝ)^2 else 0) =
        ((d : ℝ)*(e : ℝ)) *
          (if Nat.lcm d e ∣ n then 1/(n : ℝ)^2 else 0) := by
    simp only [Nat.lcm_dvd_iff]
    split_ifs <;> ring
  unfold gcdReferenceKernel
  simp_rw [ht]
  rw [tsum_mul_left, inverseSquare_multiples _ hL]
  ring

/-- The same exact entry in the classical GCD normalization. -/
theorem gcdReferenceKernel_gcd (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hL : 0 < Nat.lcm d e) :
    gcdReferenceKernel d e =
      zetaTwoSeries * ((Nat.gcd d e : ℝ)^2/((d : ℝ)*(e : ℝ))) := by
  rw [gcdReferenceKernel_lcm d e hL]
  congr 1
  have hdR : (d : ℝ) ≠ 0 := by positivity
  have heR : (e : ℝ) ≠ 0 := by positivity
  have hLR : (Nat.lcm d e : ℝ) ≠ 0 := by positivity
  have hprod : (Nat.gcd d e : ℝ)*(Nat.lcm d e : ℝ) = (d : ℝ)*(e : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm d e
  have hs := congrArg (fun x : ℝ => x^2) hprod
  field_simp
  nlinarith [hs]

theorem zetaTwoSeries_summable : Summable (fun n : ℕ => 1/(n : ℝ)^2) := by
  apply (summable_nat_add_iff 1).mp
  have h := bounded_profile_summable (fun _ => (1 : ℝ)) 1 (by norm_num)
    (fun _ => by norm_num)
  simpa only [Nat.cast_add, Nat.cast_one, div_pow, one_pow] using h

theorem gcdReferenceTerm_summable (d e : ℕ) :
    Summable (fun n : ℕ =>
      if d ∣ n ∧ e ∣ n then (d : ℝ)*(e : ℝ)/(n : ℝ)^2 else 0) := by
  apply Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) _
    (zetaTwoSeries_summable.mul_left ((d : ℝ)*(e : ℝ)))
  intro n
  split_ifs
  · exact le_of_eq (by ring)
  · positivity

theorem incidenceProfile_square_expansion (s : Finset ℕ) (c : ℕ → ℝ) (n : ℕ) :
    (incidenceProfile s c n/(n : ℝ))^2 =
      ∑ d ∈ s, ∑ e ∈ s,
        (c d*c e) * (if d ∣ n ∧ e ∣ n then (d : ℝ)*(e : ℝ)/(n : ℝ)^2 else 0) := by
  unfold incidenceProfile
  rw [div_pow, pow_two]
  simp only [Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  by_cases hdn : d ∣ n <;> by_cases hen : e ∣ n <;>
    simp only [hdn, hen, and_self, and_false, false_and, if_true, if_false] <;> ring

/-- Full signed GCD quadratic form: every mixed term is retained. -/
theorem referenceEnergy_incidenceProfile (s : Finset ℕ) (c : ℕ → ℝ) :
    referenceEnergy (incidenceProfile s c) =
      ∑ d ∈ s, ∑ e ∈ s, c d*c e*gcdReferenceKernel d e := by
  have hs : Summable (fun n : ℕ => (incidenceProfile s c n/(n : ℝ))^2) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.cast_add, Nat.cast_one] using incidenceProfile_summable s c
  have hall : referenceEnergy (incidenceProfile s c) =
      ∑' n : ℕ, (incidenceProfile s c n/(n : ℝ))^2 := by
    simpa [referenceEnergy, Finset.sum_range_one] using hs.sum_add_tsum_nat_add 1
  rw [hall]
  simp_rw [incidenceProfile_square_expansion]
  have hterm (d e : ℕ) : Summable (fun n : ℕ =>
      (c d*c e)*(if d ∣ n ∧ e ∣ n then (d : ℝ)*(e : ℝ)/(n : ℝ)^2 else 0)) :=
    (gcdReferenceTerm_summable d e).mul_left (c d*c e)
  have hinner (d : ℕ) : Summable (fun n : ℕ => ∑ e ∈ s,
      (c d*c e)*(if d ∣ n ∧ e ∣ n then (d : ℝ)*(e : ℝ)/(n : ℝ)^2 else 0)) := by
    clear hs hall
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hterm d a).add ih
  calc
    (∑' n : ℕ, ∑ d ∈ s, ∑ e ∈ s,
        (c d*c e)*(if d ∣ n ∧ e ∣ n then (d : ℝ)*(e : ℝ)/(n : ℝ)^2 else 0)) =
        ∑ d ∈ s, ∑' n : ℕ, ∑ e ∈ s,
          (c d*c e)*(if d ∣ n ∧ e ∣ n then (d : ℝ)*(e : ℝ)/(n : ℝ)^2 else 0) :=
      Summable.tsum_finsetSum (fun d hd => hinner d)
    _ = ∑ d ∈ s, ∑ e ∈ s, ∑' n : ℕ,
          (c d*c e)*(if d ∣ n ∧ e ∣ n then (d : ℝ)*(e : ℝ)/(n : ℝ)^2 else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact Summable.tsum_finsetSum (fun e he => hterm d e)
    _ = _ := by simp only [tsum_mul_left, gcdReferenceKernel]

theorem incidence_sparseEnergy_gcd_relative_bounds (M : ℕ) (hM : 0 < M)
    (s : Finset ℕ) (c : ℕ → ℝ) :
    ((M : ℝ)/((M : ℝ)+1)) *
        (∑ d ∈ s, ∑ e ∈ s, c d*c e*gcdReferenceKernel d e) ≤
      sparseEnergy M (incidenceProfile s c) ∧
    sparseEnergy M (incidenceProfile s c) ≤
      ∑ d ∈ s, ∑ e ∈ s, c d*c e*gcdReferenceKernel d e := by
  simpa only [referenceEnergy_incidenceProfile] using
    sparseEnergy_relative_bounds M hM (incidenceProfile s c) (incidenceProfile_summable s c)

end RiemannResearch.RH.Pareto.CRTSparseEnergy
