import RiemannResearch.Analysis.MontgomeryPrimeProbeLogSpectrum
import Mathlib.NumberTheory.EulerProduct.Basic

/-! # The mean square of the prime-power atoms -/

noncomputable section
namespace RiemannResearch.Analysis.MontgomeryPrimeTrace
open Filter MeasureTheory Set ZeroOrdinate
open scoped Topology BigOperators

def primeProbeDiagonal : ℝ := ∑' n : ℕ, primeAtomWeight n ^ 2

def primeProbePartialDiagonal (Y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊Real.exp Y⌋₊, primeAtomWeight n ^ 2

theorem summable_primeAtomWeight_sq : Summable (fun n : ℕ => primeAtomWeight n ^ 2) := by
  have hs := (Real.summable_nat_rpow.mpr (by norm_num : (-3/2 : ℝ) < -1)).mul_left 16
  apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) _ hs
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num [primeAtomWeight]
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have ha : primeAtomWeight n ≤ 4*(n:ℝ)^(-(3/4):ℝ) := by
    calc
      _ ≤ ((n:ℝ)^(1/4:ℝ)/(1/4)) / n :=
        div_le_div_of_nonneg_right (ArithmeticFunction.vonMangoldt_le_log.trans
          (Real.log_le_rpow_div hn'.le (by norm_num))) hn'.le
      _ = _ := by
        rw [show (-(3/4) : ℝ) = 1/4-1 by norm_num, Real.rpow_sub_one hn'.ne']
        ring
  have ha0 : 0 ≤ primeAtomWeight n := div_nonneg ArithmeticFunction.vonMangoldt_nonneg hn'.le
  calc
    _ ≤ (4*(n:ℝ)^(-(3/4):ℝ))^2 := pow_le_pow_left₀ ha0 ha 2
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast hn'.le]
      norm_num

theorem primeProbeDiagonal_pos : 0 < primeProbeDiagonal := by
  have h := summable_primeAtomWeight_sq.sum_le_tsum ({2} : Finset ℕ) (fun _ _ => sq_nonneg _)
  simp only [Finset.sum_singleton] at h
  have hp : 0 < primeAtomWeight 2 := by
    simp only [primeAtomWeight, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    positivity
  exact (sq_pos_of_pos hp).trans_le h

/-- Regrouping the square-summable atoms over the distinct prime powers and evaluating each
geometric series gives the boundary coefficient as a single sum over primes. -/
theorem primeProbeDiagonal_eq_tsum_primes :
    primeProbeDiagonal = ∑' p : Nat.Primes, Real.log (p:ℕ)^2 / ((p:ℝ)^2-1) := by
  have hs : Function.support (fun n => primeAtomWeight n ^ 2) ⊆ {n | IsPrimePow n} := by
    intro n hn
    by_contra h
    change ¬ IsPrimePow n at h
    exact hn (by simp [primeAtomWeight,ArithmeticFunction.vonMangoldt_apply,h])
  rw [primeProbeDiagonal,
    tsum_eq_tsum_primes_of_support_subset_prime_powers summable_primeAtomWeight_sq hs]
  apply tsum_congr
  intro p
  let x : ℝ := (p:ℕ)
  have hx : 1 < x := by dsimp [x]; exact_mod_cast p.property.one_lt
  have hpos : 0 < x := by linarith
  have hx2 : 1 < x^2 := by nlinarith [sq_nonneg (x-1)]
  have hgeom : (x^2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx2
  have hw (j : ℕ) : primeAtomWeight ((p:ℕ)^(j+1))^2 =
      ((Real.log x)^2/x^2) * ((x^2)⁻¹)^j := by
    rw [primeAtomWeight,ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero j),
      ArithmeticFunction.vonMangoldt_apply_prime p.property,Nat.cast_pow, div_pow]
    change Real.log x^2 / (x^(j+1))^2 = _
    have hp : (x^j)^2 = (x^2)^j := by rw [← pow_mul,Nat.mul_comm,pow_mul]
    rw [pow_succ x j, mul_pow, hp, inv_pow]
    field_simp [hpos.ne']
    <;> ring
  simp_rw [hw]
  rw [tsum_mul_left,tsum_geometric_of_lt_one (by positivity) hgeom]
  change (Real.log x^2/x^2)*(1-(x^2)⁻¹)⁻¹ = Real.log x^2/(x^2-1)
  field_simp [hpos.ne',(sub_pos.mpr hx2).ne']
  <;> ring

theorem primeProbePartialDiagonal_le (Y : ℝ) : primeProbePartialDiagonal Y ≤ primeProbeDiagonal :=
  summable_primeAtomWeight_sq.sum_le_tsum _ (fun _ _ => sq_nonneg _)

theorem tendsto_primeProbePartialDiagonal :
    Tendsto primeProbePartialDiagonal atTop (𝓝 primeProbeDiagonal) := by
  have hN : Tendsto (fun Y : ℝ => ⌊Real.exp Y⌋₊ + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp (tendsto_nat_floor_atTop.comp Real.tendsto_exp_atTop)
  apply (summable_primeAtomWeight_sq.hasSum.tendsto_sum_nat.comp hN).congr
  intro Y
  change (∑ i ∈ Finset.range (⌊Real.exp Y⌋₊+1), primeAtomWeight i ^ 2) = _
  have he (N : ℕ) : Finset.Ioc 0 N = (Finset.range (N+1)).erase 0 := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_erase, Finset.mem_range]
    omega
  unfold primeProbePartialDiagonal
  rw [he, Finset.sum_erase_eq_sub (Finset.mem_range.mpr (Nat.zero_lt_succ _))]
  simp [primeAtomWeight]

/-- The weighted Montgomery–Vaughan bound is uniform over every subset of the logarithmic
atoms up to the cutoff, including intervals obtained by deleting a finite head. -/
theorem primeAtomSubset_mean_square {Y : ℝ} (hY : 0 ≤ Y) (B : ℝ) (s : Finset ℕ)
    (hs : s ⊆ Finset.Ioc 0 ⌊Real.exp Y⌋₊) :
    |(∫ t in (0:ℝ)..B, ‖∑ j ∈ s, (primeAtomWeight j : ℂ)*phase (Real.log j) t‖^2) -
      B * ∑ j ∈ s, primeAtomWeight j^2| ≤ 52 * Y * (Y + (Real.log 4 + 4)) := by
  classical
  let n : s → ℕ := Subtype.val
  let w (i : s) : ℂ := (primeAtomWeight (n i) : ℂ)
  have hn (i : s) : 1 ≤ n i := (Finset.mem_Ioc.mp (hs i.property)).1
  have hp (i : s) : 0 < (n i : ℝ) := by exact_mod_cast hn i
  have hj : Function.Injective n := Subtype.val_injective
  have hinj : Function.Injective (fun i : s => Real.log (n i : ℝ)) := by
    intro i j hij
    apply hj
    exact_mod_cast Real.log_injOn_pos (Set.mem_Ioi.mpr (hp i)) (Set.mem_Ioi.mpr (hp j)) hij
  have hmv := DirichletMeanSquare.abs_integral_norm_sq_sub_le w (fun i => Real.log (n i))
    (fun i => 1/(2*(n i:ℝ))) hinj (fun i => by have := hp i; positivity)
    (fun i j hij => Zeta23.PrimeSide.inv_two_mul_le_abs_log_sub
      (hn i) (hn j) (fun e => hij (hj e))) 0 B
  have hnw (i : s) : ‖w i‖ = primeAtomWeight (n i) :=
    (Complex.norm_real _).trans (abs_of_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (hp i).le))
  have he (t : ℝ) : DirichletMeanSquare.polynomial w (fun i => Real.log (n i)) t =
      (∑ j ∈ s, (primeAtomWeight j : ℂ)*phase (Real.log j) t) :=
    Finset.sum_coe_sort s (fun j => (primeAtomWeight j : ℂ) * phase (Real.log j) t)
  simp_rw [he, hnw] at hmv
  rw [sub_zero, Finset.sum_coe_sort s (fun j => primeAtomWeight j ^ 2)] at hmv
  refine hmv.trans ?_
  have hm := Zeta23.Cheb.mertensFirst (Real.one_le_exp hY)
  rw [Real.log_exp] at hm
  have hsum : (∑ i : s, primeAtomWeight (n i)) ≤ Y + (Real.log 4 + 4) := by
    rw [Finset.sum_coe_sort s primeAtomWeight]
    calc
      _ ≤ ∑ i ∈ Finset.Ioc 0 ⌊Real.exp Y⌋₊, primeAtomWeight i :=
        Finset.sum_le_sum_of_subset_of_nonneg hs (fun i _ _ =>
          div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg i))
      _ ≤ _ := by
        unfold primeAtomWeight
        linarith only [(abs_le.mp hm).2]
  have hweight (i : s) : primeAtomWeight (n i)^2/(1/(2*(n i:ℝ))) ≤ 2*Y*primeAtomWeight (n i) := by
    have hle : (n i:ℝ) ≤ Real.exp Y := (Nat.le_floor_iff (Real.exp_pos _).le).1
      (Finset.mem_Ioc.mp (hs i.property)).2
    have hΛ : ArithmeticFunction.vonMangoldt (n i) ≤ Y :=
      ArithmeticFunction.vonMangoldt_le_log.trans ((Real.log_le_iff_le_exp (hp i)).2 hle)
    have he' : primeAtomWeight (n i)^2/(1/(2*(n i:ℝ))) =
        2*ArithmeticFunction.vonMangoldt (n i)*primeAtomWeight (n i) := by
      unfold primeAtomWeight
      field_simp [(hp i).ne']
    rw [he']
    exact mul_le_mul_of_nonneg_right (by linarith only [hΛ])
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (hp i).le)
  calc
    _ ≤ 26 * ∑ i : s, (2*Y)*primeAtomWeight (n i) := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hweight i) (by norm_num)
    _ ≤ _ := by
      rw [← Finset.mul_sum, ← mul_assoc, show 26*(2*Y) = 52*Y by ring]
      exact mul_le_mul_of_nonneg_left hsum (by positivity)

/-- Mean square of the full finite prime-power polynomial. -/
theorem primeLogPolynomial_mean_square {Y : ℝ} (hY : 0 ≤ Y) (B : ℝ) :
    |(∫ t in (0:ℝ)..B, ‖primeLogPolynomial Y t‖^2) - B * primeProbePartialDiagonal Y| ≤
      52 * Y * (Y + (Real.log 4 + 4)) :=
  primeAtomSubset_mean_square hY B _ (fun _ h => h)

/-- Mean square of a finite prime-power tail. Only the omitted diagonal occurs in the main term. -/
theorem primeLogPolynomial_tail_mean_square {M Y : ℝ} (hM : 0 ≤ M) (hMY : M ≤ Y) (B : ℝ) :
    |(∫ t in (0:ℝ)..B, ‖primeLogPolynomial Y t - primeLogPolynomial M t‖^2) -
      B*(primeProbePartialDiagonal Y - primeProbePartialDiagonal M)| ≤ 52*Y*(Y+(Real.log 4+4)) := by
  classical
  let m := Finset.Ioc 0 ⌊Real.exp M⌋₊
  let s := Finset.Ioc 0 ⌊Real.exp Y⌋₊
  have hsub : m ⊆ s := Finset.Ioc_subset_Ioc_right (Nat.floor_le_floor (Real.exp_le_exp.mpr hMY))
  have he {A : Type} [AddCommGroup A] (f : ℕ → A) :
      (∑ n ∈ s, f n)-(∑ n ∈ m, f n) = ∑ n ∈ s \ m, f n := by
    exact sub_eq_of_eq_add (Finset.sum_sdiff (f := f) hsub).symm
  have hp (t : ℝ) : primeLogPolynomial Y t-primeLogPolynomial M t =
      ∑ j ∈ s \ m, (primeAtomWeight j : ℂ)*phase (Real.log j) t :=
    he (fun j => (primeAtomWeight j : ℂ)*phase (Real.log j) t)
  have hd : primeProbePartialDiagonal Y-primeProbePartialDiagonal M =
      ∑ j ∈ s \ m, primeAtomWeight j^2 := he (fun j => primeAtomWeight j^2)
  simp_rw [hp,hd]
  exact primeAtomSubset_mean_square (hM.trans hMY) B (s \ m) Finset.sdiff_subset

/--
info: 'RiemannResearch.Analysis.MontgomeryPrimeTrace.primeProbeDiagonal_eq_tsum_primes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms primeProbeDiagonal_eq_tsum_primes

/--
info: 'RiemannResearch.Analysis.MontgomeryPrimeTrace.primeProbeDiagonal_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms primeProbeDiagonal_pos

/--
info: 'RiemannResearch.Analysis.MontgomeryPrimeTrace.primeLogPolynomial_tail_mean_square' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms primeLogPolynomial_tail_mean_square

end RiemannResearch.Analysis.MontgomeryPrimeTrace
