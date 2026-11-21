import RiemannResearch.RH.AnnularPrimePairTargets
import RiemannResearch.NumberTheory.PrimePairEulerProductTail
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Mean value of the binary Hardy–Littlewood singular series

For the actual Euler product used by the annular prime-pair modules, the
average over all positive shifts tends to one. The proof expands the odd
local correction factors over subsets of primes and counts the multiples
of each resulting squarefree modulus exactly. See van de Bult and Korevaar,
*Mean value one of prime-pair constants*, Proposition 4.1,
https://arxiv.org/abs/0806.1667. Their even-shift constant is half of ours.
-/

noncomputable section
open Finset Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.AnnularPrimePair
open RiemannResearch.NumberTheory.PrimePairEulerProduct

private def primesBelow (N : ℕ) : Finset ℕ :=
  (range N).filter (fun p => p.Prime ∧ 2 < p)

private def divisorWeight (t : Finset ℕ) : ℝ :=
  ∏ p ∈ t, (1 / ((p : ℝ) - 2))

private def modulus (t : Finset ℕ) : ℕ :=
  2 * ∏ p ∈ t, p

private def truncated (N h : ℕ) : ℝ :=
  2 * twinPrimeConstant * ∑ t ∈ (primesBelow N).powerset,
    if modulus t ∣ h then divisorWeight t else 0

private theorem prime_data {N p : ℕ} (hp : p ∈ primesBelow N) :
    p.Prime ∧ 2 < p := (mem_filter.mp hp).2

private theorem weight_nonneg {N : ℕ} {t : Finset ℕ} (ht : t ⊆ primesBelow N) :
    0 ≤ divisorWeight t := by
  apply prod_nonneg
  intro p hp
  have h : (2 : ℝ) < p := by exact_mod_cast (prime_data (ht hp)).2
  positivity

private theorem modulus_pos {N : ℕ} {t : Finset ℕ} (ht : t ⊆ primesBelow N) :
    0 < modulus t := by
  apply Nat.mul_pos (by decide)
  exact prod_pos (fun p hp => (prime_data (ht hp)).1.pos)

private theorem modulus_dvd_iff {N h : ℕ} {t : Finset ℕ}
    (ht : t ⊆ primesBelow N) (hh : h ≠ 0) :
    modulus t ∣ h ↔ 2 ∣ h ∧ t ⊆ h.primeFactors.filter (fun p => 2 < p) := by
  have h2 : 2 ∉ t := fun hp => (lt_irrefl 2) (prime_data (ht hp)).2
  have hm : modulus t = ∏ p ∈ insert 2 t, p := by simp [modulus, h2]
  rw [hm]
  constructor
  · intro hd
    refine ⟨(dvd_prod_of_mem id (mem_insert_self 2 t)).trans hd, ?_⟩
    intro p hp
    have hpd : p ∣ h := (dvd_prod_of_mem id (mem_insert_of_mem hp)).trans hd
    exact mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨(prime_data (ht hp)).1, hpd, hh⟩,
      (prime_data (ht hp)).2⟩
  · rintro ⟨hd, hs⟩
    apply dvd_trans (prod_dvd_prod_of_subset (insert 2 t) h.primeFactors id ?_)
      (Nat.prod_primeFactors_dvd h)
    intro p hp
    rcases mem_insert.mp hp with he | he
    · exact he ▸ Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hd, hh⟩
    · exact (mem_filter.mp (hs he)).1

private theorem truncated_eq {N h : ℕ} (hh : 0 < h) (hN : h < N) :
    truncated N h = singularSeries h := by
  classical
  let D := h.primeFactors.filter (fun p => 2 < p)
  have hD : D ⊆ primesBelow N := by
    intro p hp
    obtain ⟨hpf, hbig⟩ := mem_filter.mp hp
    obtain ⟨hprime, hd, _⟩ := Nat.mem_primeFactors.mp hpf
    exact mem_filter.mpr ⟨mem_range.mpr ((Nat.le_of_dvd hh hd).trans_lt hN),
      hprime, hbig⟩
  by_cases he : 2 ∣ h
  · have hodd : ¬ h % 2 = 1 := by omega
    have filt : ((primesBelow N).powerset.filter (fun t => modulus t ∣ h)) =
        D.powerset := by
      ext t
      simp only [mem_filter, mem_powerset]
      constructor
      · rintro ⟨ht, hd⟩
        exact ((modulus_dvd_iff ht hh.ne').mp hd).2
      · intro ht
        exact ⟨ht.trans hD, (modulus_dvd_iff (ht.trans hD) hh.ne').mpr ⟨he, ht⟩⟩
    unfold truncated singularSeries
    rw [if_neg hodd, ← sum_filter, filt]
    change 2 * twinPrimeConstant * (∑ t ∈ D.powerset, ∏ p ∈ t, 1 / ((p : ℝ) - 2)) = _
    rw [← prod_one_add, ← prod_filter]
    congr 1
    apply prod_congr rfl
    intro p hp
    have h : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2
    field_simp [ne_of_gt (by linarith : 0 < (p : ℝ) - 2)]
    ring
  · have hodd : h % 2 = 1 := by omega
    rw [singularSeries_eq_zero_of_odd_gap h hodd]
    unfold truncated
    have hz : (∑ t ∈ (primesBelow N).powerset,
        if modulus t ∣ h then divisorWeight t else 0) = 0 := by
      apply sum_eq_zero
      intro t ht
      exact if_neg (fun hd => he (((modulus_dvd_iff (mem_powerset.mp ht) hh.ne').mp hd).1))
    rw [hz, mul_zero]

private theorem truncated_mono {M N : ℕ} (hmn : M ≤ N) (h : ℕ) :
    truncated M h ≤ truncated N h := by
  apply mul_le_mul_of_nonneg_left _ (by positivity [twinPrimeConstant_pos])
  apply sum_le_sum_of_subset_of_nonneg
  · exact powerset_mono.mpr (filter_subset_filter _ (range_mono hmn))
  · intro t ht _
    split_ifs
    · exact weight_nonneg (mem_powerset.mp ht)
    · exact le_rfl

/-- The cutoff Euler model counts each squarefree modulus with the integer quotient. -/
private theorem sum_truncated (N H : ℕ) :
    ∑ h ∈ Ioc 0 H, truncated N h =
      2 * twinPrimeConstant * ∑ t ∈ (primesBelow N).powerset,
        ((H / modulus t : ℕ) : ℝ) * divisorWeight t := by
  unfold truncated
  rw [← mul_sum, sum_comm]
  congr 1
  apply sum_congr rfl
  intro t _
  rw [← sum_filter, sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div]

private theorem finite_density (N : ℕ) :
    2 * twinPrimeConstant * (∑ t ∈ (primesBelow N).powerset,
      divisorWeight t / (modulus t : ℝ)) = twinPrimeConstant / partialProduct N := by
  classical
  have expand : ∀ t : Finset ℕ, 2 * (divisorWeight t / (modulus t : ℝ)) =
      ∏ p ∈ t, ((1 / ((p : ℝ) - 2)) / (p : ℝ)) := by
    intro t
    simp only [divisorWeight, modulus, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_prod,
      prod_div_distrib]
    ring
  have cancel : (∏ p ∈ primesBelow N, (1 + (1 / ((p : ℝ) - 2)) / (p : ℝ))) *
      partialProduct N = 1 := by
    unfold primesBelow partialProduct
    rw [prod_filter, ← prod_mul_distrib]
    apply prod_eq_one
    intro p _
    by_cases hp : p.Prime ∧ 2 < p
    · have hpR : (2 : ℝ) < p := by exact_mod_cast hp.2
      simp only [if_pos hp, primePairEulerFactor]
      field_simp [ne_of_gt (by linarith : 0 < (p : ℝ) - 2),
        ne_of_gt (by linarith : 0 < (p : ℝ) - 1), ne_of_gt (by linarith : 0 < (p : ℝ))]
      ring
    · simp [hp, primePairEulerFactor]
  apply (eq_div_iff (partialProduct_pos N).ne').mpr
  calc
    _ = twinPrimeConstant *
        ((∑ t ∈ (primesBelow N).powerset, 2 * (divisorWeight t / (modulus t : ℝ))) *
          partialProduct N) := by rw [← mul_sum]; ring
    _ = _ := by simp_rw [expand]; rw [← prod_one_add, cancel, mul_one]

private theorem quotient_bounds (H q : ℕ) (hq : 0 < q) :
    (H : ℝ) / q - 1 ≤ (↑(H / q) : ℝ) ∧ (↑(H / q) : ℝ) ≤ (H : ℝ) / q := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hm : (↑(H % q) : ℝ) < q := by exact_mod_cast Nat.mod_lt H hq
  have hs : (↑(H % q) : ℝ) + q * ↑(H / q) = (H : ℝ) := by
    exact_mod_cast Nat.mod_add_div H q
  constructor
  · apply sub_le_iff_le_add.mpr
    apply (div_le_iff₀ hqr).mpr
    nlinarith
  · apply (le_div_iff₀ hqr).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) (H % q)]

private theorem quotient_density (q : ℕ) (hq : 0 < q) :
    Tendsto (fun H : ℕ => (↑(H / q) : ℝ) / H) atTop (𝓝 (1 / (q : ℝ))) := by
  have hl := (tendsto_const_nhds (x := 1 / (q : ℝ))).sub
    (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
      Tendsto (fun H : ℕ => 1 / (H : ℝ)) atTop (𝓝 0))
  rw [sub_zero] at hl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 1] with H hH
    have Hpos : (0 : ℝ) < H := by exact_mod_cast hH
    apply (le_div_iff₀ Hpos).mpr
    calc
      (1 / (q : ℝ) - 1 / (H : ℝ)) * H = (H : ℝ) / q - 1 := by
        rw [sub_mul, div_mul_cancel₀ _ Hpos.ne']
        ring
      _ ≤ _ := (quotient_bounds H q hq).1
  · filter_upwards [eventually_ge_atTop 1] with H hH
    have Hpos : (0 : ℝ) < H := by exact_mod_cast hH
    apply (div_le_iff₀ Hpos).mpr
    calc
      _ ≤ (H : ℝ) / q := (quotient_bounds H q hq).2
      _ = _ := by ring

private theorem finite_mean (N : ℕ) :
    Tendsto (fun H : ℕ => (∑ h ∈ Ioc 0 H, truncated N h) / H) atTop
      (𝓝 (twinPrimeConstant / partialProduct N)) := by
  rw [← finite_density]
  have hs : Tendsto (fun H : ℕ => ∑ t ∈ (primesBelow N).powerset,
      ((↑(H / modulus t) : ℝ) / H) * divisorWeight t) atTop
      (𝓝 (∑ t ∈ (primesBelow N).powerset, (1 / (modulus t : ℝ)) * divisorWeight t)) :=
    tendsto_finsetSum _ fun t ht =>
      (quotient_density _ (modulus_pos (mem_powerset.mp ht))).mul_const _
  convert hs.const_mul (2 * twinPrimeConstant) using 1
  · funext H
    rw [sum_truncated, mul_div_assoc, Finset.sum_div]
    congr 1
    apply sum_congr rfl
    intro t _
    ring
  · congr 2
    apply sum_congr rfl
    intro t _
    ring

/-- For every positive integer cutoff the binary singular series has mean at most one. -/
theorem sum_singularSeries_le (H : ℕ) :
    (∑ h ∈ Ioc 0 H, singularSeries h) ≤ (H : ℝ) := by
  let N := H + 1
  have hsum : (∑ h ∈ Ioc 0 H, singularSeries h) = ∑ h ∈ Ioc 0 H, truncated N h := by
    apply sum_congr rfl
    intro h hh
    exact (truncated_eq (mem_Ioc.mp hh).1 (Nat.lt_succ_of_le (mem_Ioc.mp hh).2)).symm
  rw [hsum, sum_truncated]
  calc
    _ ≤ 2 * twinPrimeConstant * ∑ t ∈ (primesBelow N).powerset,
        ((H : ℝ) / (modulus t : ℝ)) * divisorWeight t := by
      apply mul_le_mul_of_nonneg_left _ (by positivity [twinPrimeConstant_pos])
      exact sum_le_sum fun t ht => mul_le_mul_of_nonneg_right
        (quotient_bounds H _ (modulus_pos (mem_powerset.mp ht))).2
        (weight_nonneg (mem_powerset.mp ht))
    _ = H * (twinPrimeConstant / partialProduct N) := by
      rw [← finite_density, mul_left_comm (H : ℝ) (2 * twinPrimeConstant)]
      congr 1
      rw [mul_sum]
      apply sum_congr rfl
      intro t _
      ring
    _ ≤ H * 1 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg H)
      exact (div_le_one (partialProduct_pos N)).mpr (twinPrimeConstant_le_finite_product _)
    _ = _ := mul_one _

/-- The arithmetic model has Cesàro mean one, including the vanishing odd shifts. -/
theorem tendsto_singularSeries_mean :
    Tendsto (fun H : ℕ => (∑ h ∈ Ioc 0 H, singularSeries h) / H)
      atTop (𝓝 1) := by
  have hprod : Tendsto partialProduct atTop (𝓝 twinPrimeConstant) :=
    primePairEulerFactor_multipliable.hasProd.tendsto_prod_nat
  have hlim := (tendsto_const_nhds (x := twinPrimeConstant)).div hprod twinPrimeConstant_ne_zero
  rw [div_self twinPrimeConstant_ne_zero] at hlim
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨N, hN⟩ := (hlim.eventually (eventually_gt_nhds ha)).exists
    filter_upwards [(finite_mean N).eventually (eventually_gt_nhds hN),
      eventually_ge_atTop N] with H ht hH
    apply lt_of_lt_of_le ht
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply sum_le_sum
    intro h hh
    have he := truncated_eq (mem_Ioc.mp hh).1 (Nat.lt_succ_of_le (mem_Ioc.mp hh).2)
    rw [← he]
    exact truncated_mono (hH.trans (Nat.le_succ H)) h
  · intro b hb
    filter_upwards [eventually_ge_atTop 1] with H hH
    have Hpos : (0 : ℝ) < H := by exact_mod_cast hH
    exact lt_of_le_of_lt ((div_le_one Hpos).mpr (sum_singularSeries_le H)) hb

end RiemannResearch.RH.AnnularPrimePair
