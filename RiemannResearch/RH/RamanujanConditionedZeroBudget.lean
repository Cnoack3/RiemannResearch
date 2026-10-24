import RiemannResearch.RH.RamanujanZeroCountBounds
import Mathlib.Data.Fintype.BigOperators

/-!
# Head-conditioned zero budgets from actual Ramanujan captured mass

Source: the user's fifth Ramanujan transfer program, October 2026.
A certified finite head consumes part of the product budget. The remaining
zeros must support the larger conditional mass M/P_head. The exact logarithmic
count identity retains both threshold slack and unused conditional mass.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem mellinZeroProduct_sum (h : ι → ℂ) (z : κ → ℂ) :
    mellinZeroProduct (Sum.elim h z) = mellinZeroProduct h * mellinZeroProduct z := by
  simp only [mellinZeroProduct, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]

theorem mellinZeroProduct_pos (z : ι → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hz1 : ∀ i, z i ≠ 1) :
    0 < mellinZeroProduct z := by
  classical
  apply Finset.prod_pos
  intro i _
  apply zeroFactor_pos (z i) _ (hz1 i)
  intro hi
  have h := hzre i
  simp only [hi, Complex.zero_re] at h
  linarith

theorem mellinZeroProduct_le_one (z : ι → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) : mellinZeroProduct z ≤ 1 := by
  classical
  apply Finset.prod_le_one
  · intro i _
    exact sq_nonneg _
  · intro i _
    exact (zeroFactor_lt_one (z i) (hzre i)).le

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.RamanujanZeroCertificates
open Pareto Pareto.CoefficientStabilization RamanujanCanonicalOptimizer
open RiemannResearch.Analysis.ContractiveLogBudget
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Exact factor removal from a head plus an arbitrary disjoint finite tail. -/
theorem zero_head_packet_mass_bound (h : ι → ℂ) (z : κ → ℂ)
    (hhre : ∀ i, (1 / 2 : ℝ) < (h i).re) (hzre : ∀ j, (1 / 2 : ℝ) < (z j).re)
    (hinj : Function.Injective (Sum.elim h z))
    (hh1 : ∀ i, h i ≠ 1) (hz1 : ∀ j, z j ≠ 1)
    (hhzero : ∀ i, riemannZeta (h i) = 0) (hzzero : ∀ j, riemannZeta (z j) = 0)
    (n : ℕ) : packetMass n / mellinZeroProduct h ≤ mellinZeroProduct z := by
  classical
  have hb := packetMass_le_zeroProduct (Sum.elim h z)
    (fun i => by cases i with | inl i => exact hhre i | inr j => exact hzre j)
    hinj (fun i => by cases i with | inl i => exact hh1 i | inr j => exact hz1 j)
    (fun i => by cases i with | inl i => exact hhzero i | inr j => exact hzzero j) n
  rw [mellinZeroProduct_sum] at hb
  apply (div_le_iff₀ (mellinZeroProduct_pos h hhre hh1)).mpr
  simpa only [mul_comm] using hb

theorem zero_head_limit_mass_bound (h : ι → ℂ) (z : κ → ℂ)
    (hhre : ∀ i, (1 / 2 : ℝ) < (h i).re) (hzre : ∀ j, (1 / 2 : ℝ) < (z j).re)
    (hinj : Function.Injective (Sum.elim h z))
    (hh1 : ∀ i, h i ≠ 1) (hz1 : ∀ j, z j ≠ 1)
    (hhzero : ∀ i, riemannZeta (h i) = 0) (hzzero : ∀ j, riemannZeta (z j) = 0) :
    (1 - limitEnergy) / mellinZeroProduct h ≤ mellinZeroProduct z := by
  exact le_of_tendsto' (packetMass_tendsto.div_const _)
    (zero_head_packet_mass_bound h z hhre hzre hinj hh1 hz1 hhzero hzzero)

/-- The limiting budget is at least as strong as every finite packet budget,
and conditioning on a legal head is at least as strong as the original mass. -/
theorem zero_head_mass_comparison (h : ι → ℂ)
    (hhre : ∀ i, (1 / 2 : ℝ) < (h i).re) (hh1 : ∀ i, h i ≠ 1) (n : ℕ) :
    packetMass n ≤ packetMass n / mellinZeroProduct h ∧
      packetMass n / mellinZeroProduct h ≤ (1 - limitEnergy) / mellinZeroProduct h := by
  have hp := mellinZeroProduct_pos h hhre hh1
  have hmass : packetMass n ≤ 1 - limitEnergy := by
    have ht := packetMass_tendsto.comp (tendsto_add_atTop_nat n)
    exact ge_of_tendsto' ht (fun j => packetMass_monotone (by omega : n ≤ j + n))
  constructor
  · apply (le_div_iff₀ hp).mpr
    have hnonneg := (packetMass_bounds n).1
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (mellinZeroProduct_le_one h hhre) hnonneg
  · exact div_le_div_of_nonneg_right hmass hp.le

theorem zero_head_count_limit_exact (h : ι → ℂ) (z : κ → ℂ)
    (hhre : ∀ i, (1 / 2 : ℝ) < (h i).re) (hzre : ∀ j, (1 / 2 : ℝ) < (z j).re)
    (hh1 : ∀ i, h i ≠ 1) (hz1 : ∀ j, z j ≠ 1)
    {η : ℝ} (hη : η < 1) :
    -Real.log ((1 - limitEnergy) / mellinZeroProduct h) =
      (Fintype.card κ : ℝ) * (-Real.log (1 - η)) +
      (∑ j, Real.log ((1 - η) / zeroFactor (z j))) +
      Real.log (mellinZeroProduct z / ((1 - limitEnergy) / mellinZeroProduct h)) := by
  classical
  have hz0 : ∀ j, z j ≠ 0 := by
    intro j hj; have h := hzre j; simp only [hj, Complex.zero_re] at h; linarith
  simpa only [Finset.card_univ, mellinZeroProduct, zeroFactor] using
    finite_count_budget_exact Finset.univ (fun j => zeroFactor (z j))
      (fun j _ => zeroFactor_pos (z j) (hz0 j) (hz1 j))
      (div_pos packetLimitMass_pos (mellinZeroProduct_pos h hhre hh1))
      (show 0 < 1 - η by linarith)

theorem zero_head_count_log_bound (h : ι → ℂ) (z : κ → ℂ)
    (hhre : ∀ i, (1 / 2 : ℝ) < (h i).re) (hzre : ∀ j, (1 / 2 : ℝ) < (z j).re)
    (hinj : Function.Injective (Sum.elim h z))
    (hh1 : ∀ i, h i ≠ 1) (hz1 : ∀ j, z j ≠ 1)
    (hhzero : ∀ i, riemannZeta (h i) = 0) (hzzero : ∀ j, riemannZeta (z j) = 0)
    {η : ℝ} (hη : η < 1) (hcharge : ∀ j, η ≤ zeroCharge (z j)) :
    (Fintype.card κ : ℝ) * (-Real.log (1 - η)) ≤
      -Real.log ((1 - limitEnergy) / mellinZeroProduct h) := by
  classical
  have hz0 : ∀ j, z j ≠ 0 := by
    intro j hj; have h := hzre j; simp only [hj, Complex.zero_re] at h; linarith
  have hfactor : ∀ j ∈ Finset.univ, zeroFactor (z j) ≤ 1 - η := by
    intro j _
    have h := hcharge j
    rw [zeroCharge_eq_defect _ (hz0 j)] at h
    linarith
  simpa only [Finset.card_univ, mellinZeroProduct, zeroFactor] using
    finite_count_log_bound Finset.univ (fun j => zeroFactor (z j))
      (fun j _ => zeroFactor_pos (z j) (hz0 j) (hz1 j))
      (div_pos packetLimitMass_pos (mellinZeroProduct_pos h hhre hh1))
      (show 0 < 1 - η by linarith) hfactor
      (zero_head_limit_mass_bound h z hhre hzre hinj hh1 hz1 hhzero hzzero)

theorem zero_head_count_product_bound (h : ι → ℂ) (z : κ → ℂ)
    (hhre : ∀ i, (1 / 2 : ℝ) < (h i).re) (hzre : ∀ j, (1 / 2 : ℝ) < (z j).re)
    (hinj : Function.Injective (Sum.elim h z))
    (hh1 : ∀ i, h i ≠ 1) (hz1 : ∀ j, z j ≠ 1)
    (hhzero : ∀ i, riemannZeta (h i) = 0) (hzzero : ∀ j, riemannZeta (z j) = 0)
    {η : ℝ} (hcharge : ∀ j, η ≤ zeroCharge (z j)) :
    (1 - limitEnergy) / mellinZeroProduct h ≤ (1 - η) ^ Fintype.card κ := by
  classical
  have hz0 : ∀ j, z j ≠ 0 := by
    intro j hj; have h := hzre j; simp only [hj, Complex.zero_re] at h; linarith
  have hfactor : ∀ j ∈ Finset.univ, zeroFactor (z j) ≤ 1 - η := by
    intro j _
    have h := hcharge j
    rw [zeroCharge_eq_defect _ (hz0 j)] at h
    linarith
  simpa only [Finset.card_univ, mellinZeroProduct, zeroFactor] using
    finite_count_product_bound Finset.univ (fun j => zeroFactor (z j))
      (fun j _ => sq_nonneg _) hfactor
      (zero_head_limit_mass_bound h z hhre hzre hinj hh1 hz1 hhzero hzzero)

/-- Each new zero must lie outside the disk enlarged by the certified head. -/
theorem zero_outside_head_conditioned_packet_disk (h : ι → ℂ) (t : ℂ)
    (hhre : ∀ i, (1 / 2 : ℝ) < (h i).re) (htre : (1 / 2 : ℝ) < t.re)
    (hinj : Function.Injective (Sum.elim h (fun _ : Unit => t)))
    (hh1 : ∀ i, h i ≠ 1) (ht1 : t ≠ 1)
    (hhzero : ∀ i, riemannZeta (h i) = 0) (htzero : riemannZeta t = 0) (n : ℕ) :
    let m := packetMass n / mellinZeroProduct h
    m / (1 - m) ^ 2 ≤ (t.re - 1 / (1 - m)) ^ 2 + t.im ^ 2 := by
  have hb := zero_head_packet_mass_bound h (fun _ : Unit => t) hhre (fun _ => htre)
    hinj hh1 (fun _ => ht1) hhzero (fun _ => htzero) n
  have hb' : packetMass n / mellinZeroProduct h ≤ zeroFactor t := by
    simpa only [mellinZeroProduct, Fintype.prod_unique, zeroFactor] using hb
  have hm : packetMass n / mellinZeroProduct h < 1 :=
    hb'.trans_lt (zeroFactor_lt_one t htre)
  have ht0 : t ≠ 0 := by intro ht; simp only [ht, Complex.zero_re] at htre; linarith
  exact (mass_le_zeroFactor_iff_disk t ht0 hm).mp hb'

end RiemannResearch.RH.RamanujanZeroCertificates
