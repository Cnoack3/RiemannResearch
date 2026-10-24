import RiemannResearch.Analysis.ContractiveCountBudget
import RiemannResearch.RH.RamanujanZeroLogBudget
import Mathlib.Tactic.FieldSimp

/-!
# Finite zero counts and certified exclusion disks from Ramanujan mass

Source: deductions from the exact Ramanujan product certificates, requested
24 October 2026. Counts concern distinct zeros, not their multiplicities.
The full threshold slack is recorded before the count estimate. No positive
packet mass is identified with the complete zero product.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

theorem zeroCharge_lower_of_window (z : ℂ) {δ R : ℝ}
    (hδ : 0 < δ) (hR : 0 < R) (hre : 1 / 2 + δ ≤ z.re)
    (hnorm : ‖z‖ ^ 2 ≤ R) : 2 * δ / R ≤ zeroCharge z := by
  have hz : z ≠ 0 := by intro h; simp [h] at hre; linarith
  have hn : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  unfold zeroCharge
  apply (div_le_div_iff₀ hR hn).mpr
  nlinarith

/-- The product certificate is exactly the exterior of an explicit disk. -/
theorem mass_le_zeroFactor_iff_disk (z : ℂ) (hz : z ≠ 0)
    {m : ℝ} (hm : m < 1) :
    m ≤ zeroFactor z ↔
      m / (1 - m) ^ 2 ≤ (z.re - 1 / (1 - m)) ^ 2 + z.im ^ 2 := by
  have hden : 0 < 1 - m := by linarith
  have hn : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hq := zeroCharge_eq_defect z hz
  unfold zeroCharge at hq
  have hpoly : m ≤ zeroFactor z ↔ 2 * z.re - 1 ≤ (1 - m) * ‖z‖ ^ 2 := by
    rw [← div_le_iff₀ hn]
    constructor <;> intro h <;> linarith
  rw [hpoly]
  have he : ((z.re - 1 / (1 - m)) ^ 2 + z.im ^ 2 - m / (1 - m) ^ 2) *
      (1 - m) ^ 2 = (1 - m) * ((1 - m) * ‖z‖ ^ 2 - (2 * z.re - 1)) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    field_simp
    <;> ring
  constructor <;> intro h
  · have hp : 0 ≤ (1 - m) * ((1 - m) * ‖z‖ ^ 2 - (2 * z.re - 1)) :=
      mul_nonneg hden.le (sub_nonneg.mpr h)
    have hs : 0 < (1 - m) ^ 2 := sq_pos_of_pos hden
    nlinarith
  · have hp : 0 ≤ ((z.re - 1 / (1 - m)) ^ 2 + z.im ^ 2 - m / (1 - m) ^ 2) *
        (1 - m) ^ 2 := mul_nonneg (sub_nonneg.mpr h) (sq_nonneg _)
    nlinarith

end RiemannResearch.RH.Pareto
namespace RiemannResearch.RH.RamanujanZeroCertificates
open Pareto Pareto.CoefficientStabilization RamanujanCanonicalOptimizer
open RiemannResearch.Analysis.ContractiveLogBudget
variable {ι : Type*} [Fintype ι]

theorem zero_count_limit_budget_exact (z : ι → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hz1 : ∀ i, z i ≠ 1)
    {η : ℝ} (hη : η < 1) :
    -Real.log (1 - limitEnergy) = (Fintype.card ι : ℝ) * (-Real.log (1 - η)) +
      (∑ i, Real.log ((1 - η) / zeroFactor (z i))) +
      Real.log (mellinZeroProduct z / (1 - limitEnergy)) := by
  have hz0 : ∀ i, z i ≠ 0 := by
    intro i h; have := hzre i; simp [h] at this; linarith
  simpa only [Finset.card_univ, mellinZeroProduct, zeroFactor] using
    finite_count_budget_exact Finset.univ (fun i => zeroFactor (z i))
      (fun i _ => zeroFactor_pos (z i) (hz0 i) (hz1 i)) packetLimitMass_pos
      (show 0 < 1 - η by linarith)

theorem zero_count_log_bound (z : ι → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0)
    {η : ℝ} (hη : η < 1) (hcharge : ∀ i, η ≤ zeroCharge (z i)) :
    (Fintype.card ι : ℝ) * (-Real.log (1 - η)) ≤ -Real.log (1 - limitEnergy) := by
  classical
  have hz0 : ∀ i, z i ≠ 0 := by
    intro i h; have := hzre i; simp [h] at this; linarith
  have hfactor : ∀ i ∈ Finset.univ, zeroFactor (z i) ≤ 1 - η := by
    intro i _
    have := hcharge i
    rw [zeroCharge_eq_defect _ (hz0 i)] at this
    linarith
  have hmass : 1 - limitEnergy ≤ mellinZeroProduct z := by
    linarith [zeroProduct_limitEnergy_lower_bound z hzre hinj hz1 hzero]
  simpa only [Finset.card_univ, mellinZeroProduct, zeroFactor] using
    finite_count_log_bound Finset.univ (fun i => zeroFactor (z i))
      (fun i _ => zeroFactor_pos (z i) (hz0 i) (hz1 i)) packetLimitMass_pos
      (show 0 < 1 - η by linarith) hfactor hmass

theorem zero_count_product_bound (z : ι → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0)
    {η : ℝ} (hcharge : ∀ i, η ≤ zeroCharge (z i)) :
    1 - limitEnergy ≤ (1 - η) ^ Fintype.card ι := by
  classical
  have hz0 : ∀ i, z i ≠ 0 := by
    intro i h; have := hzre i; simp [h] at this; linarith
  have hfactor : ∀ i ∈ Finset.univ, zeroFactor (z i) ≤ 1 - η := by
    intro i _
    have := hcharge i
    rw [zeroCharge_eq_defect _ (hz0 i)] at this
    linarith
  have hmass : 1 - limitEnergy ≤ mellinZeroProduct z := by
    linarith [zeroProduct_limitEnergy_lower_bound z hzre hinj hz1 hzero]
  simpa only [Finset.card_univ, mellinZeroProduct, zeroFactor] using
    finite_count_product_bound Finset.univ (fun i => zeroFactor (z i))
      (fun i _ => (zeroFactor_pos (z i) (hz0 i) (hz1 i)).le) hfactor hmass

theorem zero_window_log_count (z : ι → ℂ) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 2 * δ < R)
    (hre : ∀ i, 1 / 2 + δ ≤ (z i).re) (hnorm : ∀ i, ‖z i‖ ^ 2 ≤ R) :
    (Fintype.card ι : ℝ) * (-Real.log (1 - 2 * δ / R)) ≤
      -Real.log (1 - limitEnergy) := by
  have hR0 : 0 < R := by linarith
  exact zero_count_log_bound z (fun i => by linarith [hre i]) hinj hz1 hzero
    ((div_lt_one hR0).mpr hR)
    (fun i => zeroCharge_lower_of_window (z i) hδ hR0 (hre i) (hnorm i))

theorem zero_outside_packet_disk (z : ℂ) (hzre : (1 / 2 : ℝ) < z.re)
    (hz1 : z ≠ 1) (hzero : riemannZeta z = 0) (n : ℕ)
    (hm : packetMass n < 1) :
    packetMass n / (1 - packetMass n) ^ 2 ≤
      (z.re - 1 / (1 - packetMass n)) ^ 2 + z.im ^ 2 := by
  classical
  have hz0 : z ≠ 0 := by intro h; simp [h] at hzre; linarith
  apply (mass_le_zeroFactor_iff_disk z hz0 hm).mp
  have h := packetMass_le_zeroProduct (fun _ : Unit => z) (fun _ => hzre)
    (fun i j _ => Subsingleton.elim i j) (fun _ => hz1) (fun _ => hzero) n
  simpa [mellinZeroProduct, zeroFactor] using h

end RiemannResearch.RH.RamanujanZeroCertificates
