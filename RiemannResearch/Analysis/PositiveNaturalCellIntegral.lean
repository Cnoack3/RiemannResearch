import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Complete positive-ray integrals over natural cells

The right-closed intervals partition the open ray exactly. In particular the
initial cell remains in the complete sum; no limiting or tail hypothesis is
used for the nonnegative integral. The Bochner identity uses actual
integrability on the full ray.
-/

open MeasureTheory Set
open scoped ENNReal

namespace RiemannResearch.Analysis.PositiveNaturalCellIntegral

theorem iUnion_nat_cells (a : ℝ) :
    (⋃ n : ℕ, Ioc (a + (n : ℝ)) (a + (n : ℝ) + 1)) = Ioi a := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact lt_of_le_of_lt (by linarith) hn.1
  · intro hx
    have hx' : a < x := hx
    have hp : 0 < Nat.ceil (x - a) := Nat.ceil_pos.mpr (by linarith)
    let n := Nat.ceil (x - a) - 1
    have hn : n < Nat.ceil (x - a) := by dsimp [n]; omega
    have hn1 : n + 1 = Nat.ceil (x - a) := by dsimp [n]; omega
    have hlo : (n : ℝ) < x - a := Nat.lt_ceil.mp hn
    have hhi : x - a ≤ (n : ℝ) + 1 := by
      simpa only [← hn1, Nat.cast_add, Nat.cast_one] using Nat.le_ceil (x - a)
    exact mem_iUnion.mpr ⟨n, by constructor <;> linarith⟩

theorem pairwise_disjoint_nat_cells (a : ℝ) :
    Pairwise (fun n m : ℕ =>
      Disjoint (Ioc (a + (n : ℝ)) (a + (n : ℝ) + 1))
        (Ioc (a + (m : ℝ)) (a + (m : ℝ) + 1))) := by
  intro n m hnm
  apply disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · have hle : (n : ℝ) + 1 ≤ (m : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hlt)
    linarith [hx.2, hy.1]
  · have hle : (m : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hgt)
    linarith [hy.2, hx.1]

/-- Actual nonnegative integral on the complete ray, including its initial cell. -/
theorem lintegral_Ioi_eq_tsum_cells (a : ℝ) (f : ℝ → ℝ≥0∞) :
    (∫⁻ x in Ioi a, f x) =
      ∑' n : ℕ, ∫⁻ x in Ioc (a + (n : ℝ)) (a + (n : ℝ) + 1), f x := by
  rw [← iUnion_nat_cells a]
  exact lintegral_iUnion (fun _ => measurableSet_Ioc)
    (pairwise_disjoint_nat_cells a) f

/-- The first cell is explicit and every positive tail cell remains. -/
theorem lintegral_Ioi_eq_head_add_tsum_cells (a : ℝ) (f : ℝ → ℝ≥0∞) :
    (∫⁻ x in Ioi a, f x) = (∫⁻ x in Ioc a (a + 1), f x) +
      ∑' n : ℕ, ∫⁻ x in Ioc (a + 1 + (n : ℝ)) (a + 1 + (n : ℝ) + 1), f x := by
  have hsplit : Ioi a = Ioc a (a + 1) ∪ Ioi (a + 1) := by
    ext x
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro hx
      by_cases hx1 : x ≤ a + 1
      · exact Or.inl ⟨hx, hx1⟩
      · exact Or.inr (lt_of_not_ge hx1)
    · rintro (⟨hx, _⟩ | hx)
      · exact hx
      · linarith
  have hd : Disjoint (Ioc a (a + 1)) (Ioi (a + 1)) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact not_lt_of_ge hx.2 hy
  rw [hsplit, lintegral_union measurableSet_Ioi hd,
    lintegral_Ioi_eq_tsum_cells (a + 1) f]

/-- Actual Bochner cell integrals sum to the complete integral whenever it is
integrable. This assertion uses the full ray, not merely cell integrability. -/
theorem hasSum_integral_Ioi_cells {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (a : ℝ) {f : ℝ → E} (hf : IntegrableOn f (Ioi a)) :
    HasSum (fun n : ℕ =>
      ∫ x in Ioc (a + (n : ℝ)) (a + (n : ℝ) + 1), f x)
      (∫ x in Ioi a, f x) := by
  have h := hasSum_integral_iUnion (fun _ => measurableSet_Ioc)
    (pairwise_disjoint_nat_cells a)
    (by simpa only [iUnion_nat_cells a] using hf)
  simpa only [iUnion_nat_cells a] using h

end RiemannResearch.Analysis.PositiveNaturalCellIntegral
