import RiemannResearch.Analysis.ConreyBaluyotMollifiedBoundary
import RiemannResearch.RH.WeilExplicitFormula.RvM.ZetaGrowth
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open Complex Set
open scoped BigOperators
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- The exact finite polynomial has one uniformly bounded term for each
integer in its cutoff. This holds on the entire closed right half-plane. -/
theorem norm_nonstandardMollifier_le_cutoff
    {σ y ε C : ℝ} (hC : 0 ≤ C)
    (hcoef : ∀ n : ℕ, 0 < n → ‖mollifierCoefficient σ y n‖ ≤ C)
    {s : ℂ} (hs : 0 ≤ s.re) :
    ‖nonstandardMollifier σ y ε s‖ ≤ C * (⌊y ^ (1 + ε)⌋₊ + 1 : ℕ) := by
  let N := ⌊y ^ (1 + ε)⌋₊
  let S := Finset.Icc 1 N
  have hcard : S.card ≤ N + 1 := by
    apply (Finset.card_le_card ?_).trans
      (show (Finset.range (N + 1)).card ≤ N + 1 by simp)
    intro n hn
    exact Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hn).2; omega)
  have hterm (n : ℕ) (hn : n ∈ S) :
      ‖mollifierCoefficient σ y n / (n : ℂ) ^ s‖ ≤ C := by
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : 0 < n := by omega
    have hnℝ : (0 : ℝ) < n := by exact_mod_cast hn0
    have hp : 1 ≤ ‖(n : ℂ) ^ s‖ := by
      rw [Complex.norm_natCast_cpow_of_pos hn0]
      exact Real.one_le_rpow (by exact_mod_cast hn1) hs
    rw [norm_div]
    exact (div_le_self (norm_nonneg _) hp).trans (hcoef n hn0)
  change ‖∑ n ∈ S, mollifierCoefficient σ y n / (n : ℂ) ^ s‖ ≤ C * (N + 1 : ℕ)
  calc
    _ ≤ ∑ n ∈ S, ‖mollifierCoefficient σ y n / (n : ℂ) ^ s‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ S, C := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * C := by simp
    _ ≤ ((N + 1 : ℕ) : ℝ) * C :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hC
    _ = _ := by ring

/-- Uniform version of Baluyot (3.2.8), with the cutoff and all
constants chosen independently of y, sigma, s and the ordinate. -/
theorem exists_uniform_nonstandardMollifier_growth {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ η Y C : ℝ, 0 < η ∧ η < 1 / 4 ∧ 1 < Y ∧ 0 < C ∧
      ∀ y : ℝ, Y ≤ y → ∀ σ : ℝ, 1 / 2 + 1 / Real.log y ≤ σ →
        σ ≤ 1 / 2 + η → ∀ s : ℂ, 0 ≤ s.re →
          ‖nonstandardMollifier σ y ε s‖ ≤ C * y ^ (1 + ε) := by
  obtain ⟨η, Y, K, hη, hη', hY, _, hK, hcoeff⟩ :=
    exists_uniform_mollifier_coefficient_bounds
  let C := 8 * (K + 1)
  refine ⟨η, Y, C, hη, hη', hY, by dsimp [C]; positivity, ?_⟩
  intro y hy σ hσ hση s hs
  obtain ⟨_, _, _, hcoef, _⟩ := hcoeff y hy σ hσ hση
  have hy1 : 1 ≤ y := hY.le.trans hy
  have hp : 1 ≤ y ^ (1 + ε) := Real.one_le_rpow hy1 (by linarith)
  have hf : (⌊y ^ (1 + ε)⌋₊ : ℝ) ≤ y ^ (1 + ε) :=
    Nat.floor_le (by positivity)
  calc
    _ ≤ (4 * K) * ((⌊y ^ (1 + ε)⌋₊ : ℝ) + 1) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        norm_nonstandardMollifier_le_cutoff (by positivity : 0 ≤ 4 * K) hcoef hs
    _ ≤ C * y ^ (1 + ε) := by
      dsimp [C]
      nlinarith [mul_nonneg hK (sub_nonneg.mpr hf)]

/-- The same uniform constants combine with the existing zeta growth
estimate to control the actual product on every vertical strip to the
right of Re s = 1/4. -/
theorem exists_uniform_mollifiedZeta_growth {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ η Y C : ℝ, 0 < η ∧ η < 1 / 4 ∧ 1 < Y ∧ 0 < C ∧
      ∀ y : ℝ, Y ≤ y → ∀ σ : ℝ, 1 / 2 + 1 / Real.log y ≤ σ →
        σ ≤ 1 / 2 + η → ∀ s : ℂ, (1 / 4 : ℝ) ≤ s.re → 1 ≤ |s.im| →
          ‖mollifiedZeta σ y ε s‖ ≤ C * |s.im| * y ^ (1 + ε) := by
  obtain ⟨η, Y, C, hη, hη', hY, hC, hm⟩ := exists_uniform_nonstandardMollifier_growth hε
  refine ⟨η, Y, 13 / 2 * C, hη, hη', hY, by positivity, ?_⟩
  intro y hy σ hσ hση s hs ht
  have hz : ‖riemannZeta s‖ ≤ 13 / 2 * |s.im| := by
    have hz' := Zeta23.RvM.riemannZeta_linear_growth
      (δ := (1 / 4 : ℝ)) (by norm_num) hs ht
    norm_num at hz' ⊢
    exact hz'
  have hM := hm y hy σ hσ hση s (by linarith)
  unfold mollifiedZeta
  rw [norm_mul]
  calc
    _ ≤ (13 / 2 * |s.im|) * (C * y ^ (1 + ε)) :=
      mul_le_mul hz hM (norm_nonneg _) (by positivity)
    _ = _ := by ring

end RiemannResearch.Analysis.ConreyBaluyot
