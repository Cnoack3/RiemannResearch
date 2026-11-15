import RiemannResearch.Analysis.ConreyBaluyotMollifierGrowth
import RiemannResearch.Analysis.ConreyBaluyotMollifierTruncation

noncomputable section
open Complex Set
open scoped BigOperators
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- Global coefficient control and tail decay imply one geometric majorant. -/
theorem norm_mollifierCoefficient_le_global_geometric
    {σ y K : ℝ} (hy : 1 ≤ y) (hK : 0 ≤ K)
    (hglobal : ∀ n : ℕ, 0 < n → ‖mollifierCoefficient σ y n‖ ≤ 4 * K)
    (htail : ∀ n : ℕ, y ≤ n →
      ‖mollifierCoefficient σ y n‖ ≤ 288 * Real.exp (-(n : ℝ) / (2 * y)))
    {n : ℕ} (hn : 0 < n) :
    ‖mollifierCoefficient σ y n‖ ≤
      (288 + 8 * K) * Real.exp (-(n : ℝ) / (2 * y)) := by
  have hy0 : 0 < y := by linarith
  by_cases hny : y ≤ (n : ℝ)
  · calc
      _ ≤ 288 * Real.exp (-(n : ℝ) / (2 * y)) := htail n hny
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        nlinarith
  · have hangle : -(1 / 2 : ℝ) ≤ -(n : ℝ) / (2 * y) := by
      apply (le_div_iff₀ (show (0 : ℝ) < 2 * y by positivity)).mpr
      have : (n : ℝ) ≤ y := le_of_not_ge hny
      nlinarith
    have hhalf : (1 / 2 : ℝ) ≤ Real.exp (-(n : ℝ) / (2 * y)) := by
      have hbase : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
        linarith [Real.add_one_le_exp (-(1 / 2 : ℝ))]
      exact hbase.trans (Real.exp_le_exp.mpr hangle)
    calc
      _ ≤ 4 * K := hglobal n hn
      _ ≤ _ := by
        have hp := mul_nonneg hK (sub_nonneg.mpr hhalf)
        have he := (Real.exp_pos (-(n : ℝ) / (2 * y))).le
        nlinarith

/-- A uniform linear bound on the actual polynomial, for every cutoff exponent. -/
theorem exists_uniform_nonstandardMollifier_linear_growth :
    ∃ η Y C : ℝ, 0 < η ∧ η < 1 / 4 ∧ 1 < Y ∧ 0 < C ∧
      ∀ y : ℝ, Y ≤ y → ∀ σ : ℝ, 1 / 2 + 1 / Real.log y ≤ σ →
        σ ≤ 1 / 2 + η → ∀ (ε : ℝ) (s : ℂ), 0 ≤ s.re →
          ‖nonstandardMollifier σ y ε s‖ ≤ C * y := by
  obtain ⟨η, Y, K, hη, hη', hY, _, hK, hcoeff⟩ :=
    exists_uniform_mollifier_coefficient_bounds
  let A := 288 + 8 * K
  let C := 3 * A
  refine ⟨η, Y, C, hη, hη', hY, by dsimp [C, A]; positivity, ?_⟩
  intro y hy σ hσ hση ε s hs
  obtain ⟨_, _, _, hcoef, htail⟩ := hcoeff y hy σ hσ hση
  have hy1 : 1 ≤ y := hY.le.trans hy
  have hy0 : 0 < y := by linarith
  let q := Real.exp (-1 / (2 * y))
  let S := Finset.Icc 1 ⌊y ^ (1 + ε)⌋₊
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hqpos : 0 < q := Real.exp_pos _
  have hqlt : q < 1 := by
    apply Real.exp_lt_one_iff.mpr
    exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  have hq : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_pos hqpos] using hqlt
  have hgeom : HasSum (fun k : ℕ => A * q ^ k) (A / (1 - q)) := by
    simpa only [div_eq_mul_inv] using (hasSum_geometric_of_norm_lt_one hq).mul_left A
  have hterm (n : ℕ) (hn : n ∈ S) :
      ‖mollifierCoefficient σ y n / (n : ℂ) ^ s‖ ≤ A * q ^ n := by
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : 0 < n := by omega
    have hp : 1 ≤ ‖(n : ℂ) ^ s‖ := by
      rw [Complex.norm_natCast_cpow_of_pos hn0]
      exact Real.one_le_rpow (by exact_mod_cast hn1) hs
    have hbound := norm_mollifierCoefficient_le_global_geometric hy1 hK hcoef htail hn0
    have hexp : Real.exp (-(n : ℝ) / (2 * y)) = q ^ n := by
      dsimp [q]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hexp] at hbound
    have hd : ‖mollifierCoefficient σ y n / (n : ℂ) ^ s‖ ≤
        ‖mollifierCoefficient σ y n‖ := by
      rw [norm_div]
      exact div_le_self (norm_nonneg _) hp
    exact hd.trans hbound
  have hsum : (∑ n ∈ S, A * q ^ n) ≤ A / (1 - q) := by
    calc
      _ ≤ ∑' n : ℕ, A * q ^ n :=
        Summable.sum_le_tsum S (fun n hn => by positivity) hgeom.summable
      _ = _ := hgeom.tsum_eq
  have hden : (1 - q)⁻¹ ≤ 3 * y := geometric_denominator_inv_le hy1
  change ‖∑ n ∈ S, mollifierCoefficient σ y n / (n : ℂ) ^ s‖ ≤ C * y
  calc
    _ ≤ ∑ n ∈ S, ‖mollifierCoefficient σ y n / (n : ℂ) ^ s‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, A * q ^ n := Finset.sum_le_sum hterm
    _ ≤ A / (1 - q) := hsum
    _ ≤ A * (3 * y) := by rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hden hA
    _ = _ := by dsimp [C]; ring

/-- The linear mollifier bound yields a linear-in-y bound for the actual product. -/
theorem exists_uniform_mollifiedZeta_linear_growth :
    ∃ η Y C : ℝ, 0 < η ∧ η < 1 / 4 ∧ 1 < Y ∧ 0 < C ∧
      ∀ y : ℝ, Y ≤ y → ∀ σ : ℝ, 1 / 2 + 1 / Real.log y ≤ σ →
        σ ≤ 1 / 2 + η → ∀ (ε : ℝ) (s : ℂ), (1 / 4 : ℝ) ≤ s.re →
          1 ≤ |s.im| → ‖mollifiedZeta σ y ε s‖ ≤ C * |s.im| * y := by
  obtain ⟨η, Y, C, hη, hη', hY, hC, hm⟩ := exists_uniform_nonstandardMollifier_linear_growth
  refine ⟨η, Y, 13 / 2 * C, hη, hη', hY, by positivity, ?_⟩
  intro y hy σ hσ hση ε s hs ht
  have hz : ‖riemannZeta s‖ ≤ 13 / 2 * |s.im| := by
    have hz' := Zeta23.RvM.riemannZeta_linear_growth
      (δ := (1 / 4 : ℝ)) (by norm_num) hs ht
    norm_num at hz' ⊢
    exact hz'
  have hM := hm y hy σ hσ hση ε s (by linarith)
  unfold mollifiedZeta
  rw [norm_mul]
  calc
    _ ≤ (13 / 2 * |s.im|) * (C * y) :=
      mul_le_mul hz hM (norm_nonneg _) (by positivity)
    _ = _ := by ring

end RiemannResearch.Analysis.ConreyBaluyot
