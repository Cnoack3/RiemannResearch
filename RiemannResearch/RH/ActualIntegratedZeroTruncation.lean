import RiemannResearch.RH.ActualIntegratedZeroSeries
import RiemannResearch.RH.IntegratedZeroScalarTail
import RiemannResearch.RH.WeilExplicitFormula.RvM.LocalCount
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# An explicit truncation rate for the actual integrated zeta-zero series

The only analytic zero-count input is the already proved
`Zeta23.RvM.zetaZeroConfig_local_count`. Actual zero multiplicities are kept.
This proves the size of the omitted zero series, not the arithmetic identity
identifying the complete series with the integrated Chebyshev error.

-/

noncomputable section
open Complex Set Filter Zeta23
open scoped BigOperators

namespace RiemannResearch.RH.ActualIntegratedZeroTruncation

open IntegratedZeroScalarTail ActualIntegratedZeroSeries

private theorem cast_natAbs_eq_abs (n : ℤ) :
    (n.natAbs : ℝ) = |(n : ℝ)| := by
  cases n with
  | ofNat a => simp
  | negSucc a =>
    simp only [Int.natAbs_negSucc, Nat.cast_succ, Int.cast_negSucc]
    rw [abs_of_nonpos (by
      have hnn : (0 : ℝ) ≤ a := Nat.cast_nonneg _
      linarith)]
    ring

private theorem eq_natAbs_or_neg (n : ℤ) :
    n = (n.natAbs : ℤ) ∨ n = -(n.natAbs : ℤ) := by
  cases n with
  | ofNat a => simp
  | negSucc a =>
    right
    change Int.negSucc a = -((a + 1 : ℕ) : ℤ)
    omega

private theorem finite_nat_tail_le (F : Finset ℕ) (K : ℕ) (hK : 5 ≤ K)
    (hF : ∀ n ∈ F, K ≤ n) :
    (∑ n ∈ F, Real.log ((n : ℝ) + 3) / (n : ℝ) ^ 2) ≤
      4 * Real.log ((K : ℝ) + 3) / K := by
  classical
  set N := F.sup id + 1
  have hsub : F ⊆ Finset.Ico K N := by
    intro n hn
    exact Finset.mem_Ico.mpr ⟨hF n hn,
      Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)⟩
  calc
    _ ≤ ∑ n ∈ Finset.Ico K N,
        Real.log ((n : ℝ) + 3) / (n : ℝ) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro n _ _
      exact div_nonneg (Real.log_nonneg (by
        have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
        linarith)) (sq_nonneg _)
    _ = ∑ j ∈ Finset.range (N - K),
        Real.log (((K + j : ℕ) : ℝ) + 3) / ((K + j : ℕ) : ℝ) ^ 2 :=
      Finset.sum_Ico_eq_sum_range _ _ _
    _ ≤ _ := IntegratedZeroScalarTail.finite_tail_le K (N - K) hK

/-- The two-sided integer-window majorant has a logarithmic reciprocal tail. -/
theorem finite_int_tail_le (F : Finset ℤ) (K : ℕ) (hK : 5 ≤ K)
    (hF : ∀ n ∈ F, K ≤ n.natAbs) :
    (∑ n ∈ F, Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) ≤
      8 * Real.log ((K : ℝ) + 3) / K := by
  classical
  set κ : ℤ → ℕ := Int.natAbs
  set g : ℕ → ℝ := fun j => Real.log ((j : ℝ) + 3) / (j : ℝ) ^ 2
  have hgnonneg : ∀ j, 0 ≤ g j := fun j =>
    div_nonneg (Real.log_nonneg (by
      have hnn : (0 : ℝ) ≤ j := Nat.cast_nonneg _
      linarith)) (sq_nonneg _)
  have hpt : ∀ n ∈ F,
      Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2) ≤ g (κ n) := by
    intro n hn
    have hn5 : (5 : ℝ) ≤ |(n : ℝ)| := by
      rw [← cast_natAbs_eq_abs]
      exact_mod_cast (hK.trans (hF n hn))
    dsimp [g, κ]
    rw [cast_natAbs_eq_abs, sq_abs]
    apply div_le_div_of_nonneg_left (Real.log_nonneg (by linarith))
      (by nlinarith [sq_abs (n : ℝ)]) (by linarith)
  have hfiber : ∀ j ∈ F.image κ,
      (∑ n ∈ F with κ n = j, g (κ n)) ≤ 2 * g j := by
    intro j _
    have hsub : F.filter (fun n => κ n = j) ⊆
        ({(j : ℤ), -(j : ℤ)} : Finset ℤ) := by
      intro n hn
      have heq : n.natAbs = j := (Finset.mem_filter.mp hn).2
      rcases eq_natAbs_or_neg n with h | h
      · simp only [heq] at h
        simp [h]
      · simp only [heq] at h
        simp [h]
    have hc : (F.filter (fun n => κ n = j)).card ≤ 2 := by
      apply (Finset.card_le_card hsub).trans
      simpa using (Finset.card_insert_le (j : ℤ) ({-(j : ℤ)} : Finset ℤ))
    calc
      _ = (F.filter (fun n => κ n = j)).card * g j := by
        calc
          _ = ∑ n ∈ F with κ n = j, g j := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [(Finset.mem_filter.mp hn).2]
          _ = _ := by simp
      _ ≤ 2 * g j := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (hgnonneg j)
  have himage : ∀ j ∈ F.image κ, K ≤ j := by
    intro j hj
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hj
    exact hF n hn
  calc
    _ ≤ ∑ n ∈ F, g (κ n) := Finset.sum_le_sum hpt
    _ = ∑ j ∈ F.image κ, ∑ n ∈ F with κ n = j, g (κ n) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to (g := κ) (t := F.image κ)
        (fun n hn => Finset.mem_image_of_mem κ hn) (fun n => g (κ n))
    _ ≤ ∑ j ∈ F.image κ, 2 * g j := Finset.sum_le_sum hfiber
    _ = 2 * ∑ j ∈ F.image κ, g j := by rw [Finset.mul_sum]
    _ ≤ 2 * (4 * Real.log ((K : ℝ) + 3) / K) :=
      mul_le_mul_of_nonneg_left (finite_nat_tail_le (F.image κ) K hK himage)
        (by norm_num)
    _ = _ := by ring

/-- A unit-window key stays outside the integer cutoff for a tail zero. -/
private theorem key_abs_ge (K : ℕ) (y : ℝ) (hy : (K : ℝ) < |y|) :
    K ≤ (WeilEF.key y).natAbs := by
  have hl := WeilEF.key_lt y
  have hu := WeilEF.le_key_add_one y
  have hya : |y| ≤ |((WeilEF.key y : ℤ) : ℝ)| + 1 := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le (((WeilEF.key y : ℤ) : ℝ))]
    · linarith [le_abs_self (((WeilEF.key y : ℤ) : ℝ))]
  by_contra h
  have hn : (WeilEF.key y).natAbs + 1 ≤ K := by omega
  have hreal : |((WeilEF.key y : ℤ) : ℝ)| + 1 ≤ K := by
    rw [← cast_natAbs_eq_abs]
    exact_mod_cast hn
  linarith

/-- Finite tail weight bound; its local-count assumptions are instantiated below. -/
theorem weight_partial_tail_le {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t + 1) : ℝ) ≤
      A₀ * Real.log (|t| + 3))
    (K : ℕ) (hK : 5 ≤ K) (s : Finset ActualZero)
    (hs : ∀ ρ ∈ s, (K : ℝ) < |(ρ : ℂ).im|) :
    (∑ ρ ∈ s, weight ρ) ≤ 32 * A₀ * Real.log ((K : ℝ) + 3) / K := by
  classical
  have hLC := Tail.LocalCount.ofWindowCount zetaZeroConfig hA₀ hloc
  set κ : ActualZero → ℤ := fun ρ => WeilEF.key (ρ : ℂ).im
  have hfiber : ∀ n ∈ s.image κ,
      (∑ ρ ∈ s with κ ρ = n, weight ρ) ≤
        4 * A₀ * (Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) := by
    intro n _
    have hwin := hLC.window n (s.filter fun ρ => κ ρ = n) (fun ρ hρ => by
      simp only [Finset.mem_filter] at hρ
      rw [← hρ.2]
      exact ⟨WeilEF.key_lt _, WeilEF.le_key_add_one _⟩)
    have hpt : ∀ ρ ∈ s.filter (fun ρ => κ ρ = n),
        weight ρ ≤ (4 / (1 + (n : ℝ) ^ 2)) * (zeroMult ρ : ℝ) := by
      intro ρ hρ
      simp only [Finset.mem_filter] at hρ
      have h1 : (n : ℝ) < (ρ : ℂ).im := by
        rw [← hρ.2]
        exact WeilEF.key_lt _
      have h2 : (ρ : ℂ).im ≤ (n : ℝ) + 1 := by
        rw [← hρ.2]
        exact WeilEF.le_key_add_one _
      have hge := WeilEF.one_add_sq_ge h1 h2
      have hnorm : 1 + (ρ : ℂ).im ^ 2 ≤
          1 + Complex.normSq (gammaOf ρ) := by
        rw [Complex.normSq_apply, WeilEF.gammaOf_re]
        nlinarith [sq_nonneg ((gammaOf (ρ : ℂ)).im)]
      have hinv : 1 / (1 + Complex.normSq (gammaOf ρ)) ≤
          4 / (1 + (n : ℝ) ^ 2) := by
        rw [div_le_div_iff₀
          (by linarith [Complex.normSq_nonneg (gammaOf (ρ : ℂ))]) (by positivity)]
        nlinarith
      calc
        weight ρ = (zeroMult ρ : ℝ) * (1 / (1 + Complex.normSq (gammaOf ρ))) :=
          by unfold weight; ring
        _ ≤ (zeroMult ρ : ℝ) * (4 / (1 + (n : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg _)
        _ = _ := by ring
    calc
      _ ≤ ∑ ρ ∈ s with κ ρ = n,
          (4 / (1 + (n : ℝ) ^ 2)) * (zeroMult ρ : ℝ) :=
        Finset.sum_le_sum hpt
      _ = (4 / (1 + (n : ℝ) ^ 2)) *
          ∑ ρ ∈ s with κ ρ = n, (zeroMult ρ : ℝ) := by rw [Finset.mul_sum]
      _ ≤ (4 / (1 + (n : ℝ) ^ 2)) *
          (A₀ * Real.log (|(n : ℝ)| + 3)) :=
        mul_le_mul_of_nonneg_left hwin (by positivity)
      _ = _ := by ring
  have hkeys : ∀ n ∈ s.image κ, K ≤ n.natAbs := by
    intro n hn
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hn
    exact key_abs_ge K (ρ : ℂ).im (hs ρ hρ)
  calc
    _ = ∑ n ∈ s.image κ, ∑ ρ ∈ s with κ ρ = n, weight ρ := by
      symm
      exact Finset.sum_fiberwise_of_maps_to (g := κ) (t := s.image κ)
        (fun ρ hρ => Finset.mem_image_of_mem κ hρ) weight
    _ ≤ ∑ n ∈ s.image κ,
        4 * A₀ * (Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) :=
      Finset.sum_le_sum hfiber
    _ = 4 * A₀ * ∑ n ∈ s.image κ,
        Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ 4 * A₀ * (8 * Real.log ((K : ℝ) + 3) / K) :=
      mul_le_mul_of_nonneg_left (finite_int_tail_le (s.image κ) K hK hkeys)
        (by linarith)
    _ = _ := by ring

/-- All actual zeros above the symmetric ordinate cutoff. -/
abbrev TailZero (K : ℕ) := {ρ : ActualZero // (K : ℝ) < |(ρ : ℂ).im|}

/-- Actual unconditional reciprocal-square tail bound, retaining multiplicities. -/
theorem actual_weight_tail_bound :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ K : ℕ, 5 ≤ K →
      Summable (fun ρ : TailZero K => weight ρ.1) ∧
      (∑' ρ : TailZero K, weight ρ.1) ≤
        32 * A₀ * Real.log ((K : ℝ) + 3) / K := by
  classical
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  refine ⟨A₀, hA₀, fun K hK => ?_⟩
  have hpart : ∀ u : Finset (TailZero K),
      (∑ ρ ∈ u, weight ρ.1) ≤
        32 * A₀ * Real.log ((K : ℝ) + 3) / K := by
    intro u
    have h := weight_partial_tail_le hA₀ hloc K hK
      (u.map (Function.Embedding.subtype _)) (by
        intro ρ hρ
        obtain ⟨η, _, rfl⟩ := Finset.mem_map.mp hρ
        exact η.2)
    simpa only [Finset.sum_map, Function.Embedding.coe_subtype] using h
  have hnonneg : ∀ ρ : TailZero K, 0 ≤ weight ρ.1 := by
    intro ρ
    unfold weight
    exact div_nonneg (Nat.cast_nonneg _)
      (by linarith [Complex.normSq_nonneg (gammaOf ((ρ.1 : ActualZero) : ℂ))])
  exact ⟨summable_of_sum_le hnonneg hpart, Real.tsum_le_of_sum_le hnonneg hpart⟩

/-- Explicit unconditional size of the actual omitted integrated zero series.
No analytic estimate appears as a caller hypothesis. The constant is uniform
in x and K; its existence comes from the proved actual local zero count. -/
theorem actual_integrated_zero_truncation_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ), 5 ≤ K → ∀ (x : ℝ), 1 ≤ x →
      ‖∑' ρ : TailZero K, term x ρ.1‖ ≤
        C * x * Real.log ((K : ℝ) + 3) / K := by
  obtain ⟨A₀, hA₀, htail⟩ := actual_weight_tail_bound
  refine ⟨192 * A₀, by linarith, fun K hK x hx => ?_⟩
  have hw := htail K hK
  have hpoint : ∀ ρ : TailZero K, ‖term x ρ.1‖ ≤ (6 * x) * weight ρ.1 := by
    intro ρ
    apply ActualIntegratedZeroSeries.term_norm_le x hx ρ.1
    have hKr : (5 : ℝ) ≤ K := by exact_mod_cast hK
    linarith [ρ.2]
  have hnorm : ‖∑' ρ : TailZero K, term x ρ.1‖ ≤
      ∑' ρ : TailZero K, (6 * x) * weight ρ.1 :=
    tsum_of_norm_bounded (hw.1.mul_left (6 * x)).hasSum hpoint
  calc
    _ ≤ ∑' ρ : TailZero K, (6 * x) * weight ρ.1 := hnorm
    _ = (6 * x) * ∑' ρ : TailZero K, weight ρ.1 := tsum_mul_left
    _ ≤ (6 * x) * (32 * A₀ * Real.log ((K : ℝ) + 3) / K) :=
      mul_le_mul_of_nonneg_left hw.2 (by linarith)
    _ = _ := by ring

/-- The logarithm can be written exactly as log K at the stated cutoff. -/
theorem actual_integrated_zero_tail_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ), 5 ≤ K → ∀ (x : ℝ), 1 ≤ x →
      ‖∑' ρ : TailZero K, term x ρ.1‖ ≤ C * x * Real.log (K : ℝ) / K := by
  obtain ⟨C, hC, hbound⟩ := actual_integrated_zero_truncation_bound
  refine ⟨2 * C, by positivity, fun K hK x hx => ?_⟩
  have hKr : (5 : ℝ) ≤ K := by exact_mod_cast hK
  have hlog : Real.log ((K : ℝ) + 3) ≤ 2 * Real.log (K : ℝ) := by
    have h := Real.log_le_log (by linarith : 0 < (K : ℝ) + 3)
      (by nlinarith : (K : ℝ) + 3 ≤ (K : ℝ) ^ 2)
    rw [Real.log_pow] at h
    norm_num at h
    exact h
  calc
    _ ≤ C * x * Real.log ((K : ℝ) + 3) / K := hbound K hK x hx
    _ ≤ C * x * (2 * Real.log (K : ℝ)) / K := by gcongr
    _ = _ := by ring

/-- The actual omitted zero series has the requested O(log K / K) height rate.
Its constant depends only linearly on x; no RH hypothesis is present. -/
theorem actual_integrated_zero_tail_isBigO (x : ℝ) (hx : 1 ≤ x) :
    (fun K : ℕ => ∑' ρ : TailZero K, term x ρ.1) =O[atTop]
      (fun K : ℕ => Real.log (K : ℝ) / (K : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := actual_integrated_zero_tail_log_bound
  apply Asymptotics.IsBigO.of_bound (C * x)
  filter_upwards [eventually_ge_atTop 5] with K hK
  have hKr : (5 : ℝ) ≤ K := by exact_mod_cast hK
  have hnn : 0 ≤ Real.log (K : ℝ) / (K : ℝ) :=
    div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
  have h := hbound K hK x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnn, mul_div_assoc] using h

end RiemannResearch.RH.ActualIntegratedZeroTruncation
