/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QDivisorDPP
import RiemannResearch.Analysis.ProjectionDPPKernel
import RiemannResearch.Probability.DeterminantalIndependentLimit
import RiemannResearch.RH.QDivisorDPPOverlap
import RiemannResearch.RH.QDivisorDPPWindows
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
/-!
# Independent moving windows and the unit-lattice sine obstruction

Source: user-provided moving-window argument, Section 7 of
https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/QDPPMovingWindowsResearch20261014.md
supports the statements. The global overlap provider is proved separately.
The projection rank may be any sequence. Finite configuration limits require
only convergence of their marginals; compactness supplies subsequences.
The continuum consumer retains an explicit vanishing gcd/scale budget.
No legal-residue approximation or zeta-identification result is claimed.
-/

set_option autoImplicit false
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology
namespace RiemannResearch.RH.QDivisorDPP
open ZetaTwoProbability ZetaTwoHilbert
theorem gcd_fixed_offsets_le (x i j : ℕ) (hij : i < j) :
    Nat.gcd (x + i + 1) (x + j + 1) ≤ j - i := by
  have hd := Nat.dvd_sub (Nat.gcd_dvd_right (x + i + 1) (x + j + 1))
    (Nat.gcd_dvd_left (x + i + 1) (x + j + 1))
  have he : x + j + 1 - (x + i + 1) = j - i := by omega
  rw [he] at hd
  exact Nat.le_of_dvd (Nat.sub_pos_of_lt hij) hd

theorem basisKernel_fixed_offsets_abs_le (N x i j : ℕ) (hij : i < j) :
    |basisKernel N (x + i) (x + j)| ≤ 2 * ((j - i : ℕ) : ℝ) / ((x + 1 : ℕ) : ℝ) := by
  let g : ℝ := Nat.gcd (x + i + 1) (x + j + 1)
  let d : ℝ := (j - i : ℕ)
  let t : ℝ := (x + 1 : ℕ)
  have hg : g ≤ d := by dsimp [g, d]; exact_mod_cast gcd_fixed_offsets_le x i j hij
  have hg0 : 0 ≤ g := Nat.cast_nonneg _
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have ht : 0 < t := by dsimp [t]; positivity
  have hn : t ≤ ((x + i + 1 : ℕ) : ℝ) := by dsimp [t]; exact_mod_cast (by omega : x + 1 ≤ x + i + 1)
  have hm : t ≤ ((x + j + 1 : ℕ) : ℝ) := by dsimp [t]; exact_mod_cast (by omega : x + 1 ≤ x + j + 1)
  have hprod : t ^ 2 ≤ ((x + i + 1 : ℕ) : ℝ) * ((x + j + 1 : ℕ) : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) (sub_nonneg.mpr hm)]
  have hs : basisKernel N (x + i) (x + j) ^ 2 ≤ (2 * d / t) ^ 2 := by
    calc
      _ ≤ 4 * g ^ 2 / (((x + i + 1 : ℕ) : ℝ) * ((x + j + 1 : ℕ) : ℝ)) :=
        basisKernel_sq_le_gcd N (x + i) (x + j)
      _ ≤ 4 * d ^ 2 / (((x + i + 1 : ℕ) : ℝ) * ((x + j + 1 : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hg0 hd0).mpr hg) (by norm_num))
          (by positivity)
      _ ≤ 4 * d ^ 2 / t ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos ht) hprod
      _ = _ := by ring
  have hb : 0 ≤ 2 * d / t := by positivity
  change |basisKernel N (x + i) (x + j)| ≤ 2 * d / t
  nlinarith [sq_abs (basisKernel N (x + i) (x + j)), abs_nonneg (basisKernel N (x + i) (x + j))]

theorem basisKernel_fixed_offsets_tendsto_lt (rank x : ℕ → ℕ)
    (hx : Tendsto x atTop atTop) (i j : ℕ) (hij : i < j) :
    Tendsto (fun N => basisKernel (rank N) (x N + i) (x N + j)) atTop (𝓝 0) := by
  have hb : Tendsto (fun N => 2 * ((j - i : ℕ) : ℝ) / ((x N + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
    have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hx
    simpa [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_assoc] using
      ht.const_mul (2 * ((j - i : ℕ) : ℝ))
  have h := squeeze_zero (fun N => abs_nonneg (basisKernel (rank N) (x N + i) (x N + j)))
    (fun N => basisKernel_fixed_offsets_abs_le (rank N) (x N) i j hij) hb
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa [Real.norm_eq_abs] using h)

theorem basisKernel_fixed_offsets_tendsto (rank x : ℕ → ℕ)
    (hx : Tendsto x atTop atTop) (i j : ℕ) (hij : i ≠ j) :
    Tendsto (fun N => basisKernel (rank N) (x N + i) (x N + j)) atTop (𝓝 0) := by
  rcases lt_trichotomy i j with h | h | h
  · exact basisKernel_fixed_offsets_tendsto_lt rank x hx i j h
  · exact (hij h).elim
  · have ht := basisKernel_fixed_offsets_tendsto_lt rank x hx j i h
    have he : (fun N => basisKernel (rank N) (x N + i) (x N + j)) =
        (fun N => basisKernel (rank N) (x N + j) (x N + i)) :=
      funext (fun N => basisKernel_symm _ _ _)
    rw [he]
    exact ht

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem basisLaw_window_configuration (N : ℕ) (e : ι ↪ ℕ) (S : Finset ι) :
    (basisLaw N).real {ω | ∀ i, ω (e i) = decide (i ∈ S)} =
      RiemannResearch.Probability.DPP.exactWeight
        (Matrix.of (fun i j : ι => basisKernel N (e i) (e j))) S := by
  classical
  have hK : (Matrix.of (fun i j : ι => basisKernel N (e i) (e j))).PosSemidef :=
    RiemannResearch.Analysis.ProjectionDPP.principal_posSemidef (basisSpace N) countingBasis e
  have hI : (1 - Matrix.of (fun i j : ι => basisKernel N (e i) (e j))).PosSemidef := by
    apply RiemannResearch.Analysis.ProjectionDPP.identity_sub_principal_posSemidef
      (basisSpace N) countingBasis e
    intro i j
    simp only [countingBasis_inner, e.injective.eq_iff]
  have h := (basisLaw_isDPP N).finite_configuration e
    (fun T => RiemannResearch.Probability.DPP.exactWeight_nonneg _ hK hI T) S
  have hbool (b : Bool) (hb : Decidable (b = true)) :
      @decide (b = true) hb = b := by cases b <;> simp
  simpa only [Set.mem_ofPred_eq, hbool] using h

theorem basisLaw_fixed_offsets_configuration_tendsto (rank x : ℕ → ℕ)
    (hx : Tendsto x atTop atTop) (offset : ι ↪ ℕ) (ρ : ι → ℝ)
    (hdiag : ∀ i, Tendsto (fun N => basisKernel (rank N)
      (x N + offset i) (x N + offset i)) atTop (𝓝 (ρ i))) (S : Finset ι) :
    Tendsto (fun N => (basisLaw (rank N)).real
      {ω | ∀ i, ω (x N + offset i) = decide (i ∈ S)}) atTop
      (𝓝 (∏ i, if i ∈ S then ρ i else 1-ρ i)) := by
  let e : ℕ → (ι ↪ ℕ) := fun N =>
    ⟨fun i => x N + offset i, fun i j h => offset.injective (Nat.add_left_cancel h)⟩
  have hK : ∀ i j, Tendsto (fun N => basisKernel (rank N)
      (x N + offset i) (x N + offset j)) atTop (𝓝 (if i = j then ρ i else 0)) := by
    intro i j
    by_cases hij : i = j
    · subst j
      simpa using hdiag i
    · simpa [hij] using basisKernel_fixed_offsets_tendsto rank x hx
        (offset i) (offset j) (fun he => hij (offset.injective he))
  have h := RiemannResearch.Probability.DPP.exactWeight_tendsto_of_diagonal
    (fun N => Matrix.of (fun i j => basisKernel (rank N)
      (x N + offset i) (x N + offset j))) ρ hK S
  have he (N : ℕ) : RiemannResearch.Probability.DPP.exactWeight
      (Matrix.of (fun i j => basisKernel (rank N) (x N + offset i) (x N + offset j))) S =
        (basisLaw (rank N)).real {ω | ∀ i, ω (x N + offset i) = decide (i ∈ S)} :=
    (basisLaw_window_configuration (rank N) (e N) S).symm
  simpa only [he] using h

theorem basisLaw_fixed_offsets_bernoulli_subsequence (rank x : ℕ → ℕ)
    (hx : Tendsto x atTop atTop) (offset : ι ↪ ℕ) :
    ∃ ρ : ι → ℝ, (∀ i, ρ i ∈ Set.Icc (0 : ℝ) 1) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ S : Finset ι,
        Tendsto (fun N => (basisLaw (rank (φ N))).real
          {ω | ∀ i, ω (x (φ N) + offset i) = decide (i ∈ S)}) atTop
          (𝓝 (∏ i, if i ∈ S then ρ i else 1-ρ i)) := by
  obtain ⟨ρ, hρ, φ, hφ, hd⟩ :=
    RiemannResearch.Probability.DPP.bounded_marginals_subsequence
      (fun N i => basisKernel (rank N) (x N + offset i) (x N + offset i))
      (fun N i => (basisLaw_isDPP (rank N)).diagonal_bounds (x N + offset i))
  refine ⟨ρ, hρ, φ, hφ, ?_⟩
  intro S
  exact basisLaw_fixed_offsets_configuration_tendsto
    (fun N => rank (φ N)) (fun N => x (φ N)) (hx.comp hφ.tendsto_atTop) offset ρ hd S

theorem basisLaw_fixed_offsets_two_point_tendsto (rank x : ℕ → ℕ)
    (hx : Tendsto x atTop atTop) (i j : ℕ) (hij : i ≠ j) (ρ σ : ℝ)
    (hi : Tendsto (fun N => basisKernel (rank N) (x N + i) (x N + i)) atTop (𝓝 ρ))
    (hj : Tendsto (fun N => basisKernel (rank N) (x N + j) (x N + j)) atTop (𝓝 σ)) :
    Tendsto (fun N => (basisLaw (rank N)).real
      {ω | ω (x N + i) = true ∧ ω (x N + j) = true}) atTop (𝓝 (ρ * σ)) := by
  have he (N : ℕ) : (basisLaw (rank N)).real
      {ω | ω (x N + i) = true ∧ ω (x N + j) = true} =
        basisKernel (rank N) (x N + i) (x N + i) *
          basisKernel (rank N) (x N + j) (x N + j) -
            basisKernel (rank N) (x N + i) (x N + j) ^ 2 :=
    basisLaw_two_point _ _ _ (fun h => hij (Nat.add_left_cancel h))
  have h := (hi.mul hj).sub ((basisKernel_fixed_offsets_tendsto rank x hx i j hij).pow 2)
  simpa only [← he, zero_pow (by norm_num : 2 ≠ 0), sub_zero] using h

theorem basisLaw_not_unit_lattice_sine_limit (rank x : ℕ → ℕ)
    (hx : Tendsto x atTop atTop) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (h0 : Tendsto (fun N => basisKernel (rank N) (x N) (x N)) atTop (𝓝 ρ))
    (h1 : Tendsto (fun N => basisKernel (rank N) (x N + 1) (x N + 1)) atTop (𝓝 ρ)) :
    ¬Tendsto (fun N => (basisLaw (rank N)).real
      {ω | ω (x N) = true ∧ ω (x N + 1) = true}) atTop
      (𝓝 (ρ ^ 2 - (Real.sin (Real.pi * ρ) / Real.pi) ^ 2)) := by
  have h := basisLaw_fixed_offsets_two_point_tendsto rank x hx 0 1
    (by norm_num) ρ ρ (by simpa using h0) h1
  simp only [add_zero, ← pow_two] at h
  intro hbad
  have he := tendsto_nhds_unique h hbad
  have hs : 0 < Real.sin (Real.pi * ρ) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hρ0)
      (by nlinarith [Real.pi_pos])
  have hd : 0 < Real.sin (Real.pi * ρ) / Real.pi := div_pos hs Real.pi_pos
  nlinarith [sq_pos_of_pos hd]


theorem basisKernel_scaled_tendsto_zero_of_gcd_budget (rank i j : ℕ → ℕ)
    (a : ℕ → ℝ)
    (hb : Tendsto (fun N => 4 * (a N) ^ 2 * (Nat.gcd (i N + 1) (j N + 1) : ℝ) ^ 2 /
      (((i N + 1 : ℕ) : ℝ) * ((j N + 1 : ℕ) : ℝ))) atTop (𝓝 0)) :
    Tendsto (fun N => a N * basisKernel (rank N) (i N) (j N)) atTop (𝓝 0) := by
  have hs : Tendsto (fun N => (a N * basisKernel (rank N) (i N) (j N)) ^ 2)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun N => sq_nonneg _) _ hb
    intro N
    calc
      _ = (a N) ^ 2 * basisKernel (rank N) (i N) (j N) ^ 2 := mul_pow _ _ _
      _ ≤ (a N) ^ 2 * (4 * (Nat.gcd (i N + 1) (j N + 1) : ℝ) ^ 2 /
          (((i N + 1 : ℕ) : ℝ) * ((j N + 1 : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left (basisKernel_sq_le_gcd _ _ _) (sq_nonneg _)
      _ = _ := by ring
  have ha := (Real.continuous_sqrt.tendsto 0).comp hs
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa [Function.comp_def, Real.norm_eq_abs, Real.sqrt_sq_eq_abs] using ha

end RiemannResearch.RH.QDivisorDPP
