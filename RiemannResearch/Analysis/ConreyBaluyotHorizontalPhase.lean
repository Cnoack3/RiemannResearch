/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotHorizontalRealZeros
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# Conditional horizontal phase displacement

For a continuous real phase, each crossed odd multiple of pi/2 gives a
distinct real-part zero. The proved real-zero count therefore bounds the
phase displacement from the right-hand endpoint, uniformly on the actual
mollifier strip. A continuous polar representation is an explicit premise;
this file does not establish its existence or the boundary-limit passage.
-/

noncomputable section
open Complex Set
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- A continuous phase cannot move by more than pi per crossing, up to two
end intervals. Every zero of cosine must lie in the supplied finite cover. -/
theorem continuous_phase_oscillation_le_of_crossing_cover
    (φ : ℝ → ℝ) (A B : ℝ) (S : Finset ℝ)
    (hAB : A ≤ B) (hφ : ContinuousOn φ (Set.Icc A B))
    (hcover : ∀ x ∈ Set.Icc A B, Real.cos (φ x) = 0 → x ∈ S) :
    |φ B - φ A| ≤ ((S.card : ℝ) + 2) * Real.pi := by
  classical
  by_contra hn
  have hlarge : ((S.card : ℝ) + 2) * Real.pi < |φ B - φ A| := lt_of_not_ge hn
  let low := min (φ A) (φ B)
  let high := max (φ A) (φ B)
  let n := S.card
  have hgap : ((n : ℝ) + 2) * Real.pi < high - low := by
    dsimp [n, high, low]
    rw [max_sub_min_eq_abs]
    exact hlarge
  let k₀ : ℤ := ⌊low / Real.pi⌋
  let level : ℕ → ℝ := fun k =>
    (2 * ((k₀ : ℝ) + (k : ℝ) + 1) + 1) * Real.pi / 2
  have hfl : (k₀ : ℝ) ≤ low / Real.pi := Int.floor_le _
  have hfu : low / Real.pi < (k₀ : ℝ) + 1 := Int.lt_floor_add_one _
  have hmul : low < ((k₀ : ℝ) + 1) * Real.pi :=
    (div_lt_iff₀ Real.pi_pos).mp hfu
  have hmul' : (k₀ : ℝ) * Real.pi ≤ low :=
    (le_div_iff₀ Real.pi_pos).mp hfl
  have hcont : ContinuousOn φ (Set.uIcc A B) := by
    simpa only [Set.uIcc_of_le hAB] using hφ
  have htarget : ∀ k : ℕ, k < n + 1 →
      ∃ x ∈ Set.Icc A B, φ x = level k := by
    intro k hk
    have hkN : (k : ℝ) ≤ n := by exact_mod_cast (Nat.lt_succ_iff.mp hk)
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hlow : low ≤ level k := by
      dsimp [level]
      nlinarith [mul_nonneg hk0 Real.pi_pos.le]
    have hhigh : level k ≤ high := by
      dsimp [level]
      nlinarith [mul_nonneg (sub_nonneg.mpr hkN) Real.pi_pos.le]
    have hv : level k ∈ Set.uIcc (φ A) (φ B) := by
      exact ⟨hlow, hhigh⟩
    obtain ⟨x, hx, he⟩ := intermediate_value_uIcc hcont hv
    exact ⟨x, by simpa only [Set.uIcc_of_le hAB] using hx, he⟩
  choose! pick hpick using htarget
  have hmap : Set.MapsTo pick (Finset.range (n + 1) : Set ℕ) (S : Set ℝ) := by
    intro k hk
    have hk' : k < n + 1 := Finset.mem_range.mp hk
    apply hcover (pick k) (hpick k hk').1
    rw [(hpick k hk').2]
    apply Real.cos_eq_zero_iff.mpr
    refine ⟨k₀ + (k : ℤ) + 1, ?_⟩
    dsimp [level]
    push_cast
    ring
  have hinj : Set.InjOn pick (Finset.range (n + 1) : Set ℕ) := by
    intro i hi j hj heq
    have hi' : i < n + 1 := Finset.mem_range.mp hi
    have hj' : j < n + 1 := Finset.mem_range.mp hj
    have hlevel : level i = level j := by
      calc
        _ = φ (pick i) := (hpick i hi').2.symm
        _ = φ (pick j) := congrArg φ heq
        _ = _ := (hpick j hj').2
    have hprod : ((i : ℝ) - (j : ℝ)) * Real.pi = 0 := by
      dsimp [level] at hlevel
      nlinarith
    have hcast : (i : ℝ) = j := sub_eq_zero.mp
      ((mul_eq_zero.mp hprod).resolve_right (ne_of_gt Real.pi_pos))
    exact_mod_cast hcast
  have hsmall : S.card < (Finset.range (n + 1)).card := by simp [n]
  obtain ⟨i, hi, j, hj, hij, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hsmall hmap
  exact hij (hinj hi hj heq)

/-- The same bound holds at every point of the segment against the
right-hand endpoint, using one fixed cover for all crossings. -/
theorem continuous_phase_uniform_le_of_crossing_cover
    (φ : ℝ → ℝ) (A B : ℝ) (S : Finset ℝ)
    (_hAB : A ≤ B) (hφ : ContinuousOn φ (Set.Icc A B))
    (hcover : ∀ x ∈ Set.Icc A B, Real.cos (φ x) = 0 → x ∈ S) :
    ∀ x ∈ Set.Icc A B, |φ x - φ B| ≤ ((S.card : ℝ) + 2) * Real.pi := by
  intro x hx
  rw [abs_sub_comm]
  apply continuous_phase_oscillation_le_of_crossing_cover φ x B S hx.2
  · apply hφ.mono
    intro z hz
    exact ⟨hx.1.trans hz.1, hz.2⟩
  · intro z hz hc
    exact hcover z ⟨hx.1.trans hz.1, hz.2⟩ hc

/-- A polar representation turns a cosine zero into a real-part zero. -/
theorem realPart_eq_zero_of_polar_phase
    (w : ℂ) (t : ℝ) (hrep : w = (‖w‖ : ℂ) * Complex.exp ((t : ℂ) * I))
    (ht : Real.cos t = 0) : w.re = 0 := by
  rw [hrep]
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_re, ht]

/-- Any continuous polar phase of the actual mollified zeta has uniformly
bounded displacement along the horizontal segment. Existence of the phase
and the boundary passage are not asserted. -/
theorem exists_uniform_mollifiedZeta_horizontalPhase_bound
    {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ η Y b C : ℝ, 0 < η ∧ η < 1 / 4 ∧ 1 < Y ∧ 2 ≤ b ∧ 0 < C ∧
      (∀ y : ℝ, Y ≤ y → ∀ σ : ℝ, 1 / 2 + 1 / Real.log y ≤ σ →
        σ ≤ 1 / 2 + η → ∀ s : ℂ, b ≤ s.re →
          1 / 2 ≤ (mollifiedZeta σ y ε s).re) ∧
      ∀ y : ℝ, Y ≤ y → ∀ σ : ℝ, 1 / 2 + 1 / Real.log y ≤ σ →
        σ ≤ 1 / 2 + η → ∀ T : ℝ, b + 1 ≤ T → ∀ φ : ℝ → ℝ,
          ContinuousOn φ (Set.Icc (1 / 2 : ℝ) b) →
          (∀ x ∈ Set.Icc (1 / 2 : ℝ) b,
            mollifiedZeta σ y ε ((x : ℂ) + (T : ℂ) * I) =
              (‖mollifiedZeta σ y ε ((x : ℂ) + (T : ℂ) * I)‖ : ℂ) *
                Complex.exp ((φ x : ℂ) * I)) →
          ∀ x ∈ Set.Icc (1 / 2 : ℝ) b,
            |φ x - φ b| ≤
              (Real.log (2 * (1 + C * (T + (b - 1 / 4)) * y)) /
                Real.log ((b - 1 / 4) / (b - 1 / 2)) + 2) * Real.pi := by
  obtain ⟨η, Y, b, C, hη, hη', hY, hb, hC, hanchor, hz⟩ :=
    exists_uniform_mollifiedZeta_horizontalRealZeros_bound hε
  refine ⟨η, Y, b, C, hη, hη', hY, hb, hC, hanchor, ?_⟩
  intro y hy σ hσ hση T hT φ hφ hrep x hx
  obtain ⟨hfin, hcard⟩ := hz y hy σ hσ hση T hT
  let S := hfin.toFinset
  have hcover : ∀ z ∈ Set.Icc (1 / 2 : ℝ) b, Real.cos (φ z) = 0 → z ∈ S := by
    intro z hz hcos
    apply hfin.mem_toFinset.mpr
    exact ⟨hz, realPart_eq_zero_of_polar_phase _ _ (hrep z hz) hcos⟩
  have hphase := continuous_phase_uniform_le_of_crossing_cover φ (1 / 2) b S
    (by linarith) hφ hcover x hx
  calc
    _ ≤ ((S.card : ℝ) + 2) * Real.pi := hphase
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ Real.pi_pos.le
      dsimp [S]
      linarith

end RiemannResearch.Analysis.ConreyBaluyot
