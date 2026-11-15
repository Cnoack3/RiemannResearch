/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotHorizontalPhase
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Convex.Contractible

/-!
# Horizontal argument on a zero-free segment

A continuous nonvanishing complex function on a compact real interval has a
continuous polar phase. We normalize the phase to the principal argument at
the right endpoint, then use the actual mollified-zeta crossing bound to
control the phase and its horizontal integral.

The actual theorem assumes the horizontal segment is zero-free. Selection of
nearby zero-free heights and the Littlewood boundary-limit passage are
separate obligations.
-/

noncomputable section
open Complex Set Filter
open scoped Topology
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- A continuous nonvanishing complex function on a compact interval has a
continuous polar phase on that interval. -/
theorem exists_continuous_polar_phase_on_Icc
    (g : ℝ → ℂ) (A B : ℝ) (hAB : A ≤ B) (hg : Continuous g)
    (hne : ∀ x ∈ Set.Icc A B, g x ≠ 0) :
    ∃ φ : ℝ → ℝ, ContinuousOn φ (Set.Icc A B) ∧
      ∀ x ∈ Set.Icc A B, g x = (‖g x‖ : ℂ) * Complex.exp ((φ x : ℂ) * I) := by
  let V : Set ℝ := {x | g x ≠ 0}
  have hV : IsOpen V := by
    change IsOpen (g ⁻¹' ({0} : Set ℂ)ᶜ)
    exact isClosed_singleton.isOpen_compl.preimage hg
  have hA : A ∈ Set.Icc A B := ⟨le_rfl, hAB⟩
  have hB : B ∈ Set.Icc A B := ⟨hAB, le_rfl⟩
  have hAn : V ∈ 𝓝 A := hV.mem_nhds (hne A hA)
  have hBn : V ∈ 𝓝 B := hV.mem_nhds (hne B hB)
  obtain ⟨δA, hδA, hballA⟩ := Metric.mem_nhds_iff.mp hAn
  obtain ⟨δB, hδB, hballB⟩ := Metric.mem_nhds_iff.mp hBn
  let δ := min δA δB
  have hδ : 0 < δ := lt_min hδA hδB
  let U : Set ℝ := Set.Ioo (A - δ) (B + δ)
  have hIU : Set.Icc A B ⊆ U := by
    intro x hx
    change A - δ < x ∧ x < B + δ
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hUV : U ⊆ V := by
    intro x hx
    change A - δ < x ∧ x < B + δ at hx
    by_cases hxa : x < A
    · apply hballA
      rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith : x - A < 0)]
      have hmin := min_le_left δA δB
      dsimp [δ] at *
      linarith
    · by_cases hxb : B < x
      · apply hballB
        rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith : 0 < x - B)]
        have hmin := min_le_right δA δB
        dsimp [δ] at *
        linarith
      · exact hne x ⟨le_of_not_gt hxa, le_of_not_gt hxb⟩
  have hUo : IsOpen U := isOpen_Ioo
  have hUne : U.Nonempty := ⟨A, hIU hA⟩
  letI : ContractibleSpace U := (convex_Ioo (A - δ) (B + δ)).contractibleSpace hUne
  have hUc : IsSimplyConnected U := SimplyConnectedSpace.ofContractible U
  have hUzero : (0 : ℂ) ∉ g '' U := by
    rintro ⟨x, hx, hx0⟩
    exact (hUV hx) hx0
  obtain ⟨L, hLcont, hLexp⟩ :=
    Complex.exists_continuousOn_eqOn_exp_comp hUc hUo hg.continuousOn hUzero
  refine ⟨fun x => (L x).im, (Complex.continuous_im.comp_continuousOn hLcont).mono hIU, ?_⟩
  intro x hx
  have he : Complex.exp (L x) = g x := hLexp (hIU hx)
  have hn : ‖g x‖ = Real.exp ((L x).re) := by rw [← he, Complex.norm_exp]
  calc
    g x = Complex.exp (L x) := he.symm
    _ = Complex.exp (((L x).re : ℂ) + ((L x).im : ℂ) * I) := by
      rw [Complex.re_add_im]
    _ = (‖g x‖ : ℂ) * Complex.exp (((L x).im : ℂ) * I) := by
      rw [Complex.exp_add, ← Complex.ofReal_exp, ← hn]

/-- A polar phase may be normalized to the principal argument at the right
endpoint without changing its continuity or polar representation. -/
theorem normalize_continuous_polar_phase_on_Icc
    (g : ℝ → ℂ) (φ : ℝ → ℝ) (A B : ℝ) (hAB : A ≤ B)
    (hφ : ContinuousOn φ (Set.Icc A B))
    (hrep : ∀ x ∈ Set.Icc A B,
      g x = (‖g x‖ : ℂ) * Complex.exp ((φ x : ℂ) * I))
    (hB : g B ≠ 0) :
    ∃ ψ : ℝ → ℝ, ContinuousOn ψ (Set.Icc A B) ∧
      ψ B = (g B).arg ∧
      ∀ x ∈ Set.Icc A B,
        g x = (‖g x‖ : ℂ) * Complex.exp ((ψ x : ℂ) * I) := by
  have hBI : B ∈ Set.Icc A B := ⟨hAB, le_rfl⟩
  have hn : (‖g B‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hB)
  have he : Complex.exp ((φ B : ℂ) * I) =
      Complex.exp (((g B).arg : ℂ) * I) := by
    apply mul_left_cancel₀ hn
    rw [← hrep B hBI, Complex.norm_mul_exp_arg_mul_I]
  let ψ : ℝ → ℝ := fun x => φ x - φ B + (g B).arg
  have hexp (x : ℝ) : Complex.exp ((ψ x : ℂ) * I) =
      Complex.exp ((φ x : ℂ) * I) := by
    dsimp [ψ]
    push_cast
    rw [add_mul, sub_mul, Complex.exp_add, Complex.exp_sub, ← he]
    field_simp
  refine ⟨ψ, (hφ.sub continuousOn_const).add continuousOn_const, ?_, ?_⟩
  · dsimp [ψ]; ring
  · intro x hx
    rw [hexp]
    exact hrep x hx

/-- On a zero-free horizontal segment, the actual mollified zeta has a
continuous polar phase normalized to the principal argument at the right
endpoint. Its displacement, absolute size, and horizontal integral satisfy
the uniform Jensen bound. Zero-free heights and boundary limits are not
asserted. -/
theorem exists_uniform_mollifiedZeta_normalized_horizontal_argument
    {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ η Y b C : ℝ, 0 < η ∧ η < 1 / 4 ∧ 1 < Y ∧ 2 ≤ b ∧ 0 < C ∧
      (∀ y : ℝ, Y ≤ y → ∀ σ : ℝ, 1 / 2 + 1 / Real.log y ≤ σ →
        σ ≤ 1 / 2 + η → ∀ s : ℂ, b ≤ s.re →
          1 / 2 ≤ (mollifiedZeta σ y ε s).re) ∧
      ∀ y : ℝ, Y ≤ y → ∀ σ : ℝ, 1 / 2 + 1 / Real.log y ≤ σ →
        σ ≤ 1 / 2 + η → ∀ T : ℝ, b + 1 ≤ T →
          (∀ x ∈ Set.Icc (1 / 2 : ℝ) b,
            mollifiedZeta σ y ε ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
          ∃ φ : ℝ → ℝ, ContinuousOn φ (Set.Icc (1 / 2 : ℝ) b) ∧
            φ b = (mollifiedZeta σ y ε ((b : ℂ) + (T : ℂ) * I)).arg ∧
            (∀ x ∈ Set.Icc (1 / 2 : ℝ) b,
              mollifiedZeta σ y ε ((x : ℂ) + (T : ℂ) * I) =
                (‖mollifiedZeta σ y ε ((x : ℂ) + (T : ℂ) * I)‖ : ℂ) *
                  Complex.exp ((φ x : ℂ) * I)) ∧
            (∀ x ∈ Set.Icc (1 / 2 : ℝ) b,
              |φ x - φ b| ≤
                (Real.log (2 * (1 + C * (T + (b - 1 / 4)) * y)) /
                  Real.log ((b - 1 / 4) / (b - 1 / 2)) + 2) * Real.pi) ∧
            (∀ x ∈ Set.Icc (1 / 2 : ℝ) b,
              |φ x| ≤
                (Real.log (2 * (1 + C * (T + (b - 1 / 4)) * y)) /
                  Real.log ((b - 1 / 4) / (b - 1 / 2)) + 3) * Real.pi) ∧
            (∀ α ∈ Set.Icc (1 / 2 : ℝ) b,
              ‖∫ x in α..b, φ x‖ ≤
                ((Real.log (2 * (1 + C * (T + (b - 1 / 4)) * y)) /
                  Real.log ((b - 1 / 4) / (b - 1 / 2)) + 3) * Real.pi) *
                    |b - α|) := by
  obtain ⟨η, Y, b, C, hη, hη', hY, hb, hC, hanchor, hp⟩ :=
    exists_uniform_mollifiedZeta_horizontalPhase_bound hε
  refine ⟨η, Y, b, C, hη, hη', hY, hb, hC, hanchor, ?_⟩
  intro y hy σ hσ hση T hT hne
  have hT0 : 0 < T := by linarith
  let g : ℝ → ℂ := fun x => mollifiedZeta σ y ε ((x : ℂ) + (T : ℂ) * I)
  have hg : Continuous g := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hi : 0 < (((x : ℂ) + (T : ℂ) * I)).im := by simpa using hT0
    have hf := differentiableAt_mollifiedZeta_of_im_pos σ y ε hi
    have hh : ContinuousAt (fun z : ℝ => (z : ℂ) + (T : ℂ) * I) x :=
      (Complex.continuous_ofReal.add continuous_const).continuousAt
    exact hf.continuousAt.comp_of_eq hh rfl
  obtain ⟨φ, hφ, hrep⟩ := exists_continuous_polar_phase_on_Icc
    g (1 / 2) b (by linarith) hg hne
  have hBne : g b ≠ 0 := hne b ⟨by linarith, le_rfl⟩
  obtain ⟨ψ, hψ, hψb, hψrep⟩ := normalize_continuous_polar_phase_on_Icc
    g φ (1 / 2) b (by linarith) hφ hrep hBne
  have hdisp := hp y hy σ hσ hση T hT ψ hψ hψrep
  have habs : ∀ x ∈ Set.Icc (1 / 2 : ℝ) b,
      |ψ x| ≤
        (Real.log (2 * (1 + C * (T + (b - 1 / 4)) * y)) /
          Real.log ((b - 1 / 4) / (b - 1 / 2)) + 3) * Real.pi := by
    intro x hx
    have harg : |ψ b| ≤ Real.pi := by
      rw [hψb]
      exact Complex.abs_arg_le_pi _
    calc
      |ψ x| = |(ψ x - ψ b) + ψ b| := by congr 1; ring
      _ ≤ |ψ x - ψ b| + |ψ b| := abs_add_le _ _
      _ ≤ (Real.log (2 * (1 + C * (T + (b - 1 / 4)) * y)) /
          Real.log ((b - 1 / 4) / (b - 1 / 2)) + 2) * Real.pi + Real.pi :=
        add_le_add (hdisp x hx) harg
      _ = _ := by ring
  refine ⟨ψ, hψ, hψb, hψrep, hdisp, habs, ?_⟩
  intro α hα
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  rw [Set.uIoc_of_le hα.2] at hx
  have hx' : x ∈ Set.Icc (1 / 2 : ℝ) b := ⟨hα.1.trans hx.1.le, hx.2⟩
  simpa only [Real.norm_eq_abs] using habs x hx'

end RiemannResearch.Analysis.ConreyBaluyot
