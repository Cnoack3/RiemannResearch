/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotEstermannMellinShift
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
/-!
# The coincident Estermann Mellin pole at s = 1

For alpha = beta = 0 the actual kernel has order exactly -2. Its leading
coefficient is 1 / (K * lam). A holomorphic numerator g gives the exact
local identity F(s) = g(s)/(s-1)^2 and the pole-subtracted residue g'(1).
The latter is characterized by a proved limit; no value of the derivative
in terms of Euler's constant or logarithms is assumed or claimed.

Source: the collision in the contour calculation of
S. A. C. Baluyot, *On the Zeros of Riemann's Zeta-function* (2017),
Lemma 3.1.3, pp. 96–97:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320
The source supports the contour setting. The local normal-form argument uses
Mathlib meromorphic-order theory. The double-pole rectangle shift is separate.
-/

open Complex Set Filter
open scoped Topology
noncomputable section
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- The collision at alpha = beta = 0 has a nonzero leading double-pole coefficient. -/
theorem estermannMellinKernel_diagonal_doublePole_limit {K : ℕ} [NeZero K]
    (h : (ZMod K)ˣ) {lam : ℂ} (hlam : lam ≠ 0) :
    Tendsto (fun s : ℂ => (s - 1) ^ 2 * estermannMellinKernel (h : ZMod K) 0 0 lam s)
      (𝓝[≠] 1) (𝓝 (lam⁻¹ * (K : ℂ)⁻¹)) := by
  have hg : ContinuousAt Gamma (1 : ℂ) := by
    apply Complex.continuousAt_Gamma
    intro n hn
    have he := congrArg Complex.re hn
    simp at he
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hp : ContinuousAt (fun s : ℂ => lam ^ (-s)) (1 : ℂ) :=
    continuousAt_id.neg.const_cpow (.inl hlam)
  have hh := (hg.continuousWithinAt.tendsto.mul hp.continuousWithinAt.tendsto).mul
    (estermann_diagonal_doublePole_limit h)
  have hh' : Tendsto
      (fun s : ℂ => (Gamma s * lam ^ (-s)) * ((s - 1) ^ 2 * estermann (h : ZMod K) s s))
      (𝓝[≠] 1) (𝓝 (lam⁻¹ * (K : ℂ)⁻¹)) := by
    simpa only [Gamma_one, Complex.cpow_neg_one, one_mul] using hh
  exact hh'.congr' (Eventually.of_forall fun s => by
    dsimp [estermannMellinKernel]
    simp only [add_zero]
    ring)

/-- The collision is exactly a double pole, so the simple-pole rectangle API cannot apply. -/
theorem meromorphicOrderAt_estermannMellinKernel_diagonal {K : ℕ} [NeZero K]
    (h : (ZMod K)ˣ) {lam : ℂ} (hlam : lam ≠ 0) :
    meromorphicOrderAt (estermannMellinKernel (h : ZMod K) 0 0 lam) 1 = (-2 : ℤ) := by
  have hf := meromorphicAt_estermannMellinKernel (h : ZMod K) 0 0 hlam
    (z := 1) (by norm_num)
  have hs : MeromorphicAt (fun s : ℂ => s - 1) 1 :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt
  have hh := (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero ((hs.pow 2).mul hf)).mp
    ⟨lam⁻¹ * (K : ℂ)⁻¹,
      mul_ne_zero (inv_ne_zero hlam) (inv_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne K))),
      estermannMellinKernel_diagonal_doublePole_limit h hlam⟩
  rw [meromorphicOrderAt_mul (hs.pow 2) hf, meromorphicOrderAt_pow hs,
    meromorphicOrderAt_id_sub_const] at hh
  have hh' : (2 : WithTop ℤ) +
      meromorphicOrderAt (estermannMellinKernel (h : ZMod K) 0 0 lam) 1 = 0 := by
    simpa using hh
  apply (WithTop.add_left_cancel (show (2 : WithTop ℤ) ≠ ⊤ by simp))
  simpa using hh'


/-- A holomorphic numerator identifies both coefficients of the local double pole.
The residue is the derivative of this numerator, not the divergent simple-pole limit. -/
theorem exists_estermannMellinKernel_diagonal_laurent {K : ℕ} [NeZero K]
    (h : (ZMod K)ˣ) {lam : ℂ} (hlam : lam ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 1 ∧ g 1 = lam⁻¹ * (K : ℂ)⁻¹ ∧
      (∀ᶠ s : ℂ in 𝓝[≠] 1,
        estermannMellinKernel (h : ZMod K) 0 0 lam s = g s / (s - 1) ^ 2) ∧
      Tendsto (fun s : ℂ => (s - 1) *
        (estermannMellinKernel (h : ZMod K) 0 0 lam s -
          (lam⁻¹ * (K : ℂ)⁻¹) / (s - 1) ^ 2))
        (𝓝[≠] 1) (𝓝 (deriv g 1)) := by
  have hm := meromorphicAt_estermannMellinKernel (h : ZMod K) 0 0 hlam
    (z := 1) (by norm_num)
  obtain ⟨g, hg, _, hfg⟩ := (meromorphicOrderAt_eq_int_iff hm).mp
    (meromorphicOrderAt_estermannMellinKernel_diagonal h hlam)
  have heq : ∀ᶠ s : ℂ in 𝓝[≠] 1,
      estermannMellinKernel (h : ZMod K) 0 0 lam s = g s / (s - 1) ^ 2 := by
    filter_upwards [hfg] with s hs
    simpa only [smul_eq_mul, zpow_neg, zpow_ofNat, div_eq_mul_inv, mul_comm] using hs
  have hglim : Tendsto g (𝓝[≠] (1 : ℂ)) (𝓝 (lam⁻¹ * (K : ℂ)⁻¹)) := by
    apply (estermannMellinKernel_diagonal_doublePole_limit h hlam).congr'
    filter_upwards [heq, self_mem_nhdsWithin] with s hs hs1
    change s ≠ 1 at hs1
    rw [hs]
    field_simp [sub_ne_zero.mpr hs1]
  have hg1 : g 1 = lam⁻¹ * (K : ℂ)⁻¹ :=
    tendsto_nhds_unique hg.continuousAt.continuousWithinAt.tendsto hglim
  refine ⟨g, hg, hg1, heq, ?_⟩
  apply (hasDerivAt_iff_tendsto_slope.mp hg.differentiableAt.hasDerivAt).congr'
  filter_upwards [heq, self_mem_nhdsWithin] with s hs hs1
  change s ≠ 1 at hs1
  rw [hs, ← hg1]
  simp only [slope, smul_eq_mul, vsub_eq_sub]
  field_simp [sub_ne_zero.mpr hs1]

end RiemannResearch.Analysis.ConreyBaluyot
