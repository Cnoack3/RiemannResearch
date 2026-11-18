import RiemannResearch.Analysis.PeriodicDirichletGram
import RiemannResearch.RH.QPrimorialCarryTrace
import RiemannResearch.RH.WeilExplicitFormula.XiPrime.ExplicitFormula.ZeroFree
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Prime and actual zero resolvents for periodic Schur determinants

Source: C. Noack, *Q CRT Carry Gram and Schur Matrices with Zeta Trace
Identities*, October 2026. The contour provider is the repository's
unconditional theorem for the real part of the logarithmic derivative of ξ.
Zeros retain their real parts, ordinates and multiplicities.
-/
noncomputable section
open Filter
open scoped Topology
open Complex Zeta23 Zeta23.XiPrime Zeta23.XiPrime.ZeroFree
open RiemannResearch.Analysis.PeriodicDirichletGram
namespace RiemannResearch.RH.CRTCarryZetaResolvent
variable {D : ℕ} [NeZero D] {ι κ : Type*}
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The Dirichlet deformation is a literal tilt of the original reciprocal-square Q. -/
theorem gram_eq_Q_tilt (φ : ZMod D → ι → ℝ) {s : ℂ} (hs : 1 < s.re) (i j : ι) :
    gram φ s i j = (ZetaTwoProbability.zetaTwo : ℂ) * ∑' n : ℕ,
      (ZetaTwoHilbert.positiveQWeight n : ℂ) * (n : ℂ)^(2-s) *
        ((φ n i * φ n j : ℝ) : ℂ) := by
  rw [gram_dirichlet φ hs, LSeries, ← tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [hn, ZetaTwoHilbert.positiveQWeight]
  have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hz : (ZetaTwoProbability.zetaTwo : ℂ) ≠ 0 := by
    exact_mod_cast ZetaTwoProbability.zetaTwo_pos.ne'
  rw [LSeries.term, if_neg hn, Complex.cpow_sub 2 s hnc, Complex.cpow_two]
  simp only [ZetaTwoHilbert.positiveQWeight, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast]
  have hns : (n : ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hnc)
  field_simp [hz, hnc, hns]

theorem normalized_two_eq_Q (φ : ZMod D → ι → ℝ) (i j : ι) :
    normalized φ 2 i j = ∑' n : ℕ,
      (ZetaTwoHilbert.positiveQWeight n : ℂ) * ((φ n i * φ n j : ℝ) : ℂ) := by
  change (riemannZeta 2)⁻¹ * gram φ 2 i j = _
  rw [gram_eq_Q_tilt φ (by norm_num : 1 < (2:ℂ).re), ← ZetaTwoProbability.zetaTwo_eq_riemannZeta]
  have hz : (ZetaTwoProbability.zetaTwo : ℂ) ≠ 0 := by
    exact_mod_cast ZetaTwoProbability.zetaTwo_pos.ne'
  simp [← mul_assoc, hz]

def correction (join : ZMod D → (ι ⊕ κ) → ℝ) (s : ℂ) : ℂ :=
  let base := fun a i => join a (.inl i)
  ((normalized join s)⁻¹ * logMoment join s).trace -
    ((normalized base s)⁻¹ * logMoment base s).trace

theorem schur_prime_series (join : ZMod D → (ι ⊕ κ) → ℝ)
    {s : ℂ} (hs : 1 < s.re) (hb : (normalized (fun a i => join a (.inl i)) s).det ≠ 0)
    (hj : (normalized join s).det ≠ 0) :
    logDeriv (fun u => (schur join u).det) s =
      (Fintype.card κ : ℂ) * LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s -
      correction join s := by
  rw [logDeriv_apply, schur_det_logDeriv join hs hb hj,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  dsimp only [correction]
  ring

/-- The full leverage correction remains when the scalar prime term is written over actual zeros. -/
theorem schur_actual_zero_trace_re (join : ZMod D → (ι ⊕ κ) → ℝ)
    {s : ℂ} (hs : 1 < s.re) (hb : (normalized (fun a i => join a (.inl i)) s).det ≠ 0)
    (hj : (normalized join s).det ≠ 0) :
    (logDeriv (fun u => (schur join u).det) s).re =
      (Fintype.card κ : ℝ) * ((logDeriv Gammaℝ s + 1/s + 1/(s-1)).re -
        ∑' ρ : zetaZeroConfig.carrier, (zeroMult ρ : ℝ) *
          ((s.re - (ρ : ℂ).re) / Complex.normSq (s - ρ))) - (correction join s).re := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := fun h => by simp [h] at hs
  have he := logDeriv_xi_eq hs0 hs1 (riemannZeta_ne_zero_of_one_le_re hs.le)
  rw [Lfn] at he
  have hr := congrArg Complex.re he
  rw [re_logDeriv_xi_eq_tsum (xi_ne_zero_of_one_le_re hs.le), Complex.add_re] at hr
  have hz : (-(deriv riemannZeta s / riemannZeta s)).re =
      (logDeriv Gammaℝ s + 1/s + 1/(s-1)).re -
      ∑' ρ : zetaZeroConfig.carrier, (zeroMult ρ : ℝ) *
        ((s.re - (ρ : ℂ).re) / Complex.normSq (s - ρ)) := by
    rw [Complex.neg_re]
    change -(logDeriv riemannZeta s).re = _
    linarith
  rw [logDeriv_apply, schur_det_logDeriv join hs hb hj, Complex.sub_re, Complex.mul_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, hz]
  rfl

/-- An actual zero rules out every constant multiple of the rotated ξ as the raw limit. -/
theorem no_unscaled_xi_limit (c : ℂ) :
    ¬ ∀ z : ℂ, Tendsto (fun n => (1 - z^2 • QPrimorialCarryTrace.omega n).det)
      atTop (𝓝 (c * xi (1/2 + I*z))) := by
  intro h
  obtain ⟨ρ, hρ⟩ := exists_isNontrivialZero
  let z := (ρ - 1/2) / I
  have hz : 1/2 + I*z = ρ := by dsimp [z]; field_simp; ring
  have hzero : xi ρ = 0 := by
    rw [xi_eq_zero_iff]
    exact hρ
  have h1 := (QPrimorialCarryTrace.unscaled_det_tendsto_one ‖z‖).tendsto_at (le_refl ‖z‖)
  have heq := tendsto_nhds_unique (h z) h1
  rw [hz, hzero, mul_zero] at heq
  exact zero_ne_one heq

end RiemannResearch.RH.CRTCarryZetaResolvent
