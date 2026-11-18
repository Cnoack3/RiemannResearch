import RiemannResearch.Analysis.ActualInghamGabrielWindows
import RiemannResearch.Analysis.ActualInghamGabrielRegularity
import RiemannResearch.Analysis.GabrielAffineWindow
import Mathlib.Tactic

/-!
# Gabriel interpolation for the actual moving Ingham strip

For the actual mollified zeta error the power of the observed moment varies
from 4/3 to 2. Its two independently controlled Gaussian endpoint budgets
enter with exactly the conjugate weights. The reflecting halves of the whole
boundary integral cancel against the two equal observation windows.
-/
noncomputable section
open Set Complex MeasureTheory
open RiemannResearch.Analysis.InghamInterpolation
namespace RiemannResearch.Analysis.InghamMollifier

/-- Outer endpoint scale corresponding to physical damping `exp (-b*t^2)`
at boundary power `p`. -/
def gabrielGaussianScale (T b p : ℝ) : ℝ := (T*Real.sqrt (p*b))⁻¹

/-- Actual Gaussian endpoint, including the vertical-line normalizing
factor for the entire smoothing multiplier. -/
def gabrielBoundaryBudget (X : ℕ) (T b x p : ℝ) : ℝ :=
  Real.exp (p*b*x^2)*gabrielEndpoint (stripMomentDensity (mollifiedError X) x p) T
    (gabrielGaussianScale T b p)

private theorem gaussian_scale {T b p : ℝ} (hT : 0 < T) (hb : 0 < b) (hp : 0 < p) :
    0 < gabrielGaussianScale T b p ∧ p*b=1/(T*gabrielGaussianScale T b p)^2 := by
  have hh := Real.sqrt_pos.mpr (mul_pos hp hb)
  constructor
  · exact inv_pos.mpr (mul_pos hT hh)
  · have hv : T*gabrielGaussianScale T b p = (Real.sqrt (p*b))⁻¹ := by
      unfold gabrielGaussianScale
      field_simp
    rw [hv, inv_pow, one_div, inv_inv, Real.sq_sqrt (mul_pos hp hb).le]

private theorem actual_budget_nonneg (X : ℕ) {T b x p : ℝ}
    (hT : 0 < T) (hb : 0 < b) (hp : 0 < p) : 0 ≤ gabrielBoundaryBudget X T b x p := by
  apply mul_nonneg (Real.exp_pos _).le
  apply integral_nonneg
  intro u
  apply mul_nonneg (Real.exp_pos _).le
  exact intervalIntegral.integral_nonneg
    (mul_nonneg (mul_nonneg hT.le (gaussian_scale hT hb hp).1.le) (Real.sqrt_nonneg _))
    (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)

private theorem cancel_reflected_moments {θ K Q Z A B : ℝ} (hθ : θ ∈ Icc (0:ℝ) 1)
    (hK : 0 ≤ K) (hQ : 0 ≤ Q) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hobs : 2*(K^(4/(3-θ))*Q) ≤ Z)
    (hstrip : Z^((3-θ)/4) ≤
      ((2*A)^(3/4:ℝ))^(1-θ)*((2*B)^(1/2:ℝ))^θ) :
    K*Q^((3-θ)/4) ≤ (A^(3/4:ℝ))^(1-θ)*(B^(1/2:ℝ))^θ := by
  have ht : 0 < 3-θ := by linarith [hθ.2]
  have hc : 0 ≤ (3-θ)/4 := by positivity
  have hpc : 4/(3-θ)*((3-θ)/4)=1 := by field_simp
  have h := (Real.rpow_le_rpow (mul_nonneg (by norm_num)
    (mul_nonneg (Real.rpow_nonneg hK _) hQ)) hobs hc).trans hstrip
  have hf (v : ℝ) (hv : 0 ≤ v) (p q : ℝ) :
      ((2*v)^p)^q = (2:ℝ)^(p*q)*(v^p)^q := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hv,
      Real.mul_rpow (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hv _),
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (mul_nonneg (Real.rpow_nonneg hK _) hQ),
    Real.mul_rpow (Real.rpow_nonneg hK _) hQ, ← Real.rpow_mul hK, hpc, Real.rpow_one,
    hf A hA, hf B hB] at h
  have he : (2:ℝ)^((3/4:ℝ)*(1-θ)) * (A^(3/4:ℝ))^(1-θ) *
      ((2:ℝ)^((1/2:ℝ)*θ)*(B^(1/2:ℝ))^θ) =
      (2:ℝ)^((3-θ)/4)*((A^(3/4:ℝ))^(1-θ)*(B^(1/2:ℝ))^θ) := by
    rw [show (3-θ)/4 = (3/4:ℝ)*(1-θ)+(1/2:ℝ)*θ by ring,
      Real.rpow_add (by norm_num : (0:ℝ)<2)]
    ring
  rw [he] at h
  exact (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _)).mp h

/-- Unconditional mixed-norm interpolation for the actual mollified zeta error.
The physical damping `b` can be any positive number (in particular `κ/T²`).
The hypotheses are solely arithmetic ranges and height parameters. -/
theorem actual_gabriel_moving_window {δ : ℝ} (hδ : 0 < δ) {X : ℕ} (hX : 2 ≤ X)
    {T H b θ : ℝ} (hT : 2 ≤ T) (hXT : (X:ℝ) ≤ T) (hH : 1 ≤ H) (hHT : H ≤ T)
    (hb : 0 < b) (hθ : θ ∈ Icc (0:ℝ) 1) :
    let β := 1 + δ/Real.log (X:ℝ)
    let σ := 1/2+(β-1/2)*θ
    let p := 4/(3-θ)
    Real.exp (b*(σ^2-T^2))*(1-1/H)*
      (∫ t in H..T, stripMomentDensity (mollifiedError X) σ p t)^((3-θ)/4) ≤
      ((gabrielBoundaryBudget X T b (1/2) (4/3))^(3/4:ℝ))^(1-θ)*
      ((gabrielBoundaryBudget X T b β 2)^(1/2:ℝ))^θ := by
  let β := 1 + δ/Real.log (X:ℝ)
  let σ := 1/2+(β-1/2)*θ
  let p := 4/(3-θ)
  let F := gabrielDampedError X b
  let K := Real.exp (b*(σ^2-T^2))*(1-1/H)
  let A := gabrielBoundaryBudget X T b (1/2) (4/3)
  let B := gabrielBoundaryBudget X T b β 2
  let Q := ∫ t in H..T, stripMomentDensity (mollifiedError X) σ p t
  let Z := ∫ t in -T..T, stripMomentDensity F σ p t
  have ht : 0<T := by linarith
  have hx : 1 < (X:ℝ) := by exact_mod_cast (by omega : 1 < X)
  have hβ : 1 < β := by dsimp [β]; linarith [div_pos hδ (Real.log_pos hx)]
  have hβ0 : 1/2 ≤ β := by linarith
  have hd : 0 < β-1/2 := by linarith
  have he : 1/2+(β-1/2)=β := by ring
  have hσ : 1/2 ≤ σ := by dsimp [σ]; linarith [mul_nonneg hd.le hθ.1]
  have hp : 0 < p := div_pos (by norm_num) (by linarith [hθ.2])
  have hL : 0 < 2*T := by positivity
  have hL0 : 0 < (4/3:ℝ) := by norm_num
  have hR0 : 0 < (2:ℝ) := by norm_num
  have hA : 0 ≤ A := actual_budget_nonneg X ht hb hL0
  have hB : 0 ≤ B := actual_budget_nonneg X ht hb hR0
  obtain ⟨_,_,hcrit⟩ := exists_actual_gabriel_left_endpoint_bound
  have leftInt : IntegrableOn (fun u : ℝ => Real.exp (-u) *
      ∫ t in 0..T*gabrielGaussianScale T b (4/3)*Real.sqrt u,
      stripMomentDensity (mollifiedError X) (1/2) (4/3) t) (Ioi 0) := by
    have hm := (hcrit (by omega : 1 ≤ X) hT hXT (gaussian_scale ht hb hL0).1.le).1
    simpa only [stripMomentDensity,mollifiedError,Complex.ofReal_div,Complex.ofReal_one,
      Complex.ofReal_ofNat,mul_comm _ I] using hm
  have rightInt : IntegrableOn (fun u : ℝ => Real.exp (-u) *
      ∫ t in 0..T*gabrielGaussianScale T b 2*Real.sqrt u,
      stripMomentDensity (mollifiedError X) β 2 t) (Ioi 0) := by
    have hm := (actual_gabriel_right_endpoint_le hδ hX ht.le (gaussian_scale ht hb hR0).1.le).1
    simpa only [stripMomentDensity,mollifiedError,β,Real.rpow_two,mul_comm _ I] using hm
  have left (y : ℝ) : (∫ t in y..y+2*T, stripMomentDensity F (1/2) (4/3) t) ≤ 2*A := by
    have h := actual_gabriel_boundary_windows (X := X) (le_refl (1/2)) (by norm_num) hL0 ht
      (gaussian_scale ht hb hL0).1 (gaussian_scale ht hb hL0).2
      (norm_mollifiedError_vertical_neg X (1/2)) leftInt hL.le y
    exact h.trans_eq (by dsimp [A,gabrielBoundaryBudget]; ring)
  have right (y : ℝ) : (∫ t in y..y+2*T, stripMomentDensity F β 2 t) ≤ 2*B := by
    have h := actual_gabriel_boundary_windows (X := X) hβ0 hβ.ne' hR0 ht
      (gaussian_scale ht hb hR0).1 (gaussian_scale ht hb hR0).2
      (norm_mollifiedError_vertical_neg X β) rightInt hL.le y
    exact h.trans_eq (by dsimp [B,gabrielBoundaryBudget]; ring)
  have U (x q : ℝ) (hh : 1/2 ≤ x) (hq : 0 < q) :
      UniformContinuous (stripMomentDensity F x q) :=
    uniformContinuous_gabrielDampedError_norm_rpow X hb hh hq
  have hs := gabriel_affine_window (F := F) (a := 1/2) (d := β-1/2) (ML := 2*A) (MR := 2*B)
    hd (by simpa only [he] using gabrielDampedError_diffContOnCl X b β)
    (by simpa only [he] using gabrielDampedError_bounded_strip X hb β)
    hθ hL (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hA) (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hB)
    (U _ _ (le_refl _) hL0) (by simpa only [he] using U β 2 hβ0 hR0)
    (U σ p hσ hp) left (by simpa only [he] using right) (-T)
  rw [show -T+(2*T)=T by ring] at hs
  have ho := actual_gabriel_observation_window (X := X) (x := σ) hb.le hH hHT hp
  have hev (t : ℝ) : stripMomentDensity F σ p (-t) = stripMomentDensity F σ p t := by
    dsimp only [stripMomentDensity,F]
    rw [norm_gabrielDampedError_vertical_neg]
  have hw := gabriel_symmetric_window (U σ p hσ hp).continuous
    (fun _ => Real.rpow_nonneg (norm_nonneg _) _) hev (by linarith) hHT
  have hK : 0 ≤ K := mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr
    (by simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hH))
  have hQ : 0 ≤ Q := intervalIntegral.integral_nonneg hHT (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)
  exact cancel_reflected_moments (K := K) (Q := Q) (Z := Z) (A := A) (B := B) hθ hK hQ hA hB
    ((mul_le_mul_of_nonneg_left ho (by norm_num)).trans hw) hs

end RiemannResearch.Analysis.InghamMollifier
