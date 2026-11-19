import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Central differences for the reflected Montgomery Gram kernel

The mixed central difference keeps both opposite displacements until after
cancellation. The fourth derivative is required only between the shifted
points. -/
noncomputable section
open Set
namespace RiemannResearch.Analysis.MontgomeryCentralDifference

def central (h : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (f (x+h) + f (x-h))/2 - f x

private theorem central_deriv {f f' : ℝ → ℂ} {x h : ℝ}
    (hp : HasDerivAt f (f' (x+h)) (x+h))
    (hm : HasDerivAt f (f' (x-h)) (x-h))
    (hz : HasDerivAt f (f' x) x) :
    HasDerivAt (central h f) (central h f' x) x := by
  have hp' : HasDerivAt (fun t : ℝ => f (t+h)) (f' (x+h)) x := by
    simpa only [Function.comp_def, id_eq, one_smul] using! hp.scomp x ((hasDerivAt_id x).add_const h)
  have hm' : HasDerivAt (fun t : ℝ => f (t-h)) (f' (x-h)) x := by
    simpa only [Function.comp_def, id_eq, one_smul] using! hm.scomp x ((hasDerivAt_id x).sub_const h)
  exact ((hp'.add hm').div_const 2).sub hz

private theorem central_norm_le {f f' f'' : ℝ → ℂ} {x h M : ℝ}
    (h1 : ∀ y ∈ Icc (x-|h|) (x+|h|), HasDerivAt f (f' y) y)
    (h2 : ∀ y ∈ Icc (x-|h|) (x+|h|), HasDerivAt f' (f'' y) y)
    (hb : ∀ y ∈ Icc (x-|h|) (x+|h|), ‖f'' y‖ ≤ M) :
    ‖central h f x‖ ≤ M*h^2 := by
  let I := Icc (x-|h|) (x+|h|)
  let J := Icc (-|h|) |h|
  have hp {t : ℝ} (ht : t ∈ J) : x+t ∈ I := by
    obtain ⟨hl,hr⟩ := ht
    exact ⟨by linarith, by linarith⟩
  have hm {t : ℝ} (ht : t ∈ J) : x-t ∈ I := by
    obtain ⟨hl,hr⟩ := ht
    exact ⟨by linarith, by linarith⟩
  let g := fun t : ℝ => f (x+t) + f (x-t)
  let dg := fun t : ℝ => f' (x+t) - f' (x-t)
  have hg (t : ℝ) (ht : t ∈ J) : HasDerivAt g (dg t) t := by
    have hp' := (h1 _ (hp ht)).scomp t ((hasDerivAt_id t).const_add x)
    have hm' := (h1 _ (hm ht)).scomp t ((hasDerivAt_id t).const_sub x)
    simpa only [g, dg, Function.comp_def, one_smul, neg_smul, sub_eq_add_neg, Pi.add_def, id_eq]
      using! hp'.add hm'
  have hnorm (t : ℝ) (ht : t ∈ J) : ‖dg t‖ ≤ M*(2*|h|) := by
    have hh := (convex_Icc (x-|h|) (x+|h|)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy => (h2 y hy).hasDerivWithinAt) hb (hm ht) (hp ht)
    have ha := abs_le.mpr ht
    have hM : 0 ≤ M := (norm_nonneg _).trans (hb (x+t) (hp ht))
    calc
      ‖dg t‖ ≤ M*‖(x+t)-(x-t)‖ := hh
      _ = M*(2*|t|) := by rw [show (x+t)-(x-t) = 2*t by ring, Real.norm_eq_abs, abs_mul]; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ha (by norm_num)) hM
  have hzero : 0 ∈ J := ⟨by linarith [abs_nonneg h], abs_nonneg h⟩
  have hin : h ∈ J := ⟨neg_abs_le h, le_abs_self h⟩
  have hh := (convex_Icc (-|h|) |h|).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hg t ht).hasDerivWithinAt) hnorm hzero hin
  have he : central h f x = (g h - g 0)/2 := by
    dsimp [central,g]
    simp only [add_zero, sub_zero]
    ring
  rw [he, norm_div]
  have hn : ‖(2:ℂ)‖ = 2 := by norm_num
  rw [hn]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  simp only [sub_zero, Real.norm_eq_abs] at hh
  calc
    _ ≤ M*(2*|h|)*|h| := hh
    _ = M*h^2*2 := by rw [show M*(2*|h|)*|h| = M*|h|^2*2 by ring, sq_abs]

/-- A fourth derivative bound on the exact compact interval of sampled shifts
forces the product of two squared displacement factors. -/
theorem mixed_central_norm_le (f f₁ f₂ f₃ f₄ : ℝ → ℂ) (a b M : ℝ)
    (h₁ : ∀ x ∈ Icc (-(|a|+|b|)) (|a|+|b|), HasDerivAt f (f₁ x) x)
    (h₂ : ∀ x ∈ Icc (-(|a|+|b|)) (|a|+|b|), HasDerivAt f₁ (f₂ x) x)
    (h₃ : ∀ x ∈ Icc (-(|a|+|b|)) (|a|+|b|), HasDerivAt f₂ (f₃ x) x)
    (h₄ : ∀ x ∈ Icc (-(|a|+|b|)) (|a|+|b|), HasDerivAt f₃ (f₄ x) x)
    (hM : ∀ x ∈ Icc (-(|a|+|b|)) (|a|+|b|), ‖f₄ x‖ ≤ M) :
    ‖central a (central b f) 0‖ ≤ M*a^2*b^2 := by
  let J := Icc (0-|a|) (0+|a|)
  let I := Icc (-(|a|+|b|)) (|a|+|b|)
  have sub {x y : ℝ} (hx : x ∈ J) (hy : y ∈ Icc (x-|b|) (x+|b|)) : y ∈ I := by
    obtain ⟨hl,hr⟩ := hx
    obtain ⟨hy1,hy2⟩ := hy
    exact ⟨by linarith,by linarith⟩
  have mem (x : ℝ) : x+b ∈ Icc (x-|b|) (x+|b|) ∧
      x-b ∈ Icc (x-|b|) (x+|b|) ∧ x ∈ Icc (x-|b|) (x+|b|) := by
    have hb := abs_le.mp (le_refl |b|)
    exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩,
      ⟨by linarith [abs_nonneg b],by linarith [abs_nonneg b]⟩⟩
  apply le_trans (central_norm_le (f' := central b f₁) (f'' := central b f₂)
    (M := M*b^2) ?_ ?_ ?_) (by ring_nf; exact le_rfl)
  · intro x hx
    exact central_deriv (h₁ _ (sub hx (mem x).1)) (h₁ _ (sub hx (mem x).2.1))
      (h₁ _ (sub hx (mem x).2.2))
  · intro x hx
    exact central_deriv (h₂ _ (sub hx (mem x).1)) (h₂ _ (sub hx (mem x).2.1))
      (h₂ _ (sub hx (mem x).2.2))
  · intro x hx
    exact central_norm_le (fun y hy => h₃ _ (sub hx hy))
      (fun y hy => h₄ _ (sub hx hy)) (fun y hy => hM _ (sub hx hy))

end RiemannResearch.Analysis.MontgomeryCentralDifference
