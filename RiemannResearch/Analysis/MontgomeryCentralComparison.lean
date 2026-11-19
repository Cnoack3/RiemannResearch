import RiemannResearch.Analysis.MontgomeryCentralDifference
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Comparison theorem for mixed central differences

A real fourth derivative can dominate a complex fourth derivative pointwise.
Positive central-difference integration preserves this domination. The proof
uses one-sided derivative comparison on each compact interval. -/

noncomputable section
open Set
namespace RiemannResearch.Analysis.MontgomeryCentralDifference

def realCentral (h : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := (f (x+h)+f (x-h))/2-f x

private theorem plus_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {v : E} {x t : ℝ} (h : HasDerivAt f v (x+t)) :
    HasDerivAt (fun t : ℝ => f (x+t)) v t := by
  simpa only [Function.comp_def,id_eq,one_smul] using! h.scomp t ((hasDerivAt_id t).const_add x)

private theorem minus_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {v : E} {x t : ℝ} (h : HasDerivAt f v (x-t)) :
    HasDerivAt (fun t : ℝ => f (x-t)) (-v) t := by
  simpa only [Function.comp_def,id_eq,neg_smul,one_smul] using!
    h.scomp t ((hasDerivAt_id t).const_sub x)

private theorem fence {f f' : ℝ → ℂ} {g g' : ℝ → ℝ} {h : ℝ}
    (hf : ∀ t ∈ Icc 0 h, HasDerivAt f (f' t) t)
    (hg : ∀ t ∈ Icc 0 h, HasDerivAt g (g' t) t)
    (hz : ‖f 0‖ ≤ g 0) (hb : ∀ t ∈ Icc 0 h, ‖f' t‖ ≤ g' t) :
    ∀ t ∈ Icc 0 h, ‖f t‖ ≤ g t := by
  intro t ht
  exact image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hf x ⟨hx.1,hx.2.le⟩).hasDerivWithinAt) hz
    (fun x hx => (hg x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hg x ⟨hx.1,hx.2.le⟩).hasDerivWithinAt) (fun x hx => hb x ⟨hx.1,hx.2.le⟩) ht

private theorem central_le_realCentral {f f' f'' : ℝ → ℂ} {g g' g'' : ℝ → ℝ} {x h : ℝ}
    (h1 : ∀ y ∈ Icc (x-|h|) (x+|h|), HasDerivAt f (f' y) y)
    (h2 : ∀ y ∈ Icc (x-|h|) (x+|h|), HasDerivAt f' (f'' y) y)
    (g1 : ∀ y ∈ Icc (x-|h|) (x+|h|), HasDerivAt g (g' y) y)
    (g2 : ∀ y ∈ Icc (x-|h|) (x+|h|), HasDerivAt g' (g'' y) y)
    (hb : ∀ y ∈ Icc (x-|h|) (x+|h|), ‖f'' y‖ ≤ g'' y) :
    ‖central h f x‖ ≤ realCentral h g x := by
  let J := Icc 0 |h|
  let I := Icc (x-|h|) (x+|h|)
  have shifts {t : ℝ} (ht : t ∈ J) : x+t ∈ I ∧ x-t ∈ I := by
    obtain ⟨hl,hr⟩ := ht
    exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩
  let D := fun t : ℝ => f (x+t)+f (x-t)-(f x+f x)
  let D' := fun t : ℝ => f' (x+t)-f' (x-t)
  let D'' := fun t : ℝ => f'' (x+t)+f'' (x-t)
  let P := fun t : ℝ => g (x+t)+g (x-t)-(g x+g x)
  let P' := fun t : ℝ => g' (x+t)-g' (x-t)
  let P'' := fun t : ℝ => g'' (x+t)+g'' (x-t)
  have hd (t : ℝ) (ht : t ∈ J) : HasDerivAt D (D' t) t := by
    simpa only [D,D',sub_eq_add_neg] using!
      (((plus_deriv (h1 _ (shifts ht).1)).add (minus_deriv (h1 _ (shifts ht).2))).sub_const (f x+f x))
  have hd' (t : ℝ) (ht : t ∈ J) : HasDerivAt D' (D'' t) t := by
    simpa only [D',D'',sub_neg_eq_add] using!
      (plus_deriv (h2 _ (shifts ht).1)).sub (minus_deriv (h2 _ (shifts ht).2))
  have hp (t : ℝ) (ht : t ∈ J) : HasDerivAt P (P' t) t := by
    simpa only [P,P',sub_eq_add_neg] using!
      (((plus_deriv (g1 _ (shifts ht).1)).add (minus_deriv (g1 _ (shifts ht).2))).sub_const (g x+g x))
  have hp' (t : ℝ) (ht : t ∈ J) : HasDerivAt P' (P'' t) t := by
    simpa only [P',P'',sub_neg_eq_add] using!
      (plus_deriv (g2 _ (shifts ht).1)).sub (minus_deriv (g2 _ (shifts ht).2))
  have hb' (t : ℝ) (ht : t ∈ J) : ‖D'' t‖ ≤ P'' t :=
    (norm_add_le _ _).trans (add_le_add (hb _ (shifts ht).1) (hb _ (shifts ht).2))
  have hcmp := fence hd hp (by simp [D,P]) (fence hd' hp' (by simp [D',P']) hb')
  have he : central h f x = D |h|/2 ∧ realCentral h g x = P |h|/2 := by
    rcases le_or_gt 0 h with h0 | h0
    · constructor <;> simp only [central,realCentral,D,P,abs_of_nonneg h0] <;> ring
    · constructor <;> simp only [central,realCentral,D,P,abs_of_neg h0,
        sub_neg_eq_add,← sub_eq_add_neg] <;> ring
  rw [he.1,he.2,norm_div,show ‖(2:ℂ)‖ = 2 by norm_num]
  exact div_le_div_of_nonneg_right (hcmp |h| ⟨abs_nonneg h,le_rfl⟩) (by norm_num)

private theorem central_complex_deriv {f f' : ℝ → ℂ} {x h : ℝ}
    (hp : HasDerivAt f (f' (x+h)) (x+h)) (hm : HasDerivAt f (f' (x-h)) (x-h))
    (hz : HasDerivAt f (f' x) x) : HasDerivAt (central h f) (central h f' x) x := by
  have hp' : HasDerivAt (fun t : ℝ => f (t+h)) (f' (x+h)) x := by
    simpa only [Function.comp_def,id_eq,one_smul] using! hp.scomp x ((hasDerivAt_id x).add_const h)
  have hm' : HasDerivAt (fun t : ℝ => f (t-h)) (f' (x-h)) x := by
    simpa only [Function.comp_def,id_eq,one_smul] using! hm.scomp x ((hasDerivAt_id x).sub_const h)
  exact ((hp'.add hm').div_const 2).sub hz

private theorem central_real_deriv {f f' : ℝ → ℝ} {x h : ℝ}
    (hp : HasDerivAt f (f' (x+h)) (x+h)) (hm : HasDerivAt f (f' (x-h)) (x-h))
    (hz : HasDerivAt f (f' x) x) : HasDerivAt (realCentral h f) (realCentral h f' x) x := by
  have hp' : HasDerivAt (fun t : ℝ => f (t+h)) (f' (x+h)) x := by
    simpa only [Function.comp_def,id_eq,one_smul] using! hp.scomp x ((hasDerivAt_id x).add_const h)
  have hm' : HasDerivAt (fun t : ℝ => f (t-h)) (f' (x-h)) x := by
    simpa only [Function.comp_def,id_eq,one_smul] using! hm.scomp x ((hasDerivAt_id x).sub_const h)
  exact ((hp'.add hm').div_const 2).sub hz

/-- Pointwise domination of fourth derivatives propagates to the original shifted mixed difference. -/
theorem mixed_central_norm_le_real_model
    (f f₁ f₂ f₃ f₄ : ℝ → ℂ) (g g₁ g₂ g₃ g₄ : ℝ → ℝ) (a b : ℝ)
    (hf₁ : ∀ x ∈ Icc (-(|a| + |b|)) (|a| + |b|), HasDerivAt f (f₁ x) x)
    (hf₂ : ∀ x ∈ Icc (-(|a| + |b|)) (|a| + |b|), HasDerivAt f₁ (f₂ x) x)
    (hf₃ : ∀ x ∈ Icc (-(|a| + |b|)) (|a| + |b|), HasDerivAt f₂ (f₃ x) x)
    (hf₄ : ∀ x ∈ Icc (-(|a| + |b|)) (|a| + |b|), HasDerivAt f₃ (f₄ x) x)
    (hg₁ : ∀ x ∈ Icc (-(|a| + |b|)) (|a| + |b|), HasDerivAt g (g₁ x) x)
    (hg₂ : ∀ x ∈ Icc (-(|a| + |b|)) (|a| + |b|), HasDerivAt g₁ (g₂ x) x)
    (hg₃ : ∀ x ∈ Icc (-(|a| + |b|)) (|a| + |b|), HasDerivAt g₂ (g₃ x) x)
    (hg₄ : ∀ x ∈ Icc (-(|a| + |b|)) (|a| + |b|), HasDerivAt g₃ (g₄ x) x)
    (hb : ∀ x ∈ Icc (-(|a| + |b|)) (|a| + |b|), ‖f₄ x‖ ≤ g₄ x) :
    ‖central a (central b f) 0‖ ≤ realCentral a (realCentral b g) 0 := by
  let J := Icc (0-|a|) (0+|a|)
  let I := Icc (-(|a| + |b|)) (|a| + |b|)
  have sub {x y : ℝ} (hx : x ∈ J) (hy : y ∈ Icc (x-|b|) (x+|b|)) : y ∈ I := by
    obtain ⟨hl,hr⟩ := hx
    obtain ⟨hy1,hy2⟩ := hy
    exact ⟨by linarith,by linarith⟩
  have mem (x : ℝ) : x+b ∈ Icc (x-|b|) (x+|b|) ∧ x-b ∈ Icc (x-|b|) (x+|b|) ∧
      x ∈ Icc (x-|b|) (x+|b|) := by
    have hb0 := abs_le.mp (le_refl |b|)
    exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩,
      ⟨by linarith [abs_nonneg b],by linarith [abs_nonneg b]⟩⟩
  apply central_le_realCentral (f' := central b f₁) (f'' := central b f₂)
    (g' := realCentral b g₁) (g'' := realCentral b g₂)
  · intro x hx
    exact central_complex_deriv (hf₁ _ (sub hx (mem x).1)) (hf₁ _ (sub hx (mem x).2.1))
      (hf₁ _ (sub hx (mem x).2.2))
  · intro x hx
    exact central_complex_deriv (hf₂ _ (sub hx (mem x).1)) (hf₂ _ (sub hx (mem x).2.1))
      (hf₂ _ (sub hx (mem x).2.2))
  · intro x hx
    exact central_real_deriv (hg₁ _ (sub hx (mem x).1)) (hg₁ _ (sub hx (mem x).2.1))
      (hg₁ _ (sub hx (mem x).2.2))
  · intro x hx
    exact central_real_deriv (hg₂ _ (sub hx (mem x).1)) (hg₂ _ (sub hx (mem x).2.1))
      (hg₂ _ (sub hx (mem x).2.2))
  · intro x hx
    exact central_le_realCentral (fun y hy => hf₃ _ (sub hx hy)) (fun y hy => hf₄ _ (sub hx hy))
      (fun y hy => hg₃ _ (sub hx hy)) (fun y hy => hg₄ _ (sub hx hy)) (fun y hy => hb _ (sub hx hy))

end RiemannResearch.Analysis.MontgomeryCentralDifference
