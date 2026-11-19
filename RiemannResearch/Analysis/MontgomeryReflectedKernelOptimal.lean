import RiemannResearch.Analysis.MontgomeryCentralComparison
import RiemannResearch.Analysis.MontgomeryReflectedKernelSharpness
import RiemannResearch.Analysis.MontgomeryReflectedJetDomination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Transfer of the five rational jet comparisons to the optimal reflected kernel -/

noncomputable section
open Set
namespace RiemannResearch.Analysis.MontgomeryCentralDifference
open MontgomeryPoisson

def PoissonJetDomination : Prop := ∀ d x : ℝ, |x| ≤ 1 → ∀ k : ℕ, k ≤ 4 →
  ‖poissonJet (Complex.I*(d:ℂ)) k (x:ℂ)‖ ≤ cauchyWeight d*poissonJet (0:ℝ) 4 x

private theorem pole_nonzero_complex (x d : ℝ) (hx : |x| ≤ 1) :
    2-((x:ℂ)+Complex.I*(d:ℂ)) ≠ 0 ∧ 2+((x:ℂ)+Complex.I*(d:ℂ)) ≠ 0 := by
  constructor <;> intro h
  · have hr := congrArg Complex.re h
    simp at hr
    linarith [(abs_le.mp hx).2]
  · have hr := congrArg Complex.re h
    simp at hr
    linarith [(abs_le.mp hx).1]

private theorem exponentialJet_norm_le (hjet : PoissonJetDomination)
    (u d x s : ℝ) (hxs : |x| ≤ s) (hs : s ≤ 1) :
    ‖exponentialPoissonJet (u:ℂ) (Complex.I*(d:ℂ)) 4 (x:ℂ)‖ ≤
      ((1+|u|)^4*Real.exp (|u| * s)*cauchyWeight d)*poissonJet (0:ℝ) 4 x := by
  let W := cauchyWeight d*poissonJet (0:ℝ) 4 x
  have hJ (k : ℕ) (hk : k ≤ 4) :
      ‖poissonJet (Complex.I*(d:ℂ)) k (x:ℂ)‖ ≤ W := hjet d x (hxs.trans hs) k hk
  have hw : 0 ≤ W := (norm_nonneg _).trans (hJ 0 (by norm_num))
  have hn : ‖Complex.exp ((u:ℂ)*(x:ℂ))‖ ≤ Real.exp (|u| * s) := by
    rw [Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    apply Real.exp_le_exp.mpr
    exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hxs (abs_nonneg _))
  have ht (k : ℕ) (hk : k ∈ Finset.range 5) :
      ‖(Nat.choose 4 k : ℂ)*(u:ℂ)^(4-k)*poissonJet (Complex.I*(d:ℂ)) k (x:ℂ)‖ ≤
        (Nat.choose 4 k : ℝ)*|u|^(4-k)*W := by
    simp only [norm_mul,norm_pow,Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hJ k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))) (by positivity)
  have hs' : ‖∑ k ∈ Finset.range 5, (Nat.choose 4 k : ℂ)*(u:ℂ)^(4-k)*
      poissonJet (Complex.I*(d:ℂ)) k (x:ℂ)‖ ≤ (1+|u|)^4*W := by
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum ht).trans_eq
    generalize |u| = v
    norm_num [Finset.sum_range_succ,Nat.choose]
    ring
  rw [exponentialPoissonJet,norm_mul]
  apply (mul_le_mul hn hs' (norm_nonneg _) (Real.exp_pos _).le).trans_eq
  dsimp only [W]
  ring

private theorem mixed_congr {α : Type*} [Add α] [Sub α] [Div α] [OfNat α 2]
    (a b : ℝ) (f g : ℝ → α) (h : ∀ x : ℝ, |x| ≤ |a| + |b| → f x=g x) :
    let H := fun (t : ℝ) (F : ℝ → α) (x : ℝ) => (F (x+t)+F (x-t))/2-F x
    H a (H b f) 0 = H a (H b g) 0 := by
  let H := fun (t : ℝ) (F : ℝ → α) (x : ℝ) => (F (x+t)+F (x-t))/2-F x
  have hb (x : ℝ) (hx : |x| ≤ |a|) : H b f x = H b g x := by
    have hp := (abs_add_le x b).trans (by linarith : |x| + |b| ≤ |a| + |b|)
    have hm := (abs_sub x b).trans (by linarith : |x| + |b| ≤ |a| + |b|)
    dsimp only [H]
    rw [h _ hp,h _ hm,h x (by linarith [abs_nonneg b])]
  change (H b f (0+a)+H b f (0-a))/2-H b f 0 = (H b g (0+a)+H b g (0-a))/2-H b g 0
  simp only [zero_add,zero_sub]
  rw [hb a le_rfl,hb (-a) (by simp),hb 0 (by simp)]

set_option maxHeartbeats 700000 in
/-- Once the five scalar jet inequalities are available, no further analytic assumption
enters the uniform bound. -/
theorem reflectedPairKernel_norm_le_comparison_model (hjet : PoissonJetDomination)
    (u a b d : ℝ) (ha : |a| ≤ 1/2) (hb : |b| ≤ 1/2) :
    ‖reflectedPairKernel u a b d‖ ≤
      ((1+|u|)^4*Real.exp (|u| * (|a| + |b|))*cauchyWeight d)*realPoissonMixed a b := by
  let s := |a| + |b|
  let M := (1+|u|)^4*Real.exp (|u| * s)*cauchyWeight d
  let F := fun n : ℕ => fun x : ℝ => exponentialPoissonJet (u:ℂ) (Complex.I*(d:ℂ)) n (x:ℂ)
  let g := fun n : ℕ => fun x : ℝ => M*poissonJet (0:ℝ) n x
  have hs : s ≤ 1 := by dsimp only [s]; linarith
  have hF (n : ℕ) (hn : n < 4) (x : ℝ) (hx : x ∈ Icc (-s) s) :
      HasDerivAt (F n) (F (n+1) x) x := by
    have hne := pole_nonzero_complex x d ((abs_le.mpr hx).trans hs)
    exact (hasDerivAt_exponentialPoissonJet (u := (u:ℂ)) hn hne.1 hne.2).comp_ofReal
  have hg (n : ℕ) (x : ℝ) (hx : x ∈ Icc (-s) s) : HasDerivAt (g n) (g (n+1) x) x := by
    have hxr := abs_le.mp ((abs_le.mpr hx).trans hs)
    exact (hasDerivAt_poissonJet (η := (0:ℝ)) n (by linarith) (by linarith)).const_mul M
  have hcomp := mixed_central_norm_le_real_model (F 0) (F 1) (F 2) (F 3) (F 4)
    (g 0) (g 1) (g 2) (g 3) (g 4) a b (hF 0 (by norm_num)) (hF 1 (by norm_num))
    (hF 2 (by norm_num)) (hF 3 (by norm_num)) (hg 0) (hg 1) (hg 2) (hg 3)
    (fun x hx => exponentialJet_norm_le hjet u d x s (abs_le.mpr hx) hs)
  have hcomplex : central a (central b (F 0)) 0 = reflectedPairKernel u a b d := by
    apply mixed_congr (α := ℂ) a b (F 0) (fun x : ℝ => phaseKernel u d (x:ℂ))
    intro x hx
    have hne := pole_nonzero_complex x d (hx.trans hs)
    exact exponentialPoissonJet_zero hne.1 hne.2
  have hreal : realCentral a (realCentral b (g 0)) 0 =
      realCentral a (realCentral b (fun x : ℝ => M*realPoissonModel x)) 0 := by
    apply mixed_congr (α := ℝ) a b (g 0) (fun x : ℝ => M*realPoissonModel x)
    intro x hx
    have hr := abs_le.mp (hx.trans hs)
    dsimp only [g,realPoissonModel]
    rw [poissonJet_zero_apply (by linarith : (2:ℝ)-(x+0) ≠ 0) (by linarith : (2:ℝ)+(x+0) ≠ 0),
      add_zero]
  have hsym (x : ℝ) : realPoissonModel (-x) = realPoissonModel x := by simp [realPoissonModel]
  have hzero : realPoissonModel 0=1 := by norm_num [realPoissonModel]
  have hmodel : realCentral a (realCentral b (fun x : ℝ => M*realPoissonModel x)) 0 =
      M*realPoissonMixed a b := by
    simp only [realCentral,realPoissonMixed,zero_add,zero_sub,
      show -a+b=-(a-b) by ring,show -a-b=-(a+b) by ring,hsym,hzero]
    ring
  rw [hcomplex,hreal,hmodel] at hcomp
  exact hcomp

/-- The source comparison has equality at zero frequency and zero separation for
each individual pair of displacements. -/
theorem reflectedPairKernel_at_zero_eq_model (a b : ℝ) :
    reflectedPairKernel 0 a b 0 = (realPoissonMixed a b : ℂ) := by
  have hphase (x : ℝ) : phaseKernel 0 0 (x:ℂ) = (realPoissonModel x : ℂ) := by
    simp [phaseKernel,realPoissonModel]
  have hsym (x : ℝ) : realPoissonModel (-x) = realPoissonModel x := by simp [realPoissonModel]
  have hzero : realPoissonModel 0 = 1 := by norm_num [realPoissonModel]
  simp only [reflectedPairKernel,central,hphase,realPoissonMixed,zero_add,zero_sub,
    show -a+b=-(a-b) by ring,show -a-b=-(a+b) by ring,hsym,hzero]
  push_cast
  ring

theorem reflectedPairQuarticEnvelope_of_poissonJetDomination (hjet : PoissonJetDomination) :
    ReflectedPairQuarticEnvelope (8/15) := by
  intro u a b d ha hb
  apply (reflectedPairKernel_norm_le_comparison_model hjet u a b d ha hb).trans
  have hw : 0 ≤ cauchyWeight d := by unfold cauchyWeight; positivity
  exact (mul_le_mul_of_nonneg_left (realPoissonMixed_le_eight_fifteenths a b ha hb)
    (by positivity : 0 ≤ (1+|u|)^4*Real.exp (|u| * (|a| + |b|))*cauchyWeight d)).trans_eq
    (by ring)

/-- The optimal uniform constant on both full displacement intervals and all real frequencies. -/
theorem reflectedPairQuarticEnvelope_eight_fifteenths : ReflectedPairQuarticEnvelope (8/15) :=
  reflectedPairQuarticEnvelope_of_poissonJetDomination poissonJet_norm_le_real_fourth

/-- Exact characterization of every admissible uniform constant. -/
theorem reflectedPairQuarticEnvelope_iff {K : ℝ} :
    ReflectedPairQuarticEnvelope K ↔ (8/15:ℝ) ≤ K := by
  refine ⟨reflectedPairQuarticEnvelope_lower_bound,?_⟩
  intro hK u a b d ha hb
  apply (reflectedPairQuarticEnvelope_eight_fifteenths u a b d ha hb).trans
  have hw : 0 ≤ cauchyWeight d := by unfold cauchyWeight; positivity
  gcongr

end RiemannResearch.Analysis.MontgomeryCentralDifference
