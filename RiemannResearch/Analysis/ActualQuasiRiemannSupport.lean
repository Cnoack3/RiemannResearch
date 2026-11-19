/-
Copyright (c) 2026 Joseph Bebel and RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Bebel, RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import RiemannResearch.Analysis.ActualZeroBadTailDensity

/-!
# Exact quasi-Riemann support of the actual finite zero model

Joseph Bebel's all-moduli Dirichlet theorem, QuasiRiemannTracker PR 143, was
admitted on 2026-11-15. The elementary root proofs below adapt its
`AlgebraicContact`, `ContactUniqueness` and `PolynomialContact` files at
revision `42cf5415cfaa4205caaa25ab11160724606cdc33`. The isolating interval
here is tightened to forty decimal places. The analytic Dirichlet conclusion
is an explicit source proposition. The canonical root and the cutoff,
reflection, weighted-sum and operator consequences are proved locally.

Source: https://github.com/GTimG/QuasiRiemannTracker/pull/143 .
Liu's Hexagon preprint 2611.00421v1, Theorem 1.1, reports the same polynomial
for the larger family of continuous unitary Hecke characters.
-/

noncomputable section
open Set Zeta23

namespace RiemannResearch.Analysis.ActualZeroOrdinate
namespace ContinuumContact

def polynomial (x : ℝ) : ℝ :=
  3888*19^5*(15*x-13)^4*(1-x)^5-7*(7-6*x)^4*(9*x-7)^5

def lower : ℝ := 8733458561067185768011847960650723567704 / 10^40
def upper : ℝ := 8733458561067185768011847960650723567705 / 10^40

theorem lower_negative : polynomial lower < 0 := by norm_num [polynomial,lower]
theorem upper_positive : 0 < polynomial upper := by norm_num [polynomial,upper]

theorem exists_isolated_root : ∃ x ∈ Ioo lower upper, polynomial x = 0 := by
  have hcont : Continuous polynomial := by unfold polynomial; fun_prop
  obtain ⟨x,hx,hzero⟩ := intermediate_value_Icc
    (by norm_num [lower,upper] : lower ≤ upper) hcont.continuousOn
    (show (0 : ℝ) ∈ Icc (polynomial lower) (polynomial upper) from
      ⟨lower_negative.le,upper_positive.le⟩)
  refine ⟨x,⟨?_,?_⟩,hzero⟩
  · by_contra hn
    have he : x = lower := le_antisymm (le_of_not_gt hn) hx.1
    subst x
    linarith [lower_negative]
  · by_contra hn
    have he : x = upper := le_antisymm hx.2 (le_of_not_gt hn)
    subst x
    linarith [upper_positive]

def theta : ℝ := Classical.choose exists_isolated_root

theorem theta_isolated : theta ∈ Ioo lower upper :=
  (Classical.choose_spec exists_isolated_root).1
theorem theta_root : polynomial theta = 0 :=
  (Classical.choose_spec exists_isolated_root).2

theorem theta_range : theta ∈ Ioo (13 / 15 : ℝ) (7 / 8) := by
  have h := theta_isolated
  norm_num [lower,upper] at h
  constructor <;> linarith [h.1,h.2]

def logRatio (x : ℝ) : ℝ :=
  Real.log (3888*19^5)+4*Real.log (15*x-13)+5*Real.log (1-x)-Real.log 7-
    4*Real.log (7-6*x)-5*Real.log (9*x-7)
def rate (x : ℝ) : ℝ := 60/(15*x-13)-5/(1-x)+24/(7-6*x)-45/(9*x-7)

theorem logRatio_deriv {x : ℝ} (hx : x ∈ Ioo (13 / 15 : ℝ) (7 / 8)) :
    HasDerivAt logRatio (rate x) x := by
  have ha : 0 < 15*x-13 := by linarith [hx.1]
  have hb : 0 < 1-x := by linarith [hx.2]
  have hc : 0 < 7-6*x := by linarith [hx.2]
  have hd : 0 < 9*x-7 := by linarith [hx.1]
  have h1 := (((hasDerivAt_id x).const_mul 15).sub_const 13).log ha.ne'
  have h2 := ((hasDerivAt_id x).const_sub 1).log hb.ne'
  have h3 := (((hasDerivAt_id x).const_mul 6).const_sub 7).log hc.ne'
  have h4 := (((hasDerivAt_id x).const_mul 9).sub_const 7).log hd.ne'
  have h := (((((h1.const_mul 4).const_add (Real.log (3888 * 19^5))).add
    (h2.const_mul 5)).sub_const (Real.log 7)).sub (h3.const_mul 4)).sub (h4.const_mul 5)
  apply h.congr_deriv
  simp only [rate, id_eq]
  ring

theorem rate_pos {x : ℝ} (hx : x ∈ Ioo (13 / 15 : ℝ) (7 / 8)) : 0 < rate x := by
  have ha : 0 < 15*x-13 := by linarith [hx.1]
  have hb : 0 < 1-x := by linarith [hx.2]
  have hc : 0 < 7-6*x := by linarith [hx.2]
  have hd : 0 < 9*x-7 := by linarith [hx.1]
  have h1 : (480 : ℝ) ≤ 60/(15*x-13) := (le_div_iff₀ ha).mpr (by linarith [hx.2])
  have h2 : (5 : ℝ)/(1-x) ≤ 40 := (div_le_iff₀ hb).mpr (by linarith [hx.2])
  have h3 : 0 < (24 : ℝ)/(7-6*x) := div_pos (by norm_num) hc
  have h4 : (45 : ℝ)/(9*x-7) ≤ 225/4 := (div_le_iff₀ hd).mpr (by linarith [hx.1])
  unfold rate
  linarith

theorem logRatio_strictMono : StrictMonoOn logRatio (Ioo (13 / 15 : ℝ) (7 / 8)) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioo _ _)
  · intro x hx
    exact (logRatio_deriv hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (logRatio_deriv (interior_subset hx)).hasDerivWithinAt
  · intro x hx
    exact rate_pos (interior_subset hx)

theorem logRatio_zero_of_root {x : ℝ} (hx : x ∈ Ioo (13 / 15 : ℝ) (7 / 8))
    (hroot : polynomial x = 0) : logRatio x = 0 := by
  have ha : 15*x-13 ≠ 0 := ne_of_gt (by linarith [hx.1])
  have hb : 1-x ≠ 0 := ne_of_gt (by linarith [hx.2])
  have hc : 7-6*x ≠ 0 := ne_of_gt (by linarith [hx.2])
  have hd : 9*x-7 ≠ 0 := ne_of_gt (by linarith [hx.1])
  have he : 3888*19^5*(15*x-13)^4*(1-x)^5 = 7*(7-6*x)^4*(9*x-7)^5 := by
    unfold polynomial at hroot
    linarith
  have hh := congrArg Real.log he
  rw [Real.log_mul (mul_ne_zero (by norm_num) (pow_ne_zero 4 ha)) (pow_ne_zero 5 hb),
    Real.log_mul (by norm_num) (pow_ne_zero 4 ha),
    Real.log_mul (mul_ne_zero (by norm_num) (pow_ne_zero 4 hc)) (pow_ne_zero 5 hd),
    Real.log_mul (by norm_num) (pow_ne_zero 4 hc)] at hh
  simp only [Real.log_pow] at hh
  unfold logRatio
  norm_num only [show (3888 : ℝ)*19^5 = 9627072912 by norm_num]
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem root_unique {x : ℝ} (hx : x ∈ Ioo (13 / 15 : ℝ) (7 / 8))
    (hroot : polynomial x = 0) : x = theta := by
  apply logRatio_strictMono.injOn hx theta_range
  rw [logRatio_zero_of_root hx hroot,logRatio_zero_of_root theta_range theta_root]

def expanded (x : ℝ) : ℝ :=
  ((-274959111914881) + x * (2643837682856883 + x *
  ((-11291220876239226) + x * (28111661257098222 + x *
  ((-44964545308854309) + x * (47916748658170215 + x *
  ((-34020380857037616) + x * (15517896164111592 + x *
  ((-4126408710053184) + x * 487371101862528)))))))))

theorem expanded_eq (x : ℝ) : expanded x = -polynomial x := by
  unfold expanded polynomial
  ring

theorem isolated : ∃! x : ℝ, (13 / 15 : ℝ) < x ∧ x < (7 / 8 : ℝ) ∧ expanded x = 0 := by
  refine ⟨theta, ⟨theta_range.1, theta_range.2, ?_⟩, ?_⟩
  · rw [expanded_eq, theta_root, neg_zero]
  · intro x hx
    apply root_unique ⟨hx.1, hx.2.1⟩
    have hh := hx.2.2
    rw [expanded_eq] at hh
    exact neg_eq_zero.mp hh

def contact : ℝ := sInf {x | (13 / 15 : ℝ) < x ∧ x < (7 / 8 : ℝ) ∧ expanded x = 0}

theorem contact_eq : contact = theta := by
  have hset : {x | (13 / 15 : ℝ) < x ∧ x < (7 / 8 : ℝ) ∧ expanded x = 0} = {theta} := by
    ext x
    constructor
    · intro hx
      apply Set.mem_singleton_iff.mpr
      apply root_unique ⟨hx.1, hx.2.1⟩
      have hh := hx.2.2
      rw [expanded_eq] at hh
      exact neg_eq_zero.mp hh
    · intro hx
      have he : x = theta := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨theta_range.1, theta_range.2, by rw [expanded_eq, theta_root, neg_zero]⟩
  unfold contact
  rw [hset, csInf_singleton]

end ContinuumContact

/-- Canonical isolated polynomial root, in the same sInf presentation
as upstream `Candidate.bound`. -/
def continuumContact : ℝ := ContinuumContact.contact

theorem continuumContact_mem : continuumContact ∈ Ioo (13 / 15 : ℝ) (7 / 8) := by
  rw [continuumContact, ContinuumContact.contact_eq]
  exact ContinuumContact.theta_range

theorem continuumContact_lt_rational :
    continuumContact < (8733458561067185768011847960650723567705 / 10^40 : ℝ) := by
  rw [continuumContact, ContinuumContact.contact_eq]
  exact ContinuumContact.theta_isolated.2

/-- The ζ specialization excludes the principal pole. -/
def ZetaZeroFreeHalfPlane (B : ℝ) : Prop :=
  ∀ s : ℂ, s ≠ 1 → B < s.re → riemannZeta s ≠ 0

/-- All-moduli version of Bebel's externally verified `Candidate.bound`.
The principal pole is the sole exception. -/
def DirichletContinuumContactNonvanishing : Prop :=
  ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ},
    continuumContact < s.re → ¬ (χ = 1 ∧ s = 1) → DirichletCharacter.LFunction χ s ≠ 0

/-- The ζ fragment suffices for all the finite-cutoff consumers. -/
def ContinuumContactNonvanishing : Prop := ZetaZeroFreeHalfPlane continuumContact

theorem zeta_continuumContact_of_dirichlet
    (h : DirichletContinuumContactNonvanishing) : ContinuumContactNonvanishing := by
  intro s hp hs
  have hn := h (q := 1) (1 : DirichletCharacter ℂ 1) hs (by rintro ⟨_, rfl⟩; exact hp rfl)
  simpa only [DirichletCharacter.LFunction_modOne_eq] using hn

theorem ZetaZeroFreeHalfPlane.mono {B B' : ℝ}
    (h : ZetaZeroFreeHalfPlane B) (hBB' : B ≤ B') : ZetaZeroFreeHalfPlane B' :=
  fun s hp hs => h s hp (lt_of_le_of_lt hBB' hs)

private theorem re_le_of_zeroFreeHalfPlane {B : ℝ} (h : ZetaZeroFreeHalfPlane B)
    {ρ : ℂ} (hz : IsNontrivialZero ρ) : ρ.re ≤ B := by
  by_contra! hβ
  have hp : ρ ≠ 1 := by
    intro heq
    have hlt := hz.2.2
    rw [heq, Complex.one_re] at hlt
    exact (lt_irrefl _ hlt)
  exact h ρ hp hβ hz.1

/-- Functional-equation reflection gives the complete closed strip at
every finite height and retains possible zeros on its two boundary lines. -/
theorem displacement_le_of_zeroFreeHalfPlane {B T : ℝ} (h : ZetaZeroFreeHalfPlane B)
    {ρ : ℂ} (hρ : ρ ∈ cutoff T) : |ρ.re - 1 / 2| ≤ B - 1 / 2 := by
  have hr := re_le_of_zeroFreeHalfPlane h (mem_cutoff.mp hρ).1
  have hl := re_le_of_zeroFreeHalfPlane h (mem_cutoff.mp (reflect_mem hρ)).1
  rw [reflect_re] at hl
  rw [abs_le]
  constructor <;> linarith

theorem strictTail_eq_zero_of_zeroFreeHalfPlane {B : ℝ} (h : ZetaZeroFreeHalfPlane B)
    (T δ : ℝ) (hδ : B - 1 / 2 ≤ δ) : strictTail T δ = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro c _
  exact if_neg (not_lt.mpr ((displacement_le_of_zeroFreeHalfPlane h c.1.2).trans hδ))

theorem badWeightedSum_eq_zero_of_zeroFreeHalfPlane {B : ℝ} (h : ZetaZeroFreeHalfPlane B)
    (T δ : ℝ) (φ : ℝ → ℝ) (hδ : B - 1 / 2 ≤ δ) : badWeightedSum T δ φ = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro c _
  exact if_neg (not_lt.mpr ((displacement_le_of_zeroFreeHalfPlane h c.1.2).trans hδ))

/-- The boundary term and integration ceiling both use the actual tight support. -/
theorem badWeightedSum_layerCake_of_zeroFreeHalfPlane {B : ℝ} (h : ZetaZeroFreeHalfPlane B)
    (T δ : ℝ) (φ f : ℝ → ℝ) (hδ : δ ≤ B - 1 / 2) (hf : Continuous f)
    (hderiv : ∀ t, HasDerivAt φ (f t) t) :
    badWeightedSum T δ φ = φ δ * strictTail T δ +
      ∫ t in δ..(B - 1 / 2), strictTail T t * f t := by
  apply FiniteStrictTail.layerCake _ _ _ _ hf hderiv δ (B - 1 / 2) hδ
  intro c _
  exact displacement_le_of_zeroFreeHalfPlane h c.1.2

end RiemannResearch.Analysis.ActualZeroOrdinate

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open ActualZeroOrdinate

/-- Exact disappearance of the reflected far-strip operator at every height
and positive dimension. -/
theorem badCorrection_eq_zero_of_zeroFreeHalfPlane {B : ℝ} (h : ZetaZeroFreeHalfPlane B)
    (T : ℝ) (d : ℕ) (hd : 1 ≤ d) (δ : ℝ) (hδ : B - 1 / 2 ≤ δ) :
    badCorrection T d δ = 0 := by
  have hn := badCorrection_norm_le_badWeightedSum T d hd δ
  rw [badWeightedSum_eq_zero_of_zeroFreeHalfPlane h T δ _ hδ, mul_zero] at hn
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))

theorem badCorrection_eq_zero_at_continuumContact (h : DirichletContinuumContactNonvanishing)
    (T : ℝ) (d : ℕ) (hd : 1 ≤ d) : badCorrection T d (continuumContact - 1 / 2) = 0 :=
  badCorrection_eq_zero_of_zeroFreeHalfPlane (zeta_continuumContact_of_dirichlet h)
    T d hd _ le_rfl

end RiemannResearch.Analysis.ActualZeroPhaseMoments
