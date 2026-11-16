/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotGaussianRays
import RiemannResearch.Analysis.ConreyBaluyotGaussianEstermannIntegrability
import RiemannResearch.Analysis.ConreyBaluyotRationalTwist
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact Gaussian moment assembly with reduced rational Estermann twists

Source: S. A. C. Baluyot, *On the Zeros of Riemann's Zeta-function* (2017),
Section 3.3, pp. 116-117, for the arithmetic assembly.
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320

The exact finite coefficients and both outward ray orientations are retained.
The first Estermann exponent is 2*l-1 and the second is zero. The fixed-parameter
exchange is justified by joint absolute convergence for 0 < theta < pi.
The final moment identity retains the original signed Gaussian pole residue.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- A single rational-twist ray, with its actual outward Jacobian. -/
def gaussianEstermannRay {K : ℕ} [NeZero K] (H : ℕ)
    (l Δ u θ : ℝ) (τ : ℤ) : ℂ :=
  ∫ r : ℝ in Ioi 0, gaussianRayIntegrand l Δ u 0 ((τ:ℝ)*θ) r *
    estermannDampedSeries ((τ*(H:ℤ):ℤ):ZMod K) (((2*l:ℝ):ℂ)-1) 0
      (estermannRayArgument ((H:ℝ)/(K:ℝ)) (τ:ℝ) θ r)

/-- Both reduced rational-twist rays. Nonpositive natural indices contribute zero. -/
def reducedGaussianEstermannPair (l Δ u θ : ℝ) (h k : ℕ) : ℂ :=
  if hp : 0 < h ∧ 0 < k then
    letI : NeZero (k / h.gcd k) :=
      ⟨(Nat.div_gcd_pos_of_pos_right h hp.2).ne'⟩
    gaussianEstermannRay (K := k / h.gcd k) (h / h.gcd k) l Δ u θ 1 +
      gaussianEstermannRay (K := k / h.gcd k) (h / h.gcd k) l Δ u θ (-1)
  else 0

/-- Exact signed rational phase in the actual ray integrand. The integer
multiplier and complex exponent are arbitrary; no angle or convergence
assumption is used in this algebraic identity. -/
theorem gaussianEstermannRayTerm_eq {K : ℕ} [NeZero K] (H : ℕ) (α : ℂ)
    (l Δ u θ r : ℝ) (τ : ℤ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    gaussianEstermannRayTerm ((τ*(H:ℤ):ℤ):ZMod K) α 0 l Δ u
        ((H:ℝ)/(K:ℝ)) (τ:ℝ) θ (m,n) r =
      (m:ℂ)^(-α) * gaussianRayIntegrand l Δ u
        ((τ:ℝ)*(2*Real.pi*((m:ℝ)*(n:ℝ)*((H:ℝ)/(K:ℝ)))))
        ((τ:ℝ)*θ) r := by
  have hd : estermannRayArgument ((H:ℝ)/(K:ℝ)) (τ:ℝ) θ r =
      (((τ*(H:ℤ):ℤ):ℂ)/(K:ℂ)) *
        ((r:ℂ)*Complex.exp ((((τ:ℝ)*θ):ℝ)*I)-1) := by
    unfold estermannRayArgument
    push_cast
    ring
  unfold gaussianEstermannRayTerm
  rw [hd, estermannDampedTerm_displacement (τ*(H:ℤ)) α 0 _ hm hn]
  simp only [Complex.cpow_zero, mul_one, div_eq_mul_inv, ← Complex.cpow_neg]
  have he :
      exp (2*(Real.pi:ℂ)*I*(m:ℂ)*(n:ℂ)*(((τ*(H:ℤ):ℤ):ℂ)/(K:ℂ)) *
        ((r:ℂ)*exp ((((τ:ℝ)*θ):ℝ)*I))) =
      exp (I*(((τ:ℝ)*(2*Real.pi*((m:ℝ)*(n:ℝ)*((H:ℝ)/(K:ℝ))))):ℝ) *
        ((r:ℂ)*exp ((((τ:ℝ)*θ):ℝ)*I))) := by
    congr 1
    push_cast
    ring
  simp only [div_eq_mul_inv] at he
  rw [he]
  unfold gaussianRayIntegrand
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one]
  ring

/-- The complete natural-index convention, including either zero index. -/
theorem weighted_gaussianArithmeticRayValue_eq_estermann {K : ℕ} [NeZero K]
    (A : ℂ) (l Δ u θ : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (H : ℕ)
    (hfrac : (H : ℝ) / (K : ℝ) = (h : ℝ) / (k : ℝ)) (p : ℕ × ℕ) :
    (A * (p.2:ℂ)^(((2*l:ℝ):ℂ)-1)/(k:ℂ)^((2*l:ℝ):ℂ)) *
        gaussianArithmeticRayValue l Δ u (((p.1*p.2*h:ℕ):ℝ)/(k:ℝ)) θ =
      (A * (h:ℂ)^((1-2*l:ℝ):ℂ)/(k:ℂ)) *
        ((∫ r : ℝ in Ioi 0, gaussianEstermannRayTerm ((H:ℕ):ZMod K)
          (((2*l:ℝ):ℂ)-1) 0 l Δ u ((H:ℝ)/(K:ℝ)) 1 θ p r) +
        (∫ r : ℝ in Ioi 0, gaussianEstermannRayTerm (-(H:ZMod K))
          (((2*l:ℝ):ℂ)-1) 0 l Δ u ((H:ℝ)/(K:ℝ)) (-1) θ p r)) := by
  rcases p with ⟨m,n⟩
  by_cases hm : m = 0
  · simp [hm, gaussianArithmeticRayValue, gaussianEstermannRayTerm,
      estermannDampedTerm, estermannTerm]
  by_cases hn : n = 0
  · simp [hn, gaussianArithmeticRayValue, gaussianEstermannRayTerm,
      estermannDampedTerm, estermannTerm]
  have hm' : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hn' : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hh' : (0:ℝ) < h := by exact_mod_cast hh
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hw : (m:ℝ)*(n:ℝ)*((H:ℝ)/(K:ℝ)) = ((m*n*h:ℕ):ℝ)/(k:ℝ) := by
    rw [hfrac]
    push_cast
    ring
  have hi (τ : ℤ) :
      (∫ r : ℝ in Ioi 0, gaussianEstermannRayTerm ((τ*(H:ℤ):ℤ):ZMod K)
        (((2*l:ℝ):ℂ)-1) 0 l Δ u ((H:ℝ)/(K:ℝ)) (τ:ℝ) θ (m,n) r) =
      (m:ℂ)^(-(((2*l:ℝ):ℂ)-1)) *
        gaussianRayIntegral l Δ u ((τ:ℝ)*(2*Real.pi*(((m*n*h:ℕ):ℝ)/(k:ℝ))))
          ((τ:ℝ)*θ) := by
    simp_rw [gaussianEstermannRayTerm_eq H _ l Δ u θ _ τ hm hn, hw]
    exact integral_const_mul _ _
  have hip := hi 1
  have him := hi (-1)
  simp only [Int.cast_one, Int.cast_neg, one_mul, Int.cast_natCast, neg_one_mul] at hip him
  rw [hip, him]
  have hω : (0:ℝ) < ((m*n*h:ℕ):ℝ)/(k:ℝ) := by
    push_cast
    positivity
  rw [gaussianArithmeticRayValue, if_pos hω]
  have hc := rationalTwist_coefficient A ((2*l:ℝ):ℂ) hm' hn' hh' hk'
  have hc' :
      (A*(n:ℂ)^(((2*l:ℝ):ℂ)-1)/(k:ℂ)^((2*l:ℝ):ℂ)) *
        ((((m*n*h:ℕ):ℝ)/(k:ℝ):ℝ):ℂ)^((1-2*l:ℝ):ℂ) =
      (A*(h:ℂ)^((1-2*l:ℝ):ℂ)/(k:ℂ)) * (m:ℂ)^(-(((2*l:ℝ):ℂ)-1)) := by
    simpa only [Nat.cast_mul, Complex.ofReal_natCast, Complex.ofReal_sub,
      Complex.ofReal_one] using hc
  dsimp only
  rw [← mul_assoc, hc']
  ring

/-- Absolute summability of each individual integrated rational-twist ray. -/
theorem summable_integral_gaussianEstermannRayTerm {K : ℕ} [NeZero K] (H : ℕ)
    (l u : ℝ) {Δ θ : ℝ} (hΔ : 0 < Δ) (hH : 0 < H)
    (hθ : θ ∈ Ioo 0 Real.pi) {τ : ℤ} (hτ : τ = 1 ∨ τ = -1) :
    Summable (fun p : ℕ × ℕ => ∫ r : ℝ in Ioi 0,
      gaussianEstermannRayTerm ((τ*(H:ℤ):ℤ):ZMod K) (((2*l:ℝ):ℂ)-1) 0
        l Δ u ((H:ℝ)/(K:ℝ)) (τ:ℝ) θ p r) := by
  have ha : (0:ℝ) < (H:ℝ)/(K:ℝ) := by
    exact div_pos (by exact_mod_cast hH) (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K))
  have ht : (τ:ℝ) = 1 ∨ (τ:ℝ) = -1 := by
    rcases hτ with rfl | rfl <;> norm_num
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun _ => norm_integral_le_integral_norm _)
    (summable_integral_norm_gaussianEstermannRayTerm
      ((τ*(H:ℤ):ℤ):ZMod K) (((2*l:ℝ):ℂ)-1) 0 l u hΔ ha hθ ht)

/-- Exact Fubini evaluation of either signed rational-twist ray. -/
theorem gaussianEstermannRay_eq_tsum {K : ℕ} [NeZero K] (H : ℕ)
    (l u : ℝ) {Δ θ : ℝ} (hΔ : 0 < Δ) (hH : 0 < H)
    (hθ : θ ∈ Ioo 0 Real.pi) {τ : ℤ} (hτ : τ = 1 ∨ τ = -1) :
    gaussianEstermannRay (K := K) H l Δ u θ τ =
      ∑' p : ℕ × ℕ, ∫ r : ℝ in Ioi 0,
        gaussianEstermannRayTerm ((τ*(H:ℤ):ℤ):ZMod K) (((2*l:ℝ):ℂ)-1) 0
          l Δ u ((H:ℝ)/(K:ℝ)) (τ:ℝ) θ p r := by
  have ha : (0:ℝ) < (H:ℝ)/(K:ℝ) := by
    exact div_pos (by exact_mod_cast hH) (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K))
  have ht : (τ:ℝ) = 1 ∨ (τ:ℝ) = -1 := by
    rcases hτ with rfl | rfl <;> norm_num
  exact integral_gaussianRay_mul_estermannDampedSeries
    ((τ*(H:ℤ):ℤ):ZMod K) (((2*l:ℝ):ℂ)-1) 0 l u hΔ ha hθ ht

/-- Absolute convergence of the weighted paired summand for arbitrary
complex coefficient and arbitrary real l and u. -/
theorem summable_weighted_gaussianArithmeticRayValue (A : ℂ) (l u : ℝ)
    {Δ θ : ℝ} (hΔ : 0 < Δ) (hθ : θ ∈ Ioo 0 Real.pi)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    Summable (fun p : ℕ × ℕ =>
      (A * (p.2:ℂ)^(((2*l:ℝ):ℂ)-1)/(k:ℂ)^((2*l:ℝ):ℂ)) *
        gaussianArithmeticRayValue l Δ u (((p.1*p.2*h:ℕ):ℝ)/(k:ℝ)) θ) := by
  let : NeZero k := ⟨hk.ne'⟩
  have hp := summable_integral_gaussianEstermannRayTerm (K := k) h l u hΔ hh hθ
    (Or.inl rfl : (1:ℤ) = 1 ∨ (1:ℤ) = -1)
  have hm := summable_integral_gaussianEstermannRayTerm (K := k) h l u hΔ hh hθ
    (Or.inr rfl : (-1:ℤ) = 1 ∨ (-1:ℤ) = -1)
  simp only [Int.cast_one, Int.cast_neg, one_mul, Int.cast_natCast, neg_one_mul] at hp hm
  exact ((hp.add hm).mul_left (A*(h:ℂ)^((1-2*l:ℝ):ℂ)/(k:ℂ))).congr
    (fun p => (weighted_gaussianArithmeticRayValue_eq_estermann
      A l Δ u θ hh hk h rfl p).symm)

/-- The exact infinite sum for a fixed positive pair h,k has the reduced
modulus k/gcd(h,k), both signed residue classes, and unchanged coefficients. -/
theorem tsum_weighted_gaussianArithmeticRayValue_eq_reduced (A : ℂ) (l u : ℝ)
    {Δ θ : ℝ} (hΔ : 0 < Δ) (hθ : θ ∈ Ioo 0 Real.pi)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    (∑' p : ℕ × ℕ,
      (A * (p.2:ℂ)^(((2*l:ℝ):ℂ)-1)/(k:ℂ)^((2*l:ℝ):ℂ)) *
        gaussianArithmeticRayValue l Δ u (((p.1*p.2*h:ℕ):ℝ)/(k:ℝ)) θ) =
      (A * (h:ℂ)^((1-2*l:ℝ):ℂ)/(k:ℂ)) *
        reducedGaussianEstermannPair l Δ u θ h k := by
  let H := h / h.gcd k
  let K := k / h.gcd k
  have hH : 0 < H := Nat.div_gcd_pos_of_pos_left k hh
  have hK : 0 < K := Nat.div_gcd_pos_of_pos_right h hk
  let : NeZero K := ⟨hK.ne'⟩
  have hfrac : (H : ℝ) / (K : ℝ) = (h : ℝ) / (k : ℝ) :=
    reducedRationalTwist_ratio ℝ h k
  have hp := summable_integral_gaussianEstermannRayTerm (K := K) H l u hΔ hH hθ
    (Or.inl rfl : (1:ℤ) = 1 ∨ (1:ℤ) = -1)
  have hm := summable_integral_gaussianEstermannRayTerm (K := K) H l u hΔ hH hθ
    (Or.inr rfl : (-1:ℤ) = 1 ∨ (-1:ℤ) = -1)
  have ep := gaussianEstermannRay_eq_tsum (K := K) H l u hΔ hH hθ
    (Or.inl rfl : (1:ℤ) = 1 ∨ (1:ℤ) = -1)
  have em := gaussianEstermannRay_eq_tsum (K := K) H l u hΔ hH hθ
    (Or.inr rfl : (-1:ℤ) = 1 ∨ (-1:ℤ) = -1)
  simp only [Int.cast_one, Int.cast_neg, one_mul, Int.cast_natCast, neg_one_mul] at hp hm ep em
  simp_rw [weighted_gaussianArithmeticRayValue_eq_estermann A l Δ u θ hh hk H hfrac]
  rw [tsum_mul_left, hp.tsum_add hm, ← ep, ← em]
  simp only [reducedGaussianEstermannPair, dif_pos (show 0 < h ∧ 0 < k from ⟨hh,hk⟩)]
  rfl

/-- Finite rational-twist assembly for arbitrary complex coefficient arrays,
arbitrary positive finite supports, and arbitrary real line parameter. -/
theorem finite_gaussianRay_sum_eq_estermann (s t : Finset ℕ) (A : ℕ → ℕ → ℂ)
    (l u : ℝ) {Δ θ : ℝ} (hΔ : 0 < Δ) (hθ : θ ∈ Ioo 0 Real.pi)
    (hs : ∀ h ∈ s, 0 < h) (ht : ∀ k ∈ t, 0 < k) :
    (∑' p : ℕ × ℕ, ∑ h ∈ s, ∑ k ∈ t,
      (A h k * (p.2:ℂ)^(((2*l:ℝ):ℂ)-1)/(k:ℂ)^((2*l:ℝ):ℂ)) *
        gaussianArithmeticRayValue l Δ u (((p.1*p.2*h:ℕ):ℝ)/(k:ℝ)) θ) =
      ∑ h ∈ s, ∑ k ∈ t,
        (A h k * (h:ℂ)^((1-2*l:ℝ):ℂ)/(k:ℂ)) *
          reducedGaussianEstermannPair l Δ u θ h k := by
  have hsum (h : ℕ) (hh : h ∈ s) : Summable (fun p : ℕ × ℕ => ∑ k ∈ t,
      (A h k * (p.2:ℂ)^(((2*l:ℝ):ℂ)-1)/(k:ℂ)^((2*l:ℝ):ℂ)) *
        gaussianArithmeticRayValue l Δ u (((p.1*p.2*h:ℕ):ℝ)/(k:ℝ)) θ) :=
by
    classical
    have haux (q : Finset ℕ) : (∀ k ∈ q, 0 < k) →
        Summable (fun p : ℕ × ℕ => ∑ k ∈ q,
          (A h k * (p.2:ℂ)^(((2*l:ℝ):ℂ)-1)/(k:ℂ)^((2*l:ℝ):ℂ)) *
            gaussianArithmeticRayValue l Δ u (((p.1*p.2*h:ℕ):ℝ)/(k:ℝ)) θ) := by
      induction q using Finset.induction_on with
      | empty => intro _; simp
      | @insert k q hk ih =>
        intro hq
        have hk0 := hq k (Finset.mem_insert_self k q)
        have hq0 : ∀ j ∈ q, 0 < j := fun j hj => hq j (Finset.mem_insert_of_mem hj)
        simpa only [Finset.sum_insert hk] using
          (summable_weighted_gaussianArithmeticRayValue (A h k) l u hΔ hθ
            (hs h hh) hk0).add (ih hq0)
    exact haux t ht
  rw [Summable.tsum_finsetSum hsum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Summable.tsum_finsetSum (fun k hk =>
    summable_weighted_gaussianArithmeticRayValue (A h k) l u hΔ hθ (hs h hh) (ht k hk))]
  apply Finset.sum_congr rfl
  intro k hk
  exact tsum_weighted_gaussianArithmeticRayValue_eq_reduced
    (A h k) l u hΔ hθ (hs h hh) (ht k hk)

/-- The finite mollifier expression with the actual coefficients and reduced twists. -/
def mollifiedGaussianEstermannValue (σ y ε l Δ u θ : ℝ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ⌊y^(1+ε)⌋₊, ∑ k ∈ Finset.Icc 1 ⌊y^(1+ε)⌋₊,
    ((mollifierCoefficient σ y h * mollifierCoefficient σ y k) *
      (h:ℂ)^((1-2*l:ℝ):ℂ)/(k:ℂ)) * reducedGaussianEstermannPair l Δ u θ h k

/-- Exact actual Gaussian moment: both rational-twist rays and the original
negative signed pole residue. No analytic provider is assumed. -/
theorem mollifiedGaussianMoment_eq_estermann (σ ε u : ℝ) {y l Δ θ : ℝ}
    (hy : 0 < y) (hl : 0 < l) (hl' : l < 1) (hΔ : 0 < Δ)
    (hθ : θ ∈ Ioo 0 Real.pi) :
    (mollifiedGaussianMoment σ y ε l Δ u : ℂ) =
      mollifiedGaussianEstermannValue σ y ε l Δ u θ -
        ((2*Real.sqrt Real.pi/Δ:ℝ):ℂ)*mollifiedGaussianPoleCoeff σ y ε l Δ u := by
  rw [mollifiedGaussianMoment_eq_ray_series σ ε u hy hl hl' hΔ ⟨hθ.1.le,hθ.2⟩]
  congr 1
  exact finite_gaussianRay_sum_eq_estermann
    (Finset.Icc 1 ⌊y^(1+ε)⌋₊) (Finset.Icc 1 ⌊y^(1+ε)⌋₊)
    (fun h k => mollifierCoefficient σ y h * mollifierCoefficient σ y k)
    l u hΔ hθ (fun _ hh => (Finset.mem_Icc.mp hh).1)
      (fun _ hk => (Finset.mem_Icc.mp hk).1)

/-- Each individual Estermann ray is independent of its positive angle,
for arbitrary real l and u, not merely after pairing or forming the moment. -/
theorem gaussianEstermannRay_angle_independent {K : ℕ} [NeZero K] (H : ℕ)
    (l u : ℝ) {Δ θ₁ θ₂ : ℝ} (hΔ : 0 < Δ) (hH : 0 < H)
    (hθ₁ : θ₁ ∈ Ioo 0 Real.pi) (hθ₂ : θ₂ ∈ Ioo 0 Real.pi)
    {τ : ℤ} (hτ : τ = 1 ∨ τ = -1) :
    gaussianEstermannRay (K := K) H l Δ u θ₁ τ =
      gaussianEstermannRay (K := K) H l Δ u θ₂ τ := by
  rw [gaussianEstermannRay_eq_tsum H l u hΔ hH hθ₁ hτ,
    gaussianEstermannRay_eq_tsum H l u hΔ hH hθ₂ hτ]
  apply tsum_congr
  rintro ⟨m,n⟩
  by_cases hm : m = 0
  · simp [hm, gaussianEstermannRayTerm, estermannDampedTerm, estermannTerm]
  by_cases hn : n = 0
  · simp [hn, gaussianEstermannRayTerm, estermannDampedTerm, estermannTerm]
  simp_rw [gaussianEstermannRayTerm_eq H _ l Δ u _ _ τ hm hn, integral_const_mul]
  change (m:ℂ)^(-(((2*l:ℝ):ℂ)-1)) *
      gaussianRayIntegral l Δ u _ ((τ:ℝ)*θ₁) =
    (m:ℂ)^(-(((2*l:ℝ):ℂ)-1)) *
      gaussianRayIntegral l Δ u _ ((τ:ℝ)*θ₂)
  congr 1
  have ht : (τ:ℝ) = 1 ∨ (τ:ℝ) = -1 := by
    rcases hτ with rfl | rfl <;> norm_num
  exact gaussianRayIntegral_angle_independent l u hΔ (by positivity)
    ⟨hθ₁.1.le,hθ₁.2⟩ ⟨hθ₂.1.le,hθ₂.2⟩ ht

/-- Both reduced rays preserve their angle independently, including modulus one. -/
theorem reducedGaussianEstermannPair_angle_independent (l u : ℝ)
    {Δ θ₁ θ₂ : ℝ} (hΔ : 0 < Δ) (hθ₁ : θ₁ ∈ Ioo 0 Real.pi)
    (hθ₂ : θ₂ ∈ Ioo 0 Real.pi) (h k : ℕ) :
    reducedGaussianEstermannPair l Δ u θ₁ h k =
      reducedGaussianEstermannPair l Δ u θ₂ h k := by
  by_cases hp : 0 < h ∧ 0 < k
  · let : NeZero (k / h.gcd k) :=
      ⟨(Nat.div_gcd_pos_of_pos_right h hp.2).ne'⟩
    simp only [reducedGaussianEstermannPair, dif_pos hp]
    congr 1
    · exact gaussianEstermannRay_angle_independent _ l u hΔ
        (Nat.div_gcd_pos_of_pos_left k hp.1) hθ₁ hθ₂ (Or.inl rfl)
    · exact gaussianEstermannRay_angle_independent _ l u hΔ
        (Nat.div_gcd_pos_of_pos_left k hp.1) hθ₁ hθ₂ (Or.inr rfl)
  · simp only [reducedGaussianEstermannPair, dif_neg hp]

/-- The actual finite Estermann expression has no dependence on the chosen
positive angle, even outside the moment's 0 < l < 1 strip. -/
theorem mollifiedGaussianEstermannValue_angle_independent (σ y ε l u : ℝ)
    {Δ θ₁ θ₂ : ℝ} (hΔ : 0 < Δ) (hθ₁ : θ₁ ∈ Ioo 0 Real.pi)
    (hθ₂ : θ₂ ∈ Ioo 0 Real.pi) :
    mollifiedGaussianEstermannValue σ y ε l Δ u θ₁ =
      mollifiedGaussianEstermannValue σ y ε l Δ u θ₂ := by
  unfold mollifiedGaussianEstermannValue
  simp_rw [reducedGaussianEstermannPair_angle_independent l u hΔ hθ₁ hθ₂]

/-- Exact positive-angle boundary value. This takes a limit of the already
integrated damped expression; it does not interchange the series and integral
at the undamped angle zero. -/
theorem tendsto_mollifiedGaussianEstermannValue_zero (σ ε u : ℝ) {y l Δ : ℝ}
    (hy : 0 < y) (hl : 0 < l) (hl' : l < 1) (hΔ : 0 < Δ) :
    Tendsto (fun θ : ℝ => mollifiedGaussianEstermannValue σ y ε l Δ u θ)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((mollifiedGaussianMoment σ y ε l Δ u : ℂ) +
        ((2*Real.sqrt Real.pi/Δ:ℝ):ℂ)*mollifiedGaussianPoleCoeff σ y ε l Δ u)) := by
  have he : ∀ᶠ θ : ℝ in 𝓝[>] (0 : ℝ),
      mollifiedGaussianEstermannValue σ y ε l Δ u θ =
        (mollifiedGaussianMoment σ y ε l Δ u : ℂ) +
          ((2*Real.sqrt Real.pi/Δ:ℝ):ℂ)*mollifiedGaussianPoleCoeff σ y ε l Δ u := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds Real.pi_pos)] with θ hθ0 hθπ
    exact sub_eq_iff_eq_add.mp
      (mollifiedGaussianMoment_eq_estermann σ ε u hy hl hl' hΔ ⟨hθ0,hθπ⟩).symm
  exact tendsto_const_nhds.congr' (he.mono fun _ h => h.symm)

end RiemannResearch.Analysis.ConreyBaluyot
