import RiemannResearch.Probability.ZeroOrdinateInfiniteDPP
import RiemannResearch.Probability.DeterminantalMoments
import RiemannResearch.Probability.DeterminantalWeakConvergence
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The Fourier projection on fibres of actual zero ordinates

The countable zero-label DPP uses all integer height cutoffs. A frequency
dictionary containing every nonnegative multiple of a fixed short frequency
can interpolate the indicator of each ordinate fibre on its unit height
interval. This determines the projection on coordinate vectors, including
when a zero is multiple or has a horizontally reflected companion.

Lyons, *Determinantal probability measures*, §2,
https://doi.org/10.1007/s10240-003-0016-0, supplies the projection-kernel
interpretation. Ford, Meng and Zaharescu, https://arxiv.org/abs/1511.06814,
motivate the logarithmic dictionary. The finite interpolation argument below
uses the explicit cutoff features.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace RiemannResearch.Probability.DPP.ZeroOrdinateInfinite
open RiemannResearch.Analysis ActualZeroOrdinate ExhaustiveWalk ProjectionDPP

/-- All multiplicity labels at the ordinate of a given label. -/
def ordinateFiber (i : Site) : Finset Site :=
  ((bounded_sites_finite (ordinate i)).subset
    (show {j : Site | ordinate j = ordinate i} ⊆ {j | ordinate j ≤ ordinate i}
     from fun _ h => le_of_eq h)).toFinset

@[simp] theorem mem_ordinateFiber {i j : Site} :
    j ∈ ordinateFiber i ↔ ordinate j = ordinate i :=
  Set.Finite.mem_toFinset _

theorem ordinateFiber_card_pos (i : Site) : 0 < (ordinateFiber i).card :=
  Finset.card_pos.mpr ⟨i, mem_ordinateFiber.mpr rfl⟩

/-- The unnormalised constant coordinate vector on one ordinate fibre. -/
def fiberVector (i : Site) : Space := ∑ j ∈ ordinateFiber i, coordinate j

theorem inner_coordinate_fiberVector (j i : Site) :
    inner ℝ (coordinate j) (fiberVector i) =
      if ordinate j = ordinate i then 1 else 0 := by
  unfold fiberVector
  rw [inner_sum]
  simp [coordinate_inner]

/-- Coordinate inner products determine an element of the zero-label Hilbert space. -/
theorem coordinate_ext {x y : Space}
    (h : ∀ j, inner ℝ (coordinate j) x = inner ℝ (coordinate j) y) : x = y := by
  ext j
  simpa [coordinate, lp.inner_single_left] using h j

/-- Complex unit Fourier phase at a real frequency and ordinate. -/
def harmonicPhase (b t : ℝ) : ℂ :=
  Complex.exp (((b * t : ℝ) : ℂ) * Complex.I)

theorem harmonicPhase_pow (b t : ℝ) (m : ℕ) :
    harmonicPhase b t ^ m = harmonicPhase (m * b) t := by
  unfold harmonicPhase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem harmonicPhase_re (b t : ℝ) :
    (harmonicPhase b t).re = Real.cos (b * t) := by
  rw [harmonicPhase, Complex.exp_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]

theorem harmonicPhase_im (b t : ℝ) :
    (harmonicPhase b t).im = Real.sin (b * t) := by
  rw [harmonicPhase, Complex.exp_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]

private theorem harmonicPhase_sub (b t a : ℝ) :
    harmonicPhase b (t - a) = harmonicPhase b t / harmonicPhase b a := by
  unfold harmonicPhase
  rw [← Complex.exp_sub]
  congr 1
  push_cast
  ring

private theorem harmonicPhase_injOn (b a : ℝ) (hb : 0 < b) (hbπ : b ≤ 2 * Real.pi) :
    Set.InjOn (harmonicPhase b) (Set.Ioc a (a + 1)) := by
  intro t ht s hs he
  let a₀ := a + 1 / 2
  let z := fun u : ℝ => ((b * (u - a₀) : ℝ) : ℂ) * Complex.I
  have hz (u : ℝ) : (z u).im = b * (u - a₀) := by
    simp only [z, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
  have bounds (u : ℝ) (hu : u ∈ Set.Ioc a (a + 1)) :
      -Real.pi < (z u).im ∧ (z u).im ≤ Real.pi := by
    rw [hz]
    dsimp only [a₀]
    constructor
    · nlinarith only [mul_pos hb (sub_pos.mpr hu.1), hbπ]
    · nlinarith only [mul_nonneg hb.le (sub_nonneg.mpr hu.2), hbπ]
  have he' : harmonicPhase b (t - a₀) = harmonicPhase b (s - a₀) := by
    rw [harmonicPhase_sub, harmonicPhase_sub, he]
  have heq : z t = z s := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (bounds t ht).1 (bounds t ht).2 (bounds s hs).1 (bounds s hs).2 he'
  have him := congrArg Complex.im heq
  simp only [hz] at him
  have hts := mul_left_cancel₀ hb.ne' him
  linarith

private theorem cutoffVector_add (T : ℝ) (f g : ℝ → ℝ) :
    cutoffVector T (fun t => f t + g t) = cutoffVector T f + cutoffVector T g := by
  simp [cutoffVector, add_smul, Finset.sum_add_distrib]

private theorem cutoffVector_mul (T a : ℝ) (f : ℝ → ℝ) :
    cutoffVector T (fun t => a * f t) = a • cutoffVector T f := by
  simp [cutoffVector, Finset.smul_sum, smul_smul]

/-- A complete harmonic progression in a frequency dictionary. -/
def ContainsHarmonics (q : ℕ → ℝ) (b : ℝ) : Prop := ∀ m : ℕ, ∃ k, q k = m * b

private theorem cutoff_polynomial_mem_span (q : ℕ → ℝ) (b : ℝ)
    (hq : ContainsHarmonics q b) (n : ℕ) (P : Polynomial ℂ) :
    cutoffVector n (fun t => (P.eval (harmonicPhase b t)).re) ∈
      Submodule.span ℝ (Set.range (feature q)) := by
  let S := Submodule.span ℝ (Set.range (feature q))
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simpa only [Polynomial.eval_add, Complex.add_re, cutoffVector_add] using
      (S.add_mem hP hQ)
  | monomial m c =>
    obtain ⟨k, hk⟩ := hq m
    have cosMem : cutoffVector n (fun t => Real.cos (q k * t)) ∈ S :=
      Submodule.subset_span ⟨(n, k, false), rfl⟩
    have sinMem : cutoffVector n (fun t => Real.sin (q k * t)) ∈ S :=
      Submodule.subset_span ⟨(n, k, true), rfl⟩
    have he : (fun t => ((Polynomial.monomial m c).eval (harmonicPhase b t)).re) =
        fun t => c.re * Real.cos (q k * t) + (-c.im) * Real.sin (q k * t) := by
      funext t
      rw [Polynomial.eval_monomial, harmonicPhase_pow, ← hk, Complex.mul_re,
        harmonicPhase_re, harmonicPhase_im]
      ring
    rw [he, cutoffVector_add, cutoffVector_mul, cutoffVector_mul]
    exact S.add_mem (S.smul_mem _ cosMem) (S.smul_mem _ sinMem)

private def cardinalPolynomial (A : Finset ℂ) (z : ℂ) : Polynomial ℂ :=
  ∏ w ∈ A.erase z,
    Polynomial.C ((z - w)⁻¹) * (Polynomial.X - Polynomial.C w)

private theorem cardinalPolynomial_eval (A : Finset ℂ) (z t : ℂ) (ht : t ∈ A) :
    (cardinalPolynomial A z).eval t = if t = z then 1 else 0 := by
  classical
  simp only [cardinalPolynomial, Polynomial.eval_prod, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  split_ifs with h
  · subst t
    apply Finset.prod_eq_one
    intro w hw
    exact inv_mul_cancel₀ (sub_ne_zero.mpr (Finset.ne_of_mem_erase hw).symm)
  · exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨h, ht⟩) (by simp)

/-- Finite complex Fourier coefficients isolating one ordinate in a unit shell.
The coefficients give an exact cardinal interpolant on the prescribed sites. -/
theorem exists_shell_cardinal_fourier (n : ℕ) (A : Finset Site) (i : Site) (hi : i ∈ A)
    (hA : ∀ j ∈ A, ordinate j ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1)) :
    ∃ F : Finset ℕ, ∃ a : ℕ → ℂ, ∀ j ∈ A,
      (∑ m ∈ F, a m * harmonicPhase (m : ℝ) (ordinate j)) =
        if ordinate j = ordinate i then 1 else 0 := by
  classical
  let z := fun j : Site => harmonicPhase 1 (ordinate j)
  let P := cardinalPolynomial (A.image z) (z i)
  refine ⟨P.support, P.coeff, ?_⟩
  intro j hj
  have hjz : z j ∈ A.image z := Finset.mem_image_of_mem z hj
  have hiff : z j = z i ↔ ordinate j = ordinate i :=
    ⟨harmonicPhase_injOn 1 n zero_lt_one (by linarith [Real.pi_gt_three]) (hA j hj) (hA i hi),
     fun h => congrArg (harmonicPhase 1) h⟩
  have he := cardinalPolynomial_eval (A.image z) (z i) (z j) hjz
  change P.eval (z j) = _ at he
  simp only [hiff] at he
  rw [Polynomial.eval_eq_sum] at he
  simpa only [Polynomial.sum, z, harmonicPhase_pow, mul_one] using he

/-- The fibre indicator is already a finite linear combination of the cutoff
features. The bound on the step guarantees separation within each unit interval. -/
theorem fiberVector_mem_span_of_harmonics (q : ℕ → ℝ) (b : ℝ)
    (hb : 0 < b) (hbπ : b ≤ 2 * Real.pi) (hq : ContainsHarmonics q b) (i : Site) :
    fiberVector i ∈ Submodule.span ℝ (Set.range (feature q)) := by
  classical
  have hi : 0 < ordinate i := i.1.property.2
  let n := ⌈ordinate i⌉₊ - 1
  have hceil : 0 < ⌈ordinate i⌉₊ := Nat.ceil_pos.mpr hi
  have hn : n + 1 = ⌈ordinate i⌉₊ := by dsimp [n]; omega
  have hupper : ordinate i ≤ (n : ℝ) + 1 := by
    have hhn : (n : ℝ) + 1 = (⌈ordinate i⌉₊ : ℝ) := by exact_mod_cast hn
    rw [hhn]
    exact Nat.le_ceil _
  have hlower : (n : ℝ) < ordinate i := (Nat.lt_ceil.mp (by omega : n < ⌈ordinate i⌉₊))
  let B := (bounded_sites_finite ((n : ℝ) + 1)).toFinset.filter (fun j => (n : ℝ) < ordinate j)
  let A := B.image (fun j => harmonicPhase b (ordinate j))
  let z := harmonicPhase b (ordinate i)
  let P := cardinalPolynomial A z
  let f : ℝ → ℝ := fun t => (P.eval (harmonicPhase b t)).re
  have heq : cutoffVector (n + 1 : ℕ) f - cutoffVector n f = fiberVector i := by
    apply coordinate_ext
    intro j
    rw [inner_sub_right, cutoffVector_coordinate, cutoffVector_coordinate,
      inner_coordinate_fiberVector, Nat.cast_add, Nat.cast_one]
    by_cases hj : ordinate j ≤ (n : ℝ)
    · have hne : ordinate j ≠ ordinate i := ne_of_lt (hj.trans_lt hlower)
      simp [hj, (by linarith : ordinate j ≤ (n : ℝ) + 1), hne]
    by_cases hu : ordinate j ≤ (n : ℝ) + 1
    · have hA : harmonicPhase b (ordinate j) ∈ A :=
        Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr
          ⟨(Set.Finite.mem_toFinset _).mpr hu, lt_of_not_ge hj⟩, rfl⟩
      have hinj : harmonicPhase b (ordinate j) = z ↔ ordinate j = ordinate i :=
        ⟨harmonicPhase_injOn b n hb hbπ ⟨lt_of_not_ge hj, hu⟩ ⟨hlower, hupper⟩,
          fun h => congrArg _ h⟩
      simp only [if_pos hu, if_neg hj, sub_zero, f, P, cardinalPolynomial_eval _ _ _ hA]
      by_cases h : ordinate j = ordinate i
      · rw [if_pos (hinj.mpr h), if_pos h, Complex.one_re]
      · rw [if_neg (fun he => h (hinj.mp he)), if_neg h, Complex.zero_re]
    · have hne : ordinate j ≠ ordinate i := fun h => hu (h ▸ hupper)
      simp [hu, hj, hne]
  rw [← heq]
  exact Submodule.sub_mem _
    (cutoff_polynomial_mem_span q b hq (n + 1) P) (cutoff_polynomial_mem_span q b hq n P)

/-- The standard logarithmic dictionary contains all dyadic harmonics. -/
theorem logarithmic_containsHarmonics :
    ContainsHarmonics (fun k => Real.log ((k : ℝ) + 1)) (Real.log 2) := by
  intro m
  refine ⟨2 ^ m - 1, ?_⟩
  have hp : 0 < 2 ^ m := pow_pos (by decide) m
  have h : (2 ^ m - 1 : ℕ) + 1 = 2 ^ m := by omega
  have hcast : (((2 ^ m - 1 : ℕ) : ℝ) + 1) = (2 : ℝ) ^ m := by exact_mod_cast h
  change Real.log (((2 ^ m - 1 : ℕ) : ℝ) + 1) = _
  rw [hcast, Real.log_pow]


private theorem projection_eq_of_le_closedSpace (q : ℕ → ℝ) (S : Submodule ℝ Space)
    [S.HasOrthogonalProjection] (hS : S ≤ closedSpace q) {i j : Site}
    (hij : ordinate i = ordinate j) :
    S.starProjection (coordinate i) = S.starProjection (coordinate j) := by
  have hzero : (closedSpace q).starProjection (coordinate i - coordinate j) = 0 := by
    rw [map_sub, collision_projection_eq q hij, sub_self]
  have horth := (closedSpace q).starProjection_apply_eq_zero_iff.mp hzero
  have hsmall : coordinate i - coordinate j ∈ Sᗮ :=
    Submodule.orthogonal_le hS horth
  simpa only [map_sub, sub_eq_zero] using S.starProjection_apply_eq_zero_iff.mpr hsmall

private theorem projection_eq_fiberAverage (q : ℕ → ℝ) (S : Submodule ℝ Space)
    [S.HasOrthogonalProjection] (hS : S ≤ closedSpace q) (i : Site)
    (hi : fiberVector i ∈ S) :
    S.starProjection (coordinate i) = ((ordinateFiber i).card : ℝ)⁻¹ • fiberVector i := by
  have hcard : ((ordinateFiber i).card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ordinateFiber_card_pos i).ne'
  have he : fiberVector i = ((ordinateFiber i).card : ℝ) • S.starProjection (coordinate i) := by
    calc
      fiberVector i = S.starProjection (fiberVector i) :=
        ((Submodule.starProjection_eq_self_iff (K := S)).mpr hi).symm
      _ = ∑ j ∈ ordinateFiber i, S.starProjection (coordinate j) := by
        rw [fiberVector, map_sum]
      _ = ∑ _j ∈ ordinateFiber i, S.starProjection (coordinate i) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact projection_eq_of_le_closedSpace q S hS (mem_ordinateFiber.mp hj)
      _ = _ := by simp only [Finset.sum_const, Nat.cast_smul_eq_nsmul]
  conv_rhs => rw [he, smul_smul, inv_mul_cancel₀ hcard, one_smul]

/-- Every coordinate projects to the uniform vector on its complete ordinate fibre. -/
theorem starProjection_coordinate_of_harmonics (q : ℕ → ℝ) (b : ℝ)
    (hb : 0 < b) (hbπ : b ≤ 2 * Real.pi) (hq : ContainsHarmonics q b) (i : Site) :
    (closedSpace q).starProjection (coordinate i) =
      ((ordinateFiber i).card : ℝ)⁻¹ • fiberVector i :=
  projection_eq_fiberAverage q _ le_rfl i
    ((Submodule.le_topologicalClosure _) (fiberVector_mem_span_of_harmonics q b hb hbπ hq i))

private theorem kernelOfSpace_eq_inner_coordinate (S : Submodule ℝ Space)
    [S.HasOrthogonalProjection] (i j : Site) :
    kernelOfSpace S i j = inner ℝ (coordinate j) (S.starProjection (coordinate i)) := by
  have hz := (S.mem_orthogonal _).mp (Submodule.sub_starProjection_mem_orthogonal (coordinate j))
    _ (S.starProjection_apply_mem (coordinate i))
  rw [inner_sub_right, sub_eq_zero] at hz
  exact hz.symm.trans (real_inner_comm _ _)

/-- The limiting kernel is a direct sum of uniform rank-one fibre kernels. -/
theorem limitingKernel_of_harmonics (q : ℕ → ℝ) (b : ℝ)
    (hb : 0 < b) (hbπ : b ≤ 2 * Real.pi) (hq : ContainsHarmonics q b) (i j : Site) :
    limitingKernel q i j =
      if ordinate j = ordinate i then ((ordinateFiber i).card : ℝ)⁻¹ else 0 := by
  rw [limitingKernel, kernelOfSpace_eq_inner_coordinate, starProjection_coordinate_of_harmonics
    q b hb hbπ hq, inner_smul_right, inner_coordinate_fiberVector]
  split_ifs <;> simp

/-- Closed-form kernel for the log-integer dictionary used in the FMZ construction. -/
theorem logarithmic_limitingKernel (i j : Site) :
    limitingKernel (fun k => Real.log ((k : ℝ) + 1)) i j =
      if ordinate j = ordinate i then ((ordinateFiber i).card : ℝ)⁻¹ else 0 := by
  apply limitingKernel_of_harmonics _ (Real.log 2) (Real.log_pos (by norm_num)) _
    logarithmic_containsHarmonics
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2), Real.pi_gt_three]

/-- Fibre inclusion alone determines the whole limiting kernel. -/
theorem limitingKernel_eq_logarithmic_of_fiber_mem (q : ℕ → ℝ)
    (h : ∀ i, fiberVector i ∈ closedSpace q) :
    limitingKernel q = limitingKernel (fun k => Real.log ((k : ℝ) + 1)) := by
  funext i j
  rw [logarithmic_limitingKernel, limitingKernel, kernelOfSpace_eq_inner_coordinate,
    projection_eq_fiberAverage q _ le_rfl i (h i), inner_smul_right, inner_coordinate_fiberVector]
  split_ifs <;> simp

/-- Every dictionary containing all fibre indicators in its closed span
has exactly the same Boolean probability law as the full log-integer list. -/
theorem limitingLaw_eq_logarithmic_of_fiber_mem (q : ℕ → ℝ)
    (h : ∀ i, fiberVector i ∈ closedSpace q) :
    limitingLaw q = limitingLaw (fun k => Real.log ((k : ℝ) + 1)) := by
  apply boolLaw_unique _ (limitingLaw_isDPP _)
  simpa only [limitingKernel_eq_logarithmic_of_fiber_mem q h] using limitingLaw_isDPP q

/-- Exact eventual stabilization of an entire kernel row on every fixed label.
The feature index may depend on the ordinate. -/
theorem eventually_finiteKernel_row_eq_of_fiber_span (q : ℕ → ℝ) (i : Site)
    (h : fiberVector i ∈ Submodule.span ℝ (Set.range (feature q))) :
    ∀ᶠ n : ℕ in atTop, ∀ j : Site, finiteKernel q n i j = limitingKernel q i j := by
  have hf := h
  rw [← iSup_walkSpan (feature q) enumeration enumeration_surjective] at hf
  obtain ⟨N, hN⟩ := (Submodule.mem_iSup_of_directed _ (walkSpan_mono _ _).directed_le).mp hf
  filter_upwards [eventually_ge_atTop N] with n hn
  have hs : finiteSpace q n ≤ closedSpace q :=
    (walkSpan_le _ _ _).trans (Submodule.le_topologicalClosure _)
  have hp := projection_eq_fiberAverage q (finiteSpace q n) hs i ((walkSpan_mono _ _ hn) hN)
  intro j
  rw [finiteKernel, limitingKernel, kernelOfSpace_eq_inner_coordinate,
    kernelOfSpace_eq_inner_coordinate, hp,
    projection_eq_fiberAverage q _ le_rfl i ((Submodule.le_topologicalClosure _) h)]

/-- A complete short harmonic progression gives eventual fixed-row equality. -/
theorem eventually_finiteKernel_row_eq_of_harmonics (q : ℕ → ℝ) (b : ℝ)
    (hb : 0 < b) (hbπ : b ≤ 2 * Real.pi) (hq : ContainsHarmonics q b) (i : Site) :
    ∀ᶠ n : ℕ in atTop, ∀ j : Site, finiteKernel q n i j = limitingKernel q i j :=
  eventually_finiteKernel_row_eq_of_fiber_span q i
    (fiberVector_mem_span_of_harmonics q b hb hbπ hq i)

private theorem ordinateFiber_eq_of_ordinate_eq {i j : Site} (h : ordinate i = ordinate j) :
    ordinateFiber i = ordinateFiber j := by
  ext k
  simp [h]

/-- Joint selection of prescribed labels at distinct ordinates factors at every order. -/
theorem inclusion_of_distinct_ordinates (q : ℕ → ℝ) (b : ℝ)
    (hb : 0 < b) (hbπ : b ≤ 2 * Real.pi) (hq : ContainsHarmonics q b)
    (m : ℕ) (e : Fin m ↪ Site) (he : Function.Injective (fun k => ordinate (e k))) :
    (limitingLaw q).real {x | ∀ k, x (e k) = true} =
      ∏ k, ((ordinateFiber (e k)).card : ℝ)⁻¹ := by
  have hprob : (limitingLaw q).real {x | ∀ k, x (e k) = true} =
      Matrix.det (Matrix.of (fun k l : Fin m => limitingKernel q (e k) (e l))) :=
    (limitingLaw_isDPP q).correlation m e
  rw [hprob]
  have hmatrix : Matrix.of (fun k l : Fin m => limitingKernel q (e k) (e l)) =
      Matrix.diagonal (fun k => ((ordinateFiber (e k)).card : ℝ)⁻¹) := by
    ext k l
    rw [Matrix.of_apply, limitingKernel_of_harmonics q b hb hbπ hq, Matrix.diagonal_apply]
    by_cases h : k = l
    · subst l
      simp
    · have hf : ordinate (e l) ≠ ordinate (e k) := fun ha => h (he ha).symm
      simp [hf, h]
  rw [hmatrix, Matrix.det_diagonal]

/-- Any finite prescribed set that repeats an ordinate has inclusion probability zero. -/
theorem inclusion_eq_zero_of_repeated_ordinate (q : ℕ → ℝ) (m : ℕ)
    (e : Fin m ↪ Site) {k l : Fin m} (hkl : k ≠ l) (he : ordinate (e k) = ordinate (e l)) :
    (limitingLaw q).real {x | ∀ a, x (e a) = true} = 0 := by
  have hle : (limitingLaw q).real {x | ∀ a, x (e a) = true} ≤
      (limitingLaw q).real {x | x (e k) = true ∧ x (e l) = true} :=
    measureReal_mono (fun _ h => ⟨h k, h l⟩)
  exact le_antisymm (hle.trans_eq (collision_pair_probability_zero q (e.injective.ne hkl) he))
    ENNReal.toReal_nonneg


/-- Almost surely every actual positive ordinate has exactly one selected label. -/
theorem exactly_one_per_ordinate_ae (q : ℕ → ℝ) (b : ℝ)
    (hb : 0 < b) (hbπ : b ≤ 2 * Real.pi) (hq : ContainsHarmonics q b) :
    ∀ᵐ x ∂limitingLaw q, ∀ i : Site, ∃! j : Site, ordinate j = ordinate i ∧ x j = true := by
  classical
  apply ae_all_iff.mpr
  intro i
  let X := fun x : Site → Bool => {j | x j = true}
  let e : ↥(ordinateFiber i) → Site := Subtype.val
  let C := windowCount X e
  have hD := limitingLaw_isDPP q
  have hdiag (j : ↥(ordinateFiber i)) :
      limitingKernel q (e j) (e j) = ((ordinateFiber i).card : ℝ)⁻¹ := by
    rw [limitingKernel_of_harmonics q b hb hbπ hq, if_pos rfl]
    rw [ordinateFiber_eq_of_ordinate_eq (mem_ordinateFiber.mp j.property)]
  have hcard : ((ordinateFiber i).card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ordinateFiber_card_pos i).ne'
  have hmean : (∫ x, C x ∂limitingLaw q) = 1 := by
    rw [show C = windowCount X e from rfl, hD.expected_windowCount e]
    simp [hdiag, hcard]
  have hcount (x : Site → Bool) (hs : Set.InjOn ordinate (X x)) :
      C x = if ∃ j : ↥(ordinateFiber i), x j.val = true then 1 else 0 := by
    by_cases hex : ∃ j : ↥(ordinateFiber i), x j.val = true
    · rw [if_pos hex]
      obtain ⟨j, hj⟩ := hex
      change (∑ k : ↥(ordinateFiber i), occupancyIndicator X (e k) x) = 1
      rw [Finset.sum_eq_single j]
      · simp [occupancyIndicator, X, e, hj]
      · intro k _ hkj
        have hk : x k.val ≠ true := by
          intro hk
          apply hkj
          exact Subtype.ext (hs hk hj ((mem_ordinateFiber.mp k.property).trans
            (mem_ordinateFiber.mp j.property).symm))
        simp [occupancyIndicator, X, e, hk]
      · simp
    · rw [if_neg hex]
      apply Finset.sum_eq_zero
      intro j _
      have hj : x j.val ≠ true := fun h => hex ⟨j, h⟩
      simp [occupancyIndicator, X, e, hj]
  have hnonneg : 0 ≤ᵐ[limitingLaw q] (fun x => 1 - C x) := by
    filter_upwards [ordinate_injective_ae q] with x hx
    rw [hcount x hx]
    split_ifs <;> norm_num
  have hg : Integrable (fun x => 1 - C x) (limitingLaw q) :=
    (integrable_const (1 : ℝ)).sub (hD.windowCount_integrable e)
  have hzero : (∫ x, (1 - C x) ∂limitingLaw q) = 0 := by
    rw [integral_sub (integrable_const _) (hD.windowCount_integrable e), hmean]
    simp
  have he := (integral_eq_zero_iff_of_nonneg_ae hnonneg hg).mp hzero
  filter_upwards [he, ordinate_injective_ae q] with x hx hs
  change 1 - C x = 0 at hx
  rw [hcount x hs] at hx
  by_cases hex : ∃ j : ↥(ordinateFiber i), x j.val = true
  · obtain ⟨j, hj⟩ := hex
    exact ⟨j, ⟨mem_ordinateFiber.mp j.property, hj⟩, fun k hk =>
      hs hk.2 hj (hk.1.trans (mem_ordinateFiber.mp j.property).symm)⟩
  · simp [hex] at hx

/-- The pushforward selected set has exactly the deterministic ordinate support. -/
theorem selected_ordinate_image_ae (q : ℕ → ℝ) (b : ℝ)
    (hb : 0 < b) (hbπ : b ≤ 2 * Real.pi) (hq : ContainsHarmonics q b) :
    ∀ᵐ x ∂limitingLaw q, ordinate '' {j | x j = true} = Set.range ordinate := by
  filter_upwards [exactly_one_per_ordinate_ae q b hb hbπ hq] with x hx
  ext t
  constructor
  · rintro ⟨j, _, rfl⟩
    exact ⟨j, rfl⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨j, hj, _⟩ := hx i
    exact ⟨j, hj.2, hj.1⟩

/-- Every actual label has a positive inclusion probability for every
dictionary. At an integer cutoff above the label, the sine and cosine
features of even one frequency cannot both vanish. -/
theorem limitingKernel_diagonal_pos (q : ℕ → ℝ) (i : Site) : 0 < limitingKernel q i i := by
  have hnon := ((limitingLaw_isDPP q).diagonal_bounds i).1
  by_contra hn
  have hzero : limitingKernel q i i = 0 := le_antisymm (le_of_not_gt hn) hnon
  have hp : (closedSpace q).starProjection (coordinate i) = 0 := by
    apply norm_eq_zero.mp
    apply sq_eq_zero_iff.mp
    simpa only [limitingKernel, kernelOfSpace, kernel_diagonal] using hzero
  have ho := (closedSpace q).starProjection_apply_eq_zero_iff.mp hp
  let n := ⌈ordinate i⌉₊
  have hT : ordinate i ≤ (n : ℝ) := Nat.le_ceil _
  have gone (a : FeatureIndex) : inner ℝ (coordinate i) (feature q a) = 0 := by
    rw [real_inner_comm]
    apply ((closedSpace q).mem_orthogonal _).mp ho
    apply (Submodule.le_topologicalClosure _)
    exact Submodule.subset_span ⟨a, rfl⟩
  have hc := gone (n, 0, false)
  have hs := gone (n, 0, true)
  simp only [feature, Bool.false_eq_true, if_false, cutoffVector_coordinate, if_pos hT] at hc
  simp only [feature, if_true, cutoffVector_coordinate, if_pos hT] at hs
  have hsc := Real.sin_sq_add_cos_sq (q 0 * ordinate i)
  rw [hc, hs] at hsc
  norm_num at hsc

/-- The finite-feature laws converge weakly on the full Boolean product
for every dictionary, with its product topology. -/
theorem finiteLaw_weak_tendsto (q : ℕ → ℝ) :
    Tendsto (fun n => (⟨finiteLaw q n, inferInstance⟩ : ProbabilityMeasure (Site → Bool))) atTop
      (@nhds (ProbabilityMeasure (Site → Bool)) _ ⟨limitingLaw q, inferInstance⟩) :=
  tendsto_boolLaw_of_kernel _ _ _ _ (finiteLaw_isDPP q) (limitingLaw_isDPP q) (kernel_tendsto q)

/-- Every finite marginal stabilizes exactly once the complete vectors
of its represented ordinate fibres belong to the algebraic feature span. -/
theorem finite_marginal_eventually_eq_of_fiber_span (q : ℕ → ℝ) (I : Finset Site)
    (h : ∀ i ∈ I, fiberVector i ∈ Submodule.span ℝ (Set.range (feature q))) :
    ∀ᶠ n : ℕ in atTop, (finiteLaw q n).map I.restrict = (limitingLaw q).map I.restrict := by
  classical
  have hrow : ∀ᶠ n : ℕ in atTop, ∀ i : I, ∀ j : Site,
      finiteKernel q n i.val j = limitingKernel q i.val j :=
    eventually_all.mpr (fun i =>
      eventually_finiteKernel_row_eq_of_fiber_span q i.val (h i.val i.property))
  have hr : Measurable (I.restrict : (Site → Bool) → (I → Bool)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply i.val
  filter_upwards [hrow] with n hn
  let : IsProbabilityMeasure ((finiteLaw q n).map I.restrict) :=
    Measure.isProbabilityMeasure_map hr.aemeasurable
  let : IsProbabilityMeasure ((limitingLaw q).map I.restrict) :=
    Measure.isProbabilityMeasure_map hr.aemeasurable
  apply boolMeasure_eq_of_isDPP _ _ (fun i j : I => limitingKernel q i.val j.val)
    _ ((limitingLaw_isDPP q).restrict_bool I)
  simpa only [hn] using (finiteLaw_isDPP q n).restrict_bool I

/-- Exact finite marginal stabilization for a dictionary containing a full
short harmonic progression. -/
theorem finite_marginal_eventually_eq (q : ℕ → ℝ) (b : ℝ)
    (hb : 0 < b) (hbπ : b ≤ 2 * Real.pi) (hq : ContainsHarmonics q b) (I : Finset Site) :
    ∀ᶠ n : ℕ in atTop, (finiteLaw q n).map I.restrict = (limitingLaw q).map I.restrict :=
  finite_marginal_eventually_eq_of_fiber_span q I
    (fun i _ => fiberVector_mem_span_of_harmonics q b hb hbπ hq i)

end RiemannResearch.Probability.DPP.ZeroOrdinateInfinite
