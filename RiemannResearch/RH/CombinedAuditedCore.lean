/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Kernel-checked cores from `combined_audited_manuscript(4).pdf`

The manuscript mixes finite algebra, analytic number theory, probability,
operator theory, and conjectural geometric bridges.  This module formalizes
the portions whose mathematical content can be stated and proved with the
present repository and mathlib.

Deep analytic or geometric assertions are not introduced as axioms.  For the
conditional RH arguments, the substantial missing construction is exposed as
an explicit hypothesis or a typed target.  This proves the implication while
preserving the distinction between a reduction and a proof of RH.

Source: Christian Noack, `combined_audited_manuscript(4).pdf`, August 2026.
-/

namespace RiemannResearch.RH.CombinedAuditedCore

open Filter
open scoped BigOperators

noncomputable section

/-! ## Theorem 2.1: prime-exponent coordinates -/

/-- A nonzero natural number is reconstructed from its finite prime
factorization.  This is the kernel-checked arithmetic core of Theorem 2.1. -/
theorem primeExponent_reconstructs {n : ℕ} (hn : n ≠ 0) :
    n.factorization.prod (fun p e => p ^ e) = n :=
  Nat.prod_factorization_pow_eq_self hn

/-- Multiplication adds prime-exponent coordinates. -/
theorem primeExponent_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    (m * n).factorization = m.factorization + n.factorization :=
  Nat.factorization_mul hm hn

/-- Divisibility is coordinatewise comparison of prime exponents. -/
theorem primeExponent_le_iff_dvd {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    m.factorization ≤ n.factorization ↔ m ∣ n :=
  Nat.factorization_le_iff_dvd hm hn

/-! ## Theorem 2.3: directed finite differences -/

/-- The forward difference of a sequence. -/
def forwardDifference {A : Type*} [Sub A] (s : ℕ → A) (n : ℕ) : A :=
  s n - s (n + 1)

/-- Finite differences recover interval masses by exact telescoping.  This is
the one-coordinate algebraic core of directed cylinder inversion. -/
theorem sum_forwardDifference {A : Type*} [AddCommGroup A]
    (s : ℕ → A) (a n : ℕ) :
    (∑ k in Finset.range n, forwardDifference s (a + k)) =
      s a - s (a + n) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [forwardDifference, Nat.add_succ]
      abel

/-! ## Propositions 3.1 and 3.2: represented orbits and the one-prime obstruction -/

/-- The first isomorphism theorem identifies a represented linear orbit with
the source modulo the annihilator/kernel. -/
noncomputable def representedOrbitEquivRange
    {R M N : Type*} [Ring R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    (M ⧸ LinearMap.ker f) ≃ₗ[R] LinearMap.range f :=
  f.quotKerEquivRange

/-- The Hochschild boundary of an elementary one-chain, written in degree
zero. -/
def hochschildBoundaryOne {A : Type*} [Ring A] (a b : A) : A :=
  a * b - b * a

/-- In a commutative algebra every degree-one Hochschild boundary vanishes. -/
theorem hochschildBoundaryOne_eq_zero
    {A : Type*} [CommRing A] (a b : A) :
    hochschildBoundaryOne a b = 0 := by
  simp [hochschildBoundaryOne, mul_comm]

/-- Consequently a nonzero Boolean edge `u - 1` cannot be the boundary of a
degree-one chain in a commutative Laurent algebra. -/
theorem onePrimeHochschildObstruction
    {A : Type*} [CommRing A] {u : A} (hu : u ≠ 1) :
    ¬ ∃ a b : A, hochschildBoundaryOne a b = u - 1 := by
  rintro ⟨a, b, hab⟩
  have huzero : u - 1 = 0 := by
    rw [← hab, hochschildBoundaryOne_eq_zero]
  exact hu (sub_eq_zero.mp huzero)

/-! ## Theorems 8.1--8.3: finite quadratic-form cores -/

/-- The scalar gluing penalty appearing after blockwise completion of
squares. -/
def scalarGluingPenalty {ι : Type*} (s : Finset ι)
    (G β : ι → ℝ) (b : ℝ) : ℝ :=
  ∑ i in s, G i * (b - β i) ^ 2

/-- A scalar blockwise loss splits into the sum of local optima and one common
gluing penalty. -/
theorem scalarOptimizerAwareTotalVariance
    {ι : Type*} (s : Finset ι) (ρ G β : ι → ℝ) (b : ℝ) :
    (∑ i in s, (ρ i + G i * (b - β i) ^ 2)) =
      (∑ i in s, ρ i) + scalarGluingPenalty s G β b := by
  simp [scalarGluingPenalty, Finset.sum_add_distrib]

/-- Positive block weights make the gluing penalty nonnegative. -/
theorem scalarGluingPenalty_nonneg
    {ι : Type*} {s : Finset ι} {G β : ι → ℝ} {b : ℝ}
    (hG : ∀ i ∈ s, 0 ≤ G i) :
    0 ≤ scalarGluingPenalty s G β b := by
  exact Finset.sum_nonneg fun i hi =>
    mul_nonneg (hG i hi) (sq_nonneg (b - β i))

/-- With strictly positive weights, the scalar gluing penalty vanishes exactly
when one common optimizer works on every block. -/
theorem scalarGluingPenalty_eq_zero_iff
    {ι : Type*} {s : Finset ι} {G β : ι → ℝ} {b : ℝ}
    (hG : ∀ i ∈ s, 0 < G i) :
    scalarGluingPenalty s G β b = 0 ↔
      ∀ i ∈ s, b = β i := by
  constructor
  · intro h i hi
    have hterm :
        G i * (b - β i) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j hj => mul_nonneg (hG j hj).le (sq_nonneg (b - β j)))).1 h i hi
    have hsquare : (b - β i) ^ 2 = 0 :=
      (mul_eq_zero.mp hterm).resolve_left (hG i hi).ne'
    have hsub : b - β i = 0 := by
      nlinarith
    exact sub_eq_zero.mp hsub
  · intro h
    apply Finset.sum_eq_zero
    intro i hi
    simp [scalarGluingPenalty, h i hi]

/-- Scalar form of the head-tail Schur/Woodbury completion. -/
theorem scalarHeadTailSchurIdentity (m l z : ℝ) :
    (m - l * z) ^ 2 + z ^ 2 =
      (1 + l ^ 2) * (z - l * m / (1 + l ^ 2)) ^ 2 +
        m ^ 2 / (1 + l ^ 2) := by
  have hden : 1 + l ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg l]
  field_simp [hden]
  ring

/-- The Schur value is a lower bound for every scalar lift. -/
theorem scalarHeadTailSchur_lowerBound (m l z : ℝ) :
    m ^ 2 / (1 + l ^ 2) ≤ (m - l * z) ^ 2 + z ^ 2 := by
  rw [scalarHeadTailSchurIdentity]
  have hcoef : 0 ≤ 1 + l ^ 2 := by
    nlinarith [sq_nonneg l]
  exact le_add_of_nonneg_left
    (mul_nonneg hcoef (sq_nonneg (z - l * m / (1 + l ^ 2))))

/-- A scalar linear constraint has a unique feasible lift; its weighted energy
is the corresponding dual-frame value. -/
theorem scalarMinimumEnergyDualFrame
    {r b S z : ℝ} (hr : 0 < r) (hb : b ≠ 0) (hconstraint : b * z = S) :
    z = S / b ∧ r * z ^ 2 = r * (S / b) ^ 2 := by
  have hz : z = S / b := by
    apply (eq_div_iff hb).2
    simpa [mul_comm] using hconstraint
  subst z
  exact ⟨rfl, rfl⟩

/-! ## Theorems 9.1 and 9.2: the pointed absolute point and shift exactness -/

/-- The two-element pointed set used as the algebraic core of the manuscript's
`F₁` model. -/
inductive FOne
  | zero
  | one
  deriving DecidableEq, Repr

instance : Zero FOne := ⟨FOne.zero⟩
instance : One FOne := ⟨FOne.one⟩

/-- The unique candidate map from `FOne` to a pointed target. -/
def fOneMap {A : Type*} [Zero A] [One A] : FOne → A
  | .zero => 0
  | .one => 1

/-- A map from `FOne` preserving the two distinguished points is forced to be
`fOneMap`.  This is the initiality core, without importing an `F₁` category. -/
theorem fOneMap_unique
    {A : Type*} [Zero A] [One A] (f : FOne → A)
    (hzero : f 0 = 0) (hone : f 1 = 1) :
    f = fOneMap := by
  funext x
  cases x with
  | zero => simpa [fOneMap] using hzero
  | one => simpa [fOneMap] using hone

/-- The unilateral shift on sequences. -/
def unilateralShift {A : Type*} [Zero A] (a : ℕ → A) : ℕ → A
  | 0 => 0
  | n + 1 => a n

/-- The unilateral shift is injective. -/
theorem unilateralShift_injective
    {A : Type*} [Zero A] :
    Function.Injective (unilateralShift : (ℕ → A) → (ℕ → A)) := by
  intro a b hab
  funext n
  have h := congrFun hab (n + 1)
  simpa [unilateralShift] using h

/-- A sequence is in the range of the unilateral shift exactly when its
zeroth coordinate vanishes. -/
theorem exists_unilateralShift_iff
    {A : Type*} [Zero A] (b : ℕ → A) :
    (∃ a : ℕ → A, unilateralShift a = b) ↔ b 0 = 0 := by
  constructor
  · rintro ⟨a, rfl⟩
    rfl
  · intro hb
    refine ⟨fun n => b (n + 1), ?_⟩
    funext n
    cases n with
    | zero => simpa [unilateralShift] using hb.symm
    | succ n => simp [unilateralShift]

/-! ## Theorem 10.2: finite Hardy--Ruelle telescoping -/

/-- The finite algebraic telescope underlying the local Hardy--Ruelle
calculation. -/
theorem finiteGeometricTelescope
    {R : Type*} [CommRing R] (a : R) (n : ℕ) :
    (1 - a) * (∑ k in Finset.range n, a ^ k) = 1 - a ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      ring

/-! ## Theorems 12.4, 12.6, and 12.16: finite positivity obstructions -/

/-- The two-evaluation functional-equation block. -/
def functionalEquationPairForm (a b : ℂ) : ℝ :=
  2 * (a * b).re

/-- The functional-equation block has a positive direction. -/
theorem functionalEquationPairForm_pos :
    0 < functionalEquationPairForm 1 1 := by
  norm_num [functionalEquationPairForm]

/-- The same block has a negative direction, so symmetry alone is not a
positive Hermitian polarization. -/
theorem functionalEquationPairForm_neg :
    functionalEquationPairForm 1 (-1) < 0 := by
  norm_num [functionalEquationPairForm]

/-- A scalar correction smaller than an existing negative direction cannot
make that direction nonnegative. -/
theorem scalarRenormalizationCannotRemoveNegative
    {q c : ℝ} (hq : q < 0) (hc : |c| < -q) :
    q + c < 0 := by
  have hcle : c ≤ |c| := le_abs_self c
  linarith

/-! ## Theorems 12.17 and 12.18: rigorous conditional RH implications -/

/-- The scalar eigenvector calculation in the Deninger polarization argument. -/
theorem deningerEigenvalue_onCriticalLine
    {ρ : ℂ} {mass : ℝ} (hmass : 0 < mass)
    (hpolarization : 2 * ρ.re * mass = mass) :
    ρ.re = (1 : ℝ) / 2 := by
  nlinarith

/-- A fully explicit conditional form of the Deninger implication.  The
zero-independent cohomology and determinant transfer remain hypotheses. -/
theorem deningerPolarizationImplication
    (isZero : ℂ → Prop)
    (criticalLineImpliesRH :
      (∀ ρ, isZero ρ → ρ.re = (1 : ℝ) / 2) → RiemannResearch.RH.Statement)
    (hpolarization :
      ∀ ρ, isZero ρ →
        ∃ mass : ℝ, 0 < mass ∧ 2 * ρ.re * mass = mass) :
    RiemannResearch.RH.Statement := by
  apply criticalLineImpliesRH
  intro ρ hρ
  obtain ⟨mass, hmass, hpair⟩ := hpolarization ρ hρ
  exact deningerEigenvalue_onCriticalLine hmass hpair

/-- Imaginary part of the second-order spectral parameter `ρ(1-ρ)`. -/
theorem secondOrder_im (ρ : ℂ) :
    (ρ * (1 - ρ)).im = ρ.im * (1 - 2 * ρ.re) := by
  rw [Complex.mul_im]
  simp
  ring

/-- A nonreal complex number whose second-order spectral parameter is real
lies on the critical line. -/
theorem criticalLine_of_secondOrder_real
    {ρ : ℂ} (hnonreal : ρ.im ≠ 0)
    (hreal : (ρ * (1 - ρ)).im = 0) :
    ρ.re = (1 : ℝ) / 2 := by
  rw [secondOrder_im] at hreal
  have hfactor : 1 - 2 * ρ.re = 0 :=
    (mul_eq_zero.mp hreal).resolve_left hnonreal
  linarith

/-- A fully explicit conditional form of the arithmetic second-order Selberg
target.  Self-adjointness is used only through reality of the spectral value. -/
theorem arithmeticSecondOrderImplication
    (isZero : ℂ → Prop)
    (criticalLineImpliesRH :
      (∀ ρ, isZero ρ → ρ.re = (1 : ℝ) / 2) → RiemannResearch.RH.Statement)
    (hnonreal : ∀ ρ, isZero ρ → ρ.im ≠ 0)
    (hspectralReal : ∀ ρ, isZero ρ → (ρ * (1 - ρ)).im = 0) :
    RiemannResearch.RH.Statement := by
  apply criticalLineImpliesRH
  intro ρ hρ
  exact criticalLine_of_secondOrder_real (hnonreal ρ hρ)
    (hspectralReal ρ hρ)

/-! ## Proposition 12.19 and Conjecture 12.20: positivity bridges -/

/-- A pointwise limit of nonnegative real approximants is nonnegative. -/
theorem nonnegative_of_tendsto_nonnegative
    {u : ℕ → ℝ} {x : ℝ}
    (hu : ∀ n, 0 ≤ u n)
    (hlim : Tendsto u atTop (𝓝 x)) :
    0 ≤ x :=
  ge_of_tendsto hlim (Filter.Eventually.of_forall hu)

/-- The exact logical content of Proposition 12.19. -/
theorem exactConditionalPositivityBridge
    {A0 : Type*} (QW : A0 → ℝ)
    (criterion : (∀ f, 0 ≤ QW f) → RiemannResearch.RH.Statement)
    (approx : ℕ → A0 → ℝ)
    (happrox : ∀ n f, 0 ≤ approx n f)
    (hlim : ∀ f, Tendsto (fun n => approx n f) atTop (𝓝 (QW f))) :
    RiemannResearch.RH.Statement := by
  apply criterion
  intro f
  exact nonnegative_of_tendsto_nonnegative
    (fun n => happrox n f) (hlim f)

/-- Abstract data supplied by one support-adaptive semilocal trace
certificate.  The analytic trace-class construction is not assumed globally;
it has to be provided as data. -/
structure SupportAdaptiveCertificate
    {Test : Type*} (QW : Test → ℝ)
    (admissible : ℝ → Test → Prop) (R : ℝ) where
  traceTerm : Test → ℝ
  errorTerm : Test → ℝ
  trace_nonneg : ∀ f, 0 ≤ traceTerm f
  error_nonneg : ∀ f, 0 ≤ errorTerm f
  identity : ∀ f, admissible R f → QW f = traceTerm f + errorTerm f

/-- Typed form of Conjecture 12.20.  It is a proposition, not an axiom. -/
def SupportAdaptiveSemilocalTraceBridge
    {Test : Type*} (QW : Test → ℝ)
    (admissible : ℝ → Test → Prop) : Prop :=
  ∀ R, 0 < R →
    Nonempty (SupportAdaptiveCertificate QW admissible R)

/-- The support-adaptive trace conjecture implies RH once its admissible tests
cover a criterion-determining algebra. -/
theorem supportAdaptiveSemilocalTraceBridgeImplication
    {Test : Type*} (QW : Test → ℝ)
    (admissible : ℝ → Test → Prop)
    (hcover : ∀ f, ∃ R, 0 < R ∧ admissible R f)
    (hbridge : SupportAdaptiveSemilocalTraceBridge QW admissible)
    (criterion : (∀ f, 0 ≤ QW f) → RiemannResearch.RH.Statement) :
    RiemannResearch.RH.Statement := by
  apply criterion
  intro f
  obtain ⟨R, hR, hf⟩ := hcover f
  obtain ⟨cert⟩ := hbridge R hR
  rw [cert.identity f hf]
  exact add_nonneg (cert.trace_nonneg f) (cert.error_nonneg f)

/-! ## Lemma 13.1 and Proposition 13.2: analytic symmetry algebra -/

/-- The anti-holomorphic reflection fixing the critical line. -/
def criticalReflection (ρ : ℂ) : ℂ :=
  1 - Complex.conj ρ

/-- Fixed points of the analytic reflection are exactly the critical line. -/
theorem criticalReflection_fixed_iff (ρ : ℂ) :
    criticalReflection ρ = ρ ↔ ρ.re = (1 : ℝ) / 2 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp [criticalReflection] at hre
    linarith
  · intro hre
    apply Complex.ext
    · simp [criticalReflection, hre]
    · simp [criticalReflection]

/-- The four analytic transforms have constant total sum.  This is the
termwise algebra behind the unweighted-conjugate-sum no-go. -/
theorem symmetryQuartet_sum (ρ : ℂ) :
    ρ + Complex.conj ρ + (1 - ρ) + (1 - Complex.conj ρ) = 2 := by
  ring

/-! ## Registered classical and conjectural targets

These definitions encode exact implication/equivalence shapes without
asserting the deep analytic input.
-/

/-- Typed statement shape for the classical Riesz criterion. -/
def RieszCriterionTarget (rieszCondition : Prop) : Prop :=
  RiemannResearch.RH.Statement ↔ rieszCondition

/-- Typed statement shape for the classical Nyman--Beurling criterion. -/
def NymanBeurlingTarget (nymanCondition : Prop) : Prop :=
  RiemannResearch.RH.Statement ↔ nymanCondition

/-- Typed statement shape for a conductor-restricted CRT-to-Nyman
implication. -/
def CRTToNymanTarget (restrictedEstimate : Prop) : Prop :=
  restrictedEstimate → RiemannResearch.RH.Statement

/-- Typed statement shape for the unrestricted central estimate. -/
def UnrestrictedCentralEstimateTarget (centralEstimate : Prop) : Prop :=
  centralEstimate ↔ RiemannResearch.RH.Statement

/-- Typed statement shape for the polar-vanishing Weil criterion. -/
def PolarVanishingWeilCriterionTarget (weilPositive : Prop) : Prop :=
  RiemannResearch.RH.Statement ↔ weilPositive

/-- Typed statement shape for the reciprocal running-maximum Li criterion. -/
def LiRunningMaximumCriterionTarget (liDivergence : Prop) : Prop :=
  RiemannResearch.RH.Statement ↔ liDivergence

end
end RiemannResearch.RH.CombinedAuditedCore
