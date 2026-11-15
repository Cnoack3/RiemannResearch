import RiemannResearch.RH.ArithmeticConductorCommonZeros
import RiemannResearch.RH.ParetoAtomMellinSignature
import RiemannResearch.RH.ParetoMellinDilation
import RiemannResearch.RH.QFloorDilation
import RiemannResearch.RH.QDensityCouplingSurjectivity
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.PNat.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith


/-!
# Actual right-hand zeta zeros give dimension lower bounds for the Q complement

Let V be the closed span of all physical residues g_k, k >= 2, in L2(Q).
Each actual nontrivial zeta zero with Re(s) > 1/2 supplies a continuous
complex-valued real-linear functional on W = V-perp-Q. These functionals are
linearly independent over C. Hence every finite family of distinct such
zeros has cardinality at most dim_R W, whenever W is finite-dimensional.
In particular finite dimension of W would imply finitely many right-hand zeros.

The normalized Mellin functional is s times the existing Pareto step
integral, transported along the complete Q/P equivalence. Its values on
integer dilations of one are the multiplicative characters n^(1-s).
Dedekind independence and the existing two/three logarithm argument prove
independence. Orthogonal projection transfers it to W without losing a tail.

Sources: B. Bagchi, arXiv:math/0607733, Theorem 1, for the exact discrete
Nyman--Beurling setting; F. Calderaro, J. Manzur, W. Noor and C. Santos,
arXiv:2203.05030v4, Section 4, for the independent-zero-kernel obstruction
strategy in the related Hardy-space model. This file proves the bridge
directly for the repository's actual Q space, using Mathlib's
linearIndependent_monoidHom and already checked arithmetic Mellin identities.

Open: finite-dimensionality of W, surjectivity of the density coupling,
and finiteness of the actual right-hand zero set. None is proved here.
The RH-failure conjecture and spectral synthesis are not assumed.
-/

noncomputable section
open RiemannResearch.RH
open RiemannResearch.RH.ArithmeticConductorCommonZeros
namespace RiemannResearch.RH.QComplementZeroDimension

def powerCharacter (s : ℂ) : ℕ+ →* ℂ where
  toFun n := ((n : ℕ) : ℂ) ^ (1 - s)
  map_one' := by simp
  map_mul' m n := by
    simpa using
      Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg (m : ℕ))
        (Nat.cast_nonneg (n : ℕ)) (1 - s)

theorem character_value_exp (s : ℂ) (n : ℕ+) :
    powerCharacter s n = Complex.exp ((1 - s) * (Real.log (n : ℕ) : ℂ)) := by
  have hn : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.pos
  simp only [powerCharacter, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast n.ne_zero)]
  rw [← Complex.ofReal_natCast, Complex.ofReal_log hn.le]
  congr 1
  ring

theorem symbol_zero_of_character_eq (s t : ℂ) (n : ℕ+)
    (h : powerCharacter s n = powerCharacter t n) :
    conductorSymbol (n : ℕ) (1 + s - t) = 0 := by
  rw [character_value_exp, character_value_exp] at h
  have hn : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.pos
  have he : Complex.exp ((t - s) * (Real.log (n : ℕ) : ℂ)) = 1 := by
    rw [show (t - s) * (Real.log (n : ℕ) : ℂ) =
      (1 - s) * (Real.log (n : ℕ) : ℂ) -
      (1 - t) * (Real.log (n : ℕ) : ℂ) by ring,
      Complex.exp_sub, h, div_self (Complex.exp_ne_zero _)]
  unfold conductorSymbol
  rw [show -(1 + s - t) * (Real.log (n : ℕ) : ℂ) =
    -(Real.log (n : ℕ) : ℂ) + (t - s) * (Real.log (n : ℕ) : ℂ) by ring,
    Complex.exp_add, he, mul_one, Complex.exp_neg,
    ← Complex.ofReal_exp, Real.exp_log hn]
  simp

theorem powerCharacter_injective : Function.Injective powerCharacter := by
  intro s t h
  have h2 := symbol_zero_of_character_eq s t (2 : ℕ+)
    (congrArg (fun f : ℕ+ →* ℂ => f 2) h)
  have h3 := symbol_zero_of_character_eq s t (3 : ℕ+)
    (congrArg (fun f : ℕ+ →* ℂ => f 3) h)
  have he := (conductorSymbol_two_three_common_zero_iff (1 + s - t)).mp ⟨h2, h3⟩
  linear_combination he

theorem powerCharacters_linearIndependent :
    LinearIndependent ℂ (fun s : ℂ => (powerCharacter s : ℕ+ → ℂ)) :=
  (linearIndependent_monoidHom ℕ+ ℂ).comp powerCharacter powerCharacter_injective


open ZetaTwoHilbert ZetaTwoParetoTransfer QFloorDilation Pareto
open ParetoAtomMellinSignature

/-- Points in the continuity half-plane; the pole is excluded later. -/
abbrev MellinPoint := {s : ℂ // (1 / 2 : ℝ) < s.re}

def normalizedMellin (s : MellinPoint) : QHilbert →L[ℝ] ℂ :=
  (s : ℂ) • (paretoMellinContinuous s s.property).comp toParetoCLM

def testDilations : (QHilbert →L[ℝ] ℂ) →ₗ[ℂ] (ℕ+ → ℂ) where
  toFun L n := L (fromPareto (hilbertDilation n n.pos hilbertOne))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem testDilations_normalizedMellin (s : MellinPoint) :
    testDilations (normalizedMellin s) = powerCharacter s := by
  funext n
  change (s : ℂ) * paretoMellin
    (toPareto (fromPareto (hilbertDilation n n.pos hilbertOne))) s = _
  rw [toPareto_fromPareto, paretoMellin_dilation, paretoMellin_one s s.property]
  have hs0 : (s : ℂ) ≠ 0 := by
    intro he
    have hh := s.property
    simp [he] at hh
    linarith
  change (s : ℂ) * (((n : ℕ) : ℂ) ^ (1 - (s : ℂ)) * (1 / (s : ℂ))) = _
  change (s : ℂ) * (((n : ℕ) : ℂ) ^ (1 - (s : ℂ)) * (1 / (s : ℂ))) =
    ((n : ℕ) : ℂ) ^ (1 - (s : ℂ))
  field_simp [hs0]

theorem normalizedMellin_linearIndependent :
    LinearIndependent ℂ normalizedMellin := by
  apply LinearIndependent.of_comp testDilations
  have h := powerCharacters_linearIndependent.comp
    (fun s : MellinPoint => (s : ℂ)) Subtype.val_injective
  simpa only [Function.comp_def, testDilations_normalizedMellin] using h

/-- Actual nontrivial zeros strictly right of the critical line. -/
abbrev RightZero :=
  {s : ℂ // (1 / 2 : ℝ) < s.re ∧ s.re < 1 ∧ riemannZeta s = 0}

def zeroPoint (s : RightZero) : MellinPoint := ⟨s, s.property.1⟩

theorem zeroPoint_injective : Function.Injective zeroPoint := by
  intro s t h
  apply Subtype.ext
  exact congrArg (fun p : MellinPoint => (p : ℂ)) h

theorem normalizedMellin_zero_on_closure (s : RightZero) (f : QHilbert)
    (hf : f ∈ QFullResidueProjection.closure) :
    normalizedMellin (zeroPoint s) f = 0 := by
  let L := normalizedMellin (zeroPoint s)
  have hs1 : (s : ℂ) ≠ 1 := by
    intro he
    have hh := s.property.2.1
    simp [he] at hh
  have hspan : QFullResidueProjection.legalSpan ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro f ⟨i, rfl⟩
    change (s : ℂ) * paretoMellin (toPareto (qResidue (i + 2))) s = 0
    rw [toPareto_qResidue (i + 2) (by omega)]
    simp only [Pareto.BaezDuarte.residueVector, dif_pos (show 0 < i + 2 by omega)]
    rw [paretoMellin_normalizedResidue_zero_of_zeta_zero
      (i + 2) (by omega) s (by linarith [s.property.1]) hs1 s.property.2.2, mul_zero]
  exact QFullResidueProjection.legalSpan.topologicalClosure_minimal hspan L.isClosed_ker hf

abbrev W := QFullResidueProjection.closureᗮ

def zeroFunctional (s : RightZero) : W →L[ℝ] ℂ :=
  (normalizedMellin (zeroPoint s)).comp W.subtypeL

def extendFromOrthogonal : (W →L[ℝ] ℂ) →ₗ[ℂ] (QHilbert →L[ℝ] ℂ) where
  toFun L := L.comp W.orthogonalProjectionOnto
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem extend_zeroFunctional (s : RightZero) :
    extendFromOrthogonal (zeroFunctional s) = normalizedMellin (zeroPoint s) := by
  ext f
  change normalizedMellin (zeroPoint s) (W.orthogonalProjectionOnto f : QHilbert) = _
  rw [show (W.orthogonalProjectionOnto f : QHilbert) =
    f - QFullResidueProjection.closure.starProjection f from
      QFullResidueProjection.closure.starProjection_orthogonal_val f]
  rw [map_sub, normalizedMellin_zero_on_closure s _
    (QFullResidueProjection.closure.starProjection_apply_mem f), sub_zero]

theorem zeroFunctionals_linearIndependent :
    LinearIndependent ℂ zeroFunctional := by
  apply LinearIndependent.of_comp extendFromOrthogonal
  simpa only [Function.comp_def, extend_zeroFunctional] using
    normalizedMellin_linearIndependent.comp zeroPoint zeroPoint_injective

section FiniteDimension
variable [FiniteDimensional ℝ W]

def evaluateBasis : (W →L[ℝ] ℂ) →ₗ[ℂ] (Fin (Module.finrank ℝ W) → ℂ) where
  toFun L i := L (Module.finBasis ℝ W i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evaluateBasis_injective : Function.Injective evaluateBasis := by
  intro L M h
  have he : L.toLinearMap = M.toLinearMap := by
    apply (Module.finBasis ℝ W).ext
    intro i
    exact congrFun h i
  ext w
  exact LinearMap.congr_fun he w

/-- Finite dimension of the actual complement forces finitely many right-hand zeros. -/
theorem finite_rightZeros_of_finiteDimensional : Finite RightZero := by
  have h := zeroFunctionals_linearIndependent.map' evaluateBasis
    (LinearMap.ker_eq_bot.mpr evaluateBasis_injective)
  exact h.finite

/-- Every finite family of distinct right-hand zeros gives a sharp dimension lower bound. -/
theorem rightZero_family_card_le_finrank {ι : Type*} [Fintype ι]
    (s : ι → RightZero) (hs : Function.Injective s) :
    Fintype.card ι ≤ Module.finrank ℝ W := by
  have h := (zeroFunctionals_linearIndependent.comp s hs).map' evaluateBasis
    (LinearMap.ker_eq_bot.mpr evaluateBasis_injective)
  simpa using h.fintype_card_le_finrank

end FiniteDimension

theorem not_finiteDimensional_of_infinite_rightZeros [Infinite RightZero] :
    ¬ FiniteDimensional ℝ W := by
  intro h
  let := h
  have := finite_rightZeros_of_finiteDimensional
  exact not_finite RightZero


/-- A consequence of the proposed surjectivity, not a proof of that premise. -/
theorem finite_rightZeros_of_coupling_surjective
    (h : Function.Surjective QDensityCouplingSurjectivity.coupling) :
    Finite RightZero := by
  letI : FiniteDimensional ℝ W :=
    QDensityCouplingSurjectivity.coupling_surjective_iff_finiteDimensional.mp h
  exact finite_rightZeros_of_finiteDimensional

end RiemannResearch.RH.QComplementZeroDimension
