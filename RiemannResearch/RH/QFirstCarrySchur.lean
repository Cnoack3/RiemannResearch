import RiemannResearch.RH.QGcdCellObstruction
import RiemannResearch.RH.QResidueGramNumerical
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The first physical CRT carry, including all repeats of period six

Source: C. Noack, *Q CRT Carry Gram and Schur Matrices with Zeta Trace
Identities*, October 2026. The six weights follow from exact dilation and
partition of positive integers. Rational enclosures use the project's
sixteen-term trigamma certificates.
-/
noncomputable section
open scoped BigOperators Matrix
namespace RiemannResearch.RH.QFirstCarrySchur
open QGcdCellObstruction QGcdCellRefinement CRTBlock ZetaTwoHilbert ZetaTwoProbability

def h : ℝ := residueMass 3 1 - residueMass 3 2

private theorem split_mass {R r D i j : ℕ} (hij : i ≠ j)
    (hu : ∀ n : ℕ, n % R = r ↔ n % D = i ∨ n % D = j) :
    residueMass R r = residueMass D i + residueMass D j := by
  have hs : residueEvent R r = residueEvent D i ∪ residueEvent D j := Set.ext hu
  have hd : Disjoint (residueEvent D i) (residueEvent D j) := by
    apply Set.disjoint_left.mpr
    intro n hi hj
    exact hij ((show n % D = i from hi).symm.trans hj)
  unfold residueMass
  rw [hs, eventMass_union_of_disjoint _ _ hd]

private theorem scaled_mass (a R i : ℕ) (ha : 0 < a) :
    residueMass (a * R) (a * i) = (1 / (a : ℝ)^2) * residueMass R i := by
  unfold residueMass
  rw [← scaled_residueEvent_eq a R i ha, eventMass_scaledEvent a ha]

private theorem mass_one : residueMass 1 0 = 1 := by
  have hs : residueEvent 1 0 = Set.univ := by
    ext n
    change (n % 1 = 0) ↔ True
    exact iff_true_intro (Nat.mod_one n)
  rw [residueMass, hs, eventMass_univ]

private theorem mass_zero (d : ℕ) (hd : 0 < d) : residueMass d 0 = 1 / (d : ℝ)^2 := by
  simpa only [mul_one, mul_zero, mass_one] using scaled_mass d 1 0 hd

private theorem mass_three : residueMass 3 1 + residueMass 3 2 = 8 / 9 := by
  have hdis := residueEvent_disjoint 3
  have hu : (residueEvent 3 0)ᶜ = residueEvent 3 1 ∪ residueEvent 3 2 := by
    ext n
    change (¬ n % 3 = 0) ↔ n % 3 = 1 ∨ n % 3 = 2
    omega
  have eqn := eventMass_compl (residueEvent 3 0)
  rw [hu, eventMass_union_of_disjoint _ _ hdis] at eqn
  change residueMass 3 1 + residueMass 3 2 = 1 - residueMass 3 0 at eqn
  rw [mass_zero 3 (by decide)] at eqn
  linarith

/-- Zero-indexed by the actual remainder modulo six. -/
def weights (x : ℝ) : Fin 6 → ℝ :=
  ![1/36, 1/3 + 5*x/8, 1/9 + x/8, 1/12, 1/9 - x/8, 1/3 - 5*x/8]

theorem true_weights (i : Fin 6) : residueMass 6 i.val = weights h i := by
  have h0 := mass_zero 6 (by decide)
  have h30 := mass_zero 3 (by decide)
  have h2 := scaled_mass 2 3 1 (by decide)
  have h4 := scaled_mass 2 3 2 (by decide)
  have h03 : residueMass 3 0 = residueMass 6 0 + residueMass 6 3 :=
    split_mass (by decide) (fun n => by omega)
  have h14 : residueMass 3 1 = residueMass 6 1 + residueMass 6 4 :=
    split_mass (by decide) (fun n => by omega)
  have h25 : residueMass 3 2 = residueMass 6 2 + residueMass 6 5 :=
    split_mass (by decide) (fun n => by omega)
  norm_num at h0 h30 h2 h4
  fin_cases i <;> norm_num [weights, h] <;> linarith [mass_three]

private theorem mass3_trigamma (i : ℕ) (hi : i = 1 ∨ i = 2) :
    residueMass 3 i = trigamma ((i : ℝ)/3) / (zetaTwo * 9) := by
  let f : ℕ → ℝ := fun n => if n % 3 = i then 1 else 0
  have he : residueMass 3 i = inversePowerMean 0 f := by
    have hip : 0 < i := by omega
    rw [residueMass, eventMass, (eventMass_summable _).tsum_eq_zero_add]
    simp only [eventSequence_residue _ _ _ hip]
    unfold inversePowerMean
    simp only [positiveQWeight, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, div_zero,
      zero_mul, zero_add]
    apply tsum_congr
    intro n
    dsimp [f]
    push_cast
    ring
  rw [he, inversePowerMean_zero_eq_trigamma 3 (by decide) f (C := 1)
    (fun k => by dsimp [f]; split <;> norm_num) (fun k => by simp [f])]
  rcases hi with rfl | rfl <;> norm_num [Fin.sum_univ_succ, f]

theorem h_trigamma :
    h = (trigamma (1/3 : ℝ) - trigamma (2/3 : ℝ)) / (9 * zetaTwo) := by
  rw [h, mass3_trigamma 1 (Or.inl rfl), mass3_trigamma 2 (Or.inr rfl)]
  push_cast
  ring

theorem h_bounds : 0.47497491154 ≤ h ∧ h ≤ 0.47497491155 := by
  have ha := QResidueGramNumerical.tg_1_3_contains
  have hb := QResidueGramNumerical.tg_2_3_contains
  have hz := QResidueGramNumerical.zeta_bounds
  norm_num [RatInterval.Contains, QResidueGramNumerical.tg_1_3, QResidueGramNumerical.tg_2_3,
    QResidueGramNumerical.tg_1_1] at ha hb hz
  rw [h_trigamma, le_div_iff₀ (mul_pos (by norm_num) zetaTwo_pos),
    div_le_iff₀ (mul_pos (by norm_num) zetaTwo_pos)]
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2, hz.1, hz.2]

/-- The third feature is the literal floor of the specified CRT combination. -/
def row (i : Fin 6) : Fin 3 → ℝ :=
  let a := ((i.val % 2 : ℕ) : ℝ) / 2
  let b := ((i.val % 3 : ℕ) : ℝ) / 3
  ![a, b, (⌊a + 2*b⌋ : ℤ)]

def gram : Matrix (Fin 3) (Fin 3) ℝ :=
  fun j k => ∑ i : Fin 6, residueMass 6 i.val * (row i j * row i k)

def target (j : Fin 3) : ℝ := ∑ i : Fin 6, residueMass 6 i.val * row i j

theorem gram_eq : gram =
    !![3/16, (8-5*h)/48, 1/3;
       (8-5*h)/48, 20/81-h/6, 11/27-h/8;
       1/3, 11/27-h/8, 7/9+h/8] := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    norm_num [gram, true_weights, weights, row, Fin.sum_univ_succ] <;> ring

theorem target_eq : target = ![3/8, 4/9-h/6, 7/9+h/8] := by
  funext j
  fin_cases j <;> norm_num [target, true_weights, weights, row, Fin.sum_univ_succ] <;> ring

private def baseDet := gram 0 0 * gram 1 1 - gram 1 0 ^ 2

/-- Bilinear pairing with the inverse of the actual two-by-two base Gram. -/
private def baseInv (x y z w : ℝ) : ℝ :=
  (gram 1 1*x*z - gram 0 1*(x*w+y*z) + gram 0 0*y*w) / baseDet

def omega := gram 2 2 - baseInv (gram 0 2) (gram 1 2) (gram 0 2) (gram 1 2)
def eta := target 2 - baseInv (target 0) (target 1) (gram 0 2) (gram 1 2)
def baseError := 1 - baseInv (target 0) (target 1) (target 0) (target 1)
def denom (x : ℝ) := 128 + 24*x - 75*x^2
def numer (x : ℝ) := 1664 + 672*x - 3366*x^2 - 2025*x^3
def scorePoly (x : ℝ) := 128 - 288*x + 618*x^2 + 675*x^3

private theorem denom_pos : 0 < denom h := by
  have hh := h_bounds
  unfold denom
  nlinarith [mul_nonneg (show 0 ≤ h by linarith [hh.1]) (show 0 ≤ 1 - h by linarith [hh.2])]

theorem base_det_eq : baseDet = denom h / 6912 := by
  norm_num [baseDet, gram_eq, denom]
  ring

theorem omega_eq : omega = numer h / (216 * denom h) := by
  unfold omega baseInv
  rw [base_det_eq]
  rw [gram_eq]
  change (7/9+h/8) - ((20/81-h/6)*(1/3)*(1/3) -
    ((8-5*h)/48)*((1/3)*(11/27-h/8)+(11/27-h/8)*(1/3)) +
    (3/16)*(11/27-h/8)*(11/27-h/8)) / (denom h / 6912) = _
  field_simp [denom_pos.ne']
  unfold denom numer
  ring

theorem eta_eq : eta = -scorePoly h / (72 * denom h) := by
  unfold eta baseInv
  rw [base_det_eq]
  rw [gram_eq, target_eq]
  change (7/9+h/8) - ((20/81-h/6)*(3/8)*(1/3) -
    ((8-5*h)/48)*((3/8)*(11/27-h/8)+(4/9-h/6)*(1/3)) +
    (3/16)*(4/9-h/6)*(11/27-h/8)) / (denom h / 6912) = _
  field_simp [denom_pos.ne']
  unfold denom scorePoly
  ring

theorem base_error_eq : baseError = (16 - 6*h - 21*h^2) / denom h := by
  unfold baseError baseInv
  rw [base_det_eq]
  norm_num [gram_eq, target_eq]
  field_simp [denom_pos.ne']
  unfold denom
  ring

private theorem powers :
    (0.47497491154 : ℝ)^2 ≤ h^2 ∧ h^2 ≤ (0.47497491155 : ℝ)^2 ∧
    (0.47497491154 : ℝ)^3 ≤ h^3 ∧ h^3 ≤ (0.47497491155 : ℝ)^3 := by
  have h0 : 0 ≤ h := by linarith [h_bounds.1]
  exact ⟨pow_le_pow_left₀ (by norm_num) h_bounds.1 2, pow_le_pow_left₀ h0 h_bounds.2 2,
    pow_le_pow_left₀ (by norm_num) h_bounds.1 3, pow_le_pow_left₀ h0 h_bounds.2 3⟩

theorem omega_bounds : 0.038057105 ≤ omega ∧ omega ≤ 0.038057108 := by
  have hd := mul_pos (by norm_num : (0:ℝ) < 216) denom_pos
  rw [omega_eq, le_div_iff₀ hd, div_le_iff₀ hd]
  unfold numer denom
  constructor <;> linarith only [h_bounds.1, h_bounds.2, powers.1, powers.2.1,
    powers.2.2.1, powers.2.2.2]

theorem eta_bounds : -0.023015034 ≤ eta ∧ eta ≤ -0.023015030 := by
  have hd := mul_pos (by norm_num : (0:ℝ) < 72) denom_pos
  rw [eta_eq, le_div_iff₀ hd, div_le_iff₀ hd]
  unfold scorePoly denom
  constructor <;> linarith only [h_bounds.1, h_bounds.2, powers.1, powers.2.1,
    powers.2.2.1, powers.2.2.2]

theorem base_error_bounds : 0.068685281 ≤ baseError ∧ baseError ≤ 0.068685284 := by
  rw [base_error_eq, le_div_iff₀ denom_pos, div_le_iff₀ denom_pos]
  unfold denom
  constructor <;> linarith only [h_bounds.1, h_bounds.2, powers.1, powers.2.1]

theorem gain_bounds : 0.01391833 ≤ eta^2 / omega ∧ eta^2 / omega ≤ 0.01391835 := by
  have ho : 0 < omega := by linarith [omega_bounds.1]
  have he : 0 ≤ -eta := by linarith [eta_bounds.2]
  have hl := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 0.023015030)
    (show 0.023015030 ≤ -eta by linarith [eta_bounds.2]) 2
  have hu := pow_le_pow_left₀ he (show -eta ≤ 0.023015034 by linarith [eta_bounds.1]) 2
  rw [le_div_iff₀ ho, div_le_iff₀ ho]
  constructor <;> nlinarith only [hl, hu, omega_bounds.1, omega_bounds.2]

theorem final_error_bounds :
    0.05476693 ≤ baseError - eta^2 / omega ∧ baseError - eta^2 / omega ≤ 0.05476696 := by
  constructor <;> linarith only [base_error_bounds.1, base_error_bounds.2,
    gain_bounds.1, gain_bounds.2]

end RiemannResearch.RH.QFirstCarrySchur
