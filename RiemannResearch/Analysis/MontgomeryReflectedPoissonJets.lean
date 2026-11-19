import RiemannResearch.Analysis.MontgomeryReflectedGramKernel
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Partial-fraction derivatives for the reflected Gram comparison -/

noncomputable section
open Set
namespace RiemannResearch.Analysis.MontgomeryCentralDifference

/-- The kth derivative of one signed simple pole. -/
def poleJet {𝕂 : Type*} [NontriviallyNormedField 𝕂] (s η : 𝕂) (k : ℕ) (x : 𝕂) : 𝕂 :=
  (k.factorial : 𝕂)*s^k*((2-s*(x+η))⁻¹)^(k+1)

/-- The derivatives of the rational Poisson kernel as sums of two simple poles. -/
def poissonJet {𝕂 : Type*} [NontriviallyNormedField 𝕂] (η : 𝕂) (k : ℕ) (x : 𝕂) : 𝕂 :=
  poleJet 1 η k x + poleJet (-1) η k x

theorem hasDerivAt_poleJet {𝕂 : Type*} [NontriviallyNormedField 𝕂] {s η x : 𝕂} (k : ℕ)
    (hne : 2-s*(x+η) ≠ 0) : HasDerivAt (poleJet s η k) (poleJet s η (k+1) x) x := by
  let p := fun t : 𝕂 => (2-s*(t+η))⁻¹
  have h := ((((hasDerivAt_id x).add_const η).const_mul s).const_sub 2).inv hne
  have hp : HasDerivAt p (s*(p x)^2) x := by
    convert h using 1 <;> first | rfl | (dsimp only [p]; simp only [id_eq,div_eq_mul_inv,inv_pow]; ring)
  have hpow := (hp.pow (k+1)).const_mul ((k.factorial : 𝕂)*s^k)
  convert hpow using 1 <;> first | rfl | (
    dsimp only [poleJet,p]
    simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,
      pow_succ]
    ring)

theorem hasDerivAt_poissonJet {𝕂 : Type*} [NontriviallyNormedField 𝕂] {η x : 𝕂} (k : ℕ)
    (hm : 2 - (x + η) ≠ 0) (hp : 2 + (x + η) ≠ 0) :
    HasDerivAt (poissonJet η k) (poissonJet η (k+1) x) x :=
  (hasDerivAt_poleJet k (by simpa only [one_mul] using hm)).add
    (hasDerivAt_poleJet k (by simpa only [neg_one_mul,sub_neg_eq_add] using hp))

theorem poissonJet_zero_apply {𝕂 : Type*} [NontriviallyNormedField 𝕂] {η x : 𝕂}
    (hm : 2 - (x + η) ≠ 0) (hp : 2 + (x + η) ≠ 0) : poissonJet η 0 x = 4/(4-(x+η)^2) := by
  have hfac : (4-(x+η)^2) = (2 - (x + η))*(2 + (x + η)) := by ring
  rw [hfac]
  simp only [poissonJet,poleJet,Nat.factorial_zero,Nat.cast_one,pow_zero,one_mul,
    neg_one_mul,sub_neg_eq_add]
  generalize hA : 2 - (x + η) = A at hm ⊢
  generalize hB : 2 + (x + η) = B at hp ⊢
  have hab : A+B = 4 := by rw [← hA,← hB]; ring
  rw [← hab]
  apply (eq_div_iff (mul_ne_zero hm hp)).2
  calc
    _ = (A⁻¹*A)*B + A*(B*B⁻¹) := by ring
    _ = A+B := by rw [inv_mul_cancel₀ hm,mul_inv_cancel₀ hp]; ring

def exponentialPoissonJet (u η : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (u*z) * ∑ k ∈ Finset.range (n+1), (n.choose k : ℂ)*u^(n-k)*poissonJet η k z

theorem exponentialPoissonJet_zero {u η z : ℂ}
    (hm : 2 - (z + η) ≠ 0) (hp : 2 + (z + η) ≠ 0) :
    exponentialPoissonJet u η 0 z = Complex.exp (u*z)*(4/(4-(z+η)^2)) := by
  simp [exponentialPoissonJet,poissonJet_zero_apply hm hp]

/-- The four successive product-rule steps needed for the mixed central difference. -/
theorem hasDerivAt_exponentialPoissonJet {u η z : ℂ} {n : ℕ} (hn : n < 4)
    (hm : 2 - (z + η) ≠ 0) (hp : 2 + (z + η) ≠ 0) :
    HasDerivAt (exponentialPoissonJet u η n) (exponentialPoissonJet u η (n+1) z) z := by
  have he : HasDerivAt (fun t : ℂ => Complex.exp (u*t)) (Complex.exp (u*z)*u) z := by
    simpa only [Function.comp_def,id_eq,mul_one] using!
      (Complex.hasDerivAt_exp (u*z)).comp z ((hasDerivAt_id z).const_mul u)
  have hpj (k : ℕ) := hasDerivAt_poissonJet k hm hp
  interval_cases n
  · have H := he.mul (hpj 0)
    convert! H using 1 <;> first | rfl |
      (funext t; simp [exponentialPoissonJet,Finset.sum_range_succ,Nat.choose,
        Pi.mul_apply,Pi.add_apply] <;> ring) |
      (simp [exponentialPoissonJet,Finset.sum_range_succ,Nat.choose,
        Pi.mul_apply,Pi.add_apply] <;> ring)
  · have H := he.mul (((hpj 0).const_mul (u^1)).add (hpj 1))
    convert! H using 1 <;> first | rfl |
      (funext t; simp [exponentialPoissonJet,Finset.sum_range_succ,Nat.choose,
        Pi.mul_apply,Pi.add_apply] <;> ring) |
      (simp [exponentialPoissonJet,Finset.sum_range_succ,Nat.choose,
        Pi.mul_apply,Pi.add_apply] <;> ring)
  · have H := he.mul (((hpj 0).const_mul (u^2)).add (((hpj 1).const_mul (2*u^1)).add (hpj 2)))
    convert! H using 1 <;> first | rfl |
      (funext t; simp [exponentialPoissonJet,Finset.sum_range_succ,Nat.choose,
        Pi.mul_apply,Pi.add_apply] <;> ring) |
      (simp [exponentialPoissonJet,Finset.sum_range_succ,Nat.choose,
        Pi.mul_apply,Pi.add_apply] <;> ring)
  · have H := he.mul
      (((hpj 0).const_mul (u^3)).add (((hpj 1).const_mul (3*u^2)).add (((hpj 2).const_mul (3*u^1)).add (hpj 3))))
    convert! H using 1 <;> first | rfl |
      (funext t; simp [exponentialPoissonJet,Finset.sum_range_succ,Nat.choose,
        Pi.mul_apply,Pi.add_apply] <;> ring) |
      (simp [exponentialPoissonJet,Finset.sum_range_succ,Nat.choose,
        Pi.mul_apply,Pi.add_apply] <;> ring)

end RiemannResearch.Analysis.MontgomeryCentralDifference
