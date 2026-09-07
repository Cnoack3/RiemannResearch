import RiemannResearch.RH.ArithmeticFiniteCertificateInfrastructure

/-!
# Exact integer arithmetic for interval shear certificates

Integer numerator inequalities at denominator 10^26 imply the corresponding
rational congruence enclosures at denominator 10^15. Unit-upper invertibility,
interval propagation, and diagonal dominance give a real Gram lower bound.

Source: user-provided FifthLevel_Paper_Recon_v47.md and the RH continuation
program support the certificate architecture and candidate rational data.
All identities and inequalities below are formally proved. These fixed-level
results do not establish all-level positivity, completed-Weil positivity, or RH.
-/


open scoped BigOperators
namespace RiemannResearch.RH

def integerIntervalLower (w l u : ℤ) : ℤ := if 0 ≤ w then w*l else w*u
def integerIntervalUpper (w l u : ℤ) : ℤ := if 0 ≤ w then w*u else w*l

def integerCongruenceLower {n : Type*} [Fintype n]
    (A L U : Matrix n n ℤ) (i j : n) : ℤ :=
  ∑ a, ∑ b, integerIntervalLower (A a i*A b j) (L a b) (U a b)

def integerCongruenceUpper {n : Type*} [Fintype n]
    (A L U : Matrix n n ℤ) (i j : n) : ℤ :=
  ∑ a, ∑ b, integerIntervalUpper (A a i*A b j) (L a b) (U a b)

theorem rationalInterval_integer_scaling (a b l u : ℤ) :
    rationalIntervalLower ((a:ℚ)/10000*((b:ℚ)/10000))
      ((l:ℚ)/1000000000000000000) ((u:ℚ)/1000000000000000000) =
        (integerIntervalLower (a*b) l u : ℚ)/100000000000000000000000000 ∧
    rationalIntervalUpper ((a:ℚ)/10000*((b:ℚ)/10000))
      ((l:ℚ)/1000000000000000000) ((u:ℚ)/1000000000000000000) =
        (integerIntervalUpper (a*b) l u : ℚ)/100000000000000000000000000 := by
  have hs : 0 ≤ (a:ℚ)/10000*((b:ℚ)/10000) ↔ 0 ≤ a*b := by
    have he : (a:ℚ)/10000*((b:ℚ)/10000) = ((a*b:ℤ):ℚ)/100000000 := by
      push_cast
      ring
    rw [he]
    constructor
    · intro h
      have hh : (0:ℚ) ≤ ((a*b:ℤ):ℚ) := by linarith
      exact_mod_cast hh
    · intro h
      exact div_nonneg (by exact_mod_cast h) (by norm_num)
  by_cases h : 0 ≤ a*b
  · have hh := hs.mpr h
    simp only [rationalIntervalLower, rationalIntervalUpper, integerIntervalLower,
      integerIntervalUpper, h, hh, if_true, Int.cast_mul]
    constructor <;> ring
  · have hh : ¬0 ≤ (a:ℚ)/10000*((b:ℚ)/10000) := by exact mt hs.mp h
    simp only [rationalIntervalLower, rationalIntervalUpper, integerIntervalLower,
      integerIntervalUpper, h, hh, if_false, Int.cast_mul]
    constructor <;> ring

theorem rationalCongruence_integer_scaling {n : Type*} [Fintype n]
    (A L U : Matrix n n ℤ) (i j : n) :
    rationalCongruenceLower (fun a b => (A a b:ℚ)/10000)
      (fun a b => (L a b:ℚ)/1000000000000000000)
      (fun a b => (U a b:ℚ)/1000000000000000000) i j =
        (integerCongruenceLower A L U i j : ℚ)/100000000000000000000000000 ∧
    rationalCongruenceUpper (fun a b => (A a b:ℚ)/10000)
      (fun a b => (L a b:ℚ)/1000000000000000000)
      (fun a b => (U a b:ℚ)/1000000000000000000) i j =
        (integerCongruenceUpper A L U i j : ℚ)/100000000000000000000000000 := by
  constructor
  · simp only [rationalCongruenceLower, integerCongruenceLower, Int.cast_sum, Finset.sum_div,
      (rationalInterval_integer_scaling _ _ _ _).1]
  · simp only [rationalCongruenceUpper, integerCongruenceUpper, Int.cast_sum, Finset.sum_div,
      (rationalInterval_integer_scaling _ _ _ _).2]

theorem integerCongruence_symm {n : Type*} [Fintype n]
    (A L U : Matrix n n ℤ) (hL : ∀ i j, L i j = L j i)
    (hU : ∀ i j, U i j = U j i) (i j : n) :
    integerCongruenceLower A L U i j = integerCongruenceLower A L U j i ∧
    integerCongruenceUpper A L U i j = integerCongruenceUpper A L U j i := by
  constructor
  · unfold integerCongruenceLower
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [hL b a, hU b a, mul_comm]
  · unfold integerCongruenceUpper
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [hL b a, hU b a, mul_comm]

theorem rationalCongruence_integer_refinement {n : Type*} [Fintype n]
    (A L U : Matrix n n ℤ) (i j : n) (l u : ℤ)
    (h : l*100000000000 ≤ integerCongruenceLower A L U i j ∧
      integerCongruenceUpper A L U i j ≤ u*100000000000) :
    (l:ℚ)/1000000000000000 ≤
      rationalCongruenceLower (fun a b => (A a b:ℚ)/10000)
        (fun a b => (L a b:ℚ)/1000000000000000000)
        (fun a b => (U a b:ℚ)/1000000000000000000) i j ∧
    rationalCongruenceUpper (fun a b => (A a b:ℚ)/10000)
        (fun a b => (L a b:ℚ)/1000000000000000000)
        (fun a b => (U a b:ℚ)/1000000000000000000) i j ≤
      (u:ℚ)/1000000000000000 := by
  rw [(rationalCongruence_integer_scaling A L U i j).1,
    (rationalCongruence_integer_scaling A L U i j).2]
  have hl : (l:ℚ)*100000000000 ≤ (integerCongruenceLower A L U i j : ℚ) := by
    exact_mod_cast h.1
  have hu : (integerCongruenceUpper A L U i j : ℚ) ≤ (u:ℚ)*100000000000 := by
    exact_mod_cast h.2
  constructor <;> linarith

theorem max_abs_div_quadrillion (x y : ℝ) :
    max |x/1000000000000000| |y/1000000000000000| =
      max |x| |y| / 1000000000000000 := by
  rw [abs_div, abs_div]
  norm_num
  rcases le_total |x| |y| with h | h
  · rw [max_eq_right h, max_eq_right (by linarith)]
  · rw [max_eq_left h, max_eq_left (by linarith)]

/-- Fixed-denominator integer checks imply the original real Gram lower bound. -/
theorem realMatrix_lower_of_integer_interval_shear
    {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
    (K G : Matrix n n ℝ) (A L U TL TU : Matrix n n ℤ) (ε : ℝ)
    (hK : K.IsHermitian) (hG : G.IsHermitian)
    (hupper : ∀ i j, j < i → A i j = 0) (hdiag : ∀ i, A i i = 10000)
    (hB : ∀ i j, (L i j:ℝ)/1000000000000000000 ≤ (K-ε • G) i j ∧
      (K-ε • G) i j ≤ (U i j:ℝ)/1000000000000000000)
    (hinterval : ∀ i j, TL i j*100000000000 ≤ integerCongruenceLower A L U i j ∧
      integerCongruenceUpper A L U i j ≤ TU i j*100000000000)
    (hdd : ∀ i, (∑ j ∈ Finset.univ.erase i, max |TL i j| |TU i j|) < TL i i)
    (c : n → ℝ) : ε * dotProduct c (G.mulVec c) ≤ dotProduct c (K.mulVec c) := by
  let SQ : Matrix n n ℚ := fun i j => (A i j:ℚ)/10000
  let S : Matrix n n ℝ := SQ.map (fun q : ℚ => (q:ℝ))
  let RL : Matrix n n ℝ := fun i j => (TL i j:ℝ)/1000000000000000
  let RU : Matrix n n ℝ := fun i j => (TU i j:ℝ)/1000000000000000
  have hS : IsUnit S := by
    apply realMatrix_isUnit_of_unit_upper
    · intro i j hij
      change (((A i j:ℚ)/10000:ℚ):ℝ) = 0
      rw [hupper i j hij]
      norm_num
    · intro i
      change (((A i i:ℚ)/10000:ℚ):ℝ) = 1
      rw [hdiag i]
      norm_num
  have hh (i j : n) :
      RL i j ≤ (S.transpose * (K-ε • G) * S) i j ∧
        (S.transpose * (K-ε • G) * S) i j ≤ RU i j := by
    have hr := rationalCongruence_bounds SQ
      (fun a b => (L a b:ℚ)/1000000000000000000)
      (fun a b => (U a b:ℚ)/1000000000000000000) (K-ε • G)
      (fun a b => by simpa using hB a b) i j
    have hf := rationalCongruence_integer_refinement A L U i j (TL i j) (TU i j)
      (hinterval i j)
    have hl : RL i j ≤ (rationalCongruenceLower SQ
        (fun a b => (L a b:ℚ)/1000000000000000000)
        (fun a b => (U a b:ℚ)/1000000000000000000) i j : ℝ) := by
      dsimp only [RL, SQ]
      exact_mod_cast hf.1
    have hu : (rationalCongruenceUpper SQ
        (fun a b => (L a b:ℚ)/1000000000000000000)
        (fun a b => (U a b:ℚ)/1000000000000000000) i j : ℝ) ≤ RU i j := by
      dsimp only [RU, SQ]
      exact_mod_cast hf.2
    exact ⟨hl.trans hr.1, hr.2.trans hu⟩
  have hd (i : n) :
      (∑ j ∈ Finset.univ.erase i, max |RL i j| |RU i j|) < RL i i := by
    change (∑ j ∈ Finset.univ.erase i,
      max |(TL i j:ℝ)/1000000000000000| |(TU i j:ℝ)/1000000000000000|) <
        (TL i i:ℝ)/1000000000000000
    simp_rw [max_abs_div_quadrillion]
    rw [← Finset.sum_div]
    have ht : (∑ j ∈ Finset.univ.erase i, max |(TL i j:ℝ)| |(TU i j:ℝ)|) <
        (TL i i:ℝ) := by exact_mod_cast hdd i
    linarith
  exact realMatrix_lower_of_interval_shear K G S RL RU ε hK hG hS
    (fun i j => (hh i j).1) (fun i j => (hh i j).2) hd c

end RiemannResearch.RH
