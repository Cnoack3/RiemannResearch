import RiemannResearch.Analysis.PrimeBlockCovariance
import RiemannResearch.Probability.DeterminantalIndependentLimit
import RiemannResearch.Probability.DeterminantalEntry
import Mathlib.Analysis.Matrix.PosDef

/-!
# An infinite arithmetic DPP from the signed prime-block correction

Source: user-provided `V_vector_space_RH.pdf`, Section 4, for the signed block
B_p(k,l)=-log(p)/(2*pi) p^(-|k-l|/2), off the diagonal, and its uniform bound.
The affine conversion of a bounded self-adjoint form to a positive contraction
and the discrete DPP terminology follow Lyons, arXiv:math/0204325, Sections 7--8.

The construction uses only finite row bounds and finitely supported quadratic
forms. It constructs the actual countable law for K=(I+B/C)/2 without assuming
an infinite operator extension or any zero-height asymptotic. A site (p,n)
represents p^(n+1). This law is purely arithmetic and is not asserted to be the
point process of zeta zeros.
-/

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Classical
namespace RiemannResearch.Probability.DPP.PrimeBlock
open RiemannResearch.Analysis.PrimeBlockCovariance
open RiemannResearch.Fourier
open RiemannResearch.Probability.DPP

abbrev Prime := {p : ℕ // p.Prime}
abbrev Site := Prime × ℕ

def normalization : ℝ := Real.log 2 / (Real.pi * (Real.sqrt 2 - 1))

theorem normalization_pos : 0 < normalization := by
  have hsq : 1 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  exact div_pos (Real.log_pos (by norm_num)) (mul_pos Real.pi_pos (sub_pos.mpr hsq))

def coefficient (p : Prime) : ℝ := Real.log (p.1 : ℝ) / (2 * Real.pi)
def ratio (p : Prime) : ℝ := 1 / Real.sqrt (p.1 : ℝ)

theorem prime_real_two_le (p : Prime) : (2 : ℝ) ≤ p.1 := by exact_mod_cast p.2.two_le

theorem coefficient_nonneg (p : Prime) : 0 ≤ coefficient p := by
  apply div_nonneg (Real.log_nonneg _) (by positivity)
  linarith [prime_real_two_le p]

theorem ratio_nonneg (p : Prime) : 0 ≤ ratio p := by unfold ratio; positivity

theorem ratio_lt_one (p : Prime) : ratio p < 1 := by
  have hp : 1 < (p.1 : ℝ) := by linarith [prime_real_two_le p]
  have hs : 1 < Real.sqrt (p.1 : ℝ) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (p.1 : ℝ) by positivity), Real.sqrt_nonneg (p.1 : ℝ)]
  exact (div_lt_one (lt_trans zero_lt_one hs)).mpr hs

theorem coefficient_row_bound (p : Prime) :
    coefficient p * (2 * ratio p / (1-ratio p)) ≤ normalization := by
  have hp := prime_real_two_le p
  have hs : 1 < Real.sqrt (p.1 : ℝ) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (p.1 : ℝ) by positivity), Real.sqrt_nonneg (p.1 : ℝ)]
  have he : coefficient p * (2 * ratio p / (1-ratio p)) =
      Real.log (p.1 : ℝ) / (Real.pi * (Real.sqrt (p.1 : ℝ)-1)) := by
    unfold coefficient ratio
    field_simp [Real.pi_ne_zero, (lt_trans zero_lt_one hs).ne',
      (sub_pos.mpr hs).ne', (sub_pos.mpr (ratio_lt_one p)).ne']
  rw [he]
  exact prime_constant_le_two _ hp

/-- Zero diagonal, with no interactions between distinct primes. -/
def signedEntry (x y : Site) : ℝ :=
  if y.1 = x.1 then -coefficient x.1 * entry (ratio x.1) x.2 y.2 else 0

@[simp] theorem signedEntry_self (x : Site) : signedEntry x x = 0 := by
  simp [signedEntry, entry]

theorem signedEntry_symmetric (x y : Site) : signedEntry x y = signedEntry y x := by
  by_cases hp : y.1 = x.1
  · simp [signedEntry, hp, entry_symm]
  · simp [signedEntry, hp, Ne.symm hp]

theorem signedEntry_abs (x y : Site) :
    |signedEntry x y| =
      if y.1 = x.1 then coefficient x.1 * entry (ratio x.1) x.2 y.2 else 0 := by
  by_cases hp : y.1 = x.1
  · simp [signedEntry, hp, abs_mul, abs_of_nonneg (coefficient_nonneg x.1),
      abs_of_nonneg (entry_nonneg _ (ratio_nonneg x.1) _ _)]
  · simp [signedEntry, hp]

/-- The arithmetic row bound remains uniform on arbitrary finite subsets of
all prime/exponent sites, rather than only rectangular prime blocks. -/
theorem signedEntry_row_bound (s : Finset Site) (x : Site) :
    (∑ y ∈ s, |signedEntry x y|) ≤ normalization := by
  let t : Finset Site := s.filter (fun y => y.1 = x.1)
  have hinj : ∀ a ∈ t, ∀ b ∈ t, a.2 = b.2 → a = b := by
    intro a ha b hb hab
    apply Prod.ext
    · exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
    · exact hab
  have hrow : (∑ y ∈ t, entry (ratio x.1) x.2 y.2) ≤
      2 * ratio x.1 / (1-ratio x.1) := by
    rw [← Finset.sum_image hinj]
    exact row_sum_le _ _ (ratio_nonneg x.1) (ratio_lt_one x.1) x.2
  have he : (∑ y ∈ s, |signedEntry x y|) =
      coefficient x.1 * ∑ y ∈ t, entry (ratio x.1) x.2 y.2 := by
    simp only [signedEntry_abs, Finset.mul_sum]
    simp [t, Finset.sum_filter, mul_ite]
  rw [he]
  exact (mul_le_mul_of_nonneg_left hrow (coefficient_nonneg x.1)).trans
    (coefficient_row_bound x.1)

/-- The signed quadratic bound in real coordinates, on arbitrary finite sites. -/
theorem signedEntry_quadratic_bound (s : Finset Site) (a : Site → ℝ) :
    |∑ i ∈ s, ∑ j ∈ s, a i * signedEntry i j * a j| ≤
      normalization * ∑ i ∈ s, (a i)^2 := by
  have hh := finiteGramErrorPairing_norm_le_weighted_schur s
    (fun i => (a i : ℂ)) (fun i j => (signedEntry i j : ℂ))
    (fun _ => 1) normalization (fun _ _ => by norm_num)
    (fun i _ j _ => by rw [signedEntry_symmetric i j])
    (fun i _ => by
      simpa only [Complex.norm_real, Real.norm_eq_abs, mul_one] using signedEntry_row_bound s i)
  simpa [finiteGramErrorPairing, ← Complex.ofReal_sum, ← Complex.ofReal_mul,
    Complex.norm_real, Real.norm_eq_abs, sq_abs] using hh

/-- The sign parameter displays both particles (+1) and holes (-1). -/
def shiftedKernel (sign : ℝ) (x y : Site) : ℝ :=
  ((if x = y then 1 else 0) + sign * signedEntry x y / normalization) / 2

@[simp] theorem shiftedKernel_diagonal (sign : ℝ) (x : Site) :
    shiftedKernel sign x x = 1/2 := by simp [shiftedKernel]

theorem shiftedKernel_symmetric (sign : ℝ) (x y : Site) :
    shiftedKernel sign x y = shiftedKernel sign y x := by
  simp only [shiftedKernel, signedEntry_symmetric x y, eq_comm]

private theorem shifted_quadratic (sign : ℝ) (a : Site →₀ ℝ) :
    a.sum (fun i ai => a.sum (fun j aj => star ai * shiftedKernel sign i j * aj)) =
      ((∑ i ∈ a.support, (a i)^2) + sign *
        (∑ i ∈ a.support, ∑ j ∈ a.support, a i * signedEntry i j * a j) /
          normalization) / 2 := by
  classical
  simp only [Finsupp.sum, star_trivial]
  have ht (i j : Site) : a i * shiftedKernel sign i j * a j =
      (a i * (if i = j then (1:ℝ) else 0) * a j) / 2 +
        (sign / (2*normalization)) * (a i * signedEntry i j * a j) := by
    unfold shiftedKernel
    ring
  have hd : (∑ i ∈ a.support, ∑ j ∈ a.support,
      a i * (if i = j then (1:ℝ) else 0) * a j) = ∑ i ∈ a.support, (a i)^2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_eq_single i]
    · simp [pow_two]
    · intro j hj hij
      simp [Ne.symm hij]
    · exact fun h => (h hi).elim
  simp_rw [ht, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum]
  rw [hd]
  ring

/-- Global PSD is proved on finitely supported vectors; no infinite operator
extension theorem is needed. -/
theorem shiftedKernel_posSemidef (sign : ℝ) (hsign : sign = 1 ∨ sign = -1) :
    (Matrix.of (shiftedKernel sign)).PosSemidef := by
  constructor
  · ext x y
    simpa only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial] using
      shiftedKernel_symmetric sign y x
  · intro a
    change 0 ≤ a.sum (fun i ai => a.sum (fun j aj => star ai * shiftedKernel sign i j * aj))
    rw [shifted_quadratic]
    have hq := signedEntry_quadratic_bound a.support a
    have hb := abs_le.mp hq
    have hc := normalization_pos
    have hlo : -(∑ i ∈ a.support, (a i)^2) ≤
        (∑ i ∈ a.support, ∑ j ∈ a.support, a i * signedEntry i j * a j) / normalization := by
      apply (le_div_iff₀ hc).mpr
      nlinarith [hb.1]
    have hhi : (∑ i ∈ a.support, ∑ j ∈ a.support, a i * signedEntry i j * a j) / normalization ≤
        ∑ i ∈ a.support, (a i)^2 := by
      apply (div_le_iff₀ hc).mpr
      nlinarith [hb.2]
    rcases hsign with rfl | rfl <;> simp only [one_mul, neg_one_mul, neg_div] <;> linarith

theorem complement_eq :
    (1 : Matrix Site Site ℝ) - Matrix.of (shiftedKernel 1) = Matrix.of (shiftedKernel (-1)) := by
  ext x y
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, shiftedKernel]
  ring

theorem principal_complement_eq {ι : Type*} [DecidableEq ι] (e : ι ↪ Site) :
    (1 : Matrix ι ι ℝ) - Matrix.of (fun i j => shiftedKernel 1 (e i) (e j)) =
      Matrix.of (fun i j => shiftedKernel (-1) (e i) (e j)) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, shiftedKernel,
    e.injective.eq_iff]
  ring

/-- A genuine countable arithmetic DPP, with all positivity obligations proved. -/
def law : Measure (Site → Bool) :=
  contractionDPP (shiftedKernel 1)
    (fun I => (shiftedKernel_posSemidef 1 (Or.inl rfl)).submatrix (fun i : I => i.1))
    (fun I => by
      have h := (shiftedKernel_posSemidef (-1) (Or.inr rfl)).submatrix (fun i : I => i.1)
      convert h using 1
      ext i j
      by_cases hij : i = j
      · subst j
        norm_num [Matrix.submatrix]
      · have hv : i.1 ≠ j.1 := fun hh => hij (Subtype.ext hh)
        simp [Matrix.submatrix, Matrix.one_apply, hij, hv, shiftedKernel]
        <;> ring)

instance law_probability : IsProbabilityMeasure law :=
  contractionDPP_probability _ _ _

theorem law_isDPP : IsDPP law (fun x => {i | x i = true}) (shiftedKernel 1) :=
  contractionDPP_isDPP _ _ _

theorem occupation (x : Site) : law.real {z | z x = true} = 1/2 := by
  simpa using law_isDPP.occupation x

theorem two_point (x y : Site) (hxy : x ≠ y) :
    law.real {z | z x = true ∧ z y = true} =
      1/4 - (signedEntry x y / (2*normalization))^2 := by
  have hh := law_isDPP.two_point hxy
  simp only [Set.mem_ofPred_eq] at hh
  rw [hh]
  simp only [shiftedKernel_diagonal]
  simp only [shiftedKernel, if_neg hxy, if_neg (Ne.symm hxy),
    zero_add, one_mul, signedEntry_symmetric y x]
  ring

theorem distinct_prime_two_point (x y : Site) (hp : x.1 ≠ y.1) :
    law.real {z | z x = true ∧ z y = true} = 1/4 := by
  have hxy : x ≠ y := fun h => hp (congrArg Prod.fst h)
  rw [two_point x y hxy]
  simp [signedEntry, Ne.symm hp]

/-- The actual particle-hole dual changes the sign of the arithmetic correction. -/
theorem law_holes_isDPP : IsDPP law (fun x => {i | x i = false}) (shiftedKernel (-1)) := by
  constructor
  · intro i
    exact (measurableSet_singleton false).preimage (measurable_pi_apply i)
  · intro n e
    have hpos (S : Finset (Fin n)) : 0 ≤ exactWeight
        (Matrix.of (fun i j => shiftedKernel 1 (e i) (e j))) S := by
      apply exactWeight_nonneg
      · exact (shiftedKernel_posSemidef 1 (Or.inl rfl)).submatrix e
      · rw [principal_complement_eq]
        exact (shiftedKernel_posSemidef (-1) (Or.inr rfl)).submatrix e
    have hh := law_isDPP.finite_gap e hpos
    rw [principal_complement_eq] at hh
    simpa only [Set.mem_ofPred_eq, Bool.not_eq_true] using hh

/-- Particles and holes have the same two-site laws, although this does not
assert that their complete laws agree. -/
theorem holes_two_point_eq_particles (x y : Site) (hxy : x ≠ y) :
    law.real {z | z x = false ∧ z y = false} =
      law.real {z | z x = true ∧ z y = true} := by
  have hp := law_isDPP.two_point hxy
  have hh := law_holes_isDPP.two_point hxy
  simp only [Set.mem_ofPred_eq] at hp hh
  rw [hp, hh]
  simp only [shiftedKernel_diagonal]
  simp only [shiftedKernel, if_neg hxy, if_neg (Ne.symm hxy),
    zero_add, one_mul, neg_one_mul]
  ring

/-- Any finite choice of one site per distinct prime consists of independent
fair Bernoulli variables; the assertion includes every mixed configuration. -/
theorem distinct_prime_configuration {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι ↪ Site) (hp : Function.Injective (fun i => (e i).1)) (S : Finset ι) :
    law.real {z | ∀ i, z (e i) = decide (i ∈ S)} = (1/2 : ℝ) ^ Fintype.card ι := by
  have hmat : Matrix.of (fun i j => shiftedKernel 1 (e i) (e j)) =
      Matrix.diagonal (fun _ : ι => (1/2 : ℝ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · have hprime : (e j).1 ≠ (e i).1 := fun h => hij (hp h).symm
      have he : e i ≠ e j := fun h => hij (e.injective h)
      simp [shiftedKernel, signedEntry, hprime, he, Matrix.diagonal_apply, hij]
  have hpos (S : Finset ι) : 0 ≤ exactWeight
      (Matrix.of (fun i j => shiftedKernel 1 (e i) (e j))) S := by
    rw [hmat, exactWeight_diagonal]
    positivity
  have hh := law_isDPP.finite_configuration e hpos S
  simp only [Set.mem_ofPred_eq, Bool.decide_eq_true] at hh
  rw [hh, hmat, exactWeight_diagonal]
  norm_num
  rw [div_pow, one_pow, one_div]

end RiemannResearch.Probability.DPP.PrimeBlock
