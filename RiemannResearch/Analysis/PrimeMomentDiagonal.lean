import Mathlib.Data.Nat.Factors
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

/-!
The combinatorial diagonal bound for powers of a prime Dirichlet polynomial.
The factorial comes from counting permutations of a list of prime factors.
Source for this standard diagonal estimate: K.-M. Tsang,
Some Ω-theorems for the Riemann zeta-function, Acta Arith. 46 (1986),
Section 4, https://matwbn.icm.edu.pl/ksiazki/aa/aa46/aa4646.pdf.
The proof here counts prime-factor permutations explicitly.
-/

open scoped BigOperators

noncomputable section

namespace RiemannResearch.Analysis.PrimeMoment

variable {α : Type*} [Fintype α]

def tupleProduct (p : α → ℕ) {k : ℕ} (f : Fin k → α) : ℕ :=
  ∏ i, p (f i)

def tupleCoefficient (a : α → ℂ) {k : ℕ} (f : Fin k → α) : ℂ :=
  ∏ i, a (f i)

def primePowerCoefficient (p : α → ℕ) (a : α → ℂ) (k n : ℕ) : ℂ :=
  ∑ f ∈ Finset.univ.filter (fun f : Fin k → α => tupleProduct p f = n),
    tupleCoefficient a f

theorem tupleProduct_pos (p : α → ℕ) (hp : ∀ x, 0 < p x)
    {k : ℕ} (f : Fin k → α) : 0 < tupleProduct p f := by
  exact Finset.prod_pos fun i hi => hp (f i)

theorem tupleProduct_le_pow (p : α → ℕ) (X : ℕ) (hpX : ∀ x, p x ≤ X)
    {k : ℕ} (f : Fin k → α) : tupleProduct p f ≤ X ^ k := by
  calc
    tupleProduct p f ≤ ∏ i : Fin k, X := by
      exact Finset.prod_le_prod (fun i hi => Nat.zero_le _) (fun i hi => hpX (f i))
    _ = X ^ k := by simp

theorem tupleProduct_mem_Icc (p : α → ℕ) (hp : ∀ x, Nat.Prime (p x))
    (X : ℕ) (hpX : ∀ x, p x ≤ X) {k : ℕ} (f : Fin k → α) :
    tupleProduct p f ∈ Finset.Icc 1 (X ^ k) := by
  exact Finset.mem_Icc.mpr ⟨tupleProduct_pos p (fun x => (hp x).pos) f,
    tupleProduct_le_pow p X hpX f⟩

theorem prime_tuple_product_fiber_card_le
    (p : α → ℕ) (hp : ∀ x, Nat.Prime (p x)) (hinj : Function.Injective p)
    (k n : ℕ) :
    (Finset.univ.filter (fun f : Fin k → α => tupleProduct p f = n)).card ≤
      k.factorial := by
  classical
  let F := Finset.univ.filter (fun f : Fin k → α => tupleProduct p f = n)
  change F.card ≤ k.factorial
  by_cases hF : F.Nonempty
  · obtain ⟨f, hf⟩ := hF
    let L : (Fin k → α) → List ℕ := fun g => List.ofFn (fun i => p (g i))
    have hLinj : Function.Injective L := by
      intro g h heq
      have heq' : (fun i => p (g i)) = (fun i => p (h i)) :=
        List.ofFn_injective heq
      funext i
      exact hinj (congrFun heq' i)
    have hprime (g : Fin k → α) : ∀ q ∈ L g, Nat.Prime q := by
      intro q hq
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
      exact hp (g i)
    have hsub : F.image L ⊆ (L f).permutations.toFinset := by
      intro l hl
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hl
      apply List.mem_toFinset.mpr
      apply List.mem_permutations.mpr
      have hprod : (L g).prod = (L f).prod := by
        have hg' : tupleProduct p g = n := (Finset.mem_filter.mp hg).2
        have hf' : tupleProduct p f = n := (Finset.mem_filter.mp hf).2
        simpa [L, tupleProduct, List.prod_ofFn] using hg'.trans hf'.symm
      exact (Nat.primeFactorsList_unique hprod (hprime g)).trans
        (Nat.primeFactorsList_unique rfl (hprime f)).symm
    calc
      F.card = (F.image L).card := (Finset.card_image_of_injective F hLinj).symm
      _ ≤ (L f).permutations.toFinset.card := Finset.card_le_card hsub
      _ ≤ (L f).permutations.length := List.toFinset_card_le _
      _ = k.factorial := by rw [List.length_permutations]; simp [L]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hF]

theorem norm_sum_sq_le_card_mul_sum_norm_sq {β : Type*}
    (s : Finset β) (c : β → ℂ) :
    ‖∑ x ∈ s, c x‖ ^ 2 ≤ (s.card : ℝ) * ∑ x ∈ s, ‖c x‖ ^ 2 := by
  calc
    ‖∑ x ∈ s, c x‖ ^ 2 ≤ (∑ x ∈ s, ‖c x‖) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s c) 2
    _ ≤ (s.card : ℝ) * ∑ x ∈ s, ‖c x‖ ^ 2 := sq_sum_le_card_mul_sum_sq

theorem primePowerCoefficient_sq_le
    (p : α → ℕ) (hp : ∀ x, Nat.Prime (p x)) (hinj : Function.Injective p)
    (a : α → ℂ) (k n : ℕ) :
    ‖primePowerCoefficient p a k n‖ ^ 2 ≤ (k.factorial : ℝ) *
      ∑ f ∈ Finset.univ.filter (fun f : Fin k → α => tupleProduct p f = n),
        ‖tupleCoefficient a f‖ ^ 2 := by
  classical
  refine (norm_sum_sq_le_card_mul_sum_norm_sq _ _).trans ?_
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast prime_tuple_product_fiber_card_le p hp hinj k n
  · exact Finset.sum_nonneg fun f hf => sq_nonneg _

theorem sum_primePowerCoefficient_sq_le
    (p : α → ℕ) (hp : ∀ x, Nat.Prime (p x)) (hinj : Function.Injective p)
    (a : α → ℂ) (k : ℕ) (N : Finset ℕ) :
    ∑ n ∈ N, ‖primePowerCoefficient p a k n‖ ^ 2 ≤
      (k.factorial : ℝ) * (∑ x, ‖a x‖ ^ 2) ^ k := by
  classical
  have hfiber :
      (∑ n ∈ N, ∑ f ∈ Finset.univ.filter
          (fun f : Fin k → α => tupleProduct p f = n),
        ‖tupleCoefficient a f‖ ^ 2) ≤
      ∑ f : Fin k → α, ‖tupleCoefficient a f‖ ^ 2 := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro f hf
    by_cases h : tupleProduct p f ∈ N
    · simp [eq_comm, h]
    · simpa [eq_comm, h] using sq_nonneg (‖tupleCoefficient a f‖)
  have hpower : (∑ f : Fin k → α, ‖tupleCoefficient a f‖ ^ 2) =
      (∑ x, ‖a x‖ ^ 2) ^ k := by
    rw [Fintype.sum_pow]
    apply Finset.sum_congr rfl
    intro f hf
    simp [tupleCoefficient, norm_prod, Finset.prod_pow]
  calc
    ∑ n ∈ N, ‖primePowerCoefficient p a k n‖ ^ 2 ≤
        ∑ n ∈ N, (k.factorial : ℝ) *
          ∑ f ∈ Finset.univ.filter (fun f : Fin k → α => tupleProduct p f = n),
            ‖tupleCoefficient a f‖ ^ 2 := by
      exact Finset.sum_le_sum fun n hn => primePowerCoefficient_sq_le p hp hinj a k n
    _ = (k.factorial : ℝ) *
        (∑ n ∈ N, ∑ f ∈ Finset.univ.filter
          (fun f : Fin k → α => tupleProduct p f = n),
            ‖tupleCoefficient a f‖ ^ 2) := by rw [Finset.mul_sum]
    _ ≤ (k.factorial : ℝ) * ∑ f : Fin k → α, ‖tupleCoefficient a f‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_left hfiber (Nat.cast_nonneg _)
    _ = (k.factorial : ℝ) * (∑ x, ‖a x‖ ^ 2) ^ k := by rw [hpower]

/-- Regroup the expanded power by its integer frequencies. -/
theorem sum_primePowerCoefficient_mul
    (p : α → ℕ) (a : α → ℂ) (k : ℕ) (N : Finset ℕ)
    (hN : ∀ f : Fin k → α, tupleProduct p f ∈ N) (χ : ℕ → ℂ) :
    ∑ n ∈ N, primePowerCoefficient p a k n * χ n =
      ∑ f : Fin k → α, tupleCoefficient a f * χ (tupleProduct p f) := by
  classical
  simp_rw [primePowerCoefficient, Finset.sum_mul, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f hf
  simp [eq_comm, hN f]

/-- A character need only preserve the products of the tuples actually used. -/
theorem primePolynomial_pow_expansion
    (p : α → ℕ) (a : α → ℂ) (k : ℕ) (N : Finset ℕ)
    (hN : ∀ f : Fin k → α, tupleProduct p f ∈ N) (χ : ℕ → ℂ)
    (hχ : ∀ f : Fin k → α, χ (tupleProduct p f) = ∏ i, χ (p (f i))) :
    (∑ x, a x * χ (p x)) ^ k =
      ∑ n ∈ N, primePowerCoefficient p a k n * χ n := by
  rw [Fintype.sum_pow, sum_primePowerCoefficient_mul p a k N hN χ]
  apply Finset.sum_congr rfl
  intro f hf
  rw [hχ]
  simp [tupleCoefficient, Finset.prod_mul_distrib]

end RiemannResearch.Analysis.PrimeMoment
