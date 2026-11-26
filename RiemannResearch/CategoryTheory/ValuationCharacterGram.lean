import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Character moments of the inverse-square rough cofactor
Source: the user's character expansion of mixed CRT packets. The physical Q fibre
at smooth part s has masses proportional to n⁻² on integers coprime to the
cutoff primorial. At a common multiple of conductor and primorial, the Dirichlet
characters in the synthesis vanish on all excluded sites.
-/
open scoped BigOperators LSeries.notation Topology
open Filter
namespace RiemannResearch.CategoryTheory.ValuationCharacterGram
noncomputable section
/-- Total inverse-square mass on the integers coprime to the modulus.
The term at zero is zero by the division convention. -/
def roughMass (m : ℕ) : ℂ :=
  ∑' n : ℕ, (1 : DirichletCharacter ℂ m) n / (n : ℂ)^2

/-- The cofactor expectation of a character (extended by zero on nonunits). -/
def roughMoment {m : ℕ} (χ : DirichletCharacter ℂ m) : ℂ :=
  (∑' n : ℕ, χ n / (n : ℂ)^2) / roughMass m

private theorem summable_at_two {m : ℕ} (χ : DirichletCharacter ℂ m) :
    Summable (fun n : ℕ => χ n / (n : ℂ)^2) := by
  have h : 1 < (2 : ℂ).re := by norm_num
  simpa [dirichletSummandHom, Complex.cpow_neg, div_eq_mul_inv] using
    (summable_dirichletSummand χ h).of_norm

private theorem sum_at_two {m : ℕ} (χ : DirichletCharacter ℂ m) :
    (∑' n : ℕ, χ n / (n : ℂ)^2) = LSeries ↗χ 2 := by
  have h : 1 < (2 : ℂ).re := by norm_num
  simpa [dirichletSummandHom, Complex.cpow_neg, div_eq_mul_inv] using
    (tsum_dirichletSummand χ h)
theorem roughMoment_hasProd {m : ℕ} (χ : DirichletCharacter ℂ m) :
    HasProd (fun p : Nat.Primes =>
      (1 - (1 : DirichletCharacter ℂ m) p / (p : ℂ)^2) /
        (1 - χ p / (p : ℂ)^2)) (roughMoment χ) := by
  let ε : DirichletCharacter ℂ m := 1
  have h : 1 < (2 : ℂ).re := by norm_num
  have hn : LSeries ↗ε 2 ≠ 0 := by
    rw [← ε.LSeries_eulerProduct_exp_log h]
    exact Complex.exp_ne_zero _
  rw [roughMoment, sum_at_two, roughMass, sum_at_two]
  have ha := χ.LSeries_eulerProduct_hasProd h
  have hb := ε.LSeries_eulerProduct_hasProd h
  change Tendsto _ atTop _ at ha hb ⊢
  apply (ha.div hb hn).congr' (Filter.Eventually.of_forall fun s => ?_)
  simp [Pi.div_apply, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib, div_eq_mul_inv, Complex.cpow_neg, ε, mul_comm]

theorem roughMoment_ne_zero {m : ℕ} (χ : DirichletCharacter ℂ m) : roughMoment χ ≠ 0 := by
  have h : 1 < (2 : ℂ).re := by norm_num
  have hn (ψ : DirichletCharacter ℂ m) : LSeries ↗ψ 2 ≠ 0 := by
    rw [← ψ.LSeries_eulerProduct_exp_log h]
    exact Complex.exp_ne_zero _
  rw [roughMoment, roughMass, sum_at_two, sum_at_two]
  exact div_ne_zero (hn _) (hn _)

/-- Normalizing the cofactor series gives the same moment on each smooth fibre. -/
theorem scaled_roughMoment {m : ℕ} (χ : DirichletCharacter ℂ m) {c : ℂ} (hc : c ≠ 0) :
    (∑' n : ℕ, c * (χ n / (n : ℂ)^2)) /
      (∑' n : ℕ, c * ((1 : DirichletCharacter ℂ m) n / (n : ℂ)^2)) = roughMoment χ := by
  rw [tsum_mul_left, tsum_mul_left, roughMoment, roughMass, mul_div_mul_left _ _ hc]

/-- The prime cutoff is read from the prime divisors of the inflated modulus.
At an unrevealed prime the numerator of the Euler factor is 1-p⁻². -/
theorem cutoff_hasProd {m b : ℕ} (χ : DirichletCharacter ℂ m)
    (hcover : ∀ p : Nat.Primes, p.val ∣ m ↔ p.val ≤ b) :
    HasProd (fun p : Nat.Primes => if p.val ≤ b then (1 : ℂ) else
      (1 - 1 / (p : ℂ)^2) / (1 - χ p / (p : ℂ)^2)) (roughMoment χ) := by
  have he (p : Nat.Primes) :
      (1 - (1 : DirichletCharacter ℂ m) p / (p : ℂ)^2) /
        (1 - χ p / (p : ℂ)^2) =
      if p.val ≤ b then (1 : ℂ) else (1 - 1 / (p : ℂ)^2) / (1 - χ p / (p : ℂ)^2) := by
    by_cases h : p.val ≤ b
    · have hn : ¬ IsUnit (p.val : ZMod m) := fun hu =>
        (ZMod.isUnit_prime_iff_not_dvd p.property).1 hu ((hcover p).2 h)
      simp [h, MulChar.map_nonunit _ hn]
    · have hu : IsUnit (p.val : ZMod m) :=
        (ZMod.isUnit_prime_iff_not_dvd p.property).2 (fun hd => h ((hcover p).1 hd))
      simp [h, MulChar.one_apply hu]
  simpa only [he] using roughMoment_hasProd χ

/-- In the physical Q mass ratio on the fibre n = s z, the square of the
smooth factor, and the normalizing zeta value, cancel exactly. -/
theorem physical_fibre_moment {m : ℕ} (χ : DirichletCharacter ℂ m) {s : ℕ} (hs : 0 < s) :
    (∑' n : ℕ, (RiemannResearch.RH.ZetaTwoHilbert.positiveQWeight (s*n) : ℂ) * χ n) /
      (∑' n : ℕ, (RiemannResearch.RH.ZetaTwoHilbert.positiveQWeight (s*n) : ℂ) *
        (1 : DirichletCharacter ℂ m) n) = roughMoment χ := by
  let z : ℝ := RiemannResearch.RH.ZetaTwoProbability.zetaTwo
  let c : ℂ := ((z : ℂ)*(s : ℂ)^2)⁻¹
  have hz : 0 < z := RiemannResearch.RH.ZetaTwoProbability.zetaTwo_pos
  have hc : c ≠ 0 := by
    dsimp [c]
    apply inv_ne_zero
    exact mul_ne_zero (by exact_mod_cast hz.ne') (pow_ne_zero _ (by exact_mod_cast hs.ne'))
  have hw (n : ℕ) (x : ℂ) :
      (RiemannResearch.RH.ZetaTwoHilbert.positiveQWeight (s*n) : ℂ) * x =
        c * (x / (n : ℂ)^2) := by
    simp [RiemannResearch.RH.ZetaTwoHilbert.positiveQWeight, z, c, mul_pow, div_eq_mul_inv,
      mul_comm, mul_assoc, mul_left_comm]
  simpa only [hw] using (scaled_roughMoment χ hc)

/-- Fourier synthesis on the rough cofactor, with the usual zero extension. -/
def synthesis {ι : Type*} {m : ℕ} (s : Finset ι) (a : ι → ℂ)
    (χ : ι → DirichletCharacter ℂ m) (n : ℕ) : ℂ :=
  ∑ i ∈ s, a i * χ i n

/-- Actual rough-cofactor average of a profile already zero on nonunits. -/
def roughAverage (m : ℕ) (f : ℕ → ℂ) : ℂ :=
  (∑' n : ℕ, f n / (n : ℂ)^2) / roughMass m

theorem roughAverage_synthesis {ι : Type*} {m : ℕ} (s : Finset ι) (a : ι → ℂ)
    (χ : ι → DirichletCharacter ℂ m) :
    roughAverage m (synthesis s a χ) = ∑ i ∈ s, a i * roughMoment (χ i) := by
  have h := hasSum_sum (s := s) (fun i _ => (summable_at_two (χ i)).hasSum.mul_left (a i))
  have he (n : ℕ) : synthesis s a χ n / (n : ℂ)^2 =
      ∑ i ∈ s, a i * (χ i n / (n : ℂ)^2) := by
    simp [synthesis, Finset.sum_div, mul_div_assoc]
  simp only [roughAverage, he, h.tsum_eq, Finset.sum_div, roughMoment, mul_div_assoc]

/-- Signed conditional covariance kernel, linear in its first argument. -/
def charCov {m : ℕ} (χ ψ : DirichletCharacter ℂ m) : ℂ :=
  roughMoment (χ * ψ.ringHomComp (starRingEnd ℂ)) -
    roughMoment χ * star (roughMoment ψ)

/-- Polarized covariance for two arbitrary finite character expansions. The
left side uses the physical inverse-square sum on the whole rough cofactor. -/
theorem rough_covariance_synthesis {ι κ : Type*} {m : ℕ} (s : Finset ι) (t : Finset κ)
    (a : ι → ℂ) (b : κ → ℂ) (χ : ι → DirichletCharacter ℂ m)
    (ψ : κ → DirichletCharacter ℂ m) :
    roughAverage m (fun n => synthesis s a χ n * star (synthesis t b ψ n)) -
      roughAverage m (synthesis s a χ) * star (roughAverage m (synthesis t b ψ)) =
      ∑ i ∈ s, ∑ j ∈ t, (a i * star (b j)) * charCov (χ i) (ψ j) := by
  classical
  let c := fun ij : ι × κ => a ij.1 * star (b ij.2)
  let θ := fun ij : ι × κ => χ ij.1 * (ψ ij.2).ringHomComp (starRingEnd ℂ)
  have he : (fun n => synthesis s a χ n * star (synthesis t b ψ n)) =
      synthesis (s ×ˢ t) c θ := by
    funext n
    simp only [synthesis, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum,
      Finset.sum_product, c, θ, MulChar.mul_apply, MulChar.ringHomComp_apply,
      starRingEnd_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, roughAverage_synthesis, roughAverage_synthesis, roughAverage_synthesis]
  simp only [c, θ, charCov, Finset.sum_product, star_sum, star_mul', Finset.sum_mul,
    Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Uniform Fourier coefficient on the units. Evaluation at the inverse
unit is complex conjugation of a unitary character value. -/
def unitCoefficient {m : ℕ} [NeZero m] (f : (ZMod m)ˣ → ℂ)
    (χ : DirichletCharacter ℂ m) : ℂ :=
  ∑ v : (ZMod m)ˣ, (f v / (m.totient : ℂ)) * χ ((v : ZMod m)⁻¹)

theorem unitFourier_reconstruct {m : ℕ} [NeZero m] (f : (ZMod m)ˣ → ℂ)
    (u : (ZMod m)ˣ) :
    ∑ χ : DirichletCharacter ℂ m, unitCoefficient f χ * χ u = f u := by
  classical
  have ht : (m.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m))).ne'
  simp only [unitCoefficient, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  have ho (v : (ZMod m)ˣ) := DirichletCharacter.sum_char_inv_mul_char_eq ℂ v.isUnit (u : ZMod m)
  simp_rw [← Finset.mul_sum, ho]
  simp [Units.val_inj, mul_ite, ht]

/-- A zero-extended arbitrary fibre profile on the cofactor integer sites. -/
def unitProfile {m : ℕ} (f : (ZMod m)ˣ → ℂ) (n : ℕ) : ℂ := by
  classical
  exact if h : IsUnit (n : ZMod m) then f h.unit else 0

theorem synthesis_unitProfile {m : ℕ} [NeZero m] (f : (ZMod m)ˣ → ℂ) :
    synthesis Finset.univ (unitCoefficient f) id = unitProfile f := by
  classical
  funext n
  by_cases h : IsUnit (n : ZMod m)
  · simpa only [unitProfile, dif_pos h, synthesis, id_eq, h.unit_spec] using
      (unitFourier_reconstruct f h.unit)
  · simp [synthesis, unitProfile, h, MulChar.map_nonunit _ h]

/-- Complete signed conditional cofactor Gram for arbitrary functions on the
unit group, including profiles z ↦ J_k(s*z) on noncoprime smooth fibres. -/
theorem unitProfile_covariance {m : ℕ} [NeZero m] (f g : (ZMod m)ˣ → ℂ) :
    roughAverage m (fun n => unitProfile f n * star (unitProfile g n)) -
      roughAverage m (unitProfile f) * star (roughAverage m (unitProfile g)) =
      ∑ χ : DirichletCharacter ℂ m, ∑ ψ : DirichletCharacter ℂ m,
        (unitCoefficient f χ * star (unitCoefficient g ψ)) * charCov χ ψ := by
  simpa only [synthesis_unitProfile, id_eq] using
    (rough_covariance_synthesis Finset.univ Finset.univ (unitCoefficient f)
      (unitCoefficient g) id id)

end
end RiemannResearch.CategoryTheory.ValuationCharacterGram
