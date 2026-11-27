import RiemannResearch.CategoryTheory.ArbitraryCutoffCharacterProduct
import RiemannResearch.CategoryTheory.DivisibilityCharacterGram
import RiemannResearch.CategoryTheory.PrimeValuationCovariance
import Mathlib.NumberTheory.Primorial

/-!
# Physical valuation-fibre expectations

Source: the user's CRT packet character decomposition, equations (5) and (6).
The physical orthogonal projection is reindexed on the entire rough cofactor.
The mode formula uses the gcd of the conductor shift with the actual smooth
part, so an incompatible observed exponent is visible as an explicit zero.
-/

noncomputable section
open RiemannResearch.RH.ZetaTwoHilbert RiemannResearch.RH.ZetaTwoProbability
open RiemannResearch.CategoryTheory.DivisibilityCharacterGram
open RiemannResearch.CategoryTheory.ValuationCharacterGram
open RiemannResearch.CategoryTheory.PrimeValuationCovariance

namespace RiemannResearch.CategoryTheory.ObservedModeFibre

/-- A cutoff modulus has precisely the revealed primes as its divisors. -/
def Covers (R b : ℕ) : Prop := ∀ p : ℕ, p.Prime → (p ∣ R ↔ p ≤ b)

theorem primorial_covers (b : ℕ) : Covers (primorial b) b :=
  fun _ hp => hp.dvd_primorial_iff

private theorem rough_iff_coprime {R b : ℕ} (hR : Covers R b) (n : ℕ) :
    (∀ p : ℕ, p.Prime → p ≤ b → ¬p ∣ n) ↔ n.Coprime R := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨p,hp,hpn,hpR⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    exact h p hp ((hR p hp).1 hpR) hpn
  · intro h p hp hpb hpn
    exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p,hp,hpn,(hR p hp).2 hpb⟩) h

/-- Reindex the physical mass of one fibre against an arbitrary real profile.
The probability of a site is zero at the unused coordinate zero. -/
private theorem fibre_weighted_sum {R b : ℕ} (hR : Covers R b) (s : ℕ+)
    (hs : ∀ p ∈ (s : ℕ).primeFactors, p ≤ b) (f : ℕ → ℝ) :
    (∑' n, positiveQWeight n * fibreMark b s n * f n) =
      (1 / (zetaTwo * (s : ℝ)^2)) *
        ∑' m : ℕ, if m.Coprime R then f ((s : ℕ)*m)/(m : ℝ)^2 else 0 := by
  classical
  let t := fun n : ℕ => positiveQWeight n * fibreMark b s n * f n
  have hinj : Function.Injective (fun m : ℕ => (s : ℕ)*m) :=
    fun _ _ h => Nat.eq_of_mul_eq_mul_left s.pos h
  have hsupport : Function.support t ⊆ Set.range (fun m : ℕ => (s : ℕ)*m) := by
    intro n hn
    by_cases hn0 : 0 < n
    · by_cases hf : sameFibre b s ⟨n,hn0⟩
      · obtain ⟨m,he,_⟩ := (sameFibre_iff_rough_multiple b s ⟨n,hn0⟩ hs).1 hf
        exact ⟨m,he.symm⟩
      · exact (hn (by simp [t,fibreMark,hn0,hf])).elim
    · exact (hn (by simp [t,fibreMark,hn0])).elim
  have hterm (m : ℕ) : t ((s : ℕ)*m) = (1 / (zetaTwo * (s : ℝ)^2)) *
      (if m.Coprime R then f ((s : ℕ)*m)/(m : ℝ)^2 else 0) := by
    rcases m with _ | m
    · by_cases hc : (0 : ℕ).Coprime R <;> simp [t,positiveQWeight,fibreMark,hc]
    have hn : 0 < (s : ℕ)*(m+1) := Nat.mul_pos s.pos (Nat.succ_pos m)
    let site : ℕ+ := ⟨(s : ℕ)*(m+1),hn⟩
    have hsame : sameFibre b s site ↔ (m+1).Coprime R := by
      apply (sameFibre_iff_rough_multiple b s site hs).trans
      refine Iff.trans ?_ (rough_iff_coprime hR (m+1))
      constructor
      · rintro ⟨z,hz,hrough⟩
        have he : m+1 = (z : ℕ) := Nat.eq_of_mul_eq_mul_left s.pos hz
        rwa [he]
      · exact fun h => ⟨⟨m+1,Nat.succ_pos _⟩,rfl,h⟩
    have hmark : fibreMark b s ((s : ℕ)*(m+1)) = (if (m+1).Coprime R then 1 else 0) := by
      unfold fibreMark
      rw [dif_pos hn]
      change (if sameFibre b s site then (1 : ℝ) else 0) = _
      exact if_congr hsame rfl rfl
    by_cases hc : (m+1).Coprime R
    · simp only [t, hmark, if_pos hc, mul_one, positiveQWeight, Nat.cast_mul,
        mul_pow, div_eq_mul_inv, mul_inv, one_mul]
      ring
    · simp [t,hmark,hc]
  change (∑' n, t n) = _
  rw [← hinj.tsum_eq hsupport]
  simp_rw [hterm]
  exact tsum_mul_left

/-- The star projection at the physical site s is the normalized rough
inverse-square average with its smooth part inserted into the profile. -/
theorem observed_rough_ratio {R b : ℕ} (hR : Covers R b) (s : ℕ+)
    (hs : ∀ p ∈ (s : ℕ).primeFactors, p ≤ b) (x : QHilbert) :
    qSequence ((observed b).starProjection x) s =
      (∑' m : ℕ, if m.Coprime R then qSequence x ((s : ℕ)*m)/(m : ℝ)^2 else 0) /
      (∑' m : ℕ, if m.Coprime R then 1/(m : ℝ)^2 else 0) := by
  rw [observed_fibre_mean, fibre_weighted_sum hR s hs]
  have hden := fibre_weighted_sum hR s hs (fun _ => 1)
  simp only [mul_one] at hden
  rw [hden, mul_div_mul_left]
  exact one_div_ne_zero (mul_ne_zero zetaTwo_pos.ne' (pow_ne_zero _ (by exact_mod_cast s.pos.ne')))

/-- The complex rough-cofactor ratio on a physical fibre. The factor k is the
remaining divisibility cost after removing gcd(g,s) from the shift g. -/
theorem arbitrary_mode_rough_ratio {q : ℕ} (R g s : ℕ) (hg : 0 < g)
    (χ : DirichletCharacter ℂ q) :
    let d := Nat.gcd g s
    let k := g/d
    let u := s/d
    (∑' n : ℕ, (1 : DirichletCharacter ℂ R) n * mode g χ (s*n)/(n : ℂ)^2) / roughMass R =
      if k.Coprime R then (χ (↑u : ZMod q) / (k : ℂ)^2) *
        ((∑' n : ℕ, (1 : DirichletCharacter ℂ R) n * χ (↑n : ZMod q)/(n : ℂ)^2) /
          roughMass R) else 0 := by
  intro d k u
  have hd : 0 < d := Nat.gcd_pos_of_pos_left s hg
  have hdg : d*k = g := Nat.mul_div_cancel' (Nat.gcd_dvd_left g s)
  have hds : d*u = s := Nat.mul_div_cancel' (Nat.gcd_dvd_right g s)
  have hk : 0 < k := by
    by_contra! h
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero h
    have he : g = 0 := by simpa [hk0] using hdg.symm
    omega
  have hku : k.Coprime u := Nat.coprime_div_gcd_div_gcd hd
  have heq (n : ℕ) : mode g χ (s*n) = mode k χ (u*n) := by
    rw [← hdg, ← hds]
    simp [mode, Nat.mul_assoc, Nat.mul_dvd_mul_iff_left hd, Nat.mul_div_mul_left _ _ hd]
  simp_rw [heq]
  by_cases h : k.Coprime R
  · rw [if_pos h, rough_scaled_mode R k u 2 hk hku h χ, mul_div_assoc]
  · rw [if_neg h]
    have hterm (n : ℕ) : (1 : DirichletCharacter ℂ R) n * mode k χ (u*n)/(n : ℂ)^2 = 0 := by
      by_cases hdvd : k ∣ u*n
      · have hkn : k ∣ n := hku.dvd_of_dvd_mul_left hdvd
        have hnr : ¬n.Coprime R := fun hz => h (hz.coprime_dvd_left hkn)
        have hnu : ¬IsUnit (n : ZMod R) := fun hz => hnr ((ZMod.isUnit_iff_coprime n R).mp hz)
        simp [MulChar.map_nonunit _ hnu]
      · simp [mode,hdvd]
    simp_rw [hterm]
    simp

private theorem norm_mode_le_one {q : ℕ} (g n : ℕ) (χ : DirichletCharacter ℂ q) :
    ‖mode g χ n‖ ≤ 1 := by
  by_cases h : g ∣ n
  · simpa [mode,h] using χ.norm_le_one (↑(n/g) : ZMod q)
  · simp [mode,h]

private theorem principal_nat {R : ℕ} (n : ℕ) :
    (1 : DirichletCharacter ℂ R) n = if n.Coprime R then 1 else 0 := by
  by_cases h : n.Coprime R
  · exact (MulChar.one_apply ((ZMod.isUnit_iff_coprime n R).2 h)).trans (if_pos h).symm
  · rw [if_neg h]
    exact MulChar.map_nonunit _ (fun hz => h ((ZMod.isUnit_iff_coprime n R).1 hz))

/-- Real and imaginary parts are both instances of this result, via reCLM
and imCLM respectively. The coordinate hypothesis concerns only positive
physical sites because the Q Hilbert realization has a dummy site at zero. -/
theorem observed_mode_component {R b q : ℕ} (hR : Covers R b) (s : ℕ+)
    (hs : ∀ p ∈ (s : ℕ).primeFactors, p ≤ b) (g : ℕ) (hg : 0 < g)
    (χ : DirichletCharacter ℂ q) (L : ℂ →L[ℝ] ℝ) (x : QHilbert)
    (hx : ∀ n : ℕ, 0 < n → qSequence x n = L (mode g χ n)) :
    let d := Nat.gcd g (s : ℕ)
    let k := g/d
    let u := (s : ℕ)/d
    qSequence ((observed b).starProjection x) s =
      L (if k.Coprime R then (χ (↑u : ZMod q) / (k : ℂ)^2) *
        ((∑' n : ℕ, (1 : DirichletCharacter ℂ R) n * χ (↑n : ZMod q)/(n : ℂ)^2) /
          roughMass R) else 0) := by
  intro d k u
  rw [← arbitrary_mode_rough_ratio R g s hg χ, observed_rough_ratio hR s hs x]
  let D : ℝ := ∑' n : ℕ, if n.Coprime R then 1/(n : ℝ)^2 else 0
  let t := fun n : ℕ => (1 : DirichletCharacter ℂ R) n * mode g χ ((s : ℕ)*n)/(n : ℂ)^2
  have hmass : roughMass R = (D : ℂ) := by
    rw [roughMass, show (D : ℂ) = _ from Complex.ofReal_tsum _]
    apply tsum_congr
    intro n
    rw [principal_nat]
    split_ifs <;> push_cast <;> simp
  have tsum_ok : Summable t := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      _ (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
    intro n
    have hprod : ‖(1 : DirichletCharacter ℂ R) n * mode g χ ((s : ℕ)*n)‖ ≤ 1 :=
      (norm_mul _ _).trans_le (mul_le_one₀ ((1 : DirichletCharacter ℂ R).norm_le_one n)
        (norm_nonneg _) (norm_mode_le_one g _ χ))
    change ‖_ / (n : ℂ)^2‖ ≤ _
    rw [norm_div, norm_pow, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right hprod (sq_nonneg _)
  have hreal (z : ℂ) (r : ℝ) : L (z / (r : ℂ)) = L z / r := by
    rw [div_eq_mul_inv, mul_comm, ← Complex.ofReal_inv, ← Complex.real_smul, map_smul,
      smul_eq_mul, mul_comm, ← div_eq_mul_inv]
  have hterm (n : ℕ) : L (t n) =
      if n.Coprime R then qSequence x ((s : ℕ)*n)/(n : ℝ)^2 else 0 := by
    dsimp only [t]
    rw [principal_nat]
    by_cases h : n.Coprime R
    · rw [if_pos h, if_pos h, one_mul]
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, hreal]
      by_cases hn : n = 0
      · subst n
        simp
      · rw [hx _ (Nat.mul_pos s.pos (Nat.pos_of_ne_zero hn))]
    · simp [h]
  rw [hmass, hreal]
  change _ / D = L (∑' n, t n) / D
  rw [L.map_tsum tsum_ok]
  simp only [hterm]

/-- Every real component of a shifted character has the required physical
representative, including the principal character of modulus one. -/
theorem exists_mode_component {q : ℕ} (g : ℕ) (χ : DirichletCharacter ℂ q) (L : ℂ →L[ℝ] ℝ) :
    ∃ x : QHilbert, ∀ n : ℕ, 0 < n → qSequence x n = L (mode g χ n) := by
  let f := fun n : ℕ => if n = 0 then 0 else L (mode g χ n)
  have hbound (n : ℕ) : |f n| ≤ ‖L‖ := by
    by_cases h : n = 0
    · simp [f,h]
    · rw [show f n = _ from if_neg h, ← Real.norm_eq_abs]
      exact (L.le_opNorm _).trans ((mul_le_mul_of_nonneg_left
        (norm_mode_le_one g n χ) (norm_nonneg L)).trans_eq (mul_one _))
  have hsum := boundedQ_square_summable f ‖L‖ (norm_nonneg L) hbound
  exact ⟨encodeQ f hsum, fun n hn => by
    rw [qSequence_encodeQ f hsum (by simp [f])]
    simp [f, hn.ne']⟩

/-- The physical orthogonal projection equals the complete tail Euler product
at any cutoff, including cutoffs below the character's conductor primes. -/
theorem observed_mode_component_euler {b q : ℕ} (s : ℕ+)
    (hs : ∀ p ∈ (s : ℕ).primeFactors, p ≤ b) (g : ℕ) (hg : 0 < g)
    (χ : DirichletCharacter ℂ q) (L : ℂ →L[ℝ] ℝ) (x : QHilbert)
    (hx : ∀ n : ℕ, 0 < n → qSequence x n = L (mode g χ n)) :
    let d := Nat.gcd g (s : ℕ)
    let k := g/d
    let u := (s : ℕ)/d
    qSequence ((observed b).starProjection x) s =
      L (if k.Coprime (primorial b) then (χ (↑u : ZMod q) / (k : ℂ)^2) *
        (∏' p : Nat.Primes, if p.val ≤ b then (1 : ℂ) else
          (1-1/(p : ℂ)^2)/(1-χ p/(p : ℂ)^2)) else 0) := by
  simpa only [ValuationCharacterGram.primorial_roughRatio_tprod b χ] using
    observed_mode_component (primorial_covers b) s hs g hg χ L x hx


private theorem cutoffExponents_le (b : ℕ) (n : ℕ+) :
    (n : ℕ).factorization.filter (· ≤ b) ≤ (n : ℕ).factorization := by
  intro p
  by_cases h : p ≤ b <;> simp [h]

/-- The positive integer made of precisely the observed prime powers of n. -/
def smoothSite (b : ℕ) (n : ℕ+) : ℕ+ :=
  let v := (n : ℕ).factorization.filter (· ≤ b)
  ⟨v.prod (· ^ ·), Nat.pos_of_ne_zero (fun hz => n.pos.ne' (by
    have hdvd : v.prod (· ^ ·) ∣ (n : ℕ) := Nat.prod_pow_dvd_of_le_factorization (cutoffExponents_le b n)
    rw [hz, zero_dvd_iff] at hdvd
    exact hdvd))⟩

theorem smoothSite_fibre (b : ℕ) (n : ℕ+) :
    (∀ p ∈ ((smoothSite b n : ℕ+) : ℕ).primeFactors, p ≤ b) ∧ sameFibre b (smoothSite b n) n := by
  have hv : ((smoothSite b n : ℕ+) : ℕ).factorization = (n : ℕ).factorization.filter (· ≤ b) :=
    Nat.factorization_prod_pow_eq_self_of_le_factorization (cutoffExponents_le b n)
  constructor
  · intro p hp
    change p ∈ ((smoothSite b n : ℕ+) : ℕ).factorization.support at hp
    rw [hv, Finsupp.support_filter] at hp
    exact (Finset.mem_filter.mp hp).2
  · intro p _ hb
    change ((smoothSite b n : ℕ+) : ℕ).factorization p = (n : ℕ).factorization p
    simp [hv, hb]

/-- Equation (5) evaluated at every positive integer site, using the actual
smooth part and both compatible and incompatible conductor shifts. -/
theorem observed_mode_at_site {q : ℕ} (b : ℕ) (n : ℕ+) (g : ℕ) (hg : 0 < g)
    (χ : DirichletCharacter ℂ q) (L : ℂ →L[ℝ] ℝ) (x : QHilbert)
    (hx : ∀ j : ℕ, 0 < j → qSequence x j = L (mode g χ j)) :
    let s := (smoothSite b n : ℕ)
    let d := Nat.gcd g s
    let k := g / d
    let u := s / d
    qSequence ((observed b).starProjection x) n =
      L (if k.Coprime (primorial b) then (χ (↑u : ZMod q) / (k : ℂ)^2) *
        (∏' p : Nat.Primes, if p.val ≤ b then (1 : ℂ) else
          (1-1/(p : ℂ)^2)/(1-χ p/(p : ℂ)^2)) else 0) := by
  have h := smoothSite_fibre b n
  have he := (mem_observed b _).1 ((observed b).starProjection_apply_mem x) (smoothSite b n) n h.2
  exact he.symm.trans (observed_mode_component_euler (smoothSite b n) h.1 g hg χ L x hx)

end RiemannResearch.CategoryTheory.ObservedModeFibre
#print axioms RiemannResearch.CategoryTheory.ObservedModeFibre.observed_rough_ratio
#print axioms RiemannResearch.CategoryTheory.ObservedModeFibre.arbitrary_mode_rough_ratio

#print axioms RiemannResearch.CategoryTheory.ObservedModeFibre.observed_mode_component
#print axioms RiemannResearch.CategoryTheory.ObservedModeFibre.exists_mode_component
#print axioms RiemannResearch.CategoryTheory.ObservedModeFibre.observed_mode_component_euler
#print axioms RiemannResearch.CategoryTheory.ObservedModeFibre.observed_mode_at_site
