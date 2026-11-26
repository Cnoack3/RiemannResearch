import RiemannResearch.CategoryTheory.ValuationCharacterGram

/-! # Divisibility-character modes in a Dirichlet-power Gram
Source: the user's CRT packet character decomposition, formula (6).
The full site pairing allows distinct character moduli and arbitrary positive divisors.
Integer exponents at least two supply the polynomial Pareto weight approximation.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.CategoryTheory.DivisibilityCharacterGram

def mode {m : ℕ} (g : ℕ) (χ : DirichletCharacter ℂ m) (n : ℕ) : ℂ :=
  if g ∣ n then χ ((n/g : ℕ) : ZMod m) else 0

/-- The complete unnormalized Gram at exponent s, with both character phases.
For s=2 divide both sides by zeta(2) for the physical Q Gram. -/
theorem powerGram {a b : ℕ} (g h s : ℕ) (hg : 0 < g) (hh : 0 < h)
    (χ : DirichletCharacter ℂ a) (ψ : DirichletCharacter ℂ b) :
    let L := g.lcm h
    (∑' n : ℕ, mode g χ n * star (mode h ψ n) / (n : ℂ)^s) =
      (χ ((L/g : ℕ) : ZMod a) * star (ψ ((L/h : ℕ) : ZMod b)) / (L : ℂ)^s) *
        ∑' k : ℕ, χ (k : ZMod a) * star (ψ (k : ZMod b)) / (k : ℂ)^s := by
  intro L
  have hL : 0 < L := Nat.lcm_pos hg hh
  have hinj : Function.Injective (fun k : ℕ => L*k) := fun _ _ h => Nat.eq_of_mul_eq_mul_left hL h
  have support : Function.support (fun n : ℕ =>
      mode g χ n * star (mode h ψ n) / (n : ℂ)^s) ⊆ Set.range (fun k : ℕ => L*k) := by
    intro n hn
    by_cases hd : L ∣ n
    · obtain ⟨k,rfl⟩ := hd
      exact ⟨k,rfl⟩
    · have hno : ¬(g ∣ n ∧ h ∣ n) := by simpa only [L, Nat.lcm_dvd_iff] using hd
      by_cases hx : g ∣ n <;> by_cases hy : h ∣ n <;>
        simp_all [Function.mem_support, mode]
  rw [← hinj.tsum_eq support, ← tsum_mul_left]
  apply tsum_congr
  intro k
  have divscale (d : ℕ) (hd : d ∣ L) : L*k/d = (L/d)*k := by
    rw [Nat.mul_comm L k, Nat.mul_div_assoc _ hd, Nat.mul_comm k]
  have hgL : g ∣ L := Nat.dvd_lcm_left g h
  have hhL : h ∣ L := Nat.dvd_lcm_right g h
  simp only [mode, if_pos (hgL.trans (dvd_mul_right L k)),
    if_pos (hhL.trans (dvd_mul_right L k)), divscale g hgL, divscale h hhL, Nat.cast_mul,
    map_mul, star_mul', mul_pow, div_eq_mul_inv, mul_inv]
  ring

/-- Character average on a rough fibre when a remaining divisor d is coprime
to its known multiplier c and to the primes excluded by the rough modulus R. -/
theorem rough_scaled_mode {m : ℕ} (R d c s : ℕ) (hd : 0 < d) (hcd : d.Coprime c)
    (hR : d.Coprime R) (χ : DirichletCharacter ℂ m) :
    (∑' n : ℕ, (1 : DirichletCharacter ℂ R) n * mode d χ (c*n) / (n : ℂ)^s) =
      (χ (c : ZMod m) / (d : ℂ)^s) *
        ∑' n : ℕ, (1 : DirichletCharacter ℂ R) n * χ (n : ZMod m) / (n : ℂ)^s := by
  have hinj : Function.Injective (fun k : ℕ => d*k) := fun _ _ h => Nat.eq_of_mul_eq_mul_left hd h
  have support : Function.support (fun n : ℕ =>
      (1 : DirichletCharacter ℂ R) n * mode d χ (c*n) / (n : ℂ)^s) ⊆
      Set.range (fun k : ℕ => d*k) := by
    intro n hn
    by_cases hv : d ∣ c*n
    · obtain ⟨k,rfl⟩ := hcd.dvd_of_dvd_mul_left hv
      exact ⟨k,rfl⟩
    · simp [Function.mem_support, mode, hv] at hn
  rw [← hinj.tsum_eq support, ← tsum_mul_left]
  apply tsum_congr
  intro k
  have hdR : IsUnit (d : ZMod R) := (ZMod.unitOfCoprime d hR).isUnit
  rw [show c*(d*k) = d*(c*k) by ring]
  simp only [mode, if_pos (dvd_mul_right d (c*k)), Nat.mul_div_cancel_left _ hd,
    Nat.cast_mul, map_mul, MulChar.one_apply hdR, one_mul, mul_pow, div_eq_mul_inv, mul_inv]
  ring

/-- A rough fibre mean with both the observed and the unrevealed divisor parts.
The common normalizing mass can be divided out to obtain the conditional mean. -/
theorem rough_mode_split {m : ℕ} (R a d z s : ℕ) (ha : 0 < a) (hd : 0 < d)
    (hsmooth : ∃ e : ℕ, a ∣ R^e) (hdz : d.Coprime z) (hdR : d.Coprime R)
    (χ : DirichletCharacter ℂ m) :
    (∑' n : ℕ, (1 : DirichletCharacter ℂ R) n * mode (a*d) χ (z*n) / (n : ℂ)^s) =
      (mode a χ z / (d : ℂ)^s) *
        ∑' n : ℕ, (1 : DirichletCharacter ℂ R) n * χ (n : ZMod m) / (n : ℂ)^s := by
  by_cases haz : a ∣ z
  · obtain ⟨c,rfl⟩ := haz
    have hc := Nat.coprime_mul_iff_right.mp hdz
    have hmode (n : ℕ) : mode (a*d) χ (a*c*n) = mode d χ (c*n) := by
      simp [mode, Nat.mul_assoc, Nat.mul_dvd_mul_iff_left ha, Nat.mul_div_mul_left _ _ ha]
    calc
      _ = ∑' n : ℕ, (1 : DirichletCharacter ℂ R) n * mode d χ (c*n) / (n : ℂ)^s := by
        apply tsum_congr
        intro n
        rw [hmode n]
      _ = _ := by
        rw [rough_scaled_mode R d c s hd hc.2 hdR χ]
        simp only [mode, if_pos (dvd_mul_right a c), Nat.mul_div_cancel_left _ ha]
  · have hz (n : ℕ) : (1 : DirichletCharacter ℂ R) n * mode (a*d) χ (z*n) = 0 := by
      by_cases hn : n.Coprime R
      · obtain ⟨e,he⟩ := hsmooth
        have hcop : a.Coprime n := (hn.symm.pow_left e).coprime_dvd_left he
        have hnd : ¬ a*d ∣ z*n := fun H => haz
          (hcop.dvd_of_dvd_mul_right ((dvd_mul_right a d).trans H))
        simp [mode, hnd]
      · have hu : ¬ IsUnit (n : ZMod R) := fun H => hn ((ZMod.isUnit_iff_coprime n R).mp H)
        simp [MulChar.map_nonunit _ hu]
    calc
      _ = ∑' n : ℕ, (0 : ℂ) / (n : ℂ)^s :=
        tsum_congr fun n => congrArg (fun t : ℂ => t / (n : ℂ)^s) (hz n)
      _ = _ := by simp [mode, haz]

end RiemannResearch.CategoryTheory.DivisibilityCharacterGram
