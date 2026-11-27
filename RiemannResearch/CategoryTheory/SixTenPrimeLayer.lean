import RiemannResearch.CategoryTheory.SixTenSignedCovariance

/-! # The signed layer of one newly revealed prime in the period-six and period-ten pair -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.CategoryTheory.SixTenSignedCovariance
open RiemannResearch.RH.QRamanujanPackets
open RiemannResearch.CategoryTheory.PrimeValuationCovariance
open RiemannResearch.CategoryTheory.ValuationCharacterGram

private theorem tail_split {a b : ℕ} (p : Nat.Primes) (ha : p ∉ revealedPrimeSet a)
    (hb : revealedPrimeSet b = insert p (revealedPrimeSet a)) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    tailCharacterProduct a χ = primeCharacterFactor χ p * tailCharacterProduct b χ := by
  classical
  let H := ∏ r ∈ revealedPrimeSet a, primeCharacterFactor χ r
  have hn : H ≠ 0 := by
    intro hz
    have he := fullProduct_eq_head_mul_tail a χ
    rw [show (∏ r ∈ revealedPrimeSet a, primeCharacterFactor χ r) = 0 from hz, zero_mul] at he
    exact tailCharacterProduct_ne_zero 0 χ he
  have he := (fullProduct_eq_head_mul_tail a χ).symm.trans (fullProduct_eq_head_mul_tail b χ)
  rw [hb, Finset.prod_insert ha] at he
  apply mul_left_cancel₀ hn
  exact he.trans (by ring)

/-- For an isolated prime revelation, the signed layer is its local character
covariance times the complete joint head and the two independent tail means. -/
theorem six_ten_prime_layer {a b : ℕ} (hab : a ≤ b) (h5 : 5 ≤ a) (p : Nat.Primes)
    (ha : p ∉ revealedPrimeSet a) (hb : revealedPrimeSet b = insert p (revealedPrimeSet a)) :
    covariance a (qRamanujanPacket 6) (qRamanujanPacket 10) -
        covariance b (qRamanujanPacket 6) (qRamanujanPacket 10) =
      (15/4 : ℝ) * (((1+Complex.I) * (∏ r ∈ revealedPrimeSet a, primeCharacterFactor crossCharacter r)) *
        (tailCharacterProduct b SixPacketValuationCovariance.chiThree *
          tailCharacterProduct b TenPacketValuationCovariance.betaCharacter) *
        (primeCharacterFactor crossCharacter p -
          primeCharacterFactor SixPacketValuationCovariance.chiThree p *
            primeCharacterFactor TenPacketValuationCovariance.betaCharacter p)).re := by
  rw [six_ten_covariance_euler h5, six_ten_covariance_euler (h5.trans hab),
    tail_split p ha hb crossCharacter, tail_split p ha hb SixPacketValuationCovariance.chiThree,
    tail_split p ha hb TenPacketValuationCovariance.betaCharacter, hb, Finset.prod_insert ha]
  rw [← mul_sub, ← Complex.sub_re]
  congr 2
  ring

private theorem factor_one {q : ℕ} (χ : DirichletCharacter ℂ q) (p : Nat.Primes) (h : χ p = 1) :
    primeCharacterFactor χ p = 1 := by
  rw [primeCharacterFactor, h]
  apply div_self
  have hp : 1 < (p.val : ℝ) := by exact_mod_cast p.property.one_lt
  have hlt : 1/(p.val : ℝ)^2 < 1 := (div_lt_one (by positivity)).2 (by nlinarith)
  have hn := Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (ne_of_gt hlt))
  push_cast at hn
  exact hn

private theorem factor_cancel (p : Nat.Primes) (hp : p.val%3=1 ∨ p.val%5=1) :
    primeCharacterFactor crossCharacter p =
      primeCharacterFactor SixPacketValuationCovariance.chiThree p *
        primeCharacterFactor TenPacketValuationCovariance.betaCharacter p := by
  rcases hp with hp|hp
  · have h : SixPacketValuationCovariance.chiThree p = 1 := by
      simp [SixPacketValuationCovariance.chiThree_nat, SixPacketValuationCovariance.alpha,hp]
    rw [factor_one _ _ h, one_mul]
    simp [primeCharacterFactor, crossCharacter_nat, SixPacketValuationCovariance.alpha,hp,
      TenPacketValuationCovariance.betaCharacter_nat]
  · have h : TenPacketValuationCovariance.betaCharacter p = 1 := by
      simp [TenPacketValuationCovariance.betaCharacter_nat,TenPacketValuationCovariance.beta,hp]
    rw [factor_one _ _ h, mul_one]
    simp [primeCharacterFactor, crossCharacter_nat,TenPacketValuationCovariance.beta,hp,
      SixPacketValuationCovariance.chiThree_nat]

/-- The physical signed layer vanishes at primes congruent to one modulo three
or five. The cutoff immediately before the prime gives its preceding layer. -/
theorem six_ten_prime_layer_zero (p : Nat.Primes) (hp : 5 < p.val)
    (hcong : p.val % 3 = 1 ∨ p.val % 5 = 1) :
    covariance (p.val-1) (qRamanujanPacket 6) (qRamanujanPacket 10) -
      covariance p.val (qRamanujanPacket 6) (qRamanujanPacket 10) = 0 := by
  have ha : p ∉ revealedPrimeSet (p.val-1) := by simp only [mem_revealedPrimeSet]; omega
  have hb : revealedPrimeSet p.val = insert p (revealedPrimeSet (p.val-1)) := by
    ext r
    simp only [mem_revealedPrimeSet, Finset.mem_insert]
    constructor
    · intro hr
      by_cases h : r.val = p.val
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (by omega)
    · rintro (rfl|hr)
      · exact le_rfl
      · omega
  rw [six_ten_prime_layer (by omega) (by omega) p ha hb, factor_cancel p hcong]
  simp

end RiemannResearch.CategoryTheory.SixTenSignedCovariance
