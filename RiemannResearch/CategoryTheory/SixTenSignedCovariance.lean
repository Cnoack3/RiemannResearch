import RiemannResearch.CategoryTheory.SixPacketValuationCovariance
import RiemannResearch.CategoryTheory.TenPacketValuationCovariance
import RiemannResearch.CategoryTheory.SmoothCharacterMean

/-! # The signed physical covariance of the period-six and period-ten packets

The same observed parity sign multiplies both centered signals and cancels
pointwise. The complete projected Gram uses the joint smooth-character moment.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.CategoryTheory.SixTenSignedCovariance
open RiemannResearch.RH.ZetaTwoHilbert RiemannResearch.RH.QRamanujanPackets
open RiemannResearch.CategoryTheory.PrimeValuationCovariance
open RiemannResearch.CategoryTheory.ObservedModeFibre
open RiemannResearch.CategoryTheory.SmoothCharacterMean
open RiemannResearch.CategoryTheory.ValuationCharacterGram

/-- Natural-site evaluation of the product character includes all nonunit sites. -/
private theorem product_at_nat {a b : ℕ} (χ : DirichletCharacter ℂ a)
    (ψ : DirichletCharacter ℂ b) (n : ℕ) :
    χ.mul ψ (n : ZMod (a.lcm b)) = χ (n : ZMod a)*ψ (n : ZMod b) := by
  let l := a.lcm b
  by_cases h : n.Coprime l
  · let u := ZMod.unitOfCoprime n h
    have ha := DirichletCharacter.changeLevel_eq_cast_of_dvd χ (Nat.dvd_lcm_left a b) u
    have hb := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ (Nat.dvd_lcm_right a b) u
    simp only [u, ZMod.coe_unitOfCoprime, ZMod.cast_natCast (Nat.dvd_lcm_left a b)] at ha
    simp only [u, ZMod.coe_unitOfCoprime, ZMod.cast_natCast (Nat.dvd_lcm_right a b)] at hb
    simp only [DirichletCharacter.mul, MulChar.mul_apply, ha, hb]
  · have hz := MulChar.map_nonunit (χ.mul ψ)
      (fun hu => h ((ZMod.isUnit_iff_coprime n l).mp hu))
    rw [hz]
    by_cases hna : n.Coprime a
    · have hnb : ¬ n.Coprime b := fun hb =>
        h ((hna.mul_right hb).coprime_dvd_right (Nat.lcm_dvd_mul a b))
      rw [MulChar.map_nonunit ψ (fun hu => hnb ((ZMod.isUnit_iff_coprime n b).mp hu)), mul_zero]
    · rw [MulChar.map_nonunit χ (fun hu => hna ((ZMod.isUnit_iff_coprime n a).mp hu)), zero_mul]

def crossCharacter : DirichletCharacter ℂ 15 :=
  SixPacketValuationCovariance.chiThree.mul TenPacketValuationCovariance.betaCharacter

@[simp] theorem crossCharacter_nat (n : ℕ) : crossCharacter (n : ZMod 15) =
    (SixPacketValuationCovariance.alpha n : ℂ) * TenPacketValuationCovariance.beta n := by
  exact (product_at_nat _ _ _).trans (by
    rw [SixPacketValuationCovariance.chiThree_nat, TenPacketValuationCovariance.betaCharacter_nat])

private def test : ℂ →L[ℝ] ℝ := Complex.reCLM - Complex.imCLM

private theorem sign_contraction (n : ℕ) (z : ℂ) (r : ℝ) :
    (SixPacketValuationCovariance.signal n * r) *
      ((5/2 : ℝ)*TenPacketValuationCovariance.parity n *
        ((TenPacketValuationCovariance.beta n * z).re - (TenPacketValuationCovariance.beta n * z).im)) =
      (15/4 : ℝ) * test (crossCharacter (n : ZMod 15) * ((r : ℂ)*z)) := by
  rw [crossCharacter_nat]
  by_cases h : 2 ∣ n <;>
    simp [SixPacketValuationCovariance.signal, SixPacketValuationCovariance.parity,
      TenPacketValuationCovariance.parity, h, test, Complex.mul_re, Complex.mul_im] <;> ring

private theorem signal_product (n : ℕ) :
    SixPacketValuationCovariance.signal n * TenPacketValuationCovariance.signal n =
      (15/4 : ℝ)*test (crossCharacter (n : ZMod 15)) := by
  simpa [TenPacketValuationCovariance.signal] using sign_contraction n 1 1

private theorem observed_signal_product {b : ℕ} (hb : 5 ≤ b) {x y : QHilbert}
    (hx : qSequence x = SixPacketValuationCovariance.signal)
    (hy : qSequence y = TenPacketValuationCovariance.signal) (n : ℕ) :
    qSequence ((observed b).starProjection x) n * qSequence ((observed b).starProjection y) n =
      (15/4 : ℝ)*test (crossCharacter (smoothNat b n : ZMod 15) *
        ((SixPacketValuationCovariance.tailSign (primorial b) : ℂ) *
          TenPacketValuationCovariance.tailQuartic (primorial b))) := by
  rcases n with _ | n
  · have hz : crossCharacter (0 : ZMod 15) = 0 := by
      have hzero := crossCharacter_nat 0
      norm_num [SixPacketValuationCovariance.alpha] at hzero
      exact hzero
    simp [smoothNat,hz]
  let i : ℕ+ := ⟨n+1,Nat.succ_pos _⟩
  let s := smoothSite b i
  have hf := smoothSite_fibre b i
  have ho (v : QHilbert) := (mem_observed _ _).1 ((observed b).starProjection_apply_mem v) s i hf.2
  change qSequence ((observed b).starProjection x) i * qSequence ((observed b).starProjection y) i =
    (15/4 : ℝ) * test (crossCharacter ((s : ℕ) : ZMod 15) * _)
  rw [← ho x, ← ho y,
    SixPacketValuationCovariance.signal_fibre_fit (primorial_covers b) (by omega) s hf.1 x hx,
    TenPacketValuationCovariance.ten_signal_fibre_fit (primorial_covers b) hb s hf.1 y hy]
  exact sign_contraction _ _ _

private theorem covariance_replace {b : ℕ} {x y u v : QHilbert}
    (hx : x-u ∈ observed b) (hy : y-v ∈ observed b) :
    covariance b x y = covariance b u v := by
  have h (a c : QHilbert) (hh : a-c ∈ observed b) :
      a - (observed b).starProjection a = c - (observed b).starProjection c := by
    have he := (observed b).starProjection_eq_self_iff.mpr hh
    rw [map_sub] at he
    calc
      a - (observed b).starProjection a = (a-c) - ((observed b).starProjection a -
          (observed b).starProjection c) + (c - (observed b).starProjection c) := by abel
      _ = _ := by rw [he]; abel
  unfold covariance
  rw [h _ _ hx, h _ _ hy]

/-- Equation (7), with the head moment given by its expectation over the full
physical distribution. The two scalar tails are the full rough cofactor ratios. -/
theorem six_ten_covariance {b : ℕ} (hb : 5 ≤ b) :
    covariance b (qRamanujanPacket 6) (qRamanujanPacket 10) =
      (15/4 : ℝ) * (((1+Complex.I) * headMean b crossCharacter) *
        (tailMoment b crossCharacter - (SixPacketValuationCovariance.tailSign (primorial b) : ℂ) *
          TenPacketValuationCovariance.tailQuartic (primorial b))).re := by
  obtain ⟨x,hx⟩ := SixPacketValuationCovariance.exists_signal
  obtain ⟨y,hy⟩ := TenPacketValuationCovariance.exists_signal
  rw [covariance_replace (SixPacketValuationCovariance.six_center_observed (by omega) hx)
    (TenPacketValuationCovariance.ten_center_observed hb hy)]
  have he := gram_split b x y
  rw [qInner_weighted, qInner_weighted, hx, hy] at he
  let c := (SixPacketValuationCovariance.tailSign (primorial b) : ℂ) *
    TenPacketValuationCovariance.tailQuartic (primorial b)
  have hfull (n : ℕ) : positiveQWeight n * SixPacketValuationCovariance.signal n *
      TenPacketValuationCovariance.signal n =
      (15/4 : ℝ) * (positiveQWeight n * test (crossCharacter (n : ZMod 15))) := by
    rw [mul_assoc, signal_product]; ring
  have hproj (n : ℕ) : positiveQWeight n * qSequence ((observed b).starProjection x) n *
      qSequence ((observed b).starProjection y) n =
      (15/4 : ℝ)*(positiveQWeight n * test (crossCharacter (smoothNat b n : ZMod 15)*c)) := by
    rw [mul_assoc, observed_signal_product hb hx hy n]
    dsimp only [c]
    ring
  simp only [hfull, hproj, tsum_mul_left, full_component_mean b crossCharacter test,
    weighted_component crossCharacter (smoothNat b) c test] at he
  change (15/4 : ℝ)*test (headMean b crossCharacter * tailMoment b crossCharacter) =
    (15/4 : ℝ)*test (headMean b crossCharacter*c) + covariance b x y at he
  change covariance b x y = (15/4 : ℝ)*(((1+Complex.I)*headMean b crossCharacter)*
    (tailMoment b crossCharacter-c)).re
  simp only [test, sub_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im] at he ⊢
  linear_combination -he

/-- The signed mixed covariance with the head as a finite Euler product and all
three tails as products over every unrevealed prime. -/
theorem six_ten_covariance_euler {b : ℕ} (hb : 5 ≤ b) :
    covariance b (qRamanujanPacket 6) (qRamanujanPacket 10) =
      (15/4 : ℝ) * (((1 + Complex.I) *
        ∏ p ∈ revealedPrimeSet b, primeCharacterFactor crossCharacter p) *
        (tailCharacterProduct b crossCharacter -
          tailCharacterProduct b SixPacketValuationCovariance.chiThree *
            tailCharacterProduct b TenPacketValuationCovariance.betaCharacter)).re := by
  have ha : (SixPacketValuationCovariance.tailSign (primorial b) : ℂ) =
      tailCharacterProduct b SixPacketValuationCovariance.chiThree := by
    simpa only [tailCharacterProduct, primeCharacterFactor, SixPacketValuationCovariance.chiThree_nat]
      using (SixPacketValuationCovariance.tailSign_hasProd (show 3 ≤ b by omega)).tprod_eq.symm
  have hb' : TenPacketValuationCovariance.tailQuartic (primorial b) =
      tailCharacterProduct b TenPacketValuationCovariance.betaCharacter := by
    simpa only [tailCharacterProduct, primeCharacterFactor, TenPacketValuationCovariance.betaCharacter_nat]
      using TenPacketValuationCovariance.tailQuartic_euler b
  rw [six_ten_covariance hb, headMean_eq_finite_product, ha, hb']
  rfl

end RiemannResearch.CategoryTheory.SixTenSignedCovariance
