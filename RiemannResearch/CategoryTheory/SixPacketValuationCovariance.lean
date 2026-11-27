import RiemannResearch.CategoryTheory.ObservedModeFibre
import RiemannResearch.CategoryTheory.ParetoPacketCharacters
import RiemannResearch.RH.QRamanujanPackets

/-! # Exact ambient variance of the period-six packet
The orthogonal projection is the physical Q valuation-fibre average. This
calculation includes every rough cofactor and every smooth part. The
coefficient two comes from the Q mass of the integers prime to three.
-/
noncomputable section
open RiemannResearch.RH.ZetaTwoHilbert RiemannResearch.RH.ZetaTwoParitySignal
open RiemannResearch.RH.QRamanujanPackets RiemannResearch.RH.Pareto
open RiemannResearch.CategoryTheory.PrimeValuationCovariance
open RiemannResearch.CategoryTheory.ObservedModeFibre
open RiemannResearch.CategoryTheory.ParetoPacketCharacters
open scoped BigOperators

namespace RiemannResearch.CategoryTheory.SixPacketValuationCovariance

/-- The odd quadratic character modulo three, extended by zero. -/
def alpha (n : ℕ) : ℝ := if n%3=1 then 1 else if n%3=2 then -1 else 0

def parity (n : ℕ) : ℝ := if 2 ∣ n then 1 else -1
def signal (n : ℕ) : ℝ := (3/2 : ℝ)*parity n*alpha n

/-- Complete expectation of the sign character over integers prime to R. -/
def tailSign (R : ℕ) : ℝ :=
  (∑' n : ℕ, if n.Coprime R then alpha n / (n : ℝ)^2 else 0) /
    (∑' n : ℕ, if n.Coprime R then 1 / (n : ℝ)^2 else 0)

theorem alpha_mul (a b : ℕ) : alpha (a*b) = alpha a * alpha b := by
  have ha := Nat.mod_lt a (by decide : 0 < 3)
  have hb := Nat.mod_lt b (by decide : 0 < 3)
  interval_cases ea : a%3 <;> interval_cases eb : b%3 <;>
    norm_num [alpha,Nat.mul_mod,ea,eb]

private theorem signal_sq (n : ℕ) : signal n ^ 2 = if 3 ∣ n then 0 else 9/4 := by
  have hn := Nat.mod_lt n (by decide : 0 < 3)
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> interval_cases e : n%3 <;>
    norm_num [signal,alpha,parity,Nat.dvd_iff_mod_eq_zero,h,e]

theorem exists_signal : ∃ x : QHilbert, qSequence x = signal := by
  have hbound (n : ℕ) : |signal n| ≤ 2 := by
    unfold signal parity alpha
    split_ifs <;> norm_num
  have hsum := boundedQ_square_summable signal 2 (by norm_num) hbound
  exact ⟨encodeQ signal hsum, qSequence_encodeQ _ _ (by norm_num [signal, alpha])⟩

theorem dvds {b : ℕ} {s n : ℕ+} (hsn : sameFibre b s n) (p : ℕ) (hp : p.Prime)
    (hb : p ≤ b) : p ∣ (s : ℕ) ↔ p ∣ (n : ℕ) := by
  rw [hp.dvd_iff_one_le_factorization s.pos.ne', hp.dvd_iff_one_le_factorization n.pos.ne']
  exact Iff.of_eq (congrArg (fun k : ℕ => 1 ≤ k) (hsn p hp hb))

theorem smoothRepresentative (b : ℕ) (n : ℕ+) :
    ∃ s : ℕ+, (∀ p ∈ (s : ℕ).primeFactors, p ≤ b) ∧ sameFibre b s n := by
  have H (m : ℕ) : ∀ h : 0 < m, ∃ s : ℕ+, (∀ p ∈ (s : ℕ).primeFactors, p ≤ b) ∧
      sameFibre b s ⟨m,h⟩ := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      by_cases hsm : ∀ p ∈ m.primeFactors, p ≤ b
      · exact ⟨⟨m,hm⟩,hsm,fun _ _ _ => rfl⟩
      · push Not at hsm
        obtain ⟨p,hpm,hbp⟩ := hsm
        obtain ⟨hp,hd,_⟩ := Nat.mem_primeFactors.mp hpm
        obtain ⟨k,hk⟩ := hd
        have hkpos : 0 < k := Nat.pos_of_ne_zero (fun hk0 => hm.ne' (by simp [hk,hk0]))
        have hlt : k < m := by rw [hk]; nlinarith [hp.two_le]
        obtain ⟨s,hs,he⟩ := ih k hlt hkpos
        refine ⟨s,hs,fun r hr hrb => ?_⟩
        change (s : ℕ).factorization r = m.factorization r
        rw [hk, Nat.factorization_mul hp.ne_zero hkpos.ne', Finsupp.add_apply,
          hp.factorization, Finsupp.single_eq_of_ne (show r ≠ p by omega), zero_add]
        exact he r hr hrb
  exact H n n.pos

private theorem packet_center (n : ℕ) :
    ramanujanPacket 6 n - signal n =
      (if 2 ∣ n then 0 else 2) + (3/2 : ℝ)*parity n*(if 3 ∣ n then 0 else 1) := by
  rw [six_site_characters]
  have hn : n%2 = 0 ∨ n%2 = 1 := Nat.mod_two_eq_zero_or_one _
  have ht := Nat.mod_lt n (by decide : 0 < 3)
  rcases hn with hn | hn <;> interval_cases e : n%3 <;>
    norm_num [signal,parity,alpha,Nat.dvd_iff_mod_eq_zero,hn,e]

theorem six_center_observed {b : ℕ} (hb : 3 ≤ b) {x : QHilbert}
    (hx : qSequence x = signal) :
    qRamanujanPacket 6 - x ∈ observed b := by
  apply (mem_observed _ _).2
  intro i j hij
  change qSequenceLinear (qRamanujanPacket 6 - x) i = qSequenceLinear (qRamanujanPacket 6 - x) j
  rw [map_sub]
  change qSequence (qRamanujanPacket 6) i - qSequence x i =
    qSequence (qRamanujanPacket 6) j - qSequence x j
  rw [hx,qSequence_qRamanujanPacket,packet_center,packet_center]
  simp only [parity, dvds hij 2 Nat.prime_two (by omega), dvds hij 3 Nat.prime_three hb]

theorem signal_fibre_fit {R b : ℕ} (hR : Covers R b) (hb : 3 ≤ b) (s : ℕ+)
    (hs : ∀ p ∈ (s : ℕ).primeFactors, p ≤ b) (x : QHilbert) (hx : qSequence x = signal) :
    qSequence ((observed b).starProjection x) s = signal s * tailSign R := by
  rw [observed_rough_ratio hR s hs, hx, tailSign, ← mul_div_assoc, ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro m
  by_cases h : m.Coprime R
  · have h2R := (hR 2 Nat.prime_two).2 (by omega)
    have h2m : ¬2 ∣ m := fun hd => (Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨2,Nat.prime_two,hd,h2R⟩) h
    have he : 2 ∣ (s:ℕ)*m ↔ 2 ∣ (s:ℕ) := by simp [Nat.prime_two.dvd_mul, h2m]
    simp only [if_pos h, signal, parity, he, alpha_mul]
    ring
  · simp [h]

private theorem signal_projected_sq {R b : ℕ} (hR : Covers R b) (hb : 3 ≤ b)
    (x : QHilbert) (hx : qSequence x = signal) (n : ℕ) :
    (qSequence ((observed b).starProjection x) n)^2 = (signal n)^2 * tailSign R ^ 2 := by
  rcases n with _ | n
  · simp [signal,alpha]
  let i : ℕ+ := ⟨n+1, Nat.succ_pos _⟩
  obtain ⟨s,hs,hsi⟩ := smoothRepresentative b i
  have ho := (mem_observed _ _).1 ((observed b).starProjection_apply_mem x) s i hsi
  change (qSequence ((observed b).starProjection x) i)^2 = (signal i)^2 * _
  rw [← ho, signal_fibre_fit hR hb s hs x hx, mul_pow, signal_sq, signal_sq]
  simp only [dvds hsi 3 Nat.prime_three hb]

private theorem signal_energy (x : QHilbert) (hx : qSequence x = signal) : ‖x‖^2 = 2 := by
  let d := fun n : ℕ => if 3 ∣ n then positiveQWeight n else 0
  have hd : Summable d :=
    Summable.of_nonneg_of_le (fun n => by dsimp [d]; split_ifs <;> simp [positiveQWeight_nonneg])
      (fun n => by dsimp [d]; split_ifs <;> simp [positiveQWeight_nonneg]) positiveQWeight_summable
  have he (n : ℕ) : positiveQWeight n * (signal n)^2 = (9/4 : ℝ)*(positiveQWeight n-d n) := by
    by_cases h : 3 ∣ n <;> simp [signal_sq,h,d]
    ring
  rw [qNorm_weighted_sq, hx]
  simp_rw [he]
  rw [tsum_mul_left, positiveQWeight_summable.tsum_sub hd, positiveQWeight_tsum]
  change (9/4 : ℝ)*(1 - ∑' n : ℕ, if 3 ∣ n then positiveQWeight n else 0) = 2
  rw [positiveQWeight_dvd_tsum 3 (by decide)]
  norm_num

/-- Complete omitted ambient energy of the physical period-six packet after
revealing all valuations at primes through b. -/
theorem six_covariance {b : ℕ} (hb : 3 ≤ b) :
    covariance b (qRamanujanPacket 6) (qRamanujanPacket 6) =
      2 * (1 - tailSign (primorial b)^2) := by
  obtain ⟨x,hx⟩ := exists_signal
  have hfix := (observed b).starProjection_eq_self_iff.mpr (six_center_observed hb hx)
  rw [map_sub] at hfix
  have herr : qRamanujanPacket 6 - (observed b).starProjection (qRamanujanPacket 6) =
      x - (observed b).starProjection x := by
    rw [sub_eq_sub_iff_add_eq_add] at hfix ⊢
    abel_nf at hfix ⊢
    exact hfix.symm
  have hsame : covariance b (qRamanujanPacket 6) (qRamanujanPacket 6) = covariance b x x := by
    unfold covariance; rw [herr]
  have hproj : ‖(observed b).starProjection x‖^2 = ‖x‖^2 * tailSign (primorial b)^2 := by
    rw [qNorm_weighted_sq, qNorm_weighted_sq, hx, ← tsum_mul_right]
    apply tsum_congr
    intro n
    rw [signal_projected_sq (primorial_covers b) hb x hx n, mul_assoc]
  have h := gram_split b x x
  simp only [real_inner_self_eq_norm_sq, hproj, signal_energy x hx] at h
  rw [hsame]
  linarith


private def quadraticThree : MulChar (ZMod 3) ℤ where
  toFun a := match a with | 0 => 0 | 1 => 1 | 2 => -1
  map_one' := rfl
  map_mul' := by decide
  map_nonunit' := by decide

def chiThree : DirichletCharacter ℂ 3 :=
  quadraticThree.ringHomComp (Int.castRingHom ℂ)

theorem chiThree_nat (n : ℕ) : chiThree n = (alpha n : ℂ) := by
  rw [← ZMod.natCast_mod n 3]
  have hn := Nat.mod_lt n (by decide : 0 < 3)
  have h2 : quadraticThree 2 = -1 := rfl
  interval_cases h : n%3 <;> norm_num [h,alpha,chiThree,MulChar.ringHomComp_apply,h2] <;> rfl

private theorem inflated_char {R : ℕ} (hR : 3 ∣ R) (n : ℕ) :
    (DirichletCharacter.changeLevel hR chiThree) n =
      if n.Coprime R then (alpha n : ℂ) else 0 := by
  by_cases hn : n.Coprime R
  · rw [if_pos hn, ← chiThree_nat]
    simpa only [ZMod.coe_unitOfCoprime,ZMod.cast_natCast hR] using
      DirichletCharacter.changeLevel_eq_cast_of_dvd chiThree hR (ZMod.unitOfCoprime n hn)
  · rw [if_neg hn]
    exact MulChar.map_nonunit _ (fun hu => hn ((ZMod.isUnit_iff_coprime _ _).1 hu))

/-- The rough inverse-square expectation in the physical covariance equals
the product of the omitted prime Euler factors, with unit factors retained. -/
theorem tailSign_hasProd {b : ℕ} (hb : 3 ≤ b) :
    HasProd (fun p : Nat.Primes => if p.val ≤ b then (1 : ℂ) else
      (1 - 1/(p.val : ℂ)^2)/(1 - (alpha p.val : ℂ)/(p.val : ℂ)^2))
      (tailSign (primorial b) : ℂ) := by
  let R := primorial b
  have hc := primorial_covers b
  have h3 : 3 ∣ R := (hc 3 Nat.prime_three).2 hb
  let χ := DirichletCharacter.changeLevel h3 chiThree
  have h := ValuationCharacterGram.cutoff_hasProd χ (fun p => hc p p.property)
  have hr : ValuationCharacterGram.roughMoment χ = (tailSign R : ℂ) := by
    rw [ValuationCharacterGram.roughMoment, ValuationCharacterGram.roughMass, tailSign,
      Complex.ofReal_div, Complex.ofReal_tsum, Complex.ofReal_tsum]
    congr 1
    · apply tsum_congr
      intro n
      rw [show χ n = _ from inflated_char h3 n]
      split_ifs <;> push_cast <;> simp
    · apply tsum_congr
      intro n
      by_cases hn : n.Coprime R
      · rw [if_pos hn, MulChar.one_apply ((ZMod.isUnit_iff_coprime n R).2 hn)]
        push_cast
        rfl
      · rw [if_neg hn, MulChar.map_nonunit _ (fun hu => hn ((ZMod.isUnit_iff_coprime n R).1 hu))]
        simp
  rw [hr] at h
  convert h using 1
  funext p
  by_cases hp : p.val ≤ b
  · simp [hp]
  · have hu : p.val.Coprime R := p.property.coprime_iff_not_dvd.2 (fun hd => hp ((hc _ p.property).1 hd))
    have hz : χ (p.val : ZMod R) = (alpha p.val : ℂ) :=
      (inflated_char h3 p.val).trans (if_pos hu)
    simp only [if_neg hp, hz]

end RiemannResearch.CategoryTheory.SixPacketValuationCovariance
