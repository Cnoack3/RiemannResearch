import RiemannResearch.CategoryTheory.SmoothCharacterMean
import RiemannResearch.CategoryTheory.ParetoPacketCharacters
import RiemannResearch.RH.QRamanujanPackets

/-! # Exact ambient variance of the period-ten packet

The quartic character modulo five is normalized at two to i. Its
real-minus-imaginary component realizes the fluctuating term of the CRT packet
after observing the prime valuations at two and five.
-/

noncomputable section
open RiemannResearch.RH.ZetaTwoHilbert RiemannResearch.RH.ZetaTwoParitySignal
open RiemannResearch.RH.QRamanujanPackets RiemannResearch.RH.Pareto
open RiemannResearch.CategoryTheory.PrimeValuationCovariance
open RiemannResearch.CategoryTheory.ObservedModeFibre
open RiemannResearch.CategoryTheory.ParetoPacketCharacters
open RiemannResearch.CategoryTheory.DivisibilityCharacterGram
open RiemannResearch.CategoryTheory.ValuationCharacterGram
open scoped BigOperators
namespace RiemannResearch.CategoryTheory.TenPacketValuationCovariance

def beta (n : ℕ) : ℂ := if n%5=1 then 1 else if n%5=2 then Complex.I
  else if n%5=3 then -Complex.I else if n%5=4 then -1 else 0

theorem beta_mul (a b : ℕ) : beta (a*b) = beta a * beta b := by
  have ha := Nat.mod_lt a (by decide : 0<5)
  have hb := Nat.mod_lt b (by decide : 0<5)
  interval_cases ea : a%5 <;> interval_cases eb : b%5 <;>
    norm_num [beta, Nat.mul_mod, ea, eb, Complex.I_mul_I]

/-- The Dirichlet character with beta(2) = i. -/
def betaCharacter : DirichletCharacter ℂ 5 where
  toFun a := beta a.val
  map_one' := by change beta 1 = 1; norm_num [beta]
  map_mul' a b := by
    rw [← beta_mul, ZMod.val_mul]
    simp [beta]
  map_nonunit' a ha := by
    let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
    have hz : a = 0 := not_ne_iff.mp (fun hn => ha (isUnit_iff_ne_zero.mpr hn))
    simp [hz,beta]

@[simp] theorem betaCharacter_nat (n : ℕ) : betaCharacter (n : ZMod 5) = beta n := by
  change beta (n : ZMod 5).val = _
  simp [beta, ZMod.val_natCast]

def parity (n : ℕ) : ℝ := if 2 ∣ n then 1 else -1

def signal (n : ℕ) : ℝ := (5/2 : ℝ)*parity n*((beta n).re-(beta n).im)

def tailQuartic (R : ℕ) : ℂ :=
  (∑' n : ℕ, (1 : DirichletCharacter ℂ R) n * betaCharacter (n : ZMod 5)/(n : ℂ)^2) / roughMass R

theorem tailQuartic_euler (b : ℕ) :
    tailQuartic (primorial b) =
      ∏' p : Nat.Primes, if p.val ≤ b then 1 else (1-1/(p : ℂ)^2)/(1-beta p/(p : ℂ)^2) := by
  simpa only [tailQuartic, betaCharacter_nat] using (primorial_roughRatio_tprod b betaCharacter).symm

theorem exists_signal : ∃ x : QHilbert, qSequence x = signal := by
  have hbound (n : ℕ) : |signal n| ≤ 3 := by
    unfold signal parity beta
    split_ifs <;> norm_num
  have hsum := boundedQ_square_summable signal 3 (by norm_num) hbound
  exact ⟨encodeQ signal hsum, qSequence_encodeQ _ _ (by norm_num [signal,beta])⟩

private theorem dvds {b : ℕ} {i j : ℕ+} (h : sameFibre b i j) (p : ℕ)
    (hp : p.Prime) (hb : p ≤ b) : p ∣ (i:ℕ) ↔ p ∣ (j:ℕ) := by
  rw [hp.dvd_iff_one_le_factorization i.pos.ne', hp.dvd_iff_one_le_factorization j.pos.ne']
  exact Iff.of_eq (congrArg (fun k : ℕ => 1 ≤ k) (h p hp hb))

private theorem packet_center (n : ℕ) :
    ramanujanPacket 10 n - signal n =
      (if 2 ∣ n then 0 else 4) + (5/2 : ℝ)*parity n*(if 5 ∣ n then 0 else 1) := by
  rw [ten_site_characters]
  have hn := Nat.mod_lt n (by decide : 0<5)
  rcases Nat.mod_two_eq_zero_or_one n with h2|h2 <;> interval_cases h5 : n%5 <;>
    norm_num [signal,parity,beta,Nat.dvd_iff_mod_eq_zero,h2,h5]

theorem ten_center_observed {b : ℕ} (hb : 5 ≤ b) {x : QHilbert} (hx : qSequence x = signal) :
    qRamanujanPacket 10 - x ∈ observed b := by
  apply (mem_observed _ _).2
  intro i j hij
  change qSequenceLinear (qRamanujanPacket 10 - x) i = qSequenceLinear (qRamanujanPacket 10 - x) j
  rw [map_sub]
  change qSequence (qRamanujanPacket 10) i - qSequence x i =
    qSequence (qRamanujanPacket 10) j - qSequence x j
  rw [hx,qSequence_qRamanujanPacket,packet_center,packet_center]
  simp only [parity,dvds hij 2 Nat.prime_two (by omega),dvds hij 5 (by decide) hb]

theorem ten_signal_fibre_fit {R b : ℕ} (hR : Covers R b) (hb : 5 ≤ b) (s : ℕ+)
    (hs : ∀ p ∈ (s:ℕ).primeFactors, p ≤ b) (x : QHilbert) (hx : qSequence x = signal) :
    qSequence ((observed b).starProjection x) s =
      (5/2 : ℝ)*parity s*((beta s*tailQuartic R).re-(beta s*tailQuartic R).im) := by
  let L : ℂ →L[ℝ] ℝ := Complex.reCLM - Complex.imCLM
  obtain ⟨y,hy⟩ := exists_mode_component 1 betaCharacter L
  have hy' (n : ℕ) (hn : 0<n) : qSequence y n = (beta n).re - (beta n).im := by
    simpa [L,mode] using hy n hn
  have he := observed_mode_component hR s hs 1 (by decide) betaCharacter L y hy
  have hyfit : qSequence ((observed b).starProjection y) s =
      (beta s*tailQuartic R).re - (beta s*tailQuartic R).im := by
    simpa [L,tailQuartic] using he
  rw [← hyfit, observed_rough_ratio hR s hs x, observed_rough_ratio hR s hs y, hx]
  rw [← mul_div_assoc, ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro m
  by_cases hm : m.Coprime R
  · have h2R := (hR 2 Nat.prime_two).2 (by omega)
    have h2m : ¬2 ∣ m := fun hd => (Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨2,Nat.prime_two,hd,h2R⟩) hm
    have hp : 2 ∣ (s:ℕ)*m ↔ 2 ∣ (s:ℕ) := by simp [Nat.prime_two.dvd_mul,h2m]
    by_cases hm0 : m=0
    · simp [hm0]
    · simp only [if_pos hm,signal,parity,hp,hy' _ (Nat.mul_pos s.pos (Nat.pos_of_ne_zero hm0))]
      ring
  · simp [hm]

def squareMeanAt (b n : ℕ) : ℝ :=
  if hn : 0<n then ((beta (smoothSite b ⟨n,hn⟩))^2).re else 0

/-- Complete Q expectation of the quadratic character on the revealed part. -/
def headQuadratic (b : ℕ) : ℝ := ∑' n : ℕ, positiveQWeight n * squareMeanAt b n

private def unitFive (n : ℕ) : ℝ := if 5 ∣ n then 0 else 1

private theorem component_sq (n : ℕ) (z : ℂ) :
    ((5/2 : ℝ)*parity n*((beta n*z).re-(beta n*z).im))^2 =
      (25/4 : ℝ)*(unitFive n * Complex.normSq z - ((beta n)^2).re*(z^2).im) := by
  have hn := Nat.mod_lt n (by decide : 0<5)
  by_cases h2 : 2 ∣ n <;> interval_cases h5 : n%5 <;>
    norm_num [parity,h2,beta,unitFive,Nat.dvd_iff_mod_eq_zero,h5,Complex.normSq_apply,
      pow_two,Complex.mul_re,Complex.mul_im] <;> ring

private theorem unitFive_summable : Summable (fun n : ℕ => positiveQWeight n * unitFive n) := by
  apply Summable.of_nonneg_of_le _ _ positiveQWeight_summable
  · intro n
    unfold unitFive
    split_ifs <;> simp [positiveQWeight_nonneg]
  · intro n
    unfold unitFive
    split_ifs <;> simp [positiveQWeight_nonneg]

private theorem unitFive_mass : (∑' n : ℕ, positiveQWeight n * unitFive n) = 24/25 := by
  let d := fun n : ℕ => if 5 ∣ n then positiveQWeight n else 0
  have hd : Summable d := by
    apply Summable.of_nonneg_of_le _ _ positiveQWeight_summable <;> intro n <;>
      dsimp [d] <;> split_ifs <;> simp [positiveQWeight_nonneg]
  have he (n : ℕ) : positiveQWeight n * unitFive n = positiveQWeight n - d n := by
    by_cases h : 5 ∣ n <;> simp [unitFive,d,h]
  simp_rw [he]
  rw [positiveQWeight_summable.tsum_sub hd, positiveQWeight_tsum]
  change 1 - (∑' n : ℕ, if 5 ∣ n then positiveQWeight n else 0) = 24/25
  rw [positiveQWeight_dvd_tsum 5 (by decide)]
  norm_num

private theorem squareMeanAt_summable (b : ℕ) :
    Summable (fun n : ℕ => positiveQWeight n * squareMeanAt b n) := by
  have hbound (n : ℕ) : |squareMeanAt b n| ≤ 1 := by
    unfold squareMeanAt
    split_ifs with hn
    · unfold beta
      split_ifs <;> norm_num [pow_two]
    · norm_num
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ positiveQWeight_summable
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (positiveQWeight_nonneg n)]
  exact (mul_le_mul_of_nonneg_left (hbound n) (positiveQWeight_nonneg n)).trans_eq (mul_one _)

private theorem signal_norm (x : QHilbert) (hx : qSequence x = signal) : ‖x‖^2 = 6 := by
  have h (n : ℕ) : signal n ^ 2 = (25/4 : ℝ)*unitFive n := by
    simpa [signal] using component_sq n 1
  rw [qNorm_weighted_sq, hx]
  have he (n : ℕ) : positiveQWeight n * signal n ^ 2 =
      (25/4 : ℝ)*(positiveQWeight n*unitFive n) := by rw [h]; ring
  simp_rw [he]
  rw [tsum_mul_left,unitFive_mass]
  norm_num

private theorem projected_site_sq {b : ℕ} (hb : 5 ≤ b) (x : QHilbert) (hx : qSequence x = signal)
    (n : ℕ) :
    (qSequence ((observed b).starProjection x) n)^2 = (25/4 : ℝ)*
      (unitFive n * Complex.normSq (tailQuartic (primorial b)) -
       squareMeanAt b n * ((tailQuartic (primorial b))^2).im) := by
  by_cases hn : 0<n
  · let j : ℕ+ := ⟨n,hn⟩
    have h := smoothSite_fibre b j
    have ho := (mem_observed _ _).1 ((observed b).starProjection_apply_mem x) (smoothSite b j) j h.2
    change (qSequence ((observed b).starProjection x) j)^2 = _
    rw [← ho, ten_signal_fibre_fit (primorial_covers b) hb _ h.1 x hx, component_sq]
    have hu : unitFive (smoothSite b j) = unitFive n := by
      unfold unitFive
      exact if_congr (dvds h.2 5 (by decide) hb) rfl rfl
    rw [hu, squareMeanAt, dif_pos hn]
  · have he : n=0 := by omega
    subst n
    simp [qSequence_zero,unitFive,squareMeanAt]

/-- The complete omitted covariance of the physical period-ten packet. The
second term retains the imaginary part of the square of the quartic tail. -/
theorem ten_covariance {b : ℕ} (hb : 5 ≤ b) :
    covariance b (qRamanujanPacket 10) (qRamanujanPacket 10) =
      6*(1-Complex.normSq (tailQuartic (primorial b))) +
        (25/4 : ℝ)*headQuadratic b*((tailQuartic (primorial b))^2).im := by
  obtain ⟨x,hx⟩ := exists_signal
  have hfix := (observed b).starProjection_eq_self_iff.mpr (ten_center_observed hb hx)
  rw [map_sub] at hfix
  have herr : qRamanujanPacket 10 - (observed b).starProjection (qRamanujanPacket 10) =
      x - (observed b).starProjection x := by
    calc
      _ = (qRamanujanPacket 10 - x) - (observed b).starProjection (qRamanujanPacket 10) + x := by abel
      _ = _ := by rw [← hfix]; abel
  have hsame : covariance b (qRamanujanPacket 10) (qRamanujanPacket 10) = covariance b x x := by
    unfold covariance; rw [herr]
  let t := tailQuartic (primorial b)
  have hproj : ‖(observed b).starProjection x‖^2 =
      (25/4 : ℝ)*((24/25 : ℝ)*Complex.normSq t-headQuadratic b*(t^2).im) := by
    rw [qNorm_weighted_sq]
    have ht (n : ℕ) : positiveQWeight n * (qSequence ((observed b).starProjection x) n)^2 =
        (25/4 : ℝ)*((positiveQWeight n*unitFive n)*Complex.normSq t -
                     (positiveQWeight n*squareMeanAt b n)*(t^2).im) := by
      rw [projected_site_sq hb x hx]; dsimp [t]; ring
    simp_rw [ht]
    rw [tsum_mul_left, (unitFive_summable.mul_right (Complex.normSq t)).tsum_sub
      ((squareMeanAt_summable b).mul_right (t^2).im), tsum_mul_right, tsum_mul_right,unitFive_mass]
    rfl
  have hs := gram_split b x x
  simp only [real_inner_self_eq_norm_sq, signal_norm x hx, hproj] at hs
  rw [hsame]
  change _ = 6*(1-Complex.normSq t)+(25/4 : ℝ)*headQuadratic b*(t^2).im
  linear_combination -hs

open RiemannResearch.CategoryTheory.SmoothCharacterMean

theorem headQuadratic_eq_re_headMean (b : ℕ) :
    headQuadratic b = (headMean b (betaCharacter^2)).re := by
  have hsite (n : ℕ) : squareMeanAt b n =
      ((betaCharacter^2 : DirichletCharacter ℂ 5) (smoothNat b n : ZMod 5)).re := by
    rcases n with _|n
    · have hzero : betaCharacter (0 : ZMod 5) = 0 := by change beta 0 = 0; norm_num [beta]
      simp [squareMeanAt,smoothNat,pow_two,MulChar.mul_apply,hzero]
    · simp [squareMeanAt,smoothNat,pow_two,MulChar.mul_apply]
  rw [headQuadratic]
  simp_rw [hsite]
  simpa only [headMean,mul_one,Complex.reCLM_apply] using
    weighted_component (betaCharacter^2) (smoothNat b) 1 Complex.reCLM

/-- The complete J10 diagonal in finite head and convergent tail
Euler products, for every cutoff that observes two and five. -/
theorem ten_covariance_euler {b : ℕ} (hb : 5 ≤ b) :
    covariance b (qRamanujanPacket 10) (qRamanujanPacket 10) =
      6*(1-Complex.normSq (tailCharacterProduct b betaCharacter)) +
        (25/4 : ℝ)*(∏ p ∈ revealedPrimeSet b, primeCharacterFactor (betaCharacter^2) p).re *
          ((tailCharacterProduct b betaCharacter)^2).im := by
  have ht : tailQuartic (primorial b) = tailCharacterProduct b betaCharacter := by
    simpa only [tailCharacterProduct,primeCharacterFactor,betaCharacter_nat] using tailQuartic_euler b
  rw [ten_covariance hb, ht, headQuadratic_eq_re_headMean, headMean_eq_finite_product]

end RiemannResearch.CategoryTheory.TenPacketValuationCovariance
