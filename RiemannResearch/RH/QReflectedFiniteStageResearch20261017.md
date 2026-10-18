# Quantitative legal approximants to squarefree reflected vectors

Date: 17 October 2026; verification recovered 18 October 2026.

Base inspected: [b7e8a604ad5ea71c958b45755f06332b6c4672bf](https://github.com/Cnoack3/RiemannResearch/commit/b7e8a604ad5ea71c958b45755f06332b6c4672bf).

Source: Christian Noack's requested investigation of the infinite squarefree CRT,
finite divisor stages, complete Q-Gram geometry, and legal lattice packets.
The arguments below are developed here from the cited repository identities;
no mathematical novelty claim is made.

## 1. Outcome and scope

There are explicit finite-stage legal upper bounds for the reflected targets.
There is also an unconditional obstruction to using only escaping conductors.
The raw primorial Möbius sieve, and its direct one-atom exact-head repair,
have diverging complete Q-error. None of these obstructions excludes the
full screened packet method, which retains and refits old conductors.

The existence of a legal sequence with reflected error tending to zero remains
Open. Finite improvement, ambient convergence, and the geometric equivalence
do not discharge this obligation. No singleton approximation is proposed.

Throughout,
\[
 Q(n)=\frac1{Z n^2},\quad Z=\zeta(2),\quad
 g_d(n)=\frac{n\bmod d}{d},\quad I_d(n)=\mathbf1_{d\mid n},\quad
 R_d=1-g_d-I_d .
\]
Physical coordinates are positive integers; the Lean realization anchors zero
at zero. Write
\[
 V_L=\operatorname{span}\{g_e:2\le e,\ e\mid L\},\qquad
 V_{\rm sq}=\overline{\operatorname{span}\{g_e:e\ge2,\ e\text{ squarefree}\}}^{\,Q}.
\]
For squarefree positive L, V_L is a finite legal stage.

## 2. Exact full-energy identities and explicit upper bounds

### 2.1 General shifted trial

For any Q-Hilbert vector F and positive d, retain the whole identity
\[
 \boxed{\ \|R_d-(F-g_d)\|_Q^2
 =\|1-F\|_Q^2+\frac1{d^2}
       -2\langle1-F,I_d\rangle_Q.\ }                 \tag{2.1}
\]
The complete mixed moment is
\[
 \langle F,I_d\rangle_Q
 =\frac1{d^2}\,\mathbb E_Q[F(dK)].
\]
This includes the entire d-progression and is not an independence assertion.

If F belongs to V_L and L divides d, then F vanishes on multiples of d:
\[
 \boxed{\ \|R_d-(F-g_d)\|_Q^2=\|1-F\|_Q^2-\frac1{d^2}.\ }       \tag{2.2}
\]
When L=d, the translated trial remains in V_d. With P_d the orthogonal
projection onto V_d and E_d=\|1-P_d1\|_Q^2, this gives
\[
 \boxed{\ \operatorname{dist}(R_d,V_d)^2=E_d-\frac1{d^2}.\ }      \tag{2.3}
\]
In particular E_d is at least d^(-2). Reflection subtracts only the exact
multiples-of-d energy; estimating E_d remains essential.

For an arbitrary squarefree d and legal F, the trial F-g_d is still legal,
even when their dictionaries differ. Equation (2.1) and Cauchy-Schwarz give
\[
 \operatorname{dist}(R_d,V_{\rm sq})
 \le \|1-F\|_Q+\frac1d.                                      \tag{2.4}
\]
Indeed, with \(\delta=\operatorname{dist}(1,V_{\rm sq})\),
translation by the legal g_d and the one-Lipschitz property of distance imply
\[
 \boxed{\ |\operatorname{dist}(R_d,V_{\rm sq})-\delta|\le\frac1d.\ } \tag{2.5}
\]
This sharpens the ambient-convergence reduction; it does not prove delta=0.

### 2.2 A two-atom trial valid for every squarefree d

Since \(2g_2=1-I_2\), put \(A_d=2g_2-g_d\). It is a literal legal combination.
The residual is exactly \(I_2-I_d\), so
\[
 \boxed{\ \|R_d-A_d\|_Q^2
  =\frac14+\frac1{d^2}-\frac{2}{\operatorname{lcm}(2,d)^2}.\ }    \tag{2.6}
\]
Consequently
\[
 \operatorname{dist}(R_d,V_{\rm sq})^2
 \le \begin{cases}
  \frac14-\frac1{d^2}, & 2\mid d,\\
  \frac14+\frac1{2d^2}, & 2\nmid d.
 \end{cases}
\]
The overlap term is retained exactly. This supplies a bound, not decay.

### 2.3 The complete finite Gram problem

Let d divide squarefree L, index every e>1 dividing L, and define
\[
 G_{ef}=\langle g_e,g_f\rangle_Q,\quad b_e=\langle1,g_e\rangle_Q,\quad
 v_e=\langle g_e,I_d\rangle_Q
     =d^{-2}\mathbb E_Q[g_e(dK)] .
\]
The atoms are independent, so G is positive definite. Set \(u=G^{-1}(b-v)\).
For \(F_c=\sum_e c_e g_e\), the exact completed square is
\[
 \boxed{\ \|R_d-(F_c-g_d)\|_Q^2
 =1-d^{-2}-(b-v)^TG^{-1}(b-v)+(c-u)^TG(c-u).\ }       \tag{2.7}
\]
When L=d, v=0 and (2.7) specializes to (2.3). For larger L, setting v=0
without proof would remove genuine correlations. With h=gcd(e,d),
\[
 v_e=d^{-2}\,\mathbb E_Q[g_{e/h}((d/h)K)]
\]
is an exact convenient twisted-residue expression.

## 3. Certified finite trials, including all infinite periodic tails

For L=6,30,210,2310, choose the rational coefficients listed in the appendix,
put \(F_L=\sum_{e\mid L,\ e>1}c_e g_e\), and \(A_L=F_L-g_L\).
The following are outward rounded **upper bounds on squared legal distance**:

| Squarefree L | Atoms | Complete trial error is less than |
|---:|---:|---:|
| 6 | 3 | 0.026990 |
| 30 | 7 | 0.024290 |
| 210 | 15 | 0.016848 |
| 2310 | 31 | 0.013550 |

These certify particular rational trials. They do not certify exact optimality,
a convergence rate, or distance decay along an infinite sequence.

For example, the L=6 trial has constant-target coefficients
\[
 (c_2,c_3,c_6)=\frac1{10^8}(104591812,106955801,60474992),
\]
and its reflected-target coefficient at g_6 is c_6-1. The L=30 coefficients
in increasing divisor order \(2,3,5,6,10,15,30\) are
\[
 \frac1{10^8}(98558690,96341922,82372096,-15823158,9195184,13861138,14643875).
\]
All indices are actual squarefree divisors, including the composites.

For any squarefree d>=2, keep this same L=2310 seed and use
A_d=F_2310-g_d in the finite legal stage of lcm(2310,d). Its complete
constant-target energy is less than U=0.013549483, by adding 1/2310^2
to the reflected certificate. Thus the explicit bound for arbitrary d is
\[
 \boxed{\ \operatorname{dist}(R_d,V_{\rm sq})
      \le\sqrt{0.013549483}+\frac1d.\ }
\]
The limiting bound is positive; no decay theorem follows.

### Exact certificate method

For a periodic residual r of period L, with representatives 1 through L,
the complete identity is
\[
 \|r\|_Q^2=\frac1Z\sum_{a=1}^L r(a)^2 W_L(a),\qquad
 W_L(a)=\sum_{k=0}^{\infty}\frac1{(a+kL)^2}.             \tag{3.1}
\]
The representative a=L accounts for positive multiples of L. Here r(L)=0
for the reflected trial, whereas the constant-target residual is one there.

After K=128 progression terms, monotonicity gives
\[
 \frac1{L(a+KL)}
 \le\sum_{k=K}^{\infty}\frac1{(a+kL)^2}
 \le\frac1{L(a+(K-1)L)}.                              \tag{3.2}
\]
Each reciprocal-square term, each progression remainder bound, and Z are
rounded outward using integers with scale S=10^24. For Z, retain 20,000
terms and use the tail interval [1/20001,1/20000]. The resulting final
bounds are rational numbers, displayed exactly in the appendix.

Floating point was used only to propose coefficients. Every reported trial
has rational coefficients, and its subsequent certificate uses integer
arithmetic only. The interval certificate is external computation, not a
Lean theorem. The short program and its exact output are preserved alongside
this record.

For example, the exact upper certificates for L=6 and 2310 are respectively
\[
 \frac{63422776727990217091239961581017265511}
 {2349905807997615138399140000000000000000}
 <0.026990
\]
and
\[
 \frac{148661726500746101481934276554626089377250907}
 {10971915834299064872510194584750000000000000000}
 <0.013550 .
\]

## 4. A genuine obstruction to pure escaping-conductor packets

Every finite combination of atoms with conductors greater than H satisfies
\[
 F(n)=nF(1)\quad(1\le n\le H).
\]
Suppose 1<=H<d, set \(t=F(1)+1/d\), and write
\(h_H=\sum_{n=1}^H1/n,\ s_H=\sum_{n=1}^H1/n^2\).
Keeping the entire infinite tail, the exact identity is
\[
 \boxed{\ \|R_d-F\|_Q^2
 =\frac1Z\left[s_H-\frac{h_H^2}{H}
      +H\left(t-\frac{h_H}{H}\right)^2\right]
   +\frac1Z\sum_{n>H}\frac{|R_d(n)-F(n)|^2}{n^2}.\ }    \tag{4.1}
\]
No bound on coefficients, their signs, or support cardinality is assumed.
Thus if both the least conductor and d tend to infinity,
\[
 \liminf\|R_{d_j}-F_j\|_Q^2\ge1,
\]
because \(s_H\to Z\) and \(h_H^2/H\to0\).

Since zero is an admissible trial and R_d tends strongly to one, the
squared distance infimum over the entire escaping-conductor span actually
tends to one as well (choose H_j below both cofinal cutoffs).

Already H=2 gives the uniform obstruction
\[
 \boxed{\ \|R_d-F\|_Q^2\ge\frac1{8Z}\quad(d\ge3),\ }    \tag{4.2}
\]
whenever every conductor in F is at least three.

In particular, if d is odd and the approximant is restricted to the
own-period divisor stage V_d, every nonzero atom has conductor at least
three. Thus the same positive lower bound holds over that entire stage.
A target conductor tending to infinity does not itself make its divisor
stages exhaustive. For arbitrary target sequences one must allow separate
period enlargement, for example by adjoining an increasing primorial.

More precisely, if \(F=c_2g_2+G\), with all conductors in G at least three,
then \(F(2)=2F(1)-c_2\). With \(u=1-1/d-F(1)\),
\[
 \boxed{\ \|R_d-F\|_Q^2
 =\frac{(c_2-1)^2}{8Z}
  +\frac2Z\left(u+\frac{c_2-1}{4}\right)^2
  +\frac1Z\sum_{n\ge3}\frac{|R_d(n)-F(n)|^2}{n^2}.\ }   \tag{4.3}
\]
Consequently, vanishing error forces c_2 to tend to one. Old modes cannot
all be discarded. The analogous fixed-coordinate conditions are consistent
with the existing Möbius coefficient recovery theory.

Application to CRT packets: an unscreened fresh-prime packet supported on
p_j*e with p_j tending to infinity has the escaping-support obstruction.
Compensated packets with the same escaping support also have it. This says
nothing against screened updates that reintroduce fixed old conductors;
their signed sources and full screened energies require separate estimates.

## 5. The direct primorial Möbius construction fails in full norm

This strengthens the already recorded fixed-positive obstruction for the
uncorrected prime sieve in QPrimeSieve.lean. The divergence argument here is
a mathematical proof, not newly Lean formalized.

Let \(p_1=2<p_2<\cdots\), \(L_M=\prod_{i=1}^M p_i\), and
\(\alpha_M=\varphi(L_M)/L_M\). Let \(A_L(n)\) count integers at most n
coprime to L. The existing exact sieve identity is
\[
 B_M=-\sum_{e\mid L_M}\mu(e)g_e,\qquad
 B_M(n)=A_{L_M}(n)-n\alpha_M.                         \tag{5.1}
\]
All floor/carry terms are included in A_L. For \(1\le n\le p_M\),
\(A_{L_M}(n)=1\); hence
\[
 \boxed{\ \|1-B_M\|_Q^2
 =\frac{p_M\alpha_M^2}{Z}
  +\frac1Z\sum_{n>p_M}
     \frac{|1-A_{L_M}(n)+n\alpha_M|^2}{n^2}.\ }        \tag{5.2}
\]

An elementary bound suffices to prove divergence; Mertens' theorem and PNT
are unnecessary. Since \(p_i\ge2i-1\) for i>=2, the Wallis comparison gives
\[
 \alpha_M^2\ge\frac1{4(2M-1)}.                        \tag{5.3}
\]
For completeness, start at \(\alpha_1^2=1/4\), multiply at step M+1
by at least \((2M/(2M+1))^2\), and use
\(4M^2\ge(2M-1)(2M+1)\).

Also \(p_M/M\to\infty\), by the elementary zero natural density of primes.
Here is a self-contained justification of the needed fact. Every n<=x
has prime factors at most x, so the finite harmonic sum is at most
\(\prod_{p\le x}(1-1/p)^{-1}\); therefore the reciprocal Euler products
\(\alpha_M\) tend to zero. For any fixed K, every prime exceeding p_K is
coprime to L_K, whose periodic set of coprime integers has density
\(\alpha_K\). Thus \(\limsup_{x\to\infty}\pi(x)/x\le\alpha_K\), and
letting K tend to infinity gives \(\pi(x)/x\to0\). At x=p_M, this implies
M/p_M tends to zero.

Combining (5.2)--(5.3),
\[
 \boxed{\ \|1-B_M\|_Q^2
 \ge\frac{p_M}{4Z(2M-1)}\longrightarrow\infty.\ }      \tag{5.4}
\]
The coefficients at every fixed squarefree conductor also agree eventually
with -mu(e). Thus even the correct compatible infinite coefficient family
and fixed-coordinate convergence do not supply a bounded physical realization.
This does not contradict the existing converse for bounded families or
least-squares approximants.

Yet B_M(n) tends to one at every fixed physical n. This is a concrete
failure of uniform integrability/energy, rather than a failure of legality.
The associated reflected trial \(B_M-g_{L_M}\) has error
\(\|1-B_M\|_Q^2-L_M^{-2}\), so it fails as well.

### The direct exact-head repair also fails

A natural one-atom repair is
\[
 T_M=B_M+\varphi(L_M)g_{L_M},\qquad
 T_M(n)=A_{L_M}(n)-\varphi(L_M)\lfloor n/L_M\rfloor.   \tag{5.5}
\]
It is periodic, legal, and equals one on the entire head through p_M.
For even L=L_M>=6, the reduced residues pair as a and L-a; hence
\(A_L(L/2)=\varphi(L)/2\). On L/2<=n<=L-1,
\(T_M(n)\ge\varphi(L)/2\), giving
\[
 \|1-T_M\|_Q^2\ge
 \frac{(\varphi(L)/2-1)^2}{2ZL}.                     \tag{5.6}
\]
For M>=3 this is at least
\[
 \frac{L_M}{128Z(2M-1)}\longrightarrow\infty.
\]
This also excludes the weaker subpolynomial exact-head consumer for this
particular repair. Every inclusive exact head length H_M is less than L_M, since
T_M(L_M)=0 (the exclusive cutoff is at most L_M). Also L_M>=2^M. Thus, for any cofinal exact head schedule,
\[
 \liminf_{M\to\infty}
 \frac{\log(1+\|1-T_M\|_Q^2)}{\log H_M}\ge1,
\]
because the numerator is at least log(L_M)-log(2M-1)-O(1), while the
denominator is at most log(L_M), and log(M)/log(L_M) tends to zero.
The reflected version \(T_M-g_{L_M}\) inherits this divergence via (2.2).
This excludes this direct repair. It does not exclude the exhaustive affine
optimizer with arbitrary period enlargement and old-coefficient refitting.

## 6. CRT carry and legality audit

For squarefree L and inverse CRT coefficients a_p modulo p,
\[
 g_L(n)=\sum_{p\mid L}a_p g_p(n)-K_L(n),\qquad
 K_L(n)=\left\lfloor\sum_{p\mid L}a_p g_p(n)\right\rfloor .
\]
The integer-valued carry is required. The reflected expression is therefore
\[
 R_L=1-I_L-\sum_{p\mid L}a_p g_p+K_L.
\]
Neither K_L nor the isolated constant is automatically in the legal linear
span. Nonlinear log/exp formulas in coefficient algebras need their explicit
legal synthesis theorem before they produce physical legal vectors.

Audited base sources:

* QConductorLimits.lean explicitly states ambient convergence without legality.
* QSquarefreeJumpApplications.lean proves the reflected-distance equivalence
  and individually positive reflected obstructions; it supplies no decay.
* QConductorEscape.lean requires full-norm boundedness for its weak-null
  theorem. The head obstruction (4.1) does not need this boundedness.
* QSquarefreeLatticePackets.lean proves finite membership by span induction,
  and floor-dilation transport by literal residue identities. Its finite
  legality results do not rely on ambient convergence.
* QSquarefreeFormalSynthesis.lean proves finite legality before taking limits;
  its strong_limit_mem_closed_span and weak_limit_mem_closed_span require
  every approximating vector to be legal. Its cumulant_synthesis_range
  identifies the finite cumulant range with the same finite linear range,
  so this parameterization supplies no automatic extra physical vectors.
* QPrimeSieve.lean already rejects the raw prime sieve as a norm approximation.
* QMobiusPrimePacketArithmetic.lean retains the complete coprime-count
  discrepancy and integer floors; they must not be replaced by the short head.

No incorrect ambient-limit-to-legality inference was found in these inspected
modules. This is a bounded audit, not a claim to have reviewed every historical
infinite-CRT argument. The forbidden singleton route remains excluded by
qPoint_zero_not_mem_squarefreeClosure.

The finite log/exp identities parameterize the same finite synthesis range.
Therefore their finite quantitative optimization is precisely the Gram
problem (2.7). At the infinite level, the compatible Mobius coefficients in
Section 5 supply a direct example of why a physical energy bound must be
proved separately from coefficient compatibility.

## 7. Precise remaining arithmetic obligation

A potentially viable construction must retain the necessary low Möbius modes
and control complete signed Gram energy while screening new legal packets
against the old stage.

At a finite old stage V and a fresh packet, put
\(r=R_d-P_VR_d\), \(w=(1-P_V)h\), for a genuinely legal trial h.
The exact one-direction improvement is
\[
 \min_t\|R_d-(P_VR_d+t w)\|_Q^2
 =\|r\|_Q^2-\frac{|\langle r,w\rangle_Q|^2}{\|w\|_Q^2}
\]
when w is nonzero. The packet Schur complement gives the corresponding
complete multi-direction identity.

Open: prove enough accumulated actual signed gain to exhaust the residual,
or prove subpolynomial complete error for the exhaustive exact-head affine
minima. The already formalized geometric equivalence, the small finite
certificates, and the positivity of individual packet gains are insufficient.

## 8. Verification status

**Successful complete-module server check (18 October 2026):**
job_QeBAiLVvECAXxBZueYmMx6f3Zw2Vsr_e terminated with state=succeeded,
classification=success, exit_code=0, verified=true.
The checked file was RiemannResearch/RH/QReflectedFiniteStage.lean,
SHA-256 d639adfc28af23ece46d0e847f001d2677532ae442e3e295b4d79e766d3fe357.
The check also builds its imported QDivisibilityHilbertMoments companion.

The public checked declarations in QDivisibilityHilbertMoments are
inner_qDivisor_eq_dilation, qOne_inner_qDivisor, qDivisor_norm_sq,
qDivisor_inner_qDivisor, and qResidue_inner_qDivisor_eq_zero.

The checked declarations in QReflectedFiniteStage are
qReflected_short_head, twoSite_energy_le, reflected_twoSite_energy_exact,
reflected_error_sq_ge_coefficient, reflected_error_sq_ge_of_tailSpan,
divisorStage_inner_qDivisor_zero, reflected_shift_energy_exact,
reflected_divisorStage_energy_exact, reflected_divisorStage_trial_mem,
binaryTrial, binaryTrial_mem, and binaryTrial_energy_exact.
Their complete types, including positive-conductor, squarefreeness, stage
membership, and two-site head hypotheses, are in the source files.
No RH premise or unproved arithmetic provider is used for these lemmas.

Earlier isolated checks and build timeouts were superseded by this successful
full-module check. A timeout was never interpreted as a mathematical
refutation. The source and final exports are subject to the separate
mandatory server checkpoint before publication; the terminal checkpoint
job, validation scope, integration result, and published commit are recorded
in the accompanying final research response.

The exact finite Gram/projection corollaries, sharp distance estimate (2.5),
general-H limit, and primorial divergence proofs are mathematical derivations
in this record, not newly Lean-verified declarations. The rational trials
were reproduced by the integer-only checker in Appendix B on 18 October
2026; these external certificates are not Lean proofs.

The reflected-distance decay provider and the subpolynomial complete-energy
provider remain **Open**. No unconditional RH conclusion is obtained.

## Appendix A: exact rational trial data

The coefficient at g_L in the reflected approximant is the stored
constant-target coefficient minus one. The lower interval endpoints below
bound these particular trial energies, not the distance infimum.

```json
[
  {
    "M": 2,
    "L": 6,
    "conductors": [
      2,
      3,
      6
    ],
    "coefficient_numerators": [
      104591812,
      106955801,
      60474992
    ],
    "coefficient_denominator": 100000000,
    "weight_scale": 1000000000000000000000000,
    "period_terms": 128,
    "zeta_terms": 20000,
    "reflected_error_lower": "110987144427488860145888864560741178129/4112335170245514007872715000000000000000",
    "reflected_error_upper": "63422776727990217091239961581017265511/2349905807997615138399140000000000000000",
    "reflected_error_lower_decimal": 0.02698883720143432,
    "reflected_error_upper_decimal": 0.02698949741395532
  },
  {
    "M": 3,
    "L": 30,
    "conductors": [
      2,
      3,
      5,
      6,
      10,
      15,
      30
    ],
    "coefficient_numerators": [
      98558690,
      96341922,
      82372096,
      -15823158,
      9195184,
      13861138,
      14643875
    ],
    "coefficient_denominator": 100000000,
    "weight_scale": 1000000000000000000000000,
    "period_terms": 128,
    "zeta_terms": 20000,
    "reflected_error_lower": "71916884293430726370330218548234747301929/2960881322576770085668354800000000000000000",
    "reflected_error_upper": "359587443170634810496750457561361281845243/14804406590384975371914582000000000000000000",
    "reflected_error_lower_decimal": 0.024289012783141044,
    "reflected_error_upper_decimal": 0.024289216928436445
  },
  {
    "M": 4,
    "L": 210,
    "conductors": [
      2,
      3,
      5,
      6,
      7,
      10,
      14,
      15,
      21,
      30,
      35,
      42,
      70,
      105,
      210
    ],
    "coefficient_numerators": [
      97783483,
      95786736,
      79007546,
      -46319980,
      67151411,
      -8515729,
      3657134,
      -13165232,
      1401111,
      19990833,
      -2173262,
      6993663,
      994256,
      1559079,
      -4562652
    ],
    "coefficient_denominator": 100000000,
    "weight_scale": 1000000000000000000000000,
    "period_terms": 128,
    "zeta_terms": 20000,
    "reflected_error_lower": "42436189527446114272368859799852471970973/2518805291775377329822037937500000000000000",
    "reflected_error_upper": "38798872252966503573921401868354065709/2302907691837662835631157200000000000000",
    "reflected_error_lower_decimal": 0.016847745105988327,
    "reflected_error_upper_decimal": 0.016847775701337803
  },
  {
    "M": 5,
    "L": 2310,
    "conductors": [
      2,
      3,
      5,
      6,
      7,
      10,
      11,
      14,
      15,
      21,
      22,
      30,
      33,
      35,
      42,
      55,
      66,
      70,
      77,
      105,
      110,
      154,
      165,
      210,
      231,
      330,
      385,
      462,
      770,
      1155,
      2310
    ],
    "coefficient_numerators": [
      98360368,
      95701608,
      82700157,
      -56287387,
      69806794,
      -44865827,
      67916718,
      -10680828,
      -18222439,
      -7619071,
      -8291396,
      44604022,
      -19963922,
      -10074402,
      20036042,
      -14901127,
      6450188,
      17089584,
      -13428045,
      6647380,
      5379237,
      -6449483,
      10573294,
      -24204806,
      13287971,
      -9576719,
      7435896,
      -2353177,
      -397800,
      -3272228,
      3483634
    ],
    "coefficient_denominator": 100000000,
    "weight_scale": 1000000000000000000000000,
    "period_terms": 128,
    "zeta_terms": 20000,
    "reflected_error_lower": "12388474438285181297865063065532029086063403/914326320914461970725399771312500000000000000",
    "reflected_error_upper": "148661726500746101481934276554626089377250907/10971915834299064872510194584750000000000000000",
    "reflected_error_lower_decimal": 0.013549292145385106,
    "reflected_error_upper_decimal": 0.013549295195650148
  }
]
```


## Appendix B: independent integer certificate checker

Save this code as check.py beside this report and run python3 check.py.
It reads Appendix A from this report; no numerical libraries are required.

```python
"""Check complete periodic Q-energy certificates with integer arithmetic.

The integral tail bounds are described in the accompanying research record.
This is an external arithmetic certificate checker, not a Lean proof.
"""
from fractions import Fraction
from math import isqrt
from pathlib import Path
import json

report = Path(__file__).with_name(
    "Q_Reflected_Approximants_2026-10-17.md").read_text()
records = json.loads(report.split("```json\n", 1)[1].split("```", 1)[0])
limits = {6: 26990, 30: 24290, 210: 16848, 2310: 13550}

for record in records:
    L = record["L"]
    C = record["coefficient_denominator"]
    S = record["weight_scale"]
    K = record["period_terms"]
    N = record["zeta_terms"]
    ds = record["conductors"]
    cs = record["coefficient_numerators"]
    assert L > 1 and C > 0 and S > 0 and K >= 1 and N >= 1
    assert ds == [d for d in range(2, L + 1) if L % d == 0]
    assert all(L % (k*k) for k in range(2, isqrt(L) + 1))
    assert len(ds) == len(cs)

    # Sum of floor-rounded finite terms plus outward integral remainders.
    z_base = sum(S // (n*n) for n in range(1, N + 1))
    z_lo = z_base + S // (N + 1)
    z_hi = z_base + N + (S + N - 1) // N
    lower_numerator = upper_numerator = 0
    for a in range(1, L + 1):
        base = sum(S // ((a + k*L)**2) for k in range(K))
        w_lo = base + S // (L*(a + K*L))
        den = L*(a + (K-1)*L)
        w_hi = base + K + (S + den - 1) // den
        r = (0 if a == L else
             C*L - sum(c*(a % d)*(L//d) for c, d in zip(cs, ds)))
        lower_numerator += r*r*w_lo
        upper_numerator += r*r*w_hi

    scale = C*C*L*L
    lower = Fraction(lower_numerator, scale*z_hi)
    upper = Fraction(upper_numerator, scale*z_lo)
    assert lower == Fraction(record["reflected_error_lower"])
    assert upper == Fraction(record["reflected_error_upper"])
    assert lower <= upper < Fraction(limits[L], 10**6)
    print(f"L={L}: complete reflected trial squared error < "
          f"{limits[L]//10**6}.{limits[L]%10**6:06d}")

```
