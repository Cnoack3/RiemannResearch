# Pareto continuation: normalized even optimization and exact parity energy

Date: 21 September 2026. Starting publication:
`a08278c2e59012e06c7e7aa99a04a6e5fb2307c7`.

This continues the supplied head-normalization handoff. Mathematical development
was divided among three subagents; all Lean verification was submitted by one
coordinator. RH remains unresolved. The results below keep the actual complete
Pareto tail norm and all signed mixed terms.

## 1. The optimal even correction with the correct head

Write `z=infiniteCoprimeCertificate 2`, `kappa=1+||z||^2/2`, and let E_n be
the span of every even tail atom in the finite dictionary. For fixed signed
odd coefficients b, let

\[
x_b=(I-P_{E_n})\sum_{d\text{ odd}}b_dt_d,\quad
z_E=P_{E_n}z,\quad K_n=\|z_E\|^2,\quad r_b=\langle x_b,z\rangle.
\]

For every nonempty dictionary K_n>0. The unique minimum over even coefficients
subject to the exact normalization h=kappa J is

\[
F_b^\sharp=x_b-\frac{r_b}{K_n}z_E,
\qquad
\boxed{\|F_b^\sharp\|^2=\|x_b\|^2+\frac{r_b^2}{K_n}.}
\]

The coefficients are explicit inverse-Gram coefficients in the original
dictionary. Every odd coefficient is unchanged. The normalization is checked
by the existing identity <F,z>=h-kappa J. No density assumption supplies an
inverse: finite independence already proves the inverse exists.

For every other feasible even correction a, the complete energy is exactly
the displayed minimum plus the squared norm of its difference from the
minimizing even combination. This also proves uniqueness.

Since <t_2,z>=1/2, the quantitative estimates are

\[
1\le4\|t_2\|^2K_n,\qquad
\|F_b^\sharp\|^2\le\frac{\|z\|^2}{K_n}\|x_b\|^2
\le4\|t_2\|^2\|z\|^2\|x_b\|^2.
\]

Consequently the original small-tail existence condition is equivalent to
small-tail existence using precisely these normalized even optimizers.
The associated RH theorem is a conditional research reduction: existence
of the small-energy family remains Open.

Module: `RH/ParetoOddMomentNormalizedSchur.lean`.

## 2. An explicit normalized version of the global odd-moment optimizer

Let c_n^* be the existing full inverse-Gram odd-moment optimizer, with
energy kappa^2/Q_n. Its synthesized vector is orthogonal to every even
tail atom. The earlier modulus-two normalization therefore has the sharper
exact cost

\[
\|F_n^\sharp\|^2=\frac{\kappa^2}{Q_n}
+4\langle F_n^*,z\rangle^2\|t_2\|^2
\le (1+4\|z\|^2\|t_2\|^2)\frac{\kappa^2}{Q_n}.
\]

The new coefficients have J=1 and h=kappa exactly. This supplies a canonical
normalized finite candidate at every stage n>=2. It does not establish
Q_n tending to infinity.

Module: `RH/ParetoNormalizedOddOptimizer.lean`.

## 3. Exact extraction of the arithmetic parity contrasts

For a physical odd site p>=3 define

\[
D_c(p)=\sum_{d\mid p,\ d\ge2}c_d.
\]

Only odd moduli divide p. The actual difference-certificate pairing is

\[
\langle u_p,F_c\rangle=F_c(p)-F_c(p-1)=h(c)-D_c(p),
\quad \|u_p\|^2=2p^2.
\]

The vectors u_p for distinct odd p have disjoint support. For every finite
set A of such p, with P_A its actual orthogonal projection, one has

\[
\boxed{\|F_c\|^2=
\sum_{p\in A}\frac{(\kappa-D_c(p))^2}{2p^2}
+\|F_c-P_AF_c\|^2\quad\text{if }h(c)=\kappa.}
\]

Every odd composite divisor and signed coefficient remains in D_c.
Independent even corrections cannot change any D_c(p). The final squared
norm is an exact remainder, not a term that may be discarded in proving
an upper estimate.

Module: `RH/ParetoParityContrast.lean`.

## 4. Adjacent odd/even correction with harmonic energy cost

For d>=2 put R_d(j)=j mod d and

\[
r_d=d^2t_d-d(d+1)t_{d+1}=d(R_d-R_{d+1}).
\]

If d is odd, the actual finite coefficient vector has h=0 and J=1.
Every physical coordinate j<d vanishes. For the literal infinite tail
remainder U_d of the unscaled residue difference beyond d(d+1),

\[
\boxed{\|r_d\|^2=d^2\left(H_d-\frac d{d+1}+U_d\right),
\qquad 0\le U_d\le\frac d{d+1}.}
\]

Here H_d=sum_{k=1}^d 1/k. In particular

\[
d^2\left(H_d-\frac d{d+1}\right)\le\|r_d\|^2\le d^2H_d.
\]

The exact first-period identity uses every jump and plateau on
0<=j<d(d+1). The remainder bound controls the complete infinite tail.

For any coefficient vector c whose dictionary contains d and d+1, put
delta=1-J(c) and add delta times this explicit packet. Then

\[
J(c')=1,\qquad h(c')=h(c),\qquad F_{c'}(j)=F_c(j)\ (j<d),
\]
\[
\|F_{c'}\|^2=\|F_c\|^2+2\delta\langle F_c,r_d\rangle
+\delta^2\|r_d\|^2,
\qquad \|F_{c'}-F_c\|^2\le\delta^2d^2H_d.
\]

This is a controlled normalization of candidates. To obtain vanishing
energy one still needs control of the original candidate and the displayed
correction cost. The packet with unit moment itself has growing energy.

Modules: `RH/AdjacentResidueHarmonic.lean` and
`RH/ParetoAdjacentMomentCorrection.lean`.

## 5. An explicit arithmetic family closes the complete parity component

This section concerns actual finite Hilbert vectors, not a formal replacement
of their full norm. Put

\[
S=\sum_{p\ge3,\ p\text{ odd}}p^{-2}=\pi^2/8-1,\qquad Z=S+1.
\]

For positive P divisible by three, define the finite signed coefficients on its
non-unit divisors by c_d=-a mu(d). All divisors are included, including
even ones. Let M_P denote their odd reciprocal-square moment when a=1.
Their exact divisor-sum mask and mass identity are

\[
D_c(p)=a\,\mathbf1_{\gcd(P,p)>1},\qquad
Z M_P=S-R_P,\quad
R_P=\sum_{p\ge3,\ p\text{ odd},\ \gcd(p,2P)=1}p^{-2}.
\]

M_P>0. Choose a=1/M_P, and change only the coefficient at modulus two by
2(kappa-H_P), where H_P is the reciprocal head before this correction.
The odd moment is one; the reciprocal head becomes kappa. The construction
is an actual finite tail-atom combination. Its complete odd-pair contrast
energy is exactly

\[
\boxed{\mathcal V_P=
\frac{Z^2R_P}{2S(S-R_P)}.}
\]

For P=(n+2)!, each fixed odd p>=3 is excluded from R_P eventually. The
summable majorant p^{-2} proves R_P tends to zero by dominated convergence.
Consequently the entire contrast energy of the genuine normalized finite
Möbius vectors tends to zero, without RH or a prime-distribution estimate.
The first factorial stage has no odd prime; the unit-moment assertion starts
at n>=1, which is sufficient for the limit.

The key endpoint is `factorial_sieve_fullOddPairContrast_tendsto_zero`.
The definition `fullOddPairContrastEnergy` uses the actual Hilbert pairings
with the two-point difference certificates. The identification with the
arithmetic expression, its summability, the Möbius mass identity, and the
limit are separate declarations. Thus no unproved arithmetic bridge is
being hidden in the limiting scalar expression.

Modules: `RH/ParetoParitySieveMass.lean`, `RH/ParetoSieveMobiusBridge.lean`,
and `RH/ParetoSieveContrastClosure.lean`.

## 6. The remaining full-energy test is explicit

For the all-divisor sieve just constructed, when P is even, the actual
value at physical site two and its full-energy consequence are

\[
F_P(2)=2H_P-a,\qquad
\boxed{\|F_P\|^2\ge\frac{(2H_P-a)^2}{6}.}
\]

The modulus-two head correction cannot change this value, because t_2(2)=0.
This is a checked full-tail test, not an asymptotic assertion. In ordinary
Euler-product notation H_P=a(1-B_P), with B_P=prod_{prime ell|P}(1-1/ell).
For 6 dividing P one has B_P<=1/3; together with a>1 this gives the ordinary
strict floor 1/54. The Euler-product specialization of this last numerical
floor is not separately formalized here; the exact Hilbert lower bound is.
Thus the raw all-divisor sieve should not be presented as a full small-tail
sequence merely because its contrast energy vanishes.

The productive next candidate keeps these odd Möbius coefficients and
uses the independently optimized even coefficients from Section 1. Enforcing
h=kappa ensures that every odd-pair contrast remains unchanged. What is
still missing is a bound making the complementary block-mean energy small.

Module: `RH/ParetoSieveFullEnergy.lean`.

## 7. Research boundary

The new identities identify and optimize legitimate finite corrections.
They do not supply an unconditional family with J=1, h=kappa and complete
tail norm tending to zero. No RH hypothesis, not-RH hypothesis, zeta-zero
existence input, or RH-to-density provider is introduced in these results.
No DPP estimate was needed.

The remaining goal is an upper estimate for the complete optimized energy,
including the orthogonal remainder in Section 3. Unboundedness of Q_n and
RH remain Open.

The final installed-module acceptance is the single publishing checkpoint.
Its commit and job receipt are recorded in Git and the delivered continuation.
No separate full-project build is submitted immediately before it.

## Candidate verification

The complete nine-module candidate passed the serialized Lean check with
exit code 0 in 36.535 seconds. Job:
`job_FZfCF_bDJYOsbVG8W6-dPoRkhk39ook3`.

The addition contains 101 proved theorems (including private helpers) and
18 definitions. Nine key declarations were audited; each depends only on
`[propext, Classical.choice, Quot.sound]`. There are cosmetic tactic-style
warnings, with no compilation errors or admitted proofs. No project-local
axiom or unsafe declaration is introduced. The substantive small-full-tail
premise in the conditional RH endpoint remains Open.

Final acceptance of the installed files against their declared imports is
the single publishing checkpoint, which also includes exports, catalog and
research notes. The delivery receipt records its outcome and published commit.
