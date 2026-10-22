# Direct MediumPNT bootstrap and the optimized moving subhalf band

Continuation of `ba20efab4f7d02ff2ed484f1de9b78909c74e009`.
The positive-certificate necessity extension starts from
`9434d9b3704cd76a0c3cfa93f43e6030ea8b7b24`, following
`4e15dc26dd80f7da1a9777340cd67cda23846d87`.

**Verification record:** the complete arithmetic, analytic, endpoint, and
moving-band assembly passed serialized Lean job
`job_TBpHy99-BdxFXakNU5xioVEaL215xY4Z` with `exit_code=0` and
`verified=true`. The principal Mertens, endpoint, and shared moving-band
package declarations each depend only on `propext`, `Classical.choice`,
and `Quot.sound`. Publication additionally validates the actual modules
and affected reverse dependencies through the final project checkpoint.

**Necessity extension verification:** the complete regular-profile comparison,
lower-shift, finite positive-certificate budget, and exponent-necessity assembly
passed serialized Lean job `job_S3KpGSBQdx-DubWlUuW7kYWEqIBxCZKH` with
`exit_code=0` and `verified=true`. The necessity theorem, its delayed-argument
corollary, exact deficit theorem, and scalar-budget classification each report
only `propext`, `Classical.choice`, and `Quot.sound`. The final project checkpoint
also validates the companion positive-Abel modules, actual imports, and reverse
dependencies before publication.

## Result and scope

The old inverse-fourth-log weakening and its single cutoff optimization
were not a ceiling of the finite bootstrap. Reusing the full established
`Quantitative.MediumPNT` provider gives a uniform stretched-exponential
Mertens estimate, with an iterated-logarithm improvement.

For some constants \(d>0\) and \(B\ge0\), the arithmetic theorem is

\[
\boxed{
|M(x)|\le Bx\exp\!\left[-d
 \bigl((6+\log x)\log(6+\log x)\bigr)^{1/11}\right]
\quad(x\ge1).
}
\tag{1}
\]

The positive constant is existential. Neither a numerically optimized
constant nor absolute optimality among all possible arithmetic arguments
is asserted.

The complete signed endpoint Hilbert error has the same profile with a
possibly smaller positive constant. Put

\[
L_M=6+\log(M+1),\qquad \Phi(L)=(L\log L)^{1/11}.
\]

The endpoint theorem is

\[
\boxed{
\|F_{1/2,M}-f_{1/2}\|
 \le C\exp[-a\Phi(L_M)]\quad(M\ge0)
}
\tag{2}
\]

for some \(a>0\), \(C\ge0\). This bounds the full infinite physical
Hilbert norm, including the finite head and physical tail.

For every fixed \(0\le c<a\), the supported moving band is

\[
\boxed{
0\le\tfrac12-\epsilon\le
 c\,L_M^{-10/11}(\log L_M)^{1/11}.
}
\tag{3}
\]

Equivalently, \((1/2-\epsilon)L_M\le c\Phi(L_M)\).
The full signed cutoff vectors converge to \(f_{1/2}\) uniformly over
this band as \(M\) tends to infinity. Their complete squared norms—and
hence their complete signed Gram energies—converge to the endpoint energy.

The band still shrinks to zero width. It proves no finite-energy
statement at a fixed \(\epsilon<1/2\), and does not provide positive
dampings tending to zero. The RH-strength gap remains open.

## 1. Retaining the actual PNT provider

The established arithmetic input has some positive constant \(c_0\) with
Chebyshev error bounded by a constant times

\[
u\exp[-c_0(\log u)^{1/10}].
\]

Reserve a smaller positive exponential coefficient and absorb the
remaining exponential into an inverse-square-log factor. This gives
positive \(c,D\) such that, for every \(u\ge1\),

\[
|\psi(u)-u|\le
\frac{Du\exp[-c(\log u)^{1/10}]}{(1+\log u)^2}.
\tag{4}
\]

This is a consequence of MediumPNT and bounded initial arguments; it is
not an added arithmetic hypothesis. The existing finite reciprocal-square-
log sum is at most three. Therefore the signed prime-error head satisfies

\[
\left|\sum_{n\le Y}\mu(n)(\psi(N/n)-N/n)\right|
 \le3DN\exp[-c(\log(N/Y))^{1/10}].
\tag{5}
\]

The exact Möbius/Mangoldt finite identity is retained. Only the estimates
of its pieces change.

## 2. The genuine infinite-tail envelope

Define

\[
E(T)=\sup_{N\in\mathbb N,\,N\ge1,\,\log N\ge T}\frac{|M(N)|}{N}.
\]

The implementation includes zero as a harmless value for indices below
the threshold. The elementary bound \(|M(N)|\le N\) gives
\(0\le E(T)\le1\). If \(Y\) is a positive natural cutoff with
\(e^s\le Y\), the floor identity gives the real-argument bound

\[
|M(u)|\le E(s)u\quad(u\ge Y).
\tag{6}
\]

This resolves a genuine uniformity issue: the finite reciprocal-cutoff
theorem asks for a bound at **every** real argument above \(Y\). Ordinary
strong induction on the single conductor \(N\) does not by itself supply
that hypothesis.

Fix \(T>0\), \(L\ge0\), with \(T-L\ge\log2\). For each
\(N\ge e^T\), choose

\[
Y=\lfloor Ne^{-L}\rfloor,\qquad J=\lfloor e^L\rfloor+1.
\]

The cutoff loss \(L\) is held fixed while the supremum over \(N\) is
taken. The floor inequalities give

\[
e^{T-L-\log2}\le Y,\qquad
L\le\log(N/Y)\le L+\log2.
\]

The reciprocal and harmonic terms satisfy

\[
Y/N\le e^{-L},\quad 1/J\le e^{-L},\quad
1/(YJ)\le e^{-L},\quad H_J+1\le L+2+\log2.
\]

Substitution into the finite arithmetic bound and then taking the
supremum proves the explicit recurrence inequality

\[
\boxed{
E(T)\le
\frac{(3L+13+7\log2)E(T-L-\log2)
      +3e^{-L}+3D e^{-cL^{1/10}}}{T}.
}
\tag{7}
\]

No monotonicity assumption on a subsequently chosen function \(L(T)\)
is needed.

## 3. Uniform delayed contraction

Set

\[
z(T)=\bigl((T+6)\log(T+6)\bigr)^{1/11},
\qquad L(T)=z(T)^{10},
\qquad r(T)=T-L(T)-\log2.
\]

For all sufficiently large \(T\), \(r(T)\ge0\) and
\(r(T)\le T-1\). The logarithmic comparison and an integer-power
inequality give

\[
z(T)-z(r(T))\le2(\log(T+6)+1).
\tag{8}
\]

Choose a sufficiently small positive \(d\), below the available prime
coefficient. Multiplying (7) by \(e^{dz(T)}\), (8) makes its first
coefficient at most one half for all sufficiently large \(T\). The two
forcing terms have a fixed uniform bound because
\(L(T)^{1/10}=z(T)\).

Thus \(G(T)=E(T)e^{dz(T)}\) obeys

\[
G(T)\le\tfrac12G(r(T))+C_0,
\qquad 0\le r(T)\le T-1.
\tag{9}
\]

Natural induction on successive real intervals bounds \(G\) globally,
using \(E\le1\) on the initial interval. This is uniform in \(T\);
it is stronger than a separate constant for each fixed logarithmic power.
Passing from natural to real arguments preserves the profile after a
constant-factor reduction of \(d\), yielding (1).

## 4. Propagation through the full endpoint norm

The weighted Mertens and density-tail estimates are upgraded with the same
logarithmic-product profile. Their derivative estimates use a small
positive exponential coefficient and preserve a positive coefficient
through partial summation.

The arithmetic floor-envelope and hyperbola-cutoff arguments then supply
a summable physical-coordinate envelope. The Hilbert-rate argument
combines that envelope with the finite-head truncation error. Both pieces
are controlled on the same profile, with constants allowed to change.
This yields (2); a physical-tail estimate alone would not establish it.

For undamping, let \(\delta=1/2-\epsilon\ge0\). The increasing Abel
identity is centered at the complete signed endpoint prefix errors.
Keeping the complete profile in its scalar increment sum gives a bound
of the form

\[
\|F_{\epsilon,M}-f_{1/2}\|
 \le C e^{-(a-c)\Phi(L_M)}+B_c\delta
\quad\text{when }\delta L_M\le c\Phi(L_M),\quad c<a.
\tag{10}
\]

Both terms vanish uniformly in (3). A split using only a constant bound
for all early prefix errors would lose part of this moving-band scale;
the full-profile Abel estimate avoids that additional loss.

## 5. Necessity within the positive cutoff framework

The exponent restriction is a theorem about a **positive proof certificate**
for recurrence (7). It is not a lower bound for the actual Mertens envelope.
Write

\[
p(T)=bT^\beta(\log T)^\eta,\qquad
r(T)=T-L(T)-\log2,\qquad A(T)=3L(T)+K.
\]

Fix \(b>0\), \(\beta>0\), \(\eta\in\mathbb R\), \(c\ge0\),
\(H>0\), and \(K\in\mathbb R\). Suppose \(r(T)\to\infty\), and
that for all sufficiently large \(T\),

\[
L(T)\ge0,\qquad A(T)\ge1,
\qquad
\frac{\exp(p(T)-cL(T)^{1/10})}{T}\le H,
\tag{11}
\]
\[
\frac{A(T)\exp(p(T)-p(r(T)))}{T}\le1.
\tag{12}
\]

Then

\[
\boxed{\beta\le\frac1{11},\qquad
\beta=\frac1{11}\Longrightarrow\eta\le\frac1{11}.}
\tag{13}
\]

Here \(H\) is a fixed uniform bound, not a function of \(T\).
No monotonicity or continuity of \(L\) is required. Negative logarithmic
exponents \(\eta\) are allowed. The declaration is
`regular_trial_positive_cutoff_exponents_of_delay_tendsto`. The stronger
`regular_trial_positive_cutoff_exponents_necessary` needs only the eventual
regular-region conditions \(r(T)>1\) and \(2|\eta|\le\beta\log r(T)\),
rather than \(r(T)\to\infty\). This restriction excludes the singular
behavior near \(r=1\) when \(\eta<0\).

These certificate assumptions follow, in particular, from a positive
supersolution calculation with trial majorant \(B\exp[-p(T)]\), where
\(B>0\) and the prime-source coefficient \(D>0\). Substitution into
(7) and division by that majorant gives the sufficient condition

\[
\frac{A(T)e^{p(T)-p(r(T))}
 +(3/B)e^{p(T)-L(T)}
 +(3D/B)e^{p(T)-cL(T)^{1/10}}}{T}\le1.
\tag{14}
\]

Under the stated cutoff and regular-region assumptions, every summand
is nonnegative. Thus (14) implies the forcing inequality in (11) and
(12), with \(H=B/(3D)\). More generally, the necessity theorem applies directly
to separate bounded-forcing and delayed-contraction certificates; it
does not require (14) as an additional assumption.

The finite obstruction retains the factors that the informal scale
comparison suppressed. Put
\(\Delta=p(T)-p(r(T))\). Taking logarithms of (11)–(12) gives exactly

\[
p(T)\le cL(T)^{1/10}+\log(TH),\qquad
\Delta\le\log\frac{T}{A(T)}.
\tag{15}
\]

In particular, the original factor \(1/T\) in the forcing term allows
the additive slack \(\log(TH)\); dropping it would impose an unjustified
stronger condition. The prefactor \(A(T)\) is also retained in (15).

Let \(\kappa=\beta/(\beta+2)>0\). Once
\(r(T)>1\) and \(2|\eta|\le\beta\log r(T)\), the regular-profile
shift estimate gives

\[
\kappa p(T)\frac{L(T)}{T}
 \le p(T)-p(r(T)).
\tag{16}
\]

Its threshold follows from \(r(T)\to\infty\), including when
\(\eta<0\). Combining (15)–(16), whenever
\(p(T)-\log(TH)\ge0\), yields the exact finite deficit budget

\[
\boxed{
\kappa p(T)\bigl(p(T)-\log(TH)\bigr)^{10}
 \le c^{10}T\log\frac{T}{A(T)}.
}
\tag{17}
\]

This is `positive_cutoff_certificate_exact_deficit`. The proof raises
the nonnegative forcing deficit to the tenth power and then eliminates
\(L\) using (16); it makes no estimate of the unknown arithmetic error
from below.

Because \(b,\beta>0\), eventually \(2\log(TH)\le p(T)\).
Using \(A(T)\ge1\) therefore gives the simpler necessary budget

\[
\kappa p(T)^{11}\le(2c)^{10}T\log T.
\tag{18}
\]

After division by the positive constants and by \(T\log T\), this
bounds \(T^{11\beta-1}(\log T)^{11\eta-1}\) uniformly. A positive
power of \(T\) exceeds every fixed logarithmic power; if the power of
\(T\) is zero, a positive logarithmic power is also unbounded. This
proves (13). At \(\beta=\eta=1/11\), the exact equality
\(p(T)^{11}=b^{11}T\log T\) shows that (18) permits the endpoint pair when \(c>0\) and \(b>0\)
is sufficiently small. It does not establish admissibility for every value of \(b\), nor a
converse from the algebraic budget to a recurrence certificate.

The distinction between a certificate and the actual envelope is essential:
the identically zero envelope satisfies the positive recurrence (7), and
is bounded by every positive trial envelope. Consequently, recurrence (7)
alone cannot force a lower decay rate on its solutions. The theorem rules
out certificates (11)–(12) beyond (13); it does not rule out a faster
arithmetic estimate obtained by another argument. Numerical exponential
constants and absolute arithmetic optimality are not claimed.

## 6. Fixed subhalf damping and the signed-cancellation escape

The obstruction to fixed subhalf damping is separate from the cutoff
optimization. For any real profile \(P\) satisfying

\[
\frac{P(T)}T\longrightarrow0,
\]

any fixed \(\delta>0\), \(C>0\), and real \(a,k\) satisfy

\[
C\exp\!\bigl(\delta(T-k)-aP(T)\bigr)\longrightarrow+\infty.
\tag{19}
\]

The same conclusion holds after addition of any eventually nonnegative
remainder. These are statements about the supplied positive majorant,
not about the quantity it bounds. The assumption \(C>0\) excludes an
identically zero endpoint certificate.

Apply this to \(\Phi(T)=(T\log T)^{1/11}\), whose ratio to \(T\)
tends to zero. For every fixed \(\epsilon<1/2\) and every fixed real
band coefficient \(c\), one eventually has

\[
c\Phi(L_M)<(1/2-\epsilon)L_M.
\tag{20}
\]

Thus fixed \(\epsilon\) eventually lies outside the actual band (3).
Moreover, the terminal majorant arising in positive Abel transfer, with
its one-index displacement retained, satisfies

\[
C\exp\!\left[(1/2-\epsilon)\log(M+1)
 -a\Phi\bigl(6+\log(M+2)\bigr)\right]
 \longrightarrow+\infty.
\tag{21}
\]

The displacement causes only a bounded logarithmic-coordinate shift,
since \(\log(M+2)\le\log2+\log(M+1)\). Equations (20)–(21) apply
along every conductor sequence tending to infinity. The declarations are
`dampedMobius_loglog_stretched_fixed_subhalf_eventually_not_mem` and
`dampedMobius_loglog_stretched_positiveAbel_terminal_tendsto_atTop`.

The signed-cancellation escape is control of the expression before applying
the triangle inequality. To make this precise, write
\(e_n=\sum_{m<n}u_m-f\) and \(w_m=(m+1)^\delta\). The exact
centered Abel identity is

\[
\sum_{m=0}^{N}w_mu_m-f
 =w_Ne_{N+1}
  -\sum_{m=0}^{N-1}(w_{m+1}-w_m)e_{m+1}.
\tag{22}
\]

A concrete open escape target, for one fixed \(0<\epsilon<1/2\) and
\(\delta=1/2-\epsilon\), is a uniform bound on the norm of the
**complete signed right-hand side of (22)**. A Cauchy estimate for that
same expression would address natural-order norm convergence. Neither
estimate follows from the supplied endpoint majorant.

Positive Abel transfer bounds the two terms separately by their norms.
Their signed interaction is absent from that scalar budget. A sharper
estimate of (22), a signed Gram or bilinear estimate, or cancellation in
the original prime-error identity could avoid the certificate obstruction.
Such an estimate is not supplied by the necessity theorem. In particular,
divergence of (21) proves neither divergence of the actual Hilbert error
nor failure of finite energy at a fixed subhalf damping. The latter
question remains open here; no RH conclusion follows.

## Principal declarations and verification scope

| Declaration | Result |
|---|---|
| `R_stretched_squareLog_bound` | Global direct exponential prime-error provider |
| `M_log_bootstrap_finite_stretched` | Complete finite signed bootstrap |
| `mertensTailEnvelope_stretched_recurrence` | Uniform recurrence (7) for the actual Mertens tail supremum |
| `optimized_stretched_envelope_bound` | Uniform optimized real-variable barrier |
| `regular_trial_positive_cutoff_exponents_necessary` | Necessary beta/eta boundary under explicit positive certificate and regular-region assumptions |
| `positive_cutoff_certificate_exact_deficit` | Finite deficit budget retaining both logarithmic slack and the cutoff prefactor |
| `dampedMobius_loglog_stretched_positiveAbel_terminal_tendsto_atTop` | Fixed-subhalf divergence of the supplied positive Abel terminal majorant |
| `M_stretched_loglog_bound` | Unconditional real-argument Mertens estimate (1) |
| `M_shiftedLog_stretched_bound` | The same stronger provider exposed through `MertensShiftedGlobal` |
| `dampedMobius_half_loglog_stretched_providers` | Matched signed prefix and density-tail estimates |
| `dampedMobius_half_cutoffs_loglog_stretched_rate` | Complete endpoint norm estimate (2) |
| `dampedMobius_loglog_stretched_subhalf_band_package` | Shared constants for quantitative, sequential, uniform norm, and full energy assertions |

The successful combined check included all eighteen new modules in this
optimized chain. The preceding all-fixed-logarithmic family was verified
separately in `job_YyryxvBAnMHl5OXcK1YXaMuV8cv-UbxS` and remains exported.
The actual-module checkpoint is an additional import and dependency
validation, not a replacement for these theorem and axiom checks.

The complete proof uses the repository's checked MediumPNT compatibility
provider and existing finite identities. It introduces no new arithmetic
hypothesis, `sorry`, `admit`, project-local axiom, or unsafe declaration.
No mathematical novelty or absolute optimality claim is made.
