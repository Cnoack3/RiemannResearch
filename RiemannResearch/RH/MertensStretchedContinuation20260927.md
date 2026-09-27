# Direct MediumPNT bootstrap and the optimized moving subhalf band

Continuation of `ba20efab4f7d02ff2ed484f1de9b78909c74e009`.

**Verification record:** the complete arithmetic, analytic, endpoint, and
moving-band assembly passed serialized Lean job
`job_TBpHy99-BdxFXakNU5xioVEaL215xY4Z` with `exit_code=0` and
`verified=true`. The principal Mertens, endpoint, and shared moving-band
package declarations each depend only on `propext`, `Classical.choice`,
and `Quot.sound`. Publication additionally validates the actual modules
and affected reverse dependencies through the final project checkpoint.

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

## 5. What “strongest” means here

An intermediate stage of this continuation established every fixed logarithmic Mertens and
endpoint exponent and every fixed coefficient of the
\(\log\log M/\log M\) band. Those results remain useful, but (1)–(3)
are stronger: they control one uniform stretched-exponential profile.

There is a clear optimization boundary for regular trial profiles in the
**positive recurrence (7)**. For a trial envelope
\(\exp[-bT^\beta(\log T)^\eta]\), the prime forcing requires a cutoff
with approximate scale at least
\(T^{10\beta}(\log T)^{10\eta}\). The delayed-envelope term requires
the cutoff to fit within approximate scale
\(T^{1-\beta}(\log T)^{1-\eta}\). Comparing powers suggests

\[
\beta\le1/11,
\qquad \eta\le1/11\text{ when }\beta=1/11.
\]

The profile used above reaches that exponent pair. This comparison is
documented optimization analysis, **not a kernel-verified lower bound or
an impossibility theorem**. It does not establish absolute optimality of
the signed arithmetic identity, of stronger cancellation estimates, or
of other consequences of MediumPNT. Numerical exponential constants have
not been optimized.

## Principal declarations and verification scope

| Declaration | Result |
|---|---|
| `R_stretched_squareLog_bound` | Global direct exponential prime-error provider |
| `M_log_bootstrap_finite_stretched` | Complete finite signed bootstrap |
| `mertensTailEnvelope_stretched_recurrence` | Uniform recurrence (7) for the actual Mertens tail supremum |
| `optimized_stretched_envelope_bound` | Uniform optimized real-variable barrier |
| `M_stretched_loglog_bound` | Unconditional real-argument Mertens estimate (1) |
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
