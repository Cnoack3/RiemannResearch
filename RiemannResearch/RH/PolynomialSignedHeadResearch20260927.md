# Polynomial signed-head continuation and literature audit

Continuation of Cnoack3/RiemannResearch `41c5e8f48cfd3acfeae428a163f47185037f81a3`,
which continued `d4e06595e09075250bc2c2c49399dcd0b3cd6767`.

## Outcome and scope

This continuation does **not** prove RH or establish finite energy at any
new fixed damping below one half. It proves quantitative, unconditional
approximation after signed cancellation, an exact explicit-cutoff criterion,
and a signed-vector Abel transfer. All substantive missing arithmetic
bounds remain hypotheses. The completed half endpoint and the sharp
power/log majorant obstruction are reused.

## A concrete signed arithmetic hypothesis

Write

\[
w_n=\frac1{n(n+1)},\quad
c_\varepsilon=\Re\frac1{\zeta(1+\varepsilon)},\quad
g_\varepsilon(n)=\sum_{d\le n}\mu(d)d^{-\varepsilon}
\lfloor n/d\rfloor-nc_\varepsilon.
\]

The zero index has weight zero. Let the actual residue vector be
\(a_{\varepsilon,d}(n)=\mu(d)d^{-1-\varepsilon}(n\bmod d)\), for \(d\ge1\),
and \(F_{\varepsilon,M}=-\sum_{d\le M}a_{\varepsilon,d}\). Define the signed
off-diagonal head sum, including both orientations, by

\[
O_\varepsilon(H,M)=
\sum_{\substack{1\le d,e\le M\\d\ne e}}
\sum_{n<H}w_n a_{\varepsilon,d}(n)a_{\varepsilon,e}(n).
\]

For every \(\varepsilon>0\) and integer \(k\) with \(2k\varepsilon\ge1\),
the new checked criterion is

\[
\sum_n w_ng_\varepsilon(n)^2<\infty
\quad\Longleftrightarrow\quad
\exists B\in\mathbb R\;\forall H\in\mathbb N,
O_\varepsilon\bigl(H,(H+1)^k\bigr)\le B.
\]

The constant may depend on epsilon and k; it may not depend on H.
This fixes a single explicit conductor cutoff for each physical head,
replacing the previous eventual-in-M condition.

The completely numerical remaining hypothesis sufficient for RH is

\[
\boxed{\quad\forall j\in\mathbb N\;\exists B_j\in\mathbb R\;\forall H\in\mathbb N,
O_{1/(j+3)}\bigl(H,(H+1)^{j+3}\bigr)\le B_j.\quad}
\]

Every damping here is below one half and tends to zero. The bounds need
not be uniform in j. The theorem with this hypothesis is a conditional RH
reduction, not an unconditional RH proof.

## Why the approximation is unconditional

For \(M\ge H\) the existing exact identity sums the signed tail first:

\[
\sum_{n<H}w_n\bigl(F_{\varepsilon,M}(n)-g_\varepsilon(n)\bigr)^2
=\left(c_\varepsilon-\sum_{d\le M}\frac{\mu(d)}{d^{1+\varepsilon}}\right)^2
\sum_{n<H}\frac n{n+1}.
\]

The new scalar tail estimate and quantitative head estimate are

\[
\left|c_\varepsilon-\sum_{d\le M}\frac{\mu(d)}{d^{1+\varepsilon}}\right|
\le\frac{M^{-\varepsilon}}\varepsilon,
\qquad
E_H(F_{\varepsilon,M}-g_\varepsilon)
\le\frac{HM^{-2\varepsilon}}{\varepsilon^2}.
\]

The scalar estimate uses absolute convergence of the reciprocal-density
series and the proved integral-test p-series tail bound. It does not assume
absolute convergence of the Hilbert-vector series. For \(M=(H+1)^k\),
\(HM^{-2\varepsilon}\le H/(H+1)\le1\). Thus the approximation error is
uniformly bounded at every positive damping. Comparing the two energies
costs a factor two and an additive \(2/\varepsilon^2\). The previously
proved diagonal budget handles the diagonal; only the signed off-diagonal
bound is left open.

This improves the quantifier and cutoff bookkeeping. It does not estimate
the comparable-conductor portion of the signed Gram sum.

## Signed-vector Abel bridge

`Analysis/SignedPowerDampingAbel` proves the exact finite summation-by-parts
identity for Banach-space vectors. If \(S_N=\sum_{n<N}u_n\), convergence
follows from summability of
\(|b_n-b_{n+1}|\|S_{n+1}\|\) and decay of the boundary term
\(b_NS_{N+1}\). Norms are taken after the signed prefixes are formed.

For power damping, \(\|S_N\|\le CN^\theta\) and
\(\varepsilon>\max(\theta,0)\) imply convergence of the naturally ordered
partial sums of \(n^{-\varepsilon}u_n\). This is ordered convergence,
not a claim of unconditional `Summable` for the original vector series.
`RH/DampedMobiusSignedAbelGrowth` identifies the actual arithmetic Hilbert
limit and derives centered finite energy from a bound on the complete raw
signed residue norm. That raw growth bound is **Open** in the range needed
for new subhalf damping. The repository's unconditional sublinear raw
budget from PNT does not provide a fixed power saving.

## Primary-source checks

- [Conrey–Myerson, *On the Balazard–Saias criterion*, Theorem 1 and Remark 1](https://arxiv.org/pdf/math/0002254):
  signed logarithmically smoothed fractional-part sums converge uniformly.
  The authors explicitly retain an uncontrolled shrinking-boundary square
  integral, equal to a smoothed Möbius-prefix square divided by N. Uniform
  convergence alone therefore does not provide the needed weighted energy.
- [Maier–Rassias, *Estimates of sums related to the Nyman–Beurling criterion*, Theorem 1.1 and Corollary 1.2](https://arxiv.org/pdf/1705.09921):
  the parameter constraints include \(B\ge k^{2\delta}\) with fixed
  \(\delta>0\), and the sum is over \(h\asymp Bk\). Thus it reaches
  \(h\ge k^{1+2\delta}\), while the corollary retains the cone
  \(h\le k^{1+\eta}\). This is useful separated-scale cancellation,
  not a bound on the whole signed Gram sum.
- [Maier–Rassias, *Explicit estimates*, Theorem 2.1](https://arxiv.org/pdf/1806.05070):
  the explicit power-saving theorem assumes \(D\ge2\) for numerators of
  size \(k^D\). It does not remove the comparable-conductor gap.
- [Bettin–Conrey–Farmer, *An optimal choice of Dirichlet polynomials*, Theorem 1](https://arxiv.org/pdf/1211.5191):
  the asymptotic assumes RH and a bound on inverse zeta-derivative moments.
  Its unconditional residue formula retains the zero contributions.
- [Burnol, Section 4](https://arxiv.org/pdf/math/0202166):
  finite arithmetic energy at positive dampings approaching zero implies
  RH. Spectral square-integrability of a symmetric shifted quotient does
  not itself identify its inverse transform with the required arithmetic
  function; that identification is an essential additional step.

These papers were audited for available inputs, not inserted as Lean
axioms. The new formal proofs use existing project theorems and Mathlib
summation, power, derivative, and norm estimates.

## Strength and remaining obligations

- **Established:** scalar and entire-head approximation bounds for every
  positive damping; explicit polynomial cutoff; exact fixed-damping
  criterion; conditional vector Abel transfer.
- **Open:** one uniform signed-head bound at a specified fixed
  \(0<\varepsilon_0<1/2\), equivalently the actual finite-energy membership
  displayed above. No RH equivalence for one fixed epsilon is claimed.
- **RH-strength:** the displayed family at \(1/(j+3)\) implies RH by the
  kernel-verified Burnol reduction. Its hypothesis has not been discharged.
- **Already established obstruction:** an off-line zero prevents actual
  finite energy for all sufficiently small positive dampings. Fixed-damping
  zero propagation permits common shifted zeros; it must not be silently
  strengthened to a zero-free strip.

Combined kernel check `job_RQVZ7s-SAUrF5oKdgVrbFesxVJNhyoah` returned
`exit_code=0`, `verified=true`, without warnings. All five principal
dependency reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. The publication checkpoint additionally checks the actual
separate module imports. No project-specific axiom or proof placeholder
is used. Axiom reports do not discharge hypotheses in theorem types.
