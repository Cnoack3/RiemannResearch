# Normalized exact heads and full squarefree support

Source: the user's squarefree Ramanujan, nonzero-head, and normalized-energy
requests, continued on 30 October 2026. The fresh-prime support argument below
is an independently developed simplification of the earlier coprime-count
perturbation. No mathematical novelty claim is made.

## Established construction

Write \(g_d(n)=(n\bmod d)/d\) and
\(B_q=\sum_{d\mid q}\mu(q/d)d\,g_d\). The existing
Pareto.ramanujanPacket_prefix proves
\(B_q(n)=-\sum_{m=1}^{n}c_q(m)\) for \(q>1\); QRamanujanPackets
identifies these sequences with their actual complete-Q Hilbert vectors.

The new squarefree_span_eq_packets identifies the finite squarefree residue
span with the finite squarefree packet span. All coefficients below are in
finite sums over distinct natural-number conductors.

For a prime \(p\nmid q\),
\[
 B_q(n)+B_{pq}(n)=p B_q(\lfloor n/p\rfloor).
\]
Thus this direction has zero head for \(n<p\). Given a finite packet
representation \(F=\sum_{q\in S}b_qB_q\), choose \(p>H\) and
\(p>\max S\). Both \(q\) and \(pq\) are squarefree, and the two conductor
sets are disjoint. For sufficiently small \(t>0\),
\[
 A=F+t\sum_{q\in S}(B_q+B_{pq})
   =\sum_{q\in S}(b_q+t)B_q+\sum_{q\in S}tB_{pq}.
\]
Finitely many forbidden values are avoided, so every displayed coefficient
is nonzero. Also \(\|A-F\|_Q<\varepsilon\), with any prescribed
\(\varepsilon>0\), and all coordinates through \(H\) are unchanged.
Zero coefficients can first extend \(S\) to contain any finite requested
set of squarefree conductors.

The exact signed energy is retained:
\[
 \|F+tG\|^2=\|F\|^2+2t\langle F,G\rangle+t^2\|G\|^2.
\]

QRamanujanFullSupport.full_support_sequence applies this construction at
every stage. Each squarefree \(q\ge2\) has a nonzero coefficient at **every**
stage \(j\ge q\). This is actual support, not a zero-padded enumeration.

QSquarefreeFullSupportHeads.exists_sublinear_full_support_heads supplies
an unconditional cofinal family with head constant exactly one:
\[
 A_j(n)=1\quad(1\le n\le H_j),\qquad
 \|A_j\|_Q^2/H_j\longrightarrow0.
\]
Here \(H_j+1\) is prime. The proof perturbs the existing prime-anchored
Möbius vector by less than \(1/(j+1)\). It also supplies, for every fixed
integer \(k\ge0\), a constant \(C_k\ge0\) such that eventually
\[
 \|A_j\|_Q^2\le \frac{12}{\zeta(2)}+2+
       C_k\frac{H_j}{(6+\log H_j)^k}.
\]
Thus \(c_j=1\) is available, and in particular its liminf is one. The
remaining obstacle is energy growth, not nonzero head constants or support.

## Exact spectral identity

Put
\[
 s_N=\sum_{d=1}^N\frac{\mu(d)}d,\qquad
 D_N(s)=\sum_{d=1}^N\mu(d)d^{-s},\qquad
 Z_N(s)=D_N(s)-(N+1)s_N(N+1)^{-s}.
\]
For the actual canonical corrected Möbius vector \(T_N\), with \(N>0\),
CanonicalMobiusBoundaryEnergy proves ordinary convergent Mellin linearity
throughout \(\Re s>0\), then the full boundary identity
\[
 \|T_N\|_P^2=\frac1{2\pi}\int_{\mathbb R}
   \frac{|\zeta(\tfrac12+it)|^2}{\tfrac14+t^2}
   |Z_N(\tfrac12+it)|^2\,dt.
\]
The normalized identity divides both sides by \(N\). All signed Möbius
coefficients and the anchor remain inside the square. The boundary integral
and Plancherel theorem are proved providers, not extra analytic hypotheses.

QMobiusBoundaryEnergy.exactHead_boundary_energy transports this to the
actual Q space with the exact measure correction:
\[
 \zeta(2)\|T_N\|_Q^2=\|T_N\|_P^2+
    \operatorname{metricCorrection}(T_N).
\]
The nonnegative correction is the repository's existing complete
Radon--Nikodym correction. It must not be discarded from an asserted equality.

## Actual affine optimizer

QSquarefreeOptimizerEnergy retains the exact Pythagorean equality
\[
 \|1-T_H\|_Q^2
 =\operatorname{minimumError}(H,L,r)+\|T_H-\operatorname{optimizer}(H,L,r)\|_Q^2.
\]
The finite-stage hypotheses explicitly require feasibility and that the
stage contain the trial's anchor \(H+1\) and its low squarefree conductors.
The optimizer minimizes residual energy, not vector norm.

The complete sublinear, stretched-exponential, and every-fixed-logarithmic-
saving bounds transfer to these actual minima. For squarefree \(L\), the
stage is legal in the squarefree span. No additional analytic assumption
is used in this transfer.

## Conditional research reduction and open obligation

Analysis.NormalizedEnergy proves:

- Membership of a nonzero scalar multiple of a vector in a submodule is
  equivalent to membership of the vector itself. Merely having a nonempty
  intersection with the constant line says nothing, since it contains zero.
- \(\|c^{-1}F\|^2=\|F\|^2/|c|^2\).
- Bounded perturbations preserve sublinear and logarithmically defined
  subpolynomial energy.
- Subpolynomial vector energy implies subpolynomial residual energy.

QNormalizedExactHead proves RH from legal cofinal exact heads and
\[
 \frac{\log(1+\|F_j\|_Q^2/|c_j|^2)}{\log n_j}\longrightarrow0.
\]
The strengthened theorem needs only **eventual nonvanishing** of \(c_j\);
no positive liminf assumption is required. These are conditional research
reductions: the displayed normalized estimate is an explicit hypothesis.

**Open:** prove this \(n_j^{o(1)}\) normalized-energy estimate for an actual
legal cofinal family. The unconditional \(o(H_j)\) and fixed logarithmic
savings proved here do not establish it. Neither RH nor constant closure
is claimed unconditionally.

## Modules

- Analysis/NormalizedEnergy.lean
- Analysis/FullSupportPerturbation.lean
- RH/QNormalizedExactHead.lean
- RH/QRamanujanFullSupport.lean
- RH/QSquarefreeFullSupportHeads.lean
- RH/CanonicalMobiusBoundaryEnergy.lean
- RH/QMobiusBoundaryEnergy.lean
- RH/QSquarefreeOptimizerEnergy.lean

The publication checkpoint is responsible for checking the integrated
aggregate and changed modules. Successful snippets alone are not the final
publication certificate.
