# Landau endpoint support and centered hyperbolic frames

Base commit: 6c74acbd2a68d5d36f5d8d4e9a86a88ea3304c3d.
Research date: 2026-10-05.

## Exact signed object and unconditional endpoint

The actual multiplicity-weighted operator remains exactly
E_d(T) = H_d(T) - I + T*A_d/(2*pi*N(T)).
A_d includes every integer frequency and every prime-power divisibility
interaction, including pairs involving composite conductors. Its negative
main contribution has not been omitted or replaced by an absolute majorant.

Write Y=T+3 and L=log Y. The existing sufficient fixed-c=2 contour provider
gives a numerator C[d^(7/2)+d^(5/2)*L^2+d^2*L].
The original actual zero-count theorem yields, eventually,
N(T) >= (1/(64*pi))*Y*L.
For every fixed a and log d <= a+(2/7)*L, the exact endpoint majorant is

    matrixEnvelope(L,a+2L/7)/L
      = exp(7a/2)/L
        + exp(5a/2)*L*exp(-2L/7)
        + exp(2a)*exp(-3L/7).

All three terms tend to zero. Thus d(T)=O(T^(2/7)) is admissible for
unconditional signed Landau residual convergence, including the endpoint.
This strengthens the previous square-root-log-support theorem.
It proves neither H-I -> 0 at this polynomial scale nor a phase frame:
the arithmetic main term remains. It says nothing by itself about the
completely screened physical residue Gram inverse or RH.

## Complete finite centered hyperbolic development

For a finite rectangular analysis operator V, displacement diagonal A and
centered frequency diagonal D with |a_j|<=delta and |D_nn|<=b, the exact
cosh kernel has the finite factorization H=C* C-S* S.
The quadratic identity retains the full negative sinh norm square.

The centered even operator series is

    Q = sum_{j>=1} A^(2j) V (D^(2j)-b^(2j)I/2)/(2j)!.

The diagonal half-centering inequality and full series summability give

    ||Q|| <= (cosh(delta*b)-1)*||V||/2.

The exact scalar row series is cosh(a*x)-(1+cosh(a*b))/2.
For C=K V+Q, ||K||<=k, ||Q||<=q and
h_-||f||^2 <= ||Cf||^2-||Sf||^2, the checked lower transfer is

    ||Vf|| >= ((sqrt(h_-)-q)/k)||f||.

Analysis/CenteredHyperbolicRows.lean realizes the rectangular operators in
the Euclidean Hilbert norm, proves C=K V+Q for these concrete rows, identifies
the concrete Q with the full operator series, and supplies both operator
bounds from finite displacement and frequency bounds. Its
finite_centered_frame_lower theorem therefore requires only the stated
hyperbolic-form lower bound in addition to those finite bounds.
No application supplies a zeta density estimate merely by defining C or Q.
Phase-row signs must match the existing complex quadratic convention when
specializing generic kernels to the actual zero Gram.

The follow-up [actual hyperbolic lower-bound analysis](ActualHyperbolicLowerBounds20261005.md)
now discharges the FULL form input using the complete arithmetic main matrix:
every h<1-theta is eventually valid for theta<=2/7, so every h<5/7 holds at
the existing endpoint. Its actual-row identity keeps the negative sinh square,
every multiplicity and the original complex sign convention. The shrinking
good-zero mask is distinguished explicitly: H_good=H-H_bad, and its concrete
centered-frame specialization consumes the one-sided signed bad-row provider.
The finite rank-two copy budget is proved; its required asymptotic smallness
and the closed harmonic/density specialization are separately classified.

The exact improved gap is z<7/5:
2-z^2>0 and (z-1)/2 < sqrt(2-z^2).
For z=cosh(3c^2/8), Lean proves the exact equivalence for c>=0:
cosh(3c^2/8)<7/5 iff c<centeredSupportConstant, where
centeredSupportConstant=sqrt((8/3)*arcosh(7/5)).
Its positivity and centered_support_gap are also proved.
Wolfram checked the decimal 1.5205391381485407013... and exact identities.
The decimal is not an oracle or a hypothesis in the Lean proof.

## Analytic density audit and remaining provider

The primary analytic source is Chourasiya--Simonic,
"An explicit form of Ingham's zero density estimate", arXiv:2507.15184v2,
Corollary 1 and Table 1:
https://arxiv.org/html/2507.15184v2 .

Its estimate is uniform on closed sigma intervals and explicitly covers
sigma-1/2 <= 0.28/log T. Thus shrinking near-line cutoffs are valid.
With v(s)=4s/(3-2s), the exact normalized power identity is

    T^(1-v(s))*L^(3-v(s))
      = T*L^3*exp(-(log T+log L)*v(s)).

The scalar Lean identity has no density conclusion. The source corollary
uses established finite-height zero verification; one may retain
N(sigma,H) from its Theorem 1 instead of assuming that finite certificate,
then absorb this fixed initial count only when justified eventually.
The complete additive remainder is still E*(cosh(ell/2)-1) in the
existing finite-tail transfer. No endpoint or negative companion term has
been discarded.

Open in Lean: the actual exponential density provider, including its
Littlewood/Gabriel/mollifier/fourth-moment analytic inputs. Consequently
the actual-zero unconditional frame theorem at the improved support
constant remains a separate application obligation. The physical Pareto
sampling transfer also remains open. None is asserted by source citation.

## A further paper-level Landau strengthening

The existing nonmaxed scalar estimate has positive entry envelopes
A_nm=n^(5/2)/m^(3/2), B_nm=(n/m)^(3/2), and
D_nm=1+1/log(n/m) for n>m, reflected symmetrically.
Its residual entry is bounded by C(A_nm+L^2 B_nm+L D_nm)/N(T).

For d>=2, the symmetric Hilbert--Schmidt norms satisfy
||A||_HS<=2d^3 and ||B||_HS<=2d^2. Indeed,
sum_{m>=1}m^(-3)<=2, sum_{n<=d}n^5<=d^6 and
sum_{n<=d}n^3<=d^4. Also log(n/m)>=(n-m)/n gives
D_nm<=2d/|n-m|, so its Schur row bound is <=4d*H_d.
One can split the actual entry into its three positive-envelope
proportions (with zero in the zero-denominator case); applying these
three operator bounds yields

    ||E_d(T)|| <= (C/N(T))*(2d^3+2d^2 L^2+4d H_d L).

This permits d=O(T^(1/3)) at paper-proof level using N(T)>>T log T.
The new finite-envelope/HS/Schur assembly is not included among the
Lean-verified endpoint declarations in this change.

## Sources and verification

Gonek, "A Formula of Landau and Mean Values of zeta(s)" (1985), Theorem 1:
https://www.sas.rochester.edu/mth/people/faculty/gonek-steve/assets/pdf/8-landau-form.pdf .
Ford--Zaharescu, "On the distribution of imaginary parts of zeros of the
Riemann zeta function", Lemmas 1--2:
https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf .
These support the contour and zero-density strategies, not new Lean axioms.

Isolated checks test exact declarations; their successful axiom reports
list only propext, Classical.choice and Quot.sound. Failed exploratory
snippets are not evidence of a verified theorem. Publication is accepted
only after the final checkpoint checks the actual project modules and
their affected local dependents. This record does not assert an unrelated
full project rebuild or completion of the actual density provider.
