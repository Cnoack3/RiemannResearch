# Q canonical-window capacity recurrence — 15 October 2026

The three Lean modules in this record extend commit
`8756bae8ab296c69bc404f49e3c932e1609b858d` with the actual contiguous-window
capacity recurrence, its complete Schur denominator, and exact quotient-cell
arithmetic. The repaired proof scripts passed targeted Lean-server checking
on 16 October 2026. The verification record below identifies the checks.

The record distinguishes formalized declarations from further informal
research identities. The common growing-head positive capacity threshold
remains **Open**; the conditional RH consumer keeps it as an explicit
hypothesis. Finite positivity and arbitrarily late strict gains do not
supply that threshold.

## Definitions and the complete exact recurrence

Let
\[
 z=\zeta(2),\qquad P(n)=\frac1{n(n+1)},\qquad Q(n)=\frac1{zn^2}
 \quad(n\ge1),
\]
and let the physical residue atom be \(g_d(n)=(n\bmod d)/d\). Retain the
entire boundary term in the canonical approximant:
\[
 S_Y=\sum_{d=1}^{Y}\frac{\mu(d)}d,\qquad
 F_Y=-\sum_{d=1}^{Y}\mu(d)g_d+(Y+1)S_Yg_{Y+1},\qquad r_Y=1-F_Y.
\]
The existing implementation proves \(r_Y(n)=0\) for \(1\le n\le Y\).
All physical sums below start at positive coordinates; the Lean encoding has
a zero weight at its anchor coordinate.

Fix \(1\le N\le M\). Write \(R a=\sum_{k=N}^{M}a_kr_k\),
\(G=R^*R\), \(u=G^{-1}\mathbf1\), \(h=Ru\), and
\(m_Q(N,M)=\mathbf1^\mathsf Tu=\|h\|_Q^2\).
The existing Q-window module constructs this inverse and proves independence.
For the next vector \(f=r_{M+1}\), set
\[
 g_k=\langle r_k,f\rangle_Q,
 \qquad c=G^{-1}g,\qquad s=f-Rc.
\]
The generic `screeningCoeff` solves exactly these equations; independence
identifies it with the actual inverse solution. Define
\[
 \delta_{N,M}=1-\langle f,h\rangle_Q
             =1-\sum_{k=N}^{M}u_kg_k
             =1-\sum_{k=N}^{M}c_k,
\]
\[
 \sigma_{N,M}=\|s\|_Q^2
             =\|f\|_Q^2-\sum_{k=N}^{M}c_kg_k
             =\|f\|_Q^2-g^\mathsf TG^{-1}g.
\]
All signs in these formulas are retained. In particular, no covariance is
replaced by its absolute value. The larger window is independent, so
\(\sigma_{N,M}>0\). The exact recurrence is
\[
 \boxed{m_Q(N,M+1)-m_Q(N,M)=\frac{\delta_{N,M}^2}{\sigma_{N,M}}.}
\]
It follows directly from the existing generic one-step theorem after constructing
the actual enlarged normal and proving equivalence of the two indexings.
Orthogonal screening also gives the exact equality
\[
 \|f\|_Q^2=\sigma_{N,M}+\|Rc\|_Q^2,
\]
and hence \(0<\sigma_{N,M}\le\|r_{M+1}\|_Q^2\).
The gain is strictly positive **if and only if** \(\delta_{N,M}\ne0\).
Independence alone does not prove this nonvanishing.

Every norm is the full infinite Hilbert energy. Explicitly,
\[
 \sigma_{N,M}=\sum_{n\ge1}\frac1{zn^2}
 \left(r_{M+1}(n)-\sum_{k=N}^{M}c_kr_k(n)\right)^2.
\]
There is no finite-period substitution or omitted infinite remainder.

## Telescoping and upper-cutoff selection

Put \(E_N=\|r_N\|_Q^2>0\). The diagonal window and the recurrence give
\[
 \boxed{m_Q(N,N+L)=\frac1{E_N}
       +\sum_{j=0}^{L-1}\frac{\delta_{N,N+j}^2}{\sigma_{N,N+j}}.}
\]
Thus a sufficient growing-head selection condition is: there exist \(c>0\)
and integers \(L(N)\ge0\) such that, for every \(N\ge1\),
\[
 \frac1{E_N}+\sum_{j<L(N)}
     \frac{\delta_{N,N+j}^2}{\sigma_{N,N+j}}\ge c.
\]
Then \(M(N)=N+L(N)\) satisfies the existing inverse-Gram RH consumer.
This is a **conditional research reduction**; its displayed common-threshold
hypothesis remains **Open**. It requires only a finite crossing for each head,
not divergent gains at every fixed head.

For any proposed threshold, the natural adaptive schedule is the first crossing
\[
 M_c(N)=N+\min\left\{L\ge0:
  E_N^{-1}+\sum_{j<L}\delta_{N,N+j}^2/\sigma_{N,N+j}\ge c\right\}.
\]
This is defined only when the set is nonempty. Monotonicity makes every larger
cutoff valid once a crossing has been certified. It does not prove that the
search terminates for every head. The present estimates do not justify a
fixed-width, fixed-ratio, dyadic, or other prescribed schedule uniformly in N.

## What arithmetic covariance actually controls

For a fixed old window, let
\[
 A_{N,M}=\sum_{k=N}^{M}|u_k|(1+2k),\qquad
 e_Q(T)=\frac{\|r_T\|_Q^2}{T+1},\qquad
 \kappa_T=\frac{1+1/(T+1)}z.
\]
The existing physical bound \(|r_k(n)|\le1+2k\) gives
\(|h(n)|\le A_{N,M}\). For an arbitrary added cutoff T, the sharper existing
Q covariance estimate proves
\[
 \boxed{|1-\delta_{N,M}(T)|^2
   =|\langle r_T,h\rangle_Q|^2
   \le\kappa_T A_{N,M}^2 e_Q(T).}
\]
The checked PNT provider and Q/P comparison imply \(e_Q(T)\to0\).
Consequently, **with N and M fixed**, \(\delta_{N,M}(T)\to1\).
Each entry of the cross vector \(g(T)\) also tends to zero, so finite matrix
algebra gives \(g(T)^\mathsf TG^{-1}g(T)\to0\). This last fixed-window Schur
correction limit is an informal consequence here, not a declaration in the patch.

A further unconditional consequence, formalized as `exists_larger_normalMass`, is
\[
 \boxed{\forall M\ge N\ge1,\ \exists L>M:\ m_Q(N,L)>m_Q(N,M).}
\]
Indeed the existing generic defect bound for the larger window gives
\[
 \delta_{N,M}(L)^2\le\|r_L\|_Q^2
                  [m_Q(N,L)-m_Q(N,M)].
\]
For sufficiently large L the left side is positive, so the bracket is positive.
Equivalently there are strictly positive contiguous gains arbitrarily late at
each fixed head. This does not show their sum is unbounded.

For a quantitative immediate step, the finite condition
\[
 \kappa_{M+1} A_{N,M}^2 e_Q(M+1)\le\frac14
\]
implies \(\delta_{N,M}\ge1/2\), hence
\[
 \boxed{m_Q(N,M+1)-m_Q(N,M)
          \ge\frac1{4\|r_{M+1}\|_Q^2}.}
\]
The theorem `step_gain_lower_of_amplitude_budget` keeps this condition
explicit. No existing provider controls the actual moving inverse-Gram
normal amplitude \(A_{N,M}\) uniformly. Decay for a fixed test, bounded-norm
coefficient arrays, or one slowly growing column block does not supply that
missing control for the changing normal vectors.

Even strict increase at every step would not settle the growing-head question.
For example the abstract positive array
\(a(N,M)=N^{-1}(1-2^{-(M-N+1)})\) has strictly positive increments, while
\(\sup_{M\ge N}a(N,M)=1/N\to0\). This illustrates the logical gap only;
it is not a model asserted for the actual Q Gram matrices.

## Quotient cells identify the signed source inside the arithmetic profile

Let \(\mathcal M(Y)=\sum_{d\le Y}\mu(d)\),
\(b_Y=(Y+1)S_Y-\mathcal M(Y)\), and
\(H_q(n)=\sum_{j=1}^{q}\mathcal M(\lfloor n/j\rfloor)\).
The existing exact identity is
\[
 r_Y(n)=H_q(n)+q b_Y,\qquad q=\lfloor n/(Y+1)\rfloor.
\]
On a finite common quotient cell C for every old cutoff and T, screening gives
\[
 \boxed{s(n)=\delta_{N,M}(T) H_q(n)+q B,\qquad
 B=b_T-\sum_{k=N}^{M}c_k b_k.}
\]
Thus the same signed source that enters the numerator is the coefficient
of the common Mertens profile in the denominator. This identity, and the
complete Q cell-energy-plus-complement equality, are formalized
in `QCanonicalWindowSchurArithmetic.lean`.

For clarity, completing the finite square further gives the informal identity
\[
 \sigma=\delta^2 V_Q(C,q)
    +W_Q(C)(\delta\bar H_Q+qB)^2
    +\sum_{n\notin C}Q(n)s(n)^2,
\]
where \(W_Q=\sum_CQ(n)\), \(\bar H_Q=W_Q^{-1}\sum_CQ(n)H_q(n)\), and
\(V_Q=\sum_CQ(n)(H_q(n)-\bar H_Q)^2\), for a nonempty C.
All three terms remain present. The variance term alone bounds the denominator
from below and therefore bounds a nonzero step gain from above. A gain lower
bound needs an **upper** bound on the full denominator, including the mean and
the infinite complement. Common cells may also be empty when cutoffs separate.
The variance completion is explained here; it is not separately formalized by
the formalized finite-cell energy equality.

## Finite-energy estimates give usable certificates, with a uniformity gap

For any screened coefficient array c, include its new-vector coefficient 1:
\[
 D=(1+2T)^2+\sum_{k=N}^{M}(1+2k)^2,\qquad
 C_c=1+\sum_{k=N}^{M}c_k^2.
\]
The same Cauchy--Schwarz amplitude argument used by the existing truncated
envelope gives \(|s(n)|^2\le D C_c\). First retain the exact split, for R>=1:
\[
 \sigma=\sum_{1\le n<R}Q(n)s(n)^2+\sum_{n\ge R}Q(n)s(n)^2.
\]
Since \(zQ(n)=(1+1/n)P(n)\) and \(\sum_{n\ge R}P(n)=1/R\),
\[
 \boxed{\sigma\le U_R:=\sum_{1\le n<R}Q(n)s(n)^2
        +\frac{1+1/R}{zR}\,D C_c.}
\]
This is a finite complete-tail upper certificate, with all signed cross terms
inside its retained finite square. Its derivation is informal here; the Lean development
formalizes the exact full-energy split, not this additional tail inequality.
An arbitrary trial screening array may replace the true c to bound sigma
from above, by orthogonal minimality; it must not replace the true delta in
the gain numerator. For fixed data the displayed allowance tends to zero as
R grows. The existing `CanonicalMobiusTruncatedCeiling` construction gives a
related certified primal approach: optimize a finite signed energy with a
diagonal tail allowance, then transfer the complete energy to Q.

For research, combine a certified source lower bound \(|\delta|\ge\eta>0\)
and \(\sigma\le U_R\) to obtain a gain lower bound \(\eta^2/U_R\).
Alternatively certify a bounded-energy normalized signed average directly;
it yields a mass lower bound through the already constructed actual minimum.
Both approaches permit adaptive cutoff search. Neither presently supplies
one common positive mass threshold for every growing head. Large screening
coefficients and small Gram eigenvalues can make the tail allowance expensive.

## Formalized modules and server verification

- `Analysis/FiniteGramSchurBounds.lean`: screening energy upper bound and strict
  positivity from independence of the enlarged family.
- `RH/QCanonicalWindowCapacity.lean`: actual mass, exact recurrence, telescoping,
  strict-gain criterion, explicit source control, no terminal plateau, a
  quantitative step certificate, and the conditional cumulative-gain RH consumer.
- `RH/QCanonicalWindowSchurArithmetic.lean`: complete weighted Schur energy,
  exact common-cell screened profile, and its full infinite complement.
- The aggregate exports all three modules. The theorem catalog distinguishes
  the established finite and fixed-head results from the conditional RH reduction.

The targeted server file check
`job_aAu-Q8DwQgSvzkHlY-cVLrq-5fU-dMvx` succeeded with exit code 0 and
`verified: true` on the arithmetic module and its dependency closure.
The axiom/type inspection `job_1uRUl6cmrVeZfrH5AxUqcjUAqV63F7BZ` likewise
succeeded. Because its returned log was bounded, the first 15 axiom reports
were also inspected through `job_y9foqQSHwAEhb7MDrpbOUYoHkTMcmVhV`.
Across all 29 public theorem declarations the reported axioms are only
`propext`, `Classical.choice`, and `Quot.sound`. Exact types were inspected
for the recurrence, the absence of a terminal plateau, the complete cell
energy, and the conditional RH consumer. These checks do not discharge
hypotheses appearing in those types.

Publication uses the final project checkpoint with push enabled, including
source audit and aggregate/changed-module validation. When integration with
newer main is required, that integrated source must also pass the server gate.
No hosted CI or direct unverified push is used.

**Open:** the growing-head common-threshold arithmetic provider. No RH proof,
uniform normal-amplitude estimate, or successful upper-cutoff schedule is claimed.
