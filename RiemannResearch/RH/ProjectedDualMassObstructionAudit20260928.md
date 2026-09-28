# Coefficient-mass provider: obstruction audit — 28 September 2026

Continuation of commit 7438d671055426109ae12271db4f8151257c18d3, responding to
“Prove Bound(*) or any other sufficient condition.”

## Result and formal status

No unconditional sufficient condition for RH has been proved. RH remains **Open**.

There is now a mathematical obstruction to the proposed strict-margin
coefficient-mass condition: using a critical-line zeta zero, at least one of
the fixed columns d=2 or d=3 cannot have the requested cofinal bound for
any b<a. This argument is written out below. It rules out the global
concentration budget as well, since that budget bounds the actual mass.

**The complete obstruction is not a Lean theorem in this checkpoint.**
The finite projection estimates and Schur asymptotics below are
kernel-checked. The critical-line cutoff inequality, the Mellin witness
assembly, the profile comparison under n -> floor((n+1)/4)-1, and existence
of a critical zero have not been assembled/formalized here. None is
introduced as an axiom, and none is silently used by a Lean declaration.

The earlier implications “mass bound implies residual zero” remain correct
conditional theorems. A sufficient condition can be too strong to hold.
This audit changes the assessment of the proposed provider, not the
validity of those implications. The direct signed physical-tail criterion
is not refuted by the argument.

## Notation

V_n=span(g_2,...,g_(n+1)), P_n its orthogonal projection,
h_d=coefficientRiesz d, p_(n,d)=P_n h_d, q_(n,d)=h_d-p_(n,d), and
B_(n,d)=projectedDualCoefficientMass n d.

The physical norm is

    ||f||^2 = sum_(j>=1) f(j)^2/[j(j+1)].

Write T_N=hilbertOne-canonicalMobiusHilbert N. The checked arithmetic
provider gives a>0, C>=0 and eventually

    ||T_N||^2 <= 8+C N exp(-a Phi(N)),
    Phi(N)=((6+log N) log(6+log N))^(1/11).

D_m f(j)=m f(floor(j/m)) is the repository's scaled integer dilation.
In particular ||D_m f||^2=m ||f||^2.

## Established Lean: actual finite dual approximation

Module: RH/ProjectedDualProjectionError.lean.

The new declarations prove the following without RH or an asymptotic
column-growth assumption.

1. canonicalMobiusHilbert_dilation_mem_finiteSpace:

       m(N+1)<=n+1  ==>  D_m canonicalMobiusHilbert N belongs to V_n.

   This follows from D_m g_k=m g_(mk)-(m/k)g_m. The m=1 case is included.

2. projectedDualTail_any_cutoff_le_mass:

       ||tail_N(P_n h_d)||^2 <= B_(n,d)^2/(N+1).

   The cutoff N is independent of stage n.

3. projectedDualError_tail_le_mass:

       0<d<=N  ==>  ||tail_N(q_(n,d))||^2 <= B_(n,d)^2/(N+1).

   Here tail_N(h_d)=0 exactly; no support outside the cutoff is discarded.

4. projectedDualError_dilation_pairing_sq_le:

       |<q_(n,d),D_m 1>|^2
         <= m B_(n,d)^2 ||T_N||^2/(N+1),

   provided 0<d<=N, 0<m, and m(N+1)<=n+1. Orthogonality replaces D_m 1
   by D_m T_N. This error has zero head through N, and its complete norm
   squared is m||T_N||^2.

The exact threshold syntheses are also checked:

    h_2 = 4*1 - 5*D_2 1 + 2*D_3 1,
    h_3 = 2*1 + 2*D_2 1 - 6*D_3 1 + 3*D_4 1.

Their physical sequences are (4,-6,0,...) and (2,6,-12,0,...).

Projection orthogonality gives ||q||^2=<q,h_d>. Finite Cauchy--Schwarz
therefore yields the checked theorems

    projectedDualError_two_fourth_le_mass:
      ||q_(n,2)||^4 <= 270 B_(n,2)^2 ||T_N||^2/(N+1)
      for 2<=N and 3(N+1)<=n+1;

    projectedDualError_three_fourth_le_mass:
      ||q_(n,3)||^4 <= 530 B_(n,3)^2 ||T_N||^2/(N+1)
      for 3<=N and 4(N+1)<=n+1.

The constants are 270=(4^2+5^2+2^2)(1+2+3) and
530=(2^2+2^2+6^2+3^2)(1+2+3+4).
These are upper bounds retaining B, not smallness estimates on B.

## Mathematical critical-zero obstruction (not fully formalized)

This argument is independently derived from the exact finite estimates.
The Mellin cutoff mechanism is consistent with the classical critical-zero
approximation lower bounds; see Burnol, “A lower bound in an approximation
problem involving the zeros of the Riemann zeta function,” Theorems 1.2–1.3,
https://arxiv.org/pdf/math/0103058. Burnol's theorem is not being imported as
a bound on these inverse columns.

Let rho be a zeta zero with Re(rho)=1/2. Such zeros exist unconditionally
(Hardy's theorem). For a primary research source discussing and extending
that theorem, see Dixit–Kumar–Maji–Zaharescu,
https://arxiv.org/abs/1712.08435, introduction and reference [13].
A corresponding Lean zero-existence declaration was not located.

For bounded physical steps, use the actual convergent Mellin integral

    M_s(f)=integral_(1 to infinity) f(floor x) x^(-s-1) dx.

The repository already checks bounded linearity for Re(s)>0 and the
residue Mellin identity. In particular every p_(n,d) has M_rho(p_(n,d))=0.

The finite sequences above give

    s M_s(h_2) = 4-10x+6y,
    s M_s(h_3) = 2+4x-18y+12x^2,
    x=2^(-s), y=3^(-s).

They cannot both vanish for Re(s)>0: three times the first numerator plus
the second is 2(x-1)(6x-7), whereas |x|=2^(-Re(s))<1.
Choose one fixed d in {2,3} with M=|M_rho(h_d)|>0.

The physical bound |p_(n,d)(j)|<=B_(n,d) follows from |g_k(j)|<=1.
For any real R>=d+1 the target h_d vanishes above R. Splitting the Mellin
integral, Cauchy--Schwarz on [1,R] and the bounded tail give

    M <= ||q_(n,d)|| sqrt(log R) + 2 B_(n,d)/sqrt(R).

The finite-head factor is exactly sqrt(log R):
the physical Hilbert norm equals the integral of |f(floor x)|^2/x^2,
and at Re(rho)=1/2 the complementary squared kernel is 1/x.

Take R=(d+1)(1+4 B_(n,d)/M)^2. The tail is at most M/2, hence

    ||q_(n,d)||^4
      [log(d+1)+2 log(1+4 B_(n,d)/M)]^2 >= M^4/16 > 0.       (C)

Now suppose for this fixed d and some b<a there is a cofinal set on which

    exp(-b Phi(n)) B_(n,d)^2 <= K.

Set N=floor((n+1)/4)-1. For large n, N>=3 and 4(N+1)<=n+1.
Also Phi(N)/Phi(n)->1 and Phi(n)=o(log n). Choose

    max(b,0)<a'<a.

The checked arithmetic bound then gives, in ordinary asymptotic analysis,

    ||T_N||^2/(N+1)=O(exp(-a' Phi(n))).

The checked fourth-power estimate implies, on those same good indices,

    ||q_(n,d)||^4=O(exp(-(a'-b) Phi(n))).

The logarithmic factor in (C) is O(1+Phi(n)) on those indices.
Thus the left side of (C) tends to zero, a contradiction.

Consequently the argument proves on paper that, for some fixed d in {2,3},

    for every b<a:
      exp(-b Phi(n)) B_(n,d)^2 -> +infinity.

Separate cofinal sets for d=2 and d=3 pose no problem: select the nonzero
Mellin witness first and use only its own good indices. No intersection
of unrelated cofinal sets is taken, and no RH assumption is used.

Since Bound(*) implies B^2<=2 kappa L at its good indices, it would imply
the refuted mass condition. The strict-margin global Bound(*) is therefore
not a viable provider according to this mathematical argument.
The endpoint b=a is not addressed by this contradiction.

## Established Lean: relative Schur improvement

Module: RH/ProjectedDualSchurAsymptotics.lean.

Let m_(d,j)=modeCoefficient d j, A_j=residueModeCoefficientMass j, and
S_n=sum_(j<n) A_j^2. For M<=n the new split theorem proves

    B_(n,d)^2 <=
      2 [sum_(j<M)|m_(d,j)|A_j]^2
      +2 [sum_(j>=M)m_(d,j)^2] S_n.

The mode-tail energy tends to zero by the existing Bessel summability.
Since S_n>=n, the fixed initial contribution divided by S_n tends to zero.
Thus, unconditionally for every fixed d,

    B_(n,d)^2=o(S_n).

Declarations: projectedDualCoefficientMass_sq_le_split_schur,
projectedDualCoefficientMass_sq_eventually_le_schur,
projectedDualCoefficientMass_sq_isLittleO_schur.

The checked atom bound ||g_(j+2)||^2<=2/(j+2) gives

    A_j^2 >= (j+2)/2,
    S_n >= n(n+3)/4.

Declarations: residueModeCoefficientMass_sq_ge_half_stage,
schur_amplification_energy_ge_quadratic.

This lower bound is on the absolute Schur majorant, not on the actual
signed inverse column. The little-o result supplies no quantitative rate
for its ratio, and cannot be combined with a lower bound on S_n to
deduce an upper bound on B.

## Remaining sufficient route and obligations

The complete signed physical-tail criterion remains:

    n exp(-b Phi(n)) projectedDualTailEnergy n d
      is cofinally bounded for each fixed d>1, with b<a.

This is a valid **conditional research reduction; provider Open**.
It implies residual zero and RH through the existing checked theorems.
The present work does not prove that condition or any other RH-sufficient
quantitative estimate. Absolute column mass loses cancellations that this
physical-tail criterion retains.

For a Lean refutation of the strict-margin mass provider, the remaining
obligations are the actual critical cutoff lower bound, the dual Mellin
witness selection, the finite-rescaling/asymptotic assembly, and a critical
zero-existence theorem (or an explicit zero hypothesis). They remain
**Open as formalization obligations**, distinct from RH.

Principal checked declarations use only propext, Classical.choice and
Quot.sound. No sorry, admit, unsafe declaration, or project-local axiom
is added.
