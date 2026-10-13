# CRT cancellation, coefficient stabilization, and Q Parseval energy

Date: 13 October 2026. Source: the user's constructive CRT/Parseval request.

## Outcome

No unconditional convergence to the constant one, and hence no proof of RH,
has been obtained. The construction question has a precise obstruction:
exact agreement on every growing finite head and eventual coefficients
`-mu(d)` do not control the complete Q norm. We construct legal sequences
having both properties whose squared errors are at least `(N+1)^2`.
The natural one-atom CRT density repair has a separate quantitative full-Q
lower bound. These results do not exclude all CRT constructions.

## Definitions and the two coordinate systems

Use Q(n)=1/(zeta(2)n^2), n>=1, and g_d(n)=(n mod d)/d. For a finite legal
synthesis F=sum_d c_d g_d, the orthogonal coordinates are

  a_F(r)=sum_{k|r} mu(r/k) E_Q[F(kN)].

With H_r(n)=sum_{k|r} mu(r/k) k^2 1_{k|n}, we have a_F(r)=<F,H_r> and
J_2(r)=||H_r||^2. The existing `qSynthesis_error_parseval` is the exact
identity

  ||1-F||_Q^2=sum_{r>=1}|1_{r=1}-sum_d c_d a_{g_d}(r)|^2/J_2(r).

The multiple-divisor/Ramanujan coefficients are different:

  A_q=sum_{q|d} c_d/d,
  c_m=m sum_{q:m|q} mu(q/m) A_q  (m>=2).

All sums in the second identity are finite for finite residue support.
`packetCoefficient_finite_inversion` proves this inverse for the actual
`packetCoefficient`, with no assumed synthesis identity. A general finite
synthesis version is also proved. For each finite-support candidate the sum over k>=1 in the displayed
inverse is already finite. Passing to an infinite-support limit requires
justified convergence/interchange; coefficientwise limits alone do not suffice. The transform A is not the Parseval transform a.
The actual atom g_2 already distinguishes them: A_2=1/2 whereas
its Q-wavelet coordinate a_{g_2}(2)=-E_Q[g_2]<=0.

## Exact finite cancellation without RH

The existing concrete family is

  S_N=sum_{1<=d<=N} mu(d)/d,
  H_N=-sum_{d<=N} mu(d)g_d+(N+1)S_N g_{N+1}.

The d=1 atom vanishes. Mobius inversion gives H_N(n)=1 for 1<=n<=N.
More generally the existing theorem
`residueFraction_exact_head_coefficients` shows that every finite legal
synthesis equal to one through N has c_d=-mu(d) for 2<=d<=N.
For N>=1 the reciprocal coefficient charge is exactly sum_d c_d/d=1. Thus arbitrary
high-conductor corrections must satisfy the single exact condition

  sum_{d>N} c_d/d=S_N.

This is a finite algebraic conclusion, not an RH assumption. It gives
coefficient stabilization before proving any norm convergence.

## A fully explicit escaping family

Define the legal head-invisible direction

  V_N=(N+1)g_{N+1}-(N+2)g_{N+2}.

It is zero for n<=N and equals -(N+1) at n=N+1. For any real T, set

  F_{N,T}=H_N+((H_N(N+1)-T)/(N+1)) V_N.

Then F_{N,T}(n)=1 on 1<=n<=N, F_{N,T}(N+1)=T, and all fixed coefficients
are eventually -mu(d). The first omitted coordinate gives the full-norm
lower bound

  ||1-F_{N,T}||_Q^2 >= (1-T)^2/[zeta(2)(N+1)^2].

For T_N=1+(N+1)^2 sqrt(zeta(2)), the exact lower bound is

  ||1-F_{N,T_N}||_Q^2 >= (N+1)^2.

The sequence nevertheless tends pointwise to one and each fixed residue
coefficient is eventually -mu(d). The same lower bound holds for the
entire Jordan-weighted Parseval sum. This is a concrete counterexample to
the proposed inference from finite cancellation and coefficient limits
alone. It says nothing against the actual optimizer criterion, which also
uses its unconditional strong convergence to the legal-closure projection.

## The natural CRT/lcm density repair

Let L>1, rho_L=sum_{d|L}mu(d)/d, and C_L(n)=#{1<=k<=n:gcd(k,L)=1}.
The finite legal candidate

  G_L=-sum_{d|L}mu(d)g_d+L rho_L g_L

has the exact identity

  G_L(n)=C_L(n)-L rho_L floor(n/L).

If M<L and every 2<=k<=M has a common prime factor with L, then G_L(n)=1
for 1<=n<=M. This applies to lcm and primorial conductors covering the head.
For n<L its reflection identity is

  G_L(n)+G_L(L-1-n)=L rho_L.

Its uniform period mean is therefore L rho_L/2, and the exact variance
identity is

  sum_{n=0}^{L-1}(1-G_L(n))^2
  =sum_{n=0}^{L-1}(G_L(n)-L rho_L/2)^2+L(1-L rho_L/2)^2.

Using the actual inverse-square weights on the positive first period gives

  ||1-G_L||_Q^2 >= (1-L rho_L/2)^2/[zeta(2)L].

This is a lower bound on the full infinite Q error, not on a proxy norm.
The standard arithmetic identification L rho_L=phi(L) makes its meaning
transparent. The lcm/primorial asymptotic discussion below is an ordinary
written deduction, not an additional Lean declaration in this checkpoint:

  phi(L)^2/L=product_{p^a||L} p^(a-2)(p-1)^2.

For p>=3 each factor is at least 4/3; the p=2 factor is at least 1/2.
As the conductor includes more distinct primes the product diverges.
Consequently this particular one-atom CRT repair has divergent Q error
along covering lcm/primorial conductors, despite its exact heads and
stabilized Mobius coefficients.

A repair of this particular mean defect is possible: when L is even and
L/2>M, replace the final correction by

  (L rho_L-2)g_{L/2}+(4-L rho_L)g_L.

It still repairs the head and makes the reflection constant two (mean one).
This observation is written algebra, not a formalized tail bound. It leaves
the fluctuations and all remaining Q tail energy to be controlled.

## The actual optimizer parity criterion

At stage n the project uses conductors 2,...,n+1. Let F_n be its literal
inverse-Gram optimizer and e_n=1-F_n. Orthogonality yields

  <e_n,1>=||e_n||_Q^2,
  H_2=3*1-8*g_2,
  <e_n,H_2>=3||e_n||_Q^2  (n>=1).

Thus a single parity coordinate tends to zero if and only if one belongs
to the full legal Q closure. A continuous Q-to-Pareto transfer followed by
the existing Mellin separation theorem proves RH from this limit, and also
from the literal full arithmetic Parseval limit. These are sufficient
implications, with the limiting hypotheses explicit; RH is not assumed.
The finite-stage error and parity coordinate are strictly positive, since
a finite periodic legal synthesis cannot equal the constant one.

## The precise constructive target still open

Construct finite legal F_N, exact on the growing head, with

  sup_N ||1-F_N||_Q^2 < infinity.

This is sufficient: the existing sparse-average theorem then gives actual
finite legal averages converging to one, with error B/m+4/m^2. Equivalently
for periodic candidates it is enough to bound the appropriate complete
one-period inverse-square tail uniformly. Exact finite CRT cancellations,
prime independence, coefficient stabilization, and finite Mobius inversion
do not by themselves establish this bound.

## Formal modules and verification

- `RH/QExactHeadEscape.lean`: legal null directions, prescribed tail value,
  exact heads, pointwise convergence, eventual Mobius coefficients,
  diverging lower bound and nonvanishing full error, Parseval lower bound.
- `RH/QCRTDivisorHead.lean`: the repaired divisor candidate, exact counting
  and reflection identities, exact period mean/variance, and full-Q bound.
- `RH/QRamanujanCoefficientInversion.lean`: finite inversion and the
  distinction between Ramanujan and Q-wavelet coefficients.
- `RH/QOptimizerParity.lean`: actual optimizer parity identity, positivity,
  and equivalence with legal-closure membership.
- `RH/QOptimizerParityRH.lean`: full Q closure, energy, parity, and arithmetic
  Parseval sufficient conditions for RH, via the existing Pareto transfer.

The combined proof-candidate check succeeded on the Lean server in
`job_CvrIYg5lFQ6_-JoHO9ggAzNkJj93BGQY`. The six principal checked
declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
No unconditional zero-energy provider or proof of RH is claimed.

The separate five modules subsequently compiled successfully in server job
`job_Pyd39SVg9u7ky8_leg-QexZNYH_VcJW8` (exit code 0). The principal
imported declarations were also inspected with `#print axioms`, reporting
only `propext`, `Classical.choice`, and `Quot.sound`.

The full aggregate server build `lake build RiemannResearch --quiet` also
succeeded in `job_cuWRmJ56F3Jpd5GKY6Xr7j-9Anp9kvms` (61.8 seconds),
including the five new modules and the aggregate exports.

Publication history: automatic approval review initially blocked the
commit/push pending explicit authorization. The user approved publication
on 13 October 2026 at 12:50 America/Los_Angeles. Publication proceeds through
the normal server checkpoint, including validation of any integrated source.
Workspace: `ws_4f2Qdo8rQ7LBdryTpmTpQh2AP0v5GcgB`.
