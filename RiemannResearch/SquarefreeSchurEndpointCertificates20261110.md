# Canonical Schur endpoint certificates — 10 November 2026

## Status

Cofinal smallness of the actual Schur upper endpoints remains **Open**.
The new results discharge the trial and solve-accuracy providers
unconditionally, and bound the limiting Pareto error from a single complete
finite certificate. They do not prove displacement vanishing or RH.

The uniform geometric convergence proved below is convergence of the
**endpoint error** to zero. It must not be substituted for convergence of
the endpoint itself to zero.

## Definitions

Use the complete primorial dictionary V_n from
`QSquarefreePrimorialCofinality`: every divisor greater than one of
primorial(n+3). Let P_n be its Q orthogonal projection and W_n the span
of its prime atoms. Write

- f_n^Q=P_n 1, f_n^P=the matched Pareto projection;
- d_n=f_n^Q-f_n^P, E_Q(n)=||1-f_n^Q||_Q^2;
- x_n=P^Q_(W_n)d_n;
- K_n=V_n intersect W_n^perp_Q;
- L_n x=x-P^P_(K_n)x;
- S_n(x,y)=<L_n x,L_n y>_P;
- F_n=selfForcing(n)=S_n(x_n,x_n);
- J_n(v)=2 schurForcing(n,v)-S_n(v,v).

The finite carry projection in L_n and every full Q/Pareto norm remain
part of the definitions. Evaluating a finite matrix entry by a physical
cutoff still requires a certified complete-tail bound.

## A specified iteration

`QPrimorialResolvent.lean` defines, entirely using Q projections and B,

```
b_n = P_n B(1-f_n^Q),
T_n z = (4/3) P_n (Bz-z/4),
s_n(z) = (4/3)b_n + T_n z,
C_n(z) = (18/17)s_n(s_n(z)) - z/17,
a_(n,0)=0, a_(n,k+1)=C_n(a_(n,k)).
```

The recursion does not use d_n or f_n^P as an input. The theorems prove

```
d_n = (4/3)b_n + T_n d_n,
||T_n z||_Q <= ||z||_Q/3,
||d_n-a_(n,k)||_Q <= 17^(-k)||d_n||_Q.
```

The exact energy remainder identity and the existing rational four-site
certificate 983/2000 give

```
||d_n||_Q^2 <= c E_Q(n),   c=966289/8136000,   E_Q(n)<=1,
||d_n-a_(n,k)||_Q^2 <= c E_Q(n) 289^(-k).
```

The Chebyshev numerator retains its signed expression and exact norm-square
remainder; the arithmetic displacement identity retains both nonnegative
complete-energy remainders.

## Automatic upper endpoints

In `QPrimorialSchurEndpoints.lean`, put

```
v_(n,k)=P^Q_(W_n)a_(n,k),
B_(n,k)=c zeta(2) E_Q(n) 289^(-k),
U_(n,k)=J_n(v_(n,k))+B_(n,k).
```

The unconditional interval theorem is

```
J_n(v_(n,k)) <= F_n <= U_(n,k),
0 <= U_(n,k)-F_n <= B_(n,k) <= c zeta(2) 289^(-k).
```

For every stage selection N(j), even bounded or oscillating, and every
k(j) tending to infinity, U_(N(j),k(j))-F_(N(j)) tends to zero.
No cofinality of N is required for this endpoint-error conclusion.

The same trials also satisfy the original complete dual solve-residual
hypothesis automatically, with

```
eta_(n,k)=sqrt(c E_Q(n) 289^(-k)),
|forcingResidual(n,v_(n,k),y)| <= zeta(2) eta_(n,k)||y||_Q, y in W_n.
```

The new U is no larger than the previous endpoint
J_n(v)+(59/30)zeta(2)eta^2.

A second, a posteriori certificate uses an observed iterate increment:

```
||d_n-a_(n,k+1)||_Q <= ||a_(n,k+1)-a_(n,k)||_Q/16,
F_n <= U_post(n,k)
    := J_n(v_(n,k+1))+(zeta(2)/256)||a_(n,k+1)-a_(n,k)||_Q^2.
```

Thus min(U_(n,k+1),U_post(n,k)) is also a certified upper endpoint.

## Quantitative control of the limiting residual

`QPrimorialResidualCertificate.lean` improves the Schur lower bound to

```
(1017/2000) zeta(2)||x||_Q^2 <= S_n(x,x),  x in W_n.
```

Let E_n=||1-f_n^P||_P^2 and E_infinity=||pResidual||_P^2.
The proof uses Bertrand's prime-scale estimate, the full signed pairing
identity, and monotonicity of the matched Pareto errors. For every real U
with F_n<=U,

```
E_infinity^3 <= E_n^3
  <= max((8/(n+3))^3, (128000/1017)U).
```

In particular this applies to the minimum of the two certified endpoints.
A finite stopping rule for E_infinity<=epsilon is

```
epsilon>=0,
8/(n+3)<=epsilon,
U<=(1017/128000)epsilon^3.
```

These are finite quantitative bounds, not an assumption that any requested
tolerance will eventually be met.

## Remaining obligation and circularity check

The specified diagonal satisfies

```
U_(n,n) -> 0  iff  displacement=0.
```

For any solve-depth selection k(n), cofinally arbitrarily small
U_(n,k(n)) implies displacement=0 and Mathlib RiemannHypothesis.
The sufficient direction needs no growth hypothesis on k.

What remains unproved is an arithmetic estimate making these upper
endpoints cofinally small. More accurate solves narrow a valid interval
around F_n; they cannot by themselves force F_n to vanish.

## Verification evidence

- Focused Bazel/BuildBuddy module build:
  `job_4WglM_mQ5QVqPgaQuwuoUGnsyjSC8WHr`, exit 0,
  174.838 seconds of server-reported verification time.
- Final updated-source compilation and transitive axiom audit:
  `job_c2Uj75kzlrafw0cY31fvLJNeNhmQK-3J`, exit 0,
  65.540 seconds. The temporary audit file was removed.
- Seven `#guard_msgs` checks required exactly
  `[propext, Classical.choice, Quot.sound]` for the arithmetic error
  certificate, certified interval, automatic dual residual, uniform
  endpoint-excess smallness, diagonal equivalence, conditional RH
  consumer, and limiting Pareto certificate.
- The three permanent modules are exported by `RiemannResearch.lean`.
  The publication checkpoint enforces full-project Bazel/BuildBuddy
  validation and source audit before pushing.

The axiom audit does not discharge an explicit hypothesis in a conditional
theorem. The cofinal arithmetic condition remains open.
