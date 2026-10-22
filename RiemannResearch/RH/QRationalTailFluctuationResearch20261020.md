# Rational residual tails: class Poincare bounds, sharp duality, and an absorption obstruction

Date: 20 October 2026. Source: the user-directed investigation starting from
commit `1a1335b5e30a65b6ec37b4259bb513be3abfe2dd`.

## Conclusion

The class constraints and Dirichlet identity give explicit unconditional
fluctuation and negative-mass bounds. Their elementary constants do not give
the required fixed-factor absorption. Optimizing all homogeneous constraints
recovers the original minimum exactly, rather than a separate upper estimate.

A stronger obstruction comes from a coprime three-site witness: along distinct
primorials, **S_L/R_L tends to -1 unconditionally**. Thus every fixed theta<1
eventually fails in the error-free bound S_L >= -theta R_L. A vanishing additive
error is still possible, but cannot be o(R_L). None of this shows R_L has a
positive limit; it is compatible with R_L tending to zero and with RH.

Verification distinction: the finite three-site bound, explicit signed upper
bound, class inequalities, dual identities, and the seventh-primorial obstruction
are formalized in Lean. The final prime-indexed asymptotic assembly using
Bertrand's postulate is a mathematical derivation in Section 5 below; this
change does not contain a Lean declaration asserting that primorial ratio limit.
Publication and final verification are gated by the session's server checkpoint.

## 1. Definitions and retained endpoints

For positive L, use all divisor atoms g_d(a)=(a mod d)/d, d|L. For squarefree
L these are all squarefree divisor atoms, including composites. The d=1 atom
is zero. Let F_L be the actual selected rational-weight minimizer, r=1-F_L,
and set

    w(a)=1/a^2+2/[L(2a+L)],       1 <= a <= L,
    R=sum_a w(a)r(a)^2,
    T(k)=sum_(a=k)^L w(a)r(a),
    b=5/(3L^2),   E=R-b,   m=phi(L),
    S=sum_(k coprime to L, k>1) T(k).

These are the rational periodic weights, not the exact complete-Q periodic
weights. The existing weight-comparison and convergence modules connect their
minima to the complete-Q limiting defect. No identity between the two finite
minimizers is assumed.

The previously established equalities are

    T(L)=b, T(1)=R, R+S=mb,
    E=sum_(a=1)^(L-1) (T(a)-T(a+1))^2/w(a),
    sum_(k in C_e) T(k)=|C_e| b,  C_e={1<=k<=L : gcd(k,L)=e}.

Write u(k)=T(k)-b. Every class has centered sum zero, u(L)=0, and u(1)=E.

## 2. Explicit class Poincare and negative-mass bounds

For sites i,j define the path resistance

    D(i,j)=sum_(min(i,j)<=a<max(i,j)) w(a).

First, finite weighted Cauchy--Schwarz gives

    (T(i)-T(j))^2 <= D(i,j) E.

For a gcd class C with n=|C|, put

    V_C=sum_(k in C) (T(k)-b)^2,
    A_C=(1/2)sum_(i,j in C) D(i,j).

The exact pairwise identity and resulting bound are

    sum_(i,j in C)(T(i)-T(j))^2 = 2n V_C,
    n V_C <= A_C E.

Finite interchange of sums also gives the convenient arithmetic expression

    A_C=sum_(a=1)^(L-1) w(a) n_C(a)(n-n_C(a)),
    n_C(a)=#{k in C:k<=a}.

The Lean definition uses the double-resistance expression. The prefix-count
expression above follows by counting the two orientations of pairs separated
by each edge; this reindexing is not a separate Lean declaration here.

For the coprime class C=C_1, let N and P be the negative and positive tail
masses after erasing k=1. Combining the existing signed-variance budget with
the new path bound proves

    4N(N+mb) <= m V_C <= A_C(R-b).

This is an unconditional one-sided control on the negative mass, with its
complete arithmetic constant exposed. Since S=P-N, it gives a lower bound
on S by minus the nonnegative root of this quadratic. It does not yield a
fixed theta<1 times R plus a vanishing error.

The first edge alone contributes w(1)(m-1) to A_C. This elementary constant
does not become small. This observation concerns this explicit path bound;
it does not claim that every possible sharper arithmetic estimate is impossible.

## 3. A coprime-average Cauchy--Schwarz bound and its exact slack

For the coprime prefix n(a)=#{k<=a:gcd(k,L)=1}, define

    h(a)=1-n(a)/m,       1<=a<L,
    B=sum_(a=1)^(L-1) w(a)h(a)^2.

Using the class mean, T(1)=R, and the endpoint gives

    sum_(a<L) w(a)r(a)h(a)=E.

Consequently

    E <= B,
    B-E=sum_(a<L)w(a)(r(a)-h(a))^2.

This is a full square identity, not a claim that its slack vanishes.
Along primorials B tends to zeta(2): for each fixed a the prefix is eventually
1, m tends to infinity, and the rational correction contributes at most 2/L.
The inverse-square tail supplies uniform domination. Thus this particular
certificate supplies no decaying upper bound.

This section is an elementary derivation checked by exact rational arithmetic
at the four solved periods. The profile identity and B-limit are not added as
Lean declarations in this change.

## 4. Sharp duality: where optimizing all class constraints leads

The new Lean module uses weighted-gradient coordinates x on 1,...,L-1 with
the full homogeneous normal constraints

    sum_(a<L) w(a)x(a)g_d(a)=0,       every d|L.

Define M(x)=sum_(a<L)w(a)x(a), D(x)=sum_(a<L)w(a)x(a)^2. Then Lean proves

    E-[2M(x)-D(x)] = sum_(a<L) w(a)(r(a)-x(a))^2,
    M(x)^2 <= E D(x).

The actual residual r is admissible, and attains 2M(r)-D(r)=E. In particular,
for every real K,

    E<=K  iff  every admissible x satisfies 2M(x)-D(x)<=K.

No unknown normal-equation provider is assumed for the actual minimizer.

To interpret this in tail coordinates, take z(L)=0 and
x(a)=[z(a)-z(a+1)]/w(a). Discrete summation by parts gives, for d>1,

    sum_(a<L) w(a)x(a)g_d(a)
      =(1/d)sum_(k=1)^L z(k)-sum_(d|k) z(k).

The d=L equation forces the total sum to zero, and divisor incidence inversion
then identifies the other equations with sum_(k in C_e)z(k)=0 in every class.
Thus the sharp constrained evaluation constant is exactly E:

    E = max_z [2z(1)-sum_(a<L)(z(a)-z(a+1))^2/w(a)].

The weighted-gradient version and its exact gap are Lean-verified in this
change. This summation-by-parts coordinate translation is supplied here as a
derivation, not claimed as a separately checked Lean declaration. It explains
why invoking a sharp class-constrained Poincare constant merely renames the
original minimum unless a new arithmetic bound for that constant is provided.

## 5. Three-site obstruction for the actual minimizer

Choose any q with 3<=q<L and gcd(q,L)=1. For every nontrivial divisor d|L,
there is no residue wrap at q, so

    g_d(q)-g_d(q-1)=g_d(1).

The same identity holds after full divisor synthesis. Therefore the actual
residual satisfies the exact affine constraint

    r(1)+r(q-1)-r(q)=1.

Weighted Cauchy--Schwarz on those three distinct sites yields

    1 <= K_(L,q) E,
    K_(L,q)=1/w(1)+1/w(q-1)+1/w(q).

Since 1/w(a)<=a^2,

    K_(L,q)<=1+(q-1)^2+q^2<=2q^2,
    R >= b+1/K_(L,q) >= b+1/(2q^2).

Together with R+S=mb, this supplies the exact finite test

    [mb-(1-theta)b] K_(L,q) < 1-theta
      implies S < -theta R.

The new Lean theorem also proves the simpler universal signed upper bound

    S <= -[1-10q^2/(3L)] R.

This has the opposite direction from the desired absorption inequality.

For the distinct primorial L_n=p_1...p_n, take q=p_(n+1). For n>=3,
q<L_n. Bertrand's postulate gives q<=2p_n and p_n<=2p_(n-1), hence

    q^2/L_n <= 8/L_(n-2).

The positivity of R and the signed identity therefore give

    0 <= 1+S_(L_n)/R_(L_n)
      = [5phi(L_n)/(3L_n^2)]/R_(L_n)
      <= 10q^2/(3L_n)
      <= 80/(3L_(n-2)) -> 0.

Thus S/R -> -1 without assuming or refuting RH. The finite estimates are
formalized; this final prime-indexed assembly is proved mathematically here.
Bertrand reference: Mathlib.NumberTheory.Bertrand,
`Nat.exists_prime_lt_and_le_two_mul`,
https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Bertrand.html .
The reference supports the neighboring-prime bound, not an RH conclusion.

In particular, error-free fixed-factor absorption is eventually false for
every theta<1. More generally, any valid cofinal absorption sequence must have

    epsilon_L/R_L >= 1-theta-mb/R_L = 1-theta-o(1)

along its valid stages. A requirement epsilon_L=o(R_L) would therefore also
be impossible. A requirement epsilon_L->0 remains compatible with this result
and still requires control of the absolute minimum.

## 6. Exact finite evidence; no logarithmic-head computation

Python's `fractions.Fraction` solves the entire rational normal system at
L=2,6,30,210, with respectively 1,3,7,15 nonzero divisor atoms. Checks use
exact rational arithmetic for the normal equations, all gcd means, Dirichlet
identity, initial value, signed identity, class path bound, negative budget,
and coprime-profile square gap. Decimal displays are rounded from exact values.

| L | R | -S/R | N/R | E | Coprime profile bound B | Class constant A |
|---:|---:|---:|---:|---:|---:|---:|
| 2 | .416666667 | 0 | 0 | 0 | 0 | 0 |
| 6 | .0912971351 | -.0141894651 | 0 | .0450008388 | .387549603 | 1.55019841 |
| 30 | .0421808551 | .648778699 | .648778699 | .0403290033 | 1.20139596 | 12.3224971 |
| 210 | .0278273563 | .934810230 | .934943887 | .0277895634 | 1.55450782 | 97.0711999 |

The three-site certificate requires no optimizer solve. Exact certificates
through the seventh primorial give:

| L | q | Certified lower bound for -S/R |
|---:|---:|---:|
| 6 | 5 | -.145984518 |
| 30 | 7 | -.0397293005 |
| 210 | 11 | .602432386 |
| 2310 | 13 | .952931776 |
| 30030 | 17 | .994187640 |
| 510510 | 19 | .999595697 |

At L=510510 the exact lower fraction is

    18822511506381529101815138108257489171 /
    18830124579738200353436666831536111891 > 1999/2000.

Lean independently checks the finite conclusion

    rationalSignedTail 510510 < -(1999/2000)*rationalMinimum 510510.

No eighth primorial is tested. No logarithmic-head minima are recomputed.
Only the first four periods are counted as completed full minimizer solves;
an optional L=2310 solve produced no usable result before a serialization
failure and is excluded from the evidence. The higher-period rows use only
the three-site certificate, not claimed optimizer values.

## 7. Formal additions and remaining arithmetic obligation

- `Analysis/FiniteClassDirichlet.lean`: weighted Cauchy--Schwarz, exact
  pairwise centered variance, explicit class Poincare and negative-mass bounds,
  and exact dual square completion.
- `RH/QRationalTailPoincare.lean`: actual edge representation, pairwise tail
  inequality, every gcd-class Poincare bound, and actual negative-mass budget.
- `RH/QRationalTailDuality.lean`: actual residual admissibility, exact dual
  gap, sharp Cauchy--Schwarz inequality, attained objective, and equivalence
  of a dual upper bound with the original minimum bound.
- `RH/QRationalCoprimeLower.lean`: actual coprime residue jump, three-site and
  polynomial lower bounds, finite absorption obstruction, signed upper bound,
  and exact seventh-primorial counterexample to theta=1999/2000 with no error.

Open: a genuinely new upper estimate forcing E_(L_n)->0, equivalently R_(L_n)->0.
One possible precise target is an explicit K_n->0 bounding every admissible
dual objective 2M(x)-D(x). The equivalence theorem does not provide such K_n.
Another is the original cofinal signed lower estimate with epsilon_n->0;
the new result rules out asking that error to be negligible relative to R_n.

Best next step: seek a concrete arithmetic upper certificate for the constrained
dual norm or the complete divisor approximation error, retaining its full square
slack. Replacing the original minimization by its sharp dual norm, discarding
signed terms, or claiming individual tail positivity cannot supply that input.
Squarefree closure and RH remain unresolved.
