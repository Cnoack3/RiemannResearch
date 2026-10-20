# CRT block gains and the infinite squarefree CRT

Research continuation for Christian Noack. 20 October 2026 UTC
(19 October in America/Los_Angeles).

## Status

This continuation starts from commit f6ac5fa684f01ca031166ba9856ddfec7ad4ee0e
and the attached CRT-carry handoff. It adds three Lean modules:

- Analysis/ScreenedBlockGain.lean: finite block scores bounded by the actual
  nested projection gain, without linear independence or an inverse Gram matrix.
- RH/QCRTCarryGain.lean: specialization to literal floor-defined carries,
  all nontrivial old divisors, the actual qOne target, and the complete Q metric.
  The separate new-prime gain is retained.
- RH/QParityConditionalTarget.lean: an explicit parity-conditional image of
  the legal atom g_6, whose membership in the squarefree closed span is exactly
  the original constant-target membership problem.

The arithmetic score lower bound remains Open. RH is not proved. The new
conditional RH declaration takes the unresolved membership as a hypothesis.
The RH-to-squarefree-closure implication is a literature input, not a new
Lean theorem here.

The audit also found that QRationalCoprimeMinimum, QRationalCoprimeLegality,
and QRationalCoprimeTail already formalize attained finite minima and the
signed coprime-tail identity. QSquarefreeRelativeGain already proves the
relative-gain nonsummability equivalence. These were reused conceptually,
not re-proved under new names.

## 1. The actual gain interface

Write g_d(n)=(n mod d)/d, Q(n)=1/(zeta(2)n^2), and
V_L=span{g_d:d divides L, d>1}. For a new prime p, let

W=V_L+R g_p, U=V_(pL), r_W=(I-P_W)1,
h_d=(I-P_W) kappa_(p,d), eta_d=<h_d,r_W>_Q,

where d runs over EVERY nontrivial divisor of L. In particular composite old
divisors are included. The previous publication proves h_d=-(I-P_W)g_(pd).

For arbitrary nested projection subspaces V<=W, vectors z_i in W, and target x,
the new generic theorem proves

    sum_i <R_V z_i,R_V x>^2
      <= (sum_i ||R_V z_i||^2) (||R_V x||^2-||R_W x||^2).

Its proof uses the existing exact identity

    ||R_V x||^2 = ||R_W x||^2 + ||P_W x-P_V x||^2.

Each score is the inner product with P_W x-P_V x, so Cauchy--Schwarz
and a finite sum give the estimate. It requires no invertibility, independence,
nonempty family, or spectral lower bound. The division-free result covers
the empty first carry block.

The literal block trace satisfies the existing complete-Q bound

    T_(L,p) = 2/(zeta(2)p) sum_(d|L,d>1) 1/d.

We now connect it directly to the actual projection improvement:

    sum_d eta_d^2 <= T_(L,p) (||r_W||^2-D_(pL)).

Moreover, with A_(L,p)=||P_W1-P_(V_L)1||^2,

    D_L-D_(pL)
      = A_(L,p)+||P_U1-P_W1||^2,

and, when T_(L,p)>0,

    A_(L,p) + (sum_d eta_d^2)/T_(L,p) <= D_L-D_(pL).

This is the theorem prime_gain_add_score_div_le_total_gain. It retains the
prime step that a carry-only certificate would discard. The formal statements
display the ordinary orthogonal-projection instances and valid CRT coefficient
equations. For positive periods these spaces are finite dimensional; no
arithmetic exhaustion hypothesis is among these finite-gain assumptions.

For a primorial chain a sufficient unresolved arithmetic target is divergence
of the cumulative normalized combined certificates

    sum_M [ A_M + ||eta_M||^2/T_M ] / D_M = infinity.

At an empty block omit the quotient and retain A_M. The actual relative gain
dominates each summand; the existing relative-gain criterion then gives
exhaustion. This is a conditional route, not a proved lower bound.

## 2. A single conditional image isolates the legality problem

Let C_2 be Q-conditional expectation on parity. Define

    a = E_Q[g_6(N) | N odd],
    b = E_Q[g_6(N) | N even] = E_Q[g_3(N)] > 0.

The last equality follows from the exact conditional law N/2 ~ Q given 2|N.
The new object paritySix is literally reconstructed from the complete
Q fiber means, with physical sequence

    u = C_2 g_6 = b*1 + 2(a-b)*g_2.

For every real subspace V containing g_2, the new Lean module proves

    u in V iff 1 in V.

For the actual orthogonal screen it proves the exact identities

    R_V u = b R_V 1,
    ||R_V u||_Q^2 = b^2 ||R_V 1||_Q^2.

These hold for every nonempty exhaustive squarefree stage and its closed
union H. Thus approximating u legally is precisely the original approximation
problem, scaled by a fixed nonzero constant. The atom g_6 itself is proved to
belong to H.

The module also proves

    [for every f in H, C_2 f belongs to H] iff 1 belongs to H,

using the explicitly reconstructed fiber-mean map. For bounded inputs this
map is the actual conditional expectation by the earlier QResidueConditional
formulas; the decisive input g_6 is bounded. Standard L2 integrability makes
the same formula the usual conditional expectation on all of QHilbert.
This last general integrability identification is not separately formalized
in this module.

The declaration riemannHypothesis_of_paritySix_mem_closure connects the
single unresolved membership to the existing formal Mellin RH implication.
Bagchi's Remark 8 and equivalence of the P and Q norms give the mathematical
reverse implication. No RH-to-closure provider was added here.

This is an exact reduction and a diagnostic for proposed proofs:
assuming that conditional expectation preserves legality already assumes an
RH-equivalent property, even for parity and one explicit legal input.

## 3. What the infinite CRT adds

The correct squarefree compact space is

    X_sf = inverse_limit_M Z/L_M Z = product_p F_p.

It differs from the full profinite integers Zhat=product_p Z_p, which retain
all prime powers. Finite CRT supplies compatible residue coordinates; passing
to the inverse limit organizes all levels on one compact space.

Embed positive integers diagonally and transport Q. The resulting measure is
countably atomic and has full topological support: every finite residue
cylinder contains a positive integer with positive Q mass. Haar measure assigns
zero mass to every individual diagonal integer, so these two measures are
mutually singular. Residue coordinates are independent under Haar, not under Q.
This should not be confused with the different, independent prime-valuation
description of the zeta-two law.

The useful added analytic structure is the increasing filtration of residue
sigma-algebras and its compatible Q-conditional projections C_(L_M).
The following quantitative argument is an ordinary mathematical proof in
this note, not a new Lean formalization.

For 1<=a<=L, let w_L(a)=sum_(j>=0) Q(a+jL), with a=L the zero residue.
If f is supported on {1,...,H} and L>=H, then

    C_L f(a) = Q(a) f(a)/w_L(a)       (a<=H),

and it is zero on other residue classes. Therefore

    ||f-C_L f||_Q^2
      = sum_(a<=H) f(a)^2 Q(a) [1-Q(a)/w_L(a)]
      <= sum_(a<=H) f(a)^2 [w_L(a)-Q(a)]
      <= L^(-2) sum_(a<=H) f(a)^2.

The last inequality follows directly from

    w_L(a)-Q(a)
      = 1/zeta(2) sum_(j>=1) (a+jL)^(-2) <= 1/L^2.

Finite supports are dense and conditional projections are contractions,
so C_(L_M) f -> f strongly for every f in L2(Q). This provides rigorous
ambient reconstruction with an explicit finite-support rate. It does not
place C_L f in a legal span.

In particular full-cylinder density cannot be substituted for legal density.
The squarefree legal closure is a proper subspace of ambient L2(Q)
unconditionally, as existing QSquarefreeJumpApplications witnesses establish.
For example every legal limit satisfies

    f(4)-f(3)-f(2)+f(1)=0,

whereas a singleton at 1 does not. Constant 1 does satisfy this relation.

Uniform closure is also unsuitable: every legal g_d is zero at the profinite
zero point, so the uniform distance of 1 from the legal span on X_sf is
exactly 1. That point has Q measure zero, and this does not contradict the
possibility of L2(Q) approximation.

Even pointwise approximation on positive integers is already available
without RH. For a prime p>H, writing S_H=sum_(d<=H) mu(d)/d, the legal function

    F_H = -sum_(2<=d<=H) mu(d) g_d + p S_H g_p

equals 1 at every integer 1<=n<=H. Indeed sum_(d<=n)mu(d) floor(n/d)=1.
Only squarefree conductors have nonzero coefficients. The missing property
is control of the COMPLETE Q norm, not existence of an infinite pointwise
limit.

## 4. Quantifying the Haar-to-Q obstruction

This is an ordinary proof, not Lean-verified in this continuation. Set
rho_L(a)=L w_L(a), the density on the finite residue quotient relative to
uniform Haar measure. For independent N,N' with law Q,

    ||rho_L||_(L2(Haar_L))^2 = L P(N=N' mod L).

Separate diagonal and off-diagonal collisions. Since
sum_n Q(n)^2=zeta(4)/zeta(2)^2=2/5,

    ||rho_L||^2
      = (2/5)L + (2L/zeta(2)^2)
          sum_(n>=1,k>=1) 1/[n^2 (n+kL)^2].

All summands are nonnegative and n+kL>=kL, so

    (2/5)L <= ||rho_L||^2 <= (2/5)L + 2/L.

Thus the finite densities have L2 norms asymptotic to sqrt(2L/5).
A uniform L2 bound on these density-transfer factors is impossible.
Any use of Haar Fourier/CRT orthogonality must retain the growing weights
or prove a more tailored comparison.

## 5. Finite checks performed with Wolfram

Exact rational arithmetic checked both normal equations and
E_L+S_L=5 phi(L)/(3L^2) using u_L(a)=a^(-2)+2/[L(2a+L)].

| L | Legal dimension | E_L | S_L | Exact checks |
|---:|---:|---:|---:|---|
| 2 | 1 | 0.41666666666667 | 0 | true |
| 6 | 3 | 0.091297135076544 | 0.0012954575160486 | true |
| 30 | 7 | 0.042180855136787 | -0.027366040321972 | true |
| 210 | 15 | 0.027827356272113 | -0.026013297315197 | true |

These are unnormalized rational-weight energies, not D_L.

Separately, 80-digit computations used COMPLETE Q residue weights
w_K(a)=PolyGamma[1,a/K]/(zeta(2) K^2). They included every old divisor and
checked the inverse-Gram gain against the actual energy difference to
absolute tolerance 10^(-60). These are high-precision checks, not interval
certificates or asymptotic evidence.

| L -> pL | D_L | D_(pL) | Prime gain A | Carry gain | Carry score / trace cap |
|---|---:|---:|---:|---:|---:|
| 2 -> 6 | .25 | .0547669433702622 | .181314717514652 | .0139183391150857 | .00261392381185535 |
| 6 -> 30 | .0547669433702622 | .0254002254357182 | .0275853765149467 | .00178134141959740 | .000274695878605414 |
| 30 -> 210 | .0254002254357182 | .0168704360610230 | .00849031393235046 | .0000394754423446607 | .00000149775564046723 |

The trace cap held in each numerical check. The table specifically argues
for retaining the prime gain, not for extrapolating a limiting rate.

The finite density norms squared were approximately 1.25, 2.62758346493310,
12.0594291610925, and 84.0092984663391 at L=2,6,30,210, respectively,
consistent with the proved ordinary bounds above.

## 6. Next arithmetic work

1. Estimate the combined prime-plus-carry score relative to current D_M.
   This is the most direct consumer of the new verified block interface.
2. Study legality of the single conditional target C_2g_6 through arithmetic
   approximants. Its exact proportional residual prevents mistaking
   a restatement of RH for a new estimate.
3. Formalize the quantitative full-cylinder approximation theorem if it
   becomes a consumer of a concrete legality or leakage argument.
4. Investigate the candidate intersection description
   H intersect Cyl_L subset V_L + R*1 for squarefree L. Radical jump
   relations and finite Mobius inversion suggest it. It is NOT a theorem
   of the new Lean modules, and no RH inference may assume it without proof.
5. Complete the rational-minimum-to-complete-Q convergence assembly, while
   retaining the nonzero limiting defect unless arithmetic controls it.

## 7. Sources and verification scope

- Bhaskar Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space
  reformulation of the Riemann hypothesis*, Theorem 1, Remark 8, and the
  inverse-square weight comparison discussion:
  https://arxiv.org/pdf/math/0607733 .
  This supports the RH/closure criterion, not a new exhaustion estimate.
- Ben Lynn, Stanford, finite Chinese remainder theorem:
  https://crypto.stanford.edu/pbc/notes/numbertheory/crt.html .
- Andrew Sutherland, MIT 18.785 lecture notes, Definition 26.13,
  Remark 26.16 and Example 26.17 (PDF pp. 275--276):
  https://ocw.mit.edu/courses/18-785-number-theory-i-fall-2021/mit18_785f21_full_lec.pdf .
  These support inverse-limit terminology and the distinction from full Zhat.
- The explicit cylinder rate, density-collision bound, and interpretation
  of the new target were derived in this continuation; no novelty claim is made.

The Lean checks are serialized on the user's server. Before publication,
the final checkpoint validates the project source and aggregate exports.
The direct block and parity proof axiom inspections use only propext,
Classical.choice, and Quot.sound. No project-local axiom, unfinished proof,
or unsafe declaration is part of this development. The quantitative
profinite estimates in Sections 3--4 have ordinary proofs here and are
explicitly outside the Lean verification claim.

## 8. Reproducible Wolfram calculations

Exact rational signed-tail and normal-equation check:

~~~wl
Table[Module[{ds=Rest[Divisors[L]],w,J,G,b,c,E,S,r,tail},
 w=Table[1/a^2+2/(L (2 a+L)),{a,L}];
 J=Table[Mod[a,d]/d,{a,L},{d,ds}];
 G=Transpose[J].DiagonalMatrix[w].J;
 b=Transpose[J].w; c=LinearSolve[G,b]; r=1-J.c;
 E=w.(r^2); tail=Reverse[Accumulate[Reverse[w r]]];
 S=Total[Table[If[CoprimeQ[k,L],tail[[k]],0],{k,2,L}]];
 {L,Length[ds],
  Transpose[J].(w r)==ConstantArray[0,Length[ds]],
  Together[E+S-5 EulerPhi[L]/(3 L^2)]==0,N[{E,S},14]}
],{L,{2,6,30,210}}]
~~~

Complete-Q block calculations (ordinary high precision):

~~~wl
Table[Module[{ll=pair[[1]],pp=pair[[2]],kk,ds,ww,jold,jw,jnew,
 fit,resid,hh,ss,eta,dold,dw,du,exact,trace,cap},
 kk=ll pp; ds=Rest[Divisors[ll]];
 ww=N[Table[PolyGamma[1,a/kk]/(Zeta[2] kk^2),{a,kk}],80];
 jold=Table[Mod[a,d]/d,{a,kk},{d,ds}];
 jw=Table[Mod[a,d]/d,{a,kk},{d,Append[ds,pp]}];
 jnew=Table[Mod[a,pp d]/(pp d),{a,kk},{d,ds}];
 fit[mat_]:=mat.LinearSolve[
  Transpose[mat].DiagonalMatrix[ww].mat,Transpose[mat].ww];
 resid=1-fit[jw];
 hh=jnew-jw.LinearSolve[Transpose[jw].DiagonalMatrix[ww].jw,
  Transpose[jw].DiagonalMatrix[ww].jnew];
 ss=Transpose[hh].DiagonalMatrix[ww].hh; eta=Transpose[hh].(ww resid);
 dold=ww.((1-fit[jold])^2); dw=ww.(resid^2);
 du=ww.((1-fit[Join[jw,jnew,2]])^2);
 exact=eta.LinearSolve[ss,eta]; trace=Tr[ss];
 cap=N[2/(Zeta[2] pp) Total[1/ds],80];
 {ll,pp,Length[ds],
  N[{dold,dw,du,dold-dw,dw-du,eta.eta/trace,eta.eta/cap},14],
  Abs[exact-(dw-du)]<10^-60,trace<=cap}
],{pair,{{2,3},{6,5},{30,7}}}]
~~~

Density norm calculation:

~~~wl
Table[Module[{ww=N[Table[
 PolyGamma[1,a/ll]/(Zeta[2] ll^2),{a,ll}],60],v},
 v=ll Total[ww^2]; {ll,N[v,16],2 ll/5<=v<=2 ll/5+2/ll}
],{ll,{2,6,30,210}}]
~~~
