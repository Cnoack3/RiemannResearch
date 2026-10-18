# Lattice coordinates and RH closure (2026-10-18)

Source: user's lattice, CRT, log_* and exp_* proposal. Baseline a05e887073b458c9317d647b463b1fd095439363 confirmed through GitHub. No novelty claim.

## New Lean results

Analysis/SquarefreeCumulantCoordinates.lean checks three-prime triangular
composition/inversion, squarefree exp/log polynomial inverses, exact synthesized
range/predicate invariance, and submodule membership of seven-atom synthesis.

Analysis/PrimitiveRegularization.lean adds the exact affine correction
q J(u+t v)=q J(u)-b^2+(q t-b)^2, with q=||Tv||^2+lambda||v||^2
and b=<e-Tu,Tv>-lambda<u,v>, and its strict-budget consumer.

RH/QLatticeRegularization.lean transfers the squarefree closure criterion
through explicitly surjective finite-stage coordinates, checks three-prime
physical range/closure and complete objective invariance, and proves the
four-site counterexample to representing g2*g3 by g2,g3,g6. That obstruction
concerns the finite span only, not the full closed squarefree span.

Saved sources passed job job_3PR19IOWhRis5O-GjN0ZMZZZoa2d70G_ with exit_code=0,
verified=true. Eight selected axiom reports contain only subsets of propext,
Classical.choice and Quot.sound. Final publication is separately gated by
the checkpoint.

## Open obligations

Conditional research reduction: strict_value_of_correction_certificate.
Open: a legal family supplying its complete signed inequalities as lambda
tends to zero. No new unconditional RH theorem follows.

Unrestricted cumulants parametrize exactly the same finite trials. A useful
structured family needs a quantitative full-Q norm estimate. Full exponential
coordinates can turn a convex quadratic objective into a generally nonconvex
polynomial of degree six already at three primes.

For nonlinear coefficient f_*, invertible f'(0) gives finite triangular
invertibility. For linear operator f(C), the distinct condition is f(0)!=0.
In particular log Z=C is singular although exp(±C) is invertible.

The arbitrary-finite-prime cover theorem and infinite Banach-algebra argument
are paper-level results, not new Lean declarations here. The inequality
||g_d||_Q^2<=2/(zeta(2)d) gives bounded synthesis from squarefree l1(d^-1/2).
Disjoint convolution is submultiplicative there; exp_* converges globally
and log_*(1+c) for norm(c)<1. This is a sufficient domain, not a necessary
characterization of physical closure, and synthesis is not multiplicative.

Index caution: experiments use first m primes; Lean primorialPeriod n is
primorial(n+3), so stage4 has period210 and stage0 already period6.

Next steps: formalize general lattice convolution and full primitive Gram;
compute optimal cumulants and test interaction truncations in the actual
objective; certify signed correction gains; prove one uniform provider
for a specified positive lambda_N -> 0; justify an infinite synthesis domain.

## Primary sources

- Bagchi, https://arxiv.org/abs/math/0607733, Remark8: external squarefree
  closure/RH equivalence; analytic RH-to-closure is not newly formalized.
- Rota, https://doi.org/10.1007/BF00531932: incidence algebra/Boolean Mobius.
- Li and MacHenry, https://arxiv.org/abs/1009.1892: arithmetic LOG/EXP antecedent.
- Sinclair, https://arxiv.org/abs/2606.10870, Section4, 2026 preprint:
  squarefree nilpotent log/exp and cumulant terminology.
- Bjorklund et al., https://arxiv.org/abs/cs/0611101: fast subset convolution.

---

# Finite lattice and full-Q verification

Computations used the Wolfram Language evaluator. Exact algebra/rational checks are distinguished from approximate optimization. The period210 rational certificate was independently reproduced with Python Fraction.

## Incidence log/exp is the useful linear interpretation

Let Z[S,T]=1 if T⊆S; C[S,T]=1 if T⊆S and |S∖T|=1; all subsets of an m-element set, indexed by bitmasks. Then C^k[S,T]=k! if T⊆S and |S∖T|=k, and zero otherwise. Consequently exp(C)=Z, log(Z)=C, exp(-C)=Mobius, C^(m+1)=0. Wolfram verifies all identities for m=2,3,4 exactly, determinant Z=1.

As an operator on coefficient vectors, exp(-C) is LINEAR. Applied after divisor-square scaling it yields the known primitive basis:
Psi_r = sum_{d|r,d>1} d^2 mu(r/d) g_d.
For primes 2,3; 2,3,5; 2,3,5,7, the nonempty basis matrices have dimensions/ranks3,7,15 and determinants1296,656100000000,14305686902419853283210000000000000000, equal L^(2^m). Each finite legal span and hence the union's closure is unchanged.

For any polynomial/analytic finite functional calculus f(C), invertibility is equivalent to f(0)≠0. Thus many f_* provide alternate coordinates; this alone does not shrink distance to target or prove closure. In plain Euclidean coefficient norm ||Z||2=phi^m, phi=(1+sqrt5)/2. Wolfram gives2.618033988749895,4.236067977499789,6.854101966249684. Uniform infinite operator calculus needs separate norm control; finite span equality itself does not require such uniform bounds.

## Subset-convolution identities and nonlinear obstruction

For disjoint subset convolution (f*g)(S)=sum_{T⊆S}f(T)g(S∖T), augmentation h(empty)=0 implies h^(m+1)=0. Exact Wolfram checks m=2,3,4:
- exp_*(sum i*x_i)=product_i(1+i*x_i);
- log_* of this multiplicative array returns singleton coefficients;
- log_*(exp_*(h))=h for generic rational test h(mask)=mask/(mask+1).

If instead coefficients are actual functions and products are pointwise, legality is lost:
g2*g3 not in span{g2,g3,g6}. Evaluation at n=1,2,3,4 gives the augmented matrix
[[1/2,1/3,1/6,1/6],
 [0,2/3,1/3,0],
 [1/2,0,1/2,0],
 [0,1/3,2/3,0]]
with exact determinant1/36. Its first three columns have rank3, augmented rank4. In log_*(1+sum nonempty g_d x_S), coefficient for {2,3} is g6-g2*g3, outside that finite legal space. This does not by itself prove exclusion from the infinite closed span; it blocks the automatic finite-legality inference.

## CRT: divisibility independence versus residues

For I_d=1_{d|n}, E_Q I_d=d^-2, hence coprime divisibility indicators are independent. The exact difference Gram for d,e>1 is
H_de=1/(de)-1/(d e^2)-1/(e d^2)+1/lcm(d,e)^2.
For the primitive basis Psi2=4g2,Psi3=9g3,Psi6=36g6-4g2-9g3, difference Gram is
[[4,2,2],[2,12,4],[2,4,28]].
The full primitive Gram from period weights is approximately
[[3,4.218844081711054,5.531908571977376],
 [4.218844081711054,13.58783869415979,16.10210743032760],
 [5.531908571977376,16.10210743032760,68.57134368083905]].
These are different geometries. Full residue CRT coordinates are not Q-independent: covariance of odd and n≡1 mod3 is approximately0.1187437278859297483.

## Full-Q regularization experiment

a=1/zeta(2). For L=product first M primes and d>1 divisors L, G_de=sum_{j=1}^L g_d(j)g_e(j) psi1(j/L)/(zeta(2)L^2).
b_d=a/d; coefficient vector c=(H+lambda G)^(-1)b; alpha=a-b.c.
All signed cross terms and full lambda G are present. This is numerical, at50-digit working precision.

Columns M,L,dimension,lambda,alpha/lambda,alpha,primitive energy,residual:
1,2,1,.1,2.64136068209,.264136068209,.239854209520,.240150647257
1,2,1,.01,24.1102922034,.241102922034,.273070109047,.238372220944
1,2,1,.001,238.628714476,.238628714476,.276766215872,.238351948260
1,2,1,.0001,2383.79456759,.238379456759,.277139948325,.238351742764
2,6,3,.1,1.47820674336,.147820674336,.427790838601,.105041590476
2,6,3,.01,10.5107871742,.105107871742,.527824292155,.0998296288204
2,6,3,.001,100.301939794,.100301939794,.540252424452,.0997616873700
2,6,3,.0001,998.151399385,.0998151399385,.541525989001,.0997609873396
3,30,7,.1,1.11526825181,.111526825181,.514808420006,.0600459831803
3,30,7,.01,5.73170588174,.0573170588174,.733606905403,.0499809897634
3,30,7,.001,50.5008580752,.0505008580752,.783339357358,.0497175187178
3,30,7,.0001,497.932619726,.0497932619726,.789125469223,.0497143494257
4,210,15,.1,.958984099254,.0958984099254,.557059247229,.0401924852025
4,210,15,.01,3.66939355511,.0366939355511,.857779461344,.0281161409376
4,210,15,.001,28.0392269136,.0280392269136,1.14231088961,.0268969160240
4,210,15,.0001,269.787378208,.0269787378208,1.21784455630,.0268569533651

M4,lambda=.1 has alpha<lambda; none of the displayed smaller penalties do. This is not evidence of a penalty-uniform asymptotic provider.

## Rigorous finite rational certificate in full Q

Set L=210,lambda=1/10 and
d=(2,3,5,6,7,10,14,15,21,30,35,42,70,105,210)
c=(9783,9770,9549,-8824,9426,-7399,-5918,-5955,-4698,7574,-4122,5233,2704,363,-6191)/10000
F=sum c_d g_d.

Exact Wolfram arithmetic verifies:
delta=DeltaF(1)=sum c_d/d=221089/262500;
c^T H c=52823902806611/115762500000000;
B=max_{1<=n<=210}|F(n)|=1224169/1050000<7/6;
sum_{n=1}^{210}F(n)^2/n^2<229/250.

Since F is210-periodic, its complete energy satisfies
||F||_Q^2 <= a[229/250 + (7/6)^2/210]
by integral bound sum_{n>210}n^-2 <=1/210.

For normalization let S100=sum_{n=1}^{100}1/n^2.
Exact rational checks:
S100+1/101>1028/625;
S100+1/100<329/200;
6079/10000<200/329;
625/1028<76/125.
Integral bounds therefore give6079/10000<a<76/125.

Because1-2delta<0, the FULL objective obeys
J_(1/10)(F)
= c^T H c + a(1-2delta)+(1/10)||F||_Q^2
< c^T H c+(6079/10000)(1-2delta)
  +(1/10)(76/125)[229/250+(7/6)^2/210]
=3715960194137/38587500000000
<963/10000<1/10.

All certificate arithmetic is exact. The numerical minimizer was only used to discover the rational coefficients. The infinite-series inequalities are elementary integral-tail proofs; they have not been submitted to Lean by this agent. This certifies one finite regularization budget and does not supply lambda_N→0 or prove RH.

## Suggested research route

1. Formalize incidence matrix exp/log and weighted Mobius transform as linear finite basis changes.
2. Formalize the product counterexample to prevent accidental pointwise-functional-calculus closure claims.
3. Formalize an interval-free rational certificate consumer: periodic finite values, norm tail bound, normalization brackets, then J<lambda.
4. Search larger prime sets using sparse cover operators/CRT derivative coordinates while preserving exact full primitive Gram.
5. Seek a scalable rule giving bounded primitive energy as lambda→0, e.g. signed cancellation estimates stable under adjoining primes. This is the essential open analytic/arithmetic result.
6. Do not call exp/log novel: incidence algebra and Boolean cumulant calculus are established. Potential novelty must reside in a quantitative Q-norm estimate or uniform strict-budget provider.
