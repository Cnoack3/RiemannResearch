# Actual source resolvent advance
7 October 2026 (UTC).

Starting main: 249c416bf1b04e2ac853d0d70177aa45c44ddfbd.

## Established advance

The actual complete compact source has negligible spectral mass above every
fixed positive multiple of the conductor, on the explicit fourfold sequence.
The proof uses an exact arithmetic identity for the legal corrected trial
and the already established unconditional canonical Mobius energy limit.
It assumes neither RH nor a new arithmetic convergence provider.

At spectral stage n=4m the legal stage is finiteSpace(4m+3), the physical
cutoff is N=4m+4, and the source is the literal twoThreeDual.
Every conductor and every source weight is retained.

## Exact arithmetic identity, before estimation

Write A_Y=canonicalMobiusHilbert Y and
D_h f(j)=h f(floor(j/h)). The exact Hilbert identity is

u_N = compactCorrectedHilbert N
    = 14 A_(4m+3) - 13 D_2 A_(2m+1) + 3 D_4 A_m.

The compact shifted Mobius floor sum separates into the three ordinary
Mobius sums. Its final summand cancels the last boundary-charge increment.
All three canonical boundary conductors are N; no boundary residue is omitted.

The complete signed squared norm is

||u_N||^2 =
  196||A_(4m+3)||^2 + 338||A_(2m+1)||^2 + 36||A_m||^2
  -364 <A_(4m+3),D_2 A_(2m+1)>
  +84 <A_(4m+3),D_4 A_m>
  -78 <D_2 A_(2m+1),D_4 A_m>.

The factors 338 and 36 include the exact dilation norms
||D_h f||^2=h||f||^2. Only after this full equality do we estimate:

||u_N||^2 <=
  3(196||A_(4m+3)||^2+338||A_(2m+1)||^2+36||A_m||^2).

The existing unconditional canonicalMobiusHilbert_sublinear theorem gives

||u_(4m+4)||^2/(4m+4) -> 0.

Declarations in RH/ParetoCompactTrialEnergy.lean:
- compactShiftedMobius_floor_sum_eq_dilations
- compactCorrectedTrial_floor_expansion_all
- compactCorrectedTrial_succ_floor_expansion
- compactCorrectedHilbert_fourfold_eq_canonical
- compactCorrectedHilbert_fourfold_norm_sq_exact
- compactCorrectedHilbert_fourfold_norm_sq_le
- compactCorrectedHilbert_fourfold_sublinear

## Exact complete-source resolvent and variational completion

For all actual weights w_i>=0 and eigenvalues lambda_i>=0 define

F(t)=sum_i w_i/(t+lambda_i),
R(t)=sum_i [w_i lambda_i/(1+lambda_i)]/(t+lambda_i),
D(t)=sum_i w_i lambda_i/(t+lambda_i).

The full sums satisfy, for t>0,

D(t)=B-tF(t),
(t-1)R(t)=tF(t)-F(1),
R(1)=S,

R(t)-T/(t+L)
 = sum_i [w_i lambda_i/(1+lambda_i)](L-lambda_i)
          /[(t+lambda_i)(t+L)].

Here B is literal source mass, T is complete correction and S is the
complete optimizer-tail square. The identities include t=1.

The head adjoint supplies the actual source weights in the constructed
full eigenbasis. With J the isometric head inclusion, A the whole physical
tail map, x_t=regularizedHead(A,t,t J* v), and any legal head coefficient c,
the exact physical loss identity is

t||v-Jc||^2+||Ac||^2
 = t||v||^2-headResolvent(A,t,t J* v)
   +t||x_t-c||^2+||A(x_t-c)||^2.

The signed source pairing and BOTH nonnegative remainder squares remain
in the identity. Homogeneity gives headResolvent(A,t,t J* v)=t^2F(t).

The actual source mass is exactly B=||v||^2-e_N, with e_N the literal
head-projection error square. Thus the stage application yields

D(t) <= ||v-Q_Nu||^2+||(I-Q_N)u||^2/t-e_N.

For the actual compact trial, the already supplied charge estimate and
full Pythagorean identity give

0<=D(t)<=q_N^2+||u_N||^2/t,
q_N=compactReciprocalSum N ->0.

Every weight above t contributes at least half its mass to D(t), hence

highMass(t)<=2D(t).

Consequently, for EVERY fixed c>0,

D_(4m)(c(4m+4))->0,
highMass_(4m)(c(4m+4))->0.

These are checked actual-source theorems, not generic-provider assumptions.

## Full contrast certificates

Put Phi(x)=log(1+log(1+x)) and
C=sum_i [w_i lambda_i/(1+lambda_i)](Phi(L)-Phi(lambda_i)).
The generic finite results retain the entire resolvent and give

C >= [Phi(L)-Phi(r)](t/r)[(r+t)R(t)-T]    (0<r<=L,t>0),

C >= [Phi(L)-Phi(r)](T-highMass(r))       (0<=r<=L).

Together with the previous exact M=Phi(L)T-C+P identity, the second implies
the finite moment inequality

M<=Phi(r)T+[Phi(L)-Phi(r)]highMass(r)+P.

No strict normalized double-log saving is inferred. For a polynomial
quadratic cap and a conductor-scale r, the outer-log gap is bounded.
The asymptotic additive log(2) interpretation is a paper consequence;
its limit is not a separate new Lean theorem in this checkpoint.

## Sharper explicit sufficient arithmetic target

RH/ParetoConductorTailCriterion.lean is a conditional research reduction.
It assumes ONLY the following substantive arithmetic provider:

Open: for some B>=0 and k_m->infinity,
      (4k_m+4) S_(4k_m)<=B eventually.

All source-escape and geometric limit inputs are internally supplied.
For every c>0 the existing complete threshold inequality gives

T_(4k_m) <= [1+c(4k_m+4)] S_(4k_m)
             +highMass_(4k_m)(c(4k_m+4)).

Using S->0, T->delta and the new high-mass limit yields delta<=cB
for every c>0. Therefore delta=0, and the established compact-source
criterion yields RiemannHypothesis.

Declarations:
- riemannHypothesis_of_compactSpectrum_fourfold_cofinal_bounded_tail
- riemannHypothesis_of_compactSpectrum_fourfold_bounded_tail

No provider for the displayed bound has been proved. No converse from RH
to bounded conductor-times-tail energy is asserted.

## Recommended next calculation

Estimate the literal S_(4m) from the original full head/tail Gram problem,
with the exact signed twoThreeDual source and every composite conductor
interaction retained. Aim for a bounded conductor-times-tail budget on a
cofinal subsequence, or supply the existing strict cofinal contrast budget.

The new PNT estimate ||u_N||^2=o(N) alone does not bound N*S_N.
A positive escaped source weight at lambda_N=N/log N would satisfy
highMass(cN)->0 for every c>0 while N*S_N grows like log N.
This abstract example explains why the new moving-cutoff theorem cannot
by itself close RH; it is not asserted to model the actual arithmetic spectrum.

## Verification and provenance

The coherent candidate containing all four developments passed Lean with
exit 0 and no warnings. Decisive source-escape, threshold-contrast and cofinal
RH-consumer axiom audits reported only propext, Classical.choice, Quot.sound.
Local hypotheses in the conditional consumer remain visible in its type.

Wolfram independently checked the fourfold sequence identity for m=1,...,8
and physical sites j=0,...,80; all checks returned True. Scalar resolvent
and signed completion computations were also checked. These computations
were development checks; Lean supplies the proofs.

Literature consulted for strategy and context:
- W. Ehm, On the Nyman-Beurling criterion for the Riemann hypothesis,
  https://arxiv.org/abs/2405.06349, full Gram analysis in Section 8.
- T. Tao, A remark on partial sums involving the Mobius function,
  https://arxiv.org/abs/0908.4323, unconditional reciprocal Mobius context.
- F. Alouges, S. Darses and E. Hillion, A probabilistic Nyman-Beurling
  criterion for the Riemann hypothesis,
  https://doi.org/10.5802/jtnb.1227, approximation versus coefficient control.

The new exact decomposition and assembly were developed for the requested
task. No novelty claim is made. The PNT asymptotic is reused from the existing
verified project, not inferred from Wolfram or a numerical experiment.

The preceding GitHub CI run for 249c416 failed after incomplete build logs,
without a recorded Lean compiler error. Its underlying cause was not
established; this development is accepted only after checkpoint validation.
