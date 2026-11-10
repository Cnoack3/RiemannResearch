# Montgomery pair correlation: Parseval, raw form factors, and remaining estimates

Date: 2026-11-10. Starting revision: ddffaf3b485734d24423da3945cbd9be880f01a2.
Source task: Montgomery_Pair_Correlation_Lean_Handoff.md.

## Outcome and mathematical boundary

This development proves exact finite arithmetic, Haar, Fourier-inversion, and
Poisson-integral identities. It does not prove Montgomery's pair-correlation
conjecture, RH, an unconditional raw low-support asymptotic, or a high-support
asymptotic. No such asymptotic is inserted as a project axiom.

The strongest new Parseval statement is cancellation of the signed axis-density
correction in every even moment of every homogeneous finite Fourier polynomial.
Writing its total degree as d, every frequency of P^r has total degree r*d.
Differences between frequencies of P^r have degree zero, whereas the correction
has nonzero Fourier support only along individual coordinate axes. Thus
integral |P|^(2r) density = 0 exactly. This works for every nonnegative integer r.
It does not require positivity of 1+density, and no such positivity is asserted.

For a linear prime-coordinate polynomial P(z)=sum_p c_p z_p, the checked fourth
moment is
  integral |P|^4 dm = 2 (sum_p |c_p|^2)^2 - sum_p |c_p|^4.
The same formula holds after multiplication of the Haar integrand by
1+density. This is a Haar identity, not an actual-zero moment asymptotic.

The arithmetic counterpart uses Mathlib's Nat.cardFactors for Omega:
positive n,m of equal Omega have zero PrimeBandlimitedWeil.resonance.
Specialization of the existing actual Guinand-Weil theorem removes that
resonance while retaining both pole terms and the complete gamma integral.

## Why homogeneous Parseval does not close high support

The exact cancellation concerns multiplicative prime-power ratios.
The unresolved mean-square terms involve additive close pairs n,n+h.
For a smoothed homogeneous moment the proposed transfer still requires
D^k+1<T and its gamma error bound. This controls polynomials of total length
below the height; it does not yield the fixed-alpha>1 range X=T^alpha.
Letting the finite torus grow supplies no uniform estimate for these
height-dependent tests by itself.

## Formal declaration map

See [the focused theorem catalog](THEOREM_CATALOG_MONTGOMERY_PARSEVAL_20261110.md) for all 83 theorem/lemma declarations and 24 definitions across 11 modules, with their hypotheses.

## Exact arithmetic obligation

For a(n)=Lambda(n)-1, let V(N,H) be the squared centered short-interval sum,
D(N,H) its diagonal, and C(N,H) its complete signed off-diagonal contribution.
ShortIntervalVariance proves the exact indexing identity V=D+C, and
  V-HN(log N-log H) = (D-HN log N) + (C+HN log H).
All integer endpoints are retained, including degenerate N=0 and H=0.
centeredVariance_error_le makes both error estimates explicit hypotheses.

The unresolved interior-range target is
  C(N,H) = -HN log H + o_epsilon(HN log N),
uniformly for N^epsilon <= H <= N^(1-epsilon).
The required term has a negative main term. Bounding absolute correlations
individually or setting the off-diagonal to zero does not supply this result.
The relation H about X/T with X=T^alpha explains its relevance above alpha=1.
The classical transfer also requires the RH/uniformity/Tauberian inputs
specified in the literature; the finite variance identity alone implies no
pair-correlation limit.

## Correction to the supplied handoff

Section 4 quoted a relative-error version of the unconditional complex-zero
low-support theorem. The authors explicitly correct that version in
Baluyot--Goldston--Suriajaya--Turnage-Butterbaugh,
arXiv:2501.14545v3 (2026), Section 3, equations (3.2) and (3.5):
https://arxiv.org/html/2501.14545v3#S3

For the cutoff 0<gamma,gamma'<=T, their (3.5) gives, after normalization and
x=T^alpha,
  Fsharp_T(alpha)
    = T^(-2 alpha) (log T + O(1))
      + alpha + O((log T)^(-1/2)),
uniformly 0<=alpha<=1.
The error cannot be replaced throughout this interval by the relative error
quoted in the handoff. The authors identify the issue already at x=c log T.
Their earlier applications remain valid. This correction is external
literature evidence, not a newly formalized asymptotic theorem.

Fsharp retains real parts of zeros. Fraw uses only ordinates but counts all
actual zeros and all multiplicities. Reflection can rewrite the sharp signal
with cosh horizontal factors; it does not remove those factors.

## Exact horizontal comparison

MontgomeryHorizontalTransfer identifies the sharp integral with the double sum
  sum_(rho,sigma) exp(u(rho-sigma)) * 4/(4-(rho-sigma)^2),
counting actual multiplicities. It uses reflection of the second zero;
integrability is proved from the critical strip and the bilateral transform.

With Montgomery normalization N_T=T log T/(2*pi), it proves
  |sqrt(Fsharp_T(alpha))-sqrt(Fraw_T(alpha))| <= sqrt(H_T(alpha)),
where
  H_T(alpha)=N_T^(-1) integral e^(-2|s|)
    |coshCorrection(T, alpha log T+s)|^2 ds.
This is an unconditional comparison inequality, not a proof that H_T tends
to zero. The original exponential horizontal factor remains in the exact
coshCorrection; it has not been bounded by a constant.

## What still needs analytic providers

1. **Completed in the continuation:** positive complex-shifted sech smoothing,
   its complete transform, and the actual-zero smoothing bridge. See
   [the analytic-provider ledger](MontgomeryAnalyticProviders20261110.md).
2. The complete gamma remainder with the required uniform row/operator bound.
   No proposed O((D/T)^(r+1)/log T) rate is claimed proved here.
3. The separate sharp compression norm estimate. Haar L2 control alone is
   insufficient for an operator norm on growing truncations.
4. The corrected BGSTB low-support asymptotic as a Lean theorem.
5. A vanishing horizontal defect, or another justified transfer to raw pairs.
6. A signed close-shift estimate or a high-frequency raw-probe asymptotic.
7. Uniformity at the alpha=1 transition and concentration control before any
   weak limit is inferred from estimates away from the transition.

The finite shifted probe is available for arbitrary real frequencies and
weights, so log primes and log(p)/p may be substituted directly. An exact
identity expressing an unknown high-frequency average in terms of another
unknown average does not estimate it.

The finite prime DPP is a comparison object. Its count is order log D,
whereas the zero normalization is order T log T. A sine-shaped normalized
kernel does not identify the raw zero process with that DPP.

## Literature used and the role of each source

- Montgomery (1973), "The pair correlation of zeros of the zeta function":
  https://websites.umich.edu/~hlm/paircor1.pdf
  Original raw form factor and Fourier-test interpretation; its low-support
  theorem assumes RH.
- Baluyot et al., Acta Arithmetica 214 (2024), 357--376:
  https://doi.org/10.4064/aa230612-20-3
  Complex-zero unconditional low-support method, reflection and positive
  kernels. Use the correction above for the uniform error term.
- Baluyot et al., arXiv:2501.14545v3 (2026):
  https://arxiv.org/html/2501.14545v3
  Section 3 corrects the error term and treats both full and dyadic cutoffs.
- Goldston--Montgomery (1987), "Pair correlation of zeros and primes in short
  intervals", pp. 183--203:
  https://doi.org/10.1007/978-1-4612-4816-3
  Classical conditional equivalence motivating the signed variance target.
- Languasco--Perelli--Zaccagnini, JMAA 394 (2012), 761--771:
  https://doi.org/10.1016/j.jmaa.2012.04.058
  Quantitative error transfers; uniformity cannot be omitted.
- Montgomery--Soundararajan, "Primes in short intervals" (2004):
  https://arxiv.org/abs/math/0409258
  Conditional moment analysis and the variance scale involving log(N/H).
  It is not an unconditional provider for the needed off-diagonal estimate.
- Goldston--Lee--Schettler--Suriajaya, Mathematika 72 (2026), e70127:
  https://doi.org/10.1112/mtk.70127
  PCC for the full ordinate multiset implies asymptotically all zeros are
  simple and critical, without additionally assuming RH. This conclusion
  allows an exceptional zero set and is weaker than RH.
- Das--Ismoilov--Ramos, "Fourier optimization and pair correlation problems":
  https://arxiv.org/abs/2502.05106
  Bounds for averaged form factors under stated spectral inputs; not a
  high-support equality or an unconditional PCC proof.
- Hough--Krishnapur--Peres--Virag, "Determinantal processes and independence":
  https://arxiv.org/abs/math/0503110
  Positive contraction kernels and finite-rank DPP interpretation; no
  identification with zeta zeros.
- Garrett's Guinand explicit-formula notes:
  https://www-users.cse.umn.edu/~garrett/m/mfms/notes_2015-16/04_Guinand_explicit_fml.pdf
  Pole/gamma bookkeeping behind the existing band-limited Weil specialization.
- DLMF 5.9.E16:
  https://dlmf.nist.gov/5.9.E16
  Digamma integral for a possible gamma-remainder provider. The derivative
  bounds and uniform endpoint estimates remain to be formalized.

## Independent Wolfram checks

Wolfram was used for finite validation and pattern recognition, never as a
Lean proof oracle. Symbolic differences for the bilateral Cauchy transform,
the centered variance identity, and the complex Gram transform returned zero.
The fourth Haar moment for coefficients {1+i,2-i,3} was 402 by both ordered-pair
frequency matching and the closed formula. The even moments of orders
2,4,6,8 were {16,402,12184,408166}.

A centered-von-Mangoldt finite experiment at N=10000 gave:

| H | D/(HN log N) | C/(-HN log H) | V/(HN log(N/H)) |
|---|---:|---:|---:|
| 10 | 0.7793584339 | 1.147624191 | 0.6566031816 |
| 100 | 0.7816863734 | 1.011111920 | 0.5522608264 |
| 1000 | 0.8004556205 | 0.9877368812 | 0.2386118385 |

These are finite values with full endpoints, not asymptotic evidence sufficient
to discharge the theorem inputs. They emphasize the large signed cancellation
and the danger of replacing the off-diagonal by an absolute bound.

## Verification

The publication checkpoint is responsible for auditing and building the full
Bazel target //:RiemannResearch and revalidating the integration revision.
The checkpoint job and final commit are reported in the chat; a failed job or
an isolated snippet is never a whole-project success.

## Reproducible Wolfram regression code

The following cells are independent finite checks; their outputs are not used
to discharge any Lean theorem.

```wolfram
Clear[s,u,z,w];
FullSimplify[
 Integrate[Exp[-2 Abs[s]] Exp[(u+s) (z+Conjugate[w])],
   {s,-Infinity,Infinity},
   Assumptions -> Element[u,Reals] && Abs[Re[z]]<1/2 &&
     Abs[Re[w]]<1/2, GenerateConditions -> False] -
 Exp[u (z+Conjugate[w])] 4/(4-(z+Conjugate[w])^2),
 Assumptions -> Element[u,Reals] && Abs[Re[z]]<1/2 &&
   Abs[Re[w]]<1/2]
(* 0 *)

coeffs={1+I,2-I,3};
moment[k_] := Total[
 (Multinomial@@#)^2 Times@@(Abs[coeffs]^(2 #)) & /@
 Select[Tuples[Range[0,k],Length[coeffs]],Total[#]==k&]];
Table[moment[k],{k,1,4}]
(* {16,402,12184,408166} *)

Clear[a,n,x,j,h];
a[n_] := MangoldtLambda[n]-1;
nn=10000;
Table[
 dd=Sum[Sum[a[x+j+2]^2,{x,0,nn-1}],{j,0,hh-1}];
 vv=Sum[Sum[a[x+j+2],{j,0,hh-1}]^2,{x,0,nn-1}];
 cc=vv-dd;
 N[{hh,dd/(hh nn Log[nn]),cc/(-hh nn Log[hh]),
    vv/(hh nn Log[nn/hh])},20],
 {hh,{10,100,1000}}]
(* A direct exact evaluation may be slow; prefix sums of numerical a and a^2
   give the same finite endpoints efficiently. *)

```
