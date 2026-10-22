# Exact finite checks for the CRT continuation

Christian Noack research continuation, 20 October 2026 UTC. These Wolfram
programs record auxiliary finite and numerical checks. They do not substitute
for the general Lean proofs. Decimal outputs are not interval certificates.

## Cylinder reconstruction

```wolfram
Module[{periods=Union[Select[Range[2,30],SquareFreeQ],{210}],rows,fail},rows=Table[Module[{ds=Divisors[l],delta,con,basis,rankc,rankb,ns,reconstruct,check},delta=Table[UnitVector[l,a]-UnitVector[l,Mod[a-2,l]+1],{a,l}];con=Table[delta[[a]]-delta[[GCD[a,l]]],{a,l}];basis=Transpose[Prepend[Table[Table[Mod[a,d]/d,{a,l}],{d,Rest[ds]}],ConstantArray[1,l]]];rankc=MatrixRank[con];rankb=MatrixRank[basis];ns=NullSpace[con];reconstruct[v_]:=Module[{h=delta.v,c},c=Table[Total[Table[If[Divisible[d,e],MoebiusMu[d/e]h[[e]],0],{e,ds}]],{d,ds}];Table[v[[l]]-Total[Table[c[[j]]Mod[a,ds[[j]]]/ds[[j]],{j,Length[ds]}]],{a,l}]];check=And[con.basis==ConstantArray[0,{l,Length[ds]}],l-rankc==rankb==Length[ds],And@@Table[reconstruct[v]==v,{v,ns}]];<|"L"->l,"DivisorCount"->Length[ds],"ConstraintRank"->rankc,"Nullity"->(l-rankc),"SynthesisRank"->rankb,"EveryNullspaceBasisReconstructedExactly"->check|>],{l,periods}];fail=Select[rows,Not[#["EveryNullspaceBasisReconstructedExactly"]]&];<|"Arithmetic"->"Exact rational","Periods"->periods,"NumberOfPeriods"->Length[periods],"Failures"->fail,"SelectedRows"->Select[rows,MemberQ[{2,6,30,210},#["L"]]&]|>]
```

## Midpoint and modulus-three checks

```wolfram
(* Exact algebra and complete-Q conditional checks, 20 October 2026.
   The numerical evaluations actually executed in this continuation requested
   30 significant digits, not 80-digit arithmetic. These are numerical
   observations, not interval certificates. All PolyGamma expressions use
   the complete infinite residue weights. Exact symbolic checks are listed
   separately below. Each block is self-contained. *)

(* 1. Exact midpoint identity, rational-weight comparison, optional 10/9
      comparison polynomial. Executed output:
      {0,-2(a-l)(3a+l),True,(x-1)(-1-4x+2x^2)}. *)
{
 FullSimplify[
  2/(l (2 x-l))-2/(l (2 x+l))-1/x^2-l^2/(x^2 (4 x^2-l^2)),
  Assumptions->0<l<x],
 Factor[(5/(3 a^2)-(1/a^2+2/(l (2 a+l)))) 3 a^2 l (2 a+l)],
 FullSimplify[1/a^2+2/(l (2 a+l))<=5/(3 a^2),Assumptions->0<a<=l],
 Factor[(10/9 (1/x^2+1/(x+1))-(1/x^2+2/(2 x+1)))
   9 x^2 (2 x+1)(x+1)]
}

(* 2. Complete-Q modulus-three conditional image of g_2.
      Actual executed code used symbolic A,B in ExactAlgebra, producing
      harmless undefined-symbol warnings and the displayed factorization.
      All numerical requests below are N[...,30]. *)
Module[{a,b,u1,u2,u3,j},
 a=PolyGamma[1,1/3]/(9 Zeta[2]);
 b=PolyGamma[1,2/3]/(9 Zeta[2]);
 u1=1/2-b/(8a);
 u2=1/2-a/(8b);
 u3=3/8;
 j=2u1-u2-u3;
 <|
  "A_B"->N[{a,b},30],
  "ConditionalValues"->N[{u1,u2,u3},30],
  "JumpDefect"->N[j,30],
  "DistanceSquaredLowerBound"->N[j^2/(30 Zeta[2]),30],
  "ExactAlgebra"->Factor[2(1/2-B/(8A))-(1/2-A/(8B))-3/8],
  "ActualFiberValues"->N[{
   PolyGamma[1,1/6]/(36Zeta[2])/(2a),
   PolyGamma[1,5/6]/(36Zeta[2])/(2b),
   PolyGamma[1,1/2]/(36Zeta[2])/(2/9)},30]
 |>
]

(* Executed output, rounded here for readability:
   A=.681931900216303941041026589109
   B=.206956988672584947847862299780
   (u1,u2,u3)=(.462064212605587950701416132800,
              .088119792069965936787117895265,.375)
   J=.461008633141209964615714370334
   J^2/(30 Zeta[2])=.004306737153664817778104267155
   ExactAlgebra=(A-B)(A+2B)/(8AB).
   ActualFiberValues agreed to the requested numerical accuracy.
   No interval-error certificate was requested or returned. *)

(* 3. Exact rational separation and exact residue-mass checks.
      Executed output: {True,b^2/4,
        .00225158185871861714319732140466,8/9,True}. *)
{
 FullSimplify[(a-b)(a+2b)/(8a b)>=1/3,
   Assumptions->a>0&&b>0&&a+b==8/9&&b<=1/4],
 Factor[3a^2-5a b-6b^2-(2a-5b)(3a/2+5b/4)],
 N[1/(270Zeta[2]),30],
 FullSimplify[(PolyGamma[1,1/3]+PolyGamma[1,2/3])/(9Zeta[2])],
 FullSimplify[PolyGamma[1,2/3]/(9Zeta[2])<=1/4]
}

(* Separate exploratory observation, not part of the theorem scope:
   C_6 g_5, C_6 g_7, and C_30 g_7 were evaluated with N[...,25].
   Their square-jump defects were approximately
   -.1479679762968630384164418,
   -.02065667174199616449433225,
   -.001343941418380991553117961, respectively.
   These observations do not constitute a Lean proof or interval certificate. *)
```

## Modulus-six certificate

```wolfram
(* Complete-Q C_6 g_5 obstruction.
   Exact four-term rational fiber certificate. No floating-point input.
   The analytic tail estimate is established in the accompanying Lean
   module QPrimorialSixConditionalObstruction.lean. This file checks the finite rational arithmetic,
   not the analytic estimate or a Lean declaration. *)

Module[{bounds,d,n,r,jumpUpper,smallChecks},
 bounds=Table[
   d=Sum[1/(a+6j)^2,{j,0,3}];
   n=Sum[Mod[a+6j,5]/(5(a+6j)^2),{j,0,3}];
   r=1/(a+24)^2+2/(6(2(a+24)+6));
   {a,d,n,r,n/(d+r),(n+4r/5)/d},
   {a,1,4}];
 jumpUpper=bounds[[1,6]]+bounds[[4,6]]-bounds[[2,5]]-bounds[[3,5]];
 smallChecks={
   bounds[[1,6]]<=214/1000,
   bounds[[4,6]]<=726/1000,
   bounds[[2,5]]>=404/1000,
   bounds[[3,5]]>=561/1000};
 <|
   "Columns"->{"a","D","N","R","ConditionalLower","ConditionalUpper"},
   "Bounds"->bounds,
   "SimpleEndpointChecks"->smallChecks,
   "ExactJumpUpper"->jumpUpper,
   "AtMostMinusOneFortieth"->(jumpUpper<=-1/40),
   "SimpleJumpBound"->214/1000+726/1000-404/1000-561/1000,
   "ExactEnergyLower"->1/(48000Zeta[2])
 |>
]

(* Exact executed jump upper:
   -22720739662914598516622964366473/
     842982011597922834476707992375000.
   AtMostMinusOneFortieth returned True.
   The four SimpleEndpointChecks were additionally executed in Wolfram;
   the returned list was {True,True,True,True,-1/40}, with its final entry
   equal to SimpleJumpBound. *)

(* Exploratory numerical calculation actually executed at 25 requested digits.
   The PolyGamma weights retain the complete infinite Q tail.
   This numerical observation is not needed for the rational certificate. *)
Module[{l=6,p=5,v,j},
 v=Table[
   Sum[PolyGamma[1,(a+l k)/(l p)]/(Zeta[2](l p)^2)
       Mod[a+l k,p]/p,{k,0,p-1}]/
     (PolyGamma[1,a/l]/(Zeta[2]l^2)),
   {a,1,l}];
 j=v[[4]]-v[[3]]-v[[2]]+v[[1]];
 <|"Values"->N[v,25],"Jump"->N[j,25],
   "WitnessDistanceSquaredBound"->N[j^2/(30Zeta[2]),25]|>
]
```
