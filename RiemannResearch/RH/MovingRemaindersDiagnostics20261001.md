# Reproducible Wolfram Language diagnostics

Source listing for [MovingRemaindersVerificationAndResearch20261001.md](MovingRemaindersVerificationAndResearch20261001.md). Copy the code into Mathematica or a Wolfram Language kernel. The complete listing was evaluated successfully on October 1, 2026. The Gram calculations use full physical tails and floating point evaluation; they are not certified interval bounds. Exact countermodel outputs include the identity matrix, zero survivor residuals, and the infinite energy sum 1.

```wolfram
(* October 1, 2026. Full physical tails; numerical diagnostics are not interval proofs.
   Run with a Wolfram Language kernel. The reported run used prec = 35.
   Conductors 2..17: rank 16. Physical prime p has repository row index p-3. *)
prec = 35;
wg[r_, l_] := N[(PolyGamma[0, (r+1)/l]-PolyGamma[0, r/l])/l, prec];
gt[d_, e_] := gt[d, e] = Module[{l = LCM[d,e]},
  Sum[(Mod[r,d]/d)(Mod[r,e]/e) wg[r,l], {r,1,l}] - N[1/(2 d e),prec]];
gn = Table[gt[d,e], {d,2,17}, {e,2,17}];
src = Table[N[1/d,prec], {d,2,17}];
qvec = Table[N[If[OddQ[d], Pi^2/((Pi^2-8)d^2), 0],prec], {d,2,17}];
row[p_] := row[p] = Module[{g,c,gamma,sigma,eta,tp,mass,ap,w},
  g = gn[[1;;p-2,1;;p-2]]; c = gn[[1;;p-2,p-1]];
  gamma = LinearSolve[g,c];
  sigma = gn[[p-1,p-1]] - c.gamma;
  eta = src[[p-1]] - gamma.src[[1;;p-2]];
  tp = qvec[[p-1]] - gamma.qvec[[1;;p-2]];
  mass = N[Zeta[2] Product[1-1/pp^2,{pp,Select[Range[2,p-1],PrimeQ]}],prec];
  ap = (mass/(mass-1))/p^2; w = ap^2/sigma;
  {p,sigma,eta,tp,ap,w,(eta-ap)/ap,-1+(qvec[[p-1]]+eta-tp)/ap}];
gaps[j_] := Module[{pp,left,right,rr,ul,ur,kap,g,model},
  pp = Select[Range[2^j+3,2^(j+1)+2],PrimeQ];
  left = Select[pp,#<2^j+2^(j-1)+3&]; right = Complement[pp,left];
  rr = Association@Table[p->row[p],{p,pp}];
  ul = Total[rr[#][[6]]&/@left]; ur = Total[rr[#][[6]]&/@right];
  kap = ul ur/(ul+ur);
  g = Total[rr[#][[6]]rr[#][[7]]&/@right]/ur -
      Total[rr[#][[6]]rr[#][[7]]&/@left]/ul;
  model = Total[rr[#][[6]]rr[#][[8]]&/@right]/ur -
      Total[rr[#][[6]]rr[#][[8]]&/@left]/ul;
  {j,left,right,kap,g,model,kap g^2,kap (g-model)^2,kap model^2}];
paretoDiagnostics = {
  N[gt[2,2]-(Log[2]-1/2)/4,25],
  N[Table[row[p],{p,{3,5,7,11,13,17}}],12],
  N[Table[gaps[j],{j,{3}}],12]};

(* Exact coefficient-dual checks. The proof for arbitrary primes is in the report. *)
u[p_,k_] := Piecewise[{{2,k==1},{(p-1)p,k==p-1},{-p(p+1),k==p}},0];
g[d_,k_] := Mod[k,d]/d;
pair[d_,p_] := Sum[g[d,k] u[p,k]/(k(k+1)),{k,1,p}];
dualDiagnostics = {
  Table[FullSimplify[pair[d,p]-Boole[d==p]],
    {p,{3,5,7,11,13,17}},{d,2,20}],
  FullSimplify[2+(p-1)p+p(p+1)-2(p^2+1)]};

(* Exact abstract countermodel. It is not the arithmetic residue dictionary. *)
ss[n_] := n(n+1)/2;
hh[n_,k_] := If[k==n,Sqrt[ss[n-1]/ss[n]],
  If[k<n,-Sqrt[n/(ss[n-1]ss[n])]Sqrt[k],0]];
zz[n_,k_] := If[2<=k<=n,Sqrt[k],0];
eta[n_] := Sqrt[n/(ss[n-1]ss[n])];
aa[n_] := Sqrt[n ss[n-1]/ss[n]];
abstractDiagnostics = {
  FullSimplify[Table[Sum[hh[n,k]hh[m,k],{k,1,9}],{n,2,9},{m,2,9}]],
  Table[FullSimplify[Sum[zz[n,k]hh[n,k],{k,1,9}]-eta[n]],{n,2,9}],
  FullSimplify[eta[n]/aa[n],Assumptions->n>1],
  Sum[4/(n(n-1)(n+1)),{n,2,Infinity}],
  FullSimplify[Sum[4/(n(n-1)(n+1)),{n,2,nn}],
    Assumptions->Element[nn,Integers]&&nn>=2]};
{paretoDiagnostics,dualDiagnostics,abstractDiagnostics}
```
