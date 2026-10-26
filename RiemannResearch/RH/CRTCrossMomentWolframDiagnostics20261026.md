# Wolfram diagnostics for squarefree cumulative cross moments

Date: 2026-10-26. These are the exact evaluated finite scripts. They use complete
polygamma progression sums but floating arithmetic; they are not proof certificates.
Run each block in a fresh Wolfram kernel. See CRTCrossMomentResearch20261026.md for
rounded outputs and the precise distinction from the Lean theorems.

## squarefree_wolfram_stages_5_10_15.wl

```wolfram
ClearAll[w,v,g,stage];
prec=50; zz=N[Zeta[2],prec];
w[m_Integer,a_Integer]:=w[m,a]=PolyGamma[1,N[a/m,prec]]/(zz m^2);
v[m_Integer,a_Integer]:=v[m,a]=(PolyGamma[1,N[a/m,prec]]/m^2+(PolyGamma[0,N[a/m,prec]]-PolyGamma[0,N[(a+1)/m,prec]])/m)/zz;
g[d_Integer,n_Integer]:=Mod[n,d]/d;
stage[cap_Integer]:=Module[{ds,L,G,J,mu,nu,c,alpha,ns,bs,us,es,qs,aws,mc,ap,h,idx,summary},
ds=Select[Range[2,cap+1],MoebiusMu[#]!=0&]; L=LCM@@ds;
G=Table[With[{m=LCM[d,e]},Sum[g[d,a]g[e,a]w[m,a],{a,1,m}]],{d,ds},{e,ds}];
J=Table[With[{m=LCM[d,e]},Sum[g[d,a]g[e,a]v[m,a],{a,1,m}]],{d,ds},{e,ds}];
mu=Table[Sum[g[d,a]w[d,a],{a,1,d}],{d,ds}];
nu=Table[Sum[g[d,a]v[d,a],{a,1,d}],{d,ds}];
c=LinearSolve[G,mu]; alpha=LinearSolve[G,nu-J.c];
ns=Range[20cap]; qs=1/(zz ns^2); aws=N[ns/(8+Log[ns])^2,prec];
bs=Table[alpha.(g[#,n]&/@ds),{n,ns}];
us=Table[With[{a=1+Mod[n-1,L]},(1-c.(g[#,a]&/@ds))v[L,a]/w[L,a]],{n,ns}];
es=us-bs; mc=Accumulate[qs bs es];
summary=Table[idx=Range[h];ap=Total[Differences[aws[[idx]]] Map[Max[#,0]&,Most[mc[[idx]]]]];
<|"H"->h,"x"->Total[aws[[idx]]qs[[idx]]bs[[idx]]^2],"s"->Total[aws[[idx]]qs[[idx]]us[[idx]]^2],"t"->Total[aws[[idx]]qs[[idx]]es[[idx]]^2],"K"->Total[aws[[idx]]qs[[idx]]bs[[idx]]es[[idx]]],"R"->Total[aws[[idx]]qs[[idx]](es[[idx]]^2+2bs[[idx]]es[[idx]])],"M_H"->mc[[h]],"max_positive_M"->Max[0,Max[mc[[idx]]]],"Abel_positive_sum"->ap|>,{h,{cap,4cap,20cap}}];
<|"N"->cap,"D"->ds,"L"->L,"residualNormSquared"->1-mu.c,"bNormSquared"->alpha.G.alpha,"normalEqError"->Max[Abs[G.alpha-(nu-J.c)]],"heads"->summary|>];
N[stage/@{5,10,15},12]
```

## squarefree_wolfram_stages_20_25_30.wl

```wolfram
ClearAll[w,v,g,stage];prec=40;zz=N[Zeta[2],prec];
w[m_Integer,a_Integer]:=w[m,a]=PolyGamma[1,N[a/m,prec]]/(zz m^2);
v[m_Integer,a_Integer]:=v[m,a]=(PolyGamma[1,N[a/m,prec]]/m^2+(PolyGamma[0,N[a/m,prec]]-PolyGamma[0,N[(a+1)/m,prec]])/m)/zz;
g[d_Integer,n_Integer]:=Mod[n,d]/d;
stage[cap_Integer]:=Module[{ds,ll,gg,jj,mu,nu,cc,aa,ns,bs,us,es,qs,aws,mc,idx,hh,ap},
ds=Select[Range[2,cap+1],MoebiusMu[#]!=0&];ll=LCM@@ds;
gg=Table[With[{mm=LCM[d,e]},Sum[g[d,k]g[e,k]w[mm,k],{k,1,mm}]],{d,ds},{e,ds}];
jj=Table[With[{mm=LCM[d,e]},Sum[g[d,k]g[e,k]v[mm,k],{k,1,mm}]],{d,ds},{e,ds}];
mu=Table[Sum[g[d,k]w[d,k],{k,1,d}],{d,ds}];nu=Table[Sum[g[d,k]v[d,k],{k,1,d}],{d,ds}];
cc=LinearSolve[gg,mu];aa=LinearSolve[gg,nu-jj.cc];
ns=Range[20cap];qs=1/(zz ns^2);aws=N[ns/(8+Log[ns])^2,prec];
bs=Table[aa.(g[#,n]&/@ds),{n,ns}];
us=Table[With[{k=1+Mod[n-1,ll]},(1-cc.(g[#,k]&/@ds))v[ll,k]/w[ll,k]],{n,ns}];es=us-bs;mc=Accumulate[qs bs es];
<|"N"->cap,"dim"->Length[ds],"L"->ll,"residualNormSquared"->1-mu.cc,"bNormSquared"->aa.gg.aa,"heads"->Table[idx=Range[hh];ap=Total[Differences[aws[[idx]]]Map[Max[#,0]&,Most[mc[[idx]]]]];<|"H"->hh,"x"->Total[aws[[idx]]qs[[idx]]bs[[idx]]^2],"K"->Total[aws[[idx]]qs[[idx]]bs[[idx]]es[[idx]]],"R"->Total[aws[[idx]]qs[[idx]](es[[idx]]^2+2bs[[idx]]es[[idx]])],"M_H"->mc[[hh]],"min_M"->Min[mc[[idx]]],"max_tM"->Max[idx mc[[idx]]],"Abel_positive"->ap|>,{hh,{cap,4cap,20cap}}]|>];
N[stage/@{20,25,30},10]
```

## squarefree_wolfram_stage_30_head_6000.wl

```wolfram
ClearAll[w,v,g,stage];prec=35;zz=N[Zeta[2],prec];
w[m_Integer,a_Integer]:=w[m,a]=PolyGamma[1,N[a/m,prec]]/(zz m^2);
v[m_Integer,a_Integer]:=v[m,a]=(PolyGamma[1,N[a/m,prec]]/m^2+(PolyGamma[0,N[a/m,prec]]-PolyGamma[0,N[(a+1)/m,prec]])/m)/zz;
g[d_Integer,n_Integer]:=Mod[n,d]/d;
stage[cap_Integer]:=Module[{ds,ll,gg,jj,mu,nu,cc,aa,ns,bs,us,es,qs,aws,mc,idx,hh,ap},
ds=Select[Range[2,cap+1],MoebiusMu[#]!=0&];ll=LCM@@ds;
gg=Table[With[{mm=LCM[d,e]},Sum[g[d,k]g[e,k]w[mm,k],{k,1,mm}]],{d,ds},{e,ds}];
jj=Table[With[{mm=LCM[d,e]},Sum[g[d,k]g[e,k]v[mm,k],{k,1,mm}]],{d,ds},{e,ds}];
mu=Table[Sum[g[d,k]w[d,k],{k,1,d}],{d,ds}];nu=Table[Sum[g[d,k]v[d,k],{k,1,d}],{d,ds}];
cc=LinearSolve[gg,mu];aa=LinearSolve[gg,nu-jj.cc];
ns=Range[200cap];qs=1/(zz ns^2);aws=N[ns/(8+Log[ns])^2,prec];
bs=Table[aa.(g[#,n]&/@ds),{n,ns}];
us=Table[With[{k=1+Mod[n-1,ll]},(1-cc.(g[#,k]&/@ds))v[ll,k]/w[ll,k]],{n,ns}];es=us-bs;mc=Accumulate[qs bs es];
<|"N"->cap,"dim"->Length[ds],"L"->ll,"residualNormSquared"->1-mu.cc,"bNormSquared"->aa.gg.aa,"heads"->Table[idx=Range[hh];ap=Total[Differences[aws[[idx]]]Map[Max[#,0]&,Most[mc[[idx]]]]];<|"H"->hh,"x"->Total[aws[[idx]]qs[[idx]]bs[[idx]]^2],"K"->Total[aws[[idx]]qs[[idx]]bs[[idx]]es[[idx]]],"R"->Total[aws[[idx]]qs[[idx]](es[[idx]]^2+2bs[[idx]]es[[idx]])],"M_H"->mc[[hh]],"min_M"->Min[mc[[idx]]],"max_tM"->Max[idx mc[[idx]]],"Abel_positive"->ap|>,{hh,{cap,20cap,200cap}}]|>];
N[stage/@{30},10]
```
