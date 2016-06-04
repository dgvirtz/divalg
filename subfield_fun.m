//This file computes a cyclic subextension of degree r to the given cyclotomic extension in the function field case.
import "invariants.m":GlobalPlace, GlobalLift;

//compute the representation of x in basis of FF(R) over Fprime
RepresentationKummer := function(x,Fprime,R,dprime,r)
  R2 := PolynomialRing(Fprime, dprime);
  phi:=hom<R[1]->R2|R2.1>;
  for i := 2 to dprime do
    phi := hom<R[i]->R2|phi, R2.i>;
  end for;
  cs, mons := CoefficientsAndMonomials(phi(x));
  
  I:=Vector([r^i: i in [0..dprime-1]]);
  repk := ZeroMatrix(Fprime, 1, r^dprime);
  for i:=1 to #mons do
   repk[1][(I,Vector(Exponents(mons[i])))+1]:=cs[i];
  end for;
  return repk[1];
end function;

//generate the subfield with the Kummer theory approach
intrinsic GenerateSubfieldKummer(r::RngIntElt, hw::RngUPolElt, F::FldFunRat)
-> FldFun, FldFinElt, Map, FldFinElt
{}
  require IsIrreducible(hw):"Second argument not irreducible";
  A := RingOfIntegers(F); q:=#BaseRing(A);
  k := ConstantField(F);
  dprime := Degree(hw);
  kprime := ext<k|dprime>;
  Aprime<t> := ChangeRing(A,kprime);
  _,root := HasRoot(Aprime!hw); root0 := root;
  hs := [root-t];
  R := [PolynomialRing(Aprime)];
  for i:=2 to dprime do
    Append(~R,PolynomialRing(R[i-1]));
    root := root^q;
    Append(~hs,root-t);
  end for;
  P<u> := PolynomialRing(R[dprime]);
  deltas := [];
  for i:=0 to dprime-1 do
      deltai := 1;
      for j := 0 to dprime-1 do
	deltai *:= (R[((i+j) mod dprime) + 1].1)^(q^(dprime-1-j));
      end for;
      Append(~deltas,deltai);
  end for;
  p := 1;
  zeta := RootOfUnity(r,kprime);
  for n := 0 to r-1 do
    print "Computing torsion point ",n;
    x := 0;
    for i:= 0 to dprime-1 do
      x +:= (zeta^n)^(q^i)*deltas[i+1];
      for j:=1 to dprime do
	x := x mod ((R[j].1)^r - hs[j]);
      end for;
    end for;
    if(n eq 0) then
      x0 := x;
    end if;
    if(n eq 1) then
      x1 := x;
    end if;
    p;
    p *:= (u-x);
    for i:=1 to dprime do
      p := p mod ((R[i].1)^r - hs[i]);
    end for;
  end for;
  L := ext<F|p>;
  
  Fprime<t> := FieldOfFractions(Aprime);
  V := VectorSpace(Fprime, r^dprime);
  v1 := V!RepresentationKummer(x1,Fprime,R,dprime,r);
  v := [];
  x0i := 1;
  for i:=0 to r-1 do
    print "Computing basis coefficients", i;
    for j:=1 to dprime do
      x0i := x0i mod ((R[j].1)^r - hs[j]);
    end for;
    Append(~v, V!RepresentationKummer(x0i,Fprime,R,dprime,r));
    x0i *:= x0;
  end for;
  B := Matrix(v);
  print "Computing image of Galois generator";
  img := Eltseq(Solution(B, v1));
  print "Computing generator of Galois group";
  sigma := hom<L->L|L!Eltseq(img)>;
  
  return L,sigma,zeta,root0;
end intrinsic;

//calculate the Frobenius of p
FrobKummer := function(p,pi_F,r,A,root)
  q := #BaseRing(A);
  kprime := Parent(root);
  dprime := Degree(pi_F);
  Aprime<t> := ChangeRing(A,kprime);
  rprime := (q^dprime-1) div r;
  pp:=Aprime!(A!p); e := Degree(pp); 
  return (Evaluate(pp,root^(q^(e-1))))^(rprime*q^((-e) mod dprime));
end function;


//////////Old approaches to create the subfield L. Left here for the interested mind

//generate subfield by computing norm of primitive torsion point
intrinsic GenerateSubfieldNormal(r::RngIntElt,hw::RngUPolElt,F::FldFunRat)
-> FldFun, FldFun
{}
  require IsIrreducible(hw):"Second argument not irreducible";
  A:=RingOfIntegers(F);
  w:=GlobalPlace(F,hw); k:=ResidueClassField(w); sigma:=A!GlobalLift(PrimitiveElement(k),w); 
  R<T> := TwistedPolynomials(F:q:=#BaseRing(A));
  phi_prew := CarlitzModule(R,hw);
  phi_w := Polynomial(CarlitzModule(R,hw)) div Polynomial(R!1);
  Pol<l> := Parent(phi_w);
  PolE<Z> := PolynomialRing(Pol);
  
  phi := CarlitzModule(R,A!(sigma)^r mod hw);
  prod:=1;
  for j:= 0 to r-1 do
    "Computing normal basis element", j;
    mu:=1;
    s := CarlitzModule(R,A!(sigma)^j mod hw);
    for i := 1 to (Degree(phi_w) div r) do
	mu := mu*Polynomial(s) mod phi_w;
	_,s := Quotrem(phi*s,phi_prew);
	i;
    end for;
    prod := prod*(Z-mu) mod phi_w;
  end for;
  
  E := ext<F|phi_w>;
  ev := hom<Pol->E|E.1>;
  muE := ev(mu);
  L := ext<F|prod>;
  Embed(L,E,muE);
  return L,E;
end intrinsic;

//generate subfield additively with Gauss-Thakur sums approach
intrinsic GenerateSubfieldGT(r::RngIntElt,hw::RngUPolElt,F::FldFunRat)
-> FldFun, FldFun
{}
  require IsIrreducible(hw):"Second argument not irreducible";
  A:=RingOfIntegers(F); q:=#BaseRing(A);
  w:=GlobalPlace(F,hw); k:= ResidueClassField(w); zeta:=PrimitiveElement(k);
  
  
  R<T> := TwistedPolynomials(A:q:=q);
  phi_w := Polynomial(CarlitzModule(R,hw)) div Polynomial(R!1);
  Pol := Parent(phi_w);
  Ak := ChangeRing(A,k);
  Polk := ChangeRing(Pol,Ak);
  PolPolk<Z>:=PolynomialRing(Polk);

  print "Computing basic Gauss sums from 0 to", Degree(hw)-1;
  jsum:=[];
  for j:=0 to Degree(hw)-1 do
   sum:=0;
   for b in k do
    if b ne 0 then
      bl := A!GlobalLift(b,w);
      sum := (sum - b^(-q^j)*Polk!(Polynomial(CarlitzModule(R,bl))));
    end if;
   end for;
   Append(~jsum, sum mod Polk!phi_w);
   j;
  end for;
  print "Computing universal Gauss sums from 0 to", r-1;
  usums:=[Polk|];
  for i:=0 to r-1 do
    gsum := 1;
    expansion := Intseq(i*(Degree(phi_w) div r),q);
    for j := 1 to #expansion do
      gsum := (gsum * (jsum[j])^expansion[j]) mod Polk!phi_w;
    end for;
    Append(~usums, gsum);
  end for;
  mipo:=PolPolk!1;
  print "Computing normal basis elements from 0 to", r-1;
  for m:=0 to r-1 do
    n:=0;
    for i:=0 to r-1 do
        n := (n+zeta^(i*m*(Degree(phi_w) div r))*usums[i+1]) mod Polk!phi_w;
    end for;
    mipo := mipo*(Z-n) mod PolPolk!phi_w;
    mipo;
    m;
  end for;
  E<l>:=ext<F|phi_w>;
  ev:=hom<Pol->E|l>;
  L:=ext<F|mipo>;
  Embed(L,E,ev(n));
  
  return L,E;
end intrinsic;