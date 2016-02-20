//This file computes a cyclic subextension of degree r to the given cyclotomic extension in the function field case.

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
GenerateSubfieldKummer := function(r,hw,F)
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
  
  return L,zeta,sigma,root0;
end function;

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

//utility to apply automorphism
ApplyAuto := function(sigma,x,F,E)
  R<l> := TwistedPolynomials(F);
  phi_l := Polynomial(CarlitzModule(R,sigma));
  E<l>:=E;
  phi_l := eval(Sprintf("E!(%o)",phi_l));
  phi := hom<E->E|phi_l>;
  return phi(x);
end function;

//generate subfield by computing norm of primitive torsion point
GenerateSubfieldNormal := function(hw,r,A,F)
  w:=GlobalPlace(F,hw); k:=ResidueClassField(w); sigma:=A!GlobalLift(PrimitiveElement(k),w); 
  R<T> := TwistedPolynomials(F);
  phi_prew := CarlitzModule(R,hw);
  phi_w := Polynomial(CarlitzModule(R,hw)) div Polynomial(R!1);
  E<l> := Parent(phi_w);
  E2<Z> := PolynomialRing(E);
  
  phi := CarlitzModule(R,A!(sigma)^r mod hw);
  mu:=1; s := phi;
  print "Computing generator orbit from 0 to ", Degree(phi_w div r);
  for i := 1 to (Degree(phi_w) div r) do
      i;
      mu := mu*Polynomial(s) mod phi_w;
      _,s := Quotrem(phi*s,phi_prew);
  end for;
  
  prod := 1;
  s := F!1;
  for j:=0 to r-1 do
    gamma := Polynomial(CarlitzModule(R,s));
    prod:=prod*(Z-Evaluate(mu,gamma)) mod phi_w;
    s *:= sigma;
  end for;
  L<m> := ext<F|prod>;
  E<l> := ext<F|phi_w>;
  mu := eval(Sprintf("E!(%o)",mu));
  Embed(L,E,mu);
  return L,E;
end function;

//generate subfield additively with Gauss-Thakur sums approach
GenerateSubfieldTrace := function(r,hw,q,A,F)
  P:=GlobalPlace(F,hw); k := ResidueClassField(P);
  k2 := ext<GF(q)|hw>; sigma:=PrimitiveElement(k2);
  zeta := PrimitiveElement(k); zetainv := zeta^-1;
  R<T> := TwistedPolynomials(A);
  phi_w := Polynomial(CarlitzModule(R,hw)) div Polynomial(R!1);
  phi_w_tens := phi_w mod hw;
  E<l> := Parent(phi_w);
  
  print "Computing Gauss sums of orders 0 to ", Degree(hw)-1;
  jsums := [];
  for j:=0 to Degree(hw)-1 do
    sum := 0;
    zetainvpot := zetainv^(q^j);
    b := zeta; binv := zetainvpot;
    for i:=1 to #k do
      bl := A!Lift(b,P); blinv := A!Lift(binv,P);
      sum := (sum + blinv*Polynomial(CarlitzModule(R,bl))) mod phi_w_tens mod hw;
      b *:= zeta; binv *:= zetainvpot;
    end for;
    j;
    Append(~jsums, sum);
  end for;
  jsumpot := [];
  for g in jsums do
    pots := [];
    pot := g^0;
    for i := 0 to q-1 do
      Append(~pots,pot);
      pot := (pot*g) mod phi_w_tens mod hw;
    end for;
    Append(~jsumpot,pots);
  end for;
  print "Computing and summing universal Gauss sums from 1 to ", Degree(phi_w);
  n:=0;
  for i:=1 to Degree(phi_w) do
    gsum := E!1;
    expansion := Intseq(i,q);
    for j := 1 to #expansion do
      gsum := (gsum * jsumpot[j][expansion[j]+1]) mod phi_w_tens mod hw;
    end for;
    n := (n+gsum) mod phi_w_tens mod hw;
    i;
  end for;
  
  print "Computing trace from 1 to ", (Degree(phi_w) div r);
  E<l>:=ext<F|phi_w>;
  x:=eval(Sprintf("(%o)",n));
  trace:=0; phi := A!1; sigmar := A!sigma^r mod hw;
  for i:=1 to (Degree(phi_w) div r) do
    trace +:= ApplyAuto(A!phi,x,F,E);
    phi := (phi*sigmar) mod hw;
    i;
  end for;
  P<Z> := PolynomialRing(E);
  mipo := 1;
  for i := 0 to r-1 do
    mipo *:= (Z-ApplyAuto(sigma^i,trace,F,E));
  end for;
  L<m> := ext<F|mipo>;
  Embed(L,E,trace);
  
  return L,E;
end function;