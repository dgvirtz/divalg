//This file contains the main functions to maximise the order locally at the unique ramification place w.
import "invariants.m":GlobalPlace, GlobalLift, FixDenominator, IntegralClosureRing;
import "util.m":MatrixSigma, IntegralInvert;

//Solve the norm equation Nm(x)=a up to order n locally at w (zero of hw)
//given uniformiser pi_L at extension of w to L.
SolveNormEquation := function(n,a,hw,w,pi,L)
  r := Degree(L);
  k := ResidueClassField(w);
  a_res := Evaluate(a,w);
  sol := Root(a_res,r);
  x := L!GlobalLift(sol,w);
  x_res:=x;
  
  for i:=1 to n-1 do
    testNorm := Norm(1+pi^(r*i));
    beta := Evaluate((testNorm-1)/hw^i,w);
    res := Evaluate((Norm(x)/a-1)/hw^i,w);
    x := x-pi^(r*i)*L!GlobalLift(res/beta,w)*x_res;
  end for;
  return x;
end function;

//computing rep matrix of isomorphism (L/F, sigma, a)->(L/F, sigma, 1) over F
TrivialCyclicToMatAlg := function(sigma,O,F)
  bs := Basis(O);
  r := #bs;
  P := MatrixSigma(sigma,O,F);
  M := ZeroMatrix(F,r^2,r^2);
  seq := [];
  for i:=0 to r-1 do
    for j:=1 to r do
      T := RepresentationMatrix(O!bs[j]);
      Append(~seq,P^i*T);
    end for;
  end for;
  for i:=1 to r^2 do
    M[i] := Vector(Eltseq(seq[i]));
  end for;
  return M;
end function;

//computing rep matrix of isomorphism (L/F,sigma,1)->M_r(F) over F
CyclicToTrivial := function(sigma,f,F,O)
  bs := Basis(O);
  r := #bs;
  M := ZeroMatrix(F,r^2,r^2);
  for i:=0 to r-1 do
    f_prod := 1;
    for j:=0 to i do
      img := f;
      for k:=1 to j do
	img := sigma(img);
      end for;
      f_prod *:= img;
    end for;
    for j:=1 to r do
      img := f_prod*bs[j];
      v:=Vector(Eltseq(O!img));
      InsertBlock(~M,v,i*r+j,i*r+1);
    end for;
  end for;
  return M;
end function;

//compute maximisation at ramified place
intrinsic MaximizeRamified(L::Fld,sigma::Map,a::RngElt,pi_F:RngElt)
-> Mtrx
{}
  A:=Parent(pi_F); F:=FieldOfFractions(A); O := IntegralClosureRing(A,L);
  
  print "Computing ramification place";
  w := GlobalPlace(F, pi_F);

  //The uniformiser is not required, since we may compute up to first order.
  pi_L := 1;
  min := -1;

  print "Solving norm equation up to order ", -min;
  f := SolveNormEquation(-min,F!a,pi_F,w,pi_L,L);

  print "Computing isomorphism (L/F, sigma, a)->(L/F, sigma, 1)";
  N := CyclicToTrivial(sigma,f,F,O);
  print "Inverting (L/F,sigma,a)->(L/F, sigma, 1)";
  N_inv := IntegralInvert(N,F);

  print "Computing isomorphism (L/F,sigma,1)->M_r(F)";
  M := TrivialCyclicToMatAlg(sigma,O,F);
  print "Inverting (L/F,sigma,1)->M_r(F)";
  M_inv := IntegralInvert(M,F);

  print "Combining isomorphisms";
  lambda := M_inv*N_inv;

  print "Fixing denominator";
  lambda_w := FixDenominator(lambda,pi_F,F);

  print "Computing echelon form";
  lambda_w := EchelonBasis(lambda_w, A);

  return lambda_w;
end intrinsic;
