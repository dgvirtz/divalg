//This file computes the division algebra.
import "invariants.m":GlobalPlace,LocalCycDegree,LocalSubDegree;
import "util.m":SeqSum;
import "subfield_fun.m":FrobKummer;

//decompose the invariants into numerator and denominator
DecomposeInv := function(inv)
  denoms:=[]; numers:=[];
  for s in inv do
    Append(~denoms, Denominator(s));
    Append(~numers, Numerator(s));
  end for;
  return numers, denoms;
end function;

//check if pi_F is a suitable place with weak condition
IsSuitablePlaceWeak := function(pi_F, places, denoms, F)
  print "Testing ", pi_F;
  r := LCM(denoms);
  w := GlobalPlace(F, pi_F);
  for i := 1 to #places do
      ff := LocalCycDegree(F!places[i], w);
      if (not IsDivisibleBy(ff,denoms[i]))
        or (not IsDivisibleBy(LocalSubDegree(F!places[i], w, r), denoms[i])) then
          return false;
      end if;
  end for;
  return true;
end function;

//check if pi_F is a suitable place with strong condition (necessary for max order computation)
IsSuitablePlaceStrong := function(pi_F, places, denoms, F)
  print "Testing ", pi_F;
  r := LCM(denoms);
  w := GlobalPlace(F, pi_F);
  for i := 1 to #places do
      ff := LocalCycDegree(F!places[i], w);
      if (not IsDivisibleBy(ff,denoms[i]))
        or (not (LocalSubDegree(F!places[i], w, r) eq denoms[i])) then
          return false;
      end if;
  end for;
  return true;
end function;

//compute a=\tau^r to get right invariants
Compute_a := function(pi_F, places, inv, zeta, frobs, F)
  numers, denoms := DecomposeInv(inv);
  r := LCM(denoms);
  w := GlobalPlace(F, pi_F);
  a := 1;
  for i := 1 to #places do
    d := LocalSubDegree(F!places[i], w, r);
    R := Integers(r);
    u := R!(r div d);
    log := Log(zeta,frobs[i]); error if log eq -1, "Logarithm has no solution";
    s := R!log;
    uprime := Integers()!Solution(s,u);
    g := (uprime*numers[i]) mod denoms[i];
    a *:= places[i]^((g*d) div denoms[i]);
  end for;
  sum := SeqSum(inv);
  if (Denominator(sum) eq 2) then
    a := -a;
  end if;
  return a;
end function;

//main function to compute the cyclic algebra
//returns cyclic extension L of deg r, automorphism sigma, a, and found ramification place pi_F 
intrinsic CyclicAlgebra(places::[RngElt],inv::[FldRatElt], A::Rng)
-> Fld, Map, Fld, FldElt, RngElt
{}
  require #places eq #inv: "Number of places and invariants unequal";
  require #places eq #SequenceToSet(places): "Places must not occur several times";
  for p in places do
    require IsIrreducible(A!p): p, "is reducible";
  end for;
  sum := SeqSum(inv);
  _,denoms := DecomposeInv(inv); r := LCM(denoms);
  
  F := FieldOfFractions(A);
  if ISA(Type(F), FldRat) then
    require (IsDivisibleBy(2,Denominator(sum))): "Sum of invariants is",sum;
  
    pi_F:=1;
    repeat
      pi_F := NextPrime(pi_F);
      while (pi_F in places) or ((pi_F mod r) ne 1) do
	pi_F := NextPrime(pi_F);
      end while;
      done := IsSuitablePlaceStrong(pi_F, places, denoms, F);
      if not(IsIntegral(sum)) then
	done := done and not IsDivisibleBy((pi_F-1) div r, 2);
      end if;
    until done;
    print "Found p=",pi_F;
    w := GlobalPlace(F,pi_F);
    
    L,sigma,zeta := GenerateSubfieldLL(r,pi_F);
    
    frobs := [];
    for P in places do
      Append(~frobs, Evaluate(F!P, w));
    end for;
  else
    error if not(IsDivisibleBy(1,Denominator(sum))), "Sum of invariants is",sum;
    
    p:=Characteristic(A); q:=#BaseRing(A);
    error if IsDivisibleBy(r,p), "p =",p,"divides r=",r;
    
    d0 := Order(ResidueClassRing(r)!q);
    j := 1;
    repeat
      done := false;
      list:=AllIrreduciblePolynomials(GF(q),d0*j);
      for hw in list do
	if (not (hw in places)) and (Degree(hw) gt 1)
	    and IsSuitablePlaceStrong(hw, places, denoms, F) then
	  done := true;
	  pi_F := hw;
	  break hw;
	end if;
      end for;
    j +:= 1;
    until done;
    print "Found pi_F=", pi_F;
    
    print "=Computing field extension=";
    L,sigma,zeta,root := GenerateSubfieldKummer(r,pi_F,F);
    
    print "Computing local Frobenii";
    frobs := [];
    for P in places do
      Append(~frobs, FrobKummer(P,pi_F,r,A,root));
    end for;
  end if;

  print "Computing a";
  a := Compute_a(pi_F, places, inv, zeta, frobs, F);
  
  return L,sigma,a,pi_F;
end intrinsic;