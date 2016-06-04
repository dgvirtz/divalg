//This file computes some stuff related to global fields and wraps differing function/number field functions.

//returns a global lift of x in the residue field of place p
GlobalLift := function(x,p)
  if ISA(Type(p),PlcFunElt) then
    return Lift(x,p);
  else
    return Integers()!x;
  end if;
end function;

//computes a global place in F which is a zero of f
GlobalPlace := function(F,f)
  if ISA(Type(F),FldFunG) then
    return (Zeros(F!f)[1]);
  else
    if ISA(Type(F), FldRat) then
      return (Decomposition(QNF(),f)[1][1]);
    else
      return (Decomposition(F,f)[1][1]);
    end if;
  end if;
end function;

//wrapper for the ring of integers
IntegralClosureRing := function(A,L)
  if ISA(Type(BaseField(L)), FldRat) then
    O := MaximalOrder(L);
  else
    O := IntegralClosure(A,L);
  end if;
  return O;
end function;

//computes the local degree of f at w (the unique ramification place) in a cyclotomic extension
LocalCycDegree := function(f, w)
  return Order(Evaluate(f,w));
end function;

//computes the local degree of f at w in the deg r subfield L of the cyclotomic extension
LocalSubDegree := function(f, w, r)
  ff := LocalCycDegree(f, w);
  return (ff div Gcd((#ResidueClassField(w)-1) div r, ff));
end function;

//fix the denominators of matrix lambda using the uniformiser pi
FixDenominator := function(lambda,pi,F)
  v := GlobalPlace(F,pi);
  denom := MatLCM(lambda);
  pd := denom div (pi^Valuation(denom,v));
  return lambda*pd;
end function;