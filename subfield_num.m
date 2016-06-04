//This file computes a cyclic subextension of degree r to the given cyclotomic extension in the number field case.
GenerateSubfieldLL := function(r,p,zeta)
  E<s> := CyclotomicField(p);
  h := hom<E->E|s^(Integers()!Integers(p)!(zeta))>;
  x := 0;
  for i:=1 to (p-1) div r do
    x +:= s^(Integers()!Integers(p)!(zeta^(r*i)));
  end for;
  P<t> := PolynomialRing(E);
  f := P!1;
  xorb := x;
  for i:=1 to r do
    f *:= (t-xorb);
    xorb := h(xorb);
  end for;
  L := ext<Rationals()|f>;
  Embed(L, E, x);  
  sigma := hom<L->L|h(x)>;
  return L, sigma;
end function;
