intrinsic MatrixToLatex(M::Mtrx)
->
{}
r:=Isqrt(NumberOfRows(M));
for i:=1 to r^2 do
  string:="";
  for j:=1 to r^2 do
    x:=M[i,j];
    if x ne 0 then
      if x eq 1 then
	c:="";
      elif Denominator(x) eq 1 then
       c:=Sprint(x);
      else
       c:="\\frac{" cat Sprint(Numerator(x)) cat "}{" cat Sprint(Denominator(x)) cat "}";
      end if;
      string cat:= "+" cat c cat "b_{" cat Sprint((j-1) mod r) cat "}\\tau^{" cat Sprint((j-1) div 4) cat "}"; 
    end if;
  end for;
  print Substring(string,2,#string-1) cat "\\\\&";
end for;
end intrinsic;