//This file is not needed for the algorithm.
//Constructs an AssociativeAlgebra object from Magma's package (for comparison purposes).
intrinsic AssAlgebra(O::Rng,F::Fld,sigma::Map,a::RngElt)
-> AlgAss
{}
  b := Basis(O); d := #b; n:=d^2;
  imgs:=[];
  for i:=1 to d do
    l := [];
    x := b[i];
    for j:=1 to d do
      Append(~l,x);
      x := sigma(x);
    end for;
    Append(~imgs,l);
  end for;
  l:=[];
  consts := [F|0 : i in [1..n^3]];
  for i:=1 to d do
    for j:=1 to d do
    if(i-1+j-1 ge d) then
      c:=a;
    else
      c:=1;
    end if;
    k := (i-1+j-1) mod d;
      for i2:=1 to d do
	for j2:=1 to d do
	  for k2:=1 to d do
	    consts[((i-1)*d+i2-1)*n^2+((j-1)*d+j2-1)*n+k*d+k2]:=
	    Eltseq(O!(c*b[i2]*imgs[j2][i]))[k2];
	  end for;
	end for;
      end for;
    end for;
  end for;
  A := AssociativeAlgebra<F, n|consts : Check:=false>;
  return A;
end intrinsic;

intrinsic MatrixToOrder(D::AlgAss,A::Rng,M::Mtrx)
-> AlgAssVOrd
{}
  seq := [];
  for s in RowSequence(M) do
    Append(~seq, D!s);
  end for;
  l := Order(A,seq);
  return l;
end intrinsic;