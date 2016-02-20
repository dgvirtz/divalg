//This is the main file. Change input parameters here.

load "util.magma";
load "invariants.magma";
load "subfield_fun.magma";
load "subfield_num.magma";
load "divisionalgebra.magma";
load "ramified.magma";
load "unramified.magma";

/*A := Integers();
F := Rationals();
places := [2,3,5];
inv := [1/5,1/2,3/10];*/

q:=5;
A<t> := PolynomialRing(GF(q));
F<t> := FieldOfFractions(A);
places:=[t,t^2+t+1, t^3+t^2+2]; inv:=[1/2,1/3,1/6];

for p in places do
  error if not IsIrreducible(A!p), p, " is reducible";
end for;

print "===Constructing cyclic algebra===";
L,sigma,a,pi_F,r := CyclicAlgebra(places, inv, F);

print "Computing ring of integers";
O := IntegralClosureRing(A,L);

print "===Maximising at ramification place===";
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
lambda_w := EchelonBasis(lambda_w, A, F);

lambdas:=[lambda_w, IdentityMatrix(F,r^2)];
for i:= 1 to #places do
  print "===Maximizing at place ", places[i], "===";
  lambda_v := MaximizeUnramified(places[i],w,r,O,L,F,A,sigma,a);
  print "Fixing Denominator";
  lambda_v := FixDenominator(lambda_v, A!places[i], F);
  print "Computing echelon form";
  lambda_v := EchelonBasis(lambda_v, A, F);
  Append(~lambdas, lambda_v);
end for;

print "Computing echelon form of final order";
lambda_max := VerticalJoin(lambdas);
lambda_max := EchelonBasis(lambda_max, A, F);
//The computation ends here. lambda_max contains generators of the max order/A.

//sanity check if order is indeed maximal by computing the discriminant
print "Expected discriminant";
disc := 1;
for i:=1 to #inv do
  rv := Denominator(inv[i]);
  disc *:= places[i]^(r-(r div rv));
end for;
disc := A!disc^r; disc;

print "Computing discriminant";
disc2 := A!ReducedTrace(lambda_max,L,O,F,sigma,a); disc2;

print "Factorised difference";
Factorization(disc2 div disc);

//compute the maximal order with Magma's built-in function for number fields for comparison
//WARNING: very very slow
/*print "Computing Magma algebra";
D := AssAlgebra(O,QNF(),sigma,a);

seq2 := [];
for s in RowSequence(lambda_max) do
  Append(~seq2, D!s);
end for;
l3 := Order(seq2);
print "Computing discriminant";
disc3 := Integers()!Generators(Discriminant(l3))[1]; disc3;

Factorization(disc3 div disc);

print "Computing Magma Order";
l2 := MaximalOrder(D);
print "Computing discriminant";
disc4 := Integers()!Generators(Discriminant(l2))[1];*/