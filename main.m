//This is the main file demonstrating use of the package. Change input parameters here.

AttachSpec("divalg.spec");
import "invariants.m":IntegralClosureRing;

A := Integers();
places := [2,3,5];
inv := [1/2,1/3,1/6];

q:=5;
A<t> := PolynomialRing(GF(q));
places:=[t,t^2+t+1, t^3+t^2+1];
inv:=[1/2,1/4,1/4];


print "===Constructing cyclic algebra===";
L,sigma,a,pi_F := CyclicAlgebra(places, inv, A);

time0 := Cputime();
//The integral closure is also computed later within the algorithm
//but we do it separately here to keep track performance issues.
print "Computing ring of integers";
O := IntegralClosureRing(A,L);

print "===Maximising at ramification place===";
lambda_w := MaximizeRamified(L,sigma,a,pi_F);

lambdas:=[IdentityMatrix(A,Degree(L)^2),lambda_w];
for i:= 1 to #places do
  print "===Maximizing at place", places[i], "===";
  lambda_v := MaximizeUnramified(places[i],L,sigma,a,pi_F);
  Append(~lambdas, lambda_v);
end for;

print "Computing echelon form of final order";
lambda_max := VerticalJoin(lambdas);
lambda_max := EchelonBasis(lambda_max, A);
//The computation ends here. lambda_max contains generators of the max order/A.

time1 := Cputime(time0); print "Time needed to calculate maximal order:", time1;

//sanity check if order is indeed maximal by computing the discriminant
print "Expected discriminant";
disc := 1; r:=Degree(L);
for i:=1 to #inv do
  rv := Denominator(inv[i]);
  disc *:= places[i]^(r-(r div rv));
end for;
disc := A!disc^r; disc;

print "Computing discriminant";
disc2 := A!ReducedTrace(lambda_max,L,sigma,a); disc2;

print "Factorised difference (should be empty product)";
Factorization(disc2 div disc);

//compute the maximal order with Magma's built-in function for number fields for comparison
//WARNING: very very slow
print "Constructing Magma algebra";
D := AssAlgebra(O,FieldOfFractions(A),sigma,a);

print "Converting maximal order into built-in Magma type";
l3 := MatrixToOrder(D,A,lambda_max);
print "Computing its discriminant with built-in Magma function";
disc3 := Discriminant(l3); disc3;

print "Factorised difference (should be empty product)";
Factorization(disc3 div disc);

magmatime0:=Cputime();

print "Computing maximal order with generic built-in Magma function for algebras";
l4 := MaximalOrderFinite(D);
magmatime1:=Cputime(magmatime0); print "Time needed to calculate maximal order with built-in function:", magmatime1;
print "Computing discriminant";
disc4 := Discriminant(l4);
print "Factorised difference (should be empty product)";
Factorization(disc4 div disc);
