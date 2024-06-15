
p := 2^255 - 19;
F := GF(p);
R<x> := PolynomialRing(F);
n := 8;
M := KMatrixSpace(F,n,n);
sample := 20000;
facs := {* *};

function Fp_to_int(a)
 aa := Integers() ! a;
 if aa lt (p div 2) then return aa; else return aa - p; end if;
end function;

for r := 1 to sample do

A0 := ZeroMatrix(F,n,n);
A1 := ZeroMatrix(F,n,n);
repeat
 for i in [1..n] do for j in [1..n] do
  A0[i,j] := Random([0,1,2]);
 end for; end for;
 d := Determinant(A0);
until d ne 0;

repeat
 for i in [1..n] do for j in [1..n] do
  A1[i,j] := Random([0,1,2]);
 end for; end for;
until A1 ne A0 and Determinant(A1) eq d;

E1 := M ! (A0*Random(SL(n,F)));
E2 := M ! Random(GL(n,F));

conj := E1*A0*(E2)^-1 * (E1*A1*(E2)^-1)^-1;

D := Fp_to_int(Determinant(A1));
elts := Eltseq(CharacteristicPolynomial(conj));
elts := [Fp_to_int(e) : e in elts];
pI := p*IdentityMatrix(Integers(),n);
MM := Matrix(Integers(),n+1,n, elts[1..n] cat Eltseq(pI));
L := Lattice(MM);
v1 := ShortestVector(L)[1];
if v1 notin {-D,D} then Include(~facs, Abs(D/v1)); end if;
end for;
#facs;
facs;
