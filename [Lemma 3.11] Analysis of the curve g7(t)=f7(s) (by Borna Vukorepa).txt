_<t>:=RationalFunctionField(Rationals());

//form of j-invariant giving B(7) as image of Galois
f1 := (t^2 + 13*t + 49)*(t^2 + 5*t + 1)^3/t;

//form of j-invariant allowing curve X_7 as per Rouse for mod 4 image
f2 := (32*t - 4)/t^4;

R<x,y> := PolynomialRing(Rationals(), 2);
C := ProjectiveClosure(Curve(AffineSpace(R),Numerator(Evaluate(f1,x)-Evaluate(f2,y))));

"We need to find rational points on C:";
C;
"";

"Genus is:", Genus(C);

tr, x1, mp:=IsHyperelliptic(C);

"Is C hyperelliptic?", tr;
"";

"This is the hyperelliptic curve CQ:";
x1;

J:=Jacobian(x1);
RankBounds(J);

pts := Points(x1 : Bound:=100);
Q1 := (pts[2] - pts[1]);
Order(Q1);

bas, M := ReducedBasis([Q1]);

N:=Orthogonalize(M);
absbd:=Ceiling(Exp((N[1,1]^2)/4+HeightConstant(J)));
PtsUpToAbsBound:=Points(J : Bound:=absbd);
Q2 := ReducedBasis([pt : pt in PtsUpToAbsBound])[1];

LogarithmicBound := Height(Q2) + HeightConstant(J);  // Bound on the naive h(Q)
AbsoluteBound := Ceiling(Exp(LogarithmicBound));
PtsUpToAbsBound := Points(J : Bound:=AbsoluteBound );  
ReducedBasis( [ pt : pt in PtsUpToAbsBound ]);

Height(Q2);
"Hence, Q2 is the generator modulo torsion.";
"";

pts;

"These are all the points on the hyperelliptic curve CQ by Chabauty:";
Chabauty(Q2);
"";

"These are all the points on C:";
for i in [1..#pts] do
    Points(pts[i]@@mp);
end for;

"Hence, two appropriate j-invariants exist";
"They are:";

assert Evaluate(f1, -4) eq Evaluate(f2, 2/3);
Evaluate(f1, -4);

assert Evaluate(f1, -49/4) eq Evaluate(f2, 16/479);
Evaluate(f1, -49/4);

"One can directly compute that cyclic 4-isogeny";
"is defined over cubic field in both cases,";
"so we get a cyclic 28-isogeny defined over cubic field.";
