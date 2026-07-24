needs "CubicSurface.m2"
needsPackage "Resultants"
needsPackage "FourTiTwo"

-- compute the equation of the cubic surface
cubicBasis = matrix {basisOfCubics P}
R = ring cubicBasis
linesOnSurface = linesOnACubicSurface P;
G = lineIncidenceGraph(linesOnSurface)
I = equationOfCubicSurface(P)
S = ring I


-- compute a basis for each set of canonical forms
-- here we use only the quadrilaterals
randomPts = for i from 1 to 165 list(

    paramVals := matrix {apply(gens R, i -> random(1, 10))};
    sub(cubicBasis, paramVals)
);


-- setup veronese
ver = veronese(3, 8);
V = source ver

-- compute a basis for the linear span
M1 = matrix for p in randomPts list flatten entries sub(matrix ver, p);
K = gens ker sub(M1, QQ);
B1 = support(basis(1, V) % (ideal(basis(1, V)*sub(K, QQ)))) / index;
X = QQ[(gens V)_B1];
smallVer = (matrix ver)_B1;


-- check that these forms are really linearly independent again
randomPts = for i from 1 to numgens(X) list(

    paramVals := matrix {apply(gens R, i -> random(ZZ/nextPrime(10000000000)))};
    sub(cubicBasis, paramVals)
);
M1 = matrix for p in randomPts list flatten entries sub(smallVer, p);



-- compute the quadratic relations
B = basis(2, X);

randomPts = for i from 1 to numcols(B) list(

    paramVals := matrix {apply(gens R, i -> random(ZZ/nextPrime(1000000000)))};
    cubicSurfacePt := sub(cubicBasis, paramVals);
    imVals := sub(smallVer, cubicSurfacePt)
);


MZ = matrix for p in randomPts list flatten entries sub(B, p);
KZ = gens ker MZ;
J = ideal(B*sub(KZ, QQ));
