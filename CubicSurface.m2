needsPackage "Graphs";
needsPackage "PhylogeneticTrees" -- this is used to compute join ideals

-- pick six random points 
P = {{0,1,1}, {-1,0,1}, {0,-1,1}, {1, 1/2,1}, {3/4,-1/2,1}, {-1/4, -1/2,1}};


-- pick six random points 
basisOfCubics = P -> (

    R = QQ[x_0..x_2];
    B := basis(3, R);
    K := gens ker matrix for p in P list flatten entries sub(B, matrix {p});
    I := ideal mingens ideal(B*K);

    return I_*
)


-- pick six random points 
equationOfCubicSurface = P -> (

    R = QQ[x_0..x_2];
    B := basis(3, R);
    K := gens ker matrix for p in P list flatten entries sub(B, matrix {p});
    I := ideal mingens ideal(B*K);
    S := QQ[y_0..y_3];

    return ker map(R, S, I_*)
)   


-- pick six random points 
linesOnACubicSurface = P -> (

    R := QQ[x_0..x_2];
    B := basis(3, R);
    cubicK := gens ker matrix for p in P list flatten entries sub(B, matrix {p});
    I := ideal mingens ideal(B*cubicK);
    S := QQ[y_0..y_3];  
    phi := map(R, S, I_*);
    I = ker phi;


    -- map exceptional lines
    exceptional := for p in P list (

        J := sub(jacobian matrix phi, matrix {p});
        K := gens kernel J;  
        ideal mingens ideal(basis(1, S)*K)
    );


    -- map lines between points
    simpleLines := for A in subsets(P, 2) list(

        M := basis(1, R);
        K := gens ker matrix for p in A list flatten entries sub(M, matrix {p});
        J := ideal(M*K);
        preimage(phi, J)
    );

    -- map conics which go through 5 points
    conics := for A in subsets(P, 5) list(

        M := basis(2, R);
        K := gens ker matrix for p in A list flatten entries sub(M, matrix {p});
        J := ideal mingens ideal(M*K);
        preimage(phi, J)
    );

    allLines = exceptional|simpleLines|conics;
    
    return allLines;
)


-- compute the incidence graph of the lines on the cubic surface
lineIncidenceGraph = linesOnSurface -> (

    graphEdges := for e in subsets(27, 2) list(

        (i, j) := toSequence(e);

        J := allLines_i + allLines_j;

        if dim(J) == 0 then continue else e
    );

    return  graph(toList(0..26), graphEdges)
)


triangles = G -> (
    
    V := vertices(G);
    return select(subsets(V, 3), L -> #edges(inducedSubgraph(G, L)) == 3)
);


triangularForm := (T, linesOnSurface) -> (

    ideals := linesOnSurface_T;
    J := intersect(ideals);
    h := first select(J_*, f -> degree(f) == {1});

    return 1/h
)


-- compute the triangular regions on the cubic surface \ lines
triangleForms = P -> (

    linesOnSurface := linesOnACubicSurface P;
    S := ring linesOnSurface_0;
    G := lineIncidenceGraph(linesOnSurface);
    I := sub(equationOfCubicSurface(P), S);
    tris = triangles(G);

    return for T in tris list triangularForm(T, linesOnSurface)
)



fourCycles = G -> (

    V := vertices(G);
    E := edges(G);

    adj := (u,v) -> member(set {u,v}, E);
    cycles := {};
    scan(subsets(V, 4), S -> (
        a := S#0; b := S#1; c := S#2; d := S#3;
        -- the 3 distinct cyclic orderings of {a,b,c,d}
        if adj(a,b) and adj(b,c) and adj(c,d) and adj(d,a) then cycles = append(cycles, {a,b,c,d});
        if adj(a,b) and adj(b,d) and adj(d,c) and adj(c,a) then cycles = append(cycles, {a,b,d,c});
        if adj(a,c) and adj(c,b) and adj(b,d) and adj(d,a) then cycles = append(cycles, {a,c,b,d});
    ));
    cycles
)



--  
quadForms = P -> (

    linesOnSurface := linesOnACubicSurface P;
    S := ring linesOnSurface_0;
    G := lineIncidenceGraph(linesOnSurface);
    I := sub(equationOfCubicSurface(P), S);
    quads := fourCycles(G);
    tris := triangles(G);

    forms := for C in quads list(

        a := first select(vertices(G), i -> all(C, j -> distance(G, i, j) == 2));

        possible := select(subsets(neighbors(G, a), 2), e -> member(e, edges(G)));

        T0 := {};
        T1 := {};
        T2 := {};

        for e in possible do(

            (i, j) := toSequence toList e;
            
            T0 = sort({a,i,j});
            T1 = for c in subsets(C, 2) list if member(sort({i}|c), tris) then sort({i}|c) else continue;
            T2 = for c in subsets(C, 2) list if member(sort({j}|c), tris) then sort({j}|c) else continue;

            if #T1 > 0 and #T2 > 0 then break else continue
        );

        (T0, T1, T2) = (T0, first T1, first T2);

        1/triangularForm(T0, linesOnSurface)*(triangularForm(T1, linesOnSurface)*triangularForm(T2, linesOnSurface))
    );

    return forms
)


fiveCycles = G -> (

    V := vertices(G);
    E := edges(G);

    adj := (u,v) -> member(set {u,v}, E);
    select(subsets(V, 5), S -> (
        a := S#0;
        rest := set drop(S, 1);
        any(toList rest, b ->
            adj(a, b) and
            any(toList(rest - set{b}), c ->
                adj(b, c) and
                any(toList(rest - set{b,c}), d ->
                    adj(c, d) and (
                        e := first toList(rest - set{b,c,d});
                        adj(d, e) and adj(e, a)
                    )
                )
            )
        )
    ))
)


pentagonForms = P -> (

    linesOnSurface := linesOnACubicSurface P;
    S := ring linesOnSurface_0;
    G := lineIncidenceGraph(linesOnSurface);
    I := sub(equationOfCubicSurface(P), S);
    tris := triangles(G);
    pents := fiveCycles(G);

    forms := for C in pents list(

        T1 := select(subsets(C, 3), c -> member(sort c, tris));

        if #T1 == 0 then continue else T1 = first T1;

        (b, c) := toSequence select(C, i -> not member(i, T1));
        a := first toList intersect(neighbors(G, b), neighbors(G, c));
        
 

        h1 := triangularForm(T1, linesOnSurface);
        h2 := triangularForm(sort({a,b,c}), linesOnSurface);
        
        (i, j) := toSequence select(T1, l -> degree(inducedSubgraph(G, C), l) == 3);
        g := (joinIdeal(linesOnSurface_a, linesOnSurface_i + linesOnSurface_j))_0;

        g/(h1*h2)
    );

    return forms
)

end
needs "CubicSurface.m2"

-- compute the equation of the cubic surface
cubicBasis = matrix {basisOfCubics P}
R = ring cubicBasis
linesOnSurface = linesOnACubicSurface P;
G = lineIncidenceGraph(linesOnSurface)
I = equationOfCubicSurface(P)
S = ring I

-- compute the canonical forms
tForms = matrix {triangleForms(P)};
qForms = matrix {quadForms(P)};
pForms = pentagonForms(P);


-- compute a basis for each set of canonical forms
-- here we use only the quadrilaterals
randomPts = for i from 1 to 500 list(

    paramVals := matrix {apply(gens R, i -> random(-10, 10))};
    sub(sub(cubicBasis, paramVals), QQ)
);


-- to compute a basis we simply sample random points and them compute the linear relations amongst the forms
Mq = matrix for p in randomPts list try flatten entries sub(qForms, p) else continue;
K = gens ker Mq;
T = QQ[x_1..x_(numcols qForms)];
BQ = support(basis(1, T) % (ideal(basis(1, T)*sub(K, QQ)))) / index;
basisForms = sub(qForms_BQ, frac S);


-- compute the log canonical embedding of the cubic surface without its 27 lines
use S
df = homogenize(diff(y_3, sub(I_0, y_0 => 1)), y_0)
scaledBasisForms = (1/df)*basisForms;

-- compute the quadratic relations
Z = QQ[z_1..z_109];
B = basis(2, Z);

randomPts = for i from 1 to numcols(B) list(

    paramVals := matrix {apply(gens R, i -> random(ZZ/nextPrime(10000000)))};
    cubicSurfacePt := sub(cubicBasis, paramVals);
    imVals := sub(scaledBasisForms, cubicSurfacePt)
);


MZ = matrix for p in randomPts list flatten entries sub(B, p);
KZ = gens ker MZ;
J = ideal(B*sub(KZ, QQ));


