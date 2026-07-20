using Oscar
import Oscar.kernel


# compute all regions by iteratively building all valid sign patterns 
function all_regions(A::Vector{Vector{Int64}}, b::Vector{Int64})

    A = [QQ.(a) for a in A]
    b = QQ.(b)

    d = length(A[1])
    m = length(A)

    regions = Polyhedron{QQFieldElem}[]

    # stack holds partial sign patterns
    stack = [(zeros(QQ, 0, d), zeros(QQ, 0), 1)]

    while !isempty(stack)

        Acur, bcur, i = pop!(stack)

        # if everything has a sign then push it
        if i > m
            P = polyhedron(QQ, Acur, bcur)
            if dim(P) == d
                push!(regions, P)
            end
            continue
        end

        a = A[i]
        bi = b[i]

        # ax <= bi
        A1 = vcat(Acur, reshape(a, 1, d))
        b1 = vcat(bcur, bi)

        if dim(polyhedron(A1, b1)) >= 0
            push!(stack, (A1, b1, i+1))
        end

        # ax >= bi
        A2 = vcat(Acur, reshape(-a, 1, d))
        b2 = vcat(bcur, -bi)

        if dim(polyhedron(A2, b2)) >= 0
            push!(stack, (A2, b2, i+1))
        end
    end

    return regions
end


# take only the bounded regions
function bounded_regions(A::Vector{Vector{Int64}}, b::Vector{Int64})

    regions = all_regions(A, b)
    return filter(is_bounded, regions)
end


# compute the residual arrangement
function residual_points(P::Polyhedron)
    
    n = ambient_dim(P)
    F = []

    # extract ineqs from polytope
    for f in facets(P)
        push!(F, hcat((f.a), matrix([-f.b])))
    end

    # switch to homogeneous coordinates in the polytope
    F = reduce(vcat, F)
    homP = polyhedron(F, [0 for i in 1:n_facets(P)])

    # compute the hyperplanes of the matroid on the facet normals
    M = matroid_from_matrix_rows(F)
    H = hyperplanes(M)

    # find all the residual points
    # store them in a dictionary whose keys are their orders
    res_pts = Dict()
    
    for h in H 

        # compute the corresponding intersection points
        hom_pt = nullspace(F[h, :])[2]
        p = [hom_pt[i, 1] for i in 1:n+1]
        
        res_pts[p] = order(homP, p, is_projective = true)
    end

    return res_pts
end


function order(P::Polyhedron, x::Vector ; is_projective = false)

    if is_projective
        n = ambient_dim(P) - 1
    else
        n = ambient_dim(P)
    end

    containing_hyperplanes = filter(f -> ((f.a)*x)[1] == f.b, facets(P))


    if x in P
        return length(containing_hyperplanes) - n
    else
        return length(containing_hyperplanes) - n + 1
    end
end


# build the matrix of linear conditions on the coefficients of a polynomial 
# which vanishes to the specified order on the residual 
function residual_linear_conditions(B::Vector{<:MPolyRingElem}, res_pts::Dict, R::MPolyDecRing)

    rows = Vector{QQFieldElem}[]

    for (p, k) in res_pts
        for t in 0:(k - 1)
            for m in monomial_basis(R, t)

                alpha = exponent_vector(m, 1)

                row = QQFieldElem[]
                for f in B
                    g = f
                    for i in 1:length(alpha), _ in 1:alpha[i]
                        g = derivative(g, gen(R, i))
                    end
                    push!(row, evaluate(g, p))
                end
                push!(rows, row)
            end
        end
    end

    return matrix(QQ, rows)
end


# compute the adjoint of a polyhedron
# later make R an optional argument
function adjoint(P::Polyhedron, R::MPolyDecRing)

    # compute residual points
    res_pts = residual_points(P)
    n = ambient_dim(P)
    r = n_facets(P)

    if r == n+1
        return R(1)
    end

    # candidate monomial basis for the adjoint, degree r - n - 1
    B = monomial_basis(R, r - n - 1)

    # one linear condition per (point, multi-index) pair, enforcing that f
    # and all its partials up to order k-1 vanish at each residual point
    M = residual_linear_conditions(B, res_pts, R)

    (d, N) = nullspace(M)

    return (B * N)[1]
end


function adjoint(P::Polyhedron)

    if is_bounded(P)
        n = ambient_dim(P)
    else 
        n = ambient_dim(P) - 1
    end

    R, x = graded_polynomial_ring(QQ, "x" => 1:n+1)

    return adjoint(P, R)
end


# evaluate a list of polynomials at a list of points
# the columns correspond to the polynomials and the 
function interpolate_polynomials(F, pts)

    M = matrix(QQ, [[evaluate(f, p) for f in F] for p in pts])
    (d, N) = nullspace(M)
    return F*N
end


# function 


# computes the canonical form of the polytope by computing its adjoint
function canonical_form(P::Polyhedron, R)

    F = []

    # extract ineqs from polytope
    for f in facets(P)
        push!(F, hcat(-1*(f.a), matrix([f.b])))
    end

    F = reduce(vcat, F)
    B = gens(R)

    denom = prod(F*B)

    return adjoint(P, R)//denom
end


function canonical_form(P::Polyhedron)


    n = ambient_dim(P)
    R, x = graded_polynomial_ring(QQ, "x" => 1:n+1)
    
    return canonical_form(P, R)
end


 # make parametrization of the log canonical model of P^n \ A
function log_canonical_map(A, b)

    # compute bounded regions
    bdr = bounded_regions(A, b)
    n = length(A[1])

    # setup rings
    R, x = graded_polynomial_ring(QQ, "x" => 1:n+1)
    S, z = polynomial_ring(QQ, "z" => 1:length(bdr))

    # compute canonical forms
    forms = [canonical_form(P, R) for P in bdr]

    #
    newR = forget_grading(R)

    # make map
    phi = hom(S, fraction_field(newR), [evaluate(f, gens(newR)) for f in forms])

    # implicitize map and return
    return phi
end


# function for computing the kernel of a rational map
function kernel(F::Oscar.MPolyAnyMap{QQMPolyRing, AbstractAlgebra.Generic.FracField{QQMPolyRingElem}, Nothing, AbstractAlgebra.Generic.FracFieldElem{QQMPolyRingElem}})

    S = domain(F)
    R = base_ring(codomain(F))
    E, t, x, z = polynomial_ring(QQ, "t" => 1:1, "x" => 1:ngens(R), "z" => 1:ngens(S))

    # put everything in the same ring
    images = map(F, gens(S))
    f = map(i -> evaluate(numerator(i), x), images)
    g = map(i -> evaluate(denominator(i), x), images)

    I = ideal([g[i]*z[i] - f[i] for i in 1:ngens(S)]) + ideal(t[1]*prod(g) - 1)

    return eliminate(I, vcat(t, x))
end


# 
function log_canonical_model(A, b)

    
    F = log_canonical_map(A, b)

    # implicitize map and return
    return kernel(F)
end