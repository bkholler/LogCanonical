include("HyperplaneArrangements.jl")


# explicit example of 5 lines in P^2 which are not generic
# Note that the input is dehomogenized in order to visualize the chambers
A = [
    [1, 0],
    [0, 1],
    [-2, -3],
    [-1, -2],
    [-5, -7]
]
b = [0, 0, -1, -1, -3] 


# compute all regions and visualize them.
all_regs = all_regions(A, b)
visualize(all_regs)


# compute only the bounded regions
bd_regs = bounded_regions(A, b)
visualize(bd_regs)


# compute the canonical form of a single polytope 
forms = map(canonical_form, bd_regs)
forms[2]
factor(denominator((forms[2])))



# compute the parametrization of the log canonical model via canonical forms
# then obtain the actual log canonical model in PP^(# bounded regions) by implicitization
F = log_canonical_map(A, b)
I = log_canonical_model(A, b)