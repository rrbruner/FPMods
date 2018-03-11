#------------------------Functions-for-Resolutions---------------------------------------

from sage.categories.homset import Hom

def lift(f, g):
    """
    Compute the lift of `f` over `g`, so that `g\cdot \text{lift}(f,g) = f`.
    All maps taken to be FP_Homs. If lift doesn't exist, ``False`` is
    returned with the trivial morphism.

    INPUT:

    -  ``f``  - The map to be lifted over.

    -  ``g``  - The map lifted over.

    OUTPUT: The lift of f over g.

    EXAMPLES::

    """
    if f.codomain != g.codomain:
        raise TypeError, "Cannot lift maps with different codomains."
    values = []
    for x in f.domain().gens():
        new_value = g.solve(f(x))
        if new_value is None:
            return None
        values.append(new_value)
    return Hom(f.domain(), g.domain())(values)


def Homology(f,g):
    """
    Computes the Homology of a pair of maps.

    INPUT:

    -  ``f`` - The FP_Hom corresponding to the first map of the composition.

    -  ``g`` - The second (or last) FP_Hom in the composition.

    OUTPUT:

    -  ``p``  - The map from `Ker(g)` to `Ker(g)/Im(f)`

    -  ``i``  - The inclusion of `Ker(g)` into domain of `g`.

    -  ``m``  - The inclusion of `Im(f)` into the domain of `g`.

    -  ``l``  - The lift of `m` over `i`.


    """
    i = g.kernel()
    m,e = f.image()
    l = lift(m, i)
    if l is None:
        raise ValueError, "The image is not contained in the kernel."
    p = l.cokernel()
    return p,i,m,l


def extend_resolution_kernels(R,n,verbose=False):
    """
    Extends a resolution `R` to length `n`.

    INPUT:

    -  ``R``  - A list of FP_Homs, corresponding to a resolution.

    -  ``n``  - The length to which the resolution will be extended to.

    OUTPUT: A list of FP_Homs, corresponding to the extended resolution.

    EXAMPLES::

    """
    raise RuntimeError, 'Not implemented'

    if n < len(R):
        return R
    if verbose:
        print "Step ",1+n-len(R)
    K,i = R[-1][1]
    kers = [R[i][1] for i in range(len(R))]
    r,k = K.resolution_kernels(n-len(R),kers,verbose=verbose)
    r[0] = i*r[0]
    return R + r, kers

def extend_resolution(R,n,verbose=False):
    """
    Extends a resolution `R` to length `n`.

    INPUT:

    - ``R`` -- A list of FP_Homs, corresponding to a resolution.

    - ``n`` -- The length to which the resolution will be extended to.

    OUTPUT: A list of FP_Homs, corresponding to the extended resolution.

    EXAMPLES::

        sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.module import create_fp_module
        sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.resolutions import *
        sage: M = create_fp_module([0, 5], [(Sq(2)*Sq(2)*Sq(2), Sq(1))])
        sage: r1 = M.resolution(4)
        sage: r12 = extend_resolution(r1, 8)
        sage: r = M.resolution(8)
        sage: # Compare each function in the lists:
        sage: r == r12
        True
        sage: r[4] == r12[5]
        False

    """
    if n < len(R):
        return R
    if verbose:
        print "Step ",1+n-len(R)
    i = R[-1].kernel()
    r = i.domain().resolution(n-len(R),verbose=verbose)
    r[0] = i*r[0]
    return R + r

def is_complex(R):
    """
    Determines whether a resolution `R` is a valid chain complex.

    INPUT:

    -  ``R``  - A list of FP_Homs, forming a resolution.

    OUTPUT: True if `R` corresponds to a complex, false otherwise.

    EXAMPLES::

    """
    val = True
    i = 1
    while val and i < len(R):
        val = val and (R[-i-1]*R[-i]).is_zero()
        i += 1
    return val

def is_exact(R):
    """
    Deteremines whether a resolution `R` is exact.

    INPUT:

    -  ``R``  - A list of FP_Homs, forming a resolution.

    OUTPUT: True if the list of FP_Homs passed is exact, false otherwise.

    EXAMPLES::

    """
    if not is_complex(R):
        return False
    if len(R) < 2:
        return False

    # Use homology to show exactness.
    for i in range(len(R) - 1):
        p,i,m,l = Homology(R[i+1], R[i])
        if not p.is_zero():
            return False

    return True
    # Sverre: This is the original code, which might be faster than
    #         using homology, as above:
    #      
    #    val = True
    #    i = 0
    #    while val and i < len(R)-1:
    #        K,j = R[i].kernel_gens() ## Not implemented.
    #        for x in K.gens():
    #            val = val and R[i+1].solve(j(x))[0]
    #            if not val:
    #                break
    #        i += 1
    #    return val

def chain_map(L,R,f):
    """
    Computes the lift of an FP_Hom over a resolution. `L` and `R` are
    resolutions, and `f` is an FP_Hom from L[0].codomain to R[0].codomain.

    INPUT:

    -  ``L``  - A list of FP_Homs, corresponding to a resolution.

    -  ``R``  - A list of FP_Homs, corresponding to a resolution.
    """
    raise RuntimeError, 'Not implemented'

    if len(L) == 0 or len(R) == 0:
        return [f]
    l = lift(f*L[0],R[0])[1]
    i = 0
    Z = [f]
    Z.append(l)
    for i in range(1,min(len(L),len(R))):
         Z.append(lift(Z[i]*L[i],R[i])[1])
    return Z

def extension(R,e,test=True):
    """
    Computes the module M corresponding to the presumed cocycle `e'.
    R must be a resolution of length at least 3, and e must be a cocycle.
    The checks of these can be bypassed by passing test=False.
    """
    raise RuntimeError, 'Not implemented'

    if test == True:
        if len(R) < 3:
            raise ValueError, "Resolution not of length at least 3"
        if not is_exact([R[0],R[1],R[2]]):
            raise TypeError, "Not a valid resolution"
        if not (e*R[2]).is_zero():
            raise TypeError, "Not a cocycle"
    M,I,P = DirectSum([R[0].domain,e.codomain])
    C,p = (I[0]*R[1] - I[1]*e).cokernel()
    N,q = (p*I[1]).cokernel()
    v = [R[0].solve(g)[1] for g in R[0].codomain.gens()]
    g = FP_Hom(R[0].codomain,N,[(q*p*I[0])(x) for x in v])
    j = lift(q,g)
    return M,p*I[1],j


