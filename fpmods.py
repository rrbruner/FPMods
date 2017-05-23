r"""
Finitely presented modules over the Steenrod Algebra.

This package allows the user to define finitely presented modules
over the Steenrod Algebra, elements of them, and morphisms. With 
these objects, the user can perform more complex computations, using
the secondary functions defined. 

This package is designed to work with modules over the whole Steenrod
algebra.  To make calculations finite, we take account of the fact
that finitely presented modules are defined over a finite sub Hopf
algebra of the Steenrod algebra.

AUTHORS:

- Robert R. Bruner, Michael J. Catanzaro (2012): initial version

EXAMPLES:

    sage: M = FP_Module([0,1],[[Sq(2),Sq(1)],[0,Sq(2)]])
    
    
    
    
#*****************************************************************************
#       Copyright (C) 2011 Robert R. Bruner <rrb@math.wayne.edu>
#             and          Michael J. Catanzaro <mike@math.wayne.edu>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#*****************************************************************************


fpmods.py
Ver 1.1
12/13/2011
"""
#-------------------------------------------------------------------------------
#--------------------------Utility-functions------------------------------------
#-------------------------------------------------------------------------------


def maxim(L):
    """
    Input a list of tuples and this function returns a tuple whose i-th entry is the 
    max of the i-th entries in the tuples in L, where shorter tuples are extended
    by adding 0's

    INPUT:

    -  ``L``  - A list of tuples

    OUTPUT: The component-wise maximum of the entries of L

    EXAMPLES::

    sage: maxim([[1,2,3,4],[5,4]])
    [5,4,3,4]
    sage: maxim([[1,2,3,4],[1,1,1,5],[9]])
    [9, 2, 3, 5]

    """
    if len(L) == 1:
        return [L[0][i] for i in range(len(L[0]))]
    else:
        t1 = maxim([L[i] for i in range(1,len(L))])
        t2 = [L[0][i] for i in range(len(L[0]))]
	mm = max(len(t1),len(t2))
	t1 = t1 + (mm - len(t1))*[0]
	t2 = t2 + (mm - len(t2))*[0]
	return map(max,zip(t1,t2))

def _deg_(degs,co):
    """
    Computes the degree of an FP_Element. `degs' is a list of integral degrees,
    and `co' is a tuple of Steenrod operations, as in an FP_Element.
    If all coefficients are 0, returns None.

    INPUT:

    -  ``degs``  - A list of integers.

    -  ``co``  -  A list of Steenrod algebra elements.

    OUTPUT: The degree of the FP Element formed by `degs` and `co`.

    EXAMPLES::

    sage: A = SteenrodAlgebra(2)
    sage: _deg_((0,2,4),(Sq(4),Sq(2),Sq(0)))
    4
    sage: _deg_((3,3),(Sq(2)*Sq(1),Sq(1)*Sq(2)))
    6

    """
    if len(degs) != len(co):
        raise ValueError,\
        "Wrong number (%s) of coefficients. Should be %s.\n" % (len(co),len(degs))
    nz = filter(lambda i: co[i] != 0, range(len(degs)))  # figure out which are
    d = [degs[i]+co[i].degree() for i in nz]            # non-zero
    if len(d) == 0:
        return None
    if min(d) != max(d):
        raise ValueError, "Inhomogeneous element"
    return min(d) 

def max_deg(alg):
    """
    Computes the top nonzero degree of a sub-algebra of the Steenrod Algebra.

    INPUT:

    -  ``alg``  - A sub-algebra of the Steenrod Algebra.

    OUTPUT:

    -  ``topdeg`` - The top nonzero degree of `alg`.

    EXAMPLES::

    sage: A2 = SteenrodAlgebra(p=2, profile = (3,2,1))
    sage: max_deg(A2)
    23
    sage: K = SteenrodAlgebra(p=2,profile=(0,))
    sage: max_deg(K)
    0
    sage: max_deg(SteenrodAlgebra(p=5,profile=((3,2,1),(1,1,1))))
    3136


    """
    if alg._truncation_type == +Infinity:
        raise ValueError, "Maximum degree is +Infinity"
    p = alg._prime
    if p == 2:
        topdeg = 0
        prof = [0] + list(alg._profile)
        for i in range(len(prof)):
            topdeg += (2**(i) -1)*(2**(prof[i])-1) 
        return topdeg
    else: # p odd
        topdeg, epsdeg = (0,0)
	prof = [0] + list(alg._profile[0])
	for i in range(len(prof)):
	    topdeg += 2*(p**i-1)*(p**(prof[i])-1)
	prof2 = list(alg._profile[1])
        for i in range(len(prof2)):
	    epsdeg += (2*p**(i)-1)*(prof2[i]-1)
	return epsdeg+topdeg

def pmax_deg(prof,p=2):
    """
    Computes the top nonzero degree of the sub-algebra of the Steenrod Algebra
    corresponding to the profile passed. Note: Does not have to be a valid profile,
    only a tuple or list of nonnegative integers.

    INPUT:

    -  ``p``  - The prime over which the degree computation is made. By default, `p` = 2.

    -  ``prof`` - A profile function corresponding to a sub-algebra of the Steenrod
                  Algebra. If `p` =2, `prof` is a list or tuple. If `p` is odd, `prof`
		  is a 2-tuple, corresponding to each piece of a profile function.
    OUTPUT:

    -  ``topdeg`` - The top nonzero degree of the sub-algebra.

    EXAMPLES::

    sage: pmax_deg((2,1))
    6
    sage: pmax_deg(((3,2,1),(1,1,1)),p=3)
    336


    """
    if p == 2:
        topdeg = 0
        prof = [0] + list(prof)
        for i in range(len(prof)):
            topdeg += (2**(i) -1)*(2**(prof[i])-1) 
        return topdeg
    else: # p odd
        topdeg, epsdeg = (0,0)
	prof1 = [0] + list(prof[0])
	prof2 = list(prof[1])
	for i in range(len(prof1)):
	    topdeg += 2*(p**i-1)*(p**(prof1[i])-1)
        for i in range(len(prof2)):
	    epsdeg += (2*p**(i)-1)*(prof2[i]-1)
	return epsdeg+topdeg



def _del_(i,n):
    """
    A list form of the Kronecker delta function. 

    INPUT:

    -  ``i``  - The position at which the list will take the value 1.

    -  ``n``  - The length of the list

    OUTPUT:

    -  ``ll``  - A list of length `n`, consisting of all zeros except 
                  for a 1 in    `i^{th}` position.

    EXAMPLES::

    sage: _del_(2,4)
    [0, 0, 1, 0]
    sage: _del_(0,3)
    [1, 0, 0]
    sage: _del_(6,4)
    ValueError: List of length 4 has no entry in position 6.

    """
    if i >= n:
        raise ValueError, "List of length %d has no entry in position %d." % (n,i)
    ll = n*[0]
    ll[i] = 1
    return ll

def mod_p_log(n,p):
    """
    Input an integer n and a prime p
    Output the k so that p^{k-1} lt n le p^k

    EXAMPLES::

    sage: mod_p_log(1,4)
    1
    sage: mod_p_log(8,3)
    2
    sage: mod_p_log(9,3)
    3

    """
    k=0
    pow=1
    while n >= pow:
        k += 1
	pow *= p
    return k

def DirectSum(alist,char=None):
    """
    Returns the direct sum of the list of FP_Modules passed. A list of inclusion maps and
    a list of projection maps are also returned.

    INPUT:

    -  ``alist``  -  A list of FP_Modules.

    OUTPUT:

    -  ``M``  - The direct sum of Modules in `alist`.

    -  ``incl``  - A list of inclusion maps, one from each module to M.

    -  ``proj``  - A list of projection maps, from M to the modules.

    """
    if len(alist) == 0 and char == None: 
	raise ValueError, "Empty Direct Sum -- undefined characteristic."
    elif len(alist) == 0:
        M = FP_Module([],[],char=char)
	M, incl, proj = M.copy()
	return M, [incl],[proj]
    elif len(alist) == 1:
        M,incl,proj = alist[0].copy()
	return M,[incl],[proj]  # return lists
    else:
        if char == None:
            char = alist[0].char
	else:
	    if alist[0].char != char:
	        raise ValueError,\
		"Characteristic passed (%d) differs from characteristic of module (%d)."\
		    % (char, alist[0].char)
	alg = SteenrodAlgebra(p = alist[0].char,profile=\
                  enveloping_profile_profiles([x.profile() for x in alist],char))
        listdegs = reduce(lambda x,y: x+y, [x.degs for x in alist])
        numdegs = len(listdegs)
        listrels = [[Integer(0) for i in range(numdegs)] for k in range(\
                 reduce(lambda x,y: x+y, [len(x.rels) for x in alist]))] #initialize rels
        # now scan through each module in sum, each list of rels for each module, and
        # each rel in each list of rels. modn keeps track of each module, reln keeps
        # track of the rel.
	## Hard-coded sage Integer(0), else raises ERROR above in e_p_e.
        modn = 0
        reln = 0
        for i in range(len(alist)):
            for j in range(len(alist[i].rels)):
	        for k in range(len(alist[i].rels[j])):
		    listrels[modn+j][reln+k] = alist[i].rels[j][k]
	    modn += len(alist[i].rels)
	    reln += len(alist[i].degs)
	M = FP_Module(listdegs,listrels, algebra = alg)
        incl = len(alist)*[[]]
	proj = len(alist)*[[]]
	posn = 0
	for i in range(len(alist)):
            incl[i] = FP_Hom(alist[i],M,[M.gen(posn+j)\
	         for j in range(len(alist[i].degs))])
            pvals = numdegs*[0]
	    for j in range(len(alist[i].degs)):
	        pvals[posn+j] = alist[i].gen(j)
            proj[i] = FP_Hom(M,alist[i],pvals)
	    posn += len(alist[i].degs)   
	return M, incl, proj

#------------------------Functions-for-Resolutions---------------------------------------

def lift(f,g):
    """
    Computes the lift of f over g, so that g*lift(f,g) = f. 
    All maps taken to be FP_Homs. If lift doesn't exist, False is
    returned with the 0 map.

    INPUT:

    -  `f`  - The map to be lifted over.

    -  `g`  - The map lifted over.

    OUTPUT: The lift of f over g.

    EXAMPLES::


    """
    if f.codomain != g.codomain:
        raise TypeError, "Cannot lift maps with different codomains."
    vals = []
    cando = true
    for x in f.domain.gens():
	if cando:
            newval = g.solve(f(x))
	    cando = cando and newval[0]
            vals.append(newval[1])
    if cando:
        return true,FP_Hom(f.domain,g.domain,vals)
    else:
        return false,FP_Hom(f.domain,g.domain,0)


def Homology(f,g):
    """
    Computes the Homology of a pair of maps. 

    INPUT:

    -  ``f`` - The FP_Hom corresponding to the first map of the composition.

    -  ``g`` - The second (or last) FP_Hom in the composition.

    OUTPUT:

    -  ``H``  - The quotient `Ker(g)/Im(f)`

    -  ``p``  - The map from `Ker(g)` to `H`

    -  ``i``  - The inclusion of `Ker(g)` into domain of `g`.

    -  ``m``  - The inclusion of `Im(f)` into the domain of `g`.

    -  ``l``  - The lift of `m` over `i`.

             
    """
    K,i = g.kernel()
    I,e,m = f.image()
    l = lift(m,i)[1]  # the map, not the bool
    H,p = l.cokernel()
    return H,p,i,m,l
        
	
def extend_resolution_kernels(R,n,verbose=false):
    """
    Extends a resolution `R` to length `n`.

    INPUT:

    -  ``R``  - A list of FP_Homs, corresponding to a resolution.

    -  ``n``  - The length to which the resolution will be extended to.

    OUTPUT: A list of FP_Homs, corresponding to the extended resolution.

    EXAMPLES::


    """
    if n < len(R):
        return R
    if verbose:
        print "Step ",1+n-len(R)
    K,i = R[-1][1]
    kers = [R[i][1] for i in range(len(R))]
    r,k = K.resolution_kernels(n-len(R),kers,verbose=verbose)
    r[0] = i*r[0]
    return R + r, kers

def extend_resolution(R,n,verbose=false):
    """
    Extends a resolution `R` to length `n`.

    INPUT:

    -  ``R``  - A list of FP_Homs, corresponding to a resolution.

    -  ``n``  - The length to which the resolution will be extended to.

    OUTPUT: A list of FP_Homs, corresponding to the extended resolution.

    EXAMPLES::


    """
    if n < len(R):
        return R
    if verbose:
        print "Step ",1+n-len(R)
    K,i = R[-1].kernel()
    r = K.resolution(n-len(R),verbose=verbose)
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
    val = True
    i = 0
    while val and i < len(R)-1:
        K,j = R[i].kernel_gens()
	for x in K.gens():
	    val = val and R[i+1].solve(j(x))[0]
	    if not val:
	        break
        i += 1
    return val

def chain_map(L,R,f):
    """
    Computes the lift of an FP_Hom over a resolution. `L` and `R` are 
    resolutions, and `f` is an FP_Hom from L[0].codomain to R[0].codomain.

    INPUT: 

    -  ``L``  - A list of FP_Homs, corresponding to a resolution.

    -  ``R``  - A list of FP_Homs, corresponding to a resolution.
    """
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

	

    
#----------------------------Profile-Functions-----------------------------------

## Palmieri pads all his profiles by adding a [0] to the beginning.
# Furthermore, when scanning over elements defined over an odd
# primary Steenrod Algebra, the Q part comes first, and then the P part.
# When defining a sub-algebra over an odd Steenrod algebra, the P part
# must come first in the profile.

# These functions return the P part first, and then the Q part.

from sage.algebras.steenrod.steenrod_algebra_misc import *

def profile_ele(alist,char=2):
    """
    Finds the smallest sub-Hopf algebra containing the element passed.
    `alist' is assumed to be an element of the Steenrod Algebra, (the only other
    possible cases are dealt with immediately) so it is treated as a list. 

    INPUT:

    -  ``alist`` -  An element of the Steenrod Algebra (or a sub-Hopf algebra
                 of it). Treated as a list.

    OUTPUT: The profile function corresponding to the smallest sub-Hopf algebra
    containing the element passed. 

    EXAMPLES::

        sage: A2 = SteenrodAlgebra(2)
        sage: profile_ele(A2.Sq(2))
        (2, 1)
        sage: profile_ele(A2.Sq(4,8))
	(3, 4, 3, 2, 1)


    """
    alist = SteenrodAlgebra(char)(alist)       # Coerce scalars if necessary
    if char == 2:
        alist2 = [e[0] for e in alist]
        maxlength = max([0]+[len(e) for e in alist2])
        alist2 = [list(e) + (maxlength-len(e))*[0] for e in alist2]  
        minprofile = [max([alist2[i][j] for i in range(len(alist2))]) \
                                                for j in range(maxlength)]
        minprofile = tuple(map(lambda xx: mod_p_log(xx,char),minprofile))
        return find_min_profile(minprofile,char)
    if char != 2:  
        alistQ = [e[0][0] for e in alist]
 	alistP = [e[0][1] for e in alist]
        maxlengthQ = max([0]+[len(e) for e in alistQ])
        maxlengthP = max([0]+[len(e) for e in alistP])
        alistQ = [list(e) + (maxlengthQ-len(e))*[0] for e in alistQ]  
        alistP = [list(e) + (maxlengthP-len(e))*[0] for e in alistP]  
        minprofileQ = [max([alistQ[i][j] for i in range(len(alistQ))]) \
                                            for j in range(maxlengthQ)]
        minprofileP = [max([alistP[i][j] for i in range(len(alistP))]) \
                                            for j in range(maxlengthP)]
        minprofileP = tuple(map(lambda xx: mod_p_log(xx,char),minprofileP))
        if not minprofileQ:
            minpQ=[]
	else:
	    minpQ = [1]*(max(minprofileQ)+1)
	    for j in minprofileQ:
	        minpQ[j] = 2
        return find_min_profile((minprofileP,minpQ),char=char)


def enveloping_profile_elements(alist,char=2):
    """
    Finds the profile function for the smallest sub-Hopf algebra containing
    the list of elements passed. Entries of `alist' are elements of the Steenrod 
    Algebra. Hence, each alist[i] is treated as a list. Accepts either a list of 
    lists or tuples.

    INPUT:

    -  ``alist``  - A list of Steenrod Algebra elements.

    OUTPUT: The profile function for the minimum sub-algebra containing all the 
    elements of `alist`.

    EXAMPLES::

        sage: enveloping_profile_elements([Sq(2),Sq(4)])
	(3, 2, 1)
	sage: enveloping_profile_elements([Sq(2,1,2),Sq(7)])
	(3, 2, 2, 1)

    """
    if char == 2:
        alist2 = list(map(profile_ele,[x for x in alist if  x != 0])) 
        if not alist2: 
             return (0,)
        maxlength = max([len(e) for e in alist2])
        alist2 = [list(e) + (maxlength-len(e))*[0] for e in alist2]  
        minprofile = tuple(max([alist2[i][j] for i in range(len(alist2))]) \
                                                for j in range(maxlength))
        return find_min_profile(minprofile)
    else:  
        masterlist = [profile_ele(x,char) for x in alist if x != 0]
        alistP = [x[0] for x in masterlist]
	alistQ = [x[1] for x in masterlist]
        if not alistP and not alistQ:
	    return ((0,),(0,))
        maxlengthQ = max([len(e) for e in alistQ])
	maxlengthP = max([len(e) for e in alistP])
        alistQ = [list(e) + (maxlengthQ-len(e))*[0] for e in alistQ]  
        alistP = [list(e) + (maxlengthP-len(e))*[0] for e in alistP]  
        minprofileQ = tuple(max([alistQ[i][j] for i in range(len(alistQ))]) \
                                                for j in range(maxlengthQ))
        minprofileP = tuple(max([alistP[i][j] for i in range(len(alistP))])\
	                                        for j in range(maxlengthP))
	return find_min_profile((minprofileP,minprofileQ),char=char)

def enveloping_profile_profiles(alist,char=2):
    """
    Finds the profile function for the smallest sub-Hopf algebra containing
    the sub-algebras corresponding the list of profile functions passed. Accepts
    either a list of lists or tuples.

    INPUT:

    -  ``alist``  - A list of profile functions.

    OUTPUT: The profile function for the minimum sub-algebra containing 
    the profile functions in `alist`.

    EXAMPLES::

        sage: enveloping_profile_profiles([[1,2,3],[2,4,1,1]])
	(2, 4, 3, 2, 1)
	sage: enveloping_profile_profiles([[4],[1,2,1],[3,2,3]])
	(4, 3, 3, 2, 1)

    """
    if char == 2:
        alist2 = list(copy(alist))
        maxlength = max([len(e) for e in alist2])
        alist2 = [list(e) + (maxlength-len(e))*[0] for e in alist2]  
        minprofile = tuple(max([alist2[i][j] for i in range(len(alist2))]) \
                                                for j in range(maxlength))
        return find_min_profile(minprofile)
    else:
        alistP = [copy(alist[i][0]) for i in range(len(alist))]
        alistQ = [copy(alist[i][1]) for i in range(len(alist))]
        maxlengthQ = max([len(e) for e in alistQ])
        maxlengthP = max([len(e) for e in alistP])
        alistQ = [list(e) + (maxlengthQ-len(e))*[0] for e in alistQ]  
        alistP = [list(e) + (maxlengthP-len(e))*[0] for e in alistP]  
        minprofileQ = tuple(max([alistQ[i][j] for i in range(len(alistQ))]) \
                                                for j in range(maxlengthQ))
        minprofileP = tuple(max([alistP[i][j] for i in range(len(alistP))]) \
                                                for j in range(maxlengthP))
        return find_min_profile((minprofileP,minprofileQ),char=char)


def valid(LL,char=2):
    """
    Determines if the list passed is a valid profile. 
    ## When checking at odd primes, the `P`-part must be the 0th entry in LL,
    and the `Q`-part must be the 1st entry in LL.

    INPUT:

    -  ``LL``  - A list of non-negative integers.

    OUTPUT: True or False, depending on whether the list passed is a valid profile.

    EXAMPLES::

        sage: valid([3,2,1])
	True
	sage: valid([1,2,3])
	False

    """
    if char == 2:
        L = [0] + list(LL) + [0]*(len(LL)) # Add 0 in beginning to keep rels correct
        value = true                       # so r - i works when i = 0
        for r in range(2,len(L)):  
            for i in range(1,r):   
                value = value and ((L[r] >= L[r-i] - i) or (L[r] >= L[i]))
        return value
    else:
        (alistP,alistQ) = (LL[0],LL[1])
	M = [0] + list(alistP) + [0]*len(alistP)
	L = list(alistQ) + [1]*(len(alistQ)+1)
	M = M + [0]*abs(len(M)-len(L))  # Pad so they're the same length
	L = L + [1]*abs(len(M)-len(L))
	value = valid(alistP,char=2)  # P part must satisfy same conditions, regardless of prime.
	for r in range(len(L)): # \tau's indexed at 0, unlike \xi 's
	    if (L[r] == 1) and value:  
                for i in range(r+1):
		    value = value and ((M[i] <= r -i) or (L[r-i] == 1))
        return value

def nextprof(p,n,char=2):
    """
    Takes a possible profile `p' and a base profile `n'. Returns the next 
    profile in lexicographic order. After all valid profiles `p' of 
    length = len(n) have been checked, n is increased. Intended for internal
    use only. The odd primary piece only alters the Q part of the profile. To
    increment the P part of a profile for odd primes, call nextprof with char =2.
    This works since the P part of the profile is identical to the profile 
    function when char == 2.

    INPUT:

    -  ``p``  - A pseudo-profile function which is incremented lexicographically
    and checked for validity.

    -  ``n``  - The base pseudo-profile function.

    OUTPUT: The next lexicographic profile.

    EXAMPLES::

        sage: nextprof([1,2],[1,2])
	[2, 2]
	sage: nextprof([2,2],[1,2])
	[1, 2, 1]

	sage: nextprof([2,2,3],[1,2,3])
	[3, 2, 3]
	sage: nextprof([3,2,3],[1,2,3])
	[1, 3, 3]

    """
    if char == 2:
        for i in range(len(p)):    
            if p[i] < len(p):     # we increment here because we can without altering length
                p[i] += 1
                return p
            else:
                if i > len(n)-1:               # Past end of n, so reset to 0
                    p[i] = 0
                else:                          # inside n still, so reset to n
                    p[i] = n[i]
        return n + [0]*(len(p)-len(n)) + [1]    # fell off the end
    else:  # odd primes
        pP,pQ,nP,nQ = list(p[0]),list(p[1]),list(n[0]),list(n[1])
        for i in range(len(pQ)):
	    if pQ[i] < 2:
	        pQ[i] += 1
		return pQ
	    else:
	        if i > len(nQ) -1:
		    pQ[i] = 1
		else:
		    pQ[i] = nQ[i]
	return nQ + [1]*(len(pQ)-len(nQ)) +[1]


def find_min_profile(prof,char=2):
    """
    Given a tuple of integers (a pseudo-profile), this function will
    output the smallest legal profile function containing it. This 
    function combines the above functions, and is the only one intended
    for external use.

    INPUT:

    -  ``prof``  - A list or tuple of nonnegative integers.

    OUTPUT:

    -  ``p`` - A valid profile containing ``p``.

    EXAMPLES::

        sage: find_min_profile([1,2])
	(1, 2, 1)
	sage: find_min_profile([2,1])
	(2, 1)
	sage: find_min_profile([1,2,3])
	(1, 2, 3, 1, 1)

    """
    if char == 2:
        prof2 = list(prof)
        if not prof2:
            return (0,)
        r = 0  
        for i in range(len(prof2)):
            if prof2[i] != 0:
                r = i
        n = [prof2[i] for i in range(r+1)]
        p = copy(list(n))  
        while not valid(p,char):
            p = nextprof(p,n,char)
        return tuple(p)
    else:
        pP,pQ = list(prof[0]), list(prof[1])
	P = find_min_profile(pP,char=2)
	Q = copy(pQ)
	while not valid([P,Q],char):
	    Q = nextprof([P,Q],[P,pQ],char)
	return (P,Q)

#--------------------------------------------------------------------------------
#----------------------Finitely-Presented-Modules--------------------------------
#--------------------------------------------------------------------------------

class FP_Module(SageObject):
    r"""
    A finitely presented module over a sub-Hopf algebra of the
    Steenrod Algebra (including the full Steenrod Algebra).


A  module's profile is taken to be the smallest one over which it can
be defined, unless explicitly raised by passing a profile parameter.
The coefficients of an element of that module (FP_Element), however,
can lie anywhere in the Steenrod algebra: our profiles are simply
recording the subalgebra over which the module is defined, not forcing
the module into the category of modules over that subalgebra. To make
computing with elements easier, an element also has a profile,
and computing with elements involves finding the enveloping profile.   

    INPUT:
    
    - ``degs`` - a list of integers, specifying the degrees of the generators.

    - ``rels`` - (default: []) a list of relations. By default, the list is
      empty, i.e. the module is free.

    - ``char`` - (default: 2) the characteristic of the module. By default,
      it is the characteristic of the algebra specified, or else 2.

    - ``algebra`` - The Steenrod algebra or some sub-Hopf algebra of it.

    OUTPUT:

    - A finitely presented module with generators in degrees ``degs`` and 
      relations specified by ``rels``.       

    EXAMPLES:
    
    These examples show how to define modules over the Steenrod Algebra at the
    prime 2. The last example is a free module with a single generator in
    degree 4.
    
    ::

        sage: M = FP_Module([2,3],[[Sq(2),Sq(1)],[0,Sq(2)]])
	sage: N = FP_Module([0,1],[[Sq(2),Sq(1)]])
	sage: K = FP_Module([4])

    To define a module over the mod `p` Steenrod algebra, when `p` is odd,
    you should first define a Steenrod algebra::
    
	sage: A3 = SteenrodAlgebra(3)

    Here we show how to define modules over odd primary Steenrod Algebras.::

        sage: L = FP_Module([0,8],[[A3.P(2),1]],algebra=A3)
        sage: Q = FP_Module([2],algebra = SteenrodAlgebra(5))
    
    The following examples show how to extract the parameters used when defining
    an FP_Module.::

        sage: N.degs
	[0, 1]
	sage: N.rels
	[[Sq(2), Sq(1)]]
	sage: N.char
	2
	sage: N.algebra
	sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [2, 1]
    
    .. WARNING::

        The algebra attribute should not be used, but rather the alg() method, as shown
	below. For example, if extra relations not contained in this algebra 
	are added to a module, the alg() method will keep 
	track of this enlarged algebra, whereas the algebra attribute will not. 
        A similar situation occurs with the relations of the degrees. There is
	an attribute reldegs which keeps track of this, but the method rdegs() should
	be called instead for the same reason.

    Modules have alg() methods, keeping track of the smallest sub-Hopf algebra of
    the Steenrod Algebra they can be defined over. Given the above definitions

        sage: M.alg()
	sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [2, 1]
        sage: L.alg()
	sub-Hopf algebra of mod 3 Steenrod algebra, milnor basis, profile function ([1], [])

    """

    def __init__(self,degs,rels=[],char=None,algebra=None):
        """
	See ``FP_Module`` for full documentation.
        """

        if (char is None) and (algebra is None):
            self.char = 2
            self.algebra = SteenrodAlgebra(self.char, profile=(0,))
        elif (char is None) and (algebra is not None):
            self.algebra = algebra
            self.char = self.algebra._prime
        elif (char is not None) and (algebra is None):
            self.char = char
	    if char == 2:
                self.algebra = SteenrodAlgebra(p=self.char, profile=(0,))
	    else:
	        self.algebra = SteenrodAlgebra(p=self.char, profile = ((),(0,)))
        else:
            self.char = char
            self.algebra = algebra
        if (self.char != self.algebra.prime()):
            raise TypeError, "Characteristic and algebra are incompatible."
	if degs != sorted(degs):
	    raise TypeError, "Degrees of generators must be in non-decreasing order."
        if not rels:
            prof = self.algebra._profile
        else:

            prof = enveloping_profile_profiles(\
                     [enveloping_profile_elements(r,self.char) for r in rels]\
                     +[list(self.algebra._profile)],self.char)
        self.algebra = SteenrodAlgebra(p=self.char,profile=prof)
	for r in rels:  
	    if r == [0]*len(degs):
	        rels.remove([0]*len(degs))
        self.rels = [[self.algebra(coeff) for coeff in r] for r in rels]
        self.degs = copy(degs)
        try:                        # Figure out if a rel isnt right
            self.reldegs = [_deg_(self.degs,r) for r in self.rels]
        except ValueError:
            for r in rels:          # Figure out which rel isnt right
                try:
                   _deg_(degs,r)
                except ValueError:
                   raise ValueError, "Inhomogeneous relation %s" % r


    def profile(self):
        """
	Returns the profile of the smallest sub-Hopf algebra of the Steenrod algebra
	over which the module can be defined.

	EXAMPLES::

	    sage: Z = FP_Module([0],[[Sq(1)],[Sq(2)],[Sq(4)]]); Z.profile()
	    (3, 2, 1)

	"""
	return self.algebra._profile

    def alg(self):
	"""
	Returns the smallest sub-Hopf algebra of the Steenrod algebra over which the
	module can be defined.

	EXAMPLES::

	    sage: X = FP_Module([0,2,3]);X.alg()
	    sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function []
	    sage: XX = FP_Module([0,2,3],[[0,Sq(1),1]]);XX.alg()
	    sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [1]

	"""
        return self.algebra

    def conn(self):
        """
	Returns the connectivity of the module.

	EXAMPLES::

	    sage: X = FP_Module([0,2,3]);X.conn()
	    0
	    sage: M = FP_Module([2,3],[[Sq(2),Sq(1)],[0,Sq(2)]]);M.conn()
	    2
	    sage: Q = FP_Module([]);Q.conn()
	    +Infinity
        """
        return min(self.degs+[+infinity])

    def rdegs(self):
        """
	Returns the degrees of the relations of the module.

	EXAMPLES::

	    sage: XX = FP_Module([0,2,3],[[0,Sq(1),1]]);XX.rdegs()
	    [3]
	    sage: M = FP_Module([2,3],[[Sq(2),Sq(1)],[0,Sq(2)]]);M.rdegs()
	    [4, 5]
	"""
        return [_deg_(self.degs,r) for r in self.rels]

    def __contains__(self,x):
        r"""
        Returns true if `x` is contained in the module.

        INPUT:

        -   ``x``  -  An FP_Element. 

        OUTPUT: True if ``x`` is in the module.

        EXAMPLES::

            sage: M = FP_Module([0,2],[[Sq(3),Sq(1)]])
            sage: m = FP_Element([Sq(2),Sq(1)],M)
            sage: M.__contains__(m)
            True
        """
        return x.module == self


    def _repr_(self):
        """
        String representation of the module.

        EXAMPLES::

            sage: M = FP_Module([0,2,4],[[Sq(4),Sq(2),0]]); M
	    Finitely presented module on 3 generators and 1 relations over sub-Hopf
	    algebra of mod 2 Steenrod algebra, milnor basis, profile function [3, 2, 1]

	    sage: N = FP_Module([0,1],[[Sq(2),Sq(1)],[Sq(2)*Sq(1),Sq(2)]]); N
	    Finitely presented module on 2 generators and 2 relations over sub-Hopf
	    algebra of mod 2 Steenrod algebra, milnor basis, profile function [2, 1]


        """
        return "Finitely presented module on %s generators and %s relations over %s"\
                           %(len(self.degs),len(self.rels),self.algebra)

    def __call__(self,x):
        """
        Forms the element with ith coefficient x[i].
	This results in The identity operation if x is already in the module.

        INPUT:

        -   ``x``  - A list of coefficient.

        OUTPUT: An FP_Element with coefficients from x.

	EXAMPLES::

	    sage: M = FP_Module([0,2,4],[[Sq(4),Sq(2),0]]); M([Sq(2),0,0])
	    [Sq(2), 0, 0]

        """
        if x == 0:
            return FP_Element([ 0 for i in self.degs],self)
	elif type(x) == type([0]):
            return FP_Element(x,self)
	elif x.module == self: 
	    return x
	else:
	    raise ValueError,"Element not in module"


    def _pres_(self,n,profile=None):            
        """
        Returns a vector space, a quotient map, and elements.

        INPUT:
 
        -    ``n`` -  The degree in which all computations are made.

        OUTPUT:

        -  ``quo``  - A vector space for the degree `n` part of Module.

        -  ``q``  - The quotient map from the vector space for the free module on
           the generators to quo.

        -  ``sec``  - Elements of the domain of `q` which project to the std basis for
           quo.

        -  `` bas_gen``  - A list of pairs (gen_number, algebra element) 
           corresponding to the std basis for the free module.

        EXAMPLES::
       
            sage: quo,q,sec,bas = M._pres_(2)
	    sage: dim(quo)
	    1
	    sage: q
	    Free module morphism defined by the matrix
	    [1]
	    Domain: Vector space of dimension 1 over Finite Field of size 2
	    Codomain: Vector space quotient V/W of dimension 1 over Finite Field of ...
	    sage: sec
	    Free module morphism defined by the matrix
	    [1]
	    Domain: Vector space quotient V/W of dimension 1 over Finite Field of ...
	    Codomain: Vector space of dimension 1 over Finite Field of size 2


        """
	if profile == None:
	    profile = self.profile()
	alg = SteenrodAlgebra(p=self.char,profile=profile)  
        bas_gen = reduce(lambda x,y : x+y,\
                  [[(i,bb) for bb in alg.basis(n-self.degs[i])]\
                           for i in range(len(self.degs))],[])
        bas_vec = VectorSpace(GF(self.char),len(bas_gen))
        bas_dict = dict(zip(bas_gen,bas_vec.basis()))
        rel_vec = bas_vec.subspace([0])
        for i in range(len(self.rels)):
            if self.reldegs[i] <= n:
                for co in alg.basis(n-self.reldegs[i]):
                    r = zip(range(len(self.degs)),[co*c for c in self.rels[i]])
                    r = filter(lambda x : not x[1].is_zero(),r) # remove trivial
                    if len(r) != 0:
                        r = reduce(lambda x,y : x+y,
                            [map(lambda xx: (pr[0],alg._milnor_on_basis(xx[0]),xx[1]),\
                                 [z for z in pr[1]]) for pr in r])
                        rel_vec += bas_vec.subspace(\
                            [reduce(lambda x,y: x+y,\
                            map(lambda x: x[2]*bas_dict[(x[0],x[1])],r))])
        quo = bas_vec/rel_vec
        if quo.dimension() == 0:  
            sec = Hom(quo,bas_vec)(0)
            q = Hom(bas_vec,quo)([quo(0) for xx in bas_vec.basis()])
        else:
            sec = Hom(quo,bas_vec)([quo.lift(xx) for xx in quo.basis()])
            q = Hom(bas_vec,quo)([quo(xx) for xx in bas_vec.basis()])
        return quo, q, sec, bas_gen
            
    def _lc_(self,co,bas):
        """
	Creates the FP_Element corresponding to the lists ``co`` of coefficients
	and ``bas`` of basis elements. This function is intended for internal use only.

        INPUT:
        
        -    ``co``   -  A list of (either GF(p) elements or algebra elements) 
             coefficients.

        -    ``bas``   -  A list of tuples (gen_number, algebra elt) 
             corresponding to the std basis for the free module on self.degs

       OUTPUT: The linear combination given by the sum of co[i]*basi][1]*gen(bas[i][0])

       NOTE: The list of coefficients can lie in GF(p) or the algebra. 
             This does not normalize, the sum is taken in the free module.
 
        EXAMPLES::

            sage: M = FP_Module([2,3],[[Sq(2),Sq(1)],[0,Sq(2)]])
	    sage: bas = [(0,1)]; co = [Sq(1)]
	    sage: x = M._lc_(co,bas); x
	    [Sq(1), 0]
            sage: bas2 = [(1,1)]
	    sage: y = M._lc_(co,bas2);y
	    [0,Sq(1)]

        """
        if len(co) != len(bas):
            raise ValueError,\
            "Number of coefficients (%s) must be the same as number of basis elements (%s) " \
	        % (len(co),len(bas))
        return reduce(lambda x,y : x+y, \
              [self.gen(bas[i][0])*(co[i]*bas[i][1]) for i in range(len(co))],
	      self(0))

    def basis(self,n,profile=None):        
	"""
	Returns elements of the free module mapping to self. These elements 
        form a basis for the degree n piece of the module.

	INPUT:
		
        -  ``n``   -   The degree in which the basis will be taken.

        OUTPUT: A list of elements forming a basis for the degree n part of the 
                module.
 
        EXAMPLES::
 
            sage: M = FP_Module([2,3],[[Sq(2),Sq(1)],[0,Sq(2)]])
	    sage: M.basis(0)
	    []
	    sage: M.basis(3)
	    [[Sq(1),0],[0,1]]
	    sage: for i in range(10):
	        print "Basis for M in dimension ", i, " : ", M.basis(i)
		....:
		Basis for M in dimension  0  :  []
		Basis for M in dimension  1  :  []
		Basis for M in dimension  2  :  [[1, 0]]
		Basis for M in dimension  3  :  [[Sq(1), 0], [0, 1]]
		Basis for M in dimension  4  :  [[Sq(2), 0]]
		Basis for M in dimension  5  :  [[Sq(0,1), 0]]
		Basis for M in dimension  6  :  [[Sq(1,1), 0]]
		Basis for M in dimension  7  :  []
		Basis for M in dimension  8  :  []
		Basis for M in dimension  9  :  []

	"""
        if profile == None:
	    profile = self.profile()
	quo,q,s,bas = self._pres_(n,profile=profile)
	return [self._lc_(s(v),bas) for v in quo.basis()]
	
    __getitem__ = basis

    def gens(self):
	"""
	The list of generators of the module.

	EXAMPLES::

	    sage: X = FP_Module([0,2,3]);X.gens()
	    [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
	    sage: N = FP_Module([0,1],[[Sq(2),Sq(1)]]);N.gens()
	    [[1, 0], [0, 1]]

	"""
	return [FP_Element(_del_(i,len(self.degs)),self) \
           for i in range(len(self.degs))]
 
    def gen(self,i=0):
	"""
	The `i^{th}` generator of the module as an FP_Element.
 
        EXAMPLES::

	    sage: X = FP_Module([0,2,3]);X.gen(0)
	    [1, 0, 0]
	    sage: N = FP_Module([0,1],[[Sq(2),Sq(1)]]);N.gen(1)
	    [0, 1]

	"""
	if i < 0 or i >= len(self.degs):
            raise ValueError,\
            "Module has generators numbered 0 to %s; generator %s does not exist" % (len(self.degs)-1,i)
	return FP_Element(_del_(i,len(self.degs)),self)
		

    def identity(self):
        """
        Returns the identity homomorphism of the module.

        OUTPUT: The identity homomorphism of the module as an FP_Hom.

        EXAMPLES::

            sage: N = FP_Module([0,1],[[Sq(2),Sq(1)]]);N.identity()
	    Homomorphism from
	     Finitely presented module on 2 generators and 1 relations over sub-Hopf algebra of mod 2
	    Steenrod algebra, milnor basis, profile function [2, 1] to
	     Finitely presented module on 2 generators and 1 relations over sub-Hopf algebra of mod 2
	    Steenrod algebra, milnor basis, profile function [2, 1]

        """
        return FP_Hom(self,self,[_del_(i,len(self.degs))\
                         for i in range(len(self.degs))])

    def min_pres(self):
        """
	Returns the minimal presentation of the module, along with maps
	between min_pres and self.

        OUTPUT:

	- ``M`` - An isomorphic copy of self with possibly fewer relations and
	          generators.

        -  ``g`` - An isomorphism from self to `M`.

	-  ``h`` - An isomorphism from `M` to self.

	EXAMPLES::

	    sage: K = FP_Module([0,1],[[Sq(2),Sq(1)],[0,Sq(2)],[Sq(3),0]])
	    sage: KK, g, h = K.min_pres();KK.rels
	    [[Sq(2),Sq(1)],[0,Sq(2)]]
	"""
	M,e,i = self.identity().image()
	return M,e,i

    def min_profile(self):
        """
	Returns the profile of the smallest sub-Hopf algebra containing self.

	OUTPUT: The profile function of the sub-Hopf algebra with the smallest
	degree containing self.

	EXAMPLES::

	    sage: A3 = SteenrodAlgebra(p=2,profile=(4,3,2,1))
	    sage: Y = FP_Module([0],[[Sq(1)]],algebra=A3)
	    sage: Y.profile()
	    (4, 3, 2, 1)
	    sage: Y.min_profile()
	    (1,)
	"""
        if not self.rels:
            return self.algebra._profile
        else:
            profile = enveloping_profile_profiles(\
                     [enveloping_profile_elements(r,self.char) for r in self.rels],\
		      self.char)
            return profile



    def copy(self):
        """
        Returns a copy of the module, with 2 ``identity'' morphisms from
        1. the copy to the module
        2. the module to the copy.

        OUTPUT:
 
        -   ``C``  - A duplicate of the module.

        -   Two Finitely Presented Homomorphisms: the first is a map from `C` to self,
            and the second is the map from self to `C`.

        EXAMPLES::

            sage: M = FP_Module([0,4],[[Sq(1),0],[Sq(5),Sq(1)]])
	    sage: N,i,p = M.copy(); N,i,p
	    (Finitely presented module on 2 generators and 2 relations over sub-Hopf
	    algebra of mod 2 Steenrod algebra, milnor basis, profile function [3, 2, 1],
	    Homomorphism from
	    Finitely presented module on 2 generators and 2 relations over sub-Hopf
	    algebra of mod 2 Steenrod algebra, milnor basis, profile function [3, 2, 1] to
	    Finitely presented module on 2 generators and 2 relations over sub-Hopf
	    algebra of mod 2 Steenrod algebra, milnor basis, profile function [3, 2, 1]
	    , Homomorphism from
	    Finitely presented module on 2 generators and 2 relations over sub-Hopf
	    algebra of mod 2 Steenrod algebra, milnor basis, profile function [3, 2, 1]
	    to
	    Finitely presented module on 2 generators and 2 relations over sub-Hopf
	    algebra of mod 2 Steenrod algebra, milnor basis, profile function [3, 2, 1]
	    )

        """
        C = FP_Module(self.degs, self.rels, algebra=self.algebra)
        return C,\
           FP_Hom(C,self,[_del_(i,len(self.degs))\
                  for i in range(len(self.degs))]),\
           FP_Hom(self,C,[_del_(i,len(self.degs))\
                 for i in range(len(self.degs))])

    def suspension(self,t):
        """
        Suspends a module by degree t.

	INPUT:

	-   ``t``  - An integer by which the module is suspended.

	OUTPUT: 

	-   ``C``  ` A copy of the module `self` which is suspended by `t`.

        EXAMPLES::

	    sage: Y = FP_Module([0],[[Sq(1)]])
	    sage: X = Y.suspension(4)
	    sage: X.degs;X.rels
	    [4]
	    [[Sq(1)]]
	    sage: M = FP_Module([2,3],[[Sq(2),Sq(1)],[0,Sq(2)]])
	    sage: Q = M.suspension(1)
	    sage: Q.degs;Q.rels
	    [3, 4]
	    [[Sq(2), Sq(1)], [0, Sq(2)]]

	"""
	if t == 0:
	    return self
	else:
	    C = self.copy()[0]
	    C.degs = map(lambda x: x+t, C.degs)
	    C.reldegs = map(lambda x: x+t, C.reldegs)
	    return C


    def submodule(self,L):
        """
	The submodule of self spanned by elements of the list L.

	The map from the free module on the elements of L to
	the submodule, as well as the inclusion of the submodule are also returned.

	INPUT:

	-  ``L``  - A list of elements of `self`.

	OUTPUT:

	-  ``N``  - The FP_Module generated by `L`, a submodule of `self`.

	-  ``p``  - The map from the free module on the elements of L to `N`.

	-  ``i``  - The inclusion of `N` into `self`.

	EXAMPLES::

	    sage: N = FP_Module([0,1],[[Sq(2),Sq(1)]]);
	    sage: Y,g,h = N.submodule([N.gen(0)])
	    sage: Y.degs;Y.rels
	    [0]
	    [[Sq(3)]]
	    
	"""
        F = FP_Module([x.degree for x in L],algebra=self.algebra)
	pr = FP_Hom(F,self,L)
	N,p,i = pr.image()
	return N,p,i


    def resolution(self,k,verbose=false):
        """
	Returns a list of length `k`, consisting of chain maps. These 
	maps form a resolution of length `k` of `self`.
	"""
        C0 = FP_Module(self.degs, algebra=self.algebra)
	eps = FP_Hom(C0,self,self.gens())
	if verbose:
	      print "Step ",k
	if k <= 0:
	    return [eps]
	else:
	    K0,i0 = eps.kernel()
	    r = K0.resolution(k-1,verbose=verbose)
	    r[0] = i0*r[0]
	    return [eps] + r


    def resolution_kernels(self,k,kers=[],verbose=false):
        """
	Returns a list of length `k`, consisting of chain maps and 
	a list of pairs [K_n,i_n] corresponding to the kernels
	and inclusions of the resolution. These 
	maps form a resolution of length `k` of `self`.

	A list should never be passed for kers. This is only used
	for recursion.
	"""
        C0 = FP_Module(self.degs, algebra=self.algebra)
	eps = FP_Hom(C0,self,self.gens())
	if verbose:
	      print "Step ",k
	if k <= 0:
	    return [eps],kers
	else:
	    K0,i0 = eps.kernel()
	    kers.append([K0,i0])
	    r,k = K0.resolution_kernels(k-1,kers,verbose=verbose)
	    r[0] = i0*r[0]
	    return [eps] + r, kers

#--------------------------------------------------------------------------------
#----------------------Homomorphisms-between-FP_Modules--------------------------
#--------------------------------------------------------------------------------

class FP_Hom(Morphism):
    r"""
    A finitely presented Homomorphism between two Finitely Presented Modules.
    If degree is passed, dom is suspended by degree before mapping.
    The 0 hom can be created by passing `0' for values.
    
    """

    def __init__(self,domain,codomain,values, degree=0):
        if domain.algebra.prime() != codomain.algebra.prime():
            raise ValueError,\
               "Domain algebra defined at the prime %s but codomain algebra defined at prime %s"\
                   %(domain.algebra._prime, codomain.algebra._prime)
        if degree != 0:
	    domain = domain.suspension(degree)
	if values == 0:
            values = [FP_Element([codomain.algebra(0) for j in codomain.degs],\
	                    codomain) for i in domain.degs]
        if len(values) != len (domain.degs):
            raise ValueError,\
                "Domain has %s generators, but %s values were given\,"\
                     %(len(domain.degs), len(values))
        for i in range(len(values)):
            if values[i] == 0: 
                values[i] = FP_Element([codomain.algebra(0) for j in\
                           codomain.degs],codomain) 
            else:                                     # if its a list of coeffs, make it
                values[i]= FP_Element(values[i],codomain) # an FP_Element.Otherwise ought to
                                                      # already be one.  
		if values[i].degree != None and domain.degs[i] != values[i].degree:
		    raise ValueError, \
		          "Degree of generator %d is %d but degree of %dth value is %d" \
                         %(i,domain.degs[i],i,values[i].degree)
        self.values = [x.nf() for x in values]
	initialval = FP_Element([0]*len(domain.degs),domain)
        self.domain = domain 
        self.codomain = codomain
        self.degree = degree
        if self.domain.rels:  
            for x in self.domain.rels:
                ximage = reduce(lambda xx,y: xx+y, [values[i]*x[i] for i in\
                      range(len(x))])
                if not ximage.is_zero():
                    raise ValueError, "Relation %s is not sent to 0" % x
        prof = enveloping_profile_profiles([domain.profile(),codomain.profile(),\
	                   enveloping_profile_elements(reduce(lambda x,y: x+y,\
                           [x.coeffs for x in values],initialval.coeffs),\
			    domain.char)],domain.char)
        self.algebra = SteenrodAlgebra(p = domain.algebra.prime(),\
                      profile = prof)

    def profile(self):
        return self.algebra._profile

    def alg(self):
        return self.algebra

    def _repr_(self):
        return "Homomorphism from\n %s to\n %s\n" % (self.domain, self.codomain)

    def __add__(self,g):
        """
        Sum the homomorphisms, so (f+g)(x) == f(x)+g(x)
        """
        if self.domain != g.domain:
            raise ValueError,\
            "Morphisms do not have the same domain."
        if self.codomain != g.codomain:
            raise ValueError,\
            "Morphisms do not have the same codomain."
        if self.degree != g.degree:
            raise ValueError,\
            "Morphisms do not have the same degree."
        return FP_Hom(self.domain,self.codomain,\
                   [self(x)+g(x) for x in self.domain.gens()], self.degree)

    def __neg__(self):
        return FP_Hom(self.domain,self.codomain,\
               [-self.values[i] for i in range(len(self.values))],self.degree)

    def __sub__(self,g):
        return self.__add__(g.__neg__())

    def __mul__(self,g):
        """
        Composition of morphisms. 
        """
        if self.domain != g.codomain:
            raise ValueError,\
                "Morphisms not composable."
        return FP_Hom(g.domain,self.codomain,\
                   [self(g(x)) for x in g.domain.gens()],self.degree+g.degree) 

    def is_zero(self):
        return reduce(lambda x,y: x and y, [x.is_zero() for x in self.values],True)

    def __cmp__(self,g): 
        if self.domain != g.domain:
            raise ValueError, "Morphisms not comparable, different domains."
        if (self-g).is_zero():
            return 0
        else:
            return 1  


    def __call__(self,x):
        """
        Evaluate the morphism at an FP_Element of domain.

	INPUT:

	-  ``x``  - An element of the domain of self.

	OUTPUT: The FP_Hom evaluated at `x`.

	EXAMPLES::


        """
        if x not in self.domain:
            raise ValueError,\
                  "Cannot evaluate morphism on element not in domain"
        value = reduce(lambda x,y: x+y,\
                [self.values[i]*x.coeffs[i] for i in range(len(self.domain.degs))],
		self.codomain(0)) 
	return value.nf()

    def _full_pres_(self,n,profile=None):      
        """
        Computes the linear transformation from domain in degree n
	to codomain in degree n+degree(self). 9 items returned: the
        linear transformation, self.dom._pres_(n), & self.codomain._pres_(n).
	See the documentation for _pres_ in class FP_Module for further explanation.

	INPUT:

	-  ``n``  - The degree in which all computations are made.

	-  ``profile``  - A profile function corresponding to the sub-Hopf algebra
	     of the Steenrod Algebra for which this computation will be computed over.
	     The default, `profile=None`, uses the profile of self.

	OUTPUT: 

	-  The linear transformation corresponding to the degree `n` piece of this 
	   mapping (see the documentation for _pres_ below).

	-  ``dquo``  - The vector space corresponding to self.domain in degree `n`.

        -  ``dq``  - The quotient map from the vector space for the free module on
           the generators to `dquo`.

        -  ``dsec``  - Elements of the domain of `dq` which project to the standard
	   basis for `dquo`.

        -  ``dbas_gen``  - A list of pairs (gen_number, algebra element) 
           corresponding to the standard basis for the free module.

	-  ``cquo``  - The vector space corresponding to self.codomain in degree `n` +
	   self.degree.
	
	-  ``cq``  - The quotient map from the vector space for the free module on
	   the generators to `cquo`.

	-  ``csec``  - Elements of the domain of `cq` which project to the standard basis
	   for `cquo`.
	  
        -  ``cbas_gen``  - A list of pairs (gen_number, algebra element) corresponding
	   to the standard basis for the free module.

	EXAMPLES::

	    sage:
        """
	if profile == None:
	    profile = self.profile()
        dquo,dq,dsec,dbas_gen = self.domain._pres_(n,profile=profile)
        cquo,cq,csec,cbas_gen = self.codomain._pres_(n,profile=profile)
        return Hom(dquo,cquo)(\
                    [cq(self(self.domain._lc_(dsec(x),dbas_gen)).free_vec(profile=profile))\
                    for x in dquo.basis()]),\
                    dquo,dq,dsec,dbas_gen,\
                    cquo,cq,csec,cbas_gen

    def _pres_(self,n,profile=None):       
        """
        Computes the linear transformation from domain in degree n to 
        codomain in degree n + degree(self). Intended for internal use only.

	INPUT:

	-    ``n``  - The degree in which all computations are made.

	-    ``profile``  - A profile function corresponding to the sub-Hopf algebra
	     of the Steenrod Algebra for which this computation will be computed over.

	OUTPUT: The linear transformation from the degree `n` part of self.domain
	        to the degree `n` + self.degree part of self.codomain. The basis for
		the vector space corresponding to the deg `n` piece of self.domain
		is mapped to the basis for the deg `n` + self.degree piece of self.codomain.

        EXAMPLES::

	    sage:
        """
	return self._full_pres_(n,profile)[0]

    def min_profile(self):
        """
	Returns the profile function for the smallest sub-Hopf algebra over which self
	is defined.

	This function is useful when reducing to the smallest profile function (and sub-Hopf algebra)
	an FP_Module can be defined over.

	OUTPUT:

	-  ``profile``  - The profile function corresponding to the smallest sub-Hopf algebra
	                  containing self.
	"""
	initialval = FP_Element([0]*len(self.domain.degs),self.domain)
        profile = enveloping_profile_profiles([self.domain.profile(),self.codomain.profile(),\
	                   enveloping_profile_elements(reduce(lambda x,y: x+y,\
                           [x.coeffs for x in self.values],initialval.coeffs),\
			   self.domain.char)], self.domain.char)
        return profile 

    def suspension(self,t):
        """
	Suspends an FP_Hom, which requires suspending the domain and codomain as well.

	INPUT:

	-  ``t``  - The degree by which the homomorphism is suspended.

	OUTPUT: The FP_Hom suspended by degree `t`.

	EXAMPLES::

	    sage:
	"""
	if t == 0:
	    return self
	else:
	    return FP_Hom(self.domain.suspension(t),\
	               self.codomain.suspension(t),\
	               self.values)

    def cokernel(self,min=False):
        """
	Computes the cokernel of an FP Hom.


        Cheap way of computing cokernel. Cokernel is on same degs as codomain,
        with rels = codomain.rels + self.values. Returns cokernel and the 
        projection map to it. 

	OUTPUT:

	-  ``coker``  - The FP_Module corresponding to the cokernel of self.

	-  The FP_Hom corresponding to the natural projection from self.codomain
	   to `coker`.

        EXAMPLES::


        """
        coker = FP_Module(self.codomain.degs,\
                self.codomain.rels + [x.coeffs for x in self.values],\
                algebra = self.alg()) 
        vals = [_del_(i,len(self.codomain.degs)) for i in \
                range(len(self.codomain.degs))]
	if min == False:
            return coker,FP_Hom(self.codomain,coker,vals)
	else:
	    MM,e,m = coker.min_pres()
	    p = FP_Hom(self.codomain,coker,vals)
	    return MM, e*p



    def kernel(self):
        """
        Computes the kernel of an FP_Hom, as an FP_Module.
        The kernel is non-zero in degrees starting from connectivity of domain
        through the top degree of the algebra the function is defined over plus
        the top degree of the domain.
	
	OUTPUT:

	-  ``ker``  - An FP_Module corresponding to the kernel of `self`.

	-  ``incl``  - An FP_Hom corresponding to the natural inclusion of `ker` 
	               into the domain.

        EXAMPLES::
        """
        n = self.domain.conn()
	if n == +Infinity:
	    ker = FP_Module([])
	    return ker, FP_Hom(ker,self.domain,values=0)
        notdone = True
        limit = max_deg(self.algebra) + max(self.domain.degs)
        while notdone and n <= limit:
            fn = self._pres_(n)          
            notdone = (fn.kernel().dimension() == 0)
            if notdone:  # so the kernel is 0 in this degree n. Move on to the next.
                n += 1
        if notdone: # If the kernel is 0 in all degrees.
            ker = FP_Module([],[],algebra=self.alg()) 
            return ker, FP_Hom(ker,self.domain,values=0) 
        else:
            ker = FP_Module(fn.kernel().dimension()*[n],[],algebra=self.alg())
            quo,q,sec,bas_gen = self.domain._pres_(n,profile=self.profile())
            incl = FP_Hom(ker,self.domain,\
                   [self.domain._lc_(sec(v),bas_gen) for v in fn.kernel().basis()])
	    n += 1
            while n <= limit:
                incln,Kn,p,sec,bas,Mn,q,s,Mbas_gen = incl._full_pres_(n)
                fn = self._pres_(n)
                if fn.kernel().dimension() != 0:  # so we found something new
                    Kfn = VectorSpace(GF(self.domain.algebra._prime),\
		                   fn.kernel().dimension())
                    kin = Hom(Kfn,Mn)(fn.kernel().basis())
                    jn = Hom(Kn,Kfn)(kin.matrix().solve_left(incln.matrix())) 
                    imjn = jn.image()
                    num_new_gens = 0
                    for v in Kfn.basis():  
                        if not v in imjn:  
                            num_new_gens += 1
                            imjn += Kfn.subspace([v])
                            incl.values.append(self.domain._lc_(s(kin(v)),Mbas_gen))
                    ker.degs += num_new_gens*[n]
                    pad = num_new_gens*[0]
                    ker.rels = [x + copy(pad) for x in ker.rels] 
                ker.rels += [ker._lc_(sec(v),bas).coeffs for v in incln.kernel().basis()]
                ker.reldegs += incln.kernel().dimension()*[n]
                n += 1
	    # All generators have been found.  Now see if we need any more relations.
	    while n <= max_deg(self.algebra) + max(ker.degs):
                incln,Kn,p,sec,bas,Mn,q,s,Mbas_gen = incl._full_pres_(n,profile=self.profile()) 
                ker.rels += [ker._lc_(sec(v),bas).coeffs for v in incln.kernel().basis()]
                ker.reldegs += incln.kernel().dimension()*[n]
                n += 1
            ker.algebra = SteenrodAlgebra(p=ker.char, profile = ker.min_profile())
	    incl.algebra = SteenrodAlgebra(p=ker.char, profile = incl.min_profile())
            return ker, incl            


    def kernel_gens(self):
        """
        Computes the generators of the kernel of an FP_Hom, and returns a free module
	and an epi from it to the kernel of self as a map from the free module to self.domain.
	
        The kernel is non-zero in degrees starting from connectivity of domain
        through the top degree of the algebra the function is defined over plus
        the top degree of the domain.
	
	OUTPUT:

	-  ``ker``  - A free FP_Module corresponding to the generators of the kernel of `self`.

	-  ``incl``  - An FP_Hom corresponding to the natural inclusion of `ker` 
	               into the domain.

        EXAMPLES::
        """
        n = self.domain.conn()
        notdone = True
        limit = max_deg(self.algebra) + max(self.domain.degs)
        while notdone and n <= limit:
            fn = self._pres_(n)          
            notdone = (fn.kernel().dimension() == 0)
            if notdone:  # so the kernel is 0 in this degree n. Move on to the next.
                n += 1
        if notdone: # If the kernel is 0 in all degrees.
            ker = FP_Module([],[],algebra=self.alg()) 
            return ker, FP_Hom(ker,self.domain,values=0) 
        else:
            ker = FP_Module(fn.kernel().dimension()*[n],[],algebra=self.alg())
            quo,q,sec,bas_gen = self.domain._pres_(n,profile=self.profile())
            incl = FP_Hom(ker,self.domain,\
                   [self.domain._lc_(sec(v),bas_gen) for v in fn.kernel().basis()])
	    n += 1
            while n <= limit:
                incln,Kn,p,sec,bas,Mn,q,s,Mbas_gen = incl._full_pres_(n,profile=self.profile()) 
                fn = self._pres_(n)
                if fn.kernel().dimension() != 0:  # so we found something new
                    Kfn = VectorSpace(GF(self.domain.algebra._prime),\
		                   fn.kernel().dimension())
                    kin = Hom(Kfn,Mn)(fn.kernel().basis())
                    jn = Hom(Kn,Kfn)(kin.matrix().solve_left(incln.matrix())) 
                    imjn = jn.image()
                    num_new_gens = 0
                    for v in Kfn.basis():  
                        if not v in imjn:  
                            num_new_gens += 1
                            imjn += Kfn.subspace([v])
                            incl.values.append(self.domain._lc_(s(kin(v)),Mbas_gen))
                    ker.degs += num_new_gens*[n]
                n += 1
            ker.algebra = SteenrodAlgebra(p=ker.char, profile = ker.min_profile())
	    incl.algebra = SteenrodAlgebra(p=ker.char, profile = incl.min_profile())
            return ker, incl            

                
    def image(self):
        """
        Computes the Image of an FP_Hom, as an FP_Module. Returns the factorization of
        self into epi, Image, mono. 

	Assumes generators of FP_Modules are in order of increasing degree.

	OUTPUT:

	-  ``F``  - The FP_Module corresponding to the image of self.

	-  ``mono``  - The FP_Hom corresponding to the natural inclusion of `F` into
	            the codomain of self.

        -  ``epi``  - The FP_Hom corresponding to the natural projection of the
	            domain of self onto `F`.

        EXAMPLES::


	
        """
	F = FP_Module([],algebra=self.alg())
	mono = FP_Hom(F,self.codomain,[])
	epivals = []
        # Loop to find a minimal set of generators for the image
	for i in range(len(self.domain.degs)):
	    n = self.domain.degs[i]
            pn,Fquo,Fq,Fsec,Fbas,Cquo,Cq,Csec,Cbas = mono._full_pres_(n,profile=self.profile())
	    v = self.values[i].vec(profile=self.profile())[0]
	    if Cquo(v) in pn.image():
	        y = pn.matrix().solve_left(Cquo(v))
		# Now convert the vector y into an FP_Element using lc
		epivals.append(F._lc_(Fsec(y),Fbas))
	    else:
	        F.degs.append(n)
		epivals.append(F.gen(len(F.degs)-1))
		mono.values.append(self.values[i])
	# Now compute the relations
	K,i = mono.kernel()
	F.reldegs = K.degs
	F.rels = [x.coeffs for x in i.values]
	l = len(F.degs)
	epivals = [ F(x.coeffs + [0]*(l-len(x.coeffs))) for x in epivals] 
	epi = FP_Hom(self.domain,F,epivals)
	# Now reduce profile functions
	F.algebra = SteenrodAlgebra(p=F.char, profile = F.min_profile())
	mono.algebra = SteenrodAlgebra(p=F.char,profile =  mono.min_profile())
	epi.algebra = SteenrodAlgebra(p=F.char, profile = epi.min_profile())
	return F,epi,mono

    def solve(self,x):
         """
	 Computes the element in self.domain, such that self(y) = x

	 INPUT:

	 -  ``x``  - The element to be solved for.

	 OUTPUT:

	 -  A boolean corresponding to whether or not the equation can be solved.

	 -  The element which maps to x under self.

	 EXAMPLES::
	 """
	 pn,dquo,dq,dsec,dbas,cquo,cq,csec,cbas =\
              	 self._full_pres_(x.degree,profile=self.profile())
	 v = x.vec()[0]
	 if x not in self.codomain:
	     raise TypeError, "Element not in codomain."
	 if v not in pn.image(): 
	     return False,self.domain(0)
	 else:
	     w = pn.matrix().solve_left(v)
	     return True, self.domain._lc_(dsec(w),dbas)

	     
        
#--------------------------------------------------------------------------------
#-----------------------Elements-of-FP_Modules-----------------------------------
#--------------------------------------------------------------------------------

class FP_Element(ModuleElement):
    r"""
    Yields an element of an FP_Module, given by defining the coefficients on each
    generator of the module.

    *** Do we really need FP_Elements to have profiles?
    ***
    """

    def __init__(self, coeffs, module):
        """
        Defines an element of a Finitely Presented module.

	INPUT:

	-  ``coeffs``  - A list of Steenrod Algebra elements of GF(p)
	                 coefficients.

	-  ``module``  - An FP_Module corresponding to the parent module.

	OUTPUT: The FP_Element defined by the sum over `i` of coeffs[i]*module.gen(i).

        Users can also define elements using the call() method of FP_Modules. See
	that function for documentation.

	EXAMPLES::

	sage: m = FP_Element([0,Sq(3),Sq(1)],FP_Module([2,3,5]));m
	[0, Sq(3), Sq(1)]

	"""
        self.module = module
        if isinstance(coeffs,FP_Element): 
            self.coeffs = coeffs.coeffs
        else:
            self.coeffs = [SteenrodAlgebra(module.algebra._prime)(x) for x in coeffs]
        self._parent = module
        self.degree = _deg_(self.module.degs,self.coeffs) # degree will find errors passed
        profile_coeffs = [profile_ele(j,self.module.char) for j in self.coeffs]
        self.profile = enveloping_profile_profiles(\
                 [list(module.algebra._profile)]+profile_coeffs,self.module.char)

    def __iadd__(self,y):
        if self.module != y.module:
            raise TypeError, "Can't add element in different modules"
        if self.degree == None: # if self = 0, degree is None
            return y
        if y.degree == None:   # if y = 0, degree is None
            return 
        if self.degree != y.degree:
            raise ValueError, "Can't add element of degree %s and %s"\
                  %(self.degree,y.degree)
        return FP_Element([self.coeffs[i]+y.coeffs[i] for i in range(len(self.coeffs))],self.module)

    def __add__(self,y):
        if self.module != y.module:
            raise TypeError, "Can't add element in different modules"
        if self.degree == None: # if self = 0, degree is None
            return FP_Element(y.coeffs,y.module)
        if y.degree == None:   # if y = 0, degree is None 
            return FP_Element(self.coeffs, self.module)
        if self.degree != y.degree:
            raise ValueError, "Can't add element of degree %s and %s"\
                  %(self.degree,y.degree)
        return FP_Element([self.coeffs[i]+y.coeffs[i] for i in range(len(self.coeffs))],self.module)

    def __neg__(self):
        """
        Returns the negative of the element.
        """
        return FP_Element([-self.coeffs[i] for i in range(len(self.coeffs))],self.module)

    def __sub__(self,y):
        """
        Returns the difference of the two elements.
        """
        return self.__add__(y.__neg__())

    def __cmp__(self,y):
        """
        Compares two FP_Elements for equality. Cannot compare elements in 
        different degrees or different modules.
        """
        if self.module != y.module:
            raise TypeError, "Cannot compare elements in different modules."
        if self.degree != y.degree and self.degree != None and y.degree != None:
            raise ValueError, \
            "Cannot compare elements of different degrees %s and %s"\
            %(self.degree, y.degree)
        if (self.__add__(y.__neg__())).__nonzero__():
            return 1
        else:
            return 0

    def __nonzero__(self):
	if self.degree == None:
            return False 
        v,q,sec,bas = self.vec()
        return v != 0 

    def _repr_(self):
        return '%s' % self.coeffs ## TO DO: Add parents when coeffs are sums:
                                  ## Sq(3)*M.0 + Sq(1)*M.2 is fine, but we'll 
                                  ## need (Sq(3) + Sq(0,1))*M.0. Still a problem?

    def __rlmul__(self,x):
        """ 
        This is the action which is called when x*Sq(2) is evaluated. Really a left 
        action but must be written on the right.
        """
        return FP_Element(\
          [x*self.coeffs[i] for i in range(len(self.coeffs))],self.module)

    def __lmul__(self,x):
        """ 
        This is the action which is called when x*Sq(2) is evaluated. Really a left 
        action but must be written on the right.
        """
        return FP_Element(\
          [x*self.coeffs[i] for i in range(len(self.coeffs))],self.module)

    def __mul__(self,x):
        """ 
        This is the action which is called when x*Sq(2) is evaluated. Really a left 
        action but must be written on the right.
        """
        return FP_Element(\
          [x*self.coeffs[i] for i in range(len(self.coeffs))],self.module)

    def _l_action_(self,x):
        """
        ## FIX
        Multiplication of an FP_Element by a Steenrod Algebra element.
        This is written as a right multiplication, but its really a left 
        multiplication.
        """
        return FP_Element(
               [x*self.coeffs[i] for i in range(len(self.coeffs))],self.module)
        
    def free_vec(self,profile=None):          
        """
    	Returns the vector in the free vector space corresponding to self.coeffs.
        If the coeffs are all 0, then we return the scalar 0, since it will be
        coerced up to the 0 vector in any vector space.

        INPUT:

	-  ``profile``  - The profile function of a larger algebra than
	   the one currently defined.

	OUTPUT:  The vector in the vector space for self.parent corresponding
	         to self.
        """
	if profile == None:
	   profile = self.profile
        n = self.degree
        if n == None:
             return 0
	alg = SteenrodAlgebra(p=self.module.char,profile=profile)
        bas_gen = reduce(lambda x,y : x+y,\
          [[(i,bb) for bb in alg.basis(n-self.module.degs[i])] \
                   for i in range(len(self.module.degs))])
        bas_vec = VectorSpace(GF(self.module.char),len(bas_gen))
        bas_dict = dict(zip(bas_gen,bas_vec.basis()))
        r = zip(range(len(self.coeffs)),self.coeffs)  #[...(gen,op)...]
        r = filter(lambda x: not x[1].is_zero(),r)   #remove trivial ops
        r = reduce(lambda x,y: x+y,\
	       [map(lambda xx: (pr[0],\
               alg._milnor_on_basis(xx[0]), xx[1]),\
               [z for z in pr[1]]) for pr in r])  
                  # now, r = [....(gen,basis_op,coeff)...]
        return reduce(lambda x,y: x+y, map(lambda x : x[2]*bas_dict[(x[0],x[1])],r))            
    def vec(self,profile=None):    
        """
        Returns the vector form of self, as well as the linear transformation
        `q : F_n \rightarrow M_n` and `s:M_n \rightarrow F_n`, where `M_n` 
        and `F_n` are the degree `n` parts of the module and free vector
        space, respectively. 

        OUTPUT:

	-    ``x``    - The unique vector form of self in `M_n`.

        -    ``q``    - The linear transformation from the free vector 
                        space to the module.

        -    ``s``    - The linear transformation from the module to the 
                        free vector space.

        -    ``bas``  - A list of pairs (gen_number,algebra element) 
                        corresponding to self in the std basis of the free module.

        """
	if profile == None:
	   profile = self.profile
        n = self.degree
        if n == None: 
            return 0,0,0,0  
        quo, q, s, bas = self.module._pres_(n,profile=profile)
        return q(self.free_vec(profile=profile)),q,s,bas


    def nf(self,profile=None):       
        """
        Computes the normal form of self.
        """
	if profile == None:
	   profile = self.profile
        if self.degree == None:
            return self
        v,q,sec,bas = self.vec(profile=profile)
        return self.module._lc_(sec(v),bas)

# The End
