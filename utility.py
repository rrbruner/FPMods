#-------------------------------------------------------------------------------
#--------------------------Utility-functions------------------------------------
#-------------------------------------------------------------------------------

from sage.rings.infinity import PlusInfinity

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
    [5, 4, 3, 4]
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
    if alg._truncation_type == PlusInfinity():
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
    Traceback (most recent call last):
    ...
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



