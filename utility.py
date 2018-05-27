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

    sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.utility import *
    sage: maxim([[1,2,3,4],[5,4]])
    [5, 4, 3, 4]
    sage: maxim([[1,2,3,4],[1,1,1,5],[9]])
    [9, 2, 3, 5]

    """
    max_length = max(len(l) for l in L)
    # Pad the elements of L with 0's so that they all have the same lengths
    L_padded = [l + (max_length - len(l))*[0] for l in L]
    # Compute and return the component-wise maximum of the entries
    return [max(component) for component in zip(*L_padded)]

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

    sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.utility import _deg_
    sage: _deg_((0,2,4),(Sq(4),Sq(2),Sq(0)))
    4
    sage: _deg_((3,3),(Sq(2)*Sq(1),Sq(1)*Sq(2)))
    6

    TESTS::

    sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.utility import _deg_
    sage: _deg_([2,1], [Sq(4),Sq(2),Sq(0)])
    Traceback (most recent call last):
    ...
    ValueError: Wrong number of coefficients given: 3.  Expected 2.
    sage: _deg_([2,1,2], [Sq(2),Sq(3),Sq(0)])
    Traceback (most recent call last):
    ...
    ValueError: Inhomogeneous arguments given.  The first mismatch occured here:
    Index #1: The operation Sq(3) applied to an element in degree 1 will have degree 4,
    Index #2: The operation 1 applied to an element in degree 2 will have degree 2.
    """
    if len(degs) != len(co):
        raise ValueError,\
        "Wrong number of coefficients given: %d.  Expected %d." % (len(co), len(degs))

    # Pair the operations and the degrees.
    elements = zip(co, degs)
    degrees = [d + c.degree() for (c, d) in elements if c != 0]

    # Check for emptiness first.
    if len(degrees) == 0:
        return None

    for i in range(1, len(degrees)):
        if degrees[i-1] == degrees[i]:
            continue
        raise ValueError,\
        ("Inhomogeneous arguments given.  The first mismatch occured here:\n"
         "Index #%d: The operation %s applied to an element in degree %d will have degree %d,\n"
         "Index #%d: The operation %s applied to an element in degree %d will have degree %d." % (
             i-1, str(elements[i-1][0]), elements[i-1][1], degrees[i-1],
             i, str(elements[i][0]), elements[i][1], degrees[i]))

    # All values in the list are equal.
    return degrees[0]

def max_deg(alg):
    """
    Computes the top nonzero degree of a sub-algebra of the Steenrod Algebra.

    INPUT:

    -  ``alg``  - A sub-algebra of the Steenrod Algebra.

    OUTPUT:

    -  ``topdeg`` - The top nonzero degree of `alg`.

    EXAMPLES::

    sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.utility import *
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

    sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.utility import *
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

    sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.utility import _del_
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

    sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.utility import *
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

