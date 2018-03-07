
#  http://doc.sagemath.org/html/en/developer/coding_basics.html#files-and-directory-structure

import sage.modules.fpmods.utility as Utility
import sage.modules.fpmods.profile as Profile
import sage.modules.fpmods.resolutions as Resolutions

from sage.algebras.steenrod.steenrod_algebra import SteenrodAlgebra
from sage.modules.free_module import VectorSpace
from sage.rings.finite_rings.finite_field_constructor import FiniteField

# Import the free function for creating Homsets
from sage.categories.homset import Hom


from sage.rings.infinity import PlusInfinity

from copy import copy

#--------------------------------------------------------------------------------
#-----------------------Elements-of-FP_Modules-----------------------------------
#--------------------------------------------------------------------------------

from sage.structure.element import ModuleElement
class FP_Element(ModuleElement):

    def __init__(self, module, coefficients):
        """

        Note: Never use this constructor explicitly, but rather the parent's
              call method, or this class' __call__ method.  The reason for this
              is that the dynamic type of the element class changes as a
              consequence of the category system.

        EXAMPLES::

        sage: from sage.modules.fpmods.fpmods import FP_Module, FP_Element
        sage: M = FP_Module((2,3,5))
        sage: generators = (0,Sq(3),Sq(1))
        sage: m = M(generators);m
        <0, Sq(3), Sq(1)>
        sage: n = FP_Element(M, generators);n
        <0, Sq(3), Sq(1)>
        sage: type(m)
        <class 'sage.modules.fpmods.fpmods.FP_Module_with_category.element_class'>
        sage: type(n)
        <class 'sage.modules.fpmods.fpmod_element.FP_Element'>

        EXAMPLES::

        sage: from sage.modules.fpmods.fpmods import FP_Module, FP_Element
        sage: M = FP_Module((2,3,5));M
        Finitely presented module on 3 generators and 0 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function []
        sage: m = FP_Element(M, (0,Sq(3),Sq(1)));m
        <0, Sq(3), Sq(1)>
        sage: n = FP_Element(M, (Sq(4),Sq(1)*Sq(2),0));n
        <Sq(4), Sq(3), 0>
        sage: m+n
        <Sq(4), 0, Sq(1)>
        sage: m-n
        <Sq(4), 0, Sq(1)>
        sage: Sq(7)*(m+n)
        <0, 0, Sq(5,1)>

        """

        if isinstance(coefficients, FP_Element):
            self.coefficients = coefficients.coefficients
        else:
            A = SteenrodAlgebra(module.profile_algebra().prime())
            self.coefficients = [A(x) for x in coefficients]

        self.degree = Utility._deg_(module.degs, self.coefficients)

        profile_coeffs = [Profile.profile_ele(j, module.char) for j in self.coefficients]

        self.profile = Profile.enveloping_profile_profiles(\
                 [list(module.profile())] + profile_coeffs, module.char)

        ModuleElement.__init__(self, parent=module)

    def _get_coefficients(self):
        """
        TESTS::
            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: M = FP_Module((2,3,5), ((0, Sq(2), 1),))
            sage: m = M((0,Sq(3),Sq(1)));m
            <0, Sq(3), Sq(1)>
            sage: m.get_degree()
            6
            sage: m._get_coefficients()
            [0, Sq(3), Sq(1)]

        """
        return self.coefficients

    def get_degree(self):
        """
        EXAMPLES::

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: M = FP_Module((2,3,5))
            sage: m = M((0,Sq(3),Sq(1)));m
            <0, Sq(3), Sq(1)>
            sage: m.get_degree()
            6

        """
        return self.degree

    def _repr_(self):
        ## TO DO: Add parents when coeffs are sums:
        ## Sq(3)*M.0 + Sq(1)*M.2 is fine, but we'll
        ## need (Sq(3) + Sq(0,1))*M.0. Still a problem?
        return '<%s>' % ', '.join(['%s' % c for c in self.coefficients])

    def _lmul_(self, a):
        """
        This is the action which is called when the left module action is 
        evaluated.

        EXAMPLES:

        ::
            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: M = FP_Module(degs=(0,2,4), relations=((Sq(4),Sq(2),0),))
            sage: x = M((Sq(6), Sq(4), Sq(2))); x
            <Sq(6), Sq(4), Sq(2)>
            sage: x._lmul_(Sq(5))
            <Sq(5,2), Sq(3,2), Sq(1,2) + Sq(7)>

        """
        return self.parent()([a*c for c in self.coefficients])

    def _neg_(self):
        """
        Returns the negative of the element.

        EXAMPLES:

        ::
            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: M = FP_Module(degs=(0,2,4), relations=((Sq(4),Sq(2),0),))
            sage: x = M((Sq(6), Sq(4), Sq(2))); x
            <Sq(6), Sq(4), Sq(2)>
            sage: x._neg_()
            <Sq(6), Sq(4), Sq(2)>
            sage: N = FP_Module(degs=(2,), algebra = SteenrodAlgebra(5))
            sage: a = N((3,)); a
            <3>
            sage: a._neg_()
            <2>

        """
        return self.parent()([-c for c in self.coefficients])

    def _add_(self, other):
        r"""
        Returns the module sum of this and the given module element.

        EXAMPLES:

        ::
            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: M = FP_Module(degs=(0,2,4), relations=((Sq(4),Sq(2),0),))
            sage: a = M(0)
            sage: b = M((Sq(6), 0, Sq(2)))
            sage: c = M((Sq(4), 0, 0))
            sage: d = M((0, Sq(2), 1))
            sage: a+b
            <Sq(6), 0, Sq(2)>
            sage: b+b
            <0, 0, 0>
            sage: c+d
            <Sq(4), Sq(2), 1>
        """
        if self.parent() != other.parent():
            raise TypeError, "Can't add element in different modules"
        if self.degree == None: # if self = 0, degree is None
            return self.parent()(other.coefficients)
        if other.degree == None:   # if other = 0, degree is None
            return self.parent()(self.coefficients)
        if self.degree != other.degree:
            raise ValueError, "Can't add element of degree %s and %s"\
                  %(self.degree, other.degree)
        return self.parent()(
            [x + y for x,y in zip(self.coefficients, other.coefficients)])

    def _cmp_(self, other):
        """
        Compares two FP_Elements for equality. Cannot compare elements in
        different degrees or different modules.

        EXAMPLES:

        ::

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: M = FP_Module(degs=(0,2,4), relations=((Sq(4),Sq(2),0),))
            sage: M((Sq(3)*Sq(4), 0, 0))._cmp_(M((0, Sq(3)*Sq(2), 0)))
            0
            sage: M((Sq(4),Sq(2),1))._cmp_(M((0,0,1)))
            0
            sage: M((Sq(4),Sq(2),1))._cmp_(M(0))
            1

        """
        if self.parent() != other.parent():
            raise TypeError, "Cannot compare elements in different modules."
        if self.degree != other.degree and self.degree != None and other.degree != None:
            raise ValueError, \
            "Cannot compare elements of different degrees %s and %s"\
            %(self.degree, other.degree)
        if (self._add_(other._neg_()))._nonzero_():
            return 1
        else:
            return 0

    def free_vec(self,profile=None):
        """
        Returns a tuple of coefficients corresponding to the standard basis of
        the free vector space <---> self.coeffs.
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
        alg = SteenrodAlgebra(p=self.parent().char,profile=profile)
        bas_gen = reduce(lambda x,y : x+y,\
          [[(i,bb) for bb in alg.basis(n-self.parent().degs[i])] \
                   for i in range(len(self.parent().degs))])
        bas_vec = VectorSpace(FiniteField(self.parent().char),len(bas_gen))
        bas_dict = dict(zip(bas_gen,bas_vec.basis()))
        r = zip(range(len(self.coefficients)),self.coefficients)  #[...(gen,op)...]
        r = filter(lambda x: not x[1].is_zero(),r)   #remove trivial ops
        r = reduce(lambda x,y: x+y,\
               [map(lambda xx: (pr[0],\
               alg._milnor_on_basis(xx[0]), xx[1]),\
               [z for z in pr[1]]) for pr in r])
                  # now, r = [....(gen,basis_op,coeff)...]
        return reduce(lambda x,y: x+y, map(lambda x : x[2]*bas_dict[(x[0],x[1])],r))

    def vec(self,profile=None):
        r"""
        Return the vector form of self, as well as the linear transformation
        `q : F_n \rightarrow M_n` and `s:M_n \rightarrow F_n`, where `M_n`
        and `F_n` are the degree `n` parts of the module and free vector
        space, respectively.

        OUTPUT:

        -    ``x``    - The unique vector form of self in `M_n`.

        -    ``quo``    - The quotient vector space isomorphic to M_n

        -    ``bas``  - A list of pairs (gen_number,algebra element)
                        corresponding to self in the std basis of the free module.

        """
        if profile == None:
           profile = self.profile
        n = self.degree
        if n == None:
            return 0,0,0,0
        quo, bas = self.parent()._pres_(n, profile=profile)
        free_vector = quo.V().coordinate_vector(self.free_vec(profile=profile))
        return quo.quotient_map()(free_vector), quo, bas

    def _nonzero_(self):
        """

        EXAMPLES::

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: M = FP_Module(degs=(0,2,4), relations=((Sq(4),Sq(2),0),))
            sage: M(0)._nonzero_()
            False
            sage: M((Sq(6), 0, Sq(2)))._nonzero_()
            True
            sage: a = M((Sq(1)*Sq(2)*Sq(1)*Sq(4), 0, 0))
            sage: b = M((0, Sq(2)*Sq(2)*Sq(2), 0))
            sage: a._nonzero_()
            True
            sage: b._nonzero_()
            True
            sage: (a + b)._nonzero_()
            False

        """
        if self.degree == None:
            return False
        v,quo,bas = self.vec()
        return v != 0

    def normalize(self,profile=None):
        """
        Computes the normal form of self.

        EXAMPLES::

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: M = FP_Module(degs=(0,2,4), relations=((Sq(4),Sq(2),0),))
            sage: m = M((Sq(6), 0, Sq(2)))
            sage: m; m.normalize()
            <Sq(6), 0, Sq(2)>
            <Sq(6), 0, Sq(2)>
            sage: n = M((Sq(4), Sq(2), 0))
            sage: n; n.normalize()
            <Sq(4), Sq(2), 0>
            <0, 0, 0>

        """

        if profile == None:
           profile = self.profile

        if self.degree == None:
            return self

        v,quo,bas = self.vec(profile=profile)
        return self.parent()._lc_(quo.lift(v), bas)

    def __hash__(self):
        return hash(self.coefficients)

