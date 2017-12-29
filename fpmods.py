
#  http://doc.sagemath.org/html/en/developer/coding_basics.html#files-and-directory-structure



import sage.modules.fpmods.utility as Utility
import sage.modules.fpmods.profile as Profile
import sage.modules.fpmods.resolutions as Resolutions

from sage.algebras.steenrod.steenrod_algebra import SteenrodAlgebra
from sage.modules.free_module import VectorSpace
from sage.rings.finite_rings.finite_field_constructor import FiniteField
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
        [0, Sq(3), Sq(1)]
        sage: n = FP_Element(M, generators);n
        [0, Sq(3), Sq(1)]
        sage: type(m)
        <class 'sage.modules.fpmods.fpmods.FP_Module_with_category.element_class'>
        sage: type(n)
        <class 'sage.modules.fpmods.fpmods.FP_Element'>

        EXAMPLES::

        sage: from sage.modules.fpmods.fpmods import FP_Module, FP_Element
        sage: M = FP_Module((2,3,5));M
        Finitely presented module on 3 generators and 0 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function []
        sage: m = FP_Element(M, (0,Sq(3),Sq(1)));m
        [0, Sq(3), Sq(1)]
        sage: n = FP_Element(M, (Sq(4),Sq(1)*Sq(2),0));n
        [Sq(4), Sq(3), 0]
        sage: m+n
        [Sq(4), 0, Sq(1)]
        sage: m-n
        [Sq(4), 0, Sq(1)]
        sage: Sq(7)*(m+n)
        [0, 0, Sq(5,1)]

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

    def _repr_(self):
        ## TO DO: Add parents when coeffs are sums:
        ## Sq(3)*M.0 + Sq(1)*M.2 is fine, but we'll
        ## need (Sq(3) + Sq(0,1))*M.0. Still a problem?
        return '%s' % self.coefficients

    def _lmul_(self, a):
        """
        This is the action which is called when the left module action is 
        evaluated.

        EXAMPLES:

        ::
            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: M = FP_Module(degs=(0,2,4), relations=((Sq(4),Sq(2),0),))
            sage: x = M((Sq(6), Sq(4), Sq(2))); x
            [Sq(6), Sq(4), Sq(2)]
            sage: x._lmul_(Sq(5))
            [Sq(5,2), Sq(3,2), Sq(1,2) + Sq(7)]

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
            [Sq(6), Sq(4), Sq(2)]
            sage: x._neg_()
            [Sq(6), Sq(4), Sq(2)]
            sage: N = FP_Module(degs=(2,), algebra = SteenrodAlgebra(5))
            sage: a = N((3,)); a
            [3]
            sage: a._neg_()
            [2]

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
            [Sq(6), 0, Sq(2)]
            sage: b+b
            [0, 0, 0]
            sage: c+d
            [Sq(4), Sq(2), 1]
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
        quo, q, s, bas = self.parent()._pres_(n, profile=profile)
        return q(self.free_vec(profile=profile)),q,s,bas

    def _nonzero_(self):
        """

        EXAMPLES:

        ::

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
        v,q,sec,bas = self.vec()
        return v != 0

    def normalize(self,profile=None):
        """
        Computes the normal form of self.

        EXAMPLES:

        ::

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: M = FP_Module(degs=(0,2,4), relations=((Sq(4),Sq(2),0),))
            sage: m = M((Sq(6), 0, Sq(2)))
            sage: m; m.normalize()
            [Sq(6), 0, Sq(2)]
            [Sq(6), 0, Sq(2)]
            sage: n = M((Sq(4), Sq(2), 0))
            sage: n; n.normalize()
            [Sq(4), Sq(2), 0]
            [0, 0, 0]

        """

        if profile == None:
           profile = self.profile

        if self.degree == None:
            return self

        v,q,sec,bas = self.vec(profile=profile)
        return self.parent()._lc_(sec(v),bas)

    def __hash__(self):
        return hash(self.x)


#--------------------------------------------------------------------------------
#----------------------Finitely-Presented-Modules--------------------------------
#--------------------------------------------------------------------------------
import sage.modules.fpmods.utility as Utility
import sage.modules.fpmods.profile as Profile

from sage.algebras.steenrod.steenrod_algebra import SteenrodAlgebra

from sage.structure.unique_representation import UniqueRepresentation
from sage.modules.module import Module

class FP_Module(UniqueRepresentation, Module):
    r"""
    A finitely presented module over a sub-Hopf algebra of the
    Steenrod Algebra (including the full Steenrod Algebra).

    EXAMPLES:

    These examples show how to define modules over the Steenrod Algebra at the
    prime 2. The last example is a free module with a single generator in
    degree 4.

    ::

        sage: from sage.modules.fpmods.fpmods import FP_Module
        sage: from sage.misc.sage_unittest import TestSuite
        sage: degs = [1,3]
        sage: K = FP_Module(degs = tuple(degs));K
        Finitely presented module on 2 generators and 0 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function []
        sage: K.category()
        Category of modules over mod 2 Steenrod algebra, milnor basis
        sage: L = FP_Module((2,3),((Sq(2),Sq(1)),(0,Sq(2))));L
        Finitely presented module on 2 generators and 2 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [2, 1]
        sage: M = FP_Module((2,3),((Sq(2),Sq(1)),));M
        Finitely presented module on 2 generators and 1 relation over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [2, 1]
        sage: K.element_class
        <class 'sage.modules.fpmods.fpmods.FP_Module_with_category.element_class'>
        sage: m = M((0,1)); m
        [0, 1]
        sage: K.is_parent_of(m)
        False
        sage: L.is_parent_of(m)
        False
        sage: M.is_parent_of(m)
        True
        sage: TestSuite(K).run(verbose=True)
        running ._test_additive_associativity() . . . pass
        running ._test_an_element() . . . pass
        running ._test_cardinality() . . . pass
        running ._test_category() . . . pass
        running ._test_elements() . . .
          Running the test suite of self.an_element()
          running ._test_category() . . . pass
          running ._test_eq() . . . pass
          running ._test_new() . . . pass
          running ._test_nonzero_equal() . . . pass
          running ._test_not_implemented_methods() . . . pass
          running ._test_pickling() . . . pass
          pass
        running ._test_elements_eq_reflexive() . . . pass
        running ._test_elements_eq_symmetric() . . . pass
        running ._test_elements_eq_transitive() . . . pass
        running ._test_elements_neq() . . . pass
        running ._test_eq() . . . pass
        running ._test_new() . . . pass
        running ._test_not_implemented_methods() . . . pass
        running ._test_pickling() . . . pass
        running ._test_some_elements() . . . pass
        running ._test_zero() . . . pass

    """

    # In the category framework, Elements of the class FP_Module are of the
    # class FP_Element, see
    # http://doc.sagemath.org/html/en/thematic_tutorials/coercion_and_categories.html#implementing-the-category-framework-for-the-elements
    Element = FP_Element

    def __init__(self, degs, relations=None, char=None, algebra=None):

        if (char is None) and (algebra is None):
            _char = 2
            _algebra = SteenrodAlgebra(_char, profile=(0,))
        elif (char is None) and (algebra is not None):
            _algebra = algebra
            _char = _algebra.prime()
        elif (char is not None) and (algebra is None):
            _char = char
            if char == 2:
                _algebra = SteenrodAlgebra(p=_char, profile=(0,))
            else:
                _algebra = SteenrodAlgebra(p=_char, profile = ((),(0,)))
        else:
            _char = char
            _algebra = algebra

        if (_char != _algebra.prime()):
            raise TypeError, "Characteristic and algebra are incompatible."

        for i in range(len(degs) - 1):
            if degs[i] > degs[i+1]:
                raise TypeError, "Degrees of generators must be in non-decreasing order."

        if relations is None:
            prof = _algebra._profile
        else:
            prof = Profile.enveloping_profile_profiles(\
                      [Profile.enveloping_profile_elements(r, _char) for r in relations]\
                      +[list(_algebra._profile)], _char)

        # Initialize member variables.
        self._profile_algebra = SteenrodAlgebra(p=_char, profile=prof)

        self.char = _char

        rels = [] if relations is None else list(relations) 
        for r in rels:
            if r == [0]*len(degs):
                rels.remove([0]*len(degs))

        self.rels = [[(self._profile_algebra)(c) for c in r] for r in rels]

        self.degs = list(degs)

        try:
            self.reldegs = [Utility._deg_(self.degs,r) for r in self.rels]
        except ValueError:
            for r in rels:
                try:
                   Utility._deg_(degs,r)
                except ValueError:
                   raise ValueError, "Inhomogeneous relation %s" % r

        self._populate_coercion_lists_()

        # Call the base class constructor.
        Module.__init__(self, SteenrodAlgebra(self.char))

    def profile(self):
        """
        Returns the profile of the smallest sub-Hopf algebra of the Steenrod algebra
        over which the module can be defined.  I.e. the smallest one that
        contains all the generators and relations.

        EXAMPLES::

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: Z = FP_Module((0,),((Sq(1),),(Sq(2),),(Sq(4),))); Z.profile()
            (3, 2, 1)

        """
        return self._profile_algebra._profile

    def profile_algebra(self):
        """
        Returns the smallest sub-Hopf algebra of the Steenrod algebra 
        over which the module can be defined.  I.e. the smallest one that
        contains all the generators and relations.

        EXAMPLES::

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: FP_Module((0,2,3)).profile_algebra()
            sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function []
            sage: FP_Module((0,2,3), ((0,Sq(1),1),)).profile_algebra()
            sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [1]

        """
        return self._profile_algebra

    def conn(self):
        """
        Returns the connectivity of the module.

        EXAMPLES::

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: X = FP_Module((0,2,3));X.conn()
            0
            sage: M = FP_Module((2,3),((Sq(2),Sq(1)), (0,Sq(2))));M.conn()
            2
            sage: Q = FP_Module(());Q.conn()
            +Infinity
        """
        return min(self.degs + [PlusInfinity()])

    def rdegs(self):
        """
        Returns the degrees of the relations of the module.

        EXAMPLES::

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: XX = FP_Module((0,2,3),((0,Sq(1),1),));XX.rdegs()
            [3]
            sage: M = FP_Module((2,3),((Sq(2),Sq(1)),(0,Sq(2))));M.rdegs()
            [4, 5]
        """
        return [Utility._deg_(self.degs,r) for r in self.rels]

    def _element_constructor_(self, coefficients):
        """
        Forms the element with ith coefficient x[i].
        This results in the identity operation if x is already in the module.

        INPUT:

        -   ``coefficients``  - A tuple of coefficients.

        OUTPUT: An FP_Element with coefficients from ``coefficients``.

        EXAMPLES::

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: M = FP_Module(degs=(0,2,4), relations=((Sq(4),Sq(2),0),))
            sage: e = M(0); e
            [0, 0, 0]
            sage: type(e)
            <class 'sage.modules.fpmods.fpmods.FP_Module_with_category.element_class'>
            sage: f = M((Sq(6), 0, Sq(2))); f
            [Sq(6), 0, Sq(2)]
            sage: type(f)
            <class 'sage.modules.fpmods.fpmods.FP_Module_with_category.element_class'>
            sage: g = M((Sq(6), 0, Sq(2))); g
            [Sq(6), 0, Sq(2)]
            sage: M(g)
            [Sq(6), 0, Sq(2)]
            sage: type(g)
            <class 'sage.modules.fpmods.fpmods.FP_Module_with_category.element_class'>

        """

        if isinstance(coefficients, FP_Element): #.parent() == self:
            return coefficients
        elif coefficients == 0:
            return self.element_class(self, len(self.degs)*(0,))
        else:
            return self.element_class(self, coefficients)

    def an_element(self, degree=None):
        r"""

        EXAMPLES::

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: M = FP_Module(degs=(0,2,4), relations=((Sq(4),Sq(2),0),))
            sage: M.an_element()
            [Sq(1,1,1), Sq(3,2), Sq(0,0,1)]
            sage: M.an_element(0)
            [1, 0, 0]
            sage: M.an_element(1)
            [Sq(1), 0, 0]
            sage: M.an_element(2)
            [Sq(2), 1, 0]
            sage: M.an_element(3)
            [Sq(0,1), Sq(1), 0]
            sage: M.an_element(4)
            [Sq(1,1), Sq(2), 1]
            sage: M.an_element(5)
            [Sq(2,1), Sq(0,1), Sq(1)]
            sage: M.an_element(6)
            [Sq(0,2), Sq(1,1), Sq(2)]
            sage: M.an_element(17)
            [Sq(2,0,0,1), Sq(2,2,1), Sq(4,3)]
            sage: N = FP_Module(degs=(2,), algebra = SteenrodAlgebra(2))
            sage: for d in range(20):
            ....:     N.an_element(degree=d)
            [0]
            [0]
            [1]
            [Sq(1)]
            [Sq(2)]
            [Sq(0,1)]
            [Sq(1,1)]
            [Sq(2,1)]
            [Sq(6)]
            [Sq(4,1)]
            [Sq(5,1)]
            [Sq(3,2)]
            [Sq(1,3)]
            [Sq(2,3)]
            [Sq(0,4)]
            [Sq(6,0,1)]
            [Sq(4,1,1)]
            [Sq(2,2,1)]
            [Sq(0,3,1)]
            [Sq(3,0,2)]

        """

        if degree == None:
            degree = max(self.degs) + 7

        coefficients = []

        for g in self.degs:
            basis = self.base_ring().basis(degree - g) if degree >= g else ()
            # All of the algebra generators in basis will bring the
            # module generator in dimension g to dimension
            # g + (topDimension - g) = topDimension.  Picking any one of them
            # will do, so we pick the one with index (g (mod l)).
            l = len(basis)
            coefficients.append(0 if l == 0 else basis[g % l])

        return self.element_class(self, coefficients)

#    def __cmp__(self, other):
#        if not isinstance(other, FP_Module):
#            return cmp(type(other), FP_Module)
#        return cmp(self.base_ring(),other.base_ring())

    def _repr_(self):
        """
        String representation of the module.

        EXAMPLES::

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: M = FP_Module((0,2,4),((Sq(4),Sq(2),0),)); M
            Finitely presented module on 3 generators and 1 relation over sub-Hopf
            algebra of mod 2 Steenrod algebra, milnor basis, profile function [3, 2, 1]

            sage: N = FP_Module((0,1),((Sq(2),Sq(1)),(Sq(2)*Sq(1),Sq(2)))); N
            Finitely presented module on 2 generators and 2 relations over sub-Hopf
            algebra of mod 2 Steenrod algebra, milnor basis, profile function [2, 1]


        """
        return "Finitely presented module on %s generator%s and %s relation%s over %s"\
            %(len(self.degs), "" if len(self.degs) == 1 else "s",
              len(self.rels), "" if len(self.rels) == 1 else "s",
              self._profile_algebra)

    def _pres_(self, n, profile=None):
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

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: M = FP_Module((0,2,4),((Sq(4),Sq(2),0),)); M((Sq(2),0,0))
            [Sq(2), 0, 0]
            sage: quo,q,sec,bas = M._pres_(4)
            sage: dim(quo)
            3
            sage: q
            Vector space morphism represented by the matrix:
            [1 0 0]
            [0 1 0]
            [0 1 0]
            [0 0 1]
            Domain: Vector space of dimension 4 over Finite Field of size 2
            Codomain: Vector space quotient V/W of dimension 3 over Finite Field of size 2 where
            V: Vector space of dimension 4 over Finite Field of size 2
            W: Vector space of degree 4 and dimension 1 over Finite Field of size 2
            Basis matrix:
            [0 1 1 0]
            sage: sec
            Vector space morphism represented by the matrix:
            [1 0 0 0]
            [0 1 0 0]
            [0 0 0 1]
            Domain: Vector space quotient V/W of dimension 3 over Finite Field of size 2 where
            V: Vector space of dimension 4 over Finite Field of size 2
            W: Vector space of degree 4 and dimension 1 over Finite Field of size 2
            Basis matrix:
            [0 1 1 0]
            Codomain: Vector space of dimension 4 over Finite Field of size 2
        """
        if profile == None:
            profile = self.profile()
        alg = SteenrodAlgebra(p=self.char,profile=profile)
        bas_gen = reduce(lambda x,y : x+y,\
                  [[(i,bb) for bb in alg.basis(n-self.degs[i])]\
                           for i in range(len(self.degs))],[])
        bas_vec = VectorSpace(FiniteField(self.char),len(bas_gen))
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
            sec = Hom(quo,bas_vec).zero()
            q = Hom(bas_vec,quo)([quo(0) for xx in bas_vec.basis()])
        else:
            sec = Hom(quo,bas_vec)([quo.lift(xx) for xx in quo.basis()])
            q = Hom(bas_vec,quo)([quo(xx) for xx in bas_vec.basis()])
        return quo, q, sec, bas_gen


    def _lc_(self, coefficients, basis_elements):
        """
        Creates the FP_Element corresponding to the lists ``coefficients`` of coefficients
        and ``basis_elements`` of basis elements. This function is intended for internal use only.

        INPUT:

        -    ``coefficients``   -  A list of (either FiniteField(p) elements or algebra elements)
             coefficients.

        -    ``basis_elements``   -  A list of tuples (gen_number, algebra elt)
             corresponding to the std basis for the free module on self.degs

       OUTPUT: The linear combination given by the sum of coefficients[i]*basis_elements i][1]*gen(bas[i][0]) ???

       NOTE: The list of coefficients can lie in FiniteField(p) or the algebra.
             The output is not normalizes, i.e. the sum is taken in the free module.

        EXAMPLES::

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: M = FP_Module((2, 3), ((Sq(2), Sq(1)), (0, Sq(2))))
            sage: bas = [(0, 1)]; co = [Sq(1)]
            sage: x = M._lc_(co, bas); x
            [Sq(1), 0]
            sage: bas2 = [(1, 1)]
            sage: y = M._lc_(co, bas2); y
            [0, Sq(1)]

        """
        if len(coefficients) != len(basis_elements):
            raise ValueError,\
            "Number of coefficients (%s) must be the same as number of basis elements (%s) " \
                % (len(co), len(bas))

        return reduce(lambda x,y : x+y, \
              [(coefficients[i]*basis_elements[i][1])*self.gen(basis_elements[i][0]) for i in range(len(coefficients))],
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

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: M = FP_Module((2, 3), ((Sq(2), Sq(1)), (0,Sq(2))))
            sage: M.basis(0)
            []
            sage: M.basis(3)
            [[Sq(1), 0], [0, 1]]
            sage: for i in range(10):
            ....:     print ("Basis for M in dimension %d: %s" % (i, M.basis(i)))
            Basis for M in dimension 0: []
            Basis for M in dimension 1: []
            Basis for M in dimension 2: [[1, 0]]
            Basis for M in dimension 3: [[Sq(1), 0], [0, 1]]
            Basis for M in dimension 4: [[Sq(2), 0]]
            Basis for M in dimension 5: [[Sq(0,1), 0]]
            Basis for M in dimension 6: [[Sq(1,1), 0]]
            Basis for M in dimension 7: []
            Basis for M in dimension 8: []
            Basis for M in dimension 9: []

        """
        if profile == None:
            profile = self.profile()
        quo,q,s,bas = self._pres_(n, profile=profile)
        return [self._lc_(s(v),bas) for v in quo.basis()]

#    __getitem__ = basis

    def gens(self):
        """
        The list of generators of the module.

        EXAMPLES::

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: M = FP_Module((0, 2, 3)); M.gens()
            [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
            sage: N = FP_Module((0,1),((Sq(2),Sq(1)),)); N.gens()
            [[1, 0], [0, 1]]

        """
        return [self.element_class(self, Utility._del_(i, len(self.degs)))
           for i in range(len(self.degs))]

    def gen(self, index=0):
        """
        The index'th generator of the module as an FP_Element.

        EXAMPLES::

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: M = FP_Module((0,2,3)); M.gen(0)
            [1, 0, 0]
            sage: N = FP_Module((0, 1), ((Sq(2), Sq(1)),)); N.gen(1)
            [0, 1]

        """
        if index < 0 or index >= len(self.degs):
            raise ValueError,\
            "Module has generators numbered 0 to %s; generator %s does not exist" % (len(self.degs) - 1, index)
        return self.element_class(self, Utility._del_(index, len(self.degs)))

