
#  http://doc.sagemath.org/html/en/developer/coding_basics.html#files-and-directory-structure

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

EXAMPLES:

    sage: M = FP_Module([0,1],[[Sq(2),Sq(1)],[0,Sq(2)]])

AUTHORS:

- Robert R. Bruner, Michael J. Catanzaro (2012): initial version


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



import sage.modules.fpmods.utility as Utility
import sage.modules.fpmods.profile as Profile
import sage.modules.fpmods.resolutions as Resolutions

from sage.algebras.steenrod.steenrod_algebra import SteenrodAlgebra
from sage.modules.free_module import VectorSpace
from sage.rings.finite_rings.finite_field_constructor import FiniteField

# Import the free function for creating Homsets
from sage.categories.homset import Hom
from sage.categories.homset import End


from sage.rings.infinity import PlusInfinity

from copy import copy

#--------------------------------------------------------------------------------
#----------------------Finitely-Presented-Modules--------------------------------
#--------------------------------------------------------------------------------

import sage.modules.fpmods.utility as Utility

import sage.modules.fpmods.profile as Profile

from sage.algebras.steenrod.steenrod_algebra import SteenrodAlgebra

# http://doc.sagemath.org/html/en/thematic_tutorials/coercion_and_categories.html#the-parent
# "You are encouraged to make your parent "unique". That's to say, parents 
#  should only evaluate equal if they are identical. Sage provides frameworks to
#  create unique parents. We use here the most easy one: Inheriting from the
#  class sage.structure.unique_representation.UniqueRepresentation is enough.
#  Making parents unique can be quite important for an efficient implementation,
#  because the repeated creation of "the same" parent would take a lot of time."
#
# Deriving from the class UniqueRepresentation forces the condition that the
# constructor arguments must be hashable.  This excludes the use of arrays [],
# instead we use tuples () which are immutable and hashable.  The downside
# is that notation is a bit ugly in some cases: E.g. the singleton tuple
# notation in python is (5,) to be able to distinguish it from (5) which isn't
# a tuple.
from sage.structure.unique_representation import UniqueRepresentation

from sage.modules.module import Module

from sage.modules.fpmods.fpmod_element import FP_Element


def create_fp_module(degs, relations=None, char=None, algebra=None):
    """

    Constructs an instance of the FP_Module class using non-hashable lists
    assert input.

    EXAMPLES::

        sage: from sage.modules.fpmods.fpmods import create_fp_module
        sage: K = create_fp_module(degs = [1,3], relations = [[Sq(3), Sq(1)]]);K
        Finitely presented module on 2 generators and 1 relation ...

    """
    rels = None if relations is None else tuple(tuple(rel) for rel in relations)
    return FP_Module(tuple(degs), rels, char, algebra)


class FP_Module(UniqueRepresentation, Module):
    r"""
    A finitely presented module over a sub-Hopf algebra of the
    Steenrod Algebra (including the full Steenrod Algebra).

    EXAMPLES:

    These examples show how to define modules over the Steenrod Algebra at the
    prime 2. The last example is a free module with a single generator in
    degree 4.

    The category framework::

        sage: from sage.modules.fpmods.fpmods import FP_Module
        sage: degs = [1,3]
        sage: K = FP_Module(degs = tuple(degs));K
        Finitely presented module on 2 generators and 0 relations ...
        sage: K.category()
        Category of modules over mod 2 Steenrod algebra, milnor basis
        sage: L = FP_Module((2,3),((Sq(2),Sq(1)),(0,Sq(2))));L
        Finitely presented module on 2 generators and 2 relations ...
        sage: M = FP_Module((2,3),((Sq(2),Sq(1)),));M
        Finitely presented module on 2 generators and 1 relation ...
        sage: K.element_class
        <class 'sage.modules.fpmods.fpmods.FP_Module_with_category.element_class'>
        sage: m = M((0,1)); m
        <0, 1>
        sage: K.is_parent_of(m)
        False
        sage: L.is_parent_of(m)
        False
        sage: M.is_parent_of(m)
        True
        sage: from sage.misc.sage_unittest import TestSuite
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


    Creating elements::

        sage: from sage.modules.fpmods.fpmods import FP_Module
        sage: K = FP_Module(degs = tuple([1,3]));K
        Finitely presented module on 2 generators and 0 relations ...
        sage: K.category()
        Category of modules over mod 2 Steenrod algebra, milnor basis
        sage: L = FP_Module((2,3),((Sq(2),Sq(1)),(0,Sq(2))));L
        Finitely presented module on 2 generators and 2 relations ...
        sage: M = FP_Module((2,3),((Sq(2),Sq(1)),));M
        Finitely presented module on 2 generators and 1 relation ...
        sage: m = M((0,1)); m
        <0, 1>
        sage: M(m)
        <0, 1>

    Creating homomorphisms::

        sage: from sage.modules.fpmods.fpmods import FP_Module
        sage: from sage.misc.sage_unittest import TestSuite
        sage: F = FP_Module(degs = tuple([1,3]));
        sage: L = FP_Module((2,3),((Sq(2),Sq(1)),(0,Sq(2))));
        sage: homset = Hom(F, L); homset
        Set of Morphisms from Finitely presented module on 2 generators ...
        sage: homset.an_element()
        The trivial module homomorphism:
          Domain: Finitely presented module on 2 generators and 0 relations ...
          Codomain: Finitely presented module on 2 generators and 2 relations ...
        sage: homset([L((Sq(1), 1)), L((0, Sq(2)))])
        Module homomorphism of degree 2:
          Domain: Finitely presented module on 2 generators and 0 relations ...
          Codomain: Finitely presented module on 2 generators and 2 relations ...
        sage: Hom(F, L) ([L((Sq(1), 1)), L((0, Sq(2)))]).kernel()
        Module homomorphism of degree 0:
          Domain: Finitely presented module on 2 generators and 1 relation over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [2, 1]
          Codomain: Finitely presented module on 2 generators and 0 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function []
        defined by sending the generators
          [<1, 0>, <0, 1>]
        to
          [<0, 1>, <Sq(0,1), 0>]
        sage: TestSuite(homset).run(verbose=True)
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
        sage: H = Hom(F, L); H
        Set of Morphisms from Finitely presented module on 2 generators and 0 relations ...
        sage: H(0)
        The trivial module homomorphism:
          Domain: Finitely presented module on 2 generators and 0 relations ...
          Codomain: Finitely presented module on 2 generators and 2 relations ...
        sage: f = H( [L((Sq(1), 1)), L((0, Sq(2)))] ); f
        Module homomorphism of degree 2:
          Domain: Finitely presented module on 2 generators and 0 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function []
          Codomain: Finitely presented module on 2 generators and 2 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [2, 1]
        defined by sending the generators
          [<1, 0>, <0, 1>]
        to
          [<Sq(1), 1>, <0, Sq(2)>]
        sage: Hom(F, L) ([L((0, 0)), L((0, 1))]).kernel()
        Module homomorphism of degree 0:
          Domain: Finitely presented module on 2 generators and 1 relation over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [2, 1]
          Codomain: Finitely presented module on 2 generators and 0 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function []
        defined by sending the generators
          [<1, 0>, <0, 1>]
        to
          [<1, 0>, <0, Sq(2)>]
        sage: f - H.zero() == f
        True
        sage: Hom(L, F).zero()
        The trivial module homomorphism:
          Domain: Finitely presented module on 2 generators and 2 relations ...
          Codomain: Finitely presented module on 2 generators and 0 relations ...
        sage: Hom(L, F).zero() == Hom(L, F)(0)
        True
        sage: id = End(L).identity()
        sage: id + id
        The trivial module homomorphism:
          Domain: Finitely presented module on 2 generators and 2 relations ...
          Codomain: Finitely presented module on 2 generators and 2 relations ...
        sage: id*id
        The identity module homomorphism:
          Domain: Finitely presented module on 2 generators and 2 relations ...
          Codomain: Finitely presented module on 2 generators and 2 relations ...
        sage: id*id == id
        True
        sage: id*id != id
        False
        sage: id.get_degree()
        0
        sage: f = id + id + id; f
        The identity module homomorphism:
          Domain: Finitely presented module on 2 generators and 2 relations ...
          Codomain: Finitely presented module on 2 generators and 2 relations ...
        sage: f == id
        True
        sage: el = L((Sq(5), Sq(4))); el.normalize()
        <Sq(5), Sq(4)>
        sage: End(L).identity()(el)
        <Sq(5), Sq(4)>
        sage: f(el)
        <Sq(5), Sq(4)>

    TESTS::

        sage: from sage.modules.fpmods.fpmods import FP_Module
        sage: F = FP_Module(degs = tuple([1,3]));
        sage: L = FP_Module((2,3),((Sq(2),Sq(1)),(0,Sq(2))));
        sage: H = Hom(F, L);
        sage: H( [L((Sq(1), 1)), L((0, Sq(3)))] )
        Traceback (most recent call last):
         ...
        ValueError: Ill defined homomorphism (degrees do not match)
          Generator #0 (degree 1) -> <Sq(1), 1> (degree 3) shifts degrees by 2
          Generator #1 (degree 3) -> <0, Sq(3)> (degree 6) shifts degrees by 3

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

        self.degs = degs

        rels = [] 
        reldegs = []
        # Append all the non-zero relations.
        if relations != None:
            for r in relations:
                if not all(v == 0 for v in r):
                    relation = tuple([(self._profile_algebra)(c) for c in r])
                    rels.append(relation)
                    try:
                        x = Utility._deg_(self.degs, relation)
                        reldegs.append(x)
                    except ValueError:
                        for r in rels:
                            try:
                               Utility._deg_(degs,r)
                            except ValueError:
                               raise ValueError, "Inhomogeneous relation %s" % r
                    except NotImplementedError:
                        print (r)

        self.rels = tuple(rels)
        self.reldegs = tuple(reldegs)

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
        return min(self.degs + (PlusInfinity(),))

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
            <0, 0, 0>
            sage: type(e)
            <class 'sage.modules.fpmods.fpmods.FP_Module_with_category.element_class'>
            sage: f = M((Sq(6), 0, Sq(2))); f
            <Sq(6), 0, Sq(2)>
            sage: type(f)
            <class 'sage.modules.fpmods.fpmods.FP_Module_with_category.element_class'>
            sage: g = M((Sq(6), 0, Sq(2))); g
            <Sq(6), 0, Sq(2)>
            sage: M(g)
            <Sq(6), 0, Sq(2)>
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
            sage: M.zero()
            <0, 0, 0>
            sage: M.an_element()
            <Sq(1,1,1), Sq(3,2), Sq(0,0,1)>
            sage: M.an_element(0)
            <1, 0, 0>
            sage: M.an_element(1)
            <Sq(1), 0, 0>
            sage: M.an_element(2)
            <Sq(2), 1, 0>
            sage: M.an_element(3)
            <Sq(0,1), Sq(1), 0>
            sage: M.an_element(4)
            <Sq(1,1), Sq(2), 1>
            sage: M.an_element(5)
            <Sq(2,1), Sq(0,1), Sq(1)>
            sage: M.an_element(6)
            <Sq(0,2), Sq(1,1), Sq(2)>
            sage: M.an_element(17)
            <Sq(2,0,0,1), Sq(2,2,1), Sq(4,3)>
            sage: N = FP_Module(degs=(2,), algebra = SteenrodAlgebra(2))
            sage: for d in range(20):
            ....:     N.an_element(degree=d)
            <0>
            <0>
            <1>
            <Sq(1)>
            <Sq(2)>
            <Sq(0,1)>
            <Sq(1,1)>
            <Sq(2,1)>
            <Sq(6)>
            <Sq(4,1)>
            <Sq(5,1)>
            <Sq(3,2)>
            <Sq(1,3)>
            <Sq(2,3)>
            <Sq(0,4)>
            <Sq(6,0,1)>
            <Sq(4,1,1)>
            <Sq(2,2,1)>
            <Sq(0,3,1)>
            <Sq(3,0,2)>

        """

        if len(self.degs) == 0:
            return self.element_class(self, [])

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

        -  ``M_n`` - A finite dimensional vector space over F_p isomorphic to
                    the degree n part of the module.
                      
        -  `` bas_gen``  - A list of pairs (gen_number, algebra element)
            corresponding to the std basis for the domain of q.  This set of
            elements gives the chosen isomorphism between q.domain() and F_n.

        EXAMPLES::

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: M = FP_Module((0,2,4),((Sq(4),Sq(2),0),)); M((Sq(2),0,0))
            <Sq(2), 0, 0>
            sage: M_n, bas = M._pres_(4)
            sage: dim(M_n)
            3
            sage: bas
            [(0, Sq(1,1)), (0, Sq(4)), (1, Sq(2)), (2, 1)]

        """
        if profile == None:
            profile = self.profile()
        alg = SteenrodAlgebra(p=self.char,profile=profile)
        bas_gen = reduce(lambda x,y : x+y,\
                  [[(i,bb) for bb in alg.basis(n - self.degs[i])]\
                           for i in range(len(self.degs))],[])

        bas_vec = VectorSpace(FiniteField(self.char),len(bas_gen))
        bas_dict = dict(zip(bas_gen,bas_vec.basis()))
        rel_vec = bas_vec.subspace([0])

        numRelations = len(self.rels)
        numRelDegs = len(self.reldegs)

        for i in range(numRelations):
            if self.reldegs[i] <= n:
                for co in alg.basis(n - self.reldegs[i]):
                    r = zip(range(len(self.degs)),[co*c for c in self.rels[i]])
                    r = filter(lambda x : not x[1].is_zero(),r) # remove trivial
                    if len(r) != 0:
                        r = reduce(lambda x,y : x+y,
                            [map(lambda xx: (pr[0],alg._milnor_on_basis(xx[0]),xx[1]),\
                                 [z for z in pr[1]]) for pr in r])
                        rel_vec += bas_vec.subspace(\
                            [reduce(lambda x,y: x+y,\
                            map(lambda x: x[2]*bas_dict[(x[0],x[1])],r))])
        quotient = bas_vec/rel_vec
        return quotient, bas_gen

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
            <Sq(1), 0>
            sage: bas2 = [(1, 1)]
            sage: y = M._lc_(co, bas2); y
            <0, Sq(1)>

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

        XXX: Avoid the name "basis" since a module with a basis is a free
             module (basis means a linearly independent set of generating
             elements).

        Returns elements of the free module mapping to self.  These elements
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
            [<Sq(1), 0>, <0, 1>]
            sage: for i in range(10):
            ....:     print ("Basis for M in dimension %d: %s" % (i, M.basis(i)))
            Basis for M in dimension 0: []
            Basis for M in dimension 1: []
            Basis for M in dimension 2: [<1, 0>]
            Basis for M in dimension 3: [<Sq(1), 0>, <0, 1>]
            Basis for M in dimension 4: [<Sq(2), 0>]
            Basis for M in dimension 5: [<Sq(0,1), 0>]
            Basis for M in dimension 6: [<Sq(1,1), 0>]
            Basis for M in dimension 7: []
            Basis for M in dimension 8: []
            Basis for M in dimension 9: []

        """
        if profile == None:
            profile = self.profile()
        M_n, bas = self._pres_(n, profile=profile)
        return [self._lc_(M_n.lift(v), bas) for v in M_n.basis()]

    def gens(self):
        """
        The list of generators of the module.

        EXAMPLES::

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: M = FP_Module((0, 2, 3)); M.gens()
            [<1, 0, 0>, <0, 1, 0>, <0, 0, 1>]
            sage: N = FP_Module((0,1),((Sq(2),Sq(1)),)); N.gens()
            [<1, 0>, <0, 1>]

        """
        return [self.element_class(self, Utility._del_(i, len(self.degs)))
           for i in range(len(self.degs))]

    def get_degs(self):
        """
        Returns the list of degrees of the generators for this module.

        EXAMPLES:
            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: M = FP_Module((0, 2, 3));
            sage: M.get_degs()
            (0, 2, 3)
            sage: N = FP_Module((0,1),((Sq(2),Sq(1)),));
            sage: N.get_degs()
            (0, 1)

        """
        return self.degs

    def get_rels(self):
        """
        Returns a tuple of relations, where each relation is a tuple 
        of coefficients (which are elements of the profile algebra) defining
        a relation this module.

        EXAMPLES:
            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: FP_Module((0, 2, 3)).get_rels()
            ()
            sage: N = FP_Module((0,1),((Sq(2),Sq(1)),)).get_rels(); N
            ((Sq(2), Sq(1)),)

        """
        return self.rels

    def gen(self, index=0):
        """
        Returns the module generator (as an module element) with the given 
        index.

        EXAMPLES::

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: M = FP_Module((0,2,3)); M.gen(0)
            <1, 0, 0>
            sage: N = FP_Module((0, 1), ((Sq(2), Sq(1)),)); N.gen(1)
            <0, 1>

        """
        if index < 0 or index >= len(self.degs):
            raise ValueError,\
            "Module has generators numbered 0 to %s; generator %s does not exist" % (len(self.degs) - 1, index)
        return self.element_class(self, Utility._del_(index, len(self.degs)))


    def _Hom_(self, Y, category):
#        r"""
#        The internal hook used by the free function 
#        sage.categories.homset.hom.Hom() to create homsets involving this
#        parent.
#
#        INPUT:
#
#        OUTPUT:
#
#        EXAMPLES::
#
#        TESTS::
#
#        """
        from .fpmod_homspace import FP_ModuleHomspace
        return FP_ModuleHomspace(self, Y, category)

    def min_profile(self):
        """
        Returns the profile of the smallest sub-Hopf algebra containing self.

        OUTPUT: The profile function of the sub-Hopf algebra with the smallest
        degree containing self.

        EXAMPLES::

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: A3 = SteenrodAlgebra(p=2,profile=(4,3,2,1))
            sage: Y = FP_Module((0,), ((Sq(1),),),algebra=A3)
            sage: Y.profile()
            (4, 3, 2, 1)
            sage: Y.min_profile()
            (1,)
        """
        if not self.rels:
            return self.algebra._profile
        else:
            profile = Profile.enveloping_profile_profiles(\
                     [Profile.enveloping_profile_elements(r,self.char) for r in self.rels],\
                      self.char)
            return profile

    def suspension(self,t):
        """
        Suspends a module by degree t.

        INPUT:

        -   ``t``  - An integer by which the module is suspended.

        OUTPUT:

        -   ``C``  ` A copy of the module `self` which is suspended by `t`.

        EXAMPLES::

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: Y = FP_Module((0,), ((Sq(1),),))
            sage: X = Y.suspension(4)
            sage: X.degs;X.rels
            (4,)
            ((Sq(1),),)
            sage: M = FP_Module( (2,3), ( (Sq(2), Sq(1)), (0, Sq(2)) ) )
            sage: Q = M.suspension(1)
            sage: Q.degs;Q.rels
            (3, 4)
            ((Sq(2), Sq(1)), (0, Sq(2)))

        """
        generator_degrees = [g + t for g in self.get_degs()]
        return FP_Module(degs=tuple(generator_degrees), relations=self.get_rels(), algebra=self.profile_algebra())

    def submodule(self,L):
        """
        The submodule of self spanned by elements of the list L.

        The map from the free module on the elements of L to
        the submodule, as well as the inclusion of the submodule are also returned.
        ``N``  - The FP_Module generated by `L`, a submodule of `self`.

        INPUT:

        -  ``L``  - A list of elements of `self`.

        OUTPUT:


        -  ``i``  - The inclusion of `N` into `self`.

        -  ``p``  - The map from the free module on the elements of L to `N`.


        EXAMPLES::

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: N = FP_Module((0,1), ((Sq(2),Sq(1)),))
            sage: h,g = N.submodule([N.gen(0)])
            sage: Y=h.domain()
            sage: Y.get_degs();Y.get_rels()
            (0,)
            ((Sq(3),),)

        """
        degs = [x.get_degree() for x in L]
        F = FP_Module(tuple(degs), algebra=self.profile_algebra())
        pr = Hom(F,self)(L)
        return pr.image()


    def resolution(self,k,kernels=False,verbose=False):
        """
        Returns a list of length `k`, consisting of chain maps and
        a list of pairs [K_n,i_n] corresponding to the kernels
        and inclusions of the resolution. These
        maps form a resolution of length `k` of `self`.


        INPUT:

        -  ``k``  - An non-negative integer.

        OUTPUT:

        -  ``res``   - A list of surjective homomorphisms [f_i | i = 0 ... k]
                       making a free resolution of length `k`:

                            f_k          f_k-1                 f_1       f_0
                       F_k -----> F_k-1 ------> F_k-2 --> ... ----> F_0 ----> self.

        -  ``kers``  - A list of tuples [(K_i, inj_i) | i = 0 ... k-1] where
                       K_i is an FP_Module, and inj_i is an inclusion into F_i
                       such that:

                       im (inj_i: K_i -> F_i) = ker (f_i) for i = 0 ... k-1.



        EXAMPLES::
            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: N = FP_Module((0,1), ((Sq(2),Sq(1)),))
            sage: res, kers = N.resolution(3, kernels=True, verbose=True)
            Step  3
            Step  2
            Step  1
            Step  0
            sage: len(res)
            4
            sage: len(kers)
            3
            sage: for i, kernel_inj in enumerate(kers):
            ....:     f = res[i]
            ....:     x = kernel_inj.domain().an_element()
            ....:     y = f(kernel_inj(x))
            ....:     if not y.is_zero():
            ....:         raise ValueError, 'The element %s should be in the kernel of:\n%s\n but it maps to %s.' % (x, f, y)
            sage: M = FP_Module((0,1), ((Sq(2),Sq(1)),))
            sage: resolution = M.resolution(3, verbose=True)
            Step  3
            Step  2
            Step  1
            Step  0
            sage: for i, r in enumerate(resolution): print ('f_%d: %s' % (i, r))
            f_0: Module homomorphism of degree 0:
              Domain: Finitely presented module on 2 generators and 0 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [2, 1]
              Codomain: Finitely presented module on 2 generators and 1 relation over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [2, 1]
            defined by sending the generators
              [<1, 0>, <0, 1>]
            to
              [<1, 0>, <0, 1>]
            f_1: Module homomorphism of degree 0:
              Domain: Finitely presented module on 1 generator and 0 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [2, 1]
              Codomain: Finitely presented module on 2 generators and 0 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [2, 1]
            defined by sending the generators
              [<1>]
            to
              [<Sq(2), Sq(1)>]
            f_2: The trivial module homomorphism:
              Domain: Finitely presented module on 0 generators and 0 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [2, 1]
              Codomain: Finitely presented module on 1 generator and 0 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [2, 1]
            f_3: The trivial module homomorphism:
              Domain: Finitely presented module on 0 generators and 0 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [2, 1]
              Codomain: Finitely presented module on 0 generators and 0 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [2, 1]

        """

        kers = [] if kernels else None
        res, kers = self._resolution(k, kers, verbose)
        if kernels == True:
            return res, kers
        else:
            return res

    def _resolution(self,k,kers,verbose=False):
        """
            The private implementation of resolution()
        """

        C0 = FP_Module(tuple(self.degs), algebra=self.profile_algebra())
        eps = Hom(C0,self)(self.gens())

        if verbose:
              print "Step ",k
        if k <= 0:
            return [eps], kers
        else:
            i0 = eps.kernel()
            if not kers is None:
                kers.append(i0)
            r, kz = i0.domain()._resolution(k-1, kers, verbose)
            r[0] = i0*r[0]
            return [eps] + r, kers

