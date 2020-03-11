r"""
The set of homomorphisms between finitely presented graded modules

EXAMPLES:

Users will typically use this class indirectly through the free function
``Hom``::

    sage: from sage.modules.fp_modules.fp_module import FP_Module
    sage: from sage.misc.sage_unittest import TestSuite
    sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))
    sage: F = FP_Module([1,3], A2)
    sage: L = FP_Module([2,3], A2, [[Sq(2),Sq(1)], [0,Sq(2)]])
    sage: homset = Hom(F, L)

Elements of the homset are homomorphisms `F\rightarrow L`.  To construct a
homomorphism, a list of values in the codomain module must be given,
each value corresponding to a module generator of the domain module::

    sage: homset.domain()
    Finitely presented module on 2 generators and 0 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [3, 2, 1]
    sage: homset.codomain()
    Finitely presented module on 2 generators and 2 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [3, 2, 1]
    sage: v0 = L([Sq(1), 1])
    sage: v1 = L([0, Sq(2)])
    sage: f = homset([v0, v1]); f
      Module homomorphism of degree 2 defined by sending the generators
        [<1, 0>, <0, 1>]
      to
        [<Sq(1), 1>, <0, Sq(2)>]

The trivial homomorphism sending all generators to the zero element in the
codomain can be constructed by a special API call::

    sage: z = homset.zero(); z
    The trivial homomorphism.
    sage: z(F.generator(0))
    <0, 0>
    sage: z(F.generator(1))
    <0, 0>

When the domain and codomain of the homset are the same module, the homset
consists of endomorphisms and which always contain the identity map::

    sage: id = Hom(L, L).identity(); id
    The identity homomorphism.
    sage: e = L.an_element(5); e
    <Sq(0,1), Sq(2)>
    sage: id(e) == e
    True

TESTS::

    sage: from sage.modules.fp_modules.fp_module import FP_Module
    sage: from sage.misc.sage_unittest import TestSuite
    sage: A = SteenrodAlgebra(2, profile=(3,2,1))
    sage: F = FP_Module([1,3], A)
    sage: L = FP_Module([2,3], A, [[Sq(2),Sq(1)], [0,Sq(2)]])
    sage: homset = Hom(F, L); homset
    Set of Morphisms from Finitely presented module on 2 generators ...
    sage: homset.an_element()
    The trivial homomorphism.
    sage: homset([L((Sq(1), 1)), L((0, Sq(2)))])
    Module homomorphism of degree 2 defined by sending the generators
      [<1, 0>, <0, 1>]
    to
      [<Sq(1), 1>, <0, Sq(2)>]
    sage: Hom(F, L) ([L((Sq(1), 1)), L((0, Sq(2)))]).kernel()
    Module homomorphism of degree 0 defined by sending the generators
      [<1, 0>, <0, 1>]
    to
      (<0, 1>, <Sq(0,1), 0>)
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

"""

#*****************************************************************************
#       Copyright (C) 2011 Robert R. Bruner <rrb@math.wayne.edu> and
#                          Michael J. Catanzaro <mike@math.wayne.edu>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from __future__ import absolute_import

from inspect import isfunction

from sage.categories.homset import Homset
from sage.misc.cachefunc import cached_method

import sage.categories.homset


def is_FP_ModuleHomspace(x):
    r"""
    Check if the given object is of type FP_ModuleHomspace.

    OUTPUT:: a boolean which is True if ``x`` is of type FP_ModuleHomspace.

    EXAMPLES::

        sage: from sage.modules.fp_modules.fp_module import FP_Module
        sage: from sage.modules.fp_modules.fp_homspace import is_FP_ModuleHomspace
        sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))
        sage: F = FP_Module([1,3], A2)
        sage: L = FP_Module([2,3], A2, [[Sq(2),Sq(1)], [0,Sq(2)]])
        sage: is_FP_ModuleHomspace(Hom(F, L))
        True
        sage: is_FP_ModuleHomspace(0)
        False

    """
    return isinstance(x, FP_ModuleHomspace)


class FP_ModuleHomspace(Homset):
    # FP_ModuleMorphism contains reference to is_FP_ModuleHomspace, so this import
    # statement must not appear before that function.
    from .fp_morphism import FP_ModuleMorphism

    # In the category framework, Elements of the class FP_ModuleHomspace are of the
    # class FP_ModuleMorphism, see
    # http://doc.sagemath.org/html/en/thematic_tutorials/coercion_and_categories.html#implementing-the-category-framework-for-the-elements
    Element = FP_ModuleMorphism

    def _element_constructor_(self, values):
        r"""
        Constructs a morphism contained in this homset.

        This function is not part of the public API, but is used by :meth:Hom
        method to create morphisms.

        INPUT:

        - ``values`` -- an iterable of FP_Elements of the codomain of this homset which
          equals the values of the module generators of the domain.

        OUTPUT: A module homomorphism in this homspace sending the generators
        of the domain module to the corresponding values of the input argument.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import FP_Module
            sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: F = FP_Module([1,3], A2)
            sage: L = FP_Module([2,3], A2, [[Sq(2),Sq(1)], [0,Sq(2)]])

            sage: homset = Hom(F, L)
            sage: v1 = L([Sq(1), 1])
            sage: v2 = L([0, Sq(2)])
            sage: f = homset._element_constructor_([v1, v2]);f
              Module homomorphism of degree 2 defined by sending the generators
                [<1, 0>, <0, 1>]
              to
                [<Sq(1), 1>, <0, Sq(2)>]

        One can construct a homomorphism from another homomorhism::

            sage: g = homset._element_constructor_(f)
            sage: f == g
            True

        And there is a convenient way of making the trivial homomorphism::

            sage: z = homset._element_constructor_(0); z
            The trivial homomorphism.

        """
        if isinstance(values, self.element_class):
            return values
        elif values == 0:
            return self.zero()
        else:
            return self.element_class(self, values)


    def _an_element_(self):
        r"""
        Create a morphism in this homset.

        This function simply returns the zero homomorphism, which always
        exists in the homset.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import FP_Module
            sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: F = FP_Module([1,3], A2)
            sage: L = FP_Module([2,3], A2, [[Sq(2),Sq(1)], [0,Sq(2)]])
            sage: z = Hom(F, L)._an_element_(); z
            The trivial homomorphism.

        """
        return self.zero()


    def zero(self):
        r"""
        Create the trivial homomorphism in this homset.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import FP_Module
            sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: F = FP_Module([1,3], A2)
            sage: L = FP_Module([2,3], A2, [[Sq(2),Sq(1)], [0,Sq(2)]])
            sage: z = Hom(F, L).zero(); z
            The trivial homomorphism.
            sage: z(F.an_element(5))
            <0, 0>
            sage: z(F.an_element(23))
            <0, 0>

        """
        return self.element_class(self, [self.codomain().zero() for g in self.domain().generator_degrees()])


    def identity(self):
        r"""
        Create the identity homomorphism.

        If this homset is not an endomorphism set, a type error is raised.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import FP_Module
            sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: L = FP_Module([2,3], A2, [[Sq(2),Sq(1)], [0,Sq(2)]])
            sage: id = Hom(L, L).identity(); id
            The identity homomorphism.
            sage: e = L.an_element(5)
            sage: e == id(e)
            True

        It is an error to call this function when the homset is not an
        set of endomorphisms::

            sage: F = FP_Module([1,3], A2)
            sage: Hom(F,L).identity()
            Traceback (most recent call last):
            ...
            TypeError: This homspace does not consist of endomorphisms.

        """
        if self.is_endomorphism_set():
            return self.element_class(self, self.codomain().generators())
        else:
            raise TypeError("This homspace does not consist of endomorphisms.")

