from __future__ import absolute_import

import sage.categories.homset
from inspect import isfunction
from sage.misc.cachefunc import cached_method


r"""
TESTS::

    sage: from sage.modules.fp_modules.fp_module import FP_Module
    sage: from sage.misc.sage_unittest import TestSuite
    sage: A = SteenrodAlgebra(2, profile=(3,2,1))
    sage: F = FP_Module([1,3], A)
    sage: L = FP_Module([2,3], A, [[Sq(2),Sq(1)], [0,Sq(2)]])
    sage: homset = Hom(F, L); homset
    Set of Morphisms from Finitely presented module on 2 generators ...
    sage: homset.an_element()
    The trivial module homomorphism.
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

def is_FP_ModuleHomspace(x):
    r"""
    """
    return isinstance(x, FP_ModuleHomspace)

from .fp_morphism import FP_ModuleMorphism

from sage.categories.homset import Homset


class FP_ModuleHomspace(Homset):
    # In the category framework, Elements of the class FP_ModuleHomspace are of the
    # class FP_ModuleMorphism, see
    # http://doc.sagemath.org/html/en/thematic_tutorials/coercion_and_categories.html#implementing-the-category-framework-for-the-elements
    Element = FP_ModuleMorphism

    def _element_constructor_(self, values):
        """
        INPUT:

        - An iterable of FP_Element's of the codomain which equals the values
          of the module generators of the domain.

        OUTPUT: A module homomorphism in the homspace.

        EXAMPLES::

        """
        if isinstance(values, self.element_class):
            return values
        elif values == 0:
            return self.zero()
        else:
            return self.element_class(self, values)

    def _an_element_(self):
        """
        """
        return self.zero()

    def zero(self):
        """
        Create the zero homomorphism.
        """
        return self.element_class(self, [self.codomain().zero() for g in self.domain().generator_degrees()])

    def identity(self):
        r"""
        Create the identity homomorphism.  If this hom set is not an endomorphism
        set, a type error is raised.
        """
        if self.is_endomorphism_set():
            return self.element_class(self, self.codomain().generators())
        else:
            raise TypeError("This homspace does not consist of endomorphisms. Try natural_map() instead.")

