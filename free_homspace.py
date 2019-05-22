from __future__ import absolute_import

from inspect import isfunction

import sage.categories.homset
from sage.misc.cachefunc import cached_method
from sage.categories.homset import Homset



r"""
TESTS::

    sage: from sage.modules.fp_modules.free_module import FreeModule
    sage: from sage.misc.sage_unittest import TestSuite
    sage: A = SteenrodAlgebra(2)
    sage: F1 = FreeModule((1,3), A);
    sage: F2 = FreeModule((2,3), A);
    sage: homset = Hom(F1, F2); homset
    Set of Morphisms from Finitely presented free module on 2 generators ...
    sage: homset([F2((Sq(1), 1)), F2((0, Sq(2)))])
    Module homomorphism of degree 2 defined by sending the generators
      [<1, 0>, <0, 1>]
    to
      [<Sq(1), 1>, <0, Sq(2)>]
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

def is_FreeModuleHomspace(x):
    r"""
    """
    return isinstance(x, FreeModuleHomspace)

from .free_morphism import FreeModuleMorphism


class FreeModuleHomspace(Homset):
    # In the category framework, Elements of the class FP_Module are of the
    # class FP_Element, see
    # http://doc.sagemath.org/html/en/thematic_tutorials/coercion_and_categories.html#implementing-the-category-framework-for-the-elements
    Element = FreeModuleMorphism

    def _element_constructor_(self, values):
        """
        INPUT:

        - An iterable of FP_FreeElement's of the codomain which equals the values
          of the module generators of the domain.

        OUTPUT: A module homomorphism in the homspace.

        EXAMPLES::

        """
        if isinstance(values, FreeModuleMorphism):
            return values
        elif values == 0:
            return self.zero()
        else:
            return self.element_class(self, values)

    def _an_element_(self):
        """
        """
        return self.zero()

    @cached_method
    def zero(self):
        """
        """
        return self.element_class(self, self.codomain().zero())

    def identity(self):
        r"""
        Return identity morphism in an endomorphism ring.
        """
        if self.is_endomorphism_set():
            return self.element_class(self, self.codomain().generators())
        else:
            raise TypeError("This homspace does not consist of endomorphisms. Try natural_map() instead.")

