from __future__ import absolute_import

import sage.categories.homset
from inspect import isfunction
from sage.misc.cachefunc import cached_method


r"""
TESTS::

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

"""

def is_FP_ModuleHomspace(x):
    r"""
    """
    return isinstance(x, FP_ModuleHomspace)

from sage.modules.fpmods.fpmod_morphism import FP_ModuleMorphism

from sage.categories.homset import Homset

class FP_ModuleHomspace(Homset):
    # In the category framework, Elements of the class FP_Module are of the
    # class FP_Element, see
    # http://doc.sagemath.org/html/en/thematic_tutorials/coercion_and_categories.html#implementing-the-category-framework-for-the-elements
    Element = FP_ModuleMorphism

    def _element_constructor_(self, values):
        """
        INPUT:

        - An iterable of FP_Element's of the codomain which equals the values
          of the module generators of the domain.

        OUTPUT: An FP_ModuleMorphism between fp modules.

        EXAMPLES::

        """
        if isinstance(values, FP_ModuleMorphism):
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
            return self.element_class(self, self.codomain().gens())
        else:
            raise TypeError("Identity map only defined for endomorphisms. Try natural_map() instead.")

