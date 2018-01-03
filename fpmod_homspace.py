from __future__ import absolute_import

import sage.categories.homset
from inspect import isfunction
from sage.misc.cachefunc import cached_method


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

