r"""
Homspace of homomorphisms of finitely generated free graded modules

This is the Sage parent instances of
:class:`sage.modules.fp_modules.free_module.FreeModule`.

This class is intended for private use by
:class:`sage.modules.fp_modules.fp_homspace.FP_ModuleHomspace`.

EXAMPLES::

    sage: from sage.modules.fp_modules.free_module import *
    sage: A = SteenrodAlgebra(2)
    sage: M = FreeModule((0,1), A)
    sage: N = FreeModule((2,), A)
    sage: homspace = Hom(M, N)
    sage: values = [Sq(2)*N.generator(0), Sq(2)*Sq(1)*N.generator(0)]
    sage: f = homspace(values); f
    Module homomorphism of degree 4 defined by sending the generators
      [<1, 0>, <0, 1>]
    to
      [<Sq(2)>, <Sq(0,1) + Sq(3)>]

Convenience methods exist for creating the trivial morphism as well as the
identity morphism::

    sage: homspace.zero()
    The trivial homomorphism.
    sage: Hom(M, M).identity()
    The identity homomorphism.

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

AUTHORS:

    - Robert R. Bruner, Michael J. Catanzaro (2012): initial version
    - Koen (date in ISO year-month-day format): Updating to Sage 8.1
    - Sverre A. Lunoee-Nielsen (2020-01-11): Rewritten and refactored, and updated to Sage 8.9.

"""



from __future__ import absolute_import

from inspect import isfunction

import sage.categories.homset
from sage.misc.cachefunc import cached_method
from sage.categories.homset import Homset


def is_FreeModuleHomspace(x):
    r"""
    Check if the given object is of type FreeModuleHomspace.

    OUTPUT:: the boolean ``True`` if and only if ``x`` is of type
    FreeModuleHomspace, and ``False`` otherwise.

    EXAMPLES::

        sage: from sage.modules.fp_modules.free_module import FreeModule
        sage: from sage.modules.fp_modules.free_homspace import is_FreeModuleHomspace
        sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))
        sage: F = FreeModule((1,3), A2)
        sage: L = FreeModule((2,3), A2)
        sage: is_FreeModuleHomspace(Hom(F, L))
        True

    TESTS::

        sage: is_FreeModuleHomspace(0)
        False

    """
    return isinstance(x, FreeModuleHomspace)

from .free_morphism import FreeModuleMorphism


class FreeModuleHomspace(Homset):
    # In the category framework, Elements of the class FP_Module are of the
    # class FP_Element, see
    # http://doc.sagemath.org/html/en/thematic_tutorials/coercion_and_categories.html#implementing-the-category-framework-for-the-elements
    Element = FreeModuleMorphism

    def _element_constructor_(self, values):
        r"""
        Construct any element of this homspace.

        This function is used internally by the ()-operator when creating
        homspace elements.

        INPUT:

        - ``values`` -- A tuple of values (i.e. elements of the
        codomain for this homspace) corresponding bijectively to the generators
        of the domain of this homspace, or the zero integer constant.

        OUTPUT: An instance of the morphism class.  The returned morphism is
        defined by sending the module generators in the domain to the given
        values.
                
        OUTPUT: A module homomorphism in the homspace.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import FreeModule
            sage: from sage.modules.fp_modules.free_homspace import is_FreeModuleHomspace
            sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: F = FreeModule((1,3), A2)
            sage: L = FreeModule((2,5), A2)
            sage: H = Hom(F, L)
            sage: values = (A2.Sq(4)*L.generator(0), A2.Sq(3)*L.generator(1))
            sage: f = H(values); f
            Module homomorphism of degree 5 defined by sending the generators
              [<1, 0>, <0, 1>]
            to
              [<Sq(4), 0>, <0, Sq(3)>]
            sage: H(0)
            The trivial homomorphism.

        """
        if isinstance(values, FreeModuleMorphism):
            return values
        elif values == 0:
            return self.zero()
        else:
            return self.element_class(self, values)


    def _an_element_(self):
        r"""
        Return a morphism belonging to this homspace.

        .. TODO:: At the moment, this function always returns the zero morphism.
        It would be useful if non-trivial morphisms could be produced as well.

        OUTPUT: A morhism in this homspace.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import FreeModule
            sage: from sage.modules.fp_modules.free_homspace import is_FreeModuleHomspace
            sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: F = FreeModule((1,3), A2)
            sage: L = FreeModule((2,3), A2)
            sage: H = Hom(F, L)
            sage: H._an_element_()
            The trivial homomorphism.

        """
        return self.zero()


    @cached_method
    def zero(self):
        r"""
        Return the trivial morphism of this homspace.

        OUTPUT: The morhism taking the zero value for any element in the domain.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import FreeModule
            sage: from sage.modules.fp_modules.free_homspace import is_FreeModuleHomspace
            sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: F = FreeModule((1,3), A2)
            sage: L = FreeModule((2,3), A2)
            sage: H = Hom(F, L)
            sage: H.zero()
            The trivial homomorphism.

        """
        return self.element_class(self, self.codomain().zero())


    def identity(self):
        r"""
        Return the identity morphism of this homspace, if this is an
        endomorphism set.

        OUTPUT: The identity endomorphism.

        TESTS::

            sage: from sage.modules.fp_modules.free_module import FreeModule
            sage: from sage.modules.fp_modules.free_homspace import is_FreeModuleHomspace
            sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: L = FreeModule((2,3), A2)
            sage: H = Hom(L, L)
            sage: H.identity()
            The identity homomorphism.

        TESTS::

            sage: F = FreeModule((1,3), A2)
            sage: H = Hom(F, L)
            sage: H.identity()
            Traceback (most recent call last):
            ...
            TypeError: This homspace does not consist of endomorphisms.

        """
        if self.is_endomorphism_set():
            return self.element_class(self, self.codomain().generators())
        else:
            raise TypeError("This homspace does not consist of endomorphisms.")

