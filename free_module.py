r"""
Finitely presented free modules.

EXAMPLES::

<Lots and lots of examples>

AUTHORS:

    - Robert R. Bruner, Michael J. Catanzaro (2012): initial version
    - Koen (date in ISO year-month-day format): Updating to Sage 8.1
    - Sverre (date in ISO 2018-month-day format): Updating to Sage 8.1
    - Sverre (date in ISO 2019-month-day format): Rewrite and refactor.

"""

#*****************************************************************************
#       Copyright (C) 2011 Robert R. Bruner <rrb@math.wayne.edu>
#             and          Michael J. Catanzaro <mike@math.wayne.edu>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

#  http://doc.sagemath.org/html/en/developer/coding_basics.html#files-and-directory-structure


from sage.misc.cachefunc import cached_method
from sage.modules.free_module import VectorSpace
from sage.modules.module import Module as SageModule
from sage.rings.infinity import PlusInfinity
from sage.structure.unique_representation import UniqueRepresentation

from .free_homspace import FreeModuleHomspace
from .free_element import FreeModuleElement


class FreeModule(UniqueRepresentation, SageModule):
    """
    """

    # In the category framework, Elements of the class FP_Module are of the
    # class FP_Element, see
    # http://doc.sagemath.org/html/en/thematic_tutorials/coercion_and_categories.html#implementing-the-category-framework-for-the-elements
    Element = FreeModuleElement

    def __init__(self, generator_degrees, algebra):
        r"""
        INPUT:

        - ``generator_degrees`` -- A tuple of non-decreasing integers defining the number of
          generators of the module, and their degrees.
        - ``algebra`` -- The algebra over which the module is defined.

        OUTPUT: The finitely presented module with presentation given by
        ``generators``.

        TESTS::
        """
        self._generator_degrees = generator_degrees
        if None in generator_degrees:
            raise ValueError, ("generators are not all integers: %s" % str(generator_degrees))

        if not algebra.base_ring().is_field():
            raise NotImplementedError('The algebra must be over a field.')
        
        # Call the base class constructor.
        SageModule.__init__(self, algebra)

        self._populate_coercion_lists_()

        self.ModuleClass = FreeModule


    def generator_degrees(self):
        return self._generator_degrees

    def is_trivial(self):
        return len(self._generator_degrees) == 0

    def connectivity(self):
        """
        The connectivity of the module.

        EXAMPLES::

        """
        return min(self._generator_degrees + (PlusInfinity(),))

    def _element_constructor_(self, x):
        """
        Construct any element of the module.

        INPUT:
        - ``x`` -- A tuple of coefficients, an element of FreeModule, or the
          zero integer constant.

        OUTPUT: An instance of the element class with coefficients from ``x``,
        the element ``x`` if it already was an element, or the zero element.

        EXAMPLES::

        """

        if isinstance(x, self.element_class):
            return x
        elif x == 0:
            return self.element_class(self, len(self._generator_degrees)*(0,))
        else:
            return self.element_class(self, x)

    def an_element(self, degree=None):
        r"""
        Return an element of the module.

        This function chooses deterministically an element of the module in the
        given degree.

        INPUT:

        - ``degree`` --  The degree of the element to construct.  If the default
          value ``None`` is given, a degree will be chosen by the function.

        OUTPUT:

        -  ``e`` -- An element of the given degree.

        EXAMPLES::

        """

        if len(self._generator_degrees) == 0:
            return self.element_class(self, [])

        if degree == None:
            degree = max(self._generator_degrees) + 7

        coefficients = []

        for g in self._generator_degrees:
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
        Construct a string representation of the module.

        EXAMPLES::

        """
        return "Finitely presented free module on %s generator%s over %s"\
            %(len(self._generator_degrees), "" if len(self._generator_degrees) == 1 else "s",
              self.base_ring())

    @cached_method
    def basis_elements(self, n):
        """
        Return a basis for the vectorspace of degree ``n`` module elements.
        """
        basis_n = []
        for i, generator_degree in enumerate(self._generator_degrees):
            l = n - generator_degree
            basis_n += [a*self.generator(i) for a in self.base_ring().basis(l)]

        return basis_n

    @cached_method
    def element_from_coordinates(self, coordinates, n):
        r"""
        """
        basis_elements = self.basis_elements(n)

        if len(coordinates) != len(basis_elements):
            raise ValueError, 'Incorrect coordinate vector size: %s. | Should have length %d.'\
                % (len(coordinates), len(basis_elements))

        return sum([c*element for c, element in zip(coordinates, basis_elements)])

    @cached_method
    def vector_presentation(self, n):
        """
        Return the vectorspace ``k^{\times r}`` of dimension ``r = dim(M_n)``
        where ``M_n`` is the vectorspace of degree ``n`` module elements.

        The isomorphism between this vectorspace and ``M_n`` is given by
        the bijection taking the standard basis element ``e_i`` to the ``i``-th
        element of the array returned by `self.basis(n)`.
        """
        return VectorSpace(self.base_ring().base_ring(), len(self.basis_elements(n)))

    @cached_method
    def generator(self, index):
        r"""
        Return the module generator (as an module element) with the given
        index.

        EXAMPLES::

        """
        if index < 0 or index >= len(self._generator_degrees):
            raise ValueError, 'The parent module has generators in the index '\
                'range [0, %s]; generator %s does not exist' %\
                (len(self._generator_degrees) - 1, index)

        return self.element_class(self, index)

    def generators(self):
        r"""

        Return all module generators (as an module elements).

        EXAMPLES::

        """
        return [self.generator(i) for i in range(len(self._generator_degrees))]

    def _Hom_(self, Y, category):
        r"""
        The internal hook used by the free function
        sage.categories.homset.hom.Hom() to create homsets involving this
        parent.

        TESTS::

        """
        return FreeModuleHomspace(self, Y, category)

    def suspension(self, t):
        r"""
        Suspend the module by the given degree.

        INPUT:

        - ``t`` -- An integer by which the module is suspended.

        OUTPUT:

        - ``C`` -- A a module which is identical to this module by a shift
          of degrees by the integer ``t``.

        EXAMPLES::

        """
        return self.ModuleClass(generator_degrees=tuple([g + t for g in self._generator_degrees]), algebra=self.base_ring())

