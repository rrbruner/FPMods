r"""
Elements of finitely presented graded modules

This class implements construction and basic manipulation of elements of the
Sage parent :class:`sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module.FP_Module`, which models
finitely presented modules over connected graded algebras.

.. NOTE:: This class is used by the derived class
    :class:`sage.modules.finitely_presented_over_the_steenrod_algebra.fpa_element.FPA_Element`.

AUTHORS:

    - Robert R. Bruner, Michael J. Catanzaro (2012): Initial version.
    - Sverre Lunoee--Nielsen and Koen van Woerden (2019-11-29): Updated the
      original software to Sage version 8.9.
    - Sverre Lunoee--Nielsen (2020-07-01): Refactored the code and added 
      new documentation and tests.

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

from sage.structure.element import ModuleElement as SageModuleElement

from .free_element import FreeModuleElement


class FP_Element(SageModuleElement):

    def __init__(self, module, coefficients):
        r"""
        Create a module element of a finitely presented graded module over
        a connected graded algebra.

        INPUT:

        - ``module`` -- the parent instance of this module element.

        - ``coefficients`` -- a tuple of homogeneous elements of the algebra
          over which the module is defined.

        OUTPUT: The module element given by the coefficients.

        .. NOTE:: Never use this constructor explicitly, but rather the parent's
            call method, or this class' __call__ method.  The reason for this
            is that the dynamic type of the element class changes as a
            consequence of the category system.

        """
        # Store the free representation of the element.
        self.free_element = FreeModuleElement(module.j.codomain(), coefficients)

        SageModuleElement.__init__(self, parent=module)


    def coefficients(self):
        r"""
        The coefficients of this module element.

        OUTPUT: A tuple of elements of the algebra over which this module is
        defined.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
            sage: M = FP_Module([0,1], SteenrodAlgebra(2), [[Sq(4), Sq(3)]])
            sage: x = M.element_from_coordinates((0,0,1), 5)

            sage: x
            <0, Sq(4)>
            sage: x.coefficients()
            (0, Sq(4))

            sage: y = M.element_from_coordinates((0,0,0), 5)
            sage: y
            <0, 0>
            sage: y.coefficients()
            (0, 0)

        """
        return self.free_element.coefficients()


    def degree(self):
        r"""
        The degree of this element.

        OUTPUT: The integer degree of this element, or ``None`` if this is the
        zero element.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
            sage: M = FP_Module([0,1], SteenrodAlgebra(2), [[Sq(4), Sq(3)]])
            sage: x = M.an_element(7)

            sage: x
            <Sq(0,0,1), Sq(3,1)>
            sage: x.degree()
            7
    
            sage: # The zero element has no degree::
            sage: (x-x).degree() is None
            True

        """
        return self.free_element.degree()


    def _repr_(self):
        r"""
        Return a string representation of this element.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
            sage: M = FP_Module([0,1], SteenrodAlgebra(2), [[Sq(4), Sq(3)]])
            sage: [M.an_element(n) for n in range(1,10)]
            [<Sq(1), 1>,
             <Sq(2), Sq(1)>,
             <Sq(0,1), Sq(2)>,
             <Sq(1,1), Sq(3)>,
             <Sq(2,1), Sq(4)>,
             <Sq(0,2), Sq(5)>,
             <Sq(0,0,1), Sq(3,1)>,
             <Sq(1,0,1), Sq(1,2)>,
             <Sq(2,0,1), Sq(2,2)>]

        """
        return self.free_element._repr_()


    def _lmul_(self, a):
        r"""
        Act by left multiplication on this element by ``a``.

        INPUT:

        - ``a`` -- an element of the algebra this module is defined over.

        OUTPUT: the module element `a\cdot x` where `x` is this module element.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
            sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: M = FP_Module([0,3], A2, [[Sq(2)*Sq(4), Sq(3)]])
            sage: A2.Sq(2)*M.generator(1)
            <0, Sq(2)>
            sage: A2.Sq(2)*(A2.Sq(1)*A2.Sq(2)*M.generator(0) + M.generator(1))
            <Sq(2,1), Sq(2)>

        TESTS:

            sage: elements = [M.an_element(n) for n in range(1,10)]
            sage: a = A2.Sq(3)
            sage: [a*x for x in elements]
            [<Sq(1,1), 0>,
             <0, 0>,
             <Sq(3,1), Sq(3)>,
             <0, Sq(1,1)>,
             <0, 0>,
             <Sq(3,2), Sq(3,1)>,
             <Sq(3,0,1), Sq(7)>,
             <Sq(1,1,1), Sq(5,1)>,
             <0, Sq(3,2)>]

        """
        return self.parent()(a*self.free_element)


    def _neg_(self):
        r"""
        Return the additive inverse of this element.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
            sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: M = FP_Module([0], A2)

            sage: x = M.an_element(6);x
            <Sq(0,2)>

            sage: -x
            <Sq(0,2)>

            sage: x + (-x) == 0
            True

        """
        return self.parent()(-self.free_element)


    def _add_(self, other):
        r"""
        Return the module sum of this and the given module element.

        Implementation of this function allows Sage to make sense of the +
        operator for instances of this class.

        INPUT:

        - ``other`` -- another element of this element's module.  Only elements
          of the same degree are allowed to be added together.

        OUTPUT: the module sum of this element and the given element ``other``.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
            sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: M = FP_Module([0], A2)

            sage: x = M.an_element(6);x
            <Sq(0,2)>

            sage: -x
            <Sq(0,2)>

            sage: x + (-x) == 0
            True

        TESTS::

            sage: x = M.an_element(4)
            sage: y = M.an_element(5)
            sage: x+y
            Traceback (most recent call last):
            ...
            ValueError: Can't add element of degree 4 and 5
            sage: z = M.zero()
            sage: x+z == x
            True
            sage: z+x
            <Sq(1,1)>
            sage: y+z
            <Sq(2,1)>

        """
        return self.parent()(self.free_element + other.free_element)


    def _cmp_(self, other):
        r"""
        Compare this element with ``other``.

        Implementation of this function allows Sage to make sense of the ==
        operator for instances of this class.

        INPUT:

        - ``other`` -- an instance of this class.

        OUTPUT: The integer 0 if the this element equals ``other``, i.e. that
        the element ``other`` is the additive inverse of this element.
        Otherwise, the output is the integer 1.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
            sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: M = FP_Module((0,1), A2)
            sage: x = M([Sq(1), 1]); x
            <Sq(1), 1>
            sage: y = M([0, Sq(1)]); y
            <0, Sq(1)>

        Multiplying by Sq(1) takes x to the element y::

            sage: A2.Sq(1)*x == y
            True

        TESTS::

            sage: N = FP_Module([0], A2)
            sage: x._cmp_(M.an_element(4))  # Elements of different degrees aren't equal
            1
            sage: w = N.an_element(1)
            sage: x._cmp_(w) # Elements of different modules aren't equal.
            1
            sage: z = M.zero()
            sage: x._cmp_(z) # Compare the non-trivial x to the zero element.
            1
            sage: z._cmp_(z) # Compare the zero element to itself.
            0

        """

        if self.parent() != other.parent():
            return 1
        elif self.degree() != other.degree() and self.degree() != None and other.degree() != None:
            return 1
        return 1 if (self._add_(other._neg_()))._nonzero_() else 0


    def vector_presentation(self):
        r"""
        A coordinate vector representing this module element.

        These are coordinates with respect to the basis chosen by
        :meth:`sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module.FP_Module.basis_elements`.

        OUTPUT: a vector of elements in the ground field of the algebra for
        this module.

        .. SEEALSO::

            :meth:`sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module.FP_Module.vector_presentation`
            :meth:`sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module.FP_Module.basis_elements`
            :meth:`sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module.FP_Module.element_from_coordinates`

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
            sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: M = FP_Module((0,1), A2)

            sage: x = M.an_element(7)
            sage: v = x.vector_presentation(); v
            (1, 0, 0, 0, 0, 1, 0)
            sage: type(v)
            <type 'sage.modules.vector_mod2_dense.Vector_mod2_dense'>

            sage: V = M.vector_presentation(7)
            sage: v in V
            True

            sage: M.element_from_coordinates(v, 7) == x
            True

        We can use the basis for the module elements in the degree of `x`,
        together with the coefficients `v` to recreate the element `x`::

            sage: basis = M.basis_elements(7)
            sage: x_ = sum( [c*b for (c,b) in zip(v, basis)] ); x_
            <Sq(0,0,1), Sq(3,1)>
            sage: x == x_
            True

        TESTS::

            sage: M.zero().vector_presentation() is None
            True

        """
        if self.degree() == None:
            return None

        v = self.free_element.vector_presentation()
        M_n = self.parent().vector_presentation(self.degree())
        # assert(v in M_n.V())

        return M_n.quotient_map()(v)


    def _nonzero_(self):
        r"""
        Determine if this element is non-zero.

        OUTPUT: The boolean value ``True`` if this element is non-zero, and ``False`` 
        otherwise.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
            sage: M = FP_Module([0,2,4], SteenrodAlgebra(2), [[Sq(4),Sq(2),0]])
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
        if self.degree() == None:
            return False

        return self.vector_presentation() != 0


    def normalize(self):
        r"""
        A normalized form of ``self``.

        OUTPUT: An instance of this element class representing the same
        module element as this element.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
            sage: M = FP_Module([0,2,4], SteenrodAlgebra(2), [[Sq(4),Sq(2),0]])

            sage: m = M((Sq(6), 0, Sq(2))); m
            <Sq(6), 0, Sq(2)>
            sage: m.normalize()
            <Sq(6), 0, Sq(2)>
            sage: m == m.normalize()
            True

            sage: n = M((Sq(4), Sq(2), 0)); n
            <Sq(4), Sq(2), 0>
            sage: n.normalize()
            <0, 0, 0>
            sage: n == n.normalize()
            True

        """
        if self.degree() == None:
            return self

        v = self.vector_presentation()
        return self.parent().element_from_coordinates(v, self.degree())


    def __hash__(self):
        r"""
        A hash value representing this element.

        """
        return hash(self.coefficients())

