r"""
Elements finitely generated free graded modules

This class implements construction and basic manipulation of homogeneous 
elements of the finitely generated graded free modules, modelled by the Sage 
parent :class:`sage.modules.fp_modules.free_module.FreeModule`.

Let `\{g_i\}_i` be the finite set of generators for the parent module class,
and let `\{a_i\}_i` be a set of elements of the base algebra of
that module, having degrees `\deg(a_i) + \deg(g_i) = n` for some `n\in \ZZ`.

Then an instance of this class created using the `a_i`'s
represents the module element of degree `n` given by

.. MATH::

    \sum_i a_i\cdot g_i\,.

The ordered set `\{a_i\}` is referred to as the coefficients of the module
element.

This class is intended for private use by the class 
sage.modules.fp_modules.fp_module modelling finitely presented modules over
graded algeras.

The module generators are examples of instances of the element class::

    sage: from sage.modules.fp_modules.free_module import *
    sage: A = SteenrodAlgebra(2)
    sage: M = FreeModule((0,1), A)
    sage: gens = M.generators(); gens
    [<1, 0>, <0, 1>]
    sage: type(gens[0])
    <class 'sage.modules.fp_modules.free_module.FreeModule_with_category.element_class'>

The module action produces new elements::

    sage: Sq(2)*gens[0]
    <Sq(2), 0>
    sage: Sq(1,2)*gens[0] + Sq(6)*gens[1]
    <Sq(1,2), Sq(6)>

The parent class also has methods for producing elements::

    sage: y = M([Sq(5), Sq(1,1)]); y
    <Sq(5), Sq(1,1)>

    sage: x = M.element_from_coordinates((0,1,1,0), 5); x
    <Sq(5), Sq(1,1)>

Comparison of elements::

    sage: x == y
    True

Each non-zero element has a degree::

    sage: x.degree()
    5
    sage: z = M.zero(); z
    <0, 0>
    sage: z.degree() is None
    True

Elements can be added as long as they are in the same degree::

    sage: x + z == x
    True
    sage: x - x
    <0, 0>
    sage: x + M.element_from_coordinates((1,1), 1)
    Traceback (most recent call last):
    ...
    ValueError: Can't add element of degree 5 and 1

New elements can also be constructed using the left action of the algebra::

    sage: Sq(3)*x
    <Sq(5,1), 0>

Given an element in degree `n`, it can be given as a vector in the vectorspace of all elements of degree `n`::

    sage: V = M.vector_presentation(5); V
    Vector space of dimension 4 over Finite Field of size 2
    sage: v = x.vector_presentation(); v
    (0, 1, 1, 0)
    sage: v in V
    True

AUTHORS:

    - Robert R. Bruner and Michael J. Catanzaro (2005): initial version
    - Koen (date in ISO year-month-day format): Updating to Sage 8.1
    - Sverre A. Lunoee-Nielsen (2020-01-11): Rewritten and refactored, and updated to Sage 8.9.

"""

#*****************************************************************************
#       Copyright (C) 2019 Robert R. Bruner <rrb@math.wayne.edu>
#                     and  Michael J. Catanzaro <mike@math.wayne.edu>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from sage.misc.cachefunc import cached_method
from sage.rings.integer import Integer
from sage.structure.element import ModuleElement as SageModuleElement


class FreeModuleElement(SageModuleElement):

    def __init__(self, module, coefficients):
        r"""
        Create a module element of a finitely generated free graded module over
        a graded algebra.

        INPUT:

        - ``module`` -- the parent instance of this module element.

        - ``coefficients`` -- a tuple of homogeneous elements of the algebra
          over which the module is defined, or an integer index.

        OUTPUT: The module element given by the coefficients.  Otherwise, if
        ``coefficients`` is an integer index, then the Kroenecker delta 
        function with respect to that index is used as coefficients.

        .. NOTE:: This constructor should not be used explicitly, instead use
              the parent's call method.  The reason for this is that the
              dynamic type of the element class changes as a consequence of the
              category system.

        """
        if isinstance(coefficients, FreeModuleElement):
            self._coefficients = coefficients._coefficients
        elif isinstance(coefficients, Integer) or isinstance(coefficients, int):
            # Kroenecker delta if a single index is given.
            Kroenecker = lambda i: 1 if i == coefficients else 0
            self._coefficients = tuple([module.base_ring()(
                Kroenecker(i)) for i in range(len(module.generator_degrees()))])
        else:
            self._coefficients = tuple([module.base_ring()(x) for x in coefficients])

        if len(self._coefficients) != len(module.generator_degrees()):
            raise ValueError('The number of coefficients must match the number of module generators: %d.'\
                             % len(module.generator_degrees()))

        # Check homogenity and store the degree of the element.
        self._degree = None
        for g, c in zip(module.generator_degrees(), self._coefficients):
            if not c.is_zero():
                d = g + c.degree()

                # XXX todo: Measure how much time is spent in this loop.  Since
                #           construction of free module elements is done
                #           frequently e.g. when computing resolutions, we could
                #           potentially speed things up by dropping this
                #           test.  Since this class constructor is for internal
                #           use only, this is justified:
                # self._degree = d
                # break

                if self._degree == None:
                    self._degree = d
                else:
                    if self._degree != d:
                        raise ValueError('Non-homogeneous element defined.')

        SageModuleElement.__init__(self, parent=module)


    def coefficients(self):
        r"""
        The coefficients of this module element.

        OUTPUT: A tuple of elements of the algebra over which this module is
        defined.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FreeModule((0,1), A)
            sage: x = M.element_from_coordinates((0,0,0,1), 5); x
            <0, Sq(4)>
            sage: x.coefficients()
            (0, Sq(4))
            sage: y = M.element_from_coordinates((0,0,0,0), 5); y
            <0, 0>
            sage: y.coefficients()
            (0, 0)

        """
        return self._coefficients


    def degree(self):
        r"""
        The degree of this element.

        OUTPUT: the integer degree of this element, or None if this is the zero
        element.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FreeModule((0,1), A)
            sage: x = M.an_element(7); x
            <Sq(0,0,1), Sq(3,1)>
            sage: x.degree()
            7

        The zero element has no degree::

            sage: (x-x).degree() is None
            True

        """
        return self._degree


    def _repr_(self):
        r"""
        Return a string representation of this element.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FreeModule((0,1), A)
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
        return '<%s>' % ', '.join(['%s' % c for c in self._coefficients])


    def _lmul_(self, a):
        r"""
        Act by left multiplication on this element by ``a``.

        INPUT:

        - ``a`` -- an element of the algebra this module is defined over.

        OUTPUT: the module element `a\cdot x` where `x` is this module element.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: M = FreeModule((0,0,3), A2)
            sage: A2.Sq(2)*M.generator(1)
            <0, Sq(2), 0>
            sage: A2.Sq(2)*(A2.Sq(1)*A2.Sq(2)*M.generator(1) + M.generator(2))
            <0, Sq(2,1), Sq(2)>

        TESTS::

            sage: elements = [M.an_element(n) for n in range(1,10)]
            sage: a = A2.Sq(3)
            sage: [a*x for x in elements]
            [<Sq(1,1), Sq(1,1), 0>,
             <0, 0, 0>,
             <Sq(3,1), Sq(3,1), Sq(3)>,
             <0, 0, Sq(1,1)>,
             <0, 0, 0>,
             <Sq(3,2), Sq(3,2), Sq(3,1)>,
             <Sq(3,0,1), Sq(3,0,1), Sq(7)>,
             <Sq(1,1,1), Sq(1,1,1), Sq(5,1)>,
             <0, 0, Sq(3,2)>]

        """

        return self.parent()((a*c for c in self._coefficients))


    def _neg_(self):
        r"""
        Return the additive inverse of this element.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: M = FreeModule((0,), A2)
            sage: x = M.an_element(6);x
            <Sq(0,2)>
            sage: -x
            <Sq(0,2)>
            sage: x + (-x) == 0
            True

        """
        return self.parent()([-c for c in self._coefficients])


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

            sage: from sage.modules.fp_modules.free_module import *
            sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: M = FreeModule((0,), A2)
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

        if self.parent() != other.parent():
            raise TypeError("Can't add element in different modules")
        elif self._degree == None: # if self = 0, degree is None
            return self.parent()(other.coefficients())
        elif other._degree == None:   # if other = 0, degree is None
            return self.parent()(self._coefficients)
        elif self._degree != other._degree:
            raise ValueError("Can't add element of degree %s and %s"\
                  %(self._degree, other._degree))
        else:
            return self.parent()(
                [x + y for x,y in zip(self._coefficients, other.coefficients())])


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

            sage: from sage.modules.fp_modules.free_module import *
            sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: M = FreeModule((0,1), A2)
            sage: x = M([Sq(1), 1]); x
            <Sq(1), 1>
            sage: y = M([0, Sq(1)]);y
            <0, Sq(1)>

        Multiplying by Sq(1) takes x to the element y::

            sage: A2.Sq(1)*x == y
            True

        TESTS::

            sage: N = FreeModule((0,), A2)
            sage: x._cmp_(M.an_element(4))  # Elements of different degrees aren't equal
            1
            sage: w = N.an_element(1)
            sage: x._cmp_(w) # ELements of different modules aren't equal.
            1
            sage: z = M.zero()
            sage: x._cmp_(z) # Compare the non-trivial x to the zero element.
            1
            sage: z._cmp_(z) # Compare the zero element to itself.
            0

        """
        if self.parent() != other.parent():
            return 1
        elif self._degree != other._degree and self._degree != None and other._degree != None:
            return 1
        return 1 if (self._add_(other._neg_()))._nonzero_() else 0


    @cached_method
    def vector_presentation(self):
        r"""
        A coordinate vector representing this module element.

        These are coordinates with respect to the basis chosen by
        :func:`sage.modules.fp_modules.free_module.basis_elements`.

        OUTPUT: a vector of elements in the ground field of the algebra for
        this module.

        .. SEEALSO::

            :func:`sage.modules.fp_modules.free_module.vector_presentation`
            :func:`sage.modules.fp_modules.free_module.basis_elements`
            :func:`sage.modules.fp_modules.free_module.element_from_coordinates`

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: M = FreeModule((0,1), A2)
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

            sage: M.zero().vector_presentation()
            0

        """        

        n = self._degree
        if n == None:
             return 0

        bas_gen = self.parent().basis_elements(self._degree)
        base_vec = self.parent().vector_presentation(self._degree)

        base_dict = dict(zip(bas_gen, base_vec.basis()))

        # Create a sparse representation of the element.
        sparse_coeffs = [x for x in enumerate(self._coefficients) if not x[1].is_zero()]

        vector = base_vec.zero()
        for summand_index, algebra_element in sparse_coeffs:
            for scalar_coefficient, monomial in zip(algebra_element.coefficients(), algebra_element.monomials()):
                vector += scalar_coefficient*base_dict[monomial*FreeModuleElement(self.parent(), summand_index)]

        return vector


    def _nonzero_(self):
        r"""
        Determine if this element is non-zero.

        OUTPUT: the boolean value True if this element is non-zero, and False
        otherwise.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: M = FreeModule((0,1), A2)
            sage: y = M.an_element(12);y
            <Sq(2,1,1), Sq(4,0,1)>
            sage: y._nonzero_()
            True
            sage: x = M([0, Sq(1)])
            sage: x._nonzero_()
            True
            sage: (A2.Sq(1)*x)._nonzero_()
            False

        """

        if self._degree == None:
            return False

        return not all(c == 0 for c in self._coefficients)


    def __hash__(self):
        r"""
        A hash value representing this element.

        TESTS::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: M = FreeModule((0,1), A2)
            sage: M.an_element(127).__hash__()
            6795291966596493067

        """
        return hash(self._coefficients)

