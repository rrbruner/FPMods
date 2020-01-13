r"""
Finitely generated free graded modules

This class implements methods for construction and basic manipulation of
finitely generated free graded modules over a graded algebra.

This class is intended for private use by the class 
:class:`sage.modules.fp_modules.fp_module` modelling finitely presented modules
over graded algeras.

EXAMPLES:

Create a module over the Steenrod algebra with two generators in degrees
0 and 1, respectively::

    sage: from sage.modules.fp_modules.free_module import *
    sage: A = SteenrodAlgebra(2)
    sage: M = FreeModule(generator_degrees=(0,1), algebra=A); M
    Finitely presented free module on 2 generators over mod 2 Steenrod algebra, milnor basis

The module generators are examples of instances of this element class::

    sage: gens = M.generators(); gens
    [<1, 0>, <0, 1>]
    sage: type(gens[0])
    <class 'sage.modules.fp_modules.free_module.FreeModule_with_category.element_class'>

Creating elements::

    sage: y = M([Sq(5), Sq(1,1)]); y
    <Sq(5), Sq(1,1)>

    sage: x = M.element_from_coordinates((0,1,1,0), 5); x
    <Sq(5), Sq(1,1)>

Comparison of elements::

    sage: x == y
    True

Instances of the element class represent homogeneous elements with a given degree::

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
    sage: Sq(2)*gens[0]
    <Sq(2), 0>
    sage: Sq(1,2)*gens[0] + Sq(6)*gens[1]
    <Sq(1,2), Sq(6)>

For any integer `n`, the set of module elements of degree `n` is a vectorspace
over the ground field `\mathcal{k}` of the module algebra.  The function
:math:`basis_elements` provides a basis for this vectorspace::

    sage: M.basis_elements(5)
    [<Sq(2,1), 0>, <Sq(5), 0>, <0, Sq(1,1)>, <0, Sq(4)>]

Using this basis, the vectorspace of degree `n` module elements can be
presented::

    sage: V = M.vector_presentation(5); V
    Vector space of dimension 4 over Finite Field of size 2

Given an element in degree `n`, it can be represented as a vector in the
vectorspace of all elements of degree `n`::

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
from sage.modules.free_module import VectorSpace
from sage.modules.module import Module as SageModule
from sage.rings.infinity import PlusInfinity
from sage.structure.unique_representation import UniqueRepresentation

from .free_homspace import FreeModuleHomspace
from .free_element import FreeModuleElement


class FreeModule(UniqueRepresentation, SageModule):
    # To accomodate Sage's category framework, we must specify what the
    # elements class is for this parent class.  See
    # http://doc.sagemath.org/html/en/thematic_tutorials/coercion_and_categories.html#implementing-the-category-framework-for-the-elements
    Element = FreeModuleElement

    def __init__(self, generator_degrees, algebra):
        r"""
        Create a finitely generated free graded module over a graded algebra.

        INPUT:

        - ``generator_degrees`` -- a tuple of non-decreasing integers defining
          the number of generators of the module, and their degrees.
        - ``algebra`` -- the algebra over which the module is defined.

        OUTPUT: The finitely generated free graded module on generators with
        degrees given by ``generator_degrees``.

        """
        self._generator_degrees = generator_degrees
        if None in generator_degrees:
            raise ValueError('generator_degrees are not all integers: %s' % str(generator_degrees))

        if not algebra.base_ring().is_field():
            raise NotImplementedError('The ground ring of the algebra must be a field.')
        
        # Call the base class constructor.
        SageModule.__init__(self, algebra)

        self._populate_coercion_lists_()

        self.ModuleClass = FreeModule


    def generator_degrees(self):
        r"""
        The degrees of the module generators.

        OUTPUT: A tuple containing the degrees of the generators for this
        module, in the order that the generators were given when this module
        was constructed.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FreeModule((-2,2,4), A)
            sage: M.generator_degrees()
            (-2, 2, 4)

        """
        return self._generator_degrees


    def is_trivial(self):
        r"""
        Decide if this module is trivial or not.

        OUTPUT: The boolean value True if the module is trivial, and False
        otherwise.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A = SteenrodAlgebra(2)
            sage: FreeModule((-2,2,4), A).is_trivial()
            False
            sage: FreeModule((), A).is_trivial()
            True
            
        """

        return len(self._generator_degrees) == 0


    def connectivity(self):
        r"""
        The connectivity of this module.

        OUTPUT: An integer equal to the minimal degree of the generators, if
        this module is non-trivial.  Otherwise, `+\infty`.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FreeModule((-2,2,4), A)
            sage: M.connectivity()
            -2

        TESTS::

            sage: M = FreeModule((), A)
            sage: M.is_trivial()
            True
            sage: M.connectivity()
            +Infinity

        """
        return min(self._generator_degrees + (PlusInfinity(),))


    def _element_constructor_(self, coefficients):
        r"""
        Construct any element of the module.

        This function is used internally by the ()-operator when creating
        module elements, and should not be called by the user explicitly.

        INPUT:

        - ``coefficients`` -- A tuple of coefficient (i.e. elements of the
        algebra for this module), an element of FreeModule, or the zero integer
        constant.

        OUTPUT: An instance of the element class with coefficients from
        ``coefficients``, the element ``coefficients`` if it already was an
        element, or the zero module element.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FreeModule((0,2,4), A)
            sage: zero = M(0); zero
            <0, 0, 0>
            sage: e = M((Sq(4), Sq(2), 1)); e
            <Sq(4), Sq(2), 1>
            sage: e == M(e)
            True

        """

        if isinstance(coefficients, self.element_class):
            return coefficients
        elif coefficients == 0:
            return self.element_class(self, len(self._generator_degrees)*(0,))
        else:
            return self.element_class(self, coefficients)


    def an_element(self, degree=None):
        r"""
        Return an element of the module.

        This function chooses deterministically an element of the module in the
        given degree.

        INPUT:

        - ``degree`` --  the degree of the element to construct.  If the default
          value ``None`` is given, a degree will be chosen by the function.

        OUTPUT: An element of the given degree.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FreeModule((0,2,4), A)
            sage: M.an_element(172)
            <Sq(0,0,2,0,1,0,1), Sq(0,4,0,0,1,0,1), Sq(7,1,0,0,1,0,1)>

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
        r"""
        Construct a string representation of the module.

        TESTS::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FreeModule((0,2,4), A)
            sage: M._repr_()
            'Finitely presented free module on 3 generators over mod 2 Steenrod algebra, milnor basis'

        """
        return "Finitely presented free module on %s generator%s over %s"\
            %(len(self._generator_degrees), "" if len(self._generator_degrees) == 1 else "s",
              self.base_ring())


    @cached_method
    def basis_elements(self, n):
        r"""
        A basis for the vectorspace of degree ``n`` module elements.

        INPUT:

        - ``n`` -- an integer.

        OUTPUT: A sequence of homogeneous module elements of degree ``n``
        which is a basis for the vectorspace of all degree ``n`` module
        elements.

        .. SEEALSO::
            :meth:`vector_presentation`, :meth:`element_from_coordinates`

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FreeModule((0,2,4), A)
            sage: M.basis_elements(8)
            [<Sq(1,0,1), 0, 0>,
             <Sq(2,2), 0, 0>,
             <Sq(5,1), 0, 0>,
             <Sq(8), 0, 0>,
             <0, Sq(0,2), 0>,
             <0, Sq(3,1), 0>,
             <0, Sq(6), 0>,
             <0, 0, Sq(1,1)>,
             <0, 0, Sq(4)>]

        """
        basis_n = []
        for i, generator_degree in enumerate(self._generator_degrees):
            l = n - generator_degree
            basis_n += [a*self.generator(i) for a in self.base_ring().basis(l)]

        return basis_n


    @cached_method
    def element_from_coordinates(self, coordinates, n):
        r"""
        The module element of degree ``n`` having the given coordinates
        with respect to the basis of module elements given by
        :meth:`basis_elements`.

        INPUT:

        - ``coordinates`` -- a sequence of elements of the ground field.
        - ``n`` -- an integer.

        OUTPUT: A module element of degree ``n``.

        .. SEEALSO::
            :meth:`vector_presentation`, and :meth:`basis_elements`.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FreeModule((0,1), A)
            sage: x = M.element_from_coordinates((0,1,0,1), 5); x
            <Sq(5), Sq(4)>
            sage: basis = M.basis_elements(5)
            sage: y = 0*basis[0] + 1*basis[1] + 0*basis[2] + 1*basis[3]
            sage: x == y
            True

        """
        basis_elements = self.basis_elements(n)

        if len(coordinates) != len(basis_elements):
            raise ValueError('Incorrect coordinate vector size: %s. | Should have length %d.'\
                % (len(coordinates), len(basis_elements)))

        # Adding the condition `if c != 0` improved performance dramatically in this
        # real life example:
        #
        # sage: rels = [ [Sq(1),0,0,0], [Sq(2),0,0,0], [Sq(4),0,0,0], [Sq(8),0,0,0], [0,Sq(1),0,
        # ....: 0], [0,Sq(2),0,0], [0,Sq(4),0,0], [Sq(31),Sq(14),0,0], [0,Sq(20),0,0], [0,0,Sq(1
        # ....: ),0], [0,0,Sq(2),0], [0,Sq(31),Sq(6),0], [0,0,Sq(8),0], [0,0,0,Sq(1)], [0,0,Sq(3
        # ....: 1),Sq(2)], [0,0,0,Sq(4)], [0,0,0,Sq(8)] ]
        # ....:
        # ....: M = FPA_Module([0, 17, 42, 71], A, relations=rels)
        # sage: res = M.resolution(2, top_dim=30, verbose=True)
        #  
        # This function was called a total of 2897 times during the computation,
        # and the total running time of the entire computation dropped from
        # 57 to 21 seconds by adding the optimization.
        #
        element = sum([c*element for c, element in zip(coordinates, basis_elements) if c != 0])
        if element == 0: 
            # The previous sum was over the empty list, yielding the integer
            # 0 as a result, rather than a module element.
            # Fix this by calling the constructor.
            return self._element_constructor_(0)
        else: 
            # The sum defining element is of the correct type. We avoid 
            # calling the constructor unnecessarily, which seems to
            # save time.
            return element


    def __getitem__(self, n):
        r"""
        A vectorspace isomorphic to the vectorspace of module elements of
        degree ``n``.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FreeModule((0,2,4), A)
            sage: V = M[4]; V
            Vector space of dimension 4 over Finite Field of size 2
            sage: V.dimension()
            4

        .. SEEALSO::
            This function is an alias for
            :meth:`sage.modules.fp_modules.free_module.vector_presentation`

        """
        return self.vector_presentation(n)


    @cached_method
    def vector_presentation(self, n):
        r"""
        A vectorspace over the ground field of the module algebra,
        isomorphic to of the degree ``n`` elements of this module.

        Let `\mathcal{k}` be the ground field of the algebra over this module is defined,
        and let `M_n` be the vectorspace of module elements of degree ``n``.

        The return value of this function is the vectorspace over `k`,
        `\mathcal{k}^{r}` where `r = dim(M_n)`.

        The isomorphism between `k^{r}` and `M_n` is given by the
        bijection taking the standard basis element `e_i` to the `i`-th
        element of the array returned by :meth:`basis_elements`.

        INPUT:

        - ``n`` -- an integer degree.

        OUTPUT: A vectorspace over the ground field of the algebra over which
        this module is defined, isomorphic to the vectorspace of module
        elements of degree ``n``.

        .. SEEALSO::
            :meth:`basis_elements`, :meth:`element_from_coordinates`

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A1 = SteenrodAlgebra(2, profile=[2,1])
            sage: M = FreeModule((0,), A1)
            sage: M.vector_presentation(3)
            Vector space of dimension 2 over Finite Field of size 2
            sage: [M.vector_presentation(i).dimension() for i in range(0, 7)]
            [1, 1, 1, 2, 1, 1, 1]

        """
        return VectorSpace(self.base_ring().base_ring(), len(self.basis_elements(n)))


    @cached_method
    def generator(self, index):
        r"""
        Return the module generator with the given ``index``.

        OUTPUT: An instance of the element class of this parent.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FreeModule((0,2,4), A)
            sage: M.generator(0)
            <1, 0, 0>
            sage: M.generator(1)
            <0, 1, 0>
            sage: M.generator(2)
            <0, 0, 1>

        """
        if index < 0 or index >= len(self._generator_degrees):
            raise ValueError('The parent module has generators in the index '\
                'range [0, %s]; generator %s does not exist' %\
                (len(self._generator_degrees) - 1, index))

        return self.element_class(self, index)


    def generators(self):
        r"""
        Return all the module generators.

        OUTPUT: A list consisting instances of the element class of this
        parent.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FreeModule((0,1), A)
            sage: M.generators()
            [<1, 0>, <0, 1>]

        """
        return [self.generator(i) for i in range(len(self._generator_degrees))]


    def _Hom_(self, Y, category):
        r"""
        The internal hook used by the free function
        sage.categories.homset.hom.Hom() to create homsets involving this
        parent.

        """
        return FreeModuleHomspace(self, Y, category)


    def suspension(self, t):
        r"""
        Suspend the module by the given integer degree.

        INPUT:

        - ``t`` -- An integer.

        OUTPUT: A module which is isomorphic to this module by a shift
        of degrees by the integer ``t``.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FreeModule((0,2,4), A)
            sage: M.suspension(4).generator_degrees()
            (4, 6, 8)
            sage: M.suspension(-4).generator_degrees()
            (-4, -2, 0)

        """
        return self.ModuleClass(\
            generator_degrees=tuple([g + t for g in self._generator_degrees]),
            algebra=self.base_ring())

