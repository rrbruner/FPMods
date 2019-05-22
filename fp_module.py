r"""
Finitely presented (graded) modules.

.. RUBRIC:: Introduction

This package allows the user to define finitely presented graded modules
over graded algebras, elements of them, and morphisms between them.

.. RUBRIC:: Implementation

Any finitely presented module over an algebra $R$ is isomorphic to the cokernel
of an $R$-linear homomorphism $f:F_1 \to F_0$ of finitely generated free
modules: The generators of $F_0$ corresponds to the generators of the module,
and the generators of $F_1$ corresponds to its relations.

When a module is constructed, the class constructor uses the given
set of generators and relations to construct such a map of free modules, using
the class FreeModuleHomomorphism, and stores it as a member.

.. NOTE:: A note on the API design

This package was designed with homological algebra in mind, and its API often
focuses on maps rather than objects.  A good example of this is the kernel
function that computes the kernel of a homomorphism $f: M\to N$.  Its return
value is not a module instance, but rather an injective homomorphism
$i: K\to M$ with the property that $\im(i) = \ker(f)$.


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


from sage.categories.homset import Hom
from sage.misc.cachefunc import cached_method
from sage.modules.module import Module as SageModule
from sage.rings.infinity import PlusInfinity
from sage.structure.unique_representation import UniqueRepresentation

from .free_module import FreeModule
from .free_element import FreeModuleElement


def FP_Module(generator_degrees, algebra, relations=()):
    r"""
    INPUT::

    - ``generator_degrees`` -- A finite iterable of non-decreasing integers.
    - ``algebra`` -- The algebra over which the module is defined.
    - ``relations`` -- A finite iterable of iterables of homogeneous algebra
        elements.

    OUTPUT: The finitely presented module over the given algebra with
    presentation given by ``generators`` and ``relations``.

    EXAMPLES::
        sage: from sage.modules.fp_modules.fp_module import FP_Module
        sage: A4 = SteenrodAlgebra(2, profile=(4,3,2,1))
        sage: M = FP_Module([0, 1], A4, [[Sq(2), Sq(1)]])
        sage: M.generators()
        [<1, 0>, <0, 1>]
        sage: M.relations()
        [<Sq(2), Sq(1)>]
        sage: Z = FP_Module([], A4)
        sage: Z.generators()
        []
        sage: Z.relations()
        []

    """
    return FP_Module_class(tuple(generator_degrees), algebra, tuple([tuple([algebra(x) for x in r]) for r in relations]))

class FP_Module_class(UniqueRepresentation, SageModule):
    r"""
    """

    # In the category framework, Elements of the class FP_Module are of the
    # class FP_Element, see
    # http://doc.sagemath.org/html/en/thematic_tutorials/coercion_and_categories.html#implementing-the-category-framework-for-the-elements
    from .fp_element import FP_Element
    Element = FP_Element

    def __init__(self, generator_degrees, algebra, relations=()):
        r"""
        INPUT:

        - ``generator_degrees`` -- A tuple of non-decreasing integers.
        - ``algebra`` -- The algebra over which the module is defined.
        - ``relations`` -- A tuple of tuples of algebra coefficients

        OUTPUT: The finitely presented module over the given algebra with
        presentation given by ``generators`` and ``relations``.

        """

        if None in generator_degrees:
            raise ValueError, ("generators are not all integers: %s" % str(generator_degrees))

        # Store a reference to the input parameters if we need to create a
        # copy of this module.
        self._gds = generator_degrees
        self._rls = relations

        # The free module on the generators of the module.
        generatorModule = FreeModule(
            generator_degrees, algebra=algebra)

        # Use the coefficients given for the relations and make module elements
        # from them.  Filter out the zero elements, as they are redundant.
        rels = [v for v in [generatorModule(r) for r in relations] if not v.is_zero()]

        # The free module for the relations of the module.
        relationsModule = FreeModule(
            tuple([r.degree() for r in rels]), algebra=algebra)

        # The module we want to model is the cokernel of the
        # following morphism.
        self.j = Hom(relationsModule, generatorModule)(rels)

        # Call the base class constructor.
        SageModule.__init__(self, algebra)
        self._populate_coercion_lists_()

        # Store the Homspace class and the module class as member variables so
        # that member functions can use them to create instances.  This enables
        # member functions to create modules and homspace instances of classes
        # that derive from this class.  We needed to do this explicitly since
        # Sage changes the class dynamically as part of its Category framework.
        from .fp_homspace import FP_ModuleHomspace
        self.HomSpaceClass = FP_ModuleHomspace
        self.ModuleClass = FP_Module_class


    @classmethod
    def from_free_module(cls, free_module):
        "Initialize from a finitely generated free module."
        return cls(free_module.generator_degrees(), algebra=free_module.base_ring(), relations=())


    @classmethod
    def from_free_module_morphism(cls, morphism):
        "Initialize from a morphism of finitely generated free module."
        return cls(morphism.codomain().generator_degrees(), algebra=morphism.base_ring(), relations=tuple([r.coefficients() for r in morphism.values()]))


    def change_ring(self, algebra):
        r"""
        Change the base ring of this module.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: A3 = SteenrodAlgebra(2,profile=(3,2,1))
            sage: M = FP_Module([0,1], A, [[Sq(2), Sq(1)]])
            sage: M.change_ring(A3)
            Finitely presented module on 2 generators and 1 relation over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [3, 2, 1]
            sage: M.change_ring(A3).change_ring(A) is M
            True
        """
        return self.ModuleClass(
            self._gds,
            algebra,
            self._rls)


    def _element_constructor_(self, x):
        r"""
        Construct any element of this module.

        INPUT:

        - ``x`` -- A tuple of coefficients, an element of FP_Module, or the
          zero integer constant.

        OUTPUT: An instance of the element class with coefficients from ``x``,
        the element ``x`` if it already was an element, or the zero element.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FP_Module([0,2,4], A, [[Sq(4), Sq(2), 0]])
            sage: e = M(0); e
            <0, 0, 0>
            sage: type(e)
            <class 'sage.modules.fp_modules.fp_module.FP_Module_class_with_category.element_class'>
            sage: f = M((Sq(6), 0, Sq(2))); f
            <Sq(6), 0, Sq(2)>
            sage: type(f)
            <class 'sage.modules.fp_modules.fp_module.FP_Module_class_with_category.element_class'>
            sage: g = M((Sq(6), 0, Sq(2))); g
            <Sq(6), 0, Sq(2)>
            sage: M(g)
            <Sq(6), 0, Sq(2)>
            sage: type(g)
            <class 'sage.modules.fp_modules.fp_module.FP_Module_class_with_category.element_class'>

        """

        if isinstance(x, self.element_class):
            return x
        if isinstance(x, FreeModuleElement):
            return self.element_class(self, x.coefficients())
        elif x == 0:
            return self.element_class(self, len(self.j.codomain().generator_degrees())*(0,))
        else:
            return self.element_class(self, x)


    def _repr_(self):
        r"""
        Construct a string representation of the module.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FP_Module([0,2,4], A, [[Sq(4),Sq(2),0]]); M
            Finitely presented module on 3 generators and 1 relation over mod 2 Steenrod algebra, milnor basis
            sage: N = FP_Module([0,1], A, [[Sq(2),Sq(1)], [Sq(2)*Sq(1),Sq(2)]]); N
            Finitely presented module on 2 generators and 2 relations over mod 2 Steenrod algebra, milnor basis
        """

        return "Finitely presented module on %s generator%s and %s relation%s over %s"\
            %(len(self.j.codomain().generator_degrees()), "" if len(self.j.codomain().generator_degrees()) == 1 else "s",
              len(self.j.values()), "" if len(self.j.values()) == 1 else "s",
              self.base_ring())


    def connectivity(self):
        r"""
        The connectivity of the module.

        EXAMPLES:

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FP_Module([0,2,4], A, [[0, Sq(5), Sq(3)], [Sq(7), 0, Sq(2)*Sq(1)]])
            sage: M.connectivity()
            0
            sage: G = FP_Module([0,2], A, [[1,0]])
            sage: G.connectivity()
            2
            sage: F = FP_Module([-1], A)
            sage: F.connectivity()
            -1

        TESTS:
            sage: C = FP_Module([0], SteenrodAlgebra(2, profile=(3,2,1)), \
                relations=[[Sq(1)], [0]])
            sage: C.connectivity()
            0


        """
        # In case there are no relations, the connectivity is the smallest
        # degree of the generators.
        if self.j._degree == None:
            return self.j.codomain().connectivity()

        # We must check that the generator(s) in the free generator module are
        # not hit by relations, since we are not guaranteed that the
        # presentation of the module is minimal.
        X = [x for x in self.generator_degrees()]
        X.sort()

        previous = None
        for k in X:
            if previous != None and k == previous:
                continue
            if not self.j.vector_presentation(k - self.j._degree).is_surjective():
                return k
            previous = k

        return PlusInfinity()


    def is_trivial(self):
        r"""
        Compute if the relations generate the entire module.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: A3 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: M = FP_Module([], A3)
            sage: M.is_trivial()
            True
            sage: N = FP_Module([1,2], A)
            sage: N.is_trivial()
            False
            sage: P = FP_Module([1,2], A, [[1,0], [0,1]])
            sage: P.is_trivial()
            True


        TESTS:

        Creating a module with a redundant relation:

            sage: C = FP_Module([0], SteenrodAlgebra(2, profile=(3,2,1)), \
                relations=[[Sq(1)], [0]])
            sage: C.is_trivial()
            False

        Creating a trivial module with a redundant relation:

        sage: C = FP_Module([0], SteenrodAlgebra(2), \
                relations=[[Sq(1)], [1]])
            sage: C.is_trivial()
            True

        """
        return self.connectivity() == PlusInfinity()


    def has_relations(self):
        r"""
        Return True if no relations are defined.

        Note that this module is free if this function returns ``False``, but
        a free module can have (unnecessary) relations.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A3 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: F = FP_Module([1,2], A3)
            sage: F.has_relations()
            False
            sage: M = FP_Module([1,2], A3, [[Sq(2), Sq(1)]])
            sage: M.has_relations()
            True
        """
        return not self.j.is_zero()


    def an_element(self, degree=None):
        r"""
        An element of the module.

        This function chooses deterministically an element of the module.

        INPUT:

        - ``degree`` --  The degree of the element to construct.  If the default
          value ``None`` is given, a degree will be chosen by the function.

        OUTPUT:

        -  ``e`` -- An element of the given degree.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A3 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: M = FP_Module([0,2,4], A3, [[0, Sq(5), Sq(3)], [Sq(7), 0, Sq(2)*Sq(1)]])
            sage: M.zero()
            <0, 0, 0>
            sage: [M.an_element(i) for i in range(10)]
            [<1, 0, 0>,
             <Sq(1), 0, 0>,
             <Sq(2), 1, 0>,
             <Sq(0,1), Sq(1), 0>,
             <Sq(1,1), Sq(2), 1>,
             <Sq(2,1), Sq(0,1), Sq(1)>,
             <Sq(0,2), Sq(1,1), Sq(2)>,
             <Sq(0,0,1), Sq(2,1), Sq(0,1)>,
             <Sq(1,0,1), Sq(6), Sq(1,1)>,
             <Sq(2,0,1), Sq(4,1), Sq(2,1)>]
        """
        a_free_element = self.j.codomain().an_element(degree)
        return self._element_constructor_(a_free_element)


    @cached_method
    def basis_elements(self, n):
        r"""
        An ordered set of homogeneous elements spanning the vectorspace of
        module elements of degree ``n``.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A3 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: M = FP_Module([0,2], A3, [[Sq(4), Sq(2)], [0, Sq(6)]])
            sage: M.basis_elements(4)
            [<Sq(1,1), 0>, <Sq(4), 0>]
            sage: M.basis_elements(5)
            [<Sq(2,1), 0>, <Sq(5), 0>, <0, Sq(0,1)>]
            sage: M.basis_elements(25)
            []
            sage: M.basis_elements(0)
            [<1, 0>]
            sage: M.basis_elements(2)
            [<Sq(2), 0>, <0, 1>]

        """
        return [self.element_from_coordinates(x, n) for\
            x in self.vector_presentation(n).basis()]


    @cached_method
    def element_from_coordinates(self, coordinates, n):
        r"""
        The module element in degree ``n`` having coordinates ``coordinates``
        in the standard basis of the vectorspace returned by
        ``self.vector_presentation``.

        INPUT:

        - ``coordinates`` -- The coordinates for a vector in the standard basis
        of the degree ``n`` vector space part of this module.

        - ``n`` -- The degree of the element to construct.

        OUTPUT:

        - ``element`` -- An element of the module in the degree ``n``.

        EXAMPLES:

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FP_Module([0], A, [[Sq(4)], [Sq(7)], [Sq(4)*Sq(9)]])
            sage: M.vector_presentation(12).dimension()
            3
            sage: x = M.element_from_coordinates((0,1,0), 12); x
            <Sq(0,4)>
            sage: x.vector_presentation()
            (0, 1, 0)

        .. SEEALSO::

            :meth:`sage.modules.fp_modules.fp_module.vector_presentation`,

        """
        M_n = self.vector_presentation(n)

        if len(coordinates) != M_n.dimension():
            raise ValueError('The coordinate vector has incorrect length: %d.  Should be %d' %
                (len(coordinates), M_n.dimension()))

        free_element = self.j.codomain().element_from_coordinates(
            M_n.lift(coordinates), n)

        return self._element_constructor_(free_element.coefficients())


    @cached_method
    def vector_presentation(self, n):
        r"""
        A vectorspace isomorphic to the vectorspace of module elements of
        degree ``n``.

        An isomorphism between this vectorspace $V$ and the
        degree ``n`` part of this module is given by the linear transformation
        $e_i\mapsto self.element_from_coordinates(e_i,n)$,
        where $e_i$ runs through the standard basis for $V$.

        INPUT:

        - ``n`` -- The degree of the presentation.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FP_Module([0,2,4], A, [[Sq(4),Sq(2),0]])
            sage: V = M.vector_presentation(4)
            sage: V.dimension()
            3
            sage: M.element_from_coordinates((1,0,0), 4)
            <Sq(1,1), 0, 0>
            sage: M.element_from_coordinates((0,1,0), 4)
            <Sq(4), 0, 0>
            sage: M.element_from_coordinates((0,0,1), 4)
            <0, 0, 1>
            sage: x = M([0, Sq(2), 0])
            sage: y = M([Sq(4), 0, 0])
            sage: x == y
            True
        """

        # Get the vector space presentation of the free module on the
        # module generators.
        F_n = self.j.codomain().vector_presentation(n)

        # Compute the sub vectorspace generated by the relations.
        spanning_set = []
        for relation in self.j.values():

            if relation.is_zero():
                continue

            for a in self.base_ring().basis(n - relation.degree()):
                # assert: isinstance(FreeElement, relation)
                v = (a*relation).vector_presentation()
                if v != None:
                    spanning_set.append(v)

        R_n = F_n.subspace(spanning_set)

        # Return the quotient of the free part by the relations.
        return F_n/R_n


    def _Hom_(self, Y, category):
        r"""
        The internal hook used by the free function
        sage.categories.homset.hom.Hom() to create homsets involving this
        parent.

        TESTS::

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: F = FP_Module([1,3], A);
            sage: L = FP_Module([2,3], A, [[Sq(2),Sq(1)], [0,Sq(2)]]);
            sage: homset = Hom(F, L); homset
            Set of Morphisms from Finitely presented module on 2 generators ...

        """
        if not isinstance(Y, self.__class__):
            raise ValueError('Cannot create homspace between incompatible types:\n%s  ->\n%s' % (self.__class__, type(Y)))
        if Y.base_ring() != self.base_ring():
            raise ValueError('The modules are not defined over the same base ring.')

        return self.HomSpaceClass(self, Y, category)


    def generator_degrees(self):
        r"""
        The degrees of the generators for this module.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A4 = SteenrodAlgebra(2, profile=(4,3,2,1))
            sage: N = FP_Module([0, 1], A4, [[Sq(2), Sq(1)]])
            sage: N.generator_degrees()
            (0, 1)

        """

        return self.j.codomain().generator_degrees()


    def generators(self):
        r"""
        The generators of this module.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A4 = SteenrodAlgebra(2, profile=(4,3,2,1))
            sage: M = FP_Module([0,2,3], A4)
            sage: M.generators()
            [<1, 0, 0>, <0, 1, 0>, <0, 0, 1>]
            sage: N = FP_Module([0, 1], A4, [[Sq(2), Sq(1)]])
            sage: N.generators()
            [<1, 0>, <0, 1>]
            sage: Z = FP_Module([], A4)
            sage: Z.generators()
            []

        """
        return [self.generator(i) for i in range(len(self.j.codomain().generator_degrees()))]


    def generator(self, index):
        r"""
        The module generator with the given ``index``.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A4 = SteenrodAlgebra(2, profile=(4,3,2,1))
            sage: M = FP_Module([0,2,3], A4); M.generator(0)
            <1, 0, 0>
            sage: N = FP_Module([0, 1], A4, [[Sq(2), Sq(1)]]); N.generator(1)
            <0, 1>

        """
        return self.element_class(self, self.j.codomain().generator(index))


    def relations(self):
        r"""
        The relations of this module.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A4 = SteenrodAlgebra(2, profile=(4,3,2,1))
            sage: M = FP_Module([0,2,3], A4)
            sage: M.relations()
            []
            sage: N = FP_Module([0, 1], A4, [[Sq(2), Sq(1)]])
            sage: N.relations()
            [<Sq(2), Sq(1)>]
            sage: Z = FP_Module([], A4)
            sage: Z.relations()
            []

        """
        return self.j.values()


    def relation(self, index):
        r"""
        The module relation with the given ``index``.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A4 = SteenrodAlgebra(2, profile=(4,3,2,1))
            sage: N = FP_Module([0, 1], A4, [[Sq(2), Sq(1)]])
            sage: N.relation(0)
            <Sq(2), Sq(1)>

        """
        return self.j.values()[index]


    def min_pres(self, top_dim=None, verbose=False):
        r"""
        A minimal presentation of this module.

        OUTPUT:

        -  ``f`` - An isomorphism $M \to self$, where $M$ has minimal
            presentation.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A3 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: M = FP_Module([0,1], A3, [[Sq(2),Sq(1)],[0,Sq(2)],[Sq(3),0]])
            sage: i = M.min_pres()
            sage: i.codomain() is M
            True
            sage: i.is_injective()
            True
            sage: i.is_surjective()
            True
            sage: i.domain().relations()
            [<Sq(2), Sq(1)>, <0, Sq(2)>]
            sage: i.codomain().relations()
            [<Sq(2), Sq(1)>, <0, Sq(2)>, <Sq(3), 0>]

        """
        return Hom(self, self).identity().image(top_dim, verbose)


    def suspension(self, t):
        r"""
        This module suspended by the given degree ``t``.

        INPUT:

        - ``t`` -- An integer by which the module is suspended.

        OUTPUT:

        - ``C`` -- A module which is identical to this module by a shift
          of degrees by the integer ``t``.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: A3 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: Y = FP_Module([0], A3, [[Sq(1)]])
            sage: X = Y.suspension(4)
            sage: X.generator_degrees()
            (4,)
            sage: X.relations()
            [<Sq(1)>]
            sage: M = FP_Module([2,3], A, [[Sq(2), Sq(1)], [0, Sq(2)]])
            sage: Q = M.suspension(1)
            sage: Q.generator_degrees()
            (3, 4)
            sage: Q.relations()
            [<Sq(2), Sq(1)>, <0, Sq(2)>]
            sage: Q = M.suspension(-3)
            sage: Q.generator_degrees()
            (-1, 0)
            sage: Q = M.suspension(0)
            sage: Q.generator_degrees()
            (2, 3)

        """
        return self.ModuleClass(
            generator_degrees=tuple([g + t for g in self.j.codomain().generator_degrees()]),
            algebra=self.base_ring(),
            relations=self._rls)


    def submodule(self, spanning_elements):
        r"""
        The submodule $S$ of this module spanned by the elements
        ``spanning_elements``.

        INPUT:

        -  ``spanning_elements``  - An iterable of elements of this module.

        OUTPUT:

        - ``i`` -- The inclusion of $S$ into this module.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A3 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: M = FP_Module([0,1], A3, [[Sq(2),Sq(1)]])
            sage: i = M.submodule([M.generator(0)])
            sage: i.codomain() is M
            True
            sage: i.is_injective()
            True
            sage: i.domain().generator_degrees()
            (0,)
            sage: i.domain().relations()
            [<Sq(3)>]

        """
        # Create the free graded module on the set of spanning elements.
        degs = [x.degree() for x in spanning_elements]
        F = self.ModuleClass(tuple(degs), algebra=self.base_ring())

        # The submodule is the module generated by the spanning elements.
        return Hom(F, self)(spanning_elements).image()


    def resolution(self, k, verbose=False):
        r"""
        A resolution of this module of length ``k``.

        INPUT:

        - ``k`` -- An non-negative integer.

        - ``verbose`` -- A boolean to control if log messages should be emitted.
          (optional, default: ``False``)

        OUTPUT:

        - ``res`` -- A list of homomorphisms `[f_0, f_1, \ldots, f_k]`
          constituting a free resolution of length `k`.  The indexing is set up
          such that `\text{codomain}(f_i) = \text{domain}(f_{i-1})` and
          `\text{codomain}(f_0)` is this module.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A3 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: M = FP_Module([0,1], A3, [[Sq(2), Sq(1)]])
            sage: M.resolution(0)
            []
            sage: res = M.resolution(4, verbose=True)
            Step 1/4
            Resolving kernel dimensions up to #25: 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25.
            Step 2/4
            Resolving kernel dimensions up to #25: 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25.
            Step 3/4
            Resolving kernel dimensions up to #26: 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26.
            Step 4/4
            Resolving kernel dimensions up to #32: 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32.
            sage: len(res)
            4
            sage: res
            [Module homomorphism of degree 0 defined by sending the generators
               [<1, 0>, <0, 1>]
             to
               (<1, 0>, <0, 1>),
             Module homomorphism of degree 0 defined by sending the generators
               [<1>]
             to
               (<Sq(2), Sq(1)>,),
             Module homomorphism of degree 0 defined by sending the generators
               [<1>]
             to
               (<Sq(3,1)>,),
             Module homomorphism of degree 0 defined by sending the generators
               [<1, 0>, <0, 1>]
             to
               (<Sq(1)>, <Sq(2)>)]
            sage: for i in range(len(res)-1):
            ....:     if not (res[i]*res[i+1]).is_zero():
            ....:          print('The result is not a complex.')
        """

        if k < 0:
            raise ValueError, "The length of the resolution must be non-negative."

        complex = []

        if k == 0:
            return complex

        # Optimization:
        #        # The first map of the resolution is just the quotient map from
        #        # the free module on the generators of the `self` module down to
        #        # `self`.
        #        free_module = self.j.codomain()
        #        F = self.ModuleClass.from_free_module(free_module)
        #
        #        # Promote the elements of the generators of the free module to
        #        # elements of the self module.
        #        values = [self(x._coefficients) for x in free_module.generators()]
        #
        #        j0 = Hom(F, self)(values)
        #        complex.append(j0)

        for i in range(k):
            if verbose:
                print ('Step %d/%d' % (i+1, k))
            j = Hom(self, self).zero() if i == 0 else complex[i-1]
            complex.append(j.resolve_kernel(verbose=verbose))

        return complex

