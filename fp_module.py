r"""
Finitely presented graded modules

This class implements methods for construction and basic manipulation of
finitely presented graded modules over connected graded algebras.

.. NOTE:: This class is intended for private use by
    :class:`sage.modules.finitely_presented_over_the_steenrod_algebra.fpa_module.FPA_Module`.
    As a consequence, all tests and examples consider modules over the
    the Steenrod algebra (or a finite sub-Hopf algebra of it).

    However, this class does not assume that the algebra is the Steenrod
    algebra and could be a starting point for developers wanting to extend
    Sage further.

==============
Implementation
==============

Let `R` be a connecteded graded algebra.  A finitely presented module over `R`
is isomorphic to the cokernel of an `R`-linear homomorphism `f:F_1 \to F_0`
of finitely generated free modules: The generators of `F_0` corresponds to the
generators of the module, and the generators of `F_1` corresponds to its
relations, via the map `f`.

The class constructor of this module class is given a set of generators and
relations, and uses them to construct a presentation, using the class
:class:`sage.modules.finitely_presented_over_the_steenrod_algebra.free_morphism.FreeModuleMorphism`.

This package was designed with homological algebra in mind, and its API
focuses on maps rather than objects.  A good example of this is the kernel
function :meth:`sage.modules.finitely_presented_over_the_steenrod_algebra.fp_morphism.FP_ModuleMorphism.kernel`
which computes the kernel of a homomorphism `f: M\to N`.  Its return value is
not an instance of the module class, but rather an injective homomorphism
`i: K\to M` with the property that `\operatorname{im}(i) = \ker(f)`.

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

from sage.categories.homset import Hom
from sage.misc.cachefunc import cached_method
from sage.modules.module import Module as SageModule
from sage.rings.infinity import PlusInfinity
from sage.structure.unique_representation import UniqueRepresentation

from .free_module import FreeModule
from .free_element import FreeModuleElement

import time



class FP_Module(UniqueRepresentation, SageModule):
    # In the category framework, Elements of the class FP_Module are of the
    # class FP_Element, see
    # http://doc.sagemath.org/html/en/thematic_tutorials/coercion_and_categories.html#implementing-the-category-framework-for-the-elements
    from .fp_element import FP_Element
    Element = FP_Element

    @staticmethod
    def __classcall_private__(cls, generator_degrees, algebra, relations=()):
        r"""
        Normalize input to ensure a unique representation.

        INPUT:

        - ``generator_degrees`` -- an iterable of integer degrees.

        - ``algebra`` -- the connected graded algebra over which the module is defined.

        - ``relations`` -- an iterable of relations.  A relation is a tuple of
          coefficients `(c_1, \ldots, c_n)` corresponding to the module
          generators.

        OUTPUT: The finitely presented module with presentation given by
        the ``generator_degrees`` and ``relations``.

        TESTS:

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
            sage: A3 = SteenrodAlgebra(2, profile=(4,3,2,1))
            sage: FP_Module([0, 1], A3, [[Sq(2), Sq(1)]])
            Finitely presented module on 2 generators and 1 relation over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [4, 3, 2, 1]

        """
        return super(FP_Module, cls).__classcall__(cls, tuple(generator_degrees), algebra, tuple([tuple([algebra(x) for x in r]) for r in relations]))


    def __init__(self, generator_degrees, algebra, relations=()):
        r"""
        Create a finitely presented module over a connected graded algebra.

        INPUT:

        - ``generator_degrees`` -- A tuple of integer degrees.

        - ``algebra`` -- The algebra over which the module is defined.

        - ``relations`` -- A tuple of relations.  A relation is a tuple of
          coefficients `(c_1, \ldots, c_n)`, ordered so that they
          correspond to the module generators.

        OUTPUT: The finitely presented module over ``algebra`` with
        presentation given by ``generator_degrees`` and ``relations``.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
            sage: A3 = SteenrodAlgebra(2, profile=(4,3,2,1))

            sage: M = FP_Module([0, 1], A3, [[Sq(2), Sq(1)]])
            sage: M.generators()
            [<1, 0>, <0, 1>]
            sage: M.relations()
            [<Sq(2), Sq(1)>]
            sage: M.is_trivial()
            False

            sage: Z = FP_Module([], A3)
            sage: Z.generators()
            []
            sage: Z.relations()
            []
            sage: Z.is_trivial()
            True

        """
        if None in generator_degrees:
            raise ValueError("generators are not all integers: %s" % str(generator_degrees))

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
        self.ModuleClass = FP_Module


    @classmethod
    def from_free_module(cls, free_module):
        r"""
        Initialize from a finitely generated free module.

        INPUT:

        - ``free_module`` -- a finitely generated free module.

        OUTPUT: the finitely presented module having same set of generators
        assert ``free_module``, and no relations.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.free_module import *
            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: F = FreeModule((-2,2,4), A)
            sage: FP_Module.from_free_module(F)
            Finitely presented module on 3 generators and 0 relations over mod 2 Steenrod algebra, milnor basis


        """
        return cls(free_module.generator_degrees(), algebra=free_module.base_ring(), relations=())


    @classmethod
    def from_free_module_morphism(cls, morphism):
        r"""
        Create a finitely presented module from a morphism of finitely
        generated free modules.

        INPUT:

        - ``morphism`` -- a morphism between finitely generated free modules.

        OUTPUT:

        The finitely presented module having presentation equal to the
        homomorphism ``morphism``.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.free_module import *
            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: F1 = FreeModule((2,), A)
            sage: F2 = FreeModule((0,), A)
            sage: v = F2([Sq(2)])
            sage: pres = Hom(F1, F2)([v])
            sage: M = FP_Module.from_free_module_morphism(pres); M
            Finitely presented module on 1 generator and 1 relation over mod 2 Steenrod algebra, milnor basis
            sage: M.generator_degrees()
            (0,)
            sage: M.relations()
            [<Sq(2)>]

        """
        return cls(morphism.codomain().generator_degrees(), algebra=morphism.base_ring(), relations=tuple([r.coefficients() for r in morphism.values()]))


    def change_ring(self, algebra):
        r"""
        Change the base ring of this module.

        INPUT:

        - ``algebra`` -- a connected graded algebra.

        OUTPUT: The finitely presented module over ``algebra`` defined with the
        exact same number of generators of the same degrees and relations as
        this module.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: A2 = SteenrodAlgebra(2,profile=(3,2,1))

            sage: M = FP_Module([0,1], A, [[Sq(2), Sq(1)]])
            sage: M_ = M.change_ring(A2); M_
            Finitely presented module on 2 generators and 1 relation over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [3, 2, 1]

            sage: # Changing back yields the original module.
            sage: M_.change_ring(A) is M
            True
        """
        return self.ModuleClass(
            self._gds, algebra, self._rls)


    def _element_constructor_(self, x):
        r"""
        Construct any element of this module.

        This function is used internally by the ()-method when creating
        module elements, and should not be called by the user explicitly.

        INPUT:

        - ``x`` -- A tuple of coefficients, an element of FP_Module, or the
          zero integer constant.

        OUTPUT: An instance of the element class with coefficients from ``x``,
        the element ``x`` if it already was an element, or the zero element.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FP_Module([0,2,4], A, [[Sq(4), Sq(2), 0]])

            sage: # Creating an element from coefficients:
            sage: e = M((Sq(6), 0, Sq(2))); e
            <Sq(6), 0, Sq(2)>
            sage: e in M
            True

            sage: # Special syntax for creating the zero element:
            sage: z = M(0); z
            <0, 0, 0>
            sage: z.is_zero()
            True

            sage: # Creating an element from another element returns a reference to itself:
            sage: M(e)
            <Sq(6), 0, Sq(2)>
            sage: e is M(e)
            True

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

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FP_Module([0,2,4], A, [[Sq(4),Sq(2),0]]); M
            Finitely presented module on 3 generators and 1 relation over mod 2 Steenrod algebra, milnor basis
            sage: N = FP_Module([0,1], A, [[Sq(2),Sq(1)], [Sq(2)*Sq(1),Sq(2)]]); N
            Finitely presented module on 2 generators and 2 relations over mod 2 Steenrod algebra, milnor basis
            sage: F = FP_Module([2], A); F
            Finitely presented module on 1 generator and 0 relations over mod 2 Steenrod algebra, milnor basis

        """
        return "Finitely presented module on %s generator%s and %s relation%s over %s"\
            %(len(self.j.codomain().generator_degrees()), "" if len(self.j.codomain().generator_degrees()) == 1 else "s",
              len(self.j.values()), "" if len(self.j.values()) == 1 else "s",
              self.base_ring())


    def connectivity(self):
        r"""
        The connectivity of this module.

        Since a finitely presented module over a connected algebra is in
        particular bounded below, the connectivity is an integer when the
        module is non-trivial, and `+\infty` when the module is trivial.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
            sage: A = SteenrodAlgebra(2)

            sage: M = FP_Module([0,2,4], A, [[0, Sq(5), Sq(3)], [Sq(7), 0, Sq(2)*Sq(1)]])
            sage: M.connectivity()
            0

            sage: G = FP_Module([0,2], A, [[1,0]])
            sage: G.connectivity()
            2

        TESTS:

            sage: C = FP_Module([0], SteenrodAlgebra(2, profile=(3,2,1)), relations=[[Sq(1)], [0]])
            sage: C.connectivity()
            0

            sage: F = FP_Module([-1], A)
            sage: F.connectivity()
            -1

            sage: F = FP_Module([], A)
            sage: F.connectivity()
            +Infinity

            sage: F = FP_Module([0], A, [[1]])
            sage: F.connectivity()
            +Infinity

        """
        # In case there are no relations, the connectivity is the equal to
        # the connectivity of the free module on the generators.
        if self.j._degree == None:
            return self.j.codomain().connectivity()

        # We must check that the generator(s) in the free generator module are
        # not hit by relations, since we are not guaranteed that the
        # presentation we have is minimal.
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
        Decide if this module is isomorphic to the trivial module.

        OUTPUT: Returns ``True`` if the relations generate every non-zero
        element of the module, and ``False`` otherwise.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
            sage: A = SteenrodAlgebra(2)
            sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))

            sage: M = FP_Module([], A2)
            sage: M.is_trivial()
            True

            sage: N = FP_Module([1,2], A)
            sage: N.is_trivial()
            False

            sage: P = FP_Module([1,2], A, [[1,0], [0,1]])
            sage: P.is_trivial()
            True

        TESTS:

            sage: C = FP_Module([0], SteenrodAlgebra(2, profile=(3,2,1)), [[Sq(1)], [0]])
            sage: C.is_trivial()
            False

            sage: C = FP_Module([0], SteenrodAlgebra(2), [[Sq(1)], [1]])
            sage: C.is_trivial()
            True

        """
        return self.connectivity() == PlusInfinity()


    def has_relations(self):
        r"""
        Return ``True`` if no relations are defined, and ``False``
        otherwise.

        .. NOTE::

            This module is free if this function returns ``False``, but a free
            module can have (redundant) relations.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
            sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))

            sage: F = FP_Module([1,2], A2)
            sage: F.has_relations()
            False

            sage: M = FP_Module([1,2], A2, [[Sq(2), Sq(1)]])
            sage: M.has_relations()
            True

            sage: # A free module constructed with a redundant
            ....: # generator and relation.
            sage: N = FP_Module([0,0], A2, [[0, 1]])
            sage: N.has_relations()
            True
            sage: # Computing a minimal presentation reveals an
            ....: # isomorphic module with no relations.
            sage: N_min = N.min_pres().domain()
            sage: N_min.has_relations()
            False

        """
        return not self.j.is_zero()


    def an_element(self, n=None):
        r"""
        An element of this module.

        This function chooses deterministically an element, i.e the output
        dependens only on the module and its input ``n``.

        INPUT:

        - ``n`` --  The degree of the element to construct.  If the default
          value ``None`` is given, a degree will be chosen by the function.

        OUTPUT: A module element of the given degree.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import *
            sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: M = FP_Module([0,2,4], A2, [[0, Sq(5), Sq(3)], [Sq(7), 0, Sq(2)*Sq(1)]])

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
        a_free_element = self.j.codomain().an_element(n)
        return self._element_constructor_(a_free_element)


#    @cached_method
    @cached_method(key=lambda self, n, fpmod_timings: (self,n))
    def basis_elements(self, n, fpmod_timings=None):
        r"""
        A basis for the vectorspace of degree ``n`` module elements.

        INPUT:

        - ``n`` -- an integer.

        - ``verbose`` -- A boolean to control if log messages should be emitted.
          (optional, default: ``False``)

        OUTPUT: A list of homogeneous module elements of degree ``n`` which is
        a basis for the vectorspace of all degree ``n`` module elements.

        .. SEEALSO::

            :meth:`vector_presentation`, :meth:`element_from_coordinates`

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import *
            sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: M = FP_Module([0,2], A2, [[Sq(4), Sq(2)], [0, Sq(6)]])

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

        TESTS:

            sage: Z0 = FP_Module([], A2)
            sage: Z0.basis_elements(n=10)
            []

            sage: Z1 = FP_Module([1], A2, [[1]])
            sage: Z1.basis_elements(n=10)
            []

        """

        selfpres = self.vector_presentation(n, fpmod_timings)

        dt = time.time()

        basis = selfpres.basis()

        if not fpmod_timings is None:
            fpmod_timings['lin_alg'] += time.time() - dt

        els = [self.element_from_coordinates(x, n, fpmod_timings) for x in basis]

        return els


    @cached_method(key=lambda self, coordinates, n, fpmod_timings: (self,n,coordinates))
    def element_from_coordinates(self, coordinates, n, fpmod_timings=None):
        r"""
        The module element in degree ``n`` having the given coordinates with
        respect to the basis returned by :meth:`basis_elements`.

        This function is inverse to
        :meth:`sage.modules.finitely_presented_over_the_steenrod_algebra.fp_element.FP_Element.vector_presentation`.

        INPUT:

        - ``coordinates`` -- a vector of coordinates.

        - ``n`` -- the degree of the element to construct.

        OUTPUT: A module element of degree ``n`` having the given coordinates
        with respect to the basis returned by :meth:`basis_elements`.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FP_Module([0], A, [[Sq(4)], [Sq(7)], [Sq(4)*Sq(9)]])

            sage: M.vector_presentation(12).dimension()
            3
            sage: x = M.element_from_coordinates((0,1,0), 12); x
            <Sq(0,4)>

        Applying the inverse function brings us back to the coordinate form::

            sage: x.vector_presentation()
            (0, 1, 0)

        TESTS:

            sage: M.element_from_coordinates((0,1,0,0), 12)
            Traceback (most recent call last):
             ...
            ValueError: The given coordinate vector has incorrect length: 4.  It should have length 3.

        .. SEEALSO::

            :meth:`sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module.FP_Module.vector_presentation`

        """
        M_n = self.vector_presentation(n,fpmod_timings)

        if len(coordinates) != M_n.dimension():
            raise ValueError('The given coordinate vector has incorrect length: %d.  '
                  'It should have length %d.' % (len(coordinates), M_n.dimension()))

        free_element = self.j.codomain().element_from_coordinates(
            M_n.lift(coordinates), n)

        return self._element_constructor_(free_element.coefficients())


    def __getitem__(self, n):
        r"""
        A basis for the vectorspace of degree ``n`` module elements.

        INPUT:

        - ``n`` -- an integer.

        OUTPUT: A list of homogeneous module elements of degree ``n`` which is
        a basis for the vectorspace of all degree ``n`` module elements.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
            sage: A = SteenrodAlgebra(2)
            sage: M = FP_Module([0,2,4], A, [[Sq(4),Sq(2),0]])

            sage: M[4]
            [<Sq(1,1), 0, 0>, <Sq(4), 0, 0>, <0, 0, 1>]

        .. SEEALSO::

            :meth:`basis_elements`

        """
        return self.basis_elements(n)


    @cached_method(key=lambda self,n, fpmod_timings: (self,n))
    def vector_presentation(self, n, fpmod_timings=None):
        r"""
        A vectorspace isomorphic to the vectorspace of module elements of
        degree ``n``.

        INPUT:

        - ``n`` -- The degree of the presentation.

        OUTPUT: A vectorspace.

        .. SEEALSO::

            :meth:`basis_elements`, :meth:`element_from_coordinates`

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FP_Module([0,2,4], A, [[Sq(4),Sq(2),0]])

            sage: V = M.vector_presentation(4)
            sage: V.dimension()
            3

            sage: len(M.basis_elements(4))
            3

        """

        dt = time.time()

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
                if not v is None:
                    spanning_set.append(v)

        R_n = F_n.subspace(spanning_set)

        # Return the quotient of the free part by the relations.
        quo = F_n/R_n

        if not fpmod_timings is None:
            fpmod_timings['vector_presentationzzz'] += time.time() - dt


        return quo



    def _Hom_(self, Y, category):
        r"""
        The internal hook used by the free function
        :meth:`sage.categories.homset.hom.Hom` to create homsets involving
        this parent class.

        TESTS:

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import *
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

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import *
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

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
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
        The module generator with the given index.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import *
            sage: A4 = SteenrodAlgebra(2, profile=(4,3,2,1))

            sage: M = FP_Module([0,2,3], A4)
            sage: M.generator(0)
            <1, 0, 0>

            sage: N = FP_Module([0, 1], A4, [[Sq(2), Sq(1)]])
            sage: N.generator(1)
            <0, 1>

        """
        return self.element_class(self, self.j.codomain().generator(index))


    def relations(self):
        r"""
        The relations of this module.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import *
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
        The module relation of the given index.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import *
            sage: A4 = SteenrodAlgebra(2, profile=(4,3,2,1))
            sage: N = FP_Module([0, 1], A4, [[Sq(2), Sq(1)]])
            sage: N.relation(0)
            <Sq(2), Sq(1)>

        """
        return self.j.values()[index]


    def min_pres(self, top_dim=None):
        r"""
        A minimal presentation of this module.

        OUTPUT: An isomorphism `M \to self`, where `M` has minimal presentation.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import *
            sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))

            sage: M = FP_Module([0,1], A2, [[Sq(2),Sq(1)],[0,Sq(2)],[Sq(3),0]])
            sage: i = M.min_pres()
            sage: M_min = i.domain()

            sage: # i is an isomorphism between M_min and M:
            sage: i.codomain() is M
            True
            sage: i.is_injective()
            True
            sage: i.is_surjective()
            True

            sage: # There are more relations in M than in M_min:
            sage: M.relations()
            [<Sq(2), Sq(1)>, <0, Sq(2)>, <Sq(3), 0>]
            sage: M_min.relations()
            [<Sq(2), Sq(1)>, <0, Sq(2)>]

        TESTS:

            sage: T = FP_Module([0], A2, [[1]])
            sage: T_min = T.min_pres().domain()
            sage: T_min.is_trivial()
            True
            sage: T_min
            Finitely presented module on 0 generators and 0 relations over ...

        """
        return Hom(self, self).identity().image(top_dim)


    def suspension(self, t):
        r"""
        The suspension of this module by the given degree.

        INPUT:

        - ``t`` -- An integer degree by which the module is suspended.

        OUTPUT: A module which is identical to this module by a shift of
        degrees by the integer ``t``.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))

            sage: Y = FP_Module([0], A2, [[Sq(1)]])
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
        The submodule of this module spanned by the given elements.

        INPUT:

        -  ``spanning_elements``  - An iterable of elements of this module.

        OUTPUT: The inclusion of the submodule into this module.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import *
            sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))

            sage: M = FP_Module([0,1], A2, [[Sq(2),Sq(1)]])
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


    def resolution(self, k, top_dim=None):
        r"""
        A resolution of this module of length ``k``.

        INPUT:

        - ``k`` -- An non-negative integer.

        - ``verbose`` -- A boolean to control if log messages should be emitted.
          (optional, default: ``False``)

        OUTPUT: A list of homomorphisms `[\epsilon, f_1, \ldots, f_k]` such that

            `f_i: F_i \to F_{i-1}` for `1<i\leq k`,

            `\epsilon: F_0\to M`,

          where each `F_i` is a finitely generated free module, and the
          sequence

            `F_k \xrightarrow{\mathit{f_k}} F_{k-1} \xrightarrow{\mathit{f_{k-1}}} \ldots \rightarrow F_0 \xrightarrow{\epsilon} M \rightarrow 0`

          is exact.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import *
            sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: M = FP_Module([0,1], A2, [[Sq(2), Sq(1)]])
            sage: M.resolution(0)
            [Module homomorphism of degree 0 defined by sending the generators
               [<1, 0>, <0, 1>]
             to
               (<1, 0>, <0, 1>)]
            sage: res = M.resolution(4, verbose=True)
            Computing f_1 (1/4)
            Computing f_2 (2/4)
            Resolving the kernel in the range of dimensions [2, 25]: 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25.
            Computing f_3 (3/4)
            Resolving the kernel in the range of dimensions [8, 31]: 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31.
            Computing f_4 (4/4)
            Resolving the kernel in the range of dimensions [9, 33]: 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 33.
            sage: len(res)
            5
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
               (<Sq(1)>, <Sq(2)>),
             Module homomorphism of degree 0 defined by sending the generators
               [<1, 0>, <0, 1>]
             to
               (<Sq(1), 0>, <Sq(0,1), Sq(2)>)]
            sage: for i in range(len(res)-1):
            ....:     if not (res[i]*res[i+1]).is_zero():
            ....:          print('The result is not a complex.')
        """

        def _print_progress(i, k):
            #            if verbose:
            print ('Computing f_%d (%d/%d)' % (i, i, k))

        if k < 0:
            raise ValueError("The length of the resolution must be non-negative.")

        complex = []

        # Epsilon: F_0 -> M
        F_0 = self.ModuleClass.from_free_module(self.j.codomain())
        epsilon = Hom(F_0, self)(tuple(self.generators()))
        complex.append(epsilon)

        if k == 0:
            return complex

        # f_1: F_1 -> F_0
        _print_progress(1, k)
        F_1 = self.ModuleClass.from_free_module(self.j.domain())
        pres = Hom(F_1, F_0)(tuple([ F_0(x.coefficients()) for x in self.j.values() ]))

        complex.append(pres)

        from .fp_morphism import FP_ModuleMorphism

        # f_i: F_i -> F_i-1, for i > 1
        for i in range(2, k+1):
            _print_progress(i, k)

            f = complex[i-1]
            complex.append(
                FP_ModuleMorphism._resolve_kernel(
                    f,
                    top_dim=top_dim))

        return complex

