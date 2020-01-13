r"""
Homomorphisms of finitely presented graded modules

This class implements construction and basic manipulation of homomorphisms
between finitely presented graded modules, modelled by the Sage
parent :class:`sage.modules.fp_modules.fp_module.FP_Module`.

This class is intended for private use by the class
:class:`sage.modules.fp_modules.fpa_morphism.FPA_ModuleMorphism` modelling
homomorphisms between finitely presented modules over the Steenrod algebra.

EXAMPLES::

    sage: from sage.modules.fp_modules.fp_module import FP_Module
    sage: A = SteenrodAlgebra(2)
    sage: F1 = FP_Module([4,5], A)
    sage: F2 = FP_Module([3,4], A)
    sage: F3 = FP_Module([2,3], A)
    sage: H1 = Hom(F1, F2)
    sage: H2 = Hom(F2, F3)
    sage: f = H1( ( F2((Sq(1), 0)), F2((0, Sq(1))) ) )
    sage: g = H2( ( F3((Sq(1), 0)), F3((0, Sq(1))) ) )
    sage: f*g
    Traceback (most recent call last):
     ...
    ValueError: Morphisms not composable.
    sage: g*f
    The trivial homomorphism.
    sage: Q1 = FP_Module((2,3), A, relations=[[Sq(6), Sq(5)]]); Q1
    Finitely presented module on 2 generators and 1 relation ...
    sage: w = Hom(F1, F1)(( F1((Sq(6), Sq(5))), F1(0) )); w
    Module homomorphism of degree 6 defined by sending the generators
      [<1, 0>, <0, 1>]
    to
      (<Sq(6), Sq(5)>, <0, 0>)
    sage: p = w.cokernel()
    sage: Q2 = p.codomain(); Q2
    Finitely presented module on 2 generators and 1 relation over mod 2 Steenrod algebra, milnor basis
    sage: Q2.relations()
    [<Sq(6), Sq(5)>]
    sage: x = F1((Sq(7)*Sq(6), Sq(7)*Sq(5))); x
    <Sq(7,2), Sq(3,3)>
    sage: x.is_zero()
    False
    sage: y = p(x); y.normalize()
    <0, 0>
    sage: y.is_zero()
    True
    sage: x2 = F1((Sq(5)*Sq(8), Sq(4)*Sq(4)*Sq(4)));
    sage: (x + x2) == x
    False
    sage: p(x + x2) == p(x2)
    True
    sage: i = p.kernel(top_dim=10); i.domain()
    Finitely presented module on 1 generator and 0 relations over mod 2 Steenrod algebra, milnor basis
    sage: i
    Module homomorphism of degree 0 defined by sending the generators
      [<1>]
    to
      (<Sq(6), Sq(5)>,)
    sage: p_ = p.change_ring(SteenrodAlgebra(2, profile=(3,2,1)))
    sage: p_.kernel().domain()
    Finitely presented module on 1 generator and 3 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [3, 2, 1]
    sage: p_.kernel().codomain()
    Finitely presented module on 2 generators and 0 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [3, 2, 1]
    sage: C = p_.codomain()
    sage: C.generator_degrees()
    (4, 5)
    sage: C.relations()
    [<Sq(6), Sq(5)>]
    sage: p_.codomain().connectivity()
    4
    sage: mono = p_.image()
    sage: mono.domain()
    Finitely presented module on 2 generators and 1 relation over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [3, 2, 1]

AUTHORS:

    - Robert R. Bruner, Michael J. Catanzaro (2012): initial version
    - Koen (date in ISO year-month-day format): Updating to Sage 8.1
    - Sverre A. Lunoee-Nielsen (2020-01-11): Rewritten and refactored, and updated to Sage 8.9.

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


from __future__ import absolute_import
from __future__ import print_function

import sys


from sage.categories.homset import Hom
from sage.categories.morphism import Morphism as SageMorphism
from sage.modules.free_module import VectorSpace
from sage.rings.infinity import PlusInfinity
from sage.misc.cachefunc import cached_method

from sage.modules.fp_modules.fp_homspace import is_FP_ModuleHomspace
from sage.modules.fp_modules.fp_element import FP_Element

from sage.structure.unique_representation import UniqueRepresentation

class FP_ModuleMorphism(SageMorphism):

    def __init__(self, parent, values):
        r"""
        Create a homomorphism between finitely presented graded modules.

        INPUT:

        - ``parent`` -- A homspace in a (sub) category of fp modules.
        - ``values`` -- A list of elements in the codomain.  Each element
          corresponds to a module generator in the domain.

        OUTPUT: A module homomorphism defined by sending generator with index
        `i` to the element in the comdomain which has index `i` in the given
        input list.


        TESTS:
            sage: from sage.modules.fp_modules.fp_module import FP_Module
            sage: # Trying to map the generators of a non-free module into a
            sage: # free module:
            sage: A = SteenrodAlgebra(2)
            sage: F = FP_Module([2,3], A)
            sage: Q = FP_Module([2,3], A, relations=[[Sq(6), Sq(5)]])
            sage: m = Hom(F, Q)( (F((Sq(1), 0)), F((0, 1))) )
            Traceback (most recent call last):
             ...
            ValueError: Ill defined homomorphism (degrees do not match)
                  Generator #0 (degree 2) -> <Sq(1), 0> (degree 3) shifts degrees by 1
                  Generator #1 (degree 3) -> <0, 1> (degree 3) shifts degrees by 0

            sage: # Trying to map the generators of a non-free module into a
            sage: # free module:
            sage: w = Hom(Q, F)( (F((1, 0)), F((0, 1))) )
            Traceback (most recent call last):
             ...
            ValueError: Relation <Sq(6), Sq(5)> is not sent to zero.

        """
        if not is_FP_ModuleHomspace(parent):
            raise TypeError("parent (=%s) must be a fp module hom space" % parent)

        self.free_morphism = Hom(parent.domain().j.codomain(), parent.codomain().j.codomain())([v.free_element for v in values])
        self._values = values

        # Call the base class constructor.
        SageMorphism.__init__(self, parent)

        # Check that the homomorphism is well defined.
        for relation in parent.domain().j.values():
            # The relation is an element in the free part of the domain.
            if not FP_Element(parent.codomain(), self.free_morphism(relation)).is_zero():
                raise ValueError("Relation %s is not sent to zero." % relation)

    def change_ring(self, algebra):
        r"""
        Change the base ring of this module homomorphism.

        INPUT:
        - ``algebra`` -- a graded algebra.

        OUTPUT: An instance of this class.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import FP_Module
            sage: A2 = SteenrodAlgebra(2, profile=(3,2,1))
            sage: A3 = SteenrodAlgebra(2, profile=(4,3,2,1))
            sage: M = FP_Module([0], A2, relations=[[Sq(1)]])
            sage: N = FP_Module([0], A2, relations=[[Sq(4)],[Sq(1)]])
            sage: f = Hom(M,N)([A2.Sq(3)*N.generator(0)]); f
            Module homomorphism of degree 3 defined by sending the generators
              [<1>]
            to
              [<Sq(3)>]
            sage: f.base_ring()
            sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [3, 2, 1]
            sage: g = f.change_ring(A3)
            sage: g.base_ring()
            sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [4, 3, 2, 1]

        """
        new_codomain = self.codomain().change_ring(algebra)
        new_values = [new_codomain(v.coefficients()) for v in self._values]
        return Hom(self.domain().change_ring(algebra), new_codomain)(new_values)

    def degree(self):
        r"""
        The degree of this homomorphism.

        OUTPUT: the integer degree of this homomorphism, or None if this is
        the zero homomorphism.

        EXAMPLES:

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: homspace = Hom(FP_Module((0,1), A), FP_Module((2,), A))
            sage: N = homspace.codomain()
            sage: values = [Sq(3)*Sq(2)*N.generator(0), Sq(3)*Sq(1)*N.generator(0)]
            sage: f = homspace(values)
            sage: f.degree()
            5

        The zero homomorphism has no degree::

            sage: homspace.zero().degree() is None
            True

        """
        return self.free_morphism.degree()

    def values(self):
        r"""
        The values under this homomorphism of the module generators of the
        domain module.

        OUTPUT: A sequence of module elements of the codomain.

        EXAMPLES:

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: homspace = Hom(FP_Module((0,1), A), FP_Module((2,), A))
            sage: N = homspace.codomain()
            sage: values = [Sq(3)*Sq(2)*N.generator(0), Sq(3)*Sq(1)*N.generator(0)]
            sage: f = homspace(values)
            sage: f.values()
            [<0>, <Sq(1,1)>]
            sage: homspace.zero().values()
            [<0>, <0>]

        """
        return self._values

    def _richcmp_(self, other, op):
        r"""
        Compare this homomorphism to the given homomorphism.

        INPUT:

        - ``other`` -- An instance of this class.

        - ``op`` -- An integer specifying the comparison operation to be
          carried out: If ``op`` == 2, then return ``True`` if and only if the
          homomorphisms are equal.  If ``op`` == 3, then return ``True `` if
          and only if the homomorphisms are not equal.  Otherwise,
          return ``False``.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: homspace = Hom(FP_Module((0,1), A), FP_Module((2,), A))
            sage: N = homspace.codomain()
            sage: values = [Sq(3)*Sq(2)*N.generator(0), Sq(3)*Sq(1)*N.generator(0)]
            sage: f = homspace(values)
            sage: f._richcmp_(f, op=2)
            True
            sage: f._richcmp_(f, op=3)
            False

        """
        try:
            same = (self - other).is_zero()
        except ValueError:
            return False

        # Equality
        if op == 2:
            return same

        # Non-equality
        if op == 3:
            return not same

        return False


    def __add__(self, g):
        r"""
        The pointwise sum of this and the given homomorphism.

        Pointwise addition of two homomorphisms `f` and `g` with the same domain
        and codomain is given by the formula `(f+g)(x) = f(x) + g(x)` for
        every `x` in the domain of `f`.

        INPUT:

        - ``g`` -- A homomorphism with the same domain and codomain as this
          homomorphism.

        OUTPUT: The pointwise sum homomorphism of this and the given
        homomorphism.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: homspace = Hom(FP_Module([0,1], A), FP_Module([2], A))
            sage: N = homspace.codomain()
            sage: values = [Sq(3)*Sq(2)*N.generator(0), Sq(3)*Sq(1)*N.generator(0)]
            sage: f = homspace(values)
            sage: ff = f.__add__(f)
            sage: ff.is_zero()
            True
            sage: ff.__add__(f) == f
            True

        """

        if self.domain() != g.domain():
            raise ValueError("Morphisms do not have the same domain.")
        elif self.codomain() != g.codomain():
            raise ValueError("Morphisms do not have the same codomain.")
        elif self.degree() and g.degree() and self.degree() != g.degree():
            raise ValueError("Morphisms do not have the same degree.")

        v = [self(x) + g(x) for x in self.domain().generators()]

        return self.parent()(v)

    def __neg__(self):
        r"""
        The additive inverse of this homomorphism with respect to the group
        structure given by pointwise sum.

        OUTPUT: An instance of this class.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: homspace = Hom(FP_Module((0,1), A), FP_Module((2,), A))
            sage: N = homspace.codomain()
            sage: values = [Sq(3)*Sq(2)*N.generator(0), Sq(3)*Sq(1)*N.generator(0)]
            sage: f = homspace(values)
            sage: f_inverse = f.__neg__(); f_inverse
            Module homomorphism of degree 5 defined by sending the generators
              [<1, 0>, <0, 1>]
            to
              [<0>, <Sq(1,1)>]
            sage: (f + f_inverse).is_zero()
            True

        """
        return self.parent()([-x for x in self._values])

    def __sub__(self, g):
        r"""
        The difference between this and the given homomorphism, with
        respect to the group structure given by pointwise sum.

        OUTPUT: The difference homomorphism.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: homspace = Hom(FP_Module((0,1), A), FP_Module((2,), A))
            sage: N = homspace.codomain()
            sage: values = [Sq(3)*Sq(2)*N.generator(0), Sq(3)*Sq(1)*N.generator(0)]
            sage: f = homspace(values)
            sage: values2 = [Sq(3)*Sq(2)*N.generator(0), Sq(3)*Sq(1)*N.generator(0)]
            sage: g = homspace(values2)
            sage: f.__sub__(g)
            The trivial homomorphism.

        """
        return self.__add__(g.__neg__())

    def __mul__(self, g):
        r"""
        The composition of the given homomorphism ``g``, followed by this
        homomorphisms.

        OUTPUT: A homomorphism from the domain of this homomorphism, into the
        codomain of the homomorphism ``g``.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FP_Module((0,1), A)
            sage: N = FP_Module((2,), A)
            sage: values = [Sq(3)*Sq(2)*N.generator(0), Sq(3)*Sq(1)*N.generator(0)]
            sage: f = Hom(M, N)(values)
            sage: values2 = [Sq(2)*M.generator(0)]
            sage: g = Hom(N, M)(values2)
            sage: fg = f.__mul__(g); fg
            The trivial homomorphism.
            sage: fg.is_endomorphism()
            True

        TESTS::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FP_Module((0,1), A)
            sage: values = [Sq(3)*Sq(2)*N.generator(0), Sq(3)*Sq(1)*N.generator(0)]
            sage: f = Hom(M, N)(values)
            sage: f.__mul__(f)
            Traceback (most recent call last):
            ...
            ValueError: Morphisms not composable.

        """
        if self.parent().domain() != g.parent().codomain():
            raise ValueError("Morphisms not composable.")
        homset = Hom(g.parent().domain(), self.parent().codomain())
        return homset([self(g(x)) for x in g.domain().generators()])

    @cached_method
    def is_zero(self):
        r"""
        Decide if this homomomorphism is trivial.

        OUTPUT: ``True`` if this homomorphism is trivial, and ``False``
        otherwise.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FreeModule((0,1), A)
            sage: N = FreeModule((2,), A)
            sage: values = [Sq(3)*Sq(2)*N.generator(0), Sq(3)*Sq(1)*N.generator(0)]
            sage: f = Hom(M, N)(values)
            sage: f.is_zero()
            False
            sage: (f-f).is_zero()
            True

        """
        return all([x.is_zero() for x in self._values])

    @cached_method
    def is_identity(self):
        r"""
        Decide if this homomomorphism is the identity endomorphism.

        OUTPUT: ``True`` if this homomorphism is the identity, and ``False``
        otherwise.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FP_Module((0,1), A)
            sage: N = FP_Module((2,), A)
            sage: values = [Sq(3)*Sq(2)*N.generator(0), Sq(3)*Sq(1)*N.generator(0)]
            sage: f = Hom(M, N)(values)
            sage: f.is_identity()
            False
            sage: id = Hom(M, M)(M.generators()); id
            The identity homomorphism.
            sage: id.is_identity()
            True
        """

        if self.parent().is_endomorphism_set():
            # XXX I think this doesn't work.  We need to compare
            #     id.values <-> self._values as FP_Modules.
            return self.parent().identity() == self
        else:
            return False


    def __call__(self, x):
        r"""
        Evaluate the homomorphism at the given domain element ``x``.

        INPUT:

        -  ``x``  - An element of the domain of the homomorphism.

        OUTPUT: The module element of the codomain which is the value of ``x``
        under this homomorphism.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FP_Module((0,1), A)
            sage: N = FP_Module((2,), A)
            sage: values = [Sq(3)*Sq(2)*N.generator(0), Sq(3)*Sq(1)*N.generator(0)]
            sage: f = Hom(M, N)(values)
            sage: f.__call__(M.generator(0))
            <0>
            sage: f.__call__(M.generator(1))
            <Sq(1,1)>

        """

        if x.parent() != self.domain():
            raise ValueError("Cannot evaluate morphism on element not in domain.")

#        return self.codomain().element_class(self.codomain(), self.free_morphism(x.free_element)).normalize()
        return self.codomain().element_class(self.codomain(), self.free_morphism(x.free_element))

    def _repr_(self):
        r"""
        A string representation of this homomorphism.

        OUTPUT: A string.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FreeModule((0,1), A)
            sage: N = FreeModule((2,), A)
            sage: values = [Sq(3)*Sq(2)*N.generator(0), Sq(3)*Sq(1)*N.generator(0)]
            sage: Hom(M, N)(values)._repr_()
            'Module homomorphism of degree 5 defined by sending the generators\n  [<1, 0>, <0, 1>]\nto\n  [<0>, <Sq(1,1)>]'
            sage: Hom(M, N).zero()._repr_()
            'The trivial homomorphism.'
            sage: Hom(M, M).identity()._repr_()
            'The identity homomorphism.'

        """

        if self.is_zero():
            return "The trivial homomorphism."
        elif self.is_identity():
            return "The identity homomorphism."
        else:
            return "Module homomorphism of degree %d defined by sending "\
                "the generators\n  %s\nto\n  %s" % (self.degree(), self.domain().generators(), self._values)

    @cached_method
    def vector_presentation(self, n):
        r"""
        The restriction of this homomorphism to the domain module elements of
        degree ``n``.

        The restriction of a module homomorphism to the vectorspace of module
        elements of degree `n` is a linear function into the vectorspace of
        elements of degree `n+d` belonging to the codomain.  Here `d` is the
        degree of this homomorphism.

        INTPUT:

        - ``n`` -- An integer degree.

        OUTPUT: A linear function over finite dimensional vectorspaces over the
        ground field of the algebra for this module.  The domain of this
        linear function is isomorphic to the vectorspace of domain elements
        of degree ``n`` of this free module, via the choice of basis given
        by :meth:`sage.modules.fp_modules.fp_module.basis_elements`.

        .. SEEALSO::
            :meth:`sage.modules.fp_modules.fp_module.fp_homspace.domain`, 
            :meth:`sage.modules.fp_modules.fp_module.fp_homspace.codomain`,
            :meth:`sage.modules.fp_modules.fp_module.fp_module.vector_presentation`,
            :meth:`sage.modules.fp_modules.fp_module.fp_module.basis_elements`.

        """

        self_degree = self.degree() if self.degree() != None else 0
        codomain_degree = self_degree + n

        D_n = self.domain().vector_presentation(n)
        C_n = self.codomain().vector_presentation(codomain_degree)

        if self.degree() == None:
            return Hom(D_n, C_n).zero()

        # The member function FP_ModuleElement.vector_presentation() can
        # return None for the zero element.
        none_to_zero = lambda v: C_n.zero() if v == None else v

        values = [none_to_zero(self(\
                self.domain().element_from_coordinates(x, n)\
            ).vector_presentation()) for x in D_n.basis()]

        return Hom(D_n, C_n)(values)


    def solve(self, x):
        r"""
        Find an element mapping to ``x`` under this morphism.

        INPUT:

        - ``x`` -- The element we want to lift.

        OUTPUT: An element which maps to ``x`` under this morphism, or
        ``None`` if ``x`` was not in the image of this morphism.

        """

        if x.parent() != self.codomain():
            raise ValueError("The given element is not in the codomain of this homomorphism.")

        if x.is_zero():
            return self.domain().zero()

        n = x.degree() - self.degree()
        f_n = self.vector_presentation(n)

        v = x.vector_presentation()
        if not v in f_n.image():
            print("The given element is not in the image of this homomorphism.")
            return None
        u = f_n.matrix().solve_left(v)
        return self.domain().element_from_coordinates(u, n)


    def lift(self, f):
        """
        Lift this homomorphism over the given map.

        OUTPUT:: A homomorphism f' such that f*f' = self.

        """

        if self.codomain() != f.codomain():
            raise TypeError('Cannot lift this homomorphism over the given map since it has a different codomain.')

        new_values = [f.solve(self(g)) for g in self.domain().generators()]

        return Hom(self.domain(), f.domain())(new_values)


    def homology(self, f):
        r"""
        The quotient $H(self, f) = \ker(self)/\im(f)$.

        OUTPUT:: The quotient homomorphism ker(self) ->> H(self, f).

        """
        k = self.kernel()
        f_ = f.lift(k)
        return f_.cokernel()


    def suspension(self, degree):
        """

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: F1 = FP_Module((4,5), A)
            sage: F2 = FP_Module((3,4), A)
            sage: H1 = Hom(F1, F2)
            sage: f = H1( ( F2((Sq(1), 0)), F2((0, Sq(1))) ) ); f
            Module homomorphism of degree 0 defined by sending the generators
              [<1, 0>, <0, 1>]
            to
              (<Sq(1), 0>, <0, Sq(1)>)
            sage: e1 = F1((1, 0))
            sage: e2 = F1((0, 1))
            sage: f(e1)
            <Sq(1), 0>
            sage: f(e2)
            <0, Sq(1)>
            sage: sf = f.suspension(4); sf
            Module homomorphism of degree 0 defined by sending the generators
              [<1, 0>, <0, 1>]
            to
              [<Sq(1), 0>, <0, Sq(1)>]
        """
        if degree == 0:
            return self
        else:
            D = self.domain().suspension(degree)
            C = self.codomain().suspension(degree)
            return Hom(D, C)([D(x.free_element.coefficients()) for x in self._values])

    def cokernel(self):
        r"""
        Compute the cokernel of this homomorphism.

        ALGORITHM: The Cokernel is on same degs as codomain,
        with rels = codomain.rels + self._values. Returns cokernel and the
        projection map to it.

        OUTPUT: The natural projection from self.codomain to `coker`.

        EXAMPLES::

        """

        new_relations = [x.coefficients() for x in self.codomain().relations()] +\
            [x.coefficients() for x in self._values]

        #from .fp_module import FP_Module
        coker = self.domain().ModuleClass(
                    self.codomain().generator_degrees(),
                    self.base_ring(),
                    relations=tuple(new_relations))

        projection = Hom(self.codomain(), coker)(coker.generators())

        return projection

    def kernel(self, top_dim=None, verbose=False):
        """
        Compute the kernel of this homomorphism.

        INPUT:

        - ``verbose`` -- Boolean to enable progress updates.

        - ``top_dim`` -- Optional stop condition.  The computation of the kernel will
          stop when reaching this dimension.  The returned module will match the kernel
          in degrees up to dimension `top_dim` only.

        OUTPUT: An injective homomorphism into the domain of `self` which is
               onto the kernel of this homomorphism.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import *
            sage: A3 = SteenrodAlgebra(2, profile=(4,3,2,1))
            sage: F = FP_Module([1,3], A3);
            sage: L = FP_Module([2,3], A3, [[Sq(2),Sq(1)], [0,Sq(2)]]);
            sage: H = Hom(F, L);
            sage: H([L((Sq(1), 1)), L((0, Sq(2)))]).kernel()
            Module homomorphism of degree 0 defined by sending the generators
              [<1, 0>, <0, 1>]
            to
              (<0, 1>, <Sq(0,1), 0>)
            sage: M = FP_Module([0,7], A3, [[Sq(1), 0], [Sq(2), 0], [Sq(4), 0], [Sq(8), Sq(1)], [0, Sq(7)], [0, Sq(0,1,1)+Sq(4,2)]])
            sage: F2 = FP_Module([0], A3, [[Sq(1)], [Sq(2)], [Sq(4)], [Sq(8)], [Sq(15)]])
            sage: H = Hom(M, F2)
            sage: f = H([F2([1]), F2([0])])
            sage: K = f.kernel(verbose=True, top_dim=17)
            1. Computing the generators of the kernel presentation:
            Resolving the kernel in the range of dimensions [0, 17]: 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17.
            2. Computing the relations of the kernel presentation:
            Resolving the kernel in the range of dimensions [7, 17]: 7 8 9 10 11 12 13 14 15 16 17.
            sage: K.domain().generators()
            [<1>]
            sage: K.domain().relations()
            [<Sq(0,1) + Sq(3)>,
             <Sq(0,0,1) + Sq(1,2) + Sq(4,1)>,
             <Sq(9)>,
             <Sq(0,1,1) + Sq(4,2)>]
            sage: K
            Module homomorphism of degree 0 defined by sending the generators
              [<1>]
            to
              (<0, 1>,)
        """
        if verbose:
            print('1. Computing the generators of the kernel presentation:')
        j0 = self.resolve_kernel(top_dim, verbose)
        if verbose:
            print('2. Computing the relations of the kernel presentation:')
        j1 = j0.resolve_kernel(top_dim, verbose)

        # Create a module isomorphic to the ker(self).
        K = self.domain().ModuleClass.from_free_module_morphism(j1)

        # Return an injection of K into the domain of self such that
        # its image equals ker(self).
        return Hom(K, j0.codomain())(j0.values())

    def image(self, top_dim=None, verbose=False):
        r"""
        Compute the image of this homomorphism.

        OUTPUT: An injective homomorphism into the codomain of `self` which is
                onto the image of this homomorphism.

        EXAMPLES:
            sage: from sage.modules.fp_modules.fp_module import *
            sage: A3 = SteenrodAlgebra(2, profile=(4,3,2,1))
            sage: F = FP_Module([1,3], A3);
            sage: L = FP_Module([2,3], A3, [[Sq(2),Sq(1)], [0,Sq(2)]]);
            sage: H = Hom(F, L);
            sage: H([L((Sq(1), 1)), L((0, Sq(2)))]).image()
            Module homomorphism of degree 0 defined by sending the generators
              [<1>]
            to
              (<Sq(1), 1>,)
            sage: M = FP_Module([0,7], A3, [[Sq(1), 0], [Sq(2), 0], [Sq(4), 0], [Sq(8), Sq(1)], [0, Sq(7)], [0, Sq(0,1,1)+Sq(4,2)]])
            sage: F2 = FP_Module([0], A3, [[Sq(1)], [Sq(2)], [Sq(4)], [Sq(8)], [Sq(15)]])
            sage: H = Hom(M, F2)
            sage: f = H([F2([1]), F2([0])])
            sage: K = f.image(verbose=True, top_dim=17)
            1. Computing the generators of the image presentation:
            Resolving the image in the range of dimensions [0, 17]: 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17.
            2. Computing the relations of the image presentation:
            Resolving the kernel in the range of dimensions [0, 17]: 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17.
            sage: K.is_injective()
            True
            sage: K.domain().generator_degrees()
            (0,)
            sage: K.domain().relations()
            [<Sq(1)>, <Sq(2)>, <Sq(4)>, <Sq(8)>]
            sage: K.domain().is_trivial()
            False

        """
        if verbose:
            print('1. Computing the generators of the image presentation:')
        j0 = self.resolve_image(top_dim, verbose)
        if verbose:
            print('2. Computing the relations of the image presentation:')
        j1 = j0.resolve_kernel(top_dim, verbose)

        # Create a module isomorphic to the im(self).
        I = self.domain().ModuleClass.from_free_module_morphism(j1)

        # Return an injection of I into the codomain of self such that
        # its image equals im(self)
        return Hom(I, j0.codomain())(j0.values())

    def is_injective(self, top_dim=None, verbose=False):
        r"""
        Return True if and only if this homomorphism has a trivial kernel.
        """
        j0 = self.resolve_kernel(top_dim, verbose)
        return j0.domain().is_trivial()

    def is_surjective(self):
        r"""
        Return True if and only if this homomorphism has a trivial cokernel.
        """
        return self.cokernel().is_zero()


#    def resolve_image(self, top_dim=None, verbose=False):
#        r"""
#            Resolve the image of this homomorphism.
#
#        INPUT::
#            self
#            top_dim
#
#        OUTPUT::
#            j: F -> self.codomain()  such that F is free, and im(j) = im(self).
#
#        """
#
#
#        # Select those generators which has values in degrees <= limit.
#        limit = top_dim if top_dim != None else PlusInfinity()
#        deg = self.degree()
#        # By shifting the dimensions of each generator by `deg`, we make sure
#        # that the resulting homomorphism has degree zero.
#        gens = [g + deg for g in self.domain().generator_degrees() if g + deg <= limit]
#        vals = [v for v in self.values() if v.degree() <= limit]
#
#        # Create the free module on the selected generators.
#        F_0 = self.codomain().ModuleClass(tuple(gens), self.base_ring())
#
#        epsilon = Hom(F_0, self.codomain())(tuple(vals))
#
#        return epsilon


    def resolve_kernel(self, top_dim=None, verbose=False):
        r"""
            Resolve the kernel of this homomorphism.

        INPUT::

        OUTPUT::
            j: F_ -> D = self.domain() such that the sequence

                   j        self
              F_ -----> D --------> C

            is exact.

        """

        # The main loop starts each iteration assuming
        # that `j` a homomorphism into `self.domain()`, and 'n' is an integer
        # such that
        #
        #       j      self
        #   F_ ---> D ------> C
        #
        # with `\im(j) \subset \ker(self)` and that `j` is an onto the kernel
        # in degrees below `n`.  Each iteration of the loop then extends the
        # map `j` minimally so that `j_n` bebcomes onto the kernel.

        # Create the trivial module F_ to start with.
        #from .fp_module import FP_Module
        F_ = self.domain().__class__((), algebra=self.base_ring())
        j = Hom(F_, self.domain())(())

        dim = self.domain().connectivity()
        if dim == PlusInfinity():
            if verbose:
                print ('The domain of the morphism is trivial, so there is nothing to resolve.')
            return j

        limit = PlusInfinity() if not self.base_ring().is_finite() else\
            (self.base_ring().top_class().degree() + max(self.domain().generator_degrees()))

        if not top_dim is None:
            limit = min(top_dim, limit)

        if top_dim == PlusInfinity():
            raise ValueError('The user must specify a top dimension for this calculation to terminate.')

        if verbose:
            if dim > limit:
                print('The dimension range is empty: [%d, %d]' % (n, limit))
            else:
                print('Resolving the kernel in the range of dimensions [%d, %d]:' % (dim, limit), end='')

        for n in range(dim, limit+1):

            if verbose:
                print(' %d' % n, end='')
                sys.stdout.flush()

            self_n = self.vector_presentation(n)
            kernel_n = self_n.kernel()

            if kernel_n.dimension() == 0:
                continue

            j_n = j.vector_presentation(n)
            Q_n = kernel_n.quotient(j_n.image())

            if Q_n.dimension() == 0:
                continue

            # The map j does not cover everything in degree `n` of the kernel.
            # Extend it.
            generator_degrees = tuple((x.degree() for x in F_.generators()))
            new_generator_degrees = tuple(Q_n.dimension()*(n,))
            F_ = self.domain().__class__(generator_degrees + new_generator_degrees, algebra=self.base_ring())

            new_values = tuple([
                self.domain().element_from_coordinates(Q_n.lift(q), n) for q in Q_n.basis()])

            j = Hom(F_, self.domain()) (j.values() + new_values)

        if verbose:
            print('.')
        return j


    def resolve_image(self, top_dim=None, verbose=False):
        r"""
            Resolve the image of this homomorphism.

        INPUT::

        OUTPUT::
            j: F_ -> C = self.codomain() such that im(j) = im(self).


        TESTS::
            sage: from sage.modules.fp_modules.fp_module import *
            sage: A3 = SteenrodAlgebra(2, profile=(4,3,2,1))
            sage: F = FP_Module([0,0], A3)
            sage: L = FP_Module([0,0], A3, [[Sq(3),Sq(0,1)], [0,Sq(2)]])
            sage: f = Hom(F, L)([L([Sq(2),0]), L([0, Sq(2)])])
            sage: f.resolve_image() # Test degree-shifting and getting rid of the uneccessary generator.
            Module homomorphism of degree 0 defined by sending the generators
              [<1>]
            to
              (<Sq(2), 0>,)

        """

        # The main loop starts each iteration assuming
        # that `j` a homomorphism into `self.codomain()`, and 'n' is an integer
        # such that
        #
        #       j         self
        #   F_ ---> C <---------- D
        #
        # with `\im(j) \subset \im(self)` and that `j` is an onto the image
        # in degrees below `n`.  Each iteration of the loop then extends the
        # map `j` minimally so that `j_n` becomes onto the image.

        # Create the trivial module F_ to start with.
        #from .fp_module import FP_Module
        F_ = self.domain().__class__((), algebra=self.base_ring())
        j = Hom(F_, self.codomain())(())

        dim = self.codomain().connectivity()
        if dim == PlusInfinity():
            if verbose:
                print ('The codomain of the morphism is trivial, so there is nothing to resolve.')
            return j

        self_degree = self.degree()
        if self_degree is None:
            if verbose:
                print ('The homomorphism is trivial, so there is nothing to resolve.')
            return j

        degree_values = [0] + [v.degree() for v in self.values() if v.degree() != None]
        limit = PlusInfinity() if not self.base_ring().is_finite() else\
            (self.base_ring().top_class().degree() + max(degree_values))

        if not top_dim is None:
            limit = min(top_dim, limit)

        if top_dim == PlusInfinity():
            raise ValueError('The user must specify a top dimension for this calculation to terminate.')

        if verbose:
            if dim > limit:
                print('The dimension range is empty: [%d, %d]' % (n, limit))
            else:
                print('Resolving the image in the range of dimensions [%d, %d]:' % (dim, limit), end='')

        for n in range(dim, limit+1):

            if verbose:
                print(' %d' % n, end='')
                sys.stdout.flush()

            self_n = self.vector_presentation(n - self_degree)
            image_n = self_n.image()

            if image_n.dimension() == 0:
                continue

            j_n = j.vector_presentation(n)
            Q_n = image_n.quotient(j_n.image())

            if Q_n.dimension() == 0:
                continue

            # The map j does not cover everything in degree `n` of the kernel.
            # Extend it.
            generator_degrees = tuple((x.degree() for x in F_.generators()))
            new_generator_degrees = tuple(Q_n.dimension()*(n,))
            F_ = self.domain().__class__(generator_degrees + new_generator_degrees, algebra=self.base_ring())

            new_values = tuple([
                self.codomain().element_from_coordinates(Q_n.lift(q), n) for q in Q_n.basis()])

            j = Hom(F_, self.codomain()) (j.values() + new_values)

        if verbose:
            print('.')
        return j
