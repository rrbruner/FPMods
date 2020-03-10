r"""
Homomorphisms of finitely presented graded modules

This class implements construction and basic manipulation of homomorphisms
between finitely presented graded modules, modelled by the Sage parent
:class:`sage.modules.fp_modules.fp_module.FP_Module`.

The category of finitely presented graded modules over an arbitrary graded ring
is not Abelian in general, since kernels of homomorphisms are not neccessarily
finitely presented.  If, however, the ring is Noetherian, or more generally 
a `P`-algebra ([Marg1983]_ Ch. 13), then modules are coherent and the
category of finitely presented modules is Abelian.  The `mod p` Steenrod 
algebra is an example of a non-Noetherian `P`-algebra which give rise to
an Abelian module category.

This methods of this homomorphism class recognizes the most trivial case of
coherency: finite, hence trivially Noetherian, graded rings.

The implication of working over a non-finite graded ring is that the function
that computes the kernel of a homomorphism will never terminate.  For this 
reason, the functions that depend on computation of the homomorphism kernels,
allow the user to impose a stop condition given by the maximum degree for which
the computation should be performed.

This class is intended for private use by the class
:class:`sage.modules.fp_modules.fpa_morphism.FPA_ModuleMorphism` modelling
homomorphisms between finitely presented modules over the Steenrod algebra.

EXAMPLES::

The construction of a homomorphism is done by specifying the values of the
module generators of the domain::

    sage: from sage.modules.fp_modules.fp_module import FP_Module
    sage: A = SteenrodAlgebra(2)
    sage: F1 = FP_Module([4,5], A)
    sage: F2 = FP_Module([3,4], A)
    sage: values = [ F2((Sq(1), 0)), F2((0, Sq(1))) ]
    sage: f = Hom(F1, F2)(values); f

Homomorphisms can be evaluated on elements of the domain module::

    sage: x = F1.generator(0)
    sage: y = f(x); y
    sage: y in f.codomain()
    True

Module homomorphisms are linear and respect to the module action::

    sage: Sq(3)*y == f(Sq(3)*x)
    True
    sage: x2 = F1.generator(1)
    sage: f(Sq(1)*x + x2) == Sq(1)*y + f(x2)

Homomorphisms have well defined degrees::

    sage: f.degree()

Homomorphisms of equal degree form a group under pointwise addition::

    sage: values2 = [ F2((Sq(1), 0)), F2((Sq(2), Sq(1))) ]
    sage: f2 = Hom(F1, F2)(values2); f2
    sage: f + f2
    sage: values3 = [ F2((0, 0)), F2((Sq(2), 0)) ]
    sage: f3 = Hom(F1, F2)(values3); f3
    sage: f3 == f - f2

Composition of homomorphisms can be performed as expected::

    sage: Q = FP_Module((2,3), A, relations=[[Sq(6), Sq(5)]]); Q
    Finitely presented module on 2 generators and 1 relation ...
    sage: H2 = Hom(F2, Q)
    sage: g = H2( ( Q((Sq(4), 0)), Q((0, Sq(1,1))) ) )
    sage: g*f
    The trivial homomorphism.
    sage: f*g
    Traceback (most recent call last):
     ...
    ValueError: Morphisms not composable.

#    sage: w = Hom(F1, F1)(( F1((Sq(6), Sq(5))), F1(0) )); w
#    Module homomorphism of degree 6 defined by sending the generators
#      [<1, 0>, <0, 1>]
#    to
#      (<Sq(6), Sq(5)>, <0, 0>)

The kernel of a homomorphism `g` is given via its natural injection into the
domain of `g`::

    sage: i = g.kernel(top_dim=10)
    sage: i.codomain() is g.domain()
    True
    sage: i.domain()
    Finitely presented module on 1 generator and 0 relations over mod 2 Steenrod algebra, milnor basis
    sage: i
    Module homomorphism of degree 0 defined by sending the generators
      [<1>]
    to
      (<Sq(6), Sq(5)>,)

The cokernel of a homomorphism `g` is given via its natural projection
`p: codomain(g) \rightarrow cokernel(g)`::

    sage: p = g.cokernel()
    sage: p.domain() is g.codomain()
    True
    sage: p.codomain()
    Finitely presented module on 2 generators and 1 relation over mod 2 Steenrod algebra, milnor basis
    sage: p.codomain().relations()
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
from sage.misc.cachefunc import cached_method
from sage.modules.fp_modules.fp_homspace import is_FP_ModuleHomspace
from sage.modules.fp_modules.fp_element import FP_Element
from sage.modules.free_module import VectorSpace
from sage.rings.infinity import PlusInfinity
from sage.structure.unique_representation import UniqueRepresentation


class FP_ModuleMorphism(SageMorphism):

    def __init__(self, parent, values):
        r"""
        Create a homomorphism between finitely presented graded modules.

        INPUT:

        - ``parent`` -- A homspace of finitely presented graded modules.
        - ``values`` -- A list of elements in the codomain.  Each element
          corresponds to a module generator in the domain.

        OUTPUT: A module homomorphism defined by sending generator with index
        `i` to the element in the comdomain which has index `i` in the given
        input list ``values``.


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
            sage: M = FP_Module([0,1], A, [[Sq(2), Sq(1)]])
            sage: N = FP_Module([2], A, [[Sq(4)]])
            sage: homspace = Hom(M, N)
            sage: values = [Sq(5)*N.generator(0), Sq(3,1)*N.generator(0)]
            sage: f = homspace(values)
            sage: f.degree()
            7

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
            sage: M = FP_Module([0,1], A, [[Sq(2), Sq(1)]])
            sage: N = FP_Module([2], A, [[Sq(4)]])
            sage: homspace = Hom(M, N)
            sage: values = [Sq(5)*N.generator(0), Sq(3,1)*N.generator(0)]
            sage: f = homspace(values)
            sage: f.values()
            [<Sq(5)>, <Sq(3,1)>]
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
            sage: M = FP_Module([0,1], A, [[Sq(2), Sq(1)]])
            sage: N = FP_Module([2], A, [[Sq(4)]])
            sage: homspace = Hom(M, N)
            sage: values = [Sq(5)*N.generator(0), Sq(3,1)*N.generator(0)]
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
            sage: M = FP_Module([0,1], A, [[Sq(2), Sq(1)]])
            sage: N = FP_Module([2], A, [[Sq(4)]])
            sage: homspace = Hom(M, N)
            sage: values = [Sq(5)*N.generator(0), Sq(3,1)*N.generator(0)]
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
            sage: M = FP_Module([0,1], A, [[Sq(2), Sq(1)]])
            sage: N = FP_Module([2], A, [[Sq(4)]])
            sage: homspace = Hom(M, N)
            sage: values = [Sq(5)*N.generator(0), Sq(3,1)*N.generator(0)]
            sage: f = homspace(values)
            sage: f_inverse = f.__neg__(); f_inverse
            Module homomorphism of degree 7 defined by sending the generators
              [<1, 0>, <0, 1>]
            to
              [<Sq(5)>, <Sq(3,1)>]
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
            sage: M = FP_Module([0], A)
            sage: N = FP_Module([0], A, [[Sq(2)]])
            sage: f = Hom(M, N)( [Sq(4)*N.generator(0)] )
            sage: g = Hom(M, N)( [Sq(2)*Sq(2)*N.generator(0)] )
            sage: f.__sub__(g)
            Module homomorphism of degree 4 defined by sending the generators
              [<1>]
            to
              [<Sq(1,1) + Sq(4)>]

        """
        return self.__add__(g.__neg__())


    def __mul__(self, g):
        r"""
        The composition of the given homomorphism ``g``, followed by this
        homomorphisms.

        OUTPUT: A homomorphism from the domain of this homomorphism, into the
        codomain of the homomorphism ``g``.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import FP_Module
            sage: A = SteenrodAlgebra(2)
            sage: M = FP_Module([0], A, [[Sq(1,2)]])
            sage: N = FP_Module([0], A, [[Sq(2,2)]])
            sage: f = Hom(M, N)( [Sq(2)*N.generator(0)] )
            sage: g = Hom(N, M)( [Sq(2,2)*M.generator(0)] )
            sage: fg = f.__mul__(g); fg
            Module homomorphism of degree 10 defined by sending the generators
              [<1>]
            to
              [<Sq(0,1,1) + Sq(1,3) + Sq(3,0,1)>]
            sage: fg.is_endomorphism()
            True

        TESTS::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FP_Module((0,1), A)
            sage: values = [Sq(5)*N.generator(0), Sq(3,1)*N.generator(0)]
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

            sage: from sage.modules.fp_modules.fp_module import FP_Module
            sage: A = SteenrodAlgebra(2)
            sage: M = FP_Module([0,1], A, [[Sq(2), Sq(1)]])
            sage: N = FP_Module([2], A, [[Sq(4)]])
            sage: values = [Sq(5)*N.generator(0), Sq(3,1)*N.generator(0)]
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
            sage: M = FP_Module([0,1], A, [[Sq(2), Sq(1)]])
            sage: N = FP_Module([2], A, [[Sq(4)]])
            sage: values = [Sq(5)*N.generator(0), Sq(3,1)*N.generator(0)]
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
            sage: M = FP_Module([0,1], A, [[Sq(2), Sq(1)]])
            sage: N = FP_Module([2], A, [[Sq(4)]])
            sage: values = [Sq(5)*N.generator(0), Sq(3,1)*N.generator(0)]
            sage: f = Hom(M, N)(values)
            sage: f.__call__(M.generator(0))
            <Sq(5)>
            sage: f.__call__(M.generator(1))
            <Sq(3,1)>

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
            sage: M = FP_Module([0,1], A, [[Sq(2), Sq(1)]])
            sage: N = FP_Module([2], A, [[Sq(4)]])
            sage: values = [Sq(5)*N.generator(0), Sq(3,1)*N.generator(0)]
            sage: Hom(M, N)(values)._repr_()
            'Module homomorphism of degree 7 defined by sending the generators\n  [<1, 0>, <0, 1>]\nto\n  [<Sq(5)>, <Sq(3,1)>]'
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

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import FP_Module
            sage: A = SteenrodAlgebra(2)
            sage: M = FP_Module([0,1], A, [[Sq(2), Sq(1)]])
            sage: N = FP_Module([2], A, [[Sq(4)]])
            sage: values = [Sq(5)*N.generator(0), Sq(3,1)*N.generator(0)]
            sage: f = Hom(M, N)(values)
            sage: f.vector_presentation(0)
            Vector space morphism represented by the matrix:
            [0]
            Domain: Vector space quotient V/W of dimension 1 over Finite Field of size 2 where
            V: Vector space of dimension 1 over Finite Field of size 2
            W: Vector space of degree 1 and dimension 0 over Finite Field of size 2
            Basis matrix:
            []
            Codomain: Vector space quotient V/W of dimension 1 over Finite Field of size 2 where
            V: Vector space of dimension 2 over Finite Field of size 2
            W: Vector space of degree 2 and dimension 1 over Finite Field of size 2
            Basis matrix:
            [0 1]
            sage: f.vector_presentation(1)
            Vector space morphism represented by the matrix:
            [0 0]
            [0 1]
            Domain: Vector space quotient V/W of dimension 2 over Finite Field of size 2 where
            V: Vector space of dimension 2 over Finite Field of size 2
            W: Vector space of degree 2 and dimension 0 over Finite Field of size 2
            Basis matrix:
            []
            Codomain: Vector space quotient V/W of dimension 2 over Finite Field of size 2 where
            V: Vector space of dimension 3 over Finite Field of size 2
            W: Vector space of degree 3 and dimension 1 over Finite Field of size 2
            Basis matrix:
            [0 1 1]
            sage: f.vector_presentation(2)
            Vector space morphism represented by the matrix:
            [0 0]
            Domain: Vector space quotient V/W of dimension 1 over Finite Field of size 2 where
            V: Vector space of dimension 2 over Finite Field of size 2
            W: Vector space of degree 2 and dimension 1 over Finite Field of size 2
            Basis matrix:
            [1 1]
            Codomain: Vector space quotient V/W of dimension 2 over Finite Field of size 2 where
            V: Vector space of dimension 4 over Finite Field of size 2
            W: Vector space of degree 4 and dimension 2 over Finite Field of size 2
            Basis matrix:
            [0 0 1 0]
            [0 0 0 1]

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
        Find an element in the inverse image of the given element ``x``.

        INPUT:

        - ``x`` -- An element of the codomain of this moprhism.

        OUTPUT: An element of the domain which maps to ``x`` under this
        morphism, or ``None`` if ``x`` was not in the image of this morphism.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import FP_Module
            sage: A = SteenrodAlgebra(2)
            sage: M = FP_Module([0], A, [[Sq(3)]])
            sage: N = FP_Module([0], A, [[Sq(2,2)]])
            sage: f = Hom(M, N)( [Sq(2)*N.generator(0)] )
            sage: y = Sq(1,1)*N.generator(0); y
            <Sq(1,1)>
            sage: x = f.solve(y); x
            <Sq(2)>
            sage: y == f(x)
            True

        Trying to lift an element which is not in the image results in a ``None`` value::

            sage: z = f.solve(Sq(1)*N.generator(0))
            sage: z is None
            True

        TESTS:

            sage: f.solve(Sq(2,2)*M.generator(0))
            Traceback (most recent call last):
            ...
            ValueError: The given element is not in the codomain of this homomorphism.

        """

        if x.parent() != self.codomain():
            raise ValueError("The given element is not in the codomain of this homomorphism.")

        # The zero element lifts over all morphisms.
        if x.is_zero():
            return self.domain().zero()

        # Handle the trivial homomorphism since it does not have a well defined
        # degree.
        if self.is_zero():
            return None

        # Handle the case where both the morhism and the element is non-trivial.
        n = x.degree() - self.degree()
        f_n = self.vector_presentation(n)

        v = x.vector_presentation()

        # Return None if ``x`` cannot be lifted.
        if not v in f_n.image():
            return None

        u = f_n.matrix().solve_left(v)
        return self.domain().element_from_coordinates(u, n)


    def lift(self, f):
        """
        A lift of this homomorphism over the given homomorphism ``f``.

        INPUT:

        - ``f`` -- A homomorphism with codomain equal to the codomain of this
          homomorphism.

        OUTPUT::

        - ``g`` -- A homomorphism with the property that this homomorphism
          equals ``f\circ g``.  If no lift exist, an error is raised.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import FP_Module
            sage: A = SteenrodAlgebra(2)
            sage: M = FP_Module([0], A, [[Sq(3)]])
            sage: N = FP_Module([0], A, [[Sq(2,2)]])
            sage: F = FP_Module([0], A)
            sage: f = Hom(M,N)([Sq(2)*N.generator(0)])
            sage: k = Hom(F,N)([Sq(1)*Sq(2)*N.generator(0)])
            sage: k.lift(f)
            Module homomorphism of degree 1 defined by sending the generators
              [<1>]
            to
              [<Sq(1)>]

        TESTS:

            sage: z = Hom(M,N).zero()
            sage: k.lift(z) is None
            True
            sage: Hom(F,N).zero().lift(z)
            The trivial homomorphism.
            sage: Hom(F,N)([Sq(2,2)*N.generator(0)]).lift(z)
            The trivial homomorphism.

        """

        if self.codomain() != f.codomain():
            raise TypeError('Cannot lift this homomorphism over the given map since it has a different codomain.')

        new_values = [f.solve(self(x)) for x in self.domain().generators()]

        # If a lift does not exist, raise an error.
        if None in new_values:
            raise ValueError('A lift of this homomorphism over the given map does not exist.')

        return Hom(self.domain(), f.domain())(new_values)


    def homology(self, f, top_dim=None, verbose=False):
        r"""
        Compute the sub-quotient module `H(self, f) = \ker(self)/\im(f)`, in
        a range of degrees.

        For a pair of composable morphisms `f: M\to N` and `g: N \to Q` of 
        finitely presented modules, the homology module is a finitely 
        presented quotient of the kernel sub module `\ker(g) \subset N`.

        INPUT:

        - ``f`` -- A homomorphism with codomain equal to the domain of this
          homomorphism, and image contained in the kernel of this homomorphism.

        - ``top_dim`` -- An integer used by this function to stop the
        computation at the given degree, or the value ``None`` if no termination
        should be enforced.  (optional, default: ``None``)

        - ``verbose`` -- Boolean to enable progress messages.  (optional,
          default: ``None``)

        OUTPUT: A quotient homomorphism `\ker(self) \to H`, where `H` is 
        isomorphict to `H(self, f)` in degrees less than or equal to ``top_dim``.

        .. NOTE:: If the algebra for this module is finite, then no ``top_dim`` 
        needs to be specified in order to ensure that this function terminates.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import FP_Module
            sage: A = SteenrodAlgebra(2, profile=(3,2,1))
            sage: M = FP_Module([0], A, [[Sq(3)]])
            sage: N = FP_Module([0], A, [[Sq(2,2)]])
            sage: F = FP_Module([0], A)
            sage: f = Hom(M,N)([A.Sq(2)*N.generator(0)])
            sage: g = Hom(F, M)([A.Sq(4)*A.Sq(1,2)*M.generator(0)])
            sage: ho = f.homology(g)
            sage: ho.codomain()
            Finitely presented module on 1 generator and 5 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [3, 2, 1]
            sage: ho.codomain().is_trivial()
            False

        """
        k = self.kernel(top_dim, verbose)
        f_ = f.lift(k)
        return f_.cokernel()


    def suspension(self, t):
        r"""
        The suspension of this morphism by the given degree ``t``.

        INPUT:

        - ``t`` -- An integer by which the morphism is suspended.

        OUTPUT: The morphism which is the suspension of this morphism by the
          degree ``t``.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import FP_Module
            sage: A = SteenrodAlgebra(2)
            sage: F1 = FP_Module([4,5], A)
            sage: F2 = FP_Module([3,4], A)
            sage: H1 = Hom(F1, F2)
            sage: f = H1( ( F2([Sq(1), 0]), F2([0, Sq(1)]) ) ); f
            Module homomorphism of degree 0 defined by sending the generators
              [<1, 0>, <0, 1>]
            to
              (<Sq(1), 0>, <0, Sq(1)>)
            sage: e1 = F1([1, 0])
            sage: e2 = F1([0, 1])
            sage: f(e1)
            <Sq(1), 0>
            sage: f(e2)
            <0, Sq(1)>
            sage: sf = f.suspension(4); sf
            Module homomorphism of degree 0 defined by sending the generators
              [<1, 0>, <0, 1>]
            to
              [<Sq(1), 0>, <0, Sq(1)>]

            sage: sf.domain() is f.domain().suspension(4)
            True
            sage: sf.codomain() is f.codomain().suspension(4)
            True

        """

        if t == 0:
            return self
        else:
            D = self.domain().suspension(t)
            C = self.codomain().suspension(t)
            return Hom(D, C)([D(x.free_element.coefficients()) for x in self._values])


    def cokernel(self):
        r"""
        Compute the cokernel of this homomorphism.

        OUTPUT: The natural projection from the codomain of this homomorphism
        to its cokernel.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import FP_Module
            sage: A1 = SteenrodAlgebra(2, profile=(2,1))
            sage: M = FP_Module([0], A1, [[Sq(2)]])
            sage: F = FP_Module([0], A1)
            sage: r = Hom(F, M)([A1.Sq(1)*M.generator(0)])
            sage: co = r.cokernel(); co
            Module homomorphism of degree 0 defined by sending the generators
              [<1>]
            to
              [<1>]
            sage: co.domain().is_trivial()
            False

        """

        new_relations = [x.coefficients() for x in self.codomain().relations()] +\
            [x.coefficients() for x in self._values]

        coker = self.domain().ModuleClass(
                    self.codomain().generator_degrees(),
                    self.base_ring(),
                    relations=tuple(new_relations))

        projection = Hom(self.codomain(), coker)(coker.generators())

        return projection


    def kernel(self, top_dim=None, verbose=False):
        r"""
        Compute the kernel of this homomorphism.

        INPUT:

        - ``top_dim`` -- An integer used by this function to stop the
        computation at the given degree, or the value ``None`` if no termination
        should be enforced.  (optional, default: ``None``)

        - ``verbose`` -- Boolean to enable progress messages. (optional,
          default: ``None``)

        OUTPUT: A homomorphism into `\ker(self)` which is an isomorphism in
        degrees less than or equal to ``top_dim``.

        .. NOTE:: If the algebra for this module is finite, then no ``top_dim`` 
        needs to be specified in order to ensure that this function terminates.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import FP_Module
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

        INPUT:

        - ``top_dim`` -- An integer used by this function to stop the
        computation at the given degree, or the value ``None`` if no termination
        should be enforced.  (optional, default: ``None``)

        - ``verbose`` -- Boolean to enable progress messages. (optional,
          default: ``False``)

        OUTPUT: A homomorphism into `\im(self)` which is an isomorphism in
        degrees less than or equal to ``top_dim``.

        .. NOTE:: If the algebra for this module is finite, then no ``top_dim`` 
        needs to be specified in order to ensure that this function terminates.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fp_module import FP_Module
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

        INPUT:

        - ``top_dim`` -- An integer used by this function to stop the
        computation at the given degree, or the value ``None`` if no termination
        should be enforced.  (optional, default: ``None``)

        - ``verbose`` -- Boolean to enable progress messages. (optional,
          default: ``False``)

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
        Resolve the kernel of this homomorphism by a free module.

        INPUT:: 

        - ``top_dim`` -- An integer used by this function to stop the
        computation at the given degree, or the value ``None`` if no termination
        should be enforced.  (optional, default: ``None``)

        - ``verbose`` -- Boolean to enable progress messages. (optional,
          default: ``False``)

        OUTPUT: A homomorphism `j: F \rightarrow D` where `D` is the domain of
        this homomorphism, `F` is free and such that `\ker(self) = \im(j)` in
        all degrees less than or equal to ``top_dim``.

        .. NOTE:: If the algebra for this module is finite, then no ``top_dim`` 
        needs to be specified in order to ensure that this function terminates.

        TESTS::
            sage: from sage.modules.fp_modules.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: F = FP_Module([0,0], A)
            sage: L = FP_Module([0,0], A, [[Sq(3),Sq(0,1)], [0,Sq(2)]])
            sage: f = Hom(F, L)([L([Sq(2),0]), L([0, Sq(2)])])
            sage: f.resolve_kernel()
            sage: f.resolve_kernel(top_dim=20)
            sage: A3 = SteenrodAlgebra(2, profile=(4,3,2,1))
            sage: f.change_rings(A3).resolve_kernel()

        """

        # Let 
        #
        #  1) `j` be a homomorphism into `\ker(self)`, and
        #  2) 'n' be an integer.
        #
        # The induction loop starts each iteration assuming that that `j` is onto
        # the kernel in degrees below `n`.  Each iteration of the loop then
        # extends the map `j` minimally so that `j_n` becomes onto the kernel.
        # 
        # This induction step is then repeated for all `n \leq` ``top_dim``.
        #

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
            raise ValueError('A top dimension must be specified for this calculation to terminate.')

        if verbose:
            if dim > limit:
                print('The dimension range is empty: [%d, %d]' % (n, limit))
            else:
                print('Resolving the kernel in the range of dimensions [%d, %d]:' % (dim, limit), end='')

        # The induction loop.
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

            # The map j is not onto in degree `n` of the kernel.
            generator_degrees = tuple((x.degree() for x in F_.generators()))
            new_generator_degrees = tuple(Q_n.dimension()*(n,))
            F_ = self.domain().__class__(generator_degrees + new_generator_degrees, algebra=self.base_ring())

            new_values = tuple([
                self.domain().element_from_coordinates(Q_n.lift(q), n) for q in Q_n.basis()])

            # Create a new homomorphism which is surjective onto the kernel
            # in all degrees less than, and including `n`.
            j = Hom(F_, self.domain()) (j.values() + new_values)

        if verbose:
            print('.')
        return j


    def resolve_image(self, top_dim=None, verbose=False):
        r"""
        Resolve the image of this homomorphism by a free module.

        INPUT:: 

        - ``top_dim`` -- An integer used by this function to stop the
        computation at the given degree, or the value ``None`` if no termination
        should be enforced.  (optional, default: ``None``)

        - ``verbose`` -- Boolean to enable progress messages. (optional,
          default: ``False``)

        OUTPUT: A homomorphism `j: F \rightarrow C` where `C` is the codomain
        of this homomorphism, `F` is free, and `\im(self) = \im(j)`  in
        all degrees less than or equal to ``top_dim``.

        .. NOTE:: If the algebra for this module is finite, then no ``top_dim`` 
        needs to be specified in order to ensure that this function terminates.

        TESTS::
            sage: from sage.modules.fp_modules.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: F = FP_Module([0,0], A)
            sage: L = FP_Module([0,0], A, [[Sq(3),Sq(0,1)], [0,Sq(2)]])
            sage: f = Hom(F, L)([L([Sq(2),0]), L([0, Sq(2)])])
            sage: f.resolve_image()
            sage: f.resolve_image(top_dim=20)
            sage: A3 = SteenrodAlgebra(2, profile=(4,3,2,1))
            sage: f.change_rings(A3).resolve_image()

        """

        # Let 
        #
        #  1) `j` be a homomorphism into `\im(self)`, and
        #  2) 'n' be an integer.
        #
        # The induction loop starts each iteration assuming that that `j` is onto
        # the image in degrees below `n`.  Each iteration of the loop then
        # extends the map `j` minimally so that `j_n` becomes onto the image.
        # 
        # This induction step is then repeated for all `n \leq` ``top_dim``.
        #

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
            raise ValueError('A top dimension must be specified for this calculation to terminate.')

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

            # The map j is not onto in degree `n` of the image.
            generator_degrees = tuple((x.degree() for x in F_.generators()))
            new_generator_degrees = tuple(Q_n.dimension()*(n,))
            F_ = self.domain().__class__(generator_degrees + new_generator_degrees, algebra=self.base_ring())

            new_values = tuple([
                self.codomain().element_from_coordinates(Q_n.lift(q), n) for q in Q_n.basis()])

            # Create a new homomorphism which is surjective onto the image
            # in all degrees less than, and including `n`.
            j = Hom(F_, self.codomain()) (j.values() + new_values)

        if verbose:
            print('.')
        return j
