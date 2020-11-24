r"""
Homomorphisms of finitely presented graded modules

This class implements construction and basic manipulation of elements of the
Sage parent :class:`sage.modules.finitely_presented_over_the_steenrod_algebra.fp_homspace.FP_ModuleHomspace`,
which models homomorphisms of finitely presented graded modules over connected
algebras.

.. NOTE:: This class is intended for private use by its derived class
          :class:`sage.modules.finitely_presented_over_the_steenrod_algebra.fpa_morphism.FPA_ModuleMorphism`.

AUTHORS:

    - Robert R. Bruner, Michael J. Catanzaro (2012): Initial version.
    - Sverre Lunoee--Nielsen and Koen van Woerden (2019-11-29): Updated the
      original software to Sage version 8.9.
    - Sverre Lunoee--Nielsen (2020-07-01): Refactored the code and added
      new documentation and tests.

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

from sage.categories.homset import End
from sage.categories.homset import Hom
from sage.categories.morphism import Morphism as SageMorphism
from sage.misc.cachefunc import cached_method
from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_element import FP_Element
from sage.rings.infinity import PlusInfinity

from .free_homspace import FreeModuleHomspace
from .fp_element import FP_Element

from .timing import g_timings
import time

def _CreateRelationsMatrix(module, relations, source_degs, target_degs):
    r"""
    The action by the given relations can be written as multiplication by
    the matrix `R = (r_{ij})_{i,j}` where each entry is an algebra element and
    each row in the matrix contains the coefficients of a single relation.

    For a given source degree, `n`, the multiplication by `r_{ij}` restricts to
    a linear transformation `M_n\to M_{n + \deg(r_{ij})}`.  This function returns
    the matrix of linear transformations gotten by restricting `R` to the given
    source degrees.

    INPUT:

    - ``module`` -- The module where the relations acts.
    - ``relations`` -- A list of lists of algebra coefficients defining the
      matrix `R`.
    - ``source_degs`` -- A list of integer degrees.  Its length should be
      equal to the number of columns of `R`.
    - ``target_degs`` -- A list of integer degrees.  Its length should be
      equal to the number of rows of `R`.

    Furthermore must the degrees given by the input satisfy the following:

        `\text{source_degs[j]} + \deg(r_{i,j}) = \text{target_degs[i]}`

    for all `i, j`.

    OUTPUT:

    - ``block_matrix`` -- A list of lists representing a matrix of linear
      transformations `(T_{ij})`.  Each transformtion `T_{ij}` is the linear map
      representing multiplication by the coefficient `r_{ij}` restricted to
      the module elements of degree ``source_degs[j]``.
    - ``R`` -- A matrix representing ``block_matrix`` as a single linear
      transformation.

    TESTS:

        sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
        sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_morphism import _CreateRelationsMatrix
        sage: A = SteenrodAlgebra(p=2)
        sage: blocks, R = _CreateRelationsMatrix(FP_Module([0], A), [[Sq(2)]], [4], [6])

        sage: blocks
          [[Vector space morphism represented by the matrix:
            [0 1 0]
            [0 1 1]
            Domain: Vector space quotient V/W of dimension 2 over Finite Field of size 2 where
            V: Vector space of dimension 2 over Finite Field of size 2
            W: Vector space of degree 2 and dimension 0 over Finite Field of size 2
            Basis matrix:
            []
            Codomain: Vector space quotient V/W of dimension 3 over Finite Field of size 2 where
            V: Vector space of dimension 3 over Finite Field of size 2
            W: Vector space of degree 3 and dimension 0 over Finite Field of size 2
            Basis matrix:
            []]]

        sage: R
          [0 0]
          [1 1]
          [0 1]


    """
    from sage.matrix.constructor import matrix

    if len(relations) == 0:
        raise ValueError('No relations given, cannot build matrix.')

    # Create the block matrix of linear transformations.
    block_matrix = []
    for i, r_i in enumerate(relations):
        row = []
        target_space = module.vector_presentation(target_degs[i])

        for j, r_ij in enumerate(r_i):

            values = []
            for b in module.basis_elements(source_degs[j]):
                w = r_ij*b
                values.append(
                    target_space.zero() if w.is_zero() else w.vector_presentation())

            row.append(
                Hom(module.vector_presentation(source_degs[j]), target_space)(values))

        block_matrix.append(row)

    # Deal with the case of zero dimensional matrices first.
    total_source_dim = 0
    for el in block_matrix[0]:
        total_source_dim += el.domain().dimension()
    total_target_dim = 0
    for row in block_matrix:
        total_target_dim += row[0].codomain().dimension()
    if total_source_dim == 0:
        return block_matrix, matrix(total_target_dim, 0)
    elif total_target_dim == 0:
        return block_matrix, matrix(0, total_source_dim)

    # Create a matrix from the matrix of linear transformations.
    entries = []
    for j in range(len(block_matrix[0])):
        for n in range(block_matrix[0][j].domain().dimension()):
            column = []
            for i in range(len(block_matrix)):
                lin_trans = block_matrix[i][j]
                column += lin_trans(lin_trans.domain().basis()[n])
            entries.append(column)

    return block_matrix, matrix(module.base_ring().base_ring(), entries).transpose()


class FP_ModuleMorphism(SageMorphism):

    def __init__(self, parent, values):
        r"""
        Create a homomorphism between finitely presented graded modules.

        INPUT:

        - ``parent`` -- A homspace of finitely presented graded modules.
        - ``values`` -- A list of elements in the codomain.  Each element
          corresponds to a module generator in the domain.

        OUTPUT: A module homomorphism defined by sending the generator with
        index `i` to the corresponding element in ``values``.

        .. NOTE:: Never use this constructor explicitly, but rather the parent's
            call method, or this class' __call__ method.  The reason for this
            is that the dynamic type of the element class changes as a
            consequence of the category system.

        TESTS:

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
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
        from .fp_homspace import is_FP_ModuleHomspace

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

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
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

        OUTPUT: The integer degree of this homomorphism, or ``None`` if this is
        the trivial homomorphism.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FP_Module([0,1], A, [[Sq(2), Sq(1)]])
            sage: N = FP_Module([2], A, [[Sq(4)]])
            sage: homspace = Hom(M, N)

            sage: values = [Sq(5)*N.generator(0), Sq(3,1)*N.generator(0)]
            sage: f = homspace(values)
            sage: f.degree()
            7

        The trivial homomorphism has no degree::

            sage: homspace.zero().degree() is None
            True
    
        TESTS::

            sage: M = FP_Module([7], algebra=SteenrodAlgebra(p=2))
            sage: N = FP_Module([0], algebra=SteenrodAlgebra(p=2), relations=[[Sq(1)]])
            sage: f = Hom(M,N)([Sq(1)*N.generator(0)])
            sage: f == Hom(M,N).zero()
            True
            sage: f.degree() is None
            True

        """
        return None if self.is_zero() else self.free_morphism.degree()


    def values(self):
        r"""
        The values under this homomorphism of the module generators of the
        domain module.

        OUTPUT: A sequence of module elements of the codomain.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import *
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

        Implementation of this function allows Sage to make sense of the ==
        operator for instances of this class.

        INPUT:

        - ``other`` -- An instance of this class.

        - ``op`` -- An integer specifying the comparison operation to be
          carried out: If ``op`` == 2, then return ``True`` if and only if the
          homomorphisms are equal.  If ``op`` == 3, then return ``True `` if
          and only if the homomorphisms are not equal.  Otherwise,
          return ``False``.

        OUTPUT: A Boolean.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import *
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

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import *
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

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import *
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

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import *
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

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
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

        TESTS:

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.free_module import *
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
        Decide if this homomomorphism is the zero homomorphism.

        OUTPUT: The boolean value ``True`` if this homomorphism is trivial, and
        ``False`` otherwise.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
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

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import *
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

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import *
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

        ff = self.free_morphism(x.free_element)
        res = self.codomain().element_class(self.codomain(), ff)
        return res

    def _repr_(self):
        r"""
        A string representation of this homomorphism.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import *
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

        The restriction of a non-zero module homomorphism to the vectorspace of
        module elements of degree `n` is a linear function into the vectorspace
        of elements of degree `n+d` belonging to the codomain.  Here `d` is the
        degree of this homomorphism.

        When this homomorphism is zero, it has no well defined degree so the
        function cannot be presented since we do not know the degree of its
        codomain.  In this case, the return value is ``None``.

        INPUT:

        - ``n`` -- An integer degree.

        OUTPUT: A linear function of finite dimensional vectorspaces over the
        ground field of the algebra for this module.  The domain is isomorphic
        to the vectorspace of domain elements of degree ``n`` of this free
        module, via the choice of basis given by
        :meth:`sage.modules.finitely_presented_over_the_steenrod_algebra.free_module.FreeModule.basis_elements`.
        If the morphism is zero, the value ``None`` is returned.

        .. SEEALSO::

            :meth:`sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module.FP_Module.vector_presentation`,
            :meth:`sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module.FP_Module.basis_elements`.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
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


        TESTS:

            sage: F = FP_Module([0], A)
            sage: Q = FP_Module([0], A, [[Sq(2)]])
            sage: z = Hom(F, Q)([Sq(2)*Q.generator(0)])
            sage: z.is_zero()
            True
            sage: z.vector_presentation(0) is None
            True

        """
        global g_timings

        # The trivial map has no degree, so we can not create the codomain
        # of the linear transformation.
        iszero = self.is_zero()

        if iszero:
            return None

        D_n = self.domain().vector_presentation(n)
        C_n = self.codomain().vector_presentation(self.degree() + n)
        domain_basis = self.domain().basis_elements(n)

        values = [self(e) for e in domain_basis]

        vps_ = [e.vector_presentation() for e in values]

        _vals = [C_n.zero() if v is None else v for v in vps_]

        g_timings.Start('fp_morphism.Hom')
        FF = Hom(D_n, C_n)(_vals)
        g_timings.End()

        return FF
    

    def solve(self, x):
        r"""
        Find an element in the inverse image of the given element.

        INPUT:

        - ``x`` -- An element of the codomain of this morphism.

        OUTPUT: An element of the domain which maps to ``x`` under this
        morphism, or ``None`` if ``x`` was not in the image of this morphism.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
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
        r"""
        A lift of this homomorphism over the given homomorphism ``f``.

        INPUT:

        - ``f`` -- A homomorphism with codomain equal to the codomain of this
          homomorphism.
        - ``verbose`` -- A boolean to enable progress messages. (optional,
          default: ``False``)

        OUTPUT: A homomorphism `g` with the property that this homomorphism
        equals `f\circ g`.  If no lift exist, ``None`` is returned.

        ALGORITHM:

        Let `L` be the domain of this homomorphism, and choose `x_1, \ldots, x_N`
        such that `f(x_i) = self(g_i)` where the `g_i`'s are the module
        generators of `L`.

        The linear function sending `g_i` to `x_i` for every `i` is well
        defined if and only if the vector `x = (x_1,\ldots, x_N)` lies
        in the nullspace of the coefficient matrix `R = (r_{ij})` given by the 
        relations of `L`.

        Let `k \in \ker(f)` solve the matrix equation:

            `R\cdot k = R\cdot x`.

        Define a module homomorphism by sending the generators of `L` to 
        `x_1 - k_1, \ldots, x_N - k_N`.  This is well defined, and is also a 
        lift of this homomorphism over `f`.

        Note that it does not matter how we choose the initial elements `x_i`:
        If `x'` is another choice then `x' - x\in \ker(f)` and
        `R\cdot k = R\cdot x` if and only if `R\cdot (k + x' - x) = R\cdot x'`.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
            sage: A = SteenrodAlgebra(2)

        Lifting a map from a free module is always possible::

            sage: M = FP_Module([0], A, [[Sq(3)]])
            sage: N = FP_Module([0], A, [[Sq(2,2)]])
            sage: F = FP_Module([0], A)
            sage: f = Hom(M,N)([Sq(2)*N.generator(0)])
            sage: k = Hom(F,N)([Sq(1)*Sq(2)*N.generator(0)])
            sage: f_ = k.lift(f)
            sage: f*f_ == k
            True
            sage: f_
            Module homomorphism of degree 1 defined by sending the generators
              [<1>]
            to
              [<Sq(1)>]

        A split projection::

            sage: A_plus_HZ = FP_Module([0,0], A, [[0, Sq(1)]])
            sage: HZ = FP_Module([0], A, [[Sq(1)]])
            sage: q = Hom(A_plus_HZ, HZ)([HZ([1]), HZ([1])])
            sage: # We can construct a splitting of `q` manually:
            sage: split = Hom(HZ,A_plus_HZ)([A_plus_HZ.generator(1)])
            sage: q*split
            The identity homomorphism.
            sage: # Thus, lifting the identity homomorphism over `q` should be possible:
            sage: id = Hom(HZ,HZ).identity()
            sage: j = id.lift(q); j
            Module homomorphism of degree 0 defined by sending the generators
              [<1>]
            to
              [<0, 1>]
            sage: q*j
            The identity homomorphism.

        Lifting over the inclusion of the image sub module::

            sage: A = SteenrodAlgebra(2)
            sage: M = FP_Module([0], A, relations=[[Sq(0,1)]])
            sage: f = Hom(M,M)([Sq(2)*M.generator(0)])
            sage: im = f.image(top_dim=10)
            sage: f.lift(im)
            Module homomorphism of degree 2 defined by sending the generators
              [<1>]
            to
              [<1>]

        When a lift cannot be found, the ``None`` value is returned.  By setting the
        verbose argument to ``True``, an explanation of why the lifting failed will
        be displayed::

            sage: F2 = FP_Module([0,0], A)
            sage: non_surjection = Hom(F2, F2)([F2([1, 0]), F2([0, 0])])
            sage: lift = Hom(F2, F2).identity().lift(non_surjection, verbose=True)
            The generators of the domain of this homomorphism does not map into the image of the homomorphism we are lifting over.
            sage: lift is None
            True

        TESTS:

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
            sage: A = SteenrodAlgebra(2)
            sage: # The trivial map often involved in corner cases..
            sage: trivial_map = Hom(FP_Module([0], A), FP_Module([], A)).zero()
            sage: trivial_map.lift(trivial_map)
            The trivial homomorphism.

            sage: F = FP_Module([0], A)
            sage: HZ = FP_Module([0], A, relations=[[Sq(1)]])
            sage: f = Hom(F,HZ)(HZ.generators())
            sage: split = Hom(HZ, HZ).identity().lift(f, verbose=True)
            The homomorphism cannot be lifted in any way such that the relations of the domain are respected: matrix equation has no solutions
            sage: split is None
            True

            sage: Hom(F, F).identity().lift(f, verbose=true)
            Traceback (most recent call last):
            ...
            ValueError: The codomains of this homomorphism and the homomorphism we are lifting over are different.

            sage: f.lift(Hom(HZ, HZ).zero(), verbose=True)
            This homomorphism cannot lift over a trivial homomorphism since it is non-trivial.

            sage: Ap = SteenrodAlgebra(p=2, profile=(2,2,2,1))
            sage: Hko = FP_Module([0], Ap, [[Sq(2)], [Sq(1)]])
            sage: f = Hom(Hko, Hko)([(Ap.Sq(0,0,3) + Ap.Sq(0,2,0,1))*Hko.generator(0)])
            sage: f*f == 0
            True
            sage: k = f.kernel()
            sage: f.lift(k)
            Module homomorphism of degree 21 defined by sending the generators
              [<1>]
            to
              [<0, Sq(1), 0>]

        Corner cases involving trivial maps::

            sage: M = FP_Module([1], A)
            sage: M1 = FP_Module([0], A)
            sage: M2 = FP_Module([0], A, [[Sq(1)]])
            sage: q = Hom(M1, M2)([M2.generator(0)])
            sage: z = Hom(M, M2).zero()
            sage: lift = z.lift(q)
            sage: lift.domain() is M and lift.codomain() is M1
            True

        .. SEEALSO::
            :meth:`split`

        """

        from sage.modules.free_module_element import vector

        #        self
        #    L -------> N
        #     \         ^
        #       \       |
        #   lift  \     | f
        #           \   |
        #            _| |
        #               M
        L = self.domain()
        N = self.codomain()
        M = f.domain()

        # It is an error to call this function with incompatible arguments.
        if not f.codomain() is N:
            raise ValueError('The codomains of this homomorphism and the homomorphism '\
                'we are lifting over are different.')

        # The trivial map lifts over any other map.
        if self.is_zero():
            return Hom(L, M).zero()

        # A non-trivial map never lifts over the trivial map.
        if f.is_zero():
#            if verbose:
#                print('This homomorphism cannot lift over a trivial homomorphism since it is non-trivial.')
            return None

        xs = [f.solve(self(g)) for g in L.generators()]

        # If some of the generators are not in the image of f, there is no
        # hope finding a lift.
        if None in xs:
#            if verbose:
#                print('The generators of the domain of this homomorphism does '\
#                      'not map into the image of the homomorphism we are lifting over.')
            return None

        # If L is free there are no relations to take into consideration.
        if not L.has_relations():
            return Hom(L, M)(xs)

        # The degree of the lifted map f_.
        lift_deg = self.degree() - f.degree()

        # Compute the kernel of f.  The equations we will solve will live in
        # this submodule.
        iK = f.kernel(top_dim=max([r.degree() + lift_deg for r in L.relations()]))

        source_degs = [g.degree() + lift_deg for g in L.generators()]
        target_degs = [r.degree() + lift_deg for r in L.relations()]

        # Act on the liftings xs by the relations.
        ys = []
        K = iK.domain()
        all_zero = True

        for r in L.relations():
            target_degree = r.degree() + lift_deg

            y = iK.solve(sum([c*x for c,x in zip(r.coefficients(), xs)]))
            if y is None:
#                if verbose:
#                    print('The homomorphism cannot be lifted in any '
#                         'way such that the relations of the domain are '
#                         'respected.')
                return None

            if y.is_zero():
                dim = len(K[target_degree])
                ys += dim*[0]  # The zero vector of the appropriate dimension.
            else:
                all_zero = False
                ys += list(y.vector_presentation())

        # If the initial guess already fits the relations, we are done.
        if all_zero:
            return Hom(L, M)(xs)

        block_matrix, R = _CreateRelationsMatrix(
            K, [r.coefficients() for r in L.relations()], source_degs, target_degs)

        try:
            solution = R.solve_right(vector(ys))
        except ValueError as error:
            if str(error) == 'matrix equation has no solutions':
#                if verbose:
#                    print('The homomorphism cannot be lifted in any '
#                          'way such that the relations of the domain '
#                          'are respected: %s' % error)

                return None
            else:
                raise ValueError(error)

        # Interpret the solution vector as a vector in the direct sum
        # $ K_1\oplus K_2\oplus \ldots \oplus K_n $.
        n = 0
        for j, source_degree in enumerate(source_degs):

            source_dimension = block_matrix[0][j].domain().dimension()

            w = K.element_from_coordinates(
                    solution[n:n + source_dimension], source_degree)

            # Subtract the solution w_i from our initial choice of lift
            # for the generator g_i.
            xs[j] -= iK(w)

            n += source_degree

        return Hom(L, M)(xs)


    def split(self):
        r"""
        A split of this homomorphism.

        INPUT:

        - ``verbose`` -- A boolean to enable progress messages. (optional,
          default: ``False``)

        OUTPUT: A homomorphism with the property that the composite
        homomorphism `self \circ f = id` is the identity homomorphism.  If no
        such split exist, ``None`` is returned.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
            sage: A = SteenrodAlgebra(2)
            sage: M = FP_Module([0,0], A, [[0, Sq(1)]])
            sage: N = FP_Module([0], A, [[Sq(1)]])
            sage: p = Hom(M, N)([N.generator(0), N.generator(0)])
            sage: s = p.split(); s
            Module homomorphism of degree 0 defined by sending the generators
              [<1>]
            to
              [<0, 1>]
            sage: # Verify that `s` is a splitting:
            sage: p*s
            The identity homomorphism.

        TESTS:

            sage: F = FP_Module([0], A)
            sage: N = FP_Module([0], A, [[Sq(1)]])
            sage: p = Hom(F, N)([N.generator(0)])
            sage: p.split(verbose=True) is None
            The homomorphism cannot be lifted in any way such that the relations of the domain are respected: matrix equation has no solutions
            True

        .. SEEALSO::
            :meth:`lift`

        """

        id = End(self.codomain()).identity()
        return id.lift(self)


    def homology(self, f, top_dim=None):
        r"""
        Compute the sub-quotient module `H(self, f) = \ker(self)/\operatorname{im}(f)`, in
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

        - ``verbose`` -- A boolean to enable progress messages.  (optional,
          default: ``False``)

        OUTPUT: A quotient homomorphism `\ker(self) \to H`, where `H` is
        isomorphic to `H(self, f)` in degrees less than or equal to ``top_dim``.

        .. NOTE::

            If the algebra for this module is finite, then no ``top_dim``
            needs to be specified in order to ensure that this function terminates.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
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
        k = self.kernel(top_dim)
        f_ = f.lift(k)
        if f_ is None:
            raise ValueError('The image of the given homomorphism is not contained '
                 'in the kernel of this homomorphism.  The homology is '
                 'therefore not defined for this pair of maps.')

        return f_.cokernel()


    def suspension(self, t):
        r"""
        The suspension of this morphism by the given degree ``t``.

        INPUT:

        - ``t`` -- An integer by which the morphism is suspended.

        OUTPUT: The morphism which is the suspension of this morphism by the
        degree ``t``.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
            sage: A = SteenrodAlgebra(2)
            sage: F1 = FP_Module([4,5], A)
            sage: F2 = FP_Module([5], A)

            sage: f = Hom(F1, F2)( ( F2([Sq(4)]), F2([Sq(5)]) ) ); f
            Module homomorphism of degree 5 defined by sending the generators
              [<1, 0>, <0, 1>]
            to
              (<Sq(4)>, <Sq(5)>)

            sage: e1 = F1([1, 0])
            sage: e2 = F1([0, 1])
            sage: f(e1)
            <Sq(4)>
            sage: f(e2)
            <Sq(5)>

            sage: sf = f.suspension(4); sf
            Module homomorphism of degree 5 defined by sending the generators
              [<1, 0>, <0, 1>]
            to
              [<Sq(4)>, <Sq(5)>]

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
            return Hom(D, C)([C(x.free_element.coefficients()) for x in self._values])


    def cokernel(self):
        r"""
        Compute the cokernel of this homomorphism.

        OUTPUT: The natural projection from the codomain of this homomorphism
        to its cokernel.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
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


    def kernel(self, top_dim=None):
        r"""
        Compute the kernel of this homomorphism.

        INPUT:

        - ``top_dim`` -- An integer used by this function to stop the
          computation at the given degree, or the value ``None`` if no
          termination should be enforced.  (optional, default: ``None``)

        - ``verbose`` -- A boolean to enable progress messages. (optional,
          default: ``False``)

        OUTPUT: A homomorphism into `\ker(self)` which is an isomorphism in
        degrees less than or equal to ``top_dim``.

        .. NOTE::

            If the algebra for this module is finite, then no ``top_dim`` needs
            to be specified in order to ensure that this function terminates.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
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

#        if verbose:
#            print('1. Computing the generators of the kernel presentation:')
        j0 = self._resolve_kernel(top_dim)
#        if verbose:
#            print('2. Computing the relations of the kernel presentation:')
        j1 = j0._resolve_kernel(top_dim)

        # Create a module isomorphic to the ker(self).
        K = self.domain().ModuleClass.from_free_module_morphism(j1)

        # Return an injection of K into the domain of self such that
        # its image equals ker(self).
        return Hom(K, j0.codomain())(j0.values())


    def image(self, top_dim=None):
        r"""
        Compute the image of this homomorphism.

        INPUT:

        - ``top_dim`` -- An integer used by this function to stop the
          computation at the given degree, or the value ``None`` if no
          termination should be enforced.  (optional, default: ``None``)

        - ``verbose`` -- A boolean to enable progress messages. (optional,
          default: ``False``)

        OUTPUT: A homomorphism into `\operatorname{im}(self)` which is an
        isomorphism in degrees less than or equal to ``top_dim``.

        .. NOTE::

            If the algebra for this module is finite, then no ``top_dim``
            needs to be specified in order to ensure that this function
            terminates.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
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
#        if verbose:
#            print('1. Computing the generators of the image presentation:')
        j0 = self._resolve_image(top_dim)
#        if verbose:
#            print('2. Computing the relations of the image presentation:')
        j1 = j0._resolve_kernel(top_dim)

        # Create a module isomorphic to the im(self).
        I = self.domain().ModuleClass.from_free_module_morphism(j1)

        # Return an injection of I into the codomain of self such that
        # its image equals im(self)
        return Hom(I, j0.codomain())(j0.values())


    def is_injective(self, top_dim=None):
        r"""
        Return ``True`` if and only if this homomorphism has a trivial kernel.

        INPUT:

        - ``top_dim`` -- An integer used by this function to stop the
          computation at the given degree, or the value ``None`` if no termination
          should be enforced.  (optional, default: ``None``)

        - ``verbose`` -- A boolean to enable progress messages. (optional,
          default: ``False``)

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
            sage: A = SteenrodAlgebra(2)

            sage: K = FP_Module([2], A, [[Sq(2)]])
            sage: HZ = FP_Module([0], A, [[Sq(1)]])

            sage: f = Hom(K, HZ)([Sq(2)*HZ([1])])
            sage: f.is_injective(top_dim=23)
            True

        TESTS:

            sage: Z = FP_Module([], A)
            sage: Hom(Z, HZ).zero().is_injective(top_dim=8)
            True

        """
        j0 = self._resolve_kernel(top_dim)
        return j0.domain().is_trivial()


    def is_surjective(self):
        r"""
        Return ``True`` if and only if this homomorphism has a trivial cokernel.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
            sage: A = SteenrodAlgebra(2)
            sage: F = FP_Module([0], A)

            sage: f = Hom(F,F)([Sq(1)*F.generator(0)])
            sage: f.is_surjective()
            False

        TESTS:

            sage: Z = FP_Module([], A)
            sage: Hom(F, Z).zero().is_surjective()
            True

        """
        return self.cokernel().is_zero()


    def _resolve_kernel(self, top_dim=None):
        r"""
        Resolve the kernel of this homomorphism by a free module.

        INPUT:

        - ``top_dim`` -- An integer used by this function to stop the
          computation at the given degree, or the value ``None`` if no termination
          should be enforced.  (optional, default: ``None``)

        - ``verbose`` -- A boolean to enable progress messages. (optional,
          default: ``False``)

        OUTPUT: A homomorphism `j: F \rightarrow D` where `D` is the domain of
        this homomorphism, `F` is free and such that
        `\ker(self) = \operatorname{im}(j)` in all degrees less than or equal
        to ``top_dim``.

        .. NOTE::

            If the algebra for this module is finite, then no ``top_dim``
            needs to be specified in order to ensure that this function terminates.

        TESTS:

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
            sage: A = SteenrodAlgebra(2)
            sage: F = FP_Module([0,0], A)
            sage: L = FP_Module([0,0], A, [[Sq(3),Sq(0,1)], [0,Sq(2)]])
            sage: f = Hom(F, L)([L([Sq(2),0]), L([0, Sq(2)])])
            sage: f._resolve_kernel()
            Traceback (most recent call last):
            ...
            ValueError: A top dimension must be specified for this calculation to terminate.
            sage: f._resolve_kernel(top_dim=20)
            Module homomorphism of degree 0 defined by sending the generators
              [<1, 0, 0>, <0, 1, 0>, <0, 0, 1>]
            to
              (<0, 1>, <Sq(0,1), 0>, <Sq(3), 0>)
            sage: A3 = SteenrodAlgebra(2, profile=(4,3,2,1))
            sage: f.change_ring(A3)._resolve_kernel()
            Module homomorphism of degree 0 defined by sending the generators
              [<1, 0, 0>, <0, 1, 0>, <0, 0, 1>]
            to
              (<0, 1>, <Sq(0,1), 0>, <Sq(3), 0>)

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

        if self.is_zero():
            # Epsilon: F_0 -> M
            M = self.domain()
            F_0 = M.ModuleClass.from_free_module(self.domain().j.codomain())
            epsilon = Hom(F_0, M)(tuple(M.generators()))
            return epsilon

        # Create the trivial module F_ to start with.
        F_ = self.domain().__class__((), algebra=self.base_ring())
        j = Hom(F_, self.domain())(())

        dim = self.domain().connectivity()
        if dim == PlusInfinity():
#            if verbose:
#                print ('The domain of the morphism is trivial, so there is nothing to resolve.')
            return j

        limit = PlusInfinity() if not self.base_ring().is_finite() else\
            (self.base_ring().top_class().degree() + max(self.domain().generator_degrees()))

        if not top_dim is None:
            limit = min(top_dim, limit)

        if limit == PlusInfinity():
            raise ValueError('A top dimension must be specified for this calculation to terminate.')

        verbose = True

        if verbose:
            if dim > limit:
                print('The dimension range is empty: [%d, %d]' % (dim, limit))
            else:
                print('Resolving the kernel in the range of dimensions [%d, %d]:' % (dim, limit), end='')

#        from .timing import Timing
#        timing = Timing()
        global g_timings

        time_degree = 20
        total_time = time.time()

        # The induction loop.
        for n in range(dim, limit+1):

#            if verbose:
#                print(' %d' % n, end='')
#                sys.stdout.flush()

            if n >= time_degree:
                total_time = time.time() - total_time
                g_timings.PrintCSV(n, total_time, ['SteenrodAlgebra', 'lin_alg'])
#                g_timings.Print(total_time)
#                g_timings.Print(timing._timings['fp_morphism.vector_presentation()'])

            # Reset performance timers.
            g_timings.Reset()
#            timing.Reset()
            total_time = time.time()

            # We have taken care of the case when self is zero, so the
            # vector presentation exists.
#            g_timings.Start('fp_morphism.vector_presentation()')
            self_n = self.vector_presentation(n)
#            timing.End()

            g_timings.Start('lin_alg')
            kernel_n = self_n.kernel()
            g_timings.End()

            if kernel_n.dimension() == 0:
                continue

            generator_degrees = tuple((x.degree() for x in F_.generators()))

            if j.is_zero():
                # The map j is not onto in degree `n` of the kernel.
                new_generator_degrees = tuple(kernel_n.dimension()*(n,))

                F_ = self.domain().__class__(generator_degrees + new_generator_degrees, algebra=self.base_ring())

                g_timings.Start('lin_alg')
                basz = kernel_n.basis()
                g_timings.End()

                new_values = tuple([
                    self.domain().element_from_coordinates(q, n) for q in basz])

            else:
#                timing.Start('fp_morphism.vector_presentation()')
                pres = j.vector_presentation(n)
#                timing.End()

                g_timings.Start('lin_alg')
                Q_n = kernel_n.quotient(pres.image())
                g_timings.End()

                if Q_n.dimension() == 0:
                    continue

                # The map j is not onto in degree `n` of the kernel.
                new_generator_degrees = tuple(Q_n.dimension()*(n,))
                F_ = self.domain().__class__(generator_degrees + new_generator_degrees, algebra=self.base_ring())

                g_timings.Start('lin_alg')
                lifts = [Q_n.lift(q) for q in Q_n.basis()]
                g_timings.End()

                new_values = tuple([
                    self.domain().element_from_coordinates(v, n) for v in lifts])

            # Create a new homomorphism which is surjective onto the kernel
            # in all degrees less than, and including `n`.
            j = Hom(F_, self.domain()) (j.values() + new_values)


        if verbose:
            print('.')
        return j


    def _resolve_image(self, top_dim=None):
        r"""
        Resolve the image of this homomorphism by a free module.

        INPUT:

        - ``top_dim`` -- An integer used by this function to stop the
          computation at the given degree, or the value ``None`` if no termination
          should be enforced.  (optional, default: ``None``)

        - ``verbose`` -- A boolean to enable progress messages. (optional,
          default: ``False``)

        OUTPUT: A homomorphism `j: F \rightarrow C` where `C` is the codomain
        of this homomorphism, `F` is free, and
        `\operatorname{im}(self) = \operatorname{im}(j)` in all degrees less
        than or equal to ``top_dim``.

        .. NOTE::

            If the algebra for this module is finite, then no ``top_dim`` needs
            to be specified in order to ensure that this function terminates.

        TESTS:

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import *
            sage: A = SteenrodAlgebra(2)
            sage: F = FP_Module([0,0], A)
            sage: L = FP_Module([0,0], A, [[Sq(3),Sq(0,1)], [0,Sq(2)]])
            sage: f = Hom(F, L)([L([Sq(2),0]), L([0, Sq(2)])])
            sage: f._resolve_image()
            Traceback (most recent call last):
            ...
            ValueError: A top dimension must be specified for this calculation to terminate.
            sage: f._resolve_image(top_dim=20)
            Module homomorphism of degree 0 defined by sending the generators
              [<1>]
            to
              (<Sq(2), 0>,)
            sage: A3 = SteenrodAlgebra(2, profile=(4,3,2,1))
            sage: f.change_ring(A3)._resolve_image()
            Module homomorphism of degree 0 defined by sending the generators
              [<1>]
            to
              (<Sq(2), 0>,)

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
#            if verbose:
#                print ('The codomain of the morphism is trivial, so there is nothing to resolve.')
            return j

        self_degree = self.degree()
        if self_degree is None:
#            if verbose:
#                print ('The homomorphism is trivial, so there is nothing to resolve.')
            return j

        degree_values = [0] + [v.degree() for v in self.values() if v.degree() != None]
        limit = PlusInfinity() if not self.base_ring().is_finite() else\
            (self.base_ring().top_class().degree() + max(degree_values))

        if not top_dim is None:
            limit = min(top_dim, limit)

        if limit == PlusInfinity():
            raise ValueError('A top dimension must be specified for this calculation to terminate.')

#        if verbose:
#            if dim > limit:
#                print('The dimension range is empty: [%d, %d]' % (dim, limit))
#            else:
#                print('Resolving the image in the range of dimensions [%d, %d]:' % (dim, limit), end='')

        for n in range(dim, limit+1):

#            if verbose:
#                print(' %d' % n, end='')
#                sys.stdout.flush()
#
            self_n = self.vector_presentation(n - self_degree)
            image_n = self_n.image()

            if image_n.dimension() == 0:
                continue


            generator_degrees = tuple((x.degree() for x in F_.generators()))
            if j.is_zero():
                # The map j is not onto in degree `n` of the image.
                new_generator_degrees = tuple(image_n.dimension()*(n,))
                F_ = self.domain().__class__(generator_degrees + new_generator_degrees, algebra=self.base_ring())

                new_values = tuple([
                    self.codomain().element_from_coordinates(q, n) for q in image_n.basis()])

            else:

                j_n = j.vector_presentation(n)
                Q_n = image_n.quotient(j_n.image())

                if Q_n.dimension() == 0:
                    continue

                # The map j is not onto in degree `n` of the image.
                new_generator_degrees = tuple(Q_n.dimension()*(n,))
                F_ = self.domain().__class__(generator_degrees + new_generator_degrees, algebra=self.base_ring())

                new_values = tuple([
                    self.codomain().element_from_coordinates(Q_n.lift(q), n) for q in Q_n.basis()])

            # Create a new homomorphism which is surjective onto the image
            # in all degrees less than, and including `n`.
            j = Hom(F_, self.codomain()) (j.values() + new_values)

#        if verbose:
#            print('.')
        return j



