r"""
Homomorphisms of finitely generated free graded modules

This class implements construction and basic manipulation of homomorphisms
between finitely generated free graded modules, modelled by the Sage parent
:class:`sage.modules.fp_modules.free_module.FreeModule`.

This class is intended for private use by
:class:`sage.modules.fp_modules.fp_morphism.FP_ModuleMorphism` which models
homomorphisms between finitely presented modules over graded algeras.


EXAMPLES::

    sage: from sage.modules.fp_modules.free_module import FreeModule
    sage: A = SteenrodAlgebra(2)
    sage: M = FreeModule((0,1), A)
    sage: N = FreeModule((2,), A)

Homomorphisms are elements of the parent homspace class, and are created
by specifying how the homomorphism should evaluate on each generator::

    sage: values = [Sq(1)*N.generator(0), Sq(2)*N.generator(0)]
    sage: homspace = Hom(M, N)
    sage: f = homspace(values); f
    Module homomorphism of degree 3 defined by sending the generators
      [<1, 0>, <0, 1>]
    to
      [<Sq(1)>, <Sq(2)>]
    sage: f.values() == values
    True

Homomorphisms can be evaluated on elements of the domain module::

    sage: v1 = f(Sq(7)*M.generator(0));v1
    <Sq(5,1)>
    sage: v2 = f(Sq(17)*M.generator(1));v2
    <Sq(13,2) + Sq(19)>

Homomorphisms respect the module action::

    sage: v1 == Sq(7)*values[0]
    True
    sage: v2 == Sq(17)*values[1]
    True

Any homomorphism has a well defined degree::

    sage: f.degree()
    3
    sage: f.values()[0].degree() - M.generators()[0].degree()
    3

Homomorphisms of equal degree form a group under pointwise addition::

    sage: g = homspace([Sq(1)*N.generator(0), 0*N.generator(0)])
    sage: f+g
    Module homomorphism of degree 3 defined by sending the generators
      [<1, 0>, <0, 1>]
    to
      [<0>, <Sq(2)>]
    sage: (f+g).values()
    [<0>, <Sq(2)>]
    sage: z = homspace.zero(); z
    The trivial homomorphism.
    sage: f == f + z
    True
    sage: f - f == z
    True

The restriction of a homomorphism to the vectorspace of `n`-dimensional module
elements is a linear transformation::

    sage: f_lin = f.vector_presentation(4)
    sage: f_lin.kernel()
    Vector space of degree 4 and dimension 2 over Finite Field of size 2
    Basis matrix:
    [1 0 0 0]
    [0 0 0 1]

AUTHORS:

    - Robert R. Bruner, Michael J. Catanzaro (2012): initial version
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

from __future__ import absolute_import

from inspect import isfunction

from sage.categories.homset import Hom
from sage.categories.morphism import Morphism as SageMorphism
from sage.misc.cachefunc import cached_method

import sage.categories.homset
import sage.categories.morphism

from .free_homspace import is_FreeModuleHomspace


class FreeModuleMorphism(SageMorphism):

    def __init__(self, parent, values):
        r"""
        Create a homomorphism between finitely generated free graded modules.

        INPUT:

        - ``parent`` -- A homspace in the category of finitely generated free
            modules.

        - ``values`` -- A list of elements in the codomain.  Each element
            corresponds (by their ordering) to a module generator in the domain.

        OUTPUT: 

        A module homomorphism defined by sending generator with index `i` to
        the element in the comdomain which has index `i` in the given input
        list.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import FreeModule
            sage: A = SteenrodAlgebra(2)
            sage: F1 = FreeModule((4,5), A)
            sage: F2 = FreeModule((3,4), A)
            sage: F3 = FreeModule((2,3), A)
            sage: H1 = Hom(F1, F2)
            sage: H2 = Hom(F2, F3)
            sage: f = H1( ( F2((Sq(4), 0)), F2((0, Sq(4))) ) )
            sage: g = H2( ( F3((Sq(2), 0)), F3((Sq(3), Sq(2))) ) )
            sage: g*f
            Module homomorphism of degree 4 defined by sending the generators
              [<1, 0>, <0, 1>]
            to
              [<Sq(0,2) + Sq(3,1) + Sq(6), 0>, <Sq(1,2) + Sq(7), Sq(0,2) + Sq(3,1) + Sq(6)>]

        """

        if not is_FreeModuleHomspace(parent):
            raise TypeError("parent (=%s) must be a fp free module hom space" % parent)

        # Get the values.
        C = parent.codomain()
        D = parent.domain()
        if isfunction(values):
            _values = [C(values(g)) for g in D.generators()]
        elif values == 0:
            _values = len(D.generator_degrees())*[C(0)]
        else:
            _values = [C(a) for a in values]

        # Check the homomorphism is well defined.
        if len(D.generator_degrees()) != len(_values):
            raise ValueError("The number of values must equal the number of " \
                "generators in the domain.  Invalid argument: %s." % _values)

        if all(v.is_zero() for v in _values):
            # The zero homomorphism does not get a degree.
            self._degree = None
        else:
            # Find the first non-zero value, and and record the shift
            # of degrees imposed by this homomorphism.
            for i, value in enumerate(_values):
                if not value.is_zero():
                    x = value.degree()
                    xx = D.generator_degrees()[i]
                    self._degree = x-xx
                    break

            # Check that all generators are shifted by the same degree.
            if not all(not v.degree() or self._degree == (v.degree() - g) \
                       for g, v in zip(D.generator_degrees(), _values)):
                errorMessage = "Ill defined homomorphism (degrees do not match)\n"
                gen_index = 0
                for g, v in zip(D.generator_degrees(), _values):
                    errorMessage += "  Generator #%d (degree %d) -> %s (degree %d)"\
                        " shifts degrees by %d\n" % (
                        gen_index, g, v, v.degree(), v.degree() - g)
                    gen_index += 1
                raise ValueError(errorMessage)

        self._values = _values

        SageMorphism.__init__(self, parent)


    def degree(self):
        r"""
        The degree of this homomorphism.

        OUTPUT:
        
        The integer degree of this homomorphism, or None if this is the zero
        homomorphism.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A = SteenrodAlgebra(2)
            sage: homspace = Hom(FreeModule((0,1), A), FreeModule((0,), A))
            sage: N = homspace.codomain()
            sage: values = [Sq(5)*N.generator(0), Sq(3,1)*N.generator(0)]
            sage: f = homspace(values)
            sage: f.degree()
            5

        The zero homomorphism has no degree::

            sage: homspace.zero().degree() is None
            True

        """
        return self._degree


    def values(self):
        r"""
        The values under this homomorphism of the module generators of the
        domain module.

        OUTPUT:
        
        A sequence of module elements of the codomain module.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A = SteenrodAlgebra(2)
            sage: homspace = Hom(FreeModule((0,1), A), FreeModule((2,), A))
            sage: N = homspace.codomain()
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

        OUTPUT:

        A boolean indicating the result of the comparison operation.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A = SteenrodAlgebra(2)
            sage: homspace = Hom(FreeModule((0,1), A), FreeModule((2,), A))
            sage: N = homspace.codomain()
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

        OUTPUT:
        
        The pointwise sum homomorphism of this and the given homomorphism.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A = SteenrodAlgebra(2)
            sage: homspace = Hom(FreeModule((0,1), A), FreeModule((2,), A))
            sage: N = homspace.codomain()
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
        elif self._degree and g.degree() and self._degree != g.degree():
            raise ValueError("Morphisms do not have the same degree.")

        v = [self(x) + g(x) for x in self.domain().generators()]

        return self.parent()(v)


    def __neg__(self):
        r"""
        The additive inverse of this homomorphism with respect to the group
        structure given by pointwise sum.

        OUTPUT: 
        
        An instance of this class.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A = SteenrodAlgebra(2)
            sage: homspace = Hom(FreeModule((0,1), A), FreeModule((2,), A))
            sage: N = homspace.codomain()
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

        OUTPUT: 
        
        The difference homomorphism.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A = SteenrodAlgebra(2)
            sage: homspace = Hom(FreeModule((0,1), A), FreeModule((2,), A))
            sage: N = homspace.codomain()
            sage: values = [Sq(5)*N.generator(0), Sq(3,1)*N.generator(0)]
            sage: f = homspace(values)
            sage: values2 = [Sq(5)*N.generator(0), Sq(3,1)*N.generator(0)]
            sage: g = homspace(values2)
            sage: f.__sub__(g)
            The trivial homomorphism.

        """

        return self.__add__(g.__neg__())


    def __mul__(self, g):
        r"""
        The composition of the given homomorphism ``g``, followed by this
        homomorphisms.

        OUTPUT:
        
        A homomorphism from the domain of this homomorphism, into the codomain
        of the homomorphism ``g``.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FreeModule((0,1), A)
            sage: N = FreeModule((2,), A)
            sage: values = [Sq(5)*N.generator(0), Sq(3,1)*N.generator(0)]
            sage: f = Hom(M, N)(values)
            sage: values2 = [Sq(2)*M.generator(0)]
            sage: g = Hom(N, M)(values2)
            sage: fg = f.__mul__(g); fg
            Module homomorphism of degree 7 defined by sending the generators
              [<1>]
            to
              [<Sq(4,1) + Sq(7)>]
            sage: fg.is_endomorphism()
            True

        TESTS:

            sage: from sage.modules.fp_modules.free_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FreeModule((0,1), A)
            sage: values = [Sq(5)*N.generator(0), Sq(3,1)*N.generator(0)]
            sage: f = Hom(M, N)(values)
            sage: f.__mul__(f)
            Traceback (most recent call last):
            ...
            ValueError: Morphisms are not composable.

        """

        if self.parent().domain() != g.parent().codomain():
            raise ValueError("Morphisms are not composable.")
        homset = Hom(g.parent().domain(), self.parent().codomain())
        return homset([self(g(x)) for x in g.domain().generators()])


    def is_zero(self):
        r"""
        Decide if this homomomorphism is trivial.

        OUTPUT:
        
        The boolean value ``True`` if this homomorphism is trivial, and
        ``False`` otherwise.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FreeModule((0,1), A)
            sage: N = FreeModule((2,), A)
            sage: values = [Sq(5)*N.generator(0), Sq(3,1)*N.generator(0)]
            sage: f = Hom(M, N)(values)
            sage: f.is_zero()
            False
            sage: (f-f).is_zero()
            True

        """
        return all([x.is_zero() for x in self._values])


    def is_identity(self):
        r"""
        Decide if this homomomorphism is the identity endomorphism.

        OUTPUT:
        
        The boolean value ``True`` if this homomorphism is the identity, and
        ``False`` otherwise.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FreeModule((0,1), A)
            sage: N = FreeModule((2,), A)
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

        -  ``x``  - An element of the domain of the morphism.

        OUTPUT: 
        
        The module element of the codomain which is the value of ``x`` under
        this homomorphism.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FreeModule((0,1), A)
            sage: N = FreeModule((2,), A)
            sage: values = [Sq(5)*N.generator(0), Sq(3,1)*N.generator(0)]
            sage: f = Hom(M, N)(values)
            sage: f.__call__(M.generator(0))
            <Sq(5)>
            sage: f.__call__(M.generator(1))
            <Sq(3,1)>

        """

        if x.parent() != self.domain():
            raise ValueError("Cannot evaluate morphism on element not in the domain.")

        value = sum([c*v for c, v in zip(
            x.coefficients(), self._values)], self.codomain()(0))

        return value


    def _repr_(self):
        r"""
        A string representation of this homomorphism.

        OUTPUT:
        
        A string.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FreeModule((0,1), A)
            sage: N = FreeModule((2,), A)
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
            r = "Module homomorphism of degree {} defined by sending the generators\n  {}\nto\n  {}"
            return r.format(self._degree, self.domain().generators(), self._values)


    @cached_method
    def vector_presentation(self, n):
        r"""
        The restriction of this homomorphism to the domain module elements of
        degree ``n``.

        The restriction of a module homomorphism to the vectorspace of module
        elements of degree `n` is a linear function into the vectorspace of
        elements of degree `n+d` belonging to the codomain.  Here `d` is the
        degree of this homomorphism.

        INPUT:

        - ``n`` -- An integer degree.

        OUTPUT:
        
        A linear function over finite dimensional vectorspaces over the ground
        field of the algebra for this module.  The domain of this linear
        function is isomorphic to the vectorspace of domain elements of degree
        ``n`` of this free module, via the choice of basis given by
        :meth:`sage.modules.fp_modules.free_module.FreeModule.basis_elements`.

        .. SEEALSO::

            :meth:`sage.modules.fp_modules.free_module.FreeModule.vector_presentation`,
            :meth:`sage.modules.fp_modules.free_module.FreeModule.basis_elements`.

        EXAMPLES::

            sage: from sage.modules.fp_modules.free_module import FreeModule
            sage: A = SteenrodAlgebra(2)
            sage: M = FreeModule((0,1), A)
            sage: N = FreeModule((2,), A)
            sage: values = [Sq(5)*N.generator(0), Sq(3,1)*N.generator(0)]
            sage: f = Hom(M, N)(values)
            sage: f.vector_presentation(0)
            Vector space morphism represented by the matrix:
            [0 1]
            Domain: Vector space of dimension 1 over Finite Field of size 2
            Codomain: Vector space of dimension 2 over Finite Field of size 2
            sage: f.vector_presentation(1)
            Vector space morphism represented by the matrix:
            [0 0 0]
            [0 1 0]
            Domain: Vector space of dimension 2 over Finite Field of size 2
            Codomain: Vector space of dimension 3 over Finite Field of size 2
            sage: f.vector_presentation(2)
            Vector space morphism represented by the matrix:
            [0 0 1 1]
            [0 0 0 0]
            Domain: Vector space of dimension 2 over Finite Field of size 2
            Codomain: Vector space of dimension 4 over Finite Field of size 2

        """

        codomain_degree = n
        if self._degree != None:
            codomain_degree += self._degree

        D_n = self.domain().vector_presentation(n)
        C_n = self.codomain().vector_presentation(codomain_degree)

        if self._degree == None:
            return Hom(D_n, C_n).zero()
        else:
            values = [self(e).vector_presentation() for e in self.domain().basis_elements(n)]
            return Hom(D_n, C_n)(values)



