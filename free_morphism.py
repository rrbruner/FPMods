r"""
Morphisms of Finitely generated free modules.

EXAMPLES::

<Lots and lots of examples>

AUTHORS:

    - Robert R. Bruner, Michael J. Catanzaro (2012): initial version
    - Koen (date in ISO year-month-day format): Updating to Sage 8.1
    - Sverre (date in ISO 2018-month-day format): Updating to Sage 8.1
    - Sverre (date in ISO 2019-month-day format): Rewrite and refactor.

"""



from __future__ import absolute_import

from sage.categories.homset import Hom

import sage.categories.morphism
import sage.categories.homset

from sage.misc.cachefunc import cached_method

from inspect import isfunction
from .free_homspace import is_FreeModuleHomspace

from sage.categories.morphism import Morphism as SageMorphism

class FreeModuleMorphism(SageMorphism):

    def __init__(self, parent, values):
        r"""
        INPUT:

        - ``parent`` -- A homspace in the category of finitely generated free
            modules.

        - ``values`` -- A list of elements in the codomain.  Each element
            corresponds (by their ordering) to a module generator in the domain.

        OUTPUT: A module homomorphism defined by sending generator with index
        `i` to the element in the comdomain which has index `i` in the given
        input list.

        EXAMPLES:

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.free_module import FreeModule
            sage: A = SteenrodAlgebra(2)
            sage: F1 = FreeModule((4,5), A)
            sage: F2 = FreeModule((3,4), A)
            sage: F3 = FreeModule((2,3), A)
            sage: H1 = Hom(F1, F2)
            sage: H2 = Hom(F2, F3)
            sage: f = H1( ( F2((Sq(1), 0)), F2((0, Sq(1))) ) )
            sage: g = H2( ( F3((Sq(1), 0)), F3((0, Sq(1))) ) )
            sage: f*g
            Traceback (most recent call last):
             ...
            ValueError: Morphisms not composable.
            sage: g*f
            The trivial module homomorphism.

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
            raise ValueError, "The number of values must equal the number of " \
                "generators in the domain.  Invalid argument: %s." % _values

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
                raise ValueError, errorMessage

        self._values = _values

        SageMorphism.__init__(self, parent)

    def degree(self):
        return self._degree

    def values(self):
        return self._values

    def _richcmp_(self, other, op):
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
        """
        if self.domain() != g.domain():
            raise ValueError,\
            "Morphisms do not have the same domain."
        elif self.codomain() != g.codomain():
            raise ValueError,\
            "Morphisms do not have the same codomain."
        elif self._degree and g.degree() and self._degree != g.degree():
            raise ValueError,\
            "Morphisms do not have the same degree."

        v = [self(x) + g(x) for x in self.domain().generators()]

        return self.parent()(v)

    def __neg__(self):
        return self.parent()([-x for x in self._values])

    def __sub__(self, g):
        return self.__add__(g.__neg__())

    def __mul__(self, g):
        r"""
        Composition of morphisms: $self \circ g$
        """
        if self.parent().domain() != g.parent().codomain():
            raise ValueError, "Morphisms not composable."
        homset = Hom(g.parent().domain(), self.parent().codomain())
        return homset([self(g(x)) for x in g.domain().generators()])

    def is_zero(self):
        r"""
        """
        return all([x.is_zero() for x in self._values])

    def is_identity(self):
        r"""
        """
        if self.parent().is_endomorphism_set():
            return self.parent().identity() == self
        else:
            return False

    def __call__(self, x):
        r"""
        """
        if x.parent() != self.domain():
            raise ValueError,\
                  "Cannot evaluate morphism on element not in domain"

        value = sum([c*v for c, v in zip(
            x.coefficients(), self._values)], self.codomain()(0))

        return value

    def _repr_(self):
        r"""
        A string representation of this morphism.
        """
        if self.is_zero():
            return "The trivial module homomorphism."
        elif self.is_identity():
            return "The identity module homomorphism."
        else:
            r = "Module homomorphism of degree {} defined by sending the generators\n  {}\nto\n  {}"
            return r.format(self._degree, self.domain().generators(), self._values)

    @cached_method
    def vector_presentation(self, n):
        r"""
        """
        codomain_degree = n + (self._degree if self._degree != None else 0)

        D_n = self.domain().vector_presentation(n)
        C_n = self.codomain().vector_presentation(codomain_degree)

        if self._degree == None:
            return Hom(D_n, C_n).zero()
        else:
            values = [self(e).vector_presentation() for e in self.domain().basis_elements(n)]
            return Hom(D_n, C_n)(values)

