"""

AUTHORS:

"""
from __future__ import absolute_import

from sage.algebras.steenrod.steenrod_algebra import SteenrodAlgebra

import sage.modules.fpmods.utility as Utility
import sage.modules.fpmods.profile as Profile

from sage.categories.homset import Hom
from sage.modules.free_module import VectorSpace

import sage.categories.morphism
import sage.categories.homset

from sage.structure.sequence import Sequence

from inspect import isfunction


def is_FP_ModuleMorphism(x):
    """
    EXAMPLES::

        sage: V = ZZ^2; f = V.hom([V.1,-2*V.0])
        sage: sage.modules.free_module_morphism.is_FreeModuleMorphism(f)
        True
        sage: sage.modules.free_module_morphism.is_FreeModuleMorphism(0)
        False
    """
    return isinstance(x, FP_ModuleMorphism)


class FP_ModuleMorphism(sage.categories.morphism.Morphism):
    def __init__(self, parent, values):
        """
        INPUT:

            -  ``parent`` - a homspace in a (sub) category of fp modules

            -  ``values`` - ...

        EXAMPLES::

        """
        from .fpmod_homspace import is_FP_ModuleHomspace
        if not is_FP_ModuleHomspace(parent):
            raise TypeError("parent (=%s) must be a fp module hom space" % parent)

        # Get the values.
        C = parent.codomain()
        D = parent.domain()
        if isfunction(values):
            _values = [C(values(g)) for g in D.gens()]
        elif values == 0:
            _values = len(D.gens())*[C(0)]
        else:
            _values = [C(a) for a in values]

        # Check the homomorphism is well defined.
        if len(D.gens()) != len(_values):
            raise ValueError, "The number of values must equal the number of" \
                "generators in the domain.  Invalid argument: %s." % _values

        if len(_values) == 0:
            raise ValueError, "Invalid argument: %s." % _values

        if all(v.is_zero() for v in _values):
            # The zero homomoprhism does not get a degree.
            self.degree = None
        else:
            # Check the homomorphism is well defined.
            self.degree = _values[0].get_degree() - D.get_degs()[0]
            if not all(not v.get_degree() or self.degree == (v.get_degree() - g) \
                       for g, v in zip(D.get_degs(), _values)):
                errorMessage = "Ill defined homomorphism (degrees do not match)\n"
                gen_index = 0
                for g, v in zip(D.get_degs(), _values):
                    errorMessage += "  Generator #%d (degree %d) -> %s (degree %d)"\
                        " shifts degrees by %d\n" % (
                        gen_index, g, v, v.get_degree(), v.get_degree() - g)
                    gen_index += 1
                raise ValueError, errorMessage

            # Check the homomorphism is well defined.
            for relation in parent.domain().get_rels():
                r = sum ([c*v for c, v in zip(relation, _values)], parent.codomain().zero())
                if not r.is_zero():
                    raise ValueError, "Relation %s is not sent to zero" % relation

        self.values = _values

        sage.categories.morphism.Morphism.__init__(self, parent)

#        initialval = D([0]*len(D.get_degs()))
#
#        prof = Profile.enveloping_profile_profiles([D.profile(), C.profile(),\
#                      Profile.enveloping_profile_elements(reduce(lambda x,y: x+y,\
#                           [x._get_coefficients() for x in _values], initialval._get_coefficients()),\
#                            D.char)], D.char)

        self.algebra = SteenrodAlgebra(p = D.profile_algebra().prime(), profile = self.min_profile())



    def profile(self):
        return self.algebra._profile

    def alg(self):
        return self.algebra



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


    def get_degree(self):
        """
        """
        return self.degree

    def __add__(self, g):
        """
        Sum the homomorphisms, so (f+g)(x) == f(x)+g(x)
        """

        if self.domain() != g.domain():
            raise ValueError,\
            "Morphisms do not have the same domain."
        elif self.codomain() != g.codomain():
            raise ValueError,\
            "Morphisms do not have the same codomain."
        elif self.get_degree() and g.get_degree() and self.get_degree() != g.get_degree():
            raise ValueError,\
            "Morphisms do not have the same degree."

        v = [self(x) + g(x) for x in self.domain().gens()]

        return self.parent()(v)

    def __neg__(self):
        return self.parent()([-x for x in self.values])

    def __sub__(self, g):
        return self.__add__(g.__neg__())

    def __mul__(self, g):
        """
        Composition of morphisms.
        """
        if self.domain != g.codomain:
            raise ValueError, "Morphisms not composable."
        return self.parent()([self(g(x)) for x in g.domain().gens()])

    def is_zero(self):
        """
        """
        return all([x.is_zero() for x in self.values])

    def is_identity(self):
        """
        """
        if self.parent().is_endomorphism_set():
            return self.parent().identity() == self
        else:
            return False

    def __call__(self, x):
        """
        Evaluate the morphism at an FP_Element of domain.

        INPUT:

        -  ``x``  - An element of the domain of self.

        OUTPUT: The FP_Hom evaluated at `x`.

        EXAMPLES::


        """
        if x not in self.domain():
            raise ValueError,\
                  "Cannot evaluate morphism on element not in domain"

        value = sum([c*v for c, v in zip(
            x._get_coefficients(), self.values)], self.codomain()(0))

        return value.normalize()

    def _repr_(self):
        r"""
        Return string representation of this morphism of free modules.
        """
        if self.is_zero():
            r = "The trivial module homomorphism:\n  Domain: {}\n  Codomain: {}"
            return r.format(self.domain(), self.codomain())
        elif self.is_identity():
            r = "The identity module homomorphism:\n  Domain: {}\n  Codomain: {}"
            return r.format(self.domain(), self.codomain())
        else:
            r = "Module homomorphism of degree {}:\n  Domain: {}\n  Codomain: {}\ndefined by sending the generators\n  {}\nto\n  {}"
            return r.format(self.degree, self.domain(), self.codomain(), self.domain().gens(), self.values)


    def _full_pres_(self,n,profile=None):
        """
        Computes the linear transformation from domain in degree n
        to codomain in degree n+degree(self). 9 items returned: the
        linear transformation, self.dom._pres_(n), & self.codomain._pres_(n).
        See the documentation for _pres_ in class FP_Module for further explanation.

        INPUT:

        -  ``n``  - The degree in which all computations are made.

        -  ``profile``  - A profile function corresponding to the sub-Hopf algebra
             of the Steenrod Algebra for which this computation will be computed over.
             The default, `profile=None`, uses the profile of self.

        OUTPUT:

        -  The linear transformation corresponding to the degree `n` piece of this
           mapping (see the documentation for _pres_ below).

        -  ``dquo``  - The vector space corresponding to self.domain in degree `n`.

        -  ``dq``  - The quotient map from the vector space for the free module on
           the generators to `dquo`.

        -  ``dsec``  - Elements of the domain of `dq` which project to the standard
           basis for `dquo`.

        -  ``dbas_gen``  - A list of pairs (gen_number, algebra element)
           corresponding to the standard basis for the free module.

        -  ``cquo``  - The vector space corresponding to self.codomain in degree `n` +
           self.degree.

        -  ``cq``  - The quotient map from the vector space for the free module on
           the generators to `cquo`.

        -  ``csec``  - Elements of the domain of `cq` which project to the standard basis
           for `cquo`.

        -  ``cbas_gen``  - A list of pairs (gen_number, algebra element) corresponding
           to the standard basis for the free module.

        EXAMPLES::

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: M = FP_Module((2,3),((Sq(2),Sq(1)),))
            sage: N = FP_Module((2,3),((Sq(2),Sq(1)),(0,Sq(2))))
            sage: f = Hom(M,N).an_element();
            sage: f._full_pres_(9)
            (Vector space morphism represented by the matrix:
             []
             Domain: Vector space quotient V/W of dimension 0 over Finite Field of size 2 where
             V: Vector space of dimension 1 over Finite Field of size 2
             W: Vector space of degree 1 and dimension 1 over Finite Field of size 2
             Basis matrix:
             [1]
             Codomain: Vector space quotient V/W of dimension 0 over Finite Field of size 2 where
             V: Vector space of dimension 1 over Finite Field of size 2
             W: Vector space of degree 1 and dimension 1 over Finite Field of size 2
             Basis matrix:
             [1],
             Vector space quotient V/W of dimension 0 over Finite Field of size 2 where
             V: Vector space of dimension 1 over Finite Field of size 2
             W: Vector space of degree 1 and dimension 1 over Finite Field of size 2
             Basis matrix:
             [1],
             Vector space morphism represented by the matrix:
             []
             Domain: Vector space of dimension 1 over Finite Field of size 2
             Codomain: Vector space quotient V/W of dimension 0 over Finite Field of size 2 where
             V: Vector space of dimension 1 over Finite Field of size 2
             W: Vector space of degree 1 and dimension 1 over Finite Field of size 2
             Basis matrix:
             [1],
             Vector space morphism represented by the matrix:
             []
             Domain: Vector space quotient V/W of dimension 0 over Finite Field of size 2 where
             V: Vector space of dimension 1 over Finite Field of size 2
             W: Vector space of degree 1 and dimension 1 over Finite Field of size 2
             Basis matrix:
             [1]
             Codomain: Vector space of dimension 1 over Finite Field of size 2,
             [(1, Sq(3,1))],
             Vector space quotient V/W of dimension 0 over Finite Field of size 2 where
             V: Vector space of dimension 1 over Finite Field of size 2
             W: Vector space of degree 1 and dimension 1 over Finite Field of size 2
             Basis matrix:
             [1],
             Vector space morphism represented by the matrix:
             []
             Domain: Vector space of dimension 1 over Finite Field of size 2
             Codomain: Vector space quotient V/W of dimension 0 over Finite Field of size 2 where
             V: Vector space of dimension 1 over Finite Field of size 2
             W: Vector space of degree 1 and dimension 1 over Finite Field of size 2
             Basis matrix:
             [1],
             Vector space morphism represented by the matrix:
             []
             Domain: Vector space quotient V/W of dimension 0 over Finite Field of size 2 where
             V: Vector space of dimension 1 over Finite Field of size 2
             W: Vector space of degree 1 and dimension 1 over Finite Field of size 2
             Basis matrix:
             [1]
             Codomain: Vector space of dimension 1 over Finite Field of size 2,
             [(1, Sq(3,1))])

        """
        if profile == None:
            profile = self.profile()
        dquo,dq,dsec,dbas_gen = self.parent().domain()._pres_(n, profile=profile)
        cquo,cq,csec,cbas_gen = self.parent().codomain()._pres_(n, profile=profile)
        return Hom(dquo,cquo)(
            [cq(self(self.parent().domain()._lc_(dsec(x), dbas_gen)).free_vec(profile=profile))\
            for x in dquo.basis()]),\
            dquo,dq,dsec,dbas_gen,\
            cquo,cq,csec,cbas_gen

    def _pres_(self,n,profile=None):
        """
        Computes the linear transformation from domain in degree n to
        codomain in degree n + degree(self). Intended for internal use only.

        INPUT:

        -    ``n``  - The degree in which all computations are made.

        -    ``profile``  - A profile function corresponding to the sub-Hopf algebra
             of the Steenrod Algebra for which this computation will be computed over.

        OUTPUT: The linear transformation from the degree `n` part of self.domain
                to the degree `n` + self.degree part of self.codomain. The basis for
                the vector space corresponding to the deg `n` piece of self.domain
                is mapped to the basis for the deg `n` + self.degree piece of self.codomain.

        EXAMPLES::

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: M = FP_Module((2,3),((Sq(2),Sq(1)),))
            sage: N = FP_Module((2,3),((Sq(2),Sq(1)),(0,Sq(2))))
            sage: f = Hom(M,N).an_element(); f
            The trivial module homomorphism:
              Domain: Finitely presented module on 2 generators and 1 relation ...
              Codomain: Finitely presented module on 2 generators and 2 relations ...
            sage: f._pres_(9)
            Vector space morphism represented by the matrix:
            []
            Domain: Vector space quotient V/W of dimension 0 over Finite Field of size 2 where
            V: Vector space of dimension 1 over Finite Field of size 2
            W: Vector space of degree 1 and dimension 1 over Finite Field of size 2
            Basis matrix:
            [1]
            Codomain: Vector space quotient V/W of dimension 0 over Finite Field of size 2 where
            V: Vector space of dimension 1 over Finite Field of size 2
            W: Vector space of degree 1 and dimension 1 over Finite Field of size 2
            Basis matrix:
            [1]

        """
        return self._full_pres_(n, profile)[0]


    def min_profile(self):
        """
        Returns the profile function for the smallest sub-Hopf algebra over which self
        is defined.

        This function is useful when reducing to the smallest profile function (and sub-Hopf algebra)
        an FP_Module can be defined over.

        OUTPUT:

        -  ``profile``  - The profile function corresponding to the smallest sub-Hopf algebra
                          containing self.

        EXAMPLES::

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: M = FP_Module((2,3),((Sq(2),Sq(1)),))
            sage: N = FP_Module((2,3),((Sq(2),Sq(1)),(0,Sq(2))))
            sage: f = Hom(M,N).an_element();
            sage: f.min_profile()
            (2, 1)

        """
        C = self.parent().codomain()
        D = self.parent().domain()
        initialval = D([0]*len(D.get_degs()))
        profile = Profile.enveloping_profile_profiles([D.profile(), C.profile(),\
                      Profile.enveloping_profile_elements(reduce(lambda x,y: x+y,\
                           [x._get_coefficients() for x in self.values], initialval._get_coefficients()),\
                            D.char)], D.char)

        return profile


