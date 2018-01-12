"""

AUTHORS:

"""
from __future__ import absolute_import

from sage.algebras.steenrod.steenrod_algebra import SteenrodAlgebra

import sage.modules.fpmods.utility as Utility
import sage.modules.fpmods.profile as Profile

from sage.modules.fpmods.fpmods import FP_Module

from sage.categories.homset import Hom
from sage.modules.free_module import VectorSpace
from sage.rings.finite_rings.finite_field_constructor import FiniteField

import sage.categories.morphism
import sage.categories.homset

from sage.structure.sequence import Sequence
from sage.rings.infinity import PlusInfinity

from inspect import isfunction
from copy import copy


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

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: F1 = FP_Module(degs = (4,5));
            sage: F2 = FP_Module(degs = (3,4));
            sage: F3 = FP_Module(degs = (2,3));
            sage: H1 = Hom(F1, F2);
            sage: H2 = Hom(F2, F3);
            sage: f = H1( ( F2((Sq(1), 0)), F2((0, Sq(1))) ) )
            sage: g = H2( ( F3((Sq(1), 0)), F3((0, Sq(1))) ) )
            sage: f*g
            Traceback (most recent call last):
             ...
            ValueError: Morphisms not composable.
            sage: g*f
            The trivial module homomorphism:
              Domain: Finitely presented module on 2 generators and 0 relations ...
              Codomain: Finitely presented module on 2 generators and 0 relations ...
            sage: Q1 = FP_Module(degs = (2,3), relations = ((Sq(6), Sq(5)),)); Q1
            Finitely presented module on 2 generators and 1 relation ...
            sage: w = Hom(F1, F1)(( F1((Sq(6), Sq(5))), F1(0) )); w
            Module homomorphism of degree 6:
              Domain: Finitely presented module on 2 generators and 0 relations ...
              Codomain: Finitely presented module on 2 generators and 0 relations ...
            defined by sending the generators
              [<1, 0>, <0, 1>]
            to
              [<Sq(6), Sq(5)>, <0, 0>]
            sage: Q2, p = w.cokernel(); Q2
            Finitely presented module on 2 generators and 1 relation ...
            sage: Q2.get_rels()
            [(Sq(6), Sq(5))]
            sage: x = F1((Sq(7)*Sq(6), Sq(7)*Sq(5))); x
            <Sq(7,2), Sq(3,3)>
            sage: x.is_zero()
            False
            sage: y = p(x); y
            <0, 0>
            sage: y.is_zero()
            True
            sage: x2 = F1((Sq(5)*Sq(8), Sq(4)*Sq(4)*Sq(4)));
            sage: (x + x2) == x
            False
            sage: p(x + x2) == p(x2)
            True
            sage: K, i = p.kernel(); K
            Finitely presented module on 1 generator and 3 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [3, 2, 1]
            sage: i
            Module homomorphism of degree 0:
              Domain: Finitely presented module on 1 generator and 3 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [3, 2, 1]
              Codomain: Finitely presented module on 2 generators and 0 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function []
            defined by sending the generators
              [<1>]
            to
              [<Sq(6), Sq(5)>]
            sage: S, epi, mono = p.image(); S
            Finitely presented module on 2 generators and 1 relation over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [3, 2, 1]
            sage: p(x + x2) == mono(epi(x + x2))
            True

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
        Composition of morphisms: self \circ g
        """
        if self.parent().domain() != g.parent().codomain():
            raise ValueError, "Morphisms not composable."
        homset = Hom(g.parent().domain(), self.parent().codomain())
        return homset([self(g(x)) for x in g.domain().gens()])

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


    def get_values(self):
        """
            Returns a tuple of elements in the codomain, corresponding to the
            value of the generator elements of the domain.

            This defines the morphism.
            
        """
        return self.values

    def suspension(self,t):
        """
        Suspends an FP_Hom, which requires suspending the domain and codomain as well.

        INPUT:

        -  ``t``  - The degree by which the homomorphism is suspended.

        OUTPUT: The FP_Hom suspended by degree `t`.

        EXAMPLES::

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: F1 = FP_Module(degs = (4,5));
            sage: F2 = FP_Module(degs = (3,4));
            sage: H1 = Hom(F1, F2);
            sage: f = H1( ( F2((Sq(1), 0)), F2((0, Sq(1))) ) ); f
            Module homomorphism of degree 0:
              Domain: Finitely presented module on 2 generators and 0 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function []
              Codomain: Finitely presented module on 2 generators and 0 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function []
            defined by sending the generators
              [<1, 0>, <0, 1>]
            to
              [<Sq(1), 0>, <0, Sq(1)>]
            sage: e1 = F1((1, 0))
            sage: e2 = F2((0, 1))
            sage: f(e1)
            <Sq(1), 0>
            sage: f(e2)
            <0, Sq(1)>
            sage: sf = f.suspension(4); sf
            Module homomorphism of degree 1:
              Domain: Finitely presented module on 2 generators and 0 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function []
              Codomain: Finitely presented module on 2 generators and 0 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function []
            defined by sending the generators
              [<1, 0>, <0, 1>]
            to
              [<Sq(1), 0>, <0, Sq(1)>]
        """
        if t == 0:
            return self
        else:
            D = self.domain().suspension(t)
            C = self.codomain().suspension(t)
            homset = Hom(D, C)
            return homset([D(x._get_coefficients()) for x in self.values])


    def cokernel(self,min=False):
        """
        Computes the cokernel of an FP Hom.


        Cheap way of computing cokernel. Cokernel is on same degs as codomain,
        with rels = codomain.rels + self.values. Returns cokernel and the
        projection map to it.

        OUTPUT:

        -  ``coker``  - The FP_Module corresponding to the cokernel of self.

        -  The FP_Hom corresponding to the natural projection from self.codomain
           to `coker`.

        EXAMPLES::


        """
        newRelations = list(self.codomain().get_rels())
        for value in self.get_values():
            newRelations.append(tuple(value._get_coefficients()))

        coker = FP_Module(degs = tuple(self.codomain().get_degs()),\
                relations = tuple(newRelations),\
                algebra = self.algebra)

        homset = Hom(self.codomain(), coker)

        # Create the quotient of the identity morhpism.
        n = len(self.codomain().get_degs())
        values = [coker( tuple(Utility._del_(i, n)) ) for i in range(n)]

        p = homset(values)

        if min == False:
            return coker, p
        else:
            MM, e, m = coker.min_pres()
            return MM, e*p


    def kernel(self):
        """
        Computes the kernel of an FP_Hom, as an FP_Module.
        The kernel is non-zero in degrees starting from connectivity of domain
        through the top degree of the algebra the function is defined over plus
        the top degree of the domain.

        OUTPUT:

        -  ``ker``  - An FP_Module corresponding to the kernel of `self`.

        -  ``incl``  - An FP_Hom corresponding to the natural inclusion of `ker`
                       into the domain.

        EXAMPLES::
        """
        n = self.domain().conn()
        if n == PlusInfinity():
            ker = FP_Module(())
            return ker, Hom(ker, self.domain())(0)

        notdone = True
        limit = Utility.max_deg(self.alg()) + max(self.domain().get_degs())

        while notdone and n <= limit:
            fn = self._pres_(n)
            notdone = (fn.kernel().dimension() == 0)
            if notdone:  # so the kernel is 0 in this degree n. Move on to the next.
                n += 1
        if notdone: # If the kernel is 0 in all degrees.
            ker = FP_Module(degs = (), relations = (), algebra=self.alg())
            return ker, Hom(ker, self.domain())(0)
        else:
            ker = FP_Module(fn.kernel().dimension()*(n,), relations=(), algebra=self.alg())
            quo,q,sec,bas_gen = self.domain()._pres_(n,profile=self.profile())
            incl = Hom(ker, self.domain())(
                   [self.domain()._lc_(sec(v), bas_gen) for v in fn.kernel().basis()])
            n += 1
            while n <= limit:
                incln,Kn,p,sec,bas,Mn,q,s,Mbas_gen = incl._full_pres_(n)
                fn = self._pres_(n)
                if fn.kernel().dimension() != 0:  # so we found something new
                    Kfn = VectorSpace(FiniteField(self.domain().profile_algebra()._prime),\
                                   fn.kernel().dimension())
                    kin = Hom(Kfn,Mn)(fn.kernel().basis())
                    jn = Hom(Kn,Kfn)(kin.matrix().solve_left(incln.matrix()))
                    imjn = jn.image()
                    num_new_gens = 0
                    for v in Kfn.basis():
                        if not v in imjn:
                            num_new_gens += 1
                            imjn += Kfn.subspace([v])
                            incl.values.append(self.domain()._lc_(s(kin(v)),Mbas_gen))
                    ker.degs += num_new_gens*[n]
                    pad = num_new_gens*[0]
                    ker.rels = [x + copy(pad) for x in ker.rels]

                # Add relations.
                ker.rels += [ker._lc_(sec(v),bas)._get_coefficients() for v in incln.kernel().basis()]
                ker.reldegs += incln.kernel().dimension()*[n]
                n += 1
            # All generators have been found.  Now see if we need any more relations.
            while n <= Utility.max_deg(self.alg()) + max(ker.get_degs()):
                incln,Kn,p,sec,bas,Mn,q,s,Mbas_gen = incl._full_pres_(n, profile=self.profile())
                ker.rels += [ker._lc_(sec(v),bas)._get_coefficients() for v in incln.kernel().basis()]
                ker.reldegs += incln.kernel().dimension()*[n]
                n += 1
            ker.algebra = SteenrodAlgebra(p=ker.char, profile = ker.min_profile())
            incl.algebra = SteenrodAlgebra(p=ker.char, profile = incl.min_profile())
            return ker, incl


    def image(self):
        """
        Computes the Image of an FP_Hom, as an FP_Module. Returns the factorization of
        self into epi, Image, mono.

        Assumes generators of FP_Modules are in order of increasing degree.

        OUTPUT:

        -  ``F``  - The FP_Module corresponding to the image of self.

        -  ``mono``  - The FP_Hom corresponding to the natural inclusion of `F` into
                    the codomain of self.

        -  ``epi``  - The FP_Hom corresponding to the natural projection of the
                    domain of self onto `F`.

        EXAMPLES::

        """

        F = FP_Module((), algebra = self.alg())
        mono = Hom(F, self.codomain())([])
        epivals = []

        # Loop to find a minimal set of generators for the image.
        for i in range(len(self.domain().get_degs())):
            n = self.domain().get_degs()[i]
            pn,Fquo,Fq,Fsec,Fbas,Cquo,Cq,Csec,Cbas = mono._full_pres_(n, profile=self.profile())
            v = self.values[i].vec(profile=self.profile())[0]
            if Cquo(v) in pn.image():
                y = pn.matrix().solve_left(Cquo(v))

                # Now convert the vector y into an FP_Element using lc
                epivals.append(F._lc_(Fsec(y),Fbas))
            else:
                F.degs.append(n)
                epivals.append(F.gen(len(F.get_degs())-1))
                mono.values.append(self.values[i])

        # Now compute the relations
        K,i = mono.kernel()
        F.reldegs = K.degs
        F.rels = [x._get_coefficients() for x in i.values]
        l = len(F.degs)
        epivals = [ F(x._get_coefficients() + [0]*(l - len(x._get_coefficients()))) for x in epivals]
        epi = Hom(self.domain(), F)(epivals)

        # Now reduce profile functions
        F.algebra = SteenrodAlgebra(p=F.char, profile = F.min_profile())
        mono.algebra = SteenrodAlgebra(p=F.char,profile =  mono.min_profile())
        epi.algebra = SteenrodAlgebra(p=F.char, profile = epi.min_profile())
        return F,epi,mono

