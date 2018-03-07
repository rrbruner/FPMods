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
            sage: p = w.cokernel()
            sage: Q2 = p.codomain(); Q2
            Finitely presented module on 2 generators and 1 relation ...
            sage: Q2.get_rels()
            ((Sq(6), Sq(5)),)
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
            sage: i = p.kernel(); i.domain()
            Finitely presented module on 1 generator and 3 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [3, 2, 1]
            sage: i
            Module homomorphism of degree 0:
              Domain: Finitely presented module on 1 generator and 3 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [3, 2, 1]
              Codomain: Finitely presented module on 2 generators and 0 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function []
            defined by sending the generators
              [<1>]
            to
              [<Sq(6), Sq(5)>]
            sage: mono,epi = p.image(); mono.domain()
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
            raise ValueError, "The number of values must equal the number of " \
                "generators in the domain.  Invalid argument: %s." % _values

        if all(v.is_zero() for v in _values):
            # The zero homomorphism does not get a degree.
            self.degree = None
        else:
            # Check the homomorphism is well defined.

            # Find the first non-zero value.
            for i, value in enumerate(_values):
                if not value.is_zero():
                    self.degree = value.get_degree() - D.get_degs()[i]
                    break

            # check all the remaining ones.
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
                    raise ValueError, ("Relation %s is not sent to zero" % relation)

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

        -  ``x``  - An element of the domain of the morphism.

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
        Return string representation of this morphism.

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
        r"""
        Returns the  linear transformation from domain in degree n
        to codomain in degree n+degree(self). 3 items returned: the
        linear transformation, the domain and codomain generator sets.
        The last two items correspond to isomorphisms between the degree n
        parts of the module and the domain and codomain vector spaces of the
        first return value.

        INPUT:

        -  ``n``  - The degree in which all computations are made.

        -  ``profile``  - A profile function corresponding to the sub-Hopf algebra
             of the Steenrod Algebra for which this computation will be computed over.
             The default, `profile=None`, uses the profile of self.

        OUTPUT:

        -  The linear transformation corresponding to the degree `n` piece of this
           mapping (see the documentation for _pres_ below).

        -  ``dbas_gen``  - A list of pairs (gen_number, algebra element)
           corresponding to the standard basis for the free module.

        -  ``cbas_gen``  - A list of pairs (gen_number, algebra element) corresponding
           to the standard basis for the free module.

        EXAMPLES::

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: M = FP_Module((2,3),((Sq(2),Sq(1)),))
            sage: N = FP_Module((2,3),((Sq(2),Sq(1)),(0,Sq(2))))
            sage: f = Hom(M,N) ( [N((1,0)), N((0,1))] );
            sage: f._full_pres_(2)
            (Vector space morphism represented by the matrix:
             [1]
             Domain: Vector space quotient V/W of dimension 1 over Finite Field of size 2 where
             V: Vector space of dimension 1 over Finite Field of size 2
             W: Vector space of degree 1 and dimension 0 over Finite Field of size 2
             Basis matrix:
             []
             Codomain: Vector space quotient V/W of dimension 1 over Finite Field of size 2 where
             V: Vector space of dimension 1 over Finite Field of size 2
             W: Vector space of degree 1 and dimension 0 over Finite Field of size 2
             Basis matrix:
             [], [(0, 1)], [(0, 1)])
            sage: f._full_pres_(5)
            (Vector space morphism represented by the matrix:
             [1]
             [0]
             Domain: Vector space quotient V/W of dimension 2 over Finite Field of size 2 where
             V: Vector space of dimension 3 over Finite Field of size 2
             W: Vector space of degree 3 and dimension 1 over Finite Field of size 2
             Basis matrix:
             [0 1 0]
             Codomain: Vector space quotient V/W of dimension 1 over Finite Field of size 2 where
             V: Vector space of dimension 3 over Finite Field of size 2
             W: Vector space of degree 3 and dimension 2 over Finite Field of size 2
             Basis matrix:
             [0 1 0]
             [0 0 1],
             [(0, Sq(0,1)), (0, Sq(3)), (1, Sq(2))],
             [(0, Sq(0,1)), (0, Sq(3)), (1, Sq(2))])

        """
        if profile == None:
            profile = self.profile()

        codomain_degree = n + (self.degree if self.degree != None else 0)

        D_n, dbas_gen = self.domain()._pres_(n, profile=profile)
        C_n, cbas_gen = self.codomain()._pres_(codomain_degree, profile=profile)

        if self.degree == None:
            return Hom(D_n, C_n).zero(), dbas_gen, cbas_gen

        target_values = [C_n.quotient_map()(\
            self(self.domain()._lc_(D_n.lift(x), dbas_gen)).free_vec(profile=profile)) for x in D_n.basis()]

        return Hom(D_n, C_n)(target_values),\
            dbas_gen, cbas_gen

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
            sage: f = Hom(M,N) ( [N((1,0)), N((0,1))] )
            sage: f._pres_(6)
            Vector space morphism represented by the matrix:
            [1]
            [1]
            Domain: Vector space quotient V/W of dimension 2 over Finite Field of size 2 where
            V: Vector space of dimension 3 over Finite Field of size 2
            W: Vector space of degree 3 and dimension 1 over Finite Field of size 2
            Basis matrix:
            [1 1 1]
            Codomain: Vector space quotient V/W of dimension 1 over Finite Field of size 2 where
            V: Vector space of dimension 3 over Finite Field of size 2
            W: Vector space of degree 3 and dimension 2 over Finite Field of size 2
            Basis matrix:
            [1 1 0]
            [0 0 1]
        """
        return self._full_pres_(n, profile)[0]


    def min_profile(self):
        """
        Returns the profile function for the smallest sub-Hopf algebra over
        which self is defined.

        This function is useful when reducing to the smallest profile function
        (and sub-Hopf algebra) an FP_Module can be defined over.

        OUTPUT:

        -  ``profile``  - The profile function corresponding to the smallest
                          sub-Hopf algebra containing self.

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
        Compute the cokernel of an FP Hom.

        Cheap way of computing cokernel. Cokernel is on same degs as codomain,
        with rels = codomain.rels + self.values. Returns cokernel and the
        projection map to it.

        OUTPUT:

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
            return p
        else:
            i, e = coker.min_pres()
            return e*p


    def kernel(self):
        """
        Computes the kernel of an FP_Hom, as an FP_Module.
        The kernel is non-zero in degrees starting from connectivity of domain
        through the top degree of the algebra the function is defined over plus
        the top degree of the domain.

        OUTPUT:

        -  ``j``  -  An injective homomorphism K -> self such that 
                     im(j) = ker(self).

        EXAMPLES::

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: F = FP_Module(degs = tuple([1,3]));
            sage: L = FP_Module((2,3),((Sq(2),Sq(1)),(0,Sq(2))));
            sage: homset = Hom(F, L);
            sage: homset([L((Sq(1), 1)), L((0, Sq(2)))]).kernel()
            Module homomorphism of degree 0:
              Domain: Finitely presented module on 2 generators and 1 relation over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [2, 1]
              Codomain: Finitely presented module on 2 generators and 0 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function []
            defined by sending the generators
              [<1, 0>, <0, 1>]
            to
              [<0, 1>, <Sq(0,1), 0>]

        """

        K = FP_Module(degs=(), relations=(), algebra=self.alg())
        j = Hom(K, self.domain()).zero()

        n = self.domain().conn()

        if n == PlusInfinity():
            return j

        limit = Utility.max_deg(self.alg()) + max(self.domain().get_degs())

        self_n = self._pres_(n)
        while n <= limit and self_n.kernel().dimension() == 0:
            n += 1; self_n = self._pres_(n)

        if n > limit:
            return j

        prime = self.alg().prime()

        kernel_n = self_n.kernel()
        # assert : kernel_n.dimension() > 0:

        #
        # Assume by induction that we have created a homomorphism j
        #
        #       j      self
        #    K ---> D ------> C
        #
        # with im(j) contained in ker(self) such that j is an isomorphism in
        # degrees < n.
        #
        # The following code creates a j for the first n such that ker(self)_n != 0
        #
        D_n, bas_gen = self.domain()._pres_(n, profile=self.profile())
        K = FP_Module(tuple(kernel_n.dimension()*[n]), relations=(), algebra=self.alg())
        j = Hom(K, self.domain()) (
               [self.domain()._lc_(D_n.lift(v), bas_gen) for v in kernel_n.basis()])

        #
        # Consider the F_p-linear part of the above diagram by restricting to
        # degree n in the domain.
        #
        #         j_n        self_n
        #    K_n -----> D_n --------> C_n'   ( n' - n = self.degree() )
        #
        # By construction, im(self_n) \subset ker(f_n), but not necessarily
        # onto the kernel.  The loop below improves j in two steps:
        # 1. Introduces new relations in degree n such that j_n becomes 
        #    injective.
        # 2. Adds new generators to K in degree n, and extend j on these
        #    generators to take values in ker(j)_n such that j becomes onto the
        #    kernel.
        #
        # Both steps leave everything in degrees below n as they were.
        #
        while True:
            n += 1
            if n > limit:
                break

            # Find new relations that, when introduced, will make j(n+1)
            # injective.
            j_n, j_n_domain_basis, j_n_codomain_basis = j._full_pres_(n, profile=self.profile())
            new_relations = [tuple(j.domain()._lc_(j_n.domain().lift(v), j_n_domain_basis)._get_coefficients()) \
                             for v in j_n.kernel().basis()]

            # Find the missing values that will make j(n+1) onto the kernel.
            kernel_self_n = self._pres_(n).kernel()

            cokernel_values = []
            if kernel_self_n.dimension() > 0:

                # The matrix giving the lift of j_n into kernel_self_n.
                #
                #            j_n        f_n
                #       K_n -----> D_n -----> C_n
                #
                #         \       /\
                #          \      /
                #          \/    /
                #
                #        kernel_self_n
                #
                lift_j_n = kernel_self_n.basis_matrix().solve_left(j_n.matrix())

                jn = Hom(j_n.domain(), kernel_self_n)(lift_j_n)
                image_j_n = jn.image()
                cokernel_j_n = kernel_self_n.quotient(image_j_n)
                cokernel_values = [
                    self.domain()._lc_(cokernel_j_n.lift(e) , j_n_codomain_basis)\
                        for e in cokernel_j_n.basis()] 

            # Add any new generators found in the loop above.
            num_new_gens = len(cokernel_values)
            new_degs = list(j.domain().get_degs()) + num_new_gens*[n]


            # Pad the existing relations-tuples with zeros.
            relations = [ (r + num_new_gens*(0,)) for r in \
                (list(j.domain().get_rels()) + new_relations) ]

            K = FP_Module(tuple(new_degs), tuple(relations), algebra=self.alg())
            ttv = list(j.get_values()) + cokernel_values
            j = Hom(K, self.domain())(ttv)

        while n <= Utility.max_deg(self.alg()) + max(K.get_degs()):

            j_n, j_n_domain_basis, j_n_codomain_basis = j._full_pres_(n, profile=self.profile())
            new_relations = [tuple(j.domain()._lc_(j_n.domain().lift(v), j_n_domain_basis)._get_coefficients()) \
                             for v in j_n.kernel().basis()]

            rels = list(j.domain().get_rels()) + new_relations

            K = FP_Module(degs=tuple(K.get_degs()), relations=tuple(rels), algebra=self.alg())
            j = Hom(K, self.domain())(j.get_values())

            n += 1

            # XXX todo: reduce profile functions.
            # K._profile_algebra = SteenrodAlgebra(p=K.char, profile = K.min_profile())
            # F._profile_algebra = SteenrodAlgebra(p=K.char, profile = F.min_profile())
            # print ('K.profile():\n%s\n\nK.min_profile(): %s\nj.min_profile(): %s' % (K.profile(), K.min_profile(), j.min_profile()))

        return j

    def image(self):
        """
        Computes the Image of an FP_Hom, as an FP_Module. Returns the factorization of
        self into epi, Image, mono.

        Assumes generators of FP_Modules are in order of increasing degree.

        OUTPUT:

        -  ``mono``  - The FP_Hom corresponding to the natural inclusion of `F` into
                    the codomain of self.

        -  ``epi``  - The FP_Hom corresponding to the natural projection of the
                    domain of self onto `F`, such that mono*epi = self.

        EXAMPLES::

        """

        # Values of the epi homomorphism.
        epi_values = []

        # Generators by degrees.
        image_module_degs = []

        # Values as elements in self.codomain().
        image_module_values = []

        # Loop to find a minimal set of generators for the image.
        for n, v in zip(self.domain().get_degs(), self.values):

            image_module = FP_Module(tuple(image_module_degs), algebra = self.alg())
            mono = Hom(image_module, self.codomain())(image_module_values)

            mono_n, image_module_bas, Cbas = mono._full_pres_(n, profile=self.profile())

            if not mono_n.is_zero():
                free_vector = mono_n.codomain().V().coordinate_vector(v.free_vec(profile=self.profile()))
                v__ = mono_n.codomain().quotient_map()(free_vector)

            if mono_n.is_zero() or not v__ in mono_n.image():
                image_module_degs.append(n)
                image_module_values.append(v)

                # append [0, 0,..., 0, 1] to the values for 'epi'.
                num_degs = len(image_module_degs)
                epi_values.append(Utility._del_(num_degs-1, num_degs))
            else:
                y = mono_n.matrix().solve_left(v__)
                y_ = image_module._lc_(
                        mono_n.domain().lift(y),
                        image_module_bas)
                epi_values.append(y_._get_coefficients())

        # Compute the relations.
        image_module = FP_Module(tuple(image_module_degs), algebra = self.alg())
        mono = Hom(image_module, self.codomain())(image_module_values)

        # Recreate the module again, this time including the relations.
        image_module = FP_Module( \
            degs=tuple(image_module_degs), \
            relations=tuple([tuple(x._get_coefficients()) for x in mono.kernel().get_values()]), \
            algebra = self.alg())

        # Create the monomorphism.
        mono = Hom(image_module, self.codomain())(image_module_values)

        # Create the epimorphism.
        l = len(image_module.get_degs())
        epi_values = [ image_module(x + [0]*(l - len(x))) for x in epi_values ]
        epi = Hom(self.domain(), image_module)(epi_values)

        # XXX todo: reduce profile functions.
        return mono, epi

    def solve(self,x):
        """
        Find an element mapping to ``x`` under this morphism.

        INPUT:

        - ``x`` -- The element we want to lift.

        OUTPUT: An element which maps to ``x`` under this morphism, or
        ``None`` if ``x`` was not in the image of this morphism.

        EXAMPLES::

        """
        if self.is_zero():
            return False, self.domain().zero()

        pn, dbas, cbas =\
            self._full_pres_(x.get_degree() - self.get_degree(), profile=self.profile())
        v = x.vec()[0]

        if x not in self.codomain():
            raise TypeError, "Element not in codomain."
        if v not in pn.image():
            return None
        else:
            w = pn.matrix().solve_left(v)
            return self.domain()._lc_(pn.domain().lift(w), dbas)

