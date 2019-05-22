r"""
<Very short 1-line summary>

<Paragraph description>

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
    The trivial module homomorphism.
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
    sage: y = p(x); y
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


from __future__ import absolute_import
from __future__ import print_function

import sys


from sage.categories.homset import Hom
from sage.categories.morphism import Morphism as SageMorphism
from sage.modules.free_module import VectorSpace
from sage.rings.infinity import PlusInfinity
from sage.misc.cachefunc import cached_method

from .fp_homspace import is_FP_ModuleHomspace
from .fp_element import FP_Element

from sage.structure.unique_representation import UniqueRepresentation

class FP_ModuleMorphism(SageMorphism):

    def __init__(self, parent, values):
        r"""
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
                raise ValueError, ("Relation %s is not sent to zero." % relation)

    def change_ring(self, algebra):
        r"""
            Return the module with a new base ring, but the `same` generators and relations.
        """
        new_codomain = self.codomain().change_ring(algebra)
        new_values = [new_codomain(v.coefficients()) for v in self._values]
        return Hom(self.domain().change_ring(algebra), new_codomain)(new_values)

    def degree(self):
        return self.free_morphism.degree()

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
        Sum the homomorphisms, so (f+g)(x) == f(x)+g(x)
        """

        if self.domain() != g.domain():
            raise ValueError,\
            "Morphisms do not have the same domain."
        elif self.codomain() != g.codomain():
            raise ValueError,\
            "Morphisms do not have the same codomain."
        elif self.degree() and g.degree() and self.degree() != g.degree():
            raise ValueError,\
            "Morphisms do not have the same degree."

        v = [self(x) + g(x) for x in self.domain().generators()]

        return self.parent()(v)

    def __neg__(self):
        return self.parent()([-x for x in self._values])

    def __sub__(self, g):
        return self.__add__(g.__neg__())

    def __mul__(self, g):
        """
        Composition of morphisms: self \circ g
        """
        if self.parent().domain() != g.parent().codomain():
            raise ValueError, "Morphisms not composable."
        homset = Hom(g.parent().domain(), self.parent().codomain())
        return homset([self(g(x)) for x in g.domain().generators()])

    @cached_method
    def is_zero(self):
        """
        """
        return all([x.is_zero() for x in self._values])

    @cached_method
    def is_identity(self):
        """
        """
        if self.parent().is_endomorphism_set():
            # XXX I think this doesn't work.  We need to compare
            #     id.values <-> self._values as FP_Modules.
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
        if x.parent() != self.domain():
            raise ValueError,\
                  "Cannot evaluate morphism on element not in domain"

        return self.codomain().element_class(self.codomain(), self.free_morphism(x.free_element)).normalize()

    def _repr_(self):
        r"""
        Return a string representation of this morphism.

        """
        if self.is_zero():
            return "The trivial module homomorphism."
        elif self.is_identity():
            return "The identity module homomorphism."
        else:
            return "Module homomorphism of degree %d defined by sending "\
                "the generators\n  %s\nto\n  %s" % (self.degree(), self.domain().generators(), self._values)

    @cached_method
    def vector_presentation(self, n):
        r"""
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
            raise ValueError, "The given element is not in the codomain of this homomorphism."

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
            raise TypeError, "Cannot lift this homomorphism over the given map since it has a different codomain."

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
            sage: K = f.kernel(verbose=True, top_dim=16)
            Step 1/2:
            Resolving kernel dimensions up to #17: 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17.
            Step 2/2:
            Resolving kernel dimensions up to #17: 7 8 9 10 11 12 13 14 15 16 17.
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
            print('Step 1/2:')
        j0 = self.resolve_kernel(top_dim, verbose)
        if verbose:
            print('Step 2/2:')
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

        """
        if verbose:
            print('Step 1/2:')
        j0 = self.resolve_image(top_dim, verbose)
        if verbose:
            print('Step 2/2:')
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

    def resolve_image(self, top_dim=None, verbose=False):
        r"""
            Resolve the image of this homomorphism.

        INPUT::
            self
            top_dim

        OUTPUT::
            j: F -> self.codomain()  such that F is free, and im(j) = im(self).

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
        # map `j` minimally so that `j_n` becomes onto the kernel.


        # Create the trivial module F_ to start with.
        # from .fp_module import FP_Module
        F_ = self.domain().__class__((), algebra=self.base_ring())
        j = Hom(F_, self.domain())(())

        if self.degree() == None:
            return j

        ### --- ### --- ###
        n = self.codomain().connectivity()
        if n == PlusInfinity():
            return j

        n -= 1

        limit = (self.base_ring().top_class().degree() + max(self.domain().generator_degrees()))\
            if top_dim is None else top_dim

        if top_dim == PlusInfinity():
            raise ValueError('The user must specify a top dimension for this calculation to terminate.')

        if verbose:
            print('Resolving image dimensions up to #%d:' % (limit+1), end='')

        #print('Self degree: %d' % self.degree())
        #print ('Top dim: %d' % limit)
        while n <= limit:
            n += 1

            if verbose:
                print(' %d' % n, end='')
                sys.stdout.flush()

            ### --- ### --- ###
            self_n = self.vector_presentation(n - self.degree())

            ### --- ### --- ###
            sub_module_n = self_n.image()

            if sub_module_n.dimension() == 0:
                continue

            j_n = j.vector_presentation(n)
            Q_n = sub_module_n.quotient(j_n.image())

            if Q_n.dimension() == 0:
                continue

            # The map j does not cover everything in degree `n` of the sub_module_n.
            # Extend it.
            generator_degrees = tuple((x.degree() for x in F_.generators()))
            new_generator_degrees = tuple(Q_n.dimension()*(n,))
            F_ = self.domain().__class__(generator_degrees + new_generator_degrees, algebra=self.base_ring())

            ### --- ### --- ###
            new_values = tuple([
                self.codomain().element_from_coordinates(Q_n.lift(q), n) for q in Q_n.basis()])

            ### --- ### --- ###
            j = Hom(F_, self.codomain()) (j.values() + new_values)

        if verbose:
            print('.')
        return j


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

        n = self.domain().connectivity()
        if n == PlusInfinity():
            return j

        n -= 1
        limit = (self.base_ring().top_class().degree() + max(self.domain().generator_degrees()))\
            if top_dim is None else top_dim

        if top_dim == PlusInfinity():
            raise ValueError('The user must specify a top dimension for this calculation to terminate.')

        if verbose:
            print('Resolving kernel dimensions up to #%d:' % (limit+1), end='')
        while n <= limit:
            n += 1

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
