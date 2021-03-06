r"""
Finitely presented modules over the Steenrod algebra.

.. RUBRIC:: Introduction

This package allows the user to define finitely presented modules
over the Steenrod Algebra, elements of them, and morphisms. With
these objects, the user can perform more complex computations, using
the secondary functions defined.

.. RUBRIC:: Theoretical background

The Steenrod algebra is the union of finite sub-Hopf algebras
[Margolis, Spectra and the Steenrod Algebra, Ch. 15, Sect. 1, Prop 7].
Therefore, any finitely presented module over the Steenrod algebra is
defined over a finite sub-Hopf algebra.  Similarly, any homomorphism
between finitely presented modules over the Steenrod algebra is
defined over a finite sub-Hopf algebra of the Steenrod algebra.
Further, tensoring up from the category of modules over a sub-Hopf
algebra is an exact functor, since the Steenrod algebra is free over
any sub-Hopf algebra.

It follows that kernels, cokernels, images, and, more generally, any finite
limits or colimits can be computed in the category of modules over the
Steenrod algebra, by working in the category of modules over an appropriate
finite sub-Hopf algebra.

It is also the case that presentations of modules and the images of the
generators of the domain of a homomorphism are the same over the sub-Hopf
algebra and over the whole Steenrod algebra, so that the tensoring up is
entirely implicit and requires no computation.

The definitions and computations carried out by this package are thus done
as follows.   First, find a small finite sub-Hopf algebra over which the
computation can be done.   Then, carry out the calculation there, where it
is a finite problem, and can be reduced to linear algebra over a finite
prime field.


.. RUBRIC:: User's guide

Creating a module class instance with given generators and relations::

    sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fpa_module import FPA_Module
    sage: A = SteenrodAlgebra(2)
    sage: M = FPA_Module([0,1], A, [[Sq(2),Sq(1)], [0,Sq(2)]]); M
    Finitely presented module on 2 generators and 2 relations over mod 2 Steenrod algebra, milnor basis

Creating module elements::

    sage: m = M([0, 1]); m
    <0, 1>
    sage: n = M([Sq(2), Sq(1)]); n
    <Sq(2), Sq(1)>

Creating homomorphisms::

    sage: F = FPA_Module([1,3], A);
    sage: L = FPA_Module([2,3], A, [[Sq(2),Sq(1)], [0,Sq(2)]]);
    sage: homset = Hom(F, L); homset
    Set of Morphisms from Finitely presented module on 2 generators ...

The ``an_element()`` member function produces a homomorphism.  (Todo: this always
results in the trivial homomorphism at the moment.)::

    sage: homset.an_element()
    The trivial module homomorphism.

A module homomorphism sending the two generators of the free
module `F` to the elements `v_1` and `v_2`, respectively::

    sage: v_1 = L((Sq(1), 1)); v_2 = L((0, Sq(2)))
    sage: f = homset([v_1, v_2]); f
    Module homomorphism of degree 2 defined by sending the generators
      [<1, 0>, <0, 1>]
    to
      [<Sq(1), 1>, <0, Sq(2)>]

The kernel of `f` can be computed using the member function ``kernel``.  Note
that this function returns an injective homomorphism `i: K \rightarrow M` where
the codomain is ``this`` module, and `f` is onto `\ker (f)`::

    sage: k = f.kernel() # returns an injective homomorphism onto the kernel.
    sage: k.is_injective()
    True
    sage: k.is_surjective()
    False
    sage: k
    Module homomorphism of degree 0 defined by sending the generators
      [<1, 0>, <0, 1>]
    to
      [<0, 1>, <Sq(0,1), 0>]

The ``image`` member function behaves similarly, returning an injective
homomorphism with image equal to the submodule `\im(f)` ::

    sage: i = f.image()
    sage: i.codomain() == f.codomain()
    True

Lifts of maps::

    sage: f_ = f.lift(i) # Lift $f$ over the inclusion of its image.
    sage: f_.domain() == F
    True
    sage: f_.codomain() == i.domain()
    True
    sage: i*f_ == f
    True

The image module::

    sage: i.domain()
    Finitely presented module on 1 generator and 1 relation over mod 2 Steenrod algebra, milnor basis

The trivial homomorphism::

    sage: t_1 = homset(0); t_1
    The trivial module homomorphism.
    sage: t_2 = homset.zero()
    sage: t_1 == t_2
    True
    sage: f = homset( [L((Sq(1), 1)), L((0, Sq(2)))] )
    sage: f - homset.zero() == f
    True

The identity homomorphism::

    sage: id = End(L).identity()
    sage: id + id
    The trivial module homomorphism.
    sage: id*id
    The identity module homomorphism.
    sage: id*id == id
    True
    sage: id*id != id
    False
    sage: id.degree()
    0
    sage: g = id + id + id; g
    The identity module homomorphism.
    sage: g == id
    True
    sage: el = L([Sq(5), Sq(4)]); el.normalize()
    <Sq(5), Sq(4)>
    sage: End(L).identity()(el)
    <Sq(5), Sq(4)>
    sage: g(el)
    <Sq(5), Sq(4)>

The category framework::

    sage: A = SteenrodAlgebra(2)
    sage: K = FPA_Module([1,3], A);K
    Finitely presented module on 2 generators and 0 relations ...
    sage: K.category()
    Category of modules over mod 2 Steenrod algebra, milnor basis
    sage: L = FPA_Module([2,3], A, [[Sq(2),Sq(1)], [0,Sq(2)]]);L
    Finitely presented module on 2 generators and 2 relations ...
    sage: M = FPA_Module([2,3], A, [[Sq(2),Sq(1)]]);M
    Finitely presented module on 2 generators and 1 relation ...
    sage: K.element_class
    <class 'sage.modules.finitely_presented_over_the_steenrod_algebra.fpa_module.FPA_Module_class_with_category.element_class'>
    sage: m = M((0,1)); m
    <0, 1>
    sage: K.is_parent_of(m)
    False
    sage: L.is_parent_of(m)
    False
    sage: M.is_parent_of(m)
    True

Lift elements::

    sage: F = FPA_Module([1,3], A);
    sage: L = FPA_Module((2,3), A, [[Sq(2),Sq(1)], [0,Sq(2)]]);
    sage: H = Hom(F, L)
    sage: f = H( [L([Sq(1), 1]), L([0, Sq(2)])] )
    sage: f.solve(L([0, Sq(2)]))
    <0, 0>
    sage: f.solve(L([Sq(1), 1]))
    <1, 0>

Computing resolutions::

    sage: # From Mike's thesis:
    sage: Hko = FPA_Module([0], A, [[Sq(1)], [Sq(2)]])
    sage: res = Hko.resolution(6, verbose=True)
    Computing f_1 (1/6)
    Computing f_2 (2/6)
    Resolving the kernel in the range of dimensions [1, 8]: 1 2 3 4 5 6 7 8.
    Computing f_3 (3/6)
    Resolving the kernel in the range of dimensions [2, 10]: 2 3 4 5 6 7 8 9 10.
    Computing f_4 (4/6)
    Resolving the kernel in the range of dimensions [3, 13]: 3 4 5 6 7 8 9 10 11 12 13.
    Computing f_5 (5/6)
    Resolving the kernel in the range of dimensions [4, 18]: 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18.
    Computing f_6 (6/6)
    Resolving the kernel in the range of dimensions [5, 20]: 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20.
    sage: [x.domain() for x in res]
    [Finitely presented module on 1 generator and 0 relations over mod 2 Steenrod algebra, milnor basis,
     Finitely presented module on 2 generators and 0 relations over mod 2 Steenrod algebra, milnor basis,
     Finitely presented module on 2 generators and 0 relations over mod 2 Steenrod algebra, milnor basis,
     Finitely presented module on 2 generators and 0 relations over mod 2 Steenrod algebra, milnor basis,
     Finitely presented module on 3 generators and 0 relations over mod 2 Steenrod algebra, milnor basis,
     Finitely presented module on 4 generators and 0 relations over mod 2 Steenrod algebra, milnor basis,
     Finitely presented module on 4 generators and 0 relations over mod 2 Steenrod algebra, milnor basis]
    sage: def is_complex(res):
    ....:     for i in range(len(res)-1):
    ....:         f = (res[i]*res[i+1])
    ....:         if not f.is_zero():
    ....:             return False
    ....:     return True
    ....:
    sage: is_complex(res)
    True
    sage: def is_exact(res):
    ....:     for i in range(len(res)-1):
    ....:         h = res[i].homology(res[i+1])
    ....:         if not h.codomain().is_trivial():
    ....:             return False
    ....:     return True
    sage: is_exact(res)
    True
    sage: [r.codomain().generator_degrees() for r in res]
    [(0,), (0,), (1, 2), (2, 4), (3, 7), (4, 8, 12), (5, 9, 13, 14)]
    sage: [r.values() for r in res]
    [[<1>],
     [<Sq(1)>, <Sq(2)>],
     [<Sq(1), 0>, <Sq(0,1), Sq(2)>],
     [<Sq(1), 0>, <Sq(2,1), Sq(3)>],
     [<Sq(1), 0>, <Sq(2,1), Sq(1)>, <0, Sq(2,1)>],
     [<Sq(1), 0, 0>, <Sq(2,1), Sq(1), 0>, <0, Sq(2,1), Sq(1)>, <0, 0, Sq(2)>],
     [<Sq(1), 0, 0, 0>,
      <Sq(2,1), Sq(1), 0, 0>,
      <0, Sq(2,1), Sq(1), 0>,
      <0, 0, Sq(0,1), Sq(2)>]]

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



from sage.algebras.steenrod.steenrod_algebra import SteenrodAlgebra
from sage.categories.homset import Hom
from sage.modules.free_module import VectorSpace
from sage.rings.infinity import PlusInfinity

from .fp_module import FP_Module_class
from .profile import enveloping_profile_elements


def FPA_Module(generator_degrees, algebra, relations=()):
    r"""
    Create a finitely presented module over a Steenrod algebra.

    INPUT:

    - ``generators`` -- An iterable of non-decreasing integers.
    - ``algebra`` -- The Steenrod algebra over which the module is defined.
    - ``relations`` -- An iterable of relations in the module.  A relation is
        given as an iterable of coefficients corresponding to the module generators.

    """
    return FPA_Module_class(tuple(generator_degrees), algebra, tuple([tuple(r) for r in relations]))


class FPA_Module_class(FP_Module_class):
    # In the category framework, Elements of the class FP_Module are of the
    # class FP_Element, see
    # http://doc.sagemath.org/html/en/thematic_tutorials/coercion_and_categories.html#implementing-the-category-framework-for-the-elements
    from .fpa_element import FPA_Element
    Element = FPA_Element

    def __init__(self, generator_degrees, algebra, relations=()):
        r"""

        Create a finitely presented module over the Steenrod algebra.

        INPUT:

        - ``generators`` -- A tuple of non-decreasing integers.
        - ``algebra`` -- The Steenrod algebra over which the module is defined.
        - ``relations`` -- A tuple of relations.  A relation is a tuple of
            coefficients $(c_1, \ldots, c_n)$ corresponding to the module
            generators.

        OUTPUT: The finitely presented module with presentation given by
            ``generators`` and ``relations``.

        """
        # Call the base class constructor.
        FP_Module_class.__init__(self, generator_degrees, algebra, relations)

        # Store the Homspace class and the module class as member variables so
        # that member functions can use them to create instances.  This enables
        # base class member functions to create modules and homspace instances
        # of this derived class type.
        from .fpa_homspace import FPA_ModuleHomspace
        self.HomSpaceClass = FPA_ModuleHomspace
        self.ModuleClass = FPA_Module_class

    @classmethod
    def from_fp_module(cls, fp_module):
        r"Construct from a finitely presented A-module."

        return cls(
            fp_module.generator_degrees(),
            algebra=fp_module.base_ring(),
            relations=tuple([r.coefficients() for r in fp_module.relations()]))


    def profile(self):
        r"""
        A finite profile over which this module can be defined.

        EXAMPLES::
            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fpa_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FPA_Module([0,1], A, [[Sq(2),Sq(1)],[0,Sq(2)],[Sq(3),0]])
            sage: M.profile()
            (2, 1)

        TESTS::
            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fpa_module import *
            sage: A = SteenrodAlgebra(2)
            sage: X = FPA_Module([0], A)
            sage: X.profile()
            (1,)

        """

        elements = [coeffifient for value in self.j.values()\
                for coeffifient in value.coefficients()]

        profile = enveloping_profile_elements(elements)

        # Avoid returning the zero profile because it triggers a corner case
        # in FP_Module_class.resolution().
        #
        # XXX: Fix FP_Module_class.resolution().
        #
        return (1,) if profile == (0,) else profile


    def min_pres(self, verbose=False):
        r"""
        A minimal presentation of this module.

        OUTPUT:

        -  ``f`` - An isomorphism $M \to self$, where $M$ has minimal
            presentation.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fpa_module import *
            sage: A = SteenrodAlgebra(2)
            sage: M = FPA_Module([0,1], A, [[Sq(2),Sq(1)],[0,Sq(2)],[Sq(3),0]])
            sage: i = M.min_pres()
            sage: i.is_injective()
            True
            sage: i.is_surjective()
            True
            sage: i.domain().relations()
            [<Sq(2), Sq(1)>, <0, Sq(2)>]
            sage: i.codomain() is M
            True
            sage: i.codomain().relations()
            [<Sq(2), Sq(1)>, <0, Sq(2)>, <Sq(3), 0>]

        """
        return Hom(self, self).identity().image(verbose=verbose)


    def resolution(self, k, top_dim=None, verbose=False):
        r"""
        A resolution of this module of length ``k``.

        INPUT:

        - ``k`` -- An non-negative integer.

        - ``verbose`` -- A boolean to control if log messages should be emitted.
          (optional, default: ``False``)

        OUTPUT:

        - ``res`` -- A list of homomorphisms `[\epsilon, f_1, \ldots, f_k]`
          which are part of a free resolution this module M.  I.e.

            `f_i: F_i \to F_{i-1}`

            `\epsilon: F_0\to M`,

          where each `F_i` is a finitely generated free module, and the
          sequence

            F_k --> F_k-1 --> .. --> F_1 --> F_0 --> M --> 0

          is exact.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fpa_module import *
            sage: A = SteenrodAlgebra(2)
            sage: Hko = FPA_Module([0], A, [[Sq(1)], [Sq(2)]])
            sage: res = Hko.resolution(5, verbose=True)
            Computing f_1 (1/5)
            Computing f_2 (2/5)
            Resolving the kernel in the range of dimensions [1, 8]: 1 2 3 4 5 6 7 8.
            Computing f_3 (3/5)
            Resolving the kernel in the range of dimensions [2, 10]: 2 3 4 5 6 7 8 9 10.
            Computing f_4 (4/5)
            Resolving the kernel in the range of dimensions [3, 13]: 3 4 5 6 7 8 9 10 11 12 13.
            Computing f_5 (5/5)
            Resolving the kernel in the range of dimensions [4, 18]: 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18.
            sage: [x.domain() for x in res]
            [Finitely presented module on 1 generator and 0 relations over mod 2 Steenrod algebra, milnor basis,
             Finitely presented module on 2 generators and 0 relations over mod 2 Steenrod algebra, milnor basis,
             Finitely presented module on 2 generators and 0 relations over mod 2 Steenrod algebra, milnor basis,
             Finitely presented module on 2 generators and 0 relations over mod 2 Steenrod algebra, milnor basis,
             Finitely presented module on 3 generators and 0 relations over mod 2 Steenrod algebra, milnor basis,
             Finitely presented module on 4 generators and 0 relations over mod 2 Steenrod algebra, milnor basis]
            sage: M = FPA_Module([0], A)
            sage: M.resolution(4)
            [The identity module homomorphism.,
             The trivial module homomorphism.,
             The trivial module homomorphism.,
             The trivial module homomorphism.,
             The trivial module homomorphism.]

        """

        algebra = self.base_ring()
        finite_algebra = algebra.__class__(algebra.prime(), profile=self.profile())

        # Change rings to the finite algebra, and call the base class
        # implementation of this function.
        res = FP_Module_class.resolution(
            self.change_ring(finite_algebra),
            k,
            top_dim=top_dim, 
            verbose=verbose)

        # Change rings back to the original Steenrod algebra.
        return [j.change_ring(self.base_ring()) for j in res]


    def export_module_definition(self, powers_of_two_only=True):
        r"""
        Export the module to Bruner's Ext program format:
        http://www.math.wayne.edu/~rrb/cohom/modfmt.html

        INPUT:

        - ``powers_of_two_only`` -- A boolean to control if the output should
          contain the action of all Steenrod squaring operations (restricted
          by the profile), or only the action of the operations of degree equal
          to a power of two. (optional, default: ``True``)

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fpa_module import *
            sage: A1 = algebra=SteenrodAlgebra(p=2, profile=[2,1])
            sage: M = FPA_Module([0], A1)
            sage: M.export_module_definition()
            8 0 1 2 3 3 4 5 6
            0 1 1 1
            2 1 1 4
            3 1 1 5
            6 1 1 7
            0 2 1 2
            1 2 2 3 4
            2 2 1 5
            3 2 1 6
            4 2 1 6
            5 2 1 7
            sage: N = FPA_Module([0], A1, [[Sq(1)]])
            sage: N.export_module_definition()
            4 0 2 3 5
            1 1 1 2
            0 2 1 1
            2 2 1 3
            sage: N.export_module_definition(powers_of_two_only=False)
            4 0 2 3 5
            1 1 1 2
            0 2 1 1
            2 2 1 3
            0 3 1 2
            sage: A2 = SteenrodAlgebra(p=2, profile=[3,2,1])
            sage: Hko = FPA_Module([0], A2, [[Sq(1)], [Sq(2)]])
            sage: Hko.export_module_definition()
            8 0 4 6 7 10 11 13 17
            2 1 1 3
            4 1 1 5
            1 2 1 2
            5 2 1 6
            0 4 1 1
            2 4 1 4
            3 4 1 5
            6 4 1 7

        """

        if not self.base_ring().is_finite():
            raise RuntimeError, "This module is not defined over a finite algebra."
            return

        if self.base_ring().characteristic() != 2:
            raise RuntimeError, "This function is not implemented for odd primes."
            return

        n = self.connectivity()
        if n == PlusInfinity():
            print('The module connectivity is infinite, so there is ' +
                  'nothing to export.')
            return

        limit = self.base_ring().top_class().degree() + max(self.generator_degrees())

        # Create a list of bases, one for every module degree we consider.
        vector_space_basis = [self.basis_elements(i) for i in range(n, limit+1)]
        # print (vector_space_basis)

        additive_generator_degrees = []
        additive_generator_global_indices = [0]
        for dim, basis_vectors in enumerate(vector_space_basis):
            additive_generator_global_indices.append(
                len(basis_vectors) + additive_generator_global_indices[-1])
            additive_generator_degrees += len(basis_vectors)*[dim + n]

        # Print the degrees of the additive generators.
        print "%d %s" % (
            len(additive_generator_degrees),
            " ".join(["%d" % x for x in additive_generator_degrees]))

        num_basis_vectors = additive_generator_global_indices[-1]

        # A private function which transforms a vector in a given dimension
        # to a vector of global indices for the basis elements corresponding
        # to the non-zero entries in the vector.  E.g.
        # _GetIndices(dim=2, vec=(1,0,1)) will return a vector of length two,
        # (a, b), where a is the index of the first vector in the basis for
        # the 2-dimensional part of the module, and b is the index of the
        # last vector in the same part.
        def _GetIndices(dim, vec):
            if len(vector_space_basis[dim]) != len(vec):
                raise ValueError, "The given vector\n%s\nhas the wrong size, it should be %d" % (str(vec), len(vector_space_basis[dim]))
            base_index = additive_generator_global_indices[dim]
            return [base_index + a for a,c in enumerate(vec) if c != 0]

        profile = self.base_ring()._profile
        powers = [2**i for i in range(profile[0])] if powers_of_two_only else\
            range(1, 2**profile[0])

        # print(powers)

        for k in powers:
            images = [[(self.base_ring().Sq(k)*x).vector_presentation() for x in D]\
                      for D in vector_space_basis]
            # print(images)

            element_index = 0

            # Note that the dim variable is relative to the bottom dimension, n.
            for dim, image in enumerate(images):
                for im in image:
                    if im != 0 and im != None:
                        values = _GetIndices(dim + k, im)

                        print "%d %d %d %s" % (
                            element_index,
                            k,
                            len(values),
                            " ".join(["%d" % x for x in values]))
                    element_index += 1

