r"""
Homomorphisms of finitely presented graded modules over the `\operatorname{mod} p` Steenrod algebra

This class implements construction and basic manipulation of homomorphisms
between finitely presented graded modules over the `\operatorname{mod} p` Steenrod algebra.

The construction of a homomorphism is done by specifying the values of the
module generators of the domain::

    sage: from sage.modules.fp_modules.fpa_module import FPA_Module
    sage: A = SteenrodAlgebra(2)
    sage: F1 = FPA_Module([4,5], A)
    sage: F2 = FPA_Module([3,4], A)
    sage: values = [ F2((Sq(1), 0)), F2((0, Sq(1))) ]
    sage: f = Hom(F1, F2)(values); f
    Module homomorphism of degree 0 defined by sending the generators
      [<1, 0>, <0, 1>]
    to
      [<Sq(1), 0>, <0, Sq(1)>]

Homomorphisms can be evaluated on elements of the domain module::

    sage: x = F1.generator(0)
    sage: y = f(x); y
    <Sq(1), 0>
    sage: y in f.codomain()
    True

Module homomorphisms are linear and respect to the module action::

    sage: Sq(3)*y == f(Sq(3)*x)
    True
    sage: x2 = F1.generator(1)
    sage: f(Sq(1)*x + x2) == Sq(1)*y + f(x2)
    True

Homomorphisms have well defined degrees::

    sage: f.degree()
    0

Homomorphisms of equal degree form a group under pointwise addition::

    sage: values2 = [ F2((Sq(1), 0)), F2((Sq(2), Sq(1))) ]
    sage: f2 = Hom(F1, F2)(values2); f2
    Module homomorphism of degree 0 defined by sending the generators
      [<1, 0>, <0, 1>]
    to
      [<Sq(1), 0>, <Sq(2), Sq(1)>]
    sage: f + f2
    Module homomorphism of degree 0 defined by sending the generators
      [<1, 0>, <0, 1>]
    to
      [<0, 0>, <Sq(2), 0>]
    sage: values3 = [ F2((0, 0)), F2((Sq(2), 0)) ]
    sage: f3 = Hom(F1, F2)(values3); f3
    Module homomorphism of degree 0 defined by sending the generators
      [<1, 0>, <0, 1>]
    to
      [<0, 0>, <Sq(2), 0>]
    sage: f3 == f - f2
    True

Composition of homomorphisms can be performed as expected::

    sage: Q = FPA_Module((2,3), A, relations=[[Sq(6), Sq(5)]]); Q
    Finitely presented module on 2 generators and 1 relation ...
    sage: H2 = Hom(F2, Q)
    sage: g = H2( ( Q((Sq(4), 0)), Q((0, Sq(1,1))) ) )
    sage: g*f
    Module homomorphism of degree 3 defined by sending the generators
      [<1, 0>, <0, 1>]
    to
      [<Sq(5), 0>, <0, 0>]
    sage: f*g
    Traceback (most recent call last):
     ...
    ValueError: Morphisms not composable.

The kernel of a homomorphism `g` is given via its natural injection into the
domain of `g`::

    sage: i = g.kernel()
    sage: i.codomain() is g.domain()
    True
    sage: i.domain()
    Finitely presented module on 7 generators and 17 relations over mod 2 Steenrod algebra, milnor basis

The cokernel of a homomorphism `g` is given via its natural projection `p: \operatorname{codomain}(g) \rightarrow \operatorname{cokernel}(g)`::

    sage: p = g.cokernel()
    sage: p.domain() is g.codomain()
    True
    sage: p.codomain()
    Finitely presented module on 2 generators and 3 relations over mod 2 Steenrod algebra, milnor basis

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

from sage.categories.homset import Hom
from sage.modules.fp_modules.fp_morphism import FP_ModuleMorphism
from sage.modules.fp_modules.profile import enveloping_profile_elements


class FPA_ModuleMorphism(FP_ModuleMorphism):

    def __init__(self, parent, values):
        r"""
        Create a homomorphism between finitely presented graded modules over
        the `\operatorname{mod} p` Steenrod algebra.

        INPUT:

        - ``parent`` -- A homspace object.

        - ``values`` -- A list of elements in the codomain.  Each element
          corresponds to a module generator in the domain.

        OUTPUT: A module homomorphism defined by sending generator with index
        `i` to the element in the codomain which has index `i` in the given
        input list.


        TESTS:

            sage: from sage.modules.fp_modules.fpa_module import FPA_Module
            sage: # Trying to map the generators of a non-free module into a
            sage: # free module:
            sage: A = SteenrodAlgebra(2)
            sage: F = FPA_Module([2,3], A)
            sage: Q = FPA_Module([2,3], A, relations=[[Sq(6), Sq(5)]])
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
        # Call the base class constructor.
        FP_ModuleMorphism.__init__(self, parent, values)


    def profile(self):
        r"""
        A finite profile over which this homomorphism can be defined.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fpa_module import FPA_Module
            sage: A = SteenrodAlgebra(2)
            sage: M = FPA_Module([0,1], A, [[Sq(2),Sq(1)], [0,Sq(2)]])
            sage: id = Hom(M,M).identity()
            sage: id.profile()
            (2, 1)
            sage: zero = Hom(M,M).zero()
            sage: zero.profile()
            (2, 1)
            sage: A_fin = SteenrodAlgebra(2, profile=(2,1))
            sage: M_fin = M.change_ring(A_fin)

        Change the ring of the module M::

            sage: M_fin.change_ring(A) is M
            True

        We can change rings to the finite sub-Hopf algebra defined by
        the profile we just computed::

            sage: id_fin = id.change_ring(A_fin); id_fin
            The identity homomorphism.
            sage: id_fin.domain()
            Finitely presented module on 2 generators and 2 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [2, 1]

        And if we change back to the full Steenrod algebra, we are back were
        we started::

            sage: id_fin.change_ring(A) == id
            True

        """
        def _flatten(f):
            return [coeffifient for value in f.values()\
                for coeffifient in value.coefficients()]

        elements = _flatten(self.domain().j) +\
            _flatten(self.codomain().j) +\
            _flatten(self)


        profile = enveloping_profile_elements(elements)

        # Avoid returning the zero profile because it triggers a corner case
        # in FP_Module.resolution().
        #
        # XXX: Fix FP_Module.resolution().
        #
        return (1,) if profile == (0,) else profile


    def is_injective(self, verbose=False):
        r"""
        Determine if this homomorphism is injective.

        INPUT:

        - ``verbose`` -- A boolean to control if log messages should be emitted.
          (optional, default: ``False``)

        OUTPUT:: The Boolean value True if this homomorphism has a trivial
        kernel, and False otherwise.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fpa_module import FPA_Module
            sage: A = SteenrodAlgebra(2)
            sage: M = FPA_Module([0,1], A, [[Sq(2),Sq(1)], [0,Sq(2)]])
            sage: S = FPA_Module([0], A, [[Sq(2)]])
            sage: f = Hom(S, M)([M([0,1])])
            sage: f.is_injective()
            True
            sage: g = Hom(S, M).zero()
            sage: g.is_injective()
            False
            sage: z = Hom(FPA_Module([], A), M).zero()
            sage: z.is_injective()
            True
            sage: z.is_zero()
            True

        """
        algebra = self.base_ring()

        finite_algebra = algebra.__class__(algebra.prime(), profile=self.profile())

        return FP_ModuleMorphism.is_injective(
            self.change_ring(finite_algebra),
            verbose=verbose)


    def kernel(self, top_dim=None, verbose=False):
        r"""
        The kernel of this homomorphism.

        INPUT:

        - ``verbose`` -- A boolean to control if log messages should be emitted.
          (optional, default: ``False``)

        OUTPUT:: An injective homomorphism into the domain of this homomorphism
        which is onto the kernel of this homomorphism.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fpa_module import FPA_Module
            sage: A = SteenrodAlgebra(2)
            sage: M = FPA_Module([0,1], A, [[Sq(2),Sq(1)], [0,Sq(2)]])
            sage: S = FPA_Module([0], A, [[Sq(2)]])
            sage: f = Hom(S, M)([M([0,1])])
            sage: f.is_injective()
            True
            sage: k = f.kernel(); k
            The trivial homomorphism.

        Since k is both trivial and injective, its domain should
        be the zero module::

            sage: k.domain().is_trivial()
            True

            sage: g = Hom(S, M)([M([Sq(3),Sq(2)])])
            sage: h = g.kernel(); h
            The identity homomorphism.
            sage: ker = h.domain();
            sage: ker is S
            True

        So ``g`` had to be trivial::

            sage: g.is_zero()
            True

        """
        return self._action(FP_ModuleMorphism.kernel, verbose)


    def image(self, verbose=False):
        r"""
        Compute the image of this homomorphism.

        INPUT:

        - ``verbose`` -- A boolean to control if log messages should be emitted.
          (optional, default: ``False``)

        OUTPUT:: An injective homomorphism into the domain of `self` which is
        onto the image of this homomorphism.

        EXAMPLES::

            sage: from sage.modules.fp_modules.fpa_module import FPA_Module
            sage: A = SteenrodAlgebra(2)
            sage: M = FPA_Module([0,1], A, [[Sq(2),Sq(1)], [0,Sq(2)]])
            sage: S = FPA_Module([0], A, [[Sq(2)]])
            sage: f = Hom(S, M)([M([0,1])])
            sage: f.is_injective()
            True
            sage: i = f.image(); i
            Module homomorphism of degree 0 defined by sending the generators
              [<1>]
            to
              [<0, 1>]
            sage: i.codomain() is M
            True

        Lift the map ``f`` over the inclusion ``i``::

            sage: f_ = f.lift(i)
            sage: f_.is_injective()
            True
            sage: f_.is_surjective()
            True

            sage: g = Hom(S, M)([M([Sq(3),Sq(2)])])
            sage: j = g.image(); j
            The trivial homomorphism.

        So ``g`` had to be trivial::

            sage: g.is_zero()
            True

        """
        return self._action(FP_ModuleMorphism.image, verbose)


    def resolve_kernel(self, top_dim=None, verbose=False):
        r"""
        Resolve the kernel of this homomorphism by a free module.

        INPUT:

        - ``verbose`` -- Boolean to enable progress messages. (optional,
          default: ``False``)

        OUTPUT: A homomorphism `j: F \rightarrow D` where `D` is the domain of
        this homomorphism, `F` is free and such that `\ker(self) = \operatorname{im}(j)`.

        """
        return self._action(FP_ModuleMorphism.resolve_kernel, verbose)


    def resolve_image(self, top_dim=None, verbose=False):
        r"""
        Resolve the image of this homomorphism by a free module.

        INPUT:

        - ``verbose`` -- Boolean to enable progress messages. (optional,
          default: ``False``)

        OUTPUT: A homomorphism `j: F \rightarrow C` where `C` is the codomain
        of this homomorphism, `F` is free, and 
        `\operatorname{im}(self) = \operatorname{im}(j)`.

        """
        return self._action(FP_ModuleMorphism.resolve_image, verbose)


    def _action(self, method, profile, verbose=False):
        r"""
        Changes the ground ring to a finite algebra, acts by the given method
        and changes back into the original ground ring before returning.

        """
        small_profile = self.profile()

        if verbose:
            print('Computing the kernel using the profile:')
            print(small_profile)

        algebra = self.base_ring()

        # Choose a finite sub Hopf-algebra of the original algebra.
        finite_algebra = algebra.__class__(algebra.prime(), profile=small_profile)

        # Perform the chosen action on the module after having changed rings
        # to the finite algebra.
        fp_result = method(
            self.change_ring(finite_algebra),
            verbose=verbose)

        # Change back to the original algebra and return the result.
        return fp_result.change_ring(self.base_ring())



