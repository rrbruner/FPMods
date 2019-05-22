r"""
<Very short 1-line summary>

<Paragraph description>

EXAMPLES::

<Lots and lots of examples>

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

from .fp_morphism import FP_ModuleMorphism
from sage.categories.homset import Hom

from .profile import enveloping_profile_elements


class FPA_ModuleMorphism(FP_ModuleMorphism):

    def __init__(self, parent, values):
        r"""
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
            The identity module homomorphism.
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
        # in FP_Module_class.resolution().
        # 
        # XXX: Fix FP_Module_class.resolution().
        #
        return (1,) if profile == (0,) else profile


    def is_injective(self, verbose=False):
        r"""
        Return True if and only if this homomorphism has a trivial kernel.
    
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


    def kernel(self, verbose=False):
        r"""
        Compute the kernel of this homomorphism.

        INPUT:: 
        - ``verbose`` -- A boolean to control if log messages should be emitted.
          (optional, default: ``False``)

        OUTPUT:: An injective homomorphism into the domain of `self` which is
        onto the kernel of this homomorphism.

        EXAMPLES::
            sage: from sage.modules.fp_modules.fpa_module import FPA_Module
            sage: A = SteenrodAlgebra(2)
            sage: M = FPA_Module([0,1], A, [[Sq(2),Sq(1)], [0,Sq(2)]])
            sage: S = FPA_Module([0], A, [[Sq(2)]])
            sage: f = Hom(S, M)([M([0,1])])
            sage: f.is_injective()
            True
            sage: k = f.kernel(); k
            The trivial module homomorphism.

        Since k is both trivial and injective, its domain should
        be the zero module::

            sage: k.domain().is_trivial()
            True

            sage: g = Hom(S, M)([M([Sq(3),Sq(2)])])
            sage: h = g.kernel(); h
            The identity module homomorphism.
            sage: ker = h.domain();
            sage: ker is S
            True

        So ``g`` had to be trivial::

            sage: g.is_zero()
            True

        """

        small_profile = self.profile()

        if verbose:
            print('Computing the kernel using the profile:')
            print(small_profile)

        return self._action(FP_ModuleMorphism.kernel, small_profile, verbose)


    def image(self, verbose=False):
        r"""
        Compute the image of this homomorphism.

        INPUT:: 
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
            The trivial module homomorphism.

        So ``g`` had to be trivial::

            sage: g.is_zero()
            True

        """

        small_profile = self.profile()

        if verbose:
            print('Computing the image using the profile:')
            print(small_profile)

        return self._action(FP_ModuleMorphism.image, small_profile, verbose)


    def _action(self, method, profile, verbose=False):
        r"""
        Changes the ground ring to a finite algebra, acts by the given method
        and changes back into the original ground ring before returning.
        """
        algebra = self.base_ring()
        finite_algebra = algebra.__class__(algebra.prime(), profile=profile)

        fp_result = method(
            self.change_ring(finite_algebra),
            verbose=verbose)

        return fp_result.change_ring(self.base_ring())

