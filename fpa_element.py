r"""
Elements of finitely presented modules over the Steenrod algebra

This class implements construction and basic manipulation of homogeneous
elements of the finitely generated graded modules, modelled by the Sage
parent :class:`sage.modules.fp_modules.fpa_module.FPA_Module`.

Let `\{g_i\}_i` be the finite set of generators for the parent module class,
and let `\{a_i\}_i` be a set of elements of the base algebra of
that module, having degrees `\deg(a_i) + \deg(g_i) = n` for some `n\in \ZZ`.

Then an instance of this class created using the `a_i`'s
represents the module element of degree `n` given by

.. MATH::

    \sum_i a_i\cdot g_i\,.

The ordered set `\{a_i\}` is referred to as the coefficients of the module
element.

AUTHORS:

    - Robert R. Bruner, Michael J. Catanzaro (2012): initial version
    - Koen (date in ISO year-month-day format): Updating to Sage 8.1
    - Sverre A. Lunoee-Nielsen (2020-01-11): Rewritten and refactored, and updated to Sage 8.9.

"""

#*****************************************************************************
#       Copyright (C) 2011 Robert R. Bruner <rrb@math.wayne.edu> and
#                          Michael J. Catanzaro <mike@math.wayne.edu>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from .fp_element import FP_Element


class FPA_Element(FP_Element):

    def __init__(self, module, coefficients):
        r"""
        Create a module element of a finitely presented graded module over
        the Steenrod algebra.

        INPUT:

        - ``module`` -- the parent instance of this module element.

        - ``coefficients`` -- a tuple of homogeneous elements of the algebra
          over which the module is defined, or an integer index.

        OUTPUT: The module element given by the coefficients.  Otherwise, if
        ``coefficients`` is an integer index, then the Kroenecker delta
        function with respect to that index is used as coefficients.

        .. NOTE:: Never use this constructor explicitly, but rather the parent's
              call method, or this class' __call__ method.  The reason for this
              is that the dynamic type of the element class changes as a
              consequence of the category system.

        """
        FP_Element.__init__(self, module, coefficients)


