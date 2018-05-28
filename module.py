r"""
Finitely presented modules over the Steenrod algebra.

.. rubric:: Introduction

This package allows the user to define finitely presented modules
over the Steenrod Algebra, elements of them, and morphisms. With
these objects, the user can perform more complex computations, using
the secondary functions defined.

.. rubric:: Theoretical background

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


.. rubric:: User's guide

Creating an instance of the module class using the create method::

    sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.module import create_fp_module
    sage: M = create_fp_module([0,1], [[Sq(2),Sq(1)], [0,Sq(2)]]); M
    Finitely presented module on 2 generators and 2 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [2, 1]

Creating module elements::

    sage: m = M([0, 1]); m
    <0, 1>
    sage: n = M([Sq(2), Sq(1)]); n
    <Sq(2), Sq(1)>

Creating homomorphisms::

    sage: F = create_fp_module([1,3]);
    sage: L = create_fp_module([2,3], [(Sq(2),Sq(1)), (0,Sq(2))]);
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
the codomain is this module, and `f` is onto `\ker (f)`::

    sage: f.kernel() # returns an injective homomorphism onto the kernel.
    Module homomorphism of degree 0 defined by sending the generators
      [<1, 0>, <0, 1>]
    to
      [<0, 1>, <Sq(0,1), 0>]

The ``image`` member function behaves similarly but returns a pair of homomorphisms
which factors `f` into an surjection and an injection::

    sage: i, p = f.image()
    sage: p.domain() == f.domain()
    True
    sage: p.codomain() == i.domain()
    True
    sage: i.codomain() == f.codomain()
    True

all of this is implied by the single statement::

    sage: i*p == f
    True

The image module::

    sage: i.domain()
    Finitely presented module on 1 generator and 1 relation over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [2, 1]

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
    sage: id.degree
    0
    sage: g = id + id + id; g
    The identity module homomorphism.
    sage: g == id
    True
    sage: el = L((Sq(5), Sq(4))); el.normalize()
    <Sq(5), Sq(4)>
    sage: End(L).identity()(el)
    <Sq(5), Sq(4)>
    sage: g(el)
    <Sq(5), Sq(4)>

The category framework::

    sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.module import FP_Module
    sage: degs = [1,3]
    sage: K = FP_Module(degs = tuple(degs));K
    Finitely presented module on 2 generators and 0 relations ...
    sage: K.category()
    Category of modules over mod 2 Steenrod algebra, milnor basis
    sage: L = FP_Module((2,3),((Sq(2),Sq(1)),(0,Sq(2))));L
    Finitely presented module on 2 generators and 2 relations ...
    sage: M = FP_Module((2,3),((Sq(2),Sq(1)),));M
    Finitely presented module on 2 generators and 1 relation ...
    sage: K.element_class
    <class 'sage.modules.finitely_presented_over_the_steenrod_algebra.module.FP_Module_with_category.element_class'>
    sage: m = M((0,1)); m
    <0, 1>
    sage: K.is_parent_of(m)
    False
    sage: L.is_parent_of(m)
    False
    sage: M.is_parent_of(m)
    True

Lifts::

    sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.module import FP_Module
    sage: F = FP_Module(degs = tuple([1,3]));
    sage: L = FP_Module((2,3), ((Sq(2),Sq(1)), (0,Sq(2))));
    sage: H = Hom(F, L)
    sage: f = H( [L((Sq(1), 1)), L((0, Sq(2)))] )
    sage: f.solve(L((0, Sq(2))))
    <0, 0>
    sage: f.solve(L((Sq(1), 1)))
    <1, 0>

Computing resolutions::

    sage: # From Mike's thesis:
    sage: Hko = create_fp_module([0], [[Sq(1)], [Sq(2)]])
    sage: R = Hko.resolution(5, verbose=True)
    Step  5
    Computing kernel degree 2/6
    Computing kernel degree 3/6
    Computing kernel degree 4/6
    Computing kernel degree 5/6
    Computing kernel degree 6/6
    Step  4
    Computing kernel degree 3/8
    Computing kernel degree 4/8
    Computing kernel degree 5/8
    Computing kernel degree 6/8
    Computing kernel degree 7/8
    Computing kernel degree 8/8
    Step  3
    Computing kernel degree 4/10
    Computing kernel degree 5/10
    Computing kernel degree 6/10
    Computing kernel degree 7/10
    Computing kernel degree 8/10
    Computing kernel degree 9/10
    Computing kernel degree 10/10
    Step  2
    Computing kernel degree 5/13
    Computing kernel degree 6/13
    Computing kernel degree 7/13
    Computing kernel degree 8/13
    Computing kernel degree 9/13
    Computing kernel degree 10/13
    Computing kernel degree 11/13
    Computing kernel degree 12/13
    Computing kernel degree 13/13
    Step  1
    Computing kernel degree 6/18
    Computing kernel degree 7/18
    Computing kernel degree 8/18
    Computing kernel degree 9/18
    Computing kernel degree 10/18
    Computing kernel degree 11/18
    Computing kernel degree 12/18
    Computing kernel degree 13/18
    Computing kernel degree 14/18
    Computing kernel degree 15/18
    Computing kernel degree 16/18
    Computing kernel degree 17/18
    Computing kernel degree 18/18
    Step  0
    sage: import sage.modules.finitely_presented_over_the_steenrod_algebra.resolutions as Resolutions
    sage: Resolutions.is_complex(R)
    True
    sage: Resolutions.is_exact(R)
    True
    sage: for i, C in enumerate(R):
    ....:     print ('Stage %d\nDegrees: %s\nValues of R[i]: %s' % (i, C.domain().degs, C.get_values()))
    Stage 0
    Degrees: (0,)
    Values of R[i]: [<1>]
    Stage 1
    Degrees: (1, 2)
    Values of R[i]: [<Sq(1)>, <Sq(2)>]
    Stage 2
    Degrees: (2, 4)
    Values of R[i]: [<Sq(1), 0>, <Sq(0,1), Sq(2)>]
    Stage 3
    Degrees: (3, 7)
    Values of R[i]: [<Sq(1), 0>, <Sq(2,1), Sq(3)>]
    Stage 4
    Degrees: (4, 8, 12)
    Values of R[i]: [<Sq(1), 0>, <Sq(2,1), Sq(1)>, <0, Sq(2,1)>]
    Stage 5
    Degrees: (5, 9, 13, 14)
    Values of R[i]: [<Sq(1), 0, 0>, <Sq(2,1), Sq(1), 0>, <0, Sq(2,1), Sq(1)>, <0, 0, Sq(2)>]

AUTHORS:

    - Robert R. Bruner, Michael J. Catanzaro (2012): initial version
    - Koen (date in ISO year-month-day format): Updating to Sage 8.1
    - Sverre (date in ISO year-month-day format): Updating to Sage 8.1

"""

#*****************************************************************************
#       Copyright (C) 2011 Robert R. Bruner <rrb@math.wayne.edu>
#             and          Michael J. Catanzaro <mike@math.wayne.edu>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#*****************************************************************************

#  http://doc.sagemath.org/html/en/developer/coding_basics.html#files-and-directory-structure

import sage.modules.finitely_presented_over_the_steenrod_algebra.utility as Utility

import sage.modules.finitely_presented_over_the_steenrod_algebra.profile as Profile

import sage.modules.finitely_presented_over_the_steenrod_algebra.resolutions as Resolutions

from sage.algebras.steenrod.steenrod_algebra import SteenrodAlgebra

from sage.modules.free_module import VectorSpace

from sage.rings.finite_rings.finite_field_constructor import FiniteField

from sage.rings.infinity import PlusInfinity

# The free functions for creating Homsets
from sage.categories.homset import Hom

from sage.categories.homset import End

# http://doc.sagemath.org/html/en/thematic_tutorials/coercion_and_categories.html#the-parent
# "You are encouraged to make your parent "unique". That's to say, parents
#  should only evaluate equal if they are identical. Sage provides frameworks to
#  create unique parents. We use here the most easy one: Inheriting from the
#  class sage.structure.unique_representation.UniqueRepresentation is enough.
#  Making parents unique can be quite important for an efficient implementation,
#  because the repeated creation of "the same" parent would take a lot of time."
#
# Deriving from the class UniqueRepresentation forces the condition that the
# constructor arguments must be hashable.  This excludes the use of arrays [],
# instead we use tuples () which are immutable and hashable.  The downside
# is that notation is a bit ugly in some cases: E.g. the singleton tuple
# notation in python is (5,) to be able to distinguish it from (5) which isn't
# a tuple.
from sage.structure.unique_representation import UniqueRepresentation

from sage.modules.module import Module

from sage.modules.finitely_presented_over_the_steenrod_algebra.element import FP_Element

import sage.modules.finitely_presented_over_the_steenrod_algebra.utility as Utility

import sage.modules.finitely_presented_over_the_steenrod_algebra.profile as Profile


def create_fp_module(degs, relations=None, char=None, algebra=None):
    r"""

    Construct an instance of the class FP_Module.

    INPUT:

    - ``degs`` -- A list or tuple of non-decreasing integers defining the
      number of generators of the module, and their degrees.
    - ``relations`` -- A list or tuple of list or tuples of length ``len(degs)``
      (optional, default ``None``)
    - ``char`` -- The characteristic of the algebra for this module.
      (optional, default ``None``)
    - ``algebra`` -- The sub-Hopf algebra of the Steenrod algebra for this
      module. (optional, default ``None``)

    OUTPUT: The finitely presented module with presentation given by
    ``degs`` and ``relations``.

    EXAMPLES::

        sage: # From Mike's thesis:
        sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.module import create_fp_module
        sage: M = create_fp_module([0,1],[[Sq(2),Sq(1)],[0,Sq(2)],[Sq(3),0]]); M
        Finitely presented module on 2 generators and 3 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [2, 1]
        sage: x = M([1,0])
        sage: x == M.gen(0)
        True
        sage: y=M.gen(1)
        sage: z=Sq(2)*Sq(1)*Sq(2)*x; z
        <Sq(2,1), 0>
        sage: z.normalize()
        <0, 0>
        sage: Sq(1)*Sq(2)*y
        <0, Sq(3)>
        sage: (Sq(1)*Sq(2)*y).normalize()
        <0, 0>
        sage: T = create_fp_module([0,2,4],[[Sq(4),0,1],[Sq(1,1),Sq(2),1]])
        sage: z = Sq(2)*T.gen(0) + T.gen(1); z
        <Sq(2), 1, 0>
        sage: g,h = T.min_pres()
        sage: TT = g.domain()
        sage: TT.degs
        (0, 2)
        sage: TT.rels
        ((Sq(1,1) + Sq(4), Sq(2)),)
        sage: g,h = M.min_pres()
        sage: MM = g.domain()
        sage: MM.rels
        ((Sq(2), Sq(1)), (0, Sq(2)))
        sage: incl,proj = MM.submodule([MM.gen(1)])
        sage: S = incl.domain()
        sage: S.degs
        (1,)
        sage: S.rels
        ((Sq(2),),)
        sage: for i in range(7):
        ....:    print ('basis for MM in dimension %d: %s' % (i, MM.basis(i)))
        basis for MM in dimension 0: [<1, 0>]
        basis for MM in dimension 1: [<Sq(1), 0>, <0, 1>]
        basis for MM in dimension 2: [<Sq(2), 0>]
        basis for MM in dimension 3: [<Sq(0,1), 0>]
        basis for MM in dimension 4: [<Sq(1,1), 0>]
        basis for MM in dimension 5: []
        basis for MM in dimension 6: []
        sage: J = create_fp_module([])
        sage: J.conn()
        +Infinity
        sage: J.profile_algebra()
        sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function []
        sage: N = create_fp_module([1], [[Sq(1)]])
        sage: Z = N.suspension(4); Z.degs
        (5,)
        sage: h = Hom(N, M)([Sq(1)*x])
        sage: g = Hom(M, N)([0, N.gen(0)])
        Traceback (most recent call last):
         ...
        ValueError: Relation #1 is not sent to zero.
        sage: i = h.kernel(); K = i.domain()
        sage: K.degs
        (6,)
        sage: i.get_values()
        [<Sq(2,1)>]
        sage: p = h.cokernel(); C = p.codomain()
        sage: C.degs
        (0, 1)
        sage: C.rels
        ((Sq(2), Sq(1)), (0, Sq(2)), (Sq(3), 0), (Sq(1), 0))
        sage: h.cokernel('minimal').codomain().rels
        ((Sq(1), 0), (Sq(2), Sq(1)), (0, Sq(2)))
        sage: image_inj, image_epi = h.image()
        sage: image_inj.domain().degs
        (1,)
        sage: image_inj.domain().rels
        ((Sq(1),), (Sq(2,1),))
        sage: A2 = SteenrodAlgebra(p=2,profile=(3,2,1))
        sage: P7 = create_fp_module([0,0], [[Sq(1),Sq(1)],[Sq(0,1),0],[Sq(0,2),0],[0,Sq(2)]], algebra=A2)
        sage: ko_a2 = create_fp_module([0], [[Sq(1)],[Sq(2)]], algebra=A2)
        sage: p = Hom(P7, ko_a2)( [[0],[1]] )
        sage: j = p.kernel()
        sage: j.domain().degs
        (0,)
        sage: j.domain().rels
        ((Sq(0,1),), (Sq(0,2),))

    TESTS:

    Testing unique parents::

        sage: A2 = SteenrodAlgebra(p=2,profile=(3,2,1))
        sage: P7 = create_fp_module([0,0], [[Sq(1),Sq(1)],[Sq(0,1),0],[Sq(0,2),0],[0,Sq(2)]], algebra=A2)
        sage: P7_ = create_fp_module([0,0], [[Sq(1),Sq(1)],[Sq(0,1),0],[Sq(0,2),0],[0,Sq(2)]], algebra=SteenrodAlgebra(p=2,profile=(3,2,1)))
        sage: P7 is P7_
        True

    """
    rels = None if relations is None else tuple(tuple(rel) for rel in relations)
    return FP_Module(tuple(degs), rels, char, algebra)


class FP_Module(UniqueRepresentation, Module):
    r"""
    A finitely presented module over a sub-Hopf algebra of the
    Steenrod Algebra (including the full Steenrod Algebra).

    TESTS::

        sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.module import FP_Module
        sage: F = FP_Module(degs = tuple([1,3]));
        sage: L = FP_Module((2,3),((Sq(2),Sq(1)),(0,Sq(2))));
        sage: K = FP_Module(degs=(1,3));K
        Finitely presented module on 2 generators and 0 relations ...
        sage: K.category()
        Category of modules over mod 2 Steenrod algebra, milnor basis
        sage: L = FP_Module((2,3),((Sq(2),Sq(1)),(0,Sq(2))));L
        Finitely presented module on 2 generators and 2 relations ...
        sage: M = FP_Module((2,3),((Sq(2),Sq(1)),));M
        Finitely presented module on 2 generators and 1 relation ...
        sage: K.element_class
        <class 'sage.modules.finitely_presented_over_the_steenrod_algebra.module.FP_Module_with_category.element_class'>
        sage: m = M((0,1)); m
        <0, 1>
        sage: K.is_parent_of(m)
        False
        sage: L.is_parent_of(m)
        False
        sage: M.is_parent_of(m)
        True
        sage: from sage.misc.sage_unittest import TestSuite
        sage: TestSuite(K).run(verbose=True)
        running ._test_additive_associativity() . . . pass
        running ._test_an_element() . . . pass
        running ._test_cardinality() . . . pass
        running ._test_category() . . . pass
        running ._test_elements() . . .
          Running the test suite of self.an_element()
          running ._test_category() . . . pass
          running ._test_eq() . . . pass
          running ._test_new() . . . pass
          running ._test_nonzero_equal() . . . pass
          running ._test_not_implemented_methods() . . . pass
          running ._test_pickling() . . . pass
          pass
        running ._test_elements_eq_reflexive() . . . pass
        running ._test_elements_eq_symmetric() . . . pass
        running ._test_elements_eq_transitive() . . . pass
        running ._test_elements_neq() . . . pass
        running ._test_eq() . . . pass
        running ._test_new() . . . pass
        running ._test_not_implemented_methods() . . . pass
        running ._test_pickling() . . . pass
        running ._test_some_elements() . . . pass
        running ._test_zero() . . . pass

    """

    # In the category framework, Elements of the class FP_Module are of the
    # class FP_Element, see
    # http://doc.sagemath.org/html/en/thematic_tutorials/coercion_and_categories.html#implementing-the-category-framework-for-the-elements
    Element = FP_Element

    def __init__(self, degs, relations=None, char=None, algebra=None):
        r"""
        INPUT:

        - ``degs`` -- A tuple of non-decreasing integers defining the number of
          generators of the module, and their degrees.
        - ``relations`` -- A tuple of tuples of length ``len(degs)``
          (optional, default ``None``)
        - ``char`` -- The characteristic of the algebra for this module.
          (optional, default ``None``)
        - ``algebra`` -- The sub-Hopf algebra of the Steenrod algebra for this
          module. (optional, default ``None``)

        OUTPUT: The finitely presented module with presentation given by
        ``degs`` and ``relations``.

        TESTS::
            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.module import FP_Module
            sage: M = FP_Module((0,1), ((Sq(2),Sq(1)),(0,Sq(2)),(Sq(3),0))); M
            Finitely presented module on 2 generators and 3 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [2, 1]
            sage: x = M([1,0])
            sage: x == M.gen(0)
            True
            sage: y=M.gen(1)
            sage: z=Sq(2)*Sq(1)*Sq(2)*x; z
            <Sq(2,1), 0>
            sage: z.normalize()
            <0, 0>
            sage: Sq(1)*Sq(2)*y
            <0, Sq(3)>
            sage: (Sq(1)*Sq(2)*y).normalize()
            <0, 0>
            sage: # Inhomogeneous relation.
            sage: FP_Module((0,1), ((Sq(2),Sq(2)),))
            Traceback (most recent call last):
            ...
            ValueError: Inhomogeneous arguments given.  The first mismatch occured here:
            Index #0: The operation Sq(2) applied to an element in degree 0 will have degree 2,
            Index #1: The operation Sq(2) applied to an element in degree 1 will have degree 3.
            sage: # Generators not in order.
            sage: FP_Module((0,2,1), ((Sq(4),Sq(2), 0),))
            Traceback (most recent call last):
            ...
            ValueError: Degrees of generators must be given in non-decreasing order.
            sage: # Incompatible algebra and chosen characteristics.
            sage: FP_Module((0,2,1), ((Sq(4),Sq(2), 0),), char=3, algebra=SteenrodAlgebra(p=2,profile=(3,2,1)))
            Traceback (most recent call last):
            ...
            TypeError: Characteristic and algebra are incompatible.
        """

        if (char is None) and (algebra is None):
            _char = 2
            _algebra = SteenrodAlgebra(_char, profile=(0,))
        elif (char is None) and (algebra is not None):
            _algebra = algebra
            _char = _algebra.prime()
        elif (char is not None) and (algebra is None):
            _char = char
            if char == 2:
                _algebra = SteenrodAlgebra(p=_char, profile=(0,))
            else:
                _algebra = SteenrodAlgebra(p=_char, profile = ((),(0,)))
        else:
            _char = char
            _algebra = algebra

        if (_char != _algebra.prime()):
            raise TypeError, "Characteristic and algebra are incompatible."

        for i in range(len(degs) - 1):
            if degs[i] > degs[i+1]:
                raise ValueError, "Degrees of generators must be given in non-decreasing order."

        if relations is None:
            prof = _algebra._profile
        else:
            prof = Profile.enveloping_profile_profiles(\
                      [Profile.enveloping_profile_elements(r, _char) for r in relations]\
                      +[list(_algebra._profile)], _char)

        # Initialize member variables.
        self._profile_algebra = SteenrodAlgebra(p=_char, profile=prof)

        self.char = _char

        self.degs = degs

        rels = []
        reldegs = []
        # Append all the non-zero relations.
        if relations != None:
            for r in relations:
                if not all(v == 0 for v in r):
                    relation = tuple([(self._profile_algebra)(c) for c in r])
                    rels.append(relation)
                    # May throw.
                    reldegs.append(Utility._deg_(self.degs, relation))

        self.rels = tuple(rels)
        self.reldegs = tuple(reldegs)

        self._populate_coercion_lists_()

        # Call the base class constructor.
        Module.__init__(self, SteenrodAlgebra(self.char))

    def profile(self):
        """
        The profile of the smallest sub-Hopf algebra of the Steenrod algebra
        over which the module can be defined.  I.e. the smallest one that
        contains all the generators and relations.

        OUTPUT: A profile as a tuple of integers.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.module import FP_Module
            sage: Z = FP_Module((0,),((Sq(1),),(Sq(2),),(Sq(4),))); Z.profile()
            (3, 2, 1)

        """
        return self._profile_algebra._profile

    def profile_algebra(self):
        """
        Return the smallest sub-Hopf algebra of the Steenrod algebra over which
        the module can be defined.  I.e. the smallest one that contains all the
        generators and relations.

        OUTPUT: A sub-Hopf algebra of the Steenrod algebra.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.module import FP_Module
            sage: FP_Module((0,2,3)).profile_algebra()
            sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function []
            sage: FP_Module((0,2,3), ((0,Sq(1),1),)).profile_algebra()
            sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [1]

        """
        return self._profile_algebra

    def conn(self):
        """
        The connectivity of the module.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.module import FP_Module
            sage: X = FP_Module((0,2,3));X.conn()
            0
            sage: M = FP_Module((2,3),((Sq(2),Sq(1)), (0,Sq(2))));M.conn()
            2
            sage: Q = FP_Module(());Q.conn()
            +Infinity
        """
        return min(self.degs + (PlusInfinity(),))

    def rdegs(self):
        """
        Return the degrees of the relations of the module.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.module import FP_Module
            sage: N = FP_Module((0,2,3),((0,Sq(1),1),));N.rdegs()
            [3]
            sage: M = FP_Module((2,3),((Sq(2),Sq(1)),(0,Sq(2))));M.rdegs()
            [4, 5]
        """
        return [Utility._deg_(self.degs,r) for r in self.rels]

    def _element_constructor_(self, x):
        """
        Construct any element of the module.

        INPUT:
        - ``x`` -- A tuple of coefficients, an element of FP_Module, or the
          zero integer constant.

        OUTPUT: An instance of the element class with coefficients from ``x``,
        the element ``x`` if it already was an element, or the zero element.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.module import FP_Module
            sage: M = FP_Module(degs=(0,2,4), relations=((Sq(4),Sq(2),0),))
            sage: e = M(0); e
            <0, 0, 0>
            sage: type(e)
            <class 'sage.modules.finitely_presented_over_the_steenrod_algebra.module.FP_Module_with_category.element_class'>
            sage: f = M((Sq(6), 0, Sq(2))); f
            <Sq(6), 0, Sq(2)>
            sage: type(f)
            <class 'sage.modules.finitely_presented_over_the_steenrod_algebra.module.FP_Module_with_category.element_class'>
            sage: g = M((Sq(6), 0, Sq(2))); g
            <Sq(6), 0, Sq(2)>
            sage: M(g)
            <Sq(6), 0, Sq(2)>
            sage: type(g)
            <class 'sage.modules.finitely_presented_over_the_steenrod_algebra.module.FP_Module_with_category.element_class'>

        """

        if isinstance(x, FP_Element):
            return x
        elif x == 0:
            return self.element_class(self, len(self.degs)*(0,))
        else:
            return self.element_class(self, x)

    def an_element(self, degree=None):
        r"""
        Return an element of the module.

        This function chooses deterministically an element of the module in the
        given degree.

        INPUT:

        - ``degree`` --  The degree of the element to construct.  If the default
          value ``None`` is given, a degree will be chosen by the function.

        OUTPUT:

        -  ``e`` -- An element of the given degree.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.module import FP_Module
            sage: M = FP_Module(degs=(0,2,4), relations=((Sq(4),Sq(2),0),))
            sage: M.zero()
            <0, 0, 0>
            sage: M.an_element()
            <Sq(1,1,1), Sq(3,2), Sq(0,0,1)>
            sage: M.an_element(0)
            <1, 0, 0>
            sage: M.an_element(1)
            <Sq(1), 0, 0>
            sage: M.an_element(2)
            <Sq(2), 1, 0>
            sage: M.an_element(3)
            <Sq(0,1), Sq(1), 0>
            sage: M.an_element(4)
            <Sq(1,1), Sq(2), 1>
            sage: M.an_element(5)
            <Sq(2,1), Sq(0,1), Sq(1)>
            sage: M.an_element(6)
            <Sq(0,2), Sq(1,1), Sq(2)>
            sage: M.an_element(17)
            <Sq(2,0,0,1), Sq(2,2,1), Sq(4,3)>
            sage: N = FP_Module(degs=(2,), algebra = SteenrodAlgebra(2))
            sage: for d in range(20):
            ....:     N.an_element(degree=d)
            <0>
            <0>
            <1>
            <Sq(1)>
            <Sq(2)>
            <Sq(0,1)>
            <Sq(1,1)>
            <Sq(2,1)>
            <Sq(6)>
            <Sq(4,1)>
            <Sq(5,1)>
            <Sq(3,2)>
            <Sq(1,3)>
            <Sq(2,3)>
            <Sq(0,4)>
            <Sq(6,0,1)>
            <Sq(4,1,1)>
            <Sq(2,2,1)>
            <Sq(0,3,1)>
            <Sq(3,0,2)>

        """

        if len(self.degs) == 0:
            return self.element_class(self, [])

        if degree == None:
            degree = max(self.degs) + 7

        coefficients = []

        for g in self.degs:
            basis = self.base_ring().basis(degree - g) if degree >= g else ()
            # All of the algebra generators in basis will bring the
            # module generator in dimension g to dimension
            # g + (topDimension - g) = topDimension.  Picking any one of them
            # will do, so we pick the one with index (g (mod l)).
            l = len(basis)
            coefficients.append(0 if l == 0 else basis[g % l])

        return self.element_class(self, coefficients)

    def _repr_(self):
        """
        Construct a string representation of the module.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.module import FP_Module
            sage: M = FP_Module((0,2,4),((Sq(4),Sq(2),0),)); M
            Finitely presented module on 3 generators and 1 relation over sub-Hopf
            algebra of mod 2 Steenrod algebra, milnor basis, profile function [3, 2, 1]

            sage: N = FP_Module((0,1),((Sq(2),Sq(1)),(Sq(2)*Sq(1),Sq(2)))); N
            Finitely presented module on 2 generators and 2 relations over sub-Hopf
            algebra of mod 2 Steenrod algebra, milnor basis, profile function [2, 1]
        """
        return "Finitely presented module on %s generator%s and %s relation%s over %s"\
            %(len(self.degs), "" if len(self.degs) == 1 else "s",
              len(self.rels), "" if len(self.rels) == 1 else "s",
              self._profile_algebra)

    def _pres_(self, n, profile=None):
        """
        Return a quotient vector space isomorphic to the ``n``-th part of the
        module, together with a chosen isomorphism.

        Let `M` denote this module, and `F\to M` be the free part of the
        finite presentation of `M`.  This function returns a quotient vector
        space ``quotient``, isomorphic to the vector space of elements of `M`
        of degree `n`.  The isomorphism is given by the second return value,
        ``bas_gen`` which is a list of pairs `(k, a)` where `k` identifies
        a module generator by its index, and `a` is a homogeneous element of
        the Steenrod algebra.  This list represents a chosen correspondance
        between the standard basis vectors of ``quotient``, and `F_n`.

        INPUT:

        - ``n`` -- The degree of the presentation.

        - ``profile`` -- The profile function to use.  When the default
          value ``None`` is used, the profile is taken from the module.

        OUTPUT:

        -  ``quotient`` - A finite dimensional vector space quotient `V/W` over
           `F_p` isomorphic to the degree `n` part of the module.

        -  ``bas_gen`` -- A list of pairs `(gen_number, algebra element)`
           corresponding to the standard basis `quotient`.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.module import FP_Module
            sage: M = FP_Module((0,2,4),((Sq(4),Sq(2),0),)); M((Sq(2),0,0))
            <Sq(2), 0, 0>
            sage: M_n, bas = M._pres_(4)
            sage: dim(M_n)
            3
            sage: bas
            [(0, Sq(1,1)), (0, Sq(4)), (1, Sq(2)), (2, 1)]

        """
        if profile == None:
            profile = self.profile()
        alg = SteenrodAlgebra(p=self.char,profile=profile)
        bas_gen = reduce(lambda x,y : x+y,\
                  [[(i,bb) for bb in alg.basis(n - self.degs[i])]\
                           for i in range(len(self.degs))],[])

        bas_vec = VectorSpace(FiniteField(self.char),len(bas_gen))
        bas_dict = dict(zip(bas_gen,bas_vec.basis()))
        rel_vec = bas_vec.subspace([0])

        numRelations = len(self.rels)
        numRelDegs = len(self.reldegs)

        for i in range(numRelations):
            if self.reldegs[i] <= n:
                for co in alg.basis(n - self.reldegs[i]):
                    r = zip(range(len(self.degs)),[co*c for c in self.rels[i]])
                    r = filter(lambda x : not x[1].is_zero(),r) # remove trivial
                    if len(r) != 0:
                        r = reduce(lambda x,y : x+y,
                            [map(lambda xx: (pr[0],alg._milnor_on_basis(xx[0]),xx[1]),\
                                 [z for z in pr[1]]) for pr in r])
                        rel_vec += bas_vec.subspace(\
                            [reduce(lambda x,y: x+y,\
                            map(lambda x: x[2]*bas_dict[(x[0],x[1])],r))])
        quotient = bas_vec/rel_vec
        return quotient, bas_gen

    def _lc_(self, coefficients, basis_elements):
        """
        Create the FP_Element given by the ``coefficients`` and ``basis_elements``.

        Both input arguments are assumed to be iterables of equal length.

        NOTE: This function is intended for internal use only.

        INPUT:

        - ``coefficients`` -- An iterable of algebra elements `[c_i]_i`.

        - ``basis_elements`` -- A iterable of tuples `[(k_i, a_i)]_i` where
          each `k_i` identifies a module generator by its index, and each `a_i`
          is an algebra element.

        OUTPUT: The sum `\Sum_i c_i \cdot a_i \cdot g_{k_i}`

        NOTE: The output is not normalized, i.e. the sum is taken in the free
        module.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.module import FP_Module
            sage: M = FP_Module((2, 3), ((Sq(2), Sq(1)), (0, Sq(2))))
            sage: bas = [(0, 1)]; co = [Sq(1)]
            sage: x = M._lc_(co, bas); x
            <Sq(1), 0>
            sage: bas2 = [(1, 1)]
            sage: y = M._lc_(co, bas2); y
            <0, Sq(1)>

        """
        if len(coefficients) != len(basis_elements):
            raise ValueError,\
            "Number of coefficients (%s) must be the same as number of basis elements (%s) " \
                % (len(co), len(bas))

        return reduce(lambda x,y : x+y, \
              [(coefficients[i]*basis_elements[i][1])*self.gen(basis_elements[i][0]) for i in range(len(coefficients))],
              self(0))

    def basis(self, n, profile=None):
        r"""
        Return a list of elements which form a basis for the vector space of
        all degree `n` elements.

        NOTE: The name "basis" refers to the vector space basis and not basis
        for the full module (modules with bases are free).

        INPUT:

        - ``n`` -- The degree in which the basis will be taken.

        - ``profile`` -- The profile function which is used in the calculation.

        OUTPUT: A list of elements forming a vector space basis for the degree
        `n` part of the module.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.module import FP_Module
            sage: M = FP_Module((2, 3), ((Sq(2), Sq(1)), (0,Sq(2))))
            sage: M.basis(0)
            []
            sage: M.basis(5)
            [<Sq(0,1), 0>]
            sage: M.basis(6)
            [<Sq(1,1), 0>]
            sage: M.basis(6, profile=[5,4,3,2,1])
            [<Sq(1,1), 0>, <Sq(4), 0>]
            sage: for i in range(10):
            ....:     print ("Basis for M in dimension %d: %s" % (i, M.basis(i)))
            Basis for M in dimension 0: []
            Basis for M in dimension 1: []
            Basis for M in dimension 2: [<1, 0>]
            Basis for M in dimension 3: [<Sq(1), 0>, <0, 1>]
            Basis for M in dimension 4: [<Sq(2), 0>]
            Basis for M in dimension 5: [<Sq(0,1), 0>]
            Basis for M in dimension 6: [<Sq(1,1), 0>]
            Basis for M in dimension 7: []
            Basis for M in dimension 8: []
            Basis for M in dimension 9: []

        """
        if profile == None:
            profile = self.profile()
        M_n, bas = self._pres_(n, profile=profile)
        return [self._lc_(M_n.lift(v), bas) for v in M_n.basis()]

    def gens(self):
        r"""
        Return the list of module elements which generates the module.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.module import FP_Module
            sage: M = FP_Module((0, 2, 3)); M.gens()
            [<1, 0, 0>, <0, 1, 0>, <0, 0, 1>]
            sage: N = FP_Module((0,1),((Sq(2),Sq(1)),)); N.gens()
            [<1, 0>, <0, 1>]

        """
        return [self.element_class(self, Utility._del_(i, len(self.degs)))
           for i in range(len(self.degs))]

    def gen(self, index=0):
        r"""
        Return the module generator (as an module element) with the given
        index.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.module import FP_Module
            sage: M = FP_Module((0,2,3)); M.gen(0)
            <1, 0, 0>
            sage: N = FP_Module((0, 1), ((Sq(2), Sq(1)),)); N.gen(1)
            <0, 1>

        """
        if index < 0 or index >= len(self.degs):
            raise ValueError,\
            "Module has generators numbered 0 to %s; generator %s does not exist" % (len(self.degs) - 1, index)
        return self.element_class(self, Utility._del_(index, len(self.degs)))

    def _Hom_(self, Y, category):
        r"""
        The internal hook used by the free function
        sage.categories.homset.hom.Hom() to create homsets involving this
        parent.

        TESTS::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.module import create_fp_module
            sage: F = create_fp_module([1,3]);
            sage: L = create_fp_module([2,3], [(Sq(2),Sq(1)), (0,Sq(2))]);
            sage: homset = Hom(F, L); homset
            Set of Morphisms from Finitely presented module on 2 generators ...

        """
        from .homspace import FP_ModuleHomspace
        return FP_ModuleHomspace(self, Y, category)

    def min_pres(self):
        r"""
        Return a minimal presentation of this module.

        OUTPUT:

        -  ``i`` - An isomorphism from a minimal presentation `M` to this module.

        -  ``e`` - The inverse of ``i``.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.module import create_fp_module
            sage: K = create_fp_module([0,1], [[Sq(2),Sq(1)],[0,Sq(2)],[Sq(3),0]])
            sage: i, e = K.min_pres()
            sage: i.domain().rels
            ((Sq(2), Sq(1)), (0, Sq(2)))
            sage: i.codomain().rels
            ((Sq(2), Sq(1)), (0, Sq(2)), (Sq(3), 0))
            sage: e.codomain() is i.domain()
            True
            sage: (i*e) is Hom(K, K).identity()
            False
            sage: (i*e) == Hom(K, K).identity()
            True
            sage: M = i.domain()
            sage: (e*i) == Hom(M, M).identity()
            True

        """
        identity_morphism = Hom(self, self).identity()
        return identity_morphism.image()

    def min_profile(self):
        r"""
        Return the profile of the smallest sub-Hopf algebra containing self.

        OUTPUT: The profile function of the sub-Hopf algebra with the smallest
        degree containing self.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.module import FP_Module
            sage: A3 = SteenrodAlgebra(p=2,profile=(4,3,2,1))
            sage: Y = FP_Module((0,), ((Sq(1),),),algebra=A3)
            sage: Y.profile()
            (4, 3, 2, 1)
            sage: Y.min_profile()
            (1,)
        """
        if not self.rels:
            return self.algebra._profile
        else:
            profile = Profile.enveloping_profile_profiles(\
                     [Profile.enveloping_profile_elements(r,self.char) for r in self.rels],\
                      self.char)
            return profile

    def suspension(self, t):
        r"""
        Suspend the module by the given degree.

        INPUT:

        - ``t`` -- An integer by which the module is suspended.

        OUTPUT:

        - ``C`` -- A a module which is identical to this module by a shift
          of degrees by the integer ``t``.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.module import FP_Module
            sage: Y = FP_Module((0,), ((Sq(1),),))
            sage: X = Y.suspension(4)
            sage: X.degs;X.rels
            (4,)
            ((Sq(1),),)
            sage: M = FP_Module( (2,3), ( (Sq(2), Sq(1)), (0, Sq(2)) ) )
            sage: Q = M.suspension(1)
            sage: Q.degs;Q.rels
            (3, 4)
            ((Sq(2), Sq(1)), (0, Sq(2)))
            sage: Q = M.suspension(-3)
            sage: Q.degs
            (-1, 0)
            sage: Q = M.suspension(0)
            sage: Q.degs
            (2, 3)

        """
        generator_degrees = [g + t for g in self.degs]
        return FP_Module(degs=tuple(generator_degrees), relations=self.rels, algebra=self.profile_algebra())

    def submodule(self, spanning_elements):
        r"""
        Construct the submodule ``S`` of this module spanned by the give
        elements.

        INPUT:

        -  ``spanning_elements``  - A list of elements of this module.

        OUTPUT:

        - ``i`` -- The inclusion of ``S`` into this module.

        - ``p`` -- The quotient homomorphism from the free module on the
          elements of ``spanning_elements`` to ``S``.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.module import FP_Module
            sage: M = FP_Module((0,1), ((Sq(2),Sq(1)),))
            sage: i,p = M.submodule([M.gen(0)])
            sage: S = i.domain()
            sage: S.degs;S.rels
            (0,)
            ((Sq(3),),)

        """
        degs = [x.degree for x in spanning_elements]
        F = FP_Module(tuple(degs), algebra=self.profile_algebra())
        pr = Hom(F,self)(spanning_elements)
        return pr.image()

    def resolution(self, k, kernels=False, verbose=False):
        r"""
        Return a resolution of this module of length ``k``.

        INPUT:

        - ``k`` -- An non-negative integer.

        - ``kernels`` -- A boolean to control if the kernel modules should be
          returned.  (optional, default: ``False``)

        - ``verbose`` -- A boolean to control if log messages should be emitted.
          (optional, default: ``False``)

        OUTPUT:

        - ``res`` -- A list of homomorphisms `[f_0, f_1, \ldots, f_k]`
          constituting a free resolution of length `k`.  The indexing is set up
          such that `\text{codomain}(f_i) = \text{domain}(f_{i-1})` and
          `\text{codomain}(f_0)` is this module.

        - If ``kernels`` == True: ``kers`` -- A list of injections `[\text{inj}_i \mid i = 0 ... k-1]` where
          `\text{inj}_i` is an injective homomorphism `K_i \rightarrow F_i=\text{domain}(f_i)`
          such that
          `\text{im} (\text{inj}_i: K_i \to F_i) = \text{ker} (f_i)` for `i = 0 ... k-1`.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.module import FP_Module
            sage: N = FP_Module((0,1), ((Sq(2),Sq(1)),))
            sage: res, kers = N.resolution(3, kernels=True, verbose=True)
            Step  3
            Computing kernel degree 3/7
            Computing kernel degree 4/7
            Computing kernel degree 5/7
            Computing kernel degree 6/7
            Computing kernel degree 7/7
            Step  2
            Step  1
            Computing kernel degree 10/14
            Computing kernel degree 11/14
            Computing kernel degree 12/14
            Computing kernel degree 13/14
            Computing kernel degree 14/14
            Step  0
            sage: len(res)
            4
            sage: len(kers)
            3
            sage: for i, kernel_inj in enumerate(kers):
            ....:     f = res[i]
            ....:     x = kernel_inj.domain().an_element()
            ....:     y = f(kernel_inj(x))
            ....:     if not y.is_zero():
            ....:         raise ValueError, 'The element %s should be in the \
            ....:            kernel of:\n%s\n but it maps to %s.' % (x, f, y)
            sage: M = FP_Module((0,1), ((Sq(2),Sq(1)),))
            sage: resolution = M.resolution(3, verbose=True)
            Step  3
            Computing kernel degree 3/7
            Computing kernel degree 4/7
            Computing kernel degree 5/7
            Computing kernel degree 6/7
            Computing kernel degree 7/7
            Step  2
            Step  1
            Computing kernel degree 10/14
            Computing kernel degree 11/14
            Computing kernel degree 12/14
            Computing kernel degree 13/14
            Computing kernel degree 14/14
            Step  0
            sage: for i, r in enumerate(resolution): print ('f_%d: %s' % (i, r))
            f_0: Module homomorphism of degree 0 defined by sending the generators
              [<1, 0>, <0, 1>]
            to
              [<1, 0>, <0, 1>]
            f_1: Module homomorphism of degree 0 defined by sending the generators
              [<1>]
            to
              [<Sq(2), Sq(1)>]
            f_2: Module homomorphism of degree 0 defined by sending the generators
              [<1>]
            to
              [<Sq(3,1)>]
            f_3: Module homomorphism of degree 0 defined by sending the generators
              [<1, 0>, <0, 1>]
            to
              [<Sq(1)>, <Sq(2)>]
        """

        kers =[]
        res = self._resolution(k, kers, verbose)
        if kernels == True:
            return res, kers
        else:
            return res

    def _resolution(self,k,kers,verbose=False):
        """
            The private implementation of resolution().

        INPUT:

        - ``k`` -- An non-negative integer.

        - ``kers`` -- A list or None.  If a list is given, the kernel modules
          is appended to it.

        - ``verbose`` -- A boolean to control if log messages should be emitted.
          (optional, default: ``False``)

        OUTPUT:

        The same as the output of resolution().

        TESTS::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.module import FP_Module
            sage: N = FP_Module((0,1), ((Sq(2),Sq(1)),))
            sage: kers=[]
            sage: res = N._resolution(2, kers, verbose=True)
            Step  2
            Computing kernel degree 3/7
            Computing kernel degree 4/7
            Computing kernel degree 5/7
            Computing kernel degree 6/7
            Computing kernel degree 7/7
            Step  1
            Step  0
            sage: print(res[2])
            Module homomorphism of degree 0 defined by sending the generators
              [<1>]
            to
              [<Sq(3,1)>]
            sage: print(kers[1])
            Module homomorphism of degree 0 defined by sending the generators
              [<1>]
            to
              [<Sq(3,1)>]
        """

        C0 = FP_Module(tuple(self.degs), algebra=self.profile_algebra())
        eps = Hom(C0,self)(self.gens())

        if verbose:
              print "Step ",k
        if k <= 0:
            return [eps]
        else:
            i0 = eps.kernel(verbose=verbose)
            if not kers is None:
                kers.append(i0)
            r = i0.domain()._resolution(k-1, kers, verbose)
            r[0] = i0*r[0]
            return [eps] + r

