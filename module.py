
from sage.structure.element import ModuleElement
class MyElement(ModuleElement):
    def __init__(self, parent, x):
#        """
#        EXAMPLES::
#
#        sage: from sage.modules.fpmods.module import MyModule, MyElement
#        sage: m = MyElement([0,Sq(3),Sq(1)],MyModule([2,3,5]));m
#        [0, Sq(3), Sq(1)]
#
#        """

        self.x = x
        sage.structure.element.ModuleElement.__init__(self, parent=parent)

    def _lmul_(self, c):
        return self.parent()(c*self.x)

    def _add_(self, other):
        return self.parent()(self.x + other.x)

    def __cmp__(self, other):
        return cmp(self.x, other.x)

    def __hash__(self):
        return hash(self.x)

    def _repr_(self):
        return repr(self.x)


import sage.modules.fpmods.utility as Utility
import sage.modules.fpmods.profile as Profile

from sage.algebras.steenrod.steenrod_algebra import SteenrodAlgebra

from sage.structure.unique_representation import UniqueRepresentation
from sage.modules.module import Module
class MyModule(UniqueRepresentation, Module):
    r"""
    A finitely presented module over a sub-Hopf algebra of the
    Steenrod Algebra (including the full Steenrod Algebra).

    EXAMPLES:

    These examples show how to define modules over the Steenrod Algebra at the
    prime 2. The last example is a free module with a single generator in
    degree 4.

    ::

        sage: from sage.modules.fpmods.module import MyModule
        sage: degs = [1,3]
        sage: K = MyModule(degs = tuple(degs));K
        Finitely presented module on 2 generators and 0 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function []
        sage: L = MyModule((2,3),((Sq(2),Sq(1)),(0,Sq(2))));L
        Finitely presented module on 2 generators and 2 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [2, 1]
        sage: M = MyModule((2,3),((Sq(2),Sq(1)),));M
        Finitely presented module on 2 generators and 1 relation over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [2, 1]
        sage: K.category()
        Category of modules over mod 2 Steenrod algebra, milnor basis
        sage: K(

#        sage: from sage.misc.sage_unittest import TestSuite
#        sage: TestSuite(K).run()

    """
    Element = MyElement

    def __init__(self, degs, rels=(), char=None, algebra=None):
        if (char is None) and (algebra is None):
            self.char = 2
            self.algebra = SteenrodAlgebra(self.char, profile=(0,))
        elif (char is None) and (algebra is not None):
            self.algebra = algebra
            self.char = self.algebra._prime
        elif (char is not None) and (algebra is None):
            self.char = char
            if char == 2:
                self.algebra = SteenrodAlgebra(p=self.char, profile=(0,))
            else:
                self.algebra = SteenrodAlgebra(p=self.char, profile = ((),(0,)))
        else:
            self.char = char
            self.algebra = algebra
        if (self.char != self.algebra.prime()):
            raise TypeError, "Characteristic and algebra are incompatible."

        for i in range(len(degs) - 1):
            if degs[i] > degs[i+1]:
                raise TypeError, "Degrees of generators must be in non-decreasing order."
        if not rels:
            prof = self.algebra._profile
        else:
             prof = Profile.enveloping_profile_profiles(\
                      [Profile.enveloping_profile_elements(r, self.char) for r in rels]\
                      +[list(self.algebra._profile)], self.char)
        self.algebra = SteenrodAlgebra(p=self.char, profile=prof)
        for r in rels:
            if r == [0]*len(degs):
                rels.remove([0]*len(degs))
        self.rels = [[self.algebra(coeff) for coeff in r] for r in rels]
        self.degs = list(degs)
        try:                        # Figure out if a rel isnt right
            self.reldegs = [Utility._deg_(self.degs,r) for r in self.rels]
        except ValueError:
            for r in rels:          # Figure out which rel isnt right
                try:
                   Utility._deg_(degs,r)
                except ValueError:
                   raise ValueError, "Inhomogeneous relation %s" % r
        self._populate_coercion_lists_()
        Module.__init__(self, SteenrodAlgebra(self.char))

    def _element_constructor_(self, x):
        """
        Forms the element with ith coefficient x[i].
        This results in The identity operation if x is already in the module.

        INPUT:

        -   ``x``  - A list of coefficient.

        OUTPUT: An FP_Element with coefficients from x.

        EXAMPLES::

            sage: from sage.modules.fpmods.fpmods import FP_Module
            sage: M = FP_Module([0,2,4],[[Sq(4),Sq(2),0]]); M([Sq(2),0,0])
            [Sq(2), 0, 0]

        """
        if x == 0:
            return FP_Element([ 0 for i in self.degs],self)
        elif type(x) == type([0]):
            return FP_Element(x,self)
        elif x.module == self:
            return x
        else:
            raise ValueError,"Element not in module"

        if isinstance(x, MyElement): x = x.x
        return self.element_class(self, self.base_ring()(x))

    def __cmp__(self, other):
        if not isinstance(other, MyModule):
            return cmp(type(other),MyModule)
        return cmp(self.base_ring(),other.base_ring())

    def _repr_(self):
        """
        String representation of the module.

        EXAMPLES::

            sage: from sage.modules.fpmods.module import MyModule
            sage: M = MyModule((0,2,4),((Sq(4),Sq(2),0),)); M
            Finitely presented module on 3 generators and 1 relation over sub-Hopf
            algebra of mod 2 Steenrod algebra, milnor basis, profile function [3, 2, 1]

            sage: N = MyModule((0,1),((Sq(2),Sq(1)),(Sq(2)*Sq(1),Sq(2)))); N
            Finitely presented module on 2 generators and 2 relations over sub-Hopf
            algebra of mod 2 Steenrod algebra, milnor basis, profile function [2, 1]


        """
        return "Finitely presented module on %s generator%s and %s relation%s over %s"\
            %(len(self.degs), "" if len(self.degs) == 1 else "s",
              len(self.rels), "" if len(self.rels) == 1 else "s",
              self.algebra)

