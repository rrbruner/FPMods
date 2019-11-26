
from sage.structure.element import ModuleElement as SageModuleElement
from .free_element import FreeModuleElement

class FP_Element(SageModuleElement):

    def __init__(self, module, coefficients):
        r"""

        NOTE: Never use this constructor explicitly, but rather the parent's
              call method, or this class' __call__ method.  The reason for this
              is that the dynamic type of the element class changes as a
              consequence of the category system.

        """

        # Store the free representation of the element.
        self.free_element = FreeModuleElement(module.j.codomain(), coefficients)

        SageModuleElement.__init__(self, parent=module)

    def coefficients(self):
        r"""
        """
        return self.free_element.coefficients()

    def degree(self):
        r"""
        """
        return self.free_element.degree()

    def _repr_(self):
        r"""
        """
        return self.free_element._repr_()

    def _lmul_(self, a):
        r"""
        This is the action which is called when the left module action is 
        evaluated.
        """
        return self.parent()(a*self.free_element)

    def _neg_(self):
        r"""
        The negative of the element.
        """
        return self.parent()(-self.free_element)

    def _add_(self, other):
        r"""
        The module sum of this and the given module element.
        """
        return self.parent()(self.free_element + other.free_element)

    def _cmp_(self, other):
        r"""
        Compares two FP_Elements for equality. Cannot compare elements in
        different degrees or different modules.

        """
        if self.parent() != other.parent():
            raise TypeError, "Cannot compare elements in different modules."
        if self.degree() != other.degree() and self.degree() != None and other.degree() != None:
            raise ValueError, \
            "Cannot compare elements of different degrees %s and %s"\
            %(self.degree(), other.degree())
        if (self._add_(other._neg_()))._nonzero_():
            return 1
        else:
            return 0

    def vector_presentation(self):
        r"""
        """
        if self.degree() == None:
            return None

        v = self.free_element.vector_presentation()
        M_n = self.parent().vector_presentation(self.degree())
        # assert(v in M_n.V())

        return M_n.quotient_map()(v)

    def _nonzero_(self):
        r"""

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
            sage: M = FP_Module([0,2,4], SteenrodAlgebra(2), [[Sq(4),Sq(2),0]])
            sage: M(0)._nonzero_()
            False
            sage: M((Sq(6), 0, Sq(2)))._nonzero_()
            True
            sage: a = M((Sq(1)*Sq(2)*Sq(1)*Sq(4), 0, 0))
            sage: b = M((0, Sq(2)*Sq(2)*Sq(2), 0))
            sage: a._nonzero_()
            True
            sage: b._nonzero_()
            True
            sage: (a + b)._nonzero_()
            False

        """
        if self.degree() == None:
            return False

        return self.vector_presentation() != 0

    def normalize(self):
        r"""
        The normal form of ``self``.

        EXAMPLES::

            sage: from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import FP_Module
            sage: M = FP_Module([0,2,4], SteenrodAlgebra(2), [[Sq(4),Sq(2),0]])
            sage: m = M((Sq(6), 0, Sq(2)))
            sage: m; m.normalize()
            <Sq(6), 0, Sq(2)>
            <Sq(6), 0, Sq(2)>
            sage: n = M((Sq(4), Sq(2), 0))
            sage: n; n.normalize()
            <Sq(4), Sq(2), 0>
            <0, 0, 0>

        """

        if self.degree() == None:
            return self

        v = self.vector_presentation()
        return self.parent().element_from_coordinates(v, self.degree())

    def __hash__(self):
        r"""
        """
        return hash(self.coefficients())

