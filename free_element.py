
from copy import copy

from sage.misc.cachefunc import cached_method

from sage.categories.homset import Hom
from sage.modules.free_module import VectorSpace
from sage.rings.infinity import PlusInfinity
from sage.rings.integer import Integer
from sage.structure.element import ModuleElement as SageModuleElement

#--------------------------------------------------------------------------------
#-----------------------Elements-of-FP_Modules-----------------------------------
#--------------------------------------------------------------------------------

class FreeModuleElement(SageModuleElement):

    def __init__(self, module, coefficients):
        r"""

        NOTE: Never use this constructor explicitly, but rather the parent's
              call method, or this class' __call__ method.  The reason for this
              is that the dynamic type of the element class changes as a
              consequence of the category system.

        """
        if isinstance(coefficients, FreeModuleElement):
            self._coefficients = coefficients._coefficients
        elif isinstance(coefficients, Integer) or isinstance(coefficients, int):
            # Kroenecker delta if a single index is given.
            Kroenecker = lambda i: 1 if i == coefficients else 0
            self._coefficients = tuple([module.base_ring()(Kroenecker(i)) for i in range(len(module.generator_degrees()))])
        else:
            self._coefficients = tuple([module.base_ring()(x) for x in coefficients])

        if len(self._coefficients) != len(module.generator_degrees()):
            raise ValueError('Incorrect number of coefficients.')

        # Check homogenity and store the degree of the element.
        self._degree = None
        for g, c in zip(module.generator_degrees(), self._coefficients):
            if not c.is_zero():
                d = g + c.degree()
                if self._degree == None:
                    self._degree = d
                else:
                    if self._degree != d:
                        raise ValueError('Non-homogeneous element defined.')

        SageModuleElement.__init__(self, parent=module)

    def coefficients(self):
        return self._coefficients

    def degree(self):
        r"""
            Return the degree of this element.

            Note that if this element is zero, then this function can return
            None.  (But not all zero elements have degree == None, e.g. x-x,
            where x != 0.
        """
        return self._degree

    def _repr_(self):
        r"""
        """
        return '<%s>' % ', '.join(['%s' % c for c in self._coefficients])

    def _lmul_(self, a):
        r"""
        This is the action which is called when the left module action is 
        evaluated.

        """
        return self.parent()([a*c for c in self._coefficients])

    def _neg_(self):
        r"""
        The negative of the element.

        """
        return self.parent()([-c for c in self._coefficients])


    def _add_(self, other):
        r"""
        Returns the module sum of this and the given module element.
        """
        if self.parent() != other.parent():
            raise TypeError, "Can't add element in different modules"
        if self._degree == None: # if self = 0, degree is None
            return self.parent()(other.coefficients())
        if other._degree == None:   # if other = 0, degree is None
            return self.parent()(self._coefficients)
        if self._degree != other._degree:
            raise ValueError, "Can't add element of degree %s and %s"\
                  %(self._degree, other._degree)
        return self.parent()(
            [x + y for x,y in zip(self._coefficients, other.coefficients())])

    def _cmp_(self, other):
        r"""
        Compares two FP_Elements for equality. Cannot compare elements in
        different degrees or different modules.
        """
        if self.parent() != other.parent():
            raise TypeError, "Cannot compare elements in different modules."
        if self._degree != other._degree and self._degree != None and other._degree != None:
            raise ValueError, \
            "Cannot compare elements of different degrees %s and %s"\
            %(self._degree, other._degree)
        if (self._add_(other._neg_()))._nonzero_():
            return 1
        else:
            return 0

    @cached_method
    def vector_presentation(self):
        r"""
        """
        n = self._degree
        if n == None:
             return 0

        bas_gen = self.parent().basis_elements(self._degree)
        base_vec = self.parent().vector_presentation(self._degree)

        base_dict = dict(zip(bas_gen, base_vec.basis()))

        # Create a sparse representation of the element.
        sparse_coeffs = [x for x in enumerate(self._coefficients) if not x[1].is_zero()]

        vector = base_vec.zero()
        for summand_index, algebra_element in sparse_coeffs:
            for scalar_coefficient, monomial in zip(algebra_element.coefficients(), algebra_element.monomials()):
                vector += scalar_coefficient*base_dict[monomial*FreeModuleElement(self.parent(), summand_index)]

        return vector

    def _nonzero_(self):
        r"""
        """
        if self._degree == None:
            return False

        return not all(c == 0 for c in self._coefficients)

    def __hash__(self):
        return hash(self._coefficients)

