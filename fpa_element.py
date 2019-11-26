from .fp_element import FP_Element

class FPA_Element(FP_Element):

    def __init__(self, module, coefficients):
        r"""

        NOTE: Never use this constructor explicitly, but rather the parent's
              call method, or this class' __call__ method.  The reason for this
              is that the dynamic type of the element class changes as a
              consequence of the category system.

        """

        FP_Element.__init__(self, module, coefficients)


