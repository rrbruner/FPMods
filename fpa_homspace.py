from __future__ import absolute_import


from .fp_homspace import FP_ModuleHomspace
from .fpa_morphism import FPA_ModuleMorphism


def is_FPA_ModuleHomspace(x):
    r"""
    """
    return isinstance(x, FP_ModuleHomspace)

class FPA_ModuleHomspace(FP_ModuleHomspace):
    # In the category framework, Elements of the class FPA_ModuleHomspace are of the
    # class FPA_ModuleMorphism, see
    # http://doc.sagemath.org/html/en/thematic_tutorials/coercion_and_categories.html#implementing-the-category-framework-for-the-elements
    Element = FPA_ModuleMorphism

