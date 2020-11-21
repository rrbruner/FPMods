from sage.modules.finitely_presented_over_the_steenrod_algebra.fp_module import *

rels = [ [Sq(1),0,0,0], [Sq(2),0,0,0], [Sq(4),0,0,0], [Sq(8),0,0,0], [0,Sq(1),0,0], [0,Sq(2),0,0], [    0,Sq(4),0,0], [Sq(31),Sq(14),0,0], [0,Sq(20),0,0], [0,0,Sq(1),0], [0,0,Sq(2),0], [0,Sq(31),Sq(6),0],     [0,0,Sq(8),0], [0,0,0,Sq(1)], [0,0,Sq(31),Sq(2)], [0,0,0,Sq(4)], [0,0,0,Sq(8)] ]

M = FP_Module([0, 17, 42, 71], SteenrodAlgebra(2), relations=rels)

# The performance will be measured when fp_morphism._resolve_kernel() reaches degree 40:
M.resolution(3, top_dim=41, verbose=True)
