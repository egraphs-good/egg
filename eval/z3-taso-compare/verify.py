#!/usr/bin/env python3

import sys
import os
from itertools import product

import z3
from z3 import ForAll

T = z3.DeclareSort('T')
P = z3.IntSort()

OP_INPUT, \
OP_WEIGHT, \
OP_ANY, \
OP_CONV2D, \
OP_DROPOUT, \
OP_LINEAR, \
OP_POOL2D_MAX, \
OP_POOL2D_AVG, \
OP_RELU, \
OP_SIGMOID, \
OP_TANH, \
OP_BATCHNORM, \
OP_CONCAT, \
OP_SPLIT, \
OP_RESHAPE, \
OP_TRANSPOSE, \
OP_EW_ADD, \
OP_EW_MUL, \
OP_MATMUL, \
OP_MUL, \
OP_ENLARGE, \
OP_MERGE_GCONV, \
OP_CONSTANT_IMM, \
OP_CONSTANT_ICONV, \
OP_CONSTANT_ONE, \
OP_CONSTANT_POOL = range(26)

PM_OP_TYPE, \
PM_NUM_INPUTS, \
PM_NUM_OUTPUTS, \
PM_GROUP, \
PM_KERNEL_H, \
PM_KERNEL_W, \
PM_STRIDE_H, \
PM_STRIDE_W, \
PM_PAD, \
PM_ACTI, \
PM_NUMDIM, \
PM_AXIS, \
PM_PERM, \
PM_OUTSHUFFLE, \
PM_MERGE_GCONV_COUNT = range(15)

AC_MODE_NONE, \
AC_MODE_SIGMOID, \
AC_MODE_RELU, \
AC_MODE_TANH = range(4)

PD_MODE_SAME, \
PD_MODE_VALID = range(2)

# map opId to (name, (key,rng)*, input arity, outputa arity, possible input dimensions)
operator_data = {
    OP_CONSTANT_POOL: ('const_pool', ((PM_KERNEL_H, {3}), (PM_KERNEL_W, {3})), 0, 1, {}),
    OP_CONSTANT_ICONV: ('const_iconv', ((PM_KERNEL_H, {3}), (PM_KERNEL_W, {3})), 0, 1, {}),
    OP_CONSTANT_IMM: ('const_imm', (), 0, 1, {}),
    OP_CONSTANT_ONE: ('const_one', (), 0, 1, {}),
    OP_CONV2D: ('conv2d', ((PM_STRIDE_H, {1,2}), (PM_STRIDE_W, {1,2}), (PM_PAD, {0,1}), (PM_ACTI, {AC_MODE_NONE, AC_MODE_RELU})), 2, 1, {4}),
    OP_POOL2D_MAX: ('pool2d_max', ((PM_KERNEL_H, {3}), (PM_KERNEL_W, {3}), (PM_STRIDE_H, {1, 2}), (PM_STRIDE_W, {1,2}), (PM_PAD, {0,1})), 1, 1, {4}),
    OP_POOL2D_AVG: ('pool2d_avg', ((PM_KERNEL_H, {3}), (PM_KERNEL_W, {3}), (PM_STRIDE_H, {1, 2}), (PM_STRIDE_W, {1,2}), (PM_PAD, {0,1})), 1, 1, {4}),
    OP_RELU: ('relu', (), 1, 1, {2, 3, 4}),
    OP_CONCAT: ('concat', ((PM_AXIS, {0, 1, 2, 3}),), 2, 1, {2,3,4}),
    OP_SPLIT: ('split', ((PM_AXIS, {0, 1, 2, 3}),), 1, 2, {2,3,4}),
    OP_TRANSPOSE: ('transpose', (), 1, 1, {2}),
    OP_ENLARGE: ('enlarge', ((PM_KERNEL_H, {3}), (PM_KERNEL_W, {3})), 1, 1, {4}),
    OP_EW_ADD: ('ewadd', (), 2, 1, {2,3,4}),
    OP_EW_MUL: ('ewmul', (), 2, 1, {2,3,4}),
    OP_MATMUL: ('matmul', (), 2, 1, {2}),
    OP_MUL: ('scalar_mul', (), 2, 1, {2, 3, 4}) # multiply a tensor (first argument) with a scalar (0-D tensor)
}

for d in operator_data.values():
    for i in range(d[3]):
        name = '{}_{}'.format(d[0], i)
        globals()[name] = z3.Function(name, *( len(d[1]) * [P] + d[2] * [T] + [T]))

x,y,z,w, one = z3.Consts('x y z w one', T)
sx, sy, kx, ky, pad, acti, ax = z3.Consts('sx sy kx ky pad acti ax', P)

N = [1,2,3,4] # change this to control number of combinations for symbolic validation, e.g., [1,2], [1,3] or [3,4] each provide a reasonable experiment to run and go for coffee (assuming 8 cores)
D = [1,3]

# list of axioms with list of possible values for verify_axioms.py. possible values are actual values for parameters, and shapes for tensors
axioms = [

    # ewadd and ewmul are associative, commutative and distributive

    # ewadd is associative
    (ForAll([x,y,z], ewadd_0(x,ewadd_0(y, z)) == ewadd_0(ewadd_0(x,y),z)),
     lambda : [(s,s,s) for dim in [2,3,4] for s in product(N, repeat=dim)] ),

    # ewadd is commutative
    (ForAll([x,y], ewadd_0(x,y) == ewadd_0(y, x)),
     lambda : [(s,s) for dim in [2,3,4] for s in product(N, repeat=dim)] ),

    # ewmul is associative
    (ForAll([x,y,z], ewmul_0(x,ewmul_0(y, z)) == ewmul_0(ewmul_0(x,y),z)),
     lambda :[(s,s,s) for dim in [2,3,4] for s in product(N, repeat=dim)] ),

    # ewmul is commutative
    (ForAll([x,y], ewmul_0(x,y) == ewmul_0(y, x)),
     lambda : [(s,s) for dim in [2,3,4] for s in product(N, repeat=dim)] ),

    # ewadd and ewmul are distributive
    (ForAll([x,y,z], ewmul_0(ewadd_0(x,y), z) == ewadd_0(ewmul_0(x, z), ewmul_0(y, z))),
     lambda : [(s,s,s) for dim in [2,3,4] for s in product(N, repeat=dim)] ),

    # scalar_mul axioms

    # scalar_mul is associative
    (ForAll([x,y,w], scalar_mul_0(scalar_mul_0(x,y),w) == scalar_mul_0(x,scalar_mul_0(y,w))),
     lambda : [(s,(),()) for dim in [2,3,4] for s in product(N, repeat=dim)] ),

    # scalar_mul distributes over ewadd
    (ForAll([x,y,w], scalar_mul_0(ewadd_0(x,y),w) == ewadd_0(scalar_mul_0(x,w), scalar_mul_0(y,w))),
     lambda : [(s,s,()) for dim in [2,3,4] for s in product(N, repeat=dim)] ),

    # scalar_mul commutes with ewmul
    (ForAll([x,y,w], scalar_mul_0(ewmul_0(x,y),w) == ewmul_0(x,scalar_mul_0(y,w))),
     lambda : [(s,s,()) for dim in [2,3,4] for s in product(N, repeat=dim)] ),

    # scalar_mul commutes with transpose
    (ForAll([x, w], scalar_mul_0(transpose_0(x), w) == transpose_0(scalar_mul_0(x, w))),
     lambda : [(s,()) for s in product(N, repeat=2)] ),

    # scalar_mul commutes with matmul (note that the other is obtained using transpose)
    (ForAll([x,y,w], scalar_mul_0(matmul_0(x,y),w) == matmul_0(x,scalar_mul_0(y,w))),
     lambda : [((n1,n2),(n2, n3),()) for n1,n2,n3 in product(N,repeat=3) ]),

    # scalar_mul and concat
    (ForAll([ax,x,y,w], scalar_mul_0(concat_0(ax, x, y), w) == concat_0(ax, scalar_mul_0(x, w), scalar_mul_0(y, w))),
     lambda : [(ax,s1,s2,())
               for dim in [2,3,4]
               for s1 in product(N, repeat=dim)
               for s2 in product(N, repeat=dim)
               for ax in range(dim)
               if all(s1[i] == s2[i] or i == ax for i in range(dim))
     ]),

    # scalar_mul and conv2d

    (ForAll([sx,sy,pad,acti,x,y,w], conv2d_0(sx,sy,pad,acti,scalar_mul_0(x,w),y) == conv2d_0(sx,sy,pad,acti,x,scalar_mul_0(y,w))),
     lambda : [(sx, sy, pad, acti, (n,c,h,w), (c1,c,d1,d2), ())
               for sx in [1,2]
               for sy in [1,2]
               for pad in [PD_MODE_SAME, PD_MODE_VALID]
               for acti in [AC_MODE_NONE, AC_MODE_RELU]
               for n,c,h,w,c1 in product(N,repeat=5)
               for d1 in D
               for d2 in D
               if (h >= d1 and w >= d2) or pad == PD_MODE_SAME
     ]),

    (ForAll([sx,sy,pad,x,y,w], scalar_mul_0(conv2d_0(sx,sy,pad,AC_MODE_NONE,x,y),w) == conv2d_0(sx,sy,pad,AC_MODE_NONE,scalar_mul_0(x,w),y)),
     lambda : [(sx, sy, pad, (n,c,h,w), (c1,c,d1,d2), ())
               for sx in [1,2]
               for sy in [1,2]
               for pad in [PD_MODE_SAME, PD_MODE_VALID]
               for n,c,h,w,c1 in product(N,repeat=5)
               for d1 in D
               for d2 in D
               if (h >= d1 and w >= d2) or pad == PD_MODE_SAME
     ]),

    # relu axioms

    # doesn't seem like this is needed
    # relu is idempotent
    #(ForAll([x], relu_0(x) == relu_0(relu_0(x))),
    # lambda : [(s,) for dim in [2,3,4] for s in product(N, repeat=dim)] ),

    # relu and conv2d
    (ForAll([sx, sy, pad, x, y], relu_0(conv2d_0(sx, sy, pad, AC_MODE_NONE, x, y)) == conv2d_0(sx, sy, pad, AC_MODE_RELU, x, y)),
     lambda : [(sx, sy, pad, (n,c,h,w), (c1,c,d1,d2))
               for sx in [1,2]
               for sy in [1,2]
               for pad in [PD_MODE_SAME, PD_MODE_VALID]
               for n,c,h,w,c1 in product(N,repeat=5)
               for d1 in D
               for d2 in D
               if (h >= d1 and w >= d2) or pad == PD_MODE_SAME
     ]),

    # relu and concat
    (ForAll([ax, x, y], relu_0(concat_0(ax, x, y)) == concat_0(ax, relu_0(x), relu_0(y))),
     lambda : [(ax,s1,s2)
               for dim in [2,3,4]
               for s1 in product(N, repeat=dim)
               for s2 in product(N, repeat=dim)
               for ax in range(dim)
               if all(s1[i] == s2[i] or i == ax for i in range(dim))
     ]),

    # relu and transpose commute
    (ForAll([x], relu_0(transpose_0(x)) == transpose_0(relu_0(x))),
     lambda : [(s,) for s in product(N, repeat=2)] ),

   # conv2d axioms
    (ForAll([sx, sy, pad, x, y, z], conv2d_0(sx, sy, pad, AC_MODE_NONE, x, ewadd_0(y, z)) == ewadd_0(conv2d_0(sx, sy, pad, AC_MODE_NONE, x, y), conv2d_0(sx, sy, pad, AC_MODE_NONE, x, z))),
     lambda : [(sx, sy, pad, (n,c,h,w), (c1,c,d1,d2), (c1,c,d1,d2))
               for sx in [1,2]
               for sy in [1,2]
               for pad in [PD_MODE_SAME, PD_MODE_VALID]
               for n,c,h,w,c1 in product(N,repeat=5)
               for d1 in D
               for d2 in D
               if (h >= d1 and w >= d2) or pad == PD_MODE_SAME
               # if (
               #     1 + (h + 2 * vpx - d1) / sx > 0 and
               #     1 + (w + 2 * vpy - d2) / sy > 0 and
               #     (vpx != 1 or d1 != 1) and
               #     (vpy != 1 or d2 != 1)
               # )
     ]),

    (ForAll([sx, sy, pad, x, y, z], conv2d_0(sx, sy, pad, AC_MODE_NONE, ewadd_0(x, y), z) == ewadd_0(conv2d_0(sx, sy, pad, AC_MODE_NONE, x, z), conv2d_0(sx, sy, pad, AC_MODE_NONE, y, z))),
     lambda : [(sx, sy, pad, (n,c,h,w), (n,c,h,w), (c1,c,d1,d2))
               for sx in [1,2]
               for sy in [1,2]
               for pad in [PD_MODE_SAME, PD_MODE_VALID]
               for n,c,h,w,c1 in product(N,repeat=5)
               for d1 in D
               for d2 in D
               if (h >= d1 and w >= d2) or pad == PD_MODE_SAME
     ]),

    # a special axiom for conv and matmul

    (ForAll([sx, sy, pad, x, y, z, w], ewadd_0(conv2d_0(sx, sy, pad, AC_MODE_NONE, x, y), conv2d_0(sx, sy, pad, AC_MODE_NONE, z, w)) == conv2d_0(sx, sy, pad, AC_MODE_NONE, concat_0(1, x, z), concat_0(1, y, w))),
     lambda : [(sx, sy, pad, (n,c1,h,w), (co,c1,d1,d2), (n,c2,h,w), (co,c2,d1,d2))
               for sx in [1,2]
               for sy in [1,2]
               for pad in [PD_MODE_SAME, PD_MODE_VALID]
               for n,c1,c2,co,h,w in product(N,repeat=6)
               for d1 in D
               for d2 in D
               if (h >= d1 and w >= d2) or pad == PD_MODE_SAME
     ]),

    # concat axioms

    # matmul and concat
    (ForAll([x, y, z, w], ewadd_0(matmul_0(x, y), matmul_0(z, w)) == matmul_0(concat_0(1, x, z), concat_0(0, y, w))),
     lambda :[((n1,n2),(n2, n3),(n1,n4),(n4,n3)) for n1,n2,n3,n4 in product(N,repeat=4)]),


    (ForAll([ax, x, y, z, w], concat_0(ax, ewadd_0(x, y), ewadd_0(z, w)) == ewadd_0(concat_0(ax, x, z), concat_0(ax, y, w))),
     lambda : [(ax,s1,s1,s2,s2)
               for dim in [2,3,4]
               for s1 in product(N, repeat=dim)
               for s2 in product(N, repeat=dim)
               for ax in range(dim)
               if all(s1[i] == s2[i] or i == ax for i in range(dim))
     ]),

    (ForAll([ax, x, y, z, w], concat_0(ax, ewmul_0(x, y), ewmul_0(z, w)) == ewmul_0(concat_0(ax, x, z), concat_0(ax, y, w))),
     lambda : [(ax,s1,s1,s2,s2)
               for dim in [2,3,4]
               for s1 in product(N, repeat=dim)
               for s2 in product(N, repeat=dim)
               for ax in range(dim)
               if all(s1[i] == s2[i] or i == ax for i in range(dim))
     ]),

    (ForAll([sx, sy, pad, acti, x, y, z], concat_0(0, conv2d_0(sx, sy, pad, acti, x, z), conv2d_0(sx, sy, pad, acti, y, z)) == conv2d_0(sx, sy, pad, acti, concat_0(0, x, y), z)),
     lambda : [(sx, sy, pad, acti, (n1,c,h,w), (n2,c,h,w), (c1,c,d1,d2))
               for sx in [1,2]
               for sy in [1,2]
               for pad in [PD_MODE_SAME, PD_MODE_VALID]
               for acti in [AC_MODE_NONE, AC_MODE_RELU]
               for n1,n2,c,h,w,c1 in product(N,repeat=6)
               for d1 in D
               for d2 in D
               if (h >= d1 and w >= d2) or pad == PD_MODE_SAME
     ]),

    (ForAll([sx, sy, pad, acti, x, y, z], concat_0(1, conv2d_0(sx, sy, pad, acti, x, y), conv2d_0(sx, sy, pad, acti, x, z)) == conv2d_0(sx, sy, pad, acti, x, concat_0(0, y, z))),
     lambda :[(sx, sy, pad, acti, (n,c,h,w), (c1,c,d1,d2), (c2,c,d1,d2))
              for sx in [1,2]
              for sy in [1,2]
              for pad in [PD_MODE_SAME, PD_MODE_VALID]
              for acti in [AC_MODE_NONE, AC_MODE_RELU]
              for n,c,h,w,c1,c2 in product(N,repeat=6)
              for d1 in D
              for d2 in D
              if (h >= d1 and w >= d2) or pad == PD_MODE_SAME
     ]),

    # matmul
    (ForAll([x, y, z], matmul_0(x, matmul_0(y, z)) == matmul_0(matmul_0(x, y), z)),
     lambda :
     # TODO: 3D matmul: [((n1, n2, n3), (n1, n3, n4), (n1, n4, n5)) for n1,n2,n3,n4,n5 in product(N,repeat=5) ] +
     [((n1, n2), (n2, n3), (n3, n4)) for n1, n2, n3, n4 in product(N, repeat=4)]
    ),

    # split and concat
    (ForAll([ax, x, y], split_0(ax, concat_0(ax, x, y)) == x),
     lambda : [(ax, s1, s2)
               for dim in [2,3,4]
               for s1 in product(N, repeat=dim)
               for s2 in product(N, repeat=dim)
               for ax in range(dim)
               if all(s1[i] == s2[i] or i == ax for i in range(dim))
     ]),

    (ForAll([ax, x, y], split_1(ax, concat_0(ax, x, y)) == y),
     lambda : [(ax, s1, s2)
               for dim in [2,3,4]
               for s1 in product(N, repeat=dim)
               for s2 in product(N, repeat=dim)
               for ax in range(dim)
               if all(s1[i] == s2[i] or i == ax for i in range(dim))
     ]),

    # split, concat, and matmul

    (ForAll([x, y, z], matmul_0(x, concat_0(1, y, z)) == concat_0(1, matmul_0(x, y), matmul_0(x, z))),
     lambda : [((n1, n2), (n2, n3), (n2, n4)) for n1,n2,n3,n4 in product(N,repeat=4) ]),

    # matmul and ewadd

    (ForAll([x, y, z], matmul_0(x, ewadd_0(y, z)) == ewadd_0(matmul_0(x, y), matmul_0(x, z))),
     lambda : [((n1,n2), (n2,n3), (n2,n3)) for n1,n2,n3 in product(N,repeat=3) ]),

    # transpose

    (ForAll([x], transpose_0(transpose_0(x)) == x),
     lambda : [((n1, n2),) for n1,n2 in product(N,repeat=2)]),

    (ForAll([x,y], transpose_0(matmul_0(x,y)) == matmul_0(transpose_0(y), transpose_0(x))  ),
     lambda : [((n1, n2),(n2,n3)) for n1,n2,n3 in product(N,repeat=3)]),

    (ForAll([x,y], transpose_0(concat_0(0, x, y)) == concat_0(1, transpose_0(x), transpose_0(y))),
     lambda : [((n1, n2), (n3,n2)) for n1,n2,n3 in product(N,repeat=3)]),

    # concat geometry

    (ForAll([x,y,z,w], concat_0(0, concat_0(1, x, y), concat_0(1, z, w)) == concat_0(1, concat_0(0, x, z), concat_0(0, y, w))),
     lambda : [(s1, s2, s3, s4)
               for dim in [2,3,4]
               for s1 in product(N, repeat=dim)
               for s2 in (tuple(s1[i] if i != 1 else n2 for i in range(dim)) for n2 in N)
               for s3 in (tuple(s1[i] if i != 0 else n3 for i in range(dim)) for n3 in N)
               for s4 in [tuple(s2[i] if i != 0 else s3[i] for i in range(dim))]
               if (
                       s1[1] + s2[1] == s3[1] + s4[1] and
                       s1[0] + s3[0] == s2[0] + s4[0]
               )
     ]),

    # transpose and elementwise opertions

    (ForAll([x,y], transpose_0(ewadd_0(x,y)) == ewadd_0(transpose_0(x), transpose_0(y))),
     lambda : [((n1, n2), (n1,n2)) for n1,n2 in product(N,repeat=2)]),

    (ForAll([x,y], transpose_0(ewmul_0(x,y)) == ewmul_0(transpose_0(x), transpose_0(y))),
     lambda :[((n1, n2), (n1,n2)) for n1,n2 in product(N,repeat=2)]),

    # pooling and concat

    (ForAll([kx, ky, sx, sy, pad, x, y], concat_0(1, pool2d_avg_0(kx, ky, sx, sy, pad, x), pool2d_avg_0(kx, ky, sx, sy, pad, y)) == pool2d_avg_0(kx, ky, sx, sy, pad, concat_0(1, x, y))),
     lambda : [(d1, d2, sx, sy, pad, s1, s2)
               for d1 in D
               for d2 in D
               for sx in [1,2]
               for sy in [1,2]
               for pad in [PD_MODE_SAME, PD_MODE_VALID]
               for s1 in product(N, repeat=4)
               for s2 in product(N, repeat=4)
               if (all(s1[i] == s2[i] or i == 1 for i in range(4)) and
                   ((s1[2] >= d1 and s1[3] >= d2) or pad == PD_MODE_SAME) and
                   ((s2[2] >= d1 and s2[3] >= d2) or pad == PD_MODE_SAME))
     ]),

    (ForAll([kx, ky, sx, sy, pad, x, y], concat_0(0, pool2d_max_0(kx, ky, sx, sy, pad, x), pool2d_max_0(kx, ky, sx, sy, pad, y)) == pool2d_max_0(kx, ky, sx, sy, pad, concat_0(0, x, y))),
     lambda : [(d1, d2, sx, sy, pad, s1, s2)
               for d1 in D
               for d2 in D
               for sx in [1,2]
               for sy in [1,2]
               for pad in [PD_MODE_SAME, PD_MODE_VALID]
               for s1 in product(N, repeat=4)
               for s2 in product(N, repeat=4)
               if (all(s1[i] == s2[i] or i == 0 for i in range(4)) and
                   ((s1[2] >= d1 and s1[3] >= d2) or pad == PD_MODE_SAME) and
                   ((s2[2] >= d1 and s2[3] >= d2) or pad == PD_MODE_SAME))
     ]),

    (ForAll([kx, ky, sx, sy, pad, x, y], concat_0(1, pool2d_max_0(kx, ky, sx, sy, pad, x), pool2d_max_0(kx, ky, sx, sy, pad, y)) == pool2d_max_0(kx, ky, sx, sy, pad, concat_0(1, x, y))),
     lambda : [(d1, d2, sx, sy, pad, s1, s2)
               for d1 in D
               for d2 in D
               for sx in [1,2]
               for sy in [1,2]
               for pad in [PD_MODE_SAME, PD_MODE_VALID]
               for s1 in product(N, repeat=4)
               for s2 in product(N, repeat=4)
               if (all(s1[i] == s2[i] or i == 1 for i in range(4)) and
                   ((s1[2] >= d1 and s1[3] >= d2) or pad == PD_MODE_SAME) and
                   ((s2[2] >= d1 and s2[3] >= d2) or pad == PD_MODE_SAME))
     ]),

    # property of const_pool
    (ForAll([sx, sy, pad, x, kx, ky], conv2d_0(sx, sy, pad, AC_MODE_NONE, x, const_pool_0(kx, ky)) == pool2d_avg_0(kx, ky, sx, sy, pad, x)),
     lambda : [(sx, sy, pad, (n,c,h,w), d1, d2)
               for sx in [1,2]
               for sy in [1,2]
               for pad in [PD_MODE_SAME, PD_MODE_VALID]
               for n,c,h,w in product(N,repeat=4)
               for d1 in D
               for d2 in D
               if (h >= d1 and w >= d2) or pad == PD_MODE_SAME
     ]),

    # conv2d and const_iconv
    (ForAll([kx, ky, x], conv2d_0(1, 1, PD_MODE_SAME, AC_MODE_NONE, x, const_iconv_0(kx, ky)) == x),
     lambda : [(d1, d2, (n,c,h,w))
               for d1 in D
               for d2 in D
               for n,c,h,w in product(N,repeat=4)
               if (h >= d1 and w >= d2) or pad == PD_MODE_SAME
     ]),

    # matmul and const_imm
    (ForAll([x], matmul_0(x, const_imm_0()) == x),
     lambda : [((n1,n2),) for n1,n2 in product(N, repeat=2) ]),

    # ewmul and const_one
    (ForAll([x], ewmul_0(x, const_one_0()) == x),
     lambda :[(s,) for dim in [2,3,4] for s in product(N, repeat=dim)] ),

    # # const_iconv and const_pool
    # (ForAll([kx, ky], pool2d_avg_0(kx, ky, 1, 1, PD_MODE_SAME, const_iconv_0(kx, ky)) == const_pool_0(kx, ky)),
    #  lambda : [(d1, d2)
    #            for d1 in D
    #            for d2 in D
    #  ]),

    # enlarge axioms
    (ForAll([sx, sy, acti, kx, ky, x, y], conv2d_0(sx, sy, PD_MODE_SAME, acti, x, y) == conv2d_0(sx, sy, PD_MODE_SAME, acti, x, enlarge_0(kx, ky, y))),
     lambda : [(sx, sy, acti, kx, ky, (n,c,h,w), (c1,c,d1,d2))
               for sx in [1,2]
               for sy in [1,2]
               for acti in [AC_MODE_NONE, AC_MODE_RELU]
               for kx, ky, d1, d2 in product(D, repeat=4)
               for n,c,h,w,c1 in product(N,repeat=5)
     ]),

    #(ForAll([kx, ky, x], conv2d_0(1, 1, PD_MODE_SAME, AC_MODE_NONE, const_iconv_0(kx, ky), conv2d_0(1, 1, PD_MODE_SAME, AC_MODE_NONE, const_iconv_0(kx, ky), x)) == enlarge_0(kx, ky, x)),
    # None),

    #(ForAll([kx, ky, x], enlarge_0(kx, ky, ewmul_0(x, pool2d_max_0(kx, ky, 1, 1, PD_MODE_SAME, x))) == ewmul_0(enlarge_0(kx, ky, x), pool2d_max_0(kx, ky, 1, 1, PD_MODE_SAME, enlarge_0(kx, ky, x)))),
    # None),

#    (ForAll([kx, ky, x, y], enlarge_0(kx, ky, ewadd_0(x, y)) == ewadd_0(enlarge_0(kx, ky, x), enlarge_0(kx, ky, y))),
#     lambda : [(kx, ky, s, s)
#               for kx, ky in product(D, repeat=2)
#               for s in product(N, repeat=4)
#     ]),
#
#    (ForAll([kx, ky, x, y], enlarge_0(kx, ky, ewmul_0(x, y)) == ewmul_0(enlarge_0(kx, ky, x), enlarge_0(kx, ky, y))),
#     lambda : [(kx, ky, s, s)
#               for kx, ky in product(D, repeat=2)
#               for s in product(N, repeat=4)
#     ]),
#
#    (ForAll([kx, ky, x, w], enlarge_0(kx, ky, scalar_mul_0(x, w)) == scalar_mul_0(enlarge_0(kx, ky, x), w)),
#     lambda : [(kx, ky, s, ())
#               for kx, ky in product(D, repeat=2)
#               for s in product(N, repeat=4)
#     ]),
#
#    (ForAll([kx, ky, x, y], enlarge_0(kx, ky, concat_0(0, x, y)) == concat_0(0, enlarge_0(kx, ky, x), enlarge_0(kx, ky, y))),
#     lambda : [(kx, ky, s1, s2)
#               for kx, ky in product(D, repeat=2)
#               for s1 in product(N, repeat=4)
#               for s2 in product(N, repeat=4)
#               if all(s1[i] == s2[i] or i == 0 for i in range(4))
#     ]),
#
#    (ForAll([kx, ky, x, y], enlarge_0(kx, ky, concat_0(1, x, y)) == concat_0(1, enlarge_0(kx, ky, x), enlarge_0(kx, ky, y))),
#     lambda : [(kx, ky, s1, s2)
#               for kx, ky in product(D, repeat=2)
#               for s1 in product(N, repeat=4)
#               for s2 in product(N, repeat=4)
#               if all(s1[i] == s2[i] or i == 1 for i in range(4))
#     ]),
#
#    (ForAll([kx, ky, x], enlarge_0(kx, ky, relu_0(x)) == relu_0(enlarge_0(kx, ky, x))),
#     lambda : [(kx, ky, s)
#               for kx, ky in product(D, repeat=2)
#               for s in product(N, repeat=4)
#     ]),
#
    # concat is associative (wrong axiom - makes many others redundant)
    # (ForAll([ax, x, y, z], concat_0(ax, x, concat_0(ax, y,z)) == concat_0(ax, concat_0(ax, x, y), z)),
    #  lambda : [(ax, s1, s2, s3)
    #            for dim in [2,3,4]
    #            for s1 in product(N, repeat=dim)
    #            for s2 in product(N, repeat=dim)
    #            for s3 in product(N, repeat=dim)
    #            for ax in range(dim)
    #            if all(s1[i] == s2[i] == s3[i] or i == ax for i in range(dim))
    #  ]),

    # grouped convolution (wrong axiom - caught with N=[1,3])
    # (ForAll([sx, sy, pad, acti, x, y, z, w], concat_0(1, conv2d_0(sx, sy, pad, acti, x, y), conv2d_0(sx, sy, pad, acti, z, w)) == conv2d_0(sx, sy, pad, acti, concat_0(1, x, z), concat_0(0, y, w))),
    #  lambda :[(sx, sy, pad, acti, (n,cx,h,w), (c1y,c2,d1,d2), (n,cz,h,w), (c1w,c2,d1,d2))
    #           for sx in [1,2]
    #           for sy in [1,2]
    #           for pad in [PD_MODE_SAME, PD_MODE_VALID]
    #           for acti in [AC_MODE_NONE, AC_MODE_RELU]
    #           for n,cx,h,w,c1y,c2,cz,c1w in product(N,repeat=8)
    #           for d1 in D
    #           for d2 in D
    #           if all([
    #                   h >= d1,
    #                   w >= d2,
    #                   cx % c2 == 0,
    #                   cz % c2 == 0,
    #                   (cx // c2) > 0 and c1y % (cx // c2) == 0,
    #                   (cz // c2) > 0 and c1w % (cz // c2) == 0,
    #                   ((cx + cz) // c2) > 0 and (c1w + c1y) % ((cx + cz) // c2) == 0,
    #           ])
    #  ]),

]

# lemmas are implied by the axioms (which is checked using Z3), and
# then also assumed to help with verification of transformations
lemmas = [
    # lemmas about const_imm
    transpose_0(const_imm_0()) == const_imm_0(),
    ForAll([x], matmul_0(const_imm_0(), x) == x),

    # lemma about pool2d_avg and concat along axis 0
    ForAll([kx, ky, sx, sy, pad, x, y], concat_0(0, pool2d_avg_0(kx, ky, sx, sy, pad, x), pool2d_avg_0(kx, ky, sx, sy, pad, y)) == pool2d_avg_0(kx, ky, sx, sy, pad, concat_0(0, x, y))),

    # other implied properties not used as lemmas for now
    # ForAll([x, y, z], matmul_0(ewadd_0(x, y), z) == ewadd_0(matmul_0(x, z), matmul_0(y, z))),
    # ForAll([x,y], transpose_0(concat_0(1, x, y)) == concat_0(0, transpose_0(x), transpose_0(y))),
    # ForAll([x, y, z], matmul_0(concat_0(0, x, y), z) == concat_0(0, matmul_0(x, z), matmul_0(y, z))),
]

def to_z3(tensor, ops):
    if tensor.opId < 0:
        # an input tensor
        return z3.Const('input_{}'.format(-tensor.opId), T)
    else:
        op = ops[tensor.opId]
        d = operator_data[op.type]
        #print(op.type, d)
        assert tensor.tsId <= d[3]
        f = globals()['{}_{}'.format(d[0], tensor.tsId)]
        params = {}
        for p in op.para:
            params[p.key] = p.value
        args = []
        for k, rng in d[1]:
            v = params[k]
            if (v not in rng):
                print(k, v, rng)
                assert False
            assert v in rng
            assert type(v) is int
            args.append(v)
        args += [to_z3(x, ops) for x in op.input]
        return f(*args)

if __name__ == '__main__':

    if len(sys.argv) != 2:
        print("Usage:", sys.argv[0], "<graph substitutions file>")
        sys.exit(-1)

    import rules_pb2
    rules = rules_pb2.RuleCollection()
    rules.ParseFromString(open(sys.argv[1], "rb").read())

    # print("Axioms:\n{}".format([a for a, b in axioms]))

    blacklist = {
        # some substitutions that are known to be incorrect and should be skipped
        #'nasnet_subst.pb': [166, 167, 186, 187, 222, 223, 224, 225, 226, 227, 283, 284, 290, 291, 298, 299],
        #'graph_subst.pb': [178, 179, 387, 405, 429, 443, 444, 485, 486, 487, 488, 489, 490, 548, 549, 555, 556, 563, 564],
        #'graph_subst.pb': [201, 202, 209, 247, 259, 264, 265, 316, 527, 528, 529, 532, 573, 584, 585, 586, 607, 627, 628, 670, 671, 672, 673, 674, 675, 740, 741, 751, 752, 761, 762],
        #'graph_subst.pb': [202, 209, 254, 255, 260, 307, 308, 518, 536, 560, 580, 581, 620, 621, 622, 623, 624, 625, 681, 682, 688, 689, 695, 696, 697],
        'graph_subst.pb': [201, 202, 209, 254, 255, 260, 307, 308, 518, 536, 560, 580, 581, 620, 621, 622, 623, 624, 625, 681, 682, 688, 689, 695, 696, 697],
        'new_graph_subst.pb': [],
    }[os.path.basename(sys.argv[1])]

    for i, rule in enumerate(rules.rule):
        if i in blacklist:
            continue
        # print("Verifying rule: {} with {} outputs\n".format(rule, len(rule.mappedOutput)))
        for output in rule.mappedOutput:
            # print("Verifing output: {}".format(output))
            src_tensor = rules_pb2.Tensor(opId=output.srcOpId, tsId=output.srcTsId)
            dst_tensor = rules_pb2.Tensor(opId=output.dstOpId, tsId=output.dstTsId)
            src = to_z3(src_tensor, rule.srcOp)
            dst = to_z3(dst_tensor, rule.dstOp)
            print("Z3 expression:\n{}\n".format(src == dst))
            s = z3.Solver()
            for a, b in axioms:
                s.add(a)
            for lem in lemmas:
                s.add(lem)
            s.add(src != dst)
            print("Checking... ({})".format(i))
            if s.check() == z3.unsat:
                print("Proved!")
            else:
                assert False
        print('\n' + '='*80)
    print("Done")
