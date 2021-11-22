import z3

# Simplify symbol
def ssym(x):
    xx = z3.simplify(x)

    if z3.is_bv(xx):
        if z3.is_bv_value(xx):
            return xx.as_long()

    if z3.is_int(xx):
        if z3.is_int_value(xx):
            return xx.as_long()

    return xx