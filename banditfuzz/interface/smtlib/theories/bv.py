from banditfuzz.interface.smtlib.script import SExpr

BV_ALIAS = {
    '#bX': SExpr("_", "BitVec", 1),  # second number is length multiplier
    '#xX': SExpr("_", "BitVec", 4),  # hex multiply length by 4
    '#oX': SExpr("_", "BitVec", 3)  # octal multiply length by 3
}

BV_SORTS = {
    'BitVec': ["Num"]  # Num is a number referring to the size of the bitvec
}

BV_FUNCS = {
    'concat': ['BitVec', 'BitVec', 'BitVec'],
    'extract': ['Num', 'Num', 'BitVec', 'BitVec'],
    'bvnot': ['BitVec', 'BitVec'],
    'bvneg': ['BitVec', 'BitVec'],
    'bvand': ['BitVec', 'BitVec', 'BitVec'],
    'bvor': ['BitVec', 'BitVec', 'BitVec'],
    'bvadd': ['BitVec', 'BitVec', 'BitVec'],
    'bvmul': ['BitVec', 'BitVec', 'BitVec'],
    'bvudiv': ['BitVec', 'BitVec', 'BitVec'],
    'bvurem': ['BitVec', 'BitVec', 'BitVec'],
    'bvshl': ['BitVec', 'BitVec', 'BitVec'],
    'bvlshr': ['BitVec', 'BitVec', 'BitVec'],
    'bvult': ['BitVec', 'BitVec', 'Bool']
}


def mk_literal(n_bits):
    return SExpr("bv", "#b%s" % n_bits)


def mk_concat(bv):
    return SExpr("concat", bv)


def mk_extract(idx1, idx2, bv):
    return SExpr("extract", idx1, idx2, bv)


def mk_bvnot(bv):
    return SExpr("bvnot", bv)


def mk_bvneg(bv):
    return SExpr("bvneg", bv)


def mk_bvand(bv1, bv2):
    return SExpr("bvand", bv1, bv2)


def mk_bvor(bv1, bv2):
    return SExpr("bvor", bv1, bv2)


def mk_bvadd(bv1, bv2):
    return SExpr("bvadd", bv1, bv2)


def mk_bvmul(bv1, bv2):
    return SExpr("bvmul", bv1, bv2)


def mk_bvudiv(bv1, bv2):
    return SExpr("bvudiv", bv1, bv2)


def mk_bvurem(bv1, bv2):
    return SExpr("bvurem", bv1, bv2)


def mk_bvshl(bv1, bv2):
    return SExpr("bvshl", bv1, bv2)


def mk_bvlshr(bv1, bv2):
    return SExpr("bvlshr", bv1, bv2)


def mk_bvult(bv1, bv2):
    return SExpr("bvult", bv1, bv2)

    # def mk_not(expr):
    #     return SExpr("not", expr)

    # def mk_and(left, right):
    #     return SExpr("and", left, right)

    # def mk_or(left, right):
    #     return SExpr("or", left, right)

    # CORE_MKS = {
    #     'not': mk_not,
    #     'and': mk_and,
    #     'or': mk_or
    # }
