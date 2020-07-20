class BVEXTRACT:  # extracts subvec
    def __init__(self):
        self.arity = 3
        self.sort = 'bv'
        self.sig = ['Num',
                    'Num',
                    'bv',
                    'bv']
        self.chainable = False  # ?

    def __str__(self):
        return "bv.extract"
    __repr__ = __str__


class BVCONCAT:
    def __init__(self):
        self.arity = 2
        self.sort = 'bv'
        self.sig = ['bv',
                    'bv',
                    'bv']
        self.chainable = False  # ?

    def __str__(self):
        return "bv.concat"
    __repr__ = __str__


class BVNOT:
    def __init__(self):
        self.arity = 1
        self.sort = 'bv'
        self.sig = ['bv',
                    'bv']
        self.chainable = False  # ?

    def __str__(self):
        return "bv.not"
    __repr__ = __str__


class BVAND:
    def __init__(self):
        self.arity = 2
        self.sort = 'bv'
        self.sig = ['bv',
                    'bv',
                    'bv']
        self.chainable = False  # ?

    def __str__(self):
        return "bv.and"
    __repr__ = __str__


class BVOR:
    def __init__(self):
        self.arity = 2
        self.sort = 'bv'
        self.sig = ['bv',
                    'bv',
                    'bv']
        self.chainable = False  # ?

    def __str__(self):
        return "bv.or"
    __repr__ = __str__


class BVNEG:
    def __init__(self):
        self.arity = 1
        self.sort = 'bv'
        self.sig = ['bv',
                    'bv']
        self.chainable = False  # ?

    def __str__(self):
        return "bv.neg"
    __repr__ = __str__


class BVADD:
    def __init__(self):
        self.arity = 2
        self.sort = 'bv'
        self.sig = ['bv',
                    'bv',
                    'bv']
        self.chainable = False  # ?

    def __str__(self):
        return "bv.add"
    __repr__ = __str__


class BVMUL:
    def __init__(self):
        self.arity = 2
        self.sort = 'bv'
        self.sig = ['bv',
                    'bv',
                    'bv']
        self.chainable = False  # ?

    def __str__(self):
        return "bv.mul"
    __repr__ = __str__


class BVUDIV:
    def __init__(self):
        self.arity = 2
        self.sort = 'bv'
        self.sig = ['bv',
                    'bv',
                    'bv']
        self.chainable = False  # ?

    def __str__(self):
        return "bv.udiv"
    __repr__ = __str__


class BVUREM:
    def __init__(self):
        self.arity = 2
        self.sort = 'bv'
        self.sig = ['bv',
                    'bv',
                    'bv']
        self.chainable = False  # ?

    def __str__(self):
        return "bv.urem"
    __repr__ = __str__


class BVSHL:
    def __init__(self):
        self.arity = 2
        self.sort = 'bv'
        self.sig = ['bv',
                    'bv',
                    'bv']
        self.chainable = False  # ?

    def __str__(self):
        return "bv.shl"
    __repr__ = __str__


class BVSHR:
    def __init__(self):
        self.arity = 2
        self.sort = 'bv'
        self.sig = ['bv',
                    'bv',
                    'bv']
        self.chainable = False  # ?

    def __str__(self):
        return "bv.shr"
    __repr__ = __str__


class BVULT:
    def __init__(self):
        self.arity = 2
        self.sort = 'bool'
        self.sig = ['bv',
                    'bv',
                    'bool']
        self.chainable = False  # ?

    def __str__(self):
        return "bv.ult"
    __repr__ = __str__


class BVNAND:
    def __init__(self):
        self.arity = 2
        self.sort = 'bv'
        self.sig = ['bv',
                    'bv',
                    'bv']
        self.chainable = False  # ?

    def __str__(self):
        return "bv.nand"
    __repr__ = __str__


class BVNOR:
    def __init__(self):
        self.arity = 2
        self.sort = 'bv'
        self.sig = ['bv',
                    'bv',
                    'bv']
        self.chainable = False  # ?

    def __str__(self):
        return "bv.nor"
    __repr__ = __str__


class BVXOR:
    def __init__(self):
        self.arity = 2
        self.sort = 'bv'
        self.sig = ['bv',
                    'bv',
                    'bv']
        self.chainable = False  # ?

    def __str__(self):
        return "bv.xor"
    __repr__ = __str__


class BVXNOR:
    def __init__(self):
        self.arity = 2
        self.sort = 'bv'
        self.sig = ['bv',
                    'bv',
                    'bv']
        self.chainable = False  # ?

    def __str__(self):
        return "bv.xnor"
    __repr__ = __str__


class BVSUB:
    def __init__(self):
        self.arity = 2
        self.sort = 'bv'
        self.sig = ['bv',
                    'bv',
                    'bv']
        self.chainable = False  # ?

    def __str__(self):
        return "bv.sub"
    __repr__ = __str__


class BVSDIV:
    def __init__(self):
        self.arity = 2
        self.sort = 'bv'
        self.sig = ['bv',
                    'bv',
                    'bv']
        self.chainable = False  # ?

    def __str__(self):
        return "bv.sdiv"
    __repr__ = __str__


class BVSREM:
    def __init__(self):
        self.arity = 2
        self.sort = 'bv'
        self.sig = ['bv',
                    'bv',
                    'bv']
        self.chainable = False  # ?

    def __str__(self):
        return "bv.srem"
    __repr__ = __str__


class BVSMOD:
    def __init__(self):
        self.arity = 2
        self.sort = 'bv'
        self.sig = ['bv',
                    'bv',
                    'bv']
        self.chainable = False  # ?

    def __str__(self):
        return "bv.smod"
    __repr__ = __str__


class BVASHR:
    def __init__(self):
        self.arity = 2
        self.sort = 'bv'
        self.sig = ['bv',
                    'bv',
                    'bv']
        self.chainable = False  # ?

    def __str__(self):
        return "bv.ashr"
    __repr__ = __str__


class BVCOMP:
    def __init__(self):
        self.arity = 2
        self.sort = 'bv'
        self.sig = ['bv',
                    'bv',
                    'bv']  # rets |bv|=1 (bool)
        self.chainable = False  # ?

    def __str__(self):
        return "bv.comp"
    __repr__ = __str__
