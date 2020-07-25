import numpy as np
from ...parser import args as settings


MAX_NUM_BITS = 32  # hardcoded max bv len


def rng():
    """ Returns random bit as str """
    return np.random.choice(['0', '1'])


class BVLiteral:  # pylint: disable=too-few-public-methods
    """ Class to implement the bitvector literal """

    def __init__(self):
        self.sort = 'bv'
        # define constant

        if settings._bin:  # binary
            length_multiplier = 1
        elif settings._hex:  # hexadecimal
            length_multiplier = 4
        # make length

        self.val = '(bv '
        self.val += '#b'
        for _ in range(MAX_NUM_BITS*length_multiplier):
            self.val += rng()

        self.val += ')'

    def __str__(self):
        return self.val
    __repr__ = __str__
