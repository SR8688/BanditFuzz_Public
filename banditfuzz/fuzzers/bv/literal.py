import random
from ...parser import args as settings


class BVLiteral:
    def __init__(self):
        # make value
        def rng(): return np.random.choice(['0', '1'])
        self.length = settings._bitveclen
        import numpy as np
        self.sort = 'fp'

        if settings._0b:
            self.length *= 1
        elif settings._0x:
            self.length *= 4

        self.val = '#b'
        for _ in range(self.length):
            self.val += rng()

    def __str__(self):
        return self.val
    __repr__ = __str__
