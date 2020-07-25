from ..variable import Variable


class BitVec_Variable(Variable):
    """ Class to implement the bitvector variable """

    def __init__(self, name, num):  # num is length
        self.sort = 'bv'
        self.name, self.num = name, num

    def declare(self):
        """ Returns a statement of declaration """
        return f'(declare-const {self.name} (_ BitVec {self.num}))'

    def __str__(self):
        return self.name
