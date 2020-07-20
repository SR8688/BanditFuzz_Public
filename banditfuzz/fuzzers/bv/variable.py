from ..variable import Variable


class BitVec_Variable(Variable):
    def __init__(self, name, num):  # num is length
        self.sort = 'bv'
        self.name, self.num = name, num

    def declare(self):
        return f'(declare-const {self.name} (_ BitVec {self.num}))'

    def __str__(self):
        return self.name
