from ..variable import Variable


class BV_Variable(Variable):
    def __init__(self, name, width):
        self.sort = 'BitVec'
        self.name, self.width = name, width

    def declare(self):
        return f'(declare-const {self.name} (_ BitVec {self.width}))'

    def __str__(self):
        return self.name
