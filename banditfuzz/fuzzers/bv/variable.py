from ..variable import Variable

# pylint: disable=invalid-name


class BV_Variable(Variable):
    """ Defines a bitvector variable """

    def __init__(self, name, width):
        self.sort = 'BitVec'
        self.name, self.width = name, width

    def declare(self):
        """ Declares the variable in SMT-lang """
        return f'(declare-const {self.name} (_ BitVec {self.width}))'

    def __str__(self):
        return self.name
