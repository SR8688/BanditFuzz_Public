from .node import Node

class Benchmark:                ##return type of fuzzer.gen, fuzzer.mutate
    def __init__(self, logic):
        self.logic = logic       # i.e, (set-logic LOGIC)
        self.assertions = []    # List of asserting ASTNodes1
        self._vars = {}
        self.solver_data = {}
    def vars(self,sort=None): 
        if sort: return self._vars[sort]
        else:
            ret = []
            for sort in self._vars: ret += self._vars[sort]
            return ret

    def add_var(self,var):
        if var.sort not in self._vars: self._vars[var.sort] = [] 
        self._vars[var.sort].append(var)

    def check(self, node):
        assert isinstance(node,Node)
        self.assertions.append(node)


    def __str__(self):
        ret = ''
        ret += '(set-info :Origin "This instance was generated by: BanditFuzz-- an RL fuzzer for SMT solvers" )\n'
        ret += '(set-info :Author "Joe Scott, Fed Mora, Vijay Ganesh" )\n'
        ret += '(set-info :Contact "Joe Scott, joseph.scott@uwaterloo.ca")\n'
        for solver in self.solver_data:
            ret += f'; {solver}\n'
            for key in self.solver_data[solver]:
                ret += f'; \t{key} => {self.solver_data[solver][key]}\n'
        ret += f'(set-logic {self.logic})\n'
        for var in self.vars():
            ret += var.declare() + '\n'
        for ast in self.assertions:
            ret += f'(assert {ast})\n'
        ret += '(check-sat)\n'
        ret += '(exit)\n'
        return ret