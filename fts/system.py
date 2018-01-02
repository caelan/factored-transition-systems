

def get_dict(d, k):
    return d.get(k, k)


class Parameter(object):

    def __init__(self, s, var):
        self.set = s
        self.var = var

    def __eq__(self, other):
        return type(self) == type(other) and (self.set == other.set) and (self.var == other.var)

    def __ne__(self, other):
        return not (self == other)

    def __hash__(self):
        return hash((type(self), self.set, self.var))

    def __repr__(self):
        return '{}[{}]'.format(self.set, self.var)


class FixedParameter(Parameter):

    def __init__(self, s, var, value):
        super(FixedParameter, self).__init__(s, var)
        self.value = value

    def __repr__(self):
        return '{}[{}]={}'.format(self.set, self.var, self.value)


class VariableSet(object):

    def __init__(self, name):
        self.name = name

    def __getitem__(self, var):
        return Parameter(self, var)

    def __repr__(self):
        return self.name


class ConstantSet(VariableSet):

    def __getitem__(self, (var, value)):
        return FixedParameter(self, var, value)


I = VariableSet('inp')
O = VariableSet('out')
X = VariableSet('X')
U = VariableSet('U')
nX = VariableSet('nX')
C = ConstantSet('C')


class Atom(object):

    def __init__(self, constraint, parameters):
        self.constraint = constraint
        self.parameters = tuple(parameters)
        assert len(self.parameters) == len(self.constraint.variables)

    def items(self):
        return zip(self.constraint.variables, self.parameters)

    def replace(self, new_from_old):
        return self.constraint(*[get_dict(new_from_old, p) for p in self.parameters])

    def __eq__(self, other):
        return type(self) == type(other) and (self.constraint == other.constraint) and (self.parameters == other.parameters)

    def __ne__(self, other):
        return not (self == other)

    def __hash__(self):
        return hash((type(self), self.constraint, self.parameters))

    def __repr__(self):
        return '{}({})'.format(self.constraint.constraint_type, ','.join(map(repr, self.parameters)))


class Constraint(object):

    def __init__(self, constraint_type, variables):
        self.constraint_type = constraint_type
        self.variables = tuple(variables)
        self._hash = None

    def __call__(self, *parameters):
        return Atom(self, parameters)

    def __eq__(self, other):
        return type(self) == type(other) and (self.constraint_type == other.constraint_type) and (self.variables == other.variables)

    def __ne__(self, other):
        return not (self == other)

    def __hash__(self):
        if self._hash is None:
            self._hash = hash(
                (type(self), self.constraint_type, self.variables))
        return self._hash

    def __repr__(self):
        return '{}({})'.format(self.constraint_type, ','.join(map(repr, self.variables)))


class ConstraintType(object):
    num = 0

    def __init__(self, name=None):
        self.n = ConstraintType.num
        ConstraintType.num += 1
        if name is None:
            name = 'Con{:d}'.format(self.n)
        self.name = name
        self.axioms = {}

    def __call__(self, *parameters):
        variables = tuple(p.var for p in parameters)
        values = [p.value if isinstance(
            p, FixedParameter) else p for p in parameters]
        return self[variables](*values)

    def __getitem__(self, variables):
        if type(variables) != tuple:

            variables = (variables,)
        return Constraint(self, variables)

    def __repr__(self):
        return self.name


class ConstraintTypeConstants(ConstraintType):

    def __call__(self, *values):
        parameters = filter(lambda v: isinstance(v, Parameter), values)
        assert parameters
        variable = parameters[0].var

        new_parameters = []
        for value in values:
            if isinstance(value, Parameter):
                new_parameters.append(value)
            else:

                new_parameters.append(C[variable, value])
        return super(ConstraintTypeConstants, self).__call__(*new_parameters)


Equal = ConstraintTypeConstants(name='Equal')
Value = ConstraintTypeConstants(name='Value')
Difference = ConstraintTypeConstants(name='Difference')
Quotient = ConstraintTypeConstants(name='Quotient')


class Clause(object):

    def __init__(self, constraints):
        self.constraints = constraints

    def get_constraints(self, variables):
        return self.constraints


class SparseClause(Clause):

    def __init__(self, constraints, changed_vars=tuple()):
        super(SparseClause, self).__init__(constraints)
        self.changed_vars = changed_vars

    def get_constraints(self, state_vars):
        unchanged_constraints = []
        changed_vars = set(self.changed_vars)
        for constraint in self.constraints:
            for param in constraint.parameters:
                if isinstance(param, Parameter) and (param.set == nX):
                    changed_vars.add(param.var)
        for var in state_vars:
            if var not in changed_vars:
                unchanged_constraints.append(unchanged(var))
        return self.constraints + unchanged_constraints


class FTSProblem(object):

    def __init__(self, initial_state, goal_clause, transitions, samplers,
                 cost_fn=None):
        self.initial_state = initial_state
        self.goal_clause = goal_clause
        self.transitions = []
        for clause in transitions:
            if isinstance(clause, Clause):
                self.transitions.append(
                    clause.get_constraints(self.state_vars))
            else:
                self.transitions.append(clause)
        self.samplers = samplers
        self.cost_fn = cost_fn

    @property
    def state_vars(self):
        return self.initial_state.keys()

    @property
    def control_vars(self):
        raise NotImplementedError()

    def __repr__(self):
        return 'Initial: {}\n'               'Goal: {}\n'               'Transition: {}\n'               'Samplers: {}'.format(self.initial_state, self.goal_clause,
                                                                                                                               self.transitions, self.samplers)


def rename_constraints(assignments):
    for name, value in assignments.iteritems():
        if isinstance(value, ConstraintType):
            value.name = name


def unchanged(var):
    return Equal(X[var], nX[var])


def increase(var, amount):
    return Difference(nX[var], X[var], amount)


def decrease(var, amount):
    return Difference(X[var], nX[var], amount)


def scale(var, amount):
    return Quotient(nX[var], X[var], amount)


def shrink(var, amount):
    return Quotient(X[var], nX[var], amount)
