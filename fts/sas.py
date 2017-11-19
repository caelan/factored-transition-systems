from fts.system import Equal, U, Parameter, X, nX, C, get_dict, Value, ConstraintType

from itertools import product
from collections import defaultdict
import copy


class Argument(object):

    def __init__(self, var, num=1):
        self.var = var
        self.num = num

    def __repr__(self):
        if self.num == 1:
            return '?{}'.format(self.var)
        return '?{}-{}'.format(self.var, self.num)


class Instance(object):

    def is_applicable(self, state):
        return all(state[var] == val for var, val in self.conditions.iteritems())

    def get_domain(self):

        return self.constraints


class ActionInstance(Instance):

    def __init__(self, lifted, arguments, constraints, derived, conditions, effects, cost=1):
        self.lifted = lifted
        self.arguments = tuple(arguments)
        self.constraints = tuple(constraints)
        self.derived = tuple(derived)
        self.conditions = copy.copy(conditions)
        self.preconditions = conditions
        self.effects = effects
        self.cost = cost
        for derived in self.derived:
            self.conditions[derived] = True

    def apply(self, state):
        new_state = copy.copy(state)
        for var, val in self.effects.items():
            new_state[var] = val
        return new_state

    def get_controls(self):
        value_from_arg = dict(zip(self.lifted.arguments, self.arguments))
        return {var: get_dict(value_from_arg, self.lifted.value_from_param[U[var]])
                for var in self.lifted.control_vars}

    def __repr__(self):

        return '<{},{}>'.format(self.preconditions, self.effects)


class AxiomInstance(Instance):

    def __init__(self, lifted, arguments, constraints, conditions, derived):
        self.lifted = lifted
        self.arguments = tuple(arguments)
        self.constraints = tuple(constraints)
        self.conditions = conditions
        self.derived = derived
        self.var, self.val = derived, True

    def __repr__(self):
        return 'Axiom({},{})'.format(self.conditions, {self.var: self.val})


def create_axiom(element):
    control_indices = tuple(i for i, p in enumerate(
        element.parameters) if p.set in (nX, U))
    constraint_type = element.constraint.constraint_type
    if (element.constraint, control_indices) not in constraint_type.axioms:
        constraint_type.axioms[(element.constraint, control_indices)] = Axiom(
            element.constraint, control_indices)
    axiom = constraint_type.axioms[(element.constraint, control_indices)]
    control_params = tuple(element.parameters[i] for i in control_indices)
    derived_element = axiom.derived.constraint(*control_params)
    return derived_element, axiom


def create_action(state_vars, atoms, max_constraints=1):

    equalities = filter(lambda a: a.constraint.constraint_type is Equal, atoms)
    value_from_param = {}
    fixed_vars = set()
    for equal in equalities:
        p1, p2 = equal.parameters
        if (not isinstance(p1, Parameter)) and (not isinstance(p2, Parameter)):
            raise RuntimeError()
        elif not isinstance(p1, Parameter):
            value_from_param[p2] = p1
        elif not isinstance(p2, Parameter):
            value_from_param[p1] = p2
        elif ((p1.set == X) and (p2.set == nX)) or ((p1.set == nX) and (p2.set == X)):
            assert p1.var == p2.var
            fixed_vars.add(p1.var)
        else:
            raise ValueError(equal)

    constraints = filter(lambda a: a not in equalities, atoms)
    control_vars = {
        p.var for a in constraints for p in a.parameters if p.set == U}

    control_params = {U[var] for var in control_vars}

    for var in state_vars:
        if (var not in fixed_vars) and (nX[var] not in value_from_param):
            control_params.add(nX[var])

    axiom_atoms = filter(lambda a: any(
        p not in control_params for p in a.parameters), constraints)
    keep_atoms = filter(lambda a: a not in axiom_atoms, constraints)
    keep_additional = max(max_constraints - len(keep_atoms),
                          0) if control_params else 0
    keep_atoms += axiom_atoms[:keep_additional]
    axiom_atoms = axiom_atoms[keep_additional:]

    derived_atoms = []
    axioms = []
    for atom in axiom_atoms:

        derived_atom, axiom = create_axiom(atom)
        derived_atoms.append(derived_atom)
        axioms.append(axiom)

    for var in sorted(control_vars):
        p = U[var]
        assert p not in value_from_param

        value_from_param[p] = Argument(var)

    parameters = {p for a in keep_atoms for p in a.parameters}
    preconditions = {}
    for var in sorted(state_vars):
        p1 = X[var]
        if p1 in value_from_param:
            preconditions[var] = value_from_param[p1]
        elif p1 in parameters:
            value_from_param[p1] = Argument(var)
            preconditions[p1.var] = value_from_param[p1]

    effects = {}
    for var in sorted(state_vars):
        p2 = nX[var]
        if p2 in value_from_param:
            effects[var] = value_from_param[p2]
        elif var in fixed_vars:
            p1 = X[var]
            if p1 in parameters:
                value_from_param[p2] = value_from_param[p1]
        else:
            value_from_param[p2] = Argument(var, 2)
            effects[var] = value_from_param[p2]
    return Action(value_from_param, keep_atoms, derived_atoms, preconditions, effects, axioms)


def satisfying_values(constraints, constraint_values):

    for combo in product(*[constraint_values.get(a.constraint, []) for a in constraints]):
        value_from_arg = {}
        for t, a in zip(constraints, combo):
            for p, v in zip(t.parameters, a.parameters):
                if value_from_arg.get(p, v) == v:
                    value_from_arg[p] = v
                else:
                    break
            else:
                continue
            break
        else:
            yield value_from_arg


class Axiom(object):

    def __init__(self, constraint, control_indices):
        self.arguments = tuple(Argument(var) for var in constraint.variables)
        self.conditions = {arg.var: arg for i, arg in enumerate(
            self.arguments) if i not in control_indices}
        self.constraint = constraint(*self.arguments)
        derived_type = ConstraintType(
            name='Der-{}'.format(constraint.constraint_type.name))
        self.derived = derived_type(
            *(self.arguments[i] for i in control_indices))

    def get_instances(self, constraint_values):
        for value_from_arg in satisfying_values([self.constraint], constraint_values):
            values = [value_from_arg[arg] for arg in self.arguments]
            element = self.constraint.replace(value_from_arg)
            assert element in constraint_values[element.constraint]
            conditions = {var: get_dict(value_from_arg, arg)
                          for var, arg in self.conditions.items()}
            derived = self.derived.replace(value_from_arg)
            yield AxiomInstance(self, values, [element], conditions, derived)

    """
    def identifier(self):
        return type(self), self.constraint, self.derived

    def __eq__(self, other):
        return (type(self) == type(other)) and (self.identifier() == other.identifier())

    def __ne__(self, other):
        return not (self == other)

    def __hash__(self):
        return hash(self.identifier())
    """

    def __repr__(self):
        return '<{}, {}, {}, {}>'.format(self.arguments, self.constraint,
                                         self.conditions, self.derived)


class Action(object):

    def __init__(self, value_from_param, constraints, derived, preconditions, effects, axioms):

        self.value_from_param = value_from_param
        self.arguments = tuple(arg for arg in set(self.value_from_param.values())
                               if isinstance(arg, Argument))
        self.conditions = preconditions
        self.effects = effects
        self.control_vars = {p.var for p in value_from_param if p.set == U}
        self.constraints = [a.replace(value_from_param) for a in constraints]
        constrained_args = {
            a for c in self.constraints for a in c.parameters if isinstance(a, Argument)}
        self.constraints += [Value(C[a.var, a])
                             for a in self.arguments if a not in constrained_args]
        self.derived = [a.replace(self.value_from_param) for a in derived]
        self.axioms = axioms

    def get_instances(self, constraint_values):
        for value_from_arg in satisfying_values(self.constraints, constraint_values):
            values = [value_from_arg[arg] for arg in self.arguments]
            constraints = [a.replace(value_from_arg) for a in self.constraints]
            assert all(a in constraint_values[
                       a.constraint] for a in constraints)
            conditions = {var: get_dict(value_from_arg, arg)
                          for var, arg in self.conditions.items()}
            effects = {var: get_dict(value_from_arg, arg)
                       for var, arg in self.effects.items()}
            derived = [derived.replace(value_from_arg)
                       for derived in self.derived]
            yield ActionInstance(self, values, constraints, derived, conditions, effects)

    def __repr__(self):
        return '<{}, {}, {}, {}, {}>'.format(self.arguments, self.constraints, self.derived,
                                             self.conditions, self.effects)


class SASProblem(object):

    def __init__(self, initial, goal, actions, axioms):
        self.var_indices = {}
        self.var_order = []
        self.var_val_indices = {}
        self.var_val_order = {}
        self.mutexes = []
        self.costs = True
        self.derived_vars = set()

        self.initial = copy.copy(initial)
        self.actions = actions
        for action in self.actions:
            for var, val in (action.conditions.items() + action.effects.items()):
                self._add_val(var, val)
        self.axioms = axioms
        self.axiom_from_derived = defaultdict(list)
        for axiom in self.axioms:
            self.axiom_from_derived[axiom.derived].append(axiom)
            for var, val in axiom.conditions.items():
                self._add_val(var, val)
            self.derived_vars.add(axiom.var)
            self.initial[axiom.var] = False
            self._add_val(axiom.var, axiom.val)
        self.goal = goal
        for var, val in (self.initial.items() + self.goal.items()):
            self._add_val(var, val)

    def is_applicable(self, state, action):

        if not all(state[var] == val for var, val in action.preconditions.items() if var in action.conditions):
            return False
        for atom in action.derived:
            if atom not in action.conditions:
                continue
            for axiom_instance in self.axiom_from_derived[atom]:
                if axiom_instance.is_applicable(state):
                    break
            else:
                return False
        return True

    def _add_var(self, var):
        if var not in self.var_indices:
            self.var_indices[var] = len(self.var_order)
            self.var_order.append(var)
            self.var_val_indices[var] = {}
            self.var_val_order[var] = []

    def _add_val(self, var, val):
        self._add_var(var)
        if val not in self.var_val_indices[var]:
            self.var_val_indices[var][val] = len(self.var_val_order[var])
            self.var_val_order[var].append(val)

    def get_var(self, var):
        return self.var_indices[var]

    def get_val(self, var, val):
        return self.var_val_indices[var][val]

    def get_var_val(self, var, val):
        return self.get_var(var), self.get_val(var, val)

    def __repr__(self):
        return str(self.actions)
