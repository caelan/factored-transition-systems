from fts.system import Parameter, X, C, Equal, nX

import copy

GOAL_VAR = 'goal'
GOAL_CLAUSE = 'goal'


def check_validity(problem):
    atoms = problem.goal_clause[:]
    for clause in problem.transitions:
        atoms += clause
    for atom in atoms:
        for param in atom.parameters:
            if isinstance(param, Parameter) and (param.set in (X, nX)) and (param.var not in problem.initial_state):
                raise ValueError(
                    'Variable {} not declared in the initial state'.format(param.var))


def transform_goal(problem):
    initial = copy.copy(problem.initial_state)
    initial[GOAL_VAR] = False
    goal = {GOAL_VAR: True}

    for atom in problem.goal_clause:
        for param in atom.parameters:
            assert (not isinstance(param, Parameter)) or (param.set == X, C)
    clauses = [list(problem.goal_clause) +
               [Equal(X[var], nX[var]) for var in problem.initial_state] +
               [Equal(nX[GOAL_VAR], True)]]
    for clause in problem.transitions:
        clauses.append(list(clause) + [Equal(X[GOAL_VAR], nX[GOAL_VAR])])
    return initial, goal, clauses


INF = float('inf')


def get_cost(plan):
    if plan is None:
        return INF
    return sum([0] + [action.cost for action in plan])


def get_controls(plan):
    if plan is None:
        return None
    return [instance.get_controls() for instance in plan]


def print_plan(plan):
    if plan is None:
        print None
        return
    for i, action in enumerate(plan):
        print i, action
