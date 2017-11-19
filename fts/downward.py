import math
import os

from time import time
from algorithms import get_cost

INF = float('inf')

COST_SCALE = 1
MAX_COST = (2**31 - 1) / 100


def read(filename):
    with open(filename, 'r') as f:
        return f.read()


def write(filename, string):
    with open(filename, 'w') as f:
        f.write(string)


def remove(path):
    if os.path.exists(path):
        os.remove(path)


def transform_cost(cost):
    new_cost = int(math.ceil(COST_SCALE * cost))
    assert new_cost < MAX_COST
    return new_cost


def write_version(version=3):
    return 'begin_version\n'           '%s\n'           'end_version\n' % version


def write_action_costs(use_costs=True):
    return 'begin_metric\n'           '%s\n'           'end_metric\n' % int(use_costs)


def write_variables(problem):
    s = '%s\n' % len(problem.var_order)
    for i, var in enumerate(problem.var_order):
        axiom_layer = 0 if var in problem.derived_vars else -1

        n = max(len(problem.var_val_order[var]), 2)
        name = var if type(var) == str else 'var%s' % i
        s += 'begin_variable\n'             '%s\n'             '%s\n'             '%s\n' % (
            name, axiom_layer, n)
        for j in xrange(n):

            s += '%s-%s\n' % (i, j)
        s += 'end_variable\n'
    return s


def write_mutexes(problem):
    s = '%s\n' % len(problem.mutexes)
    for mutex in problem.mutexes:
        s += 'begin_mutex_group\n'             '%s\n' % len(mutex)
        for var, val in mutex:
            s += '%s %s\n' % (var, val)
        s += 'end_mutex_group'
    return s


def write_initial(problem):

    s = 'begin_state\n'
    for var in problem.var_order:
        val = problem.get_val(var, problem.initial[var])
        s += '%s\n' % val
    s += 'end_state\n'
    return s


def write_goal(problem):
    s = 'begin_goal\n'        '%s\n' % len(problem.goal)
    for item in problem.goal.items():
        var, val = problem.get_var_val(*item)
        s += '%s %s\n' % (var, val)
    s += 'end_goal\n'
    return s


def write_actions(problem):
    s = '%s\n' % len(problem.actions)
    for i, action in enumerate(problem.actions):
        s += 'begin_operator\n'             'a-%s\n'             '%s\n' % (
            i, len(action.conditions))
        for item in action.conditions.iteritems():
            var, val = problem.get_var_val(*item)
            s += '%s %s\n' % (var, val)
        s += '%s\n' % len(action.effects)
        for item in action.effects.iteritems():
            var, val = problem.get_var_val(*item)
            s += '0 %s -1 %s\n' % (var, val)
        s += '%s\n'             'end_operator\n' % transform_cost(
            action.cost)
    return s


def write_axioms(problem):
    s = '%s\n' % len(problem.axioms)
    for axiom in problem.axioms:
        s += 'begin_rule\n'
        s += '%s\n' % len(axiom.conditions)
        for item in axiom.conditions.items():
            var, val = problem.get_var_val(*item)
            s += '%s %s\n' % (var, val)
        var_con = -1
        var, val = problem.get_var_val(axiom.var, axiom.val)
        s += '%s %s %s\n' % (var, var_con, val)
        s += 'end_rule\n'
    return s


FD_PATH = os.environ['FD_PATH']

SAS_PATH = 'output.sas'
OUTPUT_PATH = 'sas_plan'


SEARCH_OPTIONS = {
    'dijkstra': '--heuristic "h=blind(transform=adapt_costs(cost_type=PLUSONE))" '
                '--search "astar(h,max_time=%s,bound=%s)"',
    'max_astar': '--heuristic "h=hmax(transform=adapt_costs(cost_type=PLUSONE))" '
    '--search "astar(h,max_time=%s,bound=%s)"',
    'count_lazy': '--heuristic "h=goalcount(transform=adapt_costs(cost_type=PLUSONE))" '
                 '--search "lazy_greedy([h],boost=1000,max_time=%s,bound=%s)"',
    'cea_astar': '--heuristic "h=cea(transform=adapt_costs(cost_type=PLUSONE))" '
    '--search "astar(h,max_time=%s,bound=%s)"',
    'cea_eager': '--heuristic "h=cea(transform=adapt_costs(cost_type=PLUSONE))" '
    '--search "eager_greedy([h],preferred=[h],boost=1000,max_time=%s,bound=%s)"',
    'cea_lazy': '--heuristic "h=cea(transform=adapt_costs(cost_type=PLUSONE))" '
    '--search "lazy_greedy([h],preferred=[h],boost=1000,max_time=%s,bound=%s)"',
    'ff_astar': '--heuristic "h=ff(transform=adapt_costs(cost_type=PLUSONE))" '
                '--search "astar(h,max_time=%s,bound=%s)"',
    'ff_eager': '--heuristic "h=ff(transform=adapt_costs(cost_type=PLUSONE))" '
                 '--search "eager_greedy([h],preferred=[h],boost=1000,max_time=%s,bound=%s)"',
    'ff_lazy': '--heuristic "h=ff(transform=adapt_costs(cost_type=PLUSONE))" '
                '--search "lazy_greedy([h],preferred=[h],boost=1000,max_time=%s,bound=%s)"',
}


SEARCH_COMMAND = FD_PATH + 'bin/downward %s < %s'


def write_sas(problem):
    s = write_version() + write_action_costs() + write_variables(problem) + write_mutexes(problem) + \
        write_initial(problem) + write_goal(problem) + \
        write_actions(problem) + write_axioms(problem)
    write(SAS_PATH, s)


def fast_downward(options, max_time, max_cost, verbose=False):
    if max_time == INF:
        max_time = 'infinity'
    else:
        max_time = int(math.ceil(max_time))
    if max_cost == INF:
        max_cost = 'infinity'
    else:
        max_cost = transform_cost(max_cost)
    remove(OUTPUT_PATH)
    search_options = SEARCH_OPTIONS[options] % (max_time, max_cost)

    command = SEARCH_COMMAND % (search_options, SAS_PATH)

    print command
    t0 = time()
    p = os.popen(command)
    output = p.read()
    if verbose:
        print output
        print 'Search time:', time() - t0
    if not os.path.exists(OUTPUT_PATH):
        return None
    return read(OUTPUT_PATH)


def convert_solution(solution, problem):

    lines = solution.split('\n')[:-2]
    plan = []
    for line in lines:
        index = int(line.strip('( )')[2:])
        plan.append(problem.actions[index])
    return plan


def solve_sas(problem, options='cea_lazy', max_time=INF, max_cost=INF):
    write_sas(problem)
    plan = fast_downward(options, max_time, max_cost)
    if plan is None:
        return None
    return convert_solution(plan, problem)


def goal_serialization(problem, options='cea_lazy', new_goals=1, max_time=INF, max_cost=INF):

    start_time = time()
    goal_action = None
    for action in problem.actions:
        if action.effects == {'goal': True}:
            assert goal_action is None
            goal_action = action
    assert goal_action is not None

    goal_conditions = goal_action.conditions
    goal_order = sorted(goal_conditions.keys())
    goal_action.conditions = {}

    total_plan = []
    for i in xrange(0, len(goal_order), new_goals):
        for j in xrange(i, min(i + new_goals, len(goal_order))):
            var = goal_order[j]
            goal_action.conditions[var] = goal_conditions[var]
        if problem.is_applicable(problem.initial, goal_action):
            continue
        solution = solve_sas(problem, options=options, max_time=(max_time - (time() - start_time)),
                             max_cost=(max_cost - get_cost(total_plan)))
        if solution is None:
            return None
        plan = solution[:-1]
        for action in plan:
            problem.initial = action.apply(problem.initial)
        total_plan += plan
    return total_plan + [goal_action]
