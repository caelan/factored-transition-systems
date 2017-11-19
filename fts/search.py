from collections import namedtuple, deque, defaultdict
from heapq import heappop, heappush

from fts.sas import Argument

import time

Node = namedtuple('Node', ['action', 'parent', 'cost'])


def blind_heuristic(*args):
    return 0


def goal_count(state, goal):
    return sum(state[var] != val for var, val in goal.items())


def state_distance(state, goal, metrics={}):
    return sum([0] + [metrics[var](state[var], val) for var, val in goal.items()])


def is_goal(state, goal):
    return all(state[var] == val for var, val in goal.items())


def lifted_bfs(initial, goal, actions, constraint_values):

    for action in actions:
        value_from_arg = {var: initial[
            var] for var, arg in action.conditions.items() if isinstance(arg, Argument)}
        print value_from_arg

        print action

    if is_goal(initial, goal):
        return []
    state = frozenset(initial.items())
    visited = {state: Node(None, None)}
    queue = deque([state])
    while queue:
        state = dict(queue.popleft())
        raise NotImplentedError()
    return None


def state_key(state):

    return frozenset(state.items())


def retrace_plan(state, visited):
    key = state_key(state)
    if visited[key].parent is None:
        return []
    return retrace_plan(visited[key].parent, visited) + [visited[key].action]


def get_successor_map(actions, variables):
    index_from_var = dict(map(reversed, enumerate(variables)))
    successor_map = defaultdict(lambda: defaultdict(set))
    for action in actions:
        vars = tuple(sorted(action.conditions, key=index_from_var.get))
        vals = tuple(action.conditions[var] for var in vars)
        successor_map[vars][vals].add(action)
    return successor_map


def all_actions(state, actions):
    return actions


def successor_actions(state, successor_map):
    for vars in successor_map:
        vals = tuple(state[var] for var in vars)
        for action in successor_map[vars][vals]:
            yield action


def dijkstra(sas_problem, max_time=30):
    assert not sas_problem.axioms
    t0 = time.time()
    successor_map = get_successor_map(
        sas_problem.actions, sas_problem.initial.keys())
    visited = {state_key(sas_problem.initial): Node(None, None, 0)}
    queue = [(0, sas_problem.initial)]
    processed = set()
    while queue and (time.time() - t0) < max_time:
        _, state = heappop(queue)
        key = state_key(state)
        if key in processed:
            continue
        processed.add(key)
        if is_goal(state, sas_problem.goal):
            return retrace_plan(state, visited)

        for action in successor_actions(state, successor_map):
            if not action.is_applicable(state):
                continue
            new_state = action.apply(state)
            new_cost = visited[key].cost + action.cost
            new_key = state_key(new_state)
            if (new_key not in visited) or (new_cost < visited[new_key].cost):
                visited[new_key] = Node(action, state, new_cost)
                heappush(queue, (new_cost, new_state))
    return None


def bfs(sas_problem, max_time=30):
    assert not sas_problem.axioms
    t0 = time.time()
    visited = {state_key(sas_problem.initial): Node(None, None, 0)}
    queue = deque([sas_problem.initial])
    while queue and (time.time() - t0) < max_time:
        state = queue.popleft()
        if is_goal(state, sas_problem.goal):
            return retrace_plan(state, visited)
        for action in sas_problem.actions:
            if not action.is_applicable(state):
                continue
            new_state = action.apply(state)
            new_key = state_key(new_state)
            if new_key not in visited:
                visited[new_key] = Node(action, state, None)
                queue.append(new_state)
    return None
