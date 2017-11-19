from fts.incremental import SampleSpace, update_plan
from heapq import heappush, heappop
from fts.algorithms import GOAL_VAR, get_cost, get_controls, print_plan

from fts.algorithms import transform_goal
from itertools import product
from collections import namedtuple

from fts.sas import SASProblem
from fts.system import Value, Parameter, C, Equal
from fts.downward import solve_sas, goal_serialization
from fts.samplers import LazySample

from collections import defaultdict
import time

Node = namedtuple('Node', ['generator', 'effort'])

INF = float('inf')

EFFORT_OPERATOR = sum


class LazySampleSpace(object):

    def __init__(self, space, blocked_generators, effort_weight, max_effort=INF):
        self.space = space
        self.effort_weight = effort_weight
        self.max_effort = max_effort

        self.constraint_values = {}
        self.effort_from_generator = {}
        self.priority_queue = []
        self.blocked_generators = blocked_generators

        self.node_from_element = {}
        for generator in space.generators:
            if generator not in self.blocked_generators:
                effort = generator.effort
                self.effort_from_generator[generator] = effort
                heappush(self.priority_queue, (effort, generator))

        for _, elements in space.constraint_values.items():
            for element in elements:
                self._add_constraint(element, None, 0)
        self.sample_priority_queue()

    def retrace_generators(self, instance, generators):
        for element in instance.get_domain():
            generator = self.node_from_element[element].generator
            if (generator is not None) and (generator not in generators):

                self.retrace_generators(generator, generators)
                generators.append(generator)

    def set_cost(self, action_instance):
        if GOAL_VAR in action_instance.effects:
            action_instance.cost = 0
        elif self.space.problem.cost_fn is None:
            action_instance.cost = 1
        else:
            action_instance.cost = self.space.problem.cost_fn(
                **action_instance.get_controls())
        effort = self.get_effort(action_instance)
        assert effort <= self.max_effort
        action_instance.cost += self.effort_weight * effort

    def get_action_instances(self):

        for action in self.space.actions:
            for instance in action.get_instances(self.constraint_values):
                if not all(d in self.axiom_from_derived for d in instance.derived):
                    continue
                self.set_cost(instance)
                yield instance

    def get_axiom_instances(self):

        self.axiom_from_derived = defaultdict(list)
        for axiom in self.space.axioms:
            for instance in axiom.get_instances(self.constraint_values):
                self.axiom_from_derived[instance.derived].append(instance)
                yield instance

    def get_sas_problem(self):
        axiom_instances = list(self.get_axiom_instances())
        action_instances = list(self.get_action_instances())
        return SASProblem(self.space.initial, self.space.goal,
                          action_instances, axiom_instances)

    def sample_priority_queue(self):

        while self.priority_queue:
            effort, generator = heappop(self.priority_queue)
            output_list, element_list = generator.lazy_next()
            generator.lazy_output_list = output_list
            for element in element_list:
                self._add_constraint(element, generator, effort)

    def get_effort(self, instance):
        return EFFORT_OPERATOR([0] + [self.node_from_element[el].effort for el in instance.get_domain()])

    def _add_generator(self, generator):
        if generator in self.blocked_generators:

            return

        effort = self.get_effort(generator) + generator.effort
        if generator in self.effort_from_generator:
            assert self.effort_from_generator[generator] <= effort
            return

        self.effort_from_generator[generator] = effort
        if self.max_effort < effort:
            raise RuntimeError()

        heappush(self.priority_queue, (effort, generator))

    def _update_generators(self, element):
        for sampler, i in self.space.samplers_from_constraint[element.constraint]:
            values = [self.constraint_values.get(c, []) if i != j else [element]
                      for j, c in enumerate(sampler.domain_constraints)]
            for combo in product(*values):

                assignment = {}
                for t, a in zip(sampler.augmented_domain, combo):
                    for p, v in zip(t.parameters, a.parameters):
                        if assignment.get(p.var, v) == v:
                            assignment[p.var] = v
                        else:
                            break
                    else:
                        continue
                    break
                else:
                    input_values = tuple(assignment[j]
                                         for j in xrange(len(assignment)))
                    self._add_generator(sampler(input_values))

    def _add_atom(self, element, generator, effort):
        if element.constraint not in self.constraint_values:
            self.constraint_values[element.constraint] = set()
        elif element in self.constraint_values[element.constraint]:
            assert self.node_from_element[element].effort <= effort
            return
        self.node_from_element[element] = Node(generator, effort)
        self.constraint_values[element.constraint].add(element)
        self._update_generators(element)

    def _add_constraint(self, element, generator, effort):
        assert element.constraint.constraint_type != Equal
        assert not any(isinstance(val, Parameter)
                       for val in element.parameters)
        for var, value in element.items():
            self._add_atom(Value(C[var, value]), generator, effort)
        self._add_atom(element, generator, effort)

    def _get_plan_instances(self, solution):
        states = [self.space.initial]
        for action_instance in solution:

            for atom in action_instance.derived:
                for axiom_instance in self.axiom_from_derived[atom]:
                    if axiom_instance.is_applicable(states[-1]):
                        yield axiom_instance
                        break
                else:
                    raise RuntimeError('No supporting axioms!')
            yield action_instance

            states.append(action_instance.apply(states[-1]))

    def get_plan_generators(self, solution):
        generators = []
        for instance in self._get_plan_instances(solution):
            self.retrace_generators(instance, generators)
        return generators

    def __len__(self):
        return sum([0] + [len(values) for values in self.constraint_values.values()])


def sample_initial(space, generators, max_calls):
    assert 1 <= max_calls
    first_generators = filter(lambda g: g in space.generators, generators)
    assert first_generators
    sampled_generators = []
    for generator in first_generators:
        assert not generator.greedy
        if max_calls <= len(sampled_generators):
            break
        space.sample(generator)
        sampled_generators.append(generator)
    return sampled_generators


def sample_dag(space, generators, greedy, max_list, max_layers=INF):
    sampled_generators = []
    values_from_lazy = defaultdict(set)
    elements_from_lazy = defaultdict(set)

    for lazy_generator in generators:

        input_domains = [values_from_lazy[v] if isinstance(v, LazySample) else {v}
                         for v in lazy_generator.input_values]

        for combo in product(*input_domains):
            real_generator = lazy_generator.sampler(combo)
            if real_generator.exhausted:
                continue
            output_list = space.sample(real_generator)
            sampled_generators.append(real_generator)
            if greedy and (not output_list):
                break
            if max_list != INF:
                output_list = output_list[:max_list]
            for lazy_outputs in lazy_generator.lazy_output_list:
                for outputs in output_list:
                    for l, o in zip(lazy_outputs, outputs):

                        values_from_lazy[l].add(o)
                    for l, r in zip(lazy_generator.prepare_atoms(lazy_outputs), real_generator.prepare_atoms(outputs)):
                        elements_from_lazy[l].add(r)
    return sampled_generators


def focused(fts_problem, max_time=INF, search_options='ff_lazy', max_search_time=10, effort_weight=10, max_constraints=1,
            single_layer=False, max_samplers=INF, test_feasible=False, greedy=True, debug=True):
    assert greedy or (effort_weight == 0)

    initial, goal, clauses = transform_goal(fts_problem)
    space = SampleSpace(initial, goal, clauses, fts_problem,
                        max_constraints=max_constraints)
    space.epochs += 1
    best_plan = None
    blocked_generators = set()

    while (time.time() - space.start_time) <= max_time:
        space.iterations += 1

        if test_feasible:
            search_time = min(max_search_time, max_time -
                              (time.time() - space.start_time))
            best_plan = update_plan(space, best_plan, 'ff_lazy', search_time)
            if (best_plan is not None) and greedy:
                break

        lazy_space = LazySampleSpace(
            space, blocked_generators, effort_weight=effort_weight)
        sas_problem = lazy_space.get_sas_problem()
        print 'Iteration: {} | Epoch: {} | Atoms: {} | '              'Actions: {} | Axioms: {} | Blocked: {} | Time: {}'.format(
            space.iterations, space.epochs, len(lazy_space),
            len(sas_problem.actions), len(sas_problem.axioms),
            len(blocked_generators), (time.time() - space.start_time))
        search_time = max_time - (time.time() - space.start_time)
        if blocked_generators:
            search_time = min(search_time, max_search_time)
        solution = solve_sas(sas_problem, options=search_options,
                             max_time=search_time, max_cost=get_cost(best_plan))

        if solution is None:
            if not blocked_generators:
                break
            blocked_generators = set()
            space.epochs += 1
            continue
        if debug:
            print 'Length: {} | Cost: {}'.format(len(solution), get_cost(solution))
            print_plan(solution)

        generators = lazy_space.get_plan_generators(solution)
        if not generators:
            plan = solution[:-1]
            if get_cost(plan) < get_cost(best_plan):
                print 'New best plan! Length: {} | Cost: {}'.format(len(plan), get_cost(plan))
                best_plan = plan
            if greedy:
                break
            else:
                continue
        if single_layer:

            sampled_generators = sample_initial(
                space, generators, max_samplers)
        else:
            sampled_generators = sample_dag(
                space, generators, greedy=False, max_list=max_samplers)
        if debug:
            print sampled_generators
        blocked_generators.update(sampled_generators)

    return get_controls(best_plan)
