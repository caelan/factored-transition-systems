import time
from collections import deque
from collections import namedtuple, defaultdict
from itertools import product

from fts.algorithms import transform_goal, check_validity, GOAL_VAR, get_cost, get_controls, print_plan, INF
from fts.downward import solve_sas
from fts.sas import create_action, SASProblem
from fts.system import Value, Parameter, C, Equal
from fts.samplers import Test


class SampleSpace(object):

    def __init__(self, initial, goal, clauses, problem, max_constraints=1):
        self.start_time = time.time()
        self.iterations = 0

        self.initial = initial
        self.goal = goal
        self.problem = problem
        self.actions = {create_action(initial.keys(), clause,
                                      max_constraints=max_constraints) for clause in clauses}
        self.axioms = {ax for action in self.actions for ax in action.axioms}

        self.constraint_values = {}
        self.negative_values = {}
        self.generators = set()
        self.greedy_queue = deque()
        self.lazy_queue = deque()

        self.test_constraints = set()
        for sampler in problem.samplers:

            if sampler.is_simple_test() and sampler.greedy:
                for constraint in sampler.get_constraints():
                    self.test_constraints.add(constraint)

        for axiom in self.axioms:
            if axiom.constraint.constraint in self.test_constraints:
                axiom.value = False

        self._initialize_samplers()
        self._initialize_atoms(clauses)

    def _initialize_samplers(self):
        self.samplers_from_constraint = defaultdict(list)
        for sampler in self.problem.samplers:
            for i, constraint in enumerate(sampler.domain_constraints):
                self.samplers_from_constraint[constraint].append((sampler, i))

    def _initialize_atoms(self, clauses):
        for var, val in (self.initial.items() + self.goal.items()):
            self._add_constraint(Value(C[var, val]))
        for clause in clauses:
            for atom in clause:
                self._add_constraint(atom)
        for sampler in self.problem.samplers:
            if not sampler.augmented_domain:
                self._add_generator(sampler(tuple()))

    def set_cost(self, action_instance):
        if GOAL_VAR in action_instance.effects:
            action_instance.cost = 0
        elif self.problem.cost_fn is None:
            action_instance.cost = 1
        else:
            action_instance.cost = self.problem.cost_fn(
                **action_instance.get_controls())

    def get_axiom_instances(self):
        self.axiom_from_derived = defaultdict(list)
        for axiom in self.axioms:
            values = self.negative_values if (
                axiom.constraint.constraint in self.test_constraints) else self.constraint_values
            for instance in axiom.get_instances(values):
                self.axiom_from_derived[instance.derived].append(instance)
                yield instance

    def get_action_instances(self):

        for action in self.actions:
            for instance in action.get_instances(self.constraint_values):
                new_derived = []
                for axiom, derived in zip(instance.lifted.axioms, instance.derived):
                    if axiom.value and derived not in self.axiom_from_derived:
                        new_derived = None
                        break
                    elif not axiom.value and derived not in self.axiom_from_derived:
                        pass
                    else:
                        new_derived.append(derived)
                if new_derived is None:
                    continue
                instance.derived = new_derived
                self.set_cost(instance)
                yield instance

    def get_sas_problem(self):
        axiom_instances = list(self.get_axiom_instances())
        action_instances = list(self.get_action_instances())
        return SASProblem(self.initial, self.goal,
                          action_instances, axiom_instances)

    def sample(self, generator):
        output_list, element_list = next(generator)
        for atom in element_list:
            self._add_constraint(atom)
        if isinstance(generator.sampler, Test) and (not element_list):

            for atom in generator.prepare_atoms(tuple()):
                if atom.constraint not in self.negative_values:
                    self.negative_values[atom.constraint] = set()
                self.negative_values[atom.constraint].add(atom)
        return output_list

    def sample_lazy_queue(self, num_samples):
        if num_samples is None:
            num_samples = len(self.lazy_queue)
        for _ in xrange(num_samples):
            if not self.lazy_queue:
                return
            generator = self.lazy_queue.popleft()
            self.sample(generator)
            if not generator.exhausted:
                self.lazy_queue.append(generator)

    def _sample_greedy_queue(self):
        while self.greedy_queue:
            generator = self.greedy_queue.popleft()
            self.sample(generator)
            if not generator.exhausted:
                self.greedy_queue.append(generator)

    def _add_generator(self, generator):
        if generator not in self.generators:
            self.generators.add(generator)
            if generator.greedy:
                self.greedy_queue.append(generator)
                self._sample_greedy_queue()
            else:
                self.lazy_queue.append(generator)

    def _update_generators(self, new_atom):
        for sampler, i in self.samplers_from_constraint[new_atom.constraint]:
            values = [self.constraint_values.get(c, []) if i != j else [new_atom]
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

    def _add_atom(self, new_atom):
        if new_atom.constraint not in self.constraint_values:
            self.constraint_values[new_atom.constraint] = set()
        elif new_atom in self.constraint_values[new_atom.constraint]:
            return
        self.constraint_values[new_atom.constraint].add(new_atom)
        self._update_generators(new_atom)

    def _add_constraint(self, new_atom):
        for var, value in new_atom.items():
            if not isinstance(value, Parameter):
                self._add_atom(Value(C[var, value]))
        if (new_atom.constraint.constraint_type == Equal) or any(isinstance(val, Parameter) for val in new_atom.parameters):
            return
        self._add_atom(new_atom)

    def __repr__(self):
        s = '{} | Generators: {:d} | Constraints:'.format(
            self.__class__.__name__, len(self.generators))
        for constraint in sorted(self.constraint_values):
            s += '\n{}: {:d}'.format(constraint,
                                     len(self.constraint_values[constraint]))
        return s

    def __len__(self):
        return sum([0] + [len(values) for values in self.constraint_values.values()])


def update_plan(space, best_plan, search_options, search_time):

    sas_problem = space.get_sas_problem()
    print 'Iteration: {} | Atoms: {} | Actions: {} | Axioms: {} | Cost: {} | Time: {}'.format(
        space.iterations, len(space), len(
            sas_problem.actions), len(sas_problem.axioms),
        get_cost(best_plan), (time.time() - space.start_time))
    solution = solve_sas(sas_problem, options=search_options,
                         max_time=search_time, max_cost=get_cost(best_plan))

    if solution is not None:
        plan = solution[:-1]
        if get_cost(plan) < get_cost(best_plan):
            print 'New best plan! Length: {} | Cost: {}'.format(len(plan), get_cost(plan))
            return plan
    return best_plan


def negative_incremental(fts_problem, num_samples=None, max_time=INF, search_options='ff_lazy', max_search_time=5, greedy=True,
                         max_constraints=1, post_process=False, debug=False):
    check_validity(fts_problem)
    initial, goal, clauses = transform_goal(fts_problem)
    space = SampleSpace(initial, goal, clauses, fts_problem,
                        max_constraints=max_constraints)
    if debug:
        print len(space.actions), space.actions
        print len(space.axioms), space.axioms
    best_plan = None
    while (time.time() - space.start_time) <= max_time:
        space.iterations += 1
        if debug:
            print space
        search_time = max_time - (time.time() - space.start_time)
        if space.lazy_queue:
            search_time = min(max_search_time, search_time)

        best_plan = update_plan(space, best_plan, search_options, search_time)
        if (not space.lazy_queue) or ((best_plan is not None) and greedy):
            break
        space.sample_lazy_queue(num_samples)
    if post_process and (best_plan is not None):
        best_plan = update_plan(space, best_plan, 'ff_astar', max_search_time)
    if debug:
        print_plan(best_plan)
        print space
    return get_controls(best_plan)
