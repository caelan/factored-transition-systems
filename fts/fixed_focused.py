import time
from collections import defaultdict

from fts.algorithms import transform_goal, get_cost, get_controls, print_plan
from fts.downward import solve_sas
from fts.incremental import SampleSpace, ConstraintInfo

from fts.samplers import LazySample

INF = float('inf')


class LazySampleSpace(SampleSpace):

    def __init__(self, initial, goal, clauses, problem, max_constraints=1, effort_weight=10, max_effort=1000):
        self.effort_weight = effort_weight
        self.max_effort = max_effort

        self.blocked_generators = set()
        self.real_constraints = set()
        self.generator_from_domain = defaultdict(set)
        self.last_reset = 0
        super(LazySampleSpace, self).__init__(
            initial, goal, clauses, problem, max_constraints)

    def retrace_generators(self, instance, generators):
        for atom in instance.get_domain():
            if atom not in self.real_constraints:
                generator = self.constraint_info[atom].generator
                if (generator is not None) and (generator not in generators):
                    generators.add(generator)
                    self.retrace_generators(generator, generators)

    def is_real_generator(self, generator):
        return all(atom in self.real_constraints for atom in generator.get_domain())

    def set_cost(self, action_instance):
        if (self.problem.cost_fn is None) or all(not isinstance(arg, LazySample)
                                                 for arg in action_instance.get_controls().values()):
            super(LazySampleSpace, self).set_cost(action_instance)
        else:
            action_instance.cost = 0

    def get_action_effort(self, action):

        generators = set()
        self.retrace_generators(action, generators)
        total_effort = 0

        for constraint in action.get_domain():
            info = self.constraint_info[constraint]

        for generator in generators:
            if generator.exhausted:
                total_effort += INF

            if generator in self.blocked_generators:
                total_effort += INF
            total_effort += generator.effort

        return total_effort

    def get_action_instances(self):

        all_actions = super(LazySampleSpace, self).get_action_instances()
        actions = []
        for action in all_actions:
            effort = self.get_action_effort(action)
            if self.max_effort < effort:
                continue

            action.cost += (self.effort_weight * effort)
            actions.append(action)
        return actions

    def _lazy_sample(self, generator):
        info = ConstraintInfo(generator, False, self.calls,
                              self.iterations, self.epochs)

        lazy_samples = tuple(LazySample()
                             for _ in xrange(len(generator.sampler.outputs)))
        for atom in generator.prepare_atoms(lazy_samples):
            self._add_constraint(atom, info)

    def sample(self, generator):

        assert self.is_real_generator(generator)
        self.blocked_generators.add(generator)
        return super(LazySampleSpace, self).sample(generator)

    def _add_generator(self, generator):
        if generator in self.generators:
            return
        self.generators.add(generator)
        if generator.greedy:

            if self.is_real_generator(generator):
                self.greedy_queue.append(generator)
                self._sample_greedy_queue()
            else:
                for atom in generator.get_domain():
                    if atom not in self.real_constraints:
                        self.generator_from_domain[atom].add(generator)
                self._lazy_sample(generator)
        else:
            self._lazy_sample(generator)

    def _add_atom(self, new_atom, info):
        if info.real:
            self.real_constraints.add(new_atom)

            for generator in list(self.generator_from_domain[new_atom]):
                self.generator_from_domain[new_atom].remove(generator)
                if self.is_real_generator(generator):
                    self.greedy_queue.append(generator)
                    self._sample_greedy_queue()
        super(LazySampleSpace, self)._add_atom(new_atom, info)

    def _get_plan_instances(self, solution):
        states = [self.initial]
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

        generators = set()
        for instance in self._get_plan_instances(solution):
            self.retrace_generators(instance, generators)
        return generators


def fixed_focused(fts_problem, num_samples=None, max_time=INF, max_search_time=30, search_options='ff_lazy', effort_weight=10, max_constraints=1,
                  use_queue=False, single_call=False, greedy=True, debug=True):
    assert greedy or (effort_weight == 0)
    initial, goal, clauses = transform_goal(fts_problem)

    space = LazySampleSpace(initial, goal, clauses, fts_problem, max_constraints=max_constraints,
                            effort_weight=effort_weight)
    space.epochs += 1
    best_plan = None
    while (time.time() - space.start_time) <= max_time:
        space.iterations += 1
        space.sample_lazy_queue(num_samples)
        sas_problem = space.get_sas_problem()
        elapsed_time = time.time() - space.start_time
        print 'Iteration: {} | Epoch: {} | Atoms: {} | '              'Actions: {} | Axioms: {} | Blocked: {} | Time: {}'.format(
            space.iterations, space.epochs, len(space),
            len(sas_problem.actions), len(sas_problem.axioms),
            len(space.blocked_generators), elapsed_time)
        solution = solve_sas(sas_problem, options=search_options,
                             max_time=min(max_search_time, max_time - elapsed_time), max_cost=get_cost(best_plan))
        if solution is None:
            if (not use_queue and not space.blocked_generators) or (use_queue and not space.lazy_queue):
                break
            if not use_queue:
                space.blocked_generators = set()
            space.epochs += 1
            space.last_reset = space.iterations
            continue
        print 'Length: {} | Cost: {}'.format(len(solution), get_cost(solution))
        if debug:
            print_plan(solution)

        generators = space.get_plan_generators(solution)
        if not generators:
            plan = solution[:-1]
            if get_cost(plan) < get_cost(best_plan):
                print 'New best plan! Length: {} | Cost: {}'.format(len(plan), get_cost(plan))
                best_plan = plan
            if greedy:
                break
            else:
                continue

        first_generators = filter(space.is_real_generator, generators)
        if debug:
            print first_generators
        assert first_generators
        for generator in first_generators:
            assert not generator.greedy
            space.sample(generator)
            print generator, generator.exhausted, generator.calls
            if use_queue and not generator.exhausted:
                space.lazy_queue.append(generator)
            if single_call:
                break

    return get_controls(best_plan)
