from fts.system import Value, C, I, O, Constraint, Parameter


class LazySample(object):

    def __init__(self, sampler, inputs, var):
        self.sampler = sampler
        self.inputs = inputs
        self.var = var

    def __repr__(self):

        return '?{}'.format(self.var)


class Generator(object):

    def __init__(self, sampler, input_values):
        self.sampler = sampler
        assert len(self.sampler.inputs) == len(input_values)
        self.input_values = tuple(input_values)
        self.generator = None
        self.exhausted = False
        self.calls = 0
        self.lazy_outputs = tuple(LazySample(
            sampler, self.input_values, var) for var in self.sampler.outputs)

    @property
    def greedy(self):
        return self.sampler.greedy

    @property
    def effort(self):

        return self.sampler.effort

    def get_domain(self):
        return tuple(self.sampler.prepare_atom(a, self.input_values)
                     for a in self.sampler.augmented_domain)

    def prepare_atoms(self, output_values):
        output_list = []
        assert len(self.sampler.outputs) == len(output_values)
        for i, val in enumerate(output_values):
            var = self.sampler.outputs[i]
            output_list.append(Value(C[var, val]))
        for atom in self.sampler.constraints:
            output_list.append(self.sampler.prepare_atom(
                atom, self.input_values, output_values))
        return output_list

    def lazy_next(self):
        if self.exhausted:
            return [], []
        output_values = self.sampler.lazy_outputs if self.sampler.shared else self.lazy_outputs
        return [output_values], self.prepare_atoms(output_values)

    def next(self, **kwargs):
        assert not self.exhausted
        if self.generator is None:
            self.generator = self.sampler.generator_fn(*self.input_values)
        self.calls += 1
        output_list = []
        element_list = []
        try:
            output_list += list(next(self.generator))
        except StopIteration:
            self.exhausted = True
        for output_values in output_list:
            element_list += self.prepare_atoms(output_values)
        return output_list, element_list

    def __eq__(self, other):
        return type(self) == type(other) and (self.sampler == other.sampler) and (self.input_values == other.input_values)

    def __ne__(self, other):
        return not (self == other)

    def __hash__(self):
        return hash((type(self), self.sampler, self.input_values))

    def __repr__(self):
        return 'g({})=><{},{}>'.format(','.join(map(repr, self.input_values)), self.sampler.outputs,
                                       [c.constraint.constraint_type for c in self.sampler.constraints])


class Function(Generator):

    def next(self, **kwargs):
        assert not self.exhausted
        self.calls += 1
        output_list = list(self.sampler.function_fn(*self.input_values))
        element_list = []
        for output_values in output_list:
            element_list += self.prepare_atoms(output_values)
        self.exhausted = True
        return output_list, element_list


class AdvancedGenerator(Generator):

    def next(self, **kwargs):

        assert not self.exhausted
        if self.generator is None:
            self.generator = self.sampler.generator_fn(*self.input_values)
        self.calls += 1
        output_list = []
        element_list = []
        try:
            element_list += list(next(self.generator))
        except StopIteration:
            self.exhausted = True
        return output_list, element_list


class SamplerInterface(object):
    GenClass = None

    def __init__(self, inputs, domain, outputs, constraints, greedy=False, effort=1, shared=False, order=0):
        self.inputs = tuple(inputs)
        self.domain = tuple(domain)
        self.outputs = tuple(outputs)
        self.constraints = tuple(constraints)
        self.greedy = greedy
        self.effort = effort
        self.shared = shared
        self.order = order
        self.generators = {}
        self.lazy_outputs = tuple(LazySample(self, None, var)
                                  for var in self.outputs)

        self._check_valid()
        self._initialize_domain()

    def _check_valid(self):
        for a in self.domain:
            for p in a.parameters:
                if isinstance(p, Parameter):
                    if p.set == I:
                        assert 0 <= p.var < len(self.inputs)
                    else:
                        raise ValueError(p)
        for a in self.constraints:
            for p in a.parameters:
                if isinstance(p, Parameter):
                    if p.set == I:
                        assert 0 <= p.var < len(self.inputs)
                    elif p.set == O:
                        assert 0 <= p.var < len(self.outputs)
                    else:
                        raise ValueError(p)

    def _initialize_domain(self):
        self.augmented_domain = list(self.domain)
        parameters = {p for a in self.domain for p in a.parameters}
        for index in xrange(len(self.inputs)):
            param = I[index]
            if param not in parameters:
                self.augmented_domain.append(Value(param))
        self.domain_constraints = []
        for atom in self.augmented_domain:
            variables = [self.inputs[p.var] for p in atom.parameters]
            self.domain_constraints.append(Constraint(
                atom.constraint.constraint_type, variables))

    def input_parameters(self):
        return tuple(I[i] for i in xrange(len(self.inputs)))

    def output_parameters(self):
        return tuple(O[i] for i in xrange(len(self.outputs)))

    def prepare_atom(self, atom, input_values, output_values=tuple()):
        variables, arguments = [], []
        for i, param in enumerate(atom.parameters):
            if isinstance(param, Parameter):
                if param.set == I:
                    variables.append(self.inputs[param.var])
                    arguments.append(input_values[param.var])
                elif param.set == O:
                    variables.append(self.outputs[param.var])
                    arguments.append(output_values[param.var])
                else:
                    raise ValueError(param)
            else:
                variables.append(atom.constraint.variables[i])
                arguments.append(param)
        constraint = Constraint(atom.constraint.constraint_type, variables)
        return constraint(*arguments)

    def is_simple_test(self):

        return (not self.domain) and isinstance(self, Test) and (not self.outputs)

    def get_constraints(self):

        constraints = []
        for element in self.constraints:
            variables = []
            for i, param in enumerate(element.parameters):
                if isinstance(param, Parameter):
                    if param.set == I:
                        variables.append(self.inputs[param.var])
                    elif param.set == O:
                        variables.append(self.outputs[param.var])
                    else:
                        raise ValueError(param)
                else:
                    variables.append(element.constraint.variables[i])
            constraints.append(Constraint(
                element.constraint.constraint_type, variables))
        return constraints

    def __call__(self, input_values, **kwargs):
        input_values = tuple(input_values)
        if input_values not in self.generators:
            self.generators[input_values] = self.GenClass(self, input_values)
        return self.generators[input_values]

    def __repr__(self):
        return 'f({})=><{},{}>'.format(','.join(map(repr, self.inputs)),
                                       self.outputs,
                                       self.constraints)


class Sampler(SamplerInterface):
    GenClass = Generator

    def __init__(self, inputs, domain, outputs, constraints, generator_fn, **kwargs):
        super(Sampler, self).__init__(
            inputs, domain, outputs, constraints, **kwargs)
        self.generator_fn = generator_fn


class AdvancedSampler(SamplerInterface):
    GenClass = AdvancedGenerator

    def __init__(self, inputs, domain, outputs, constraints, generator_fn, **kwargs):
        super(AdvancedSampler, self).__init__(
            inputs, domain, outputs, constraints, **kwargs)
        self.generator_fn = generator_fn


class FunctionSampler(SamplerInterface):
    GenClass = Function

    def __init__(self, inputs, domain, outputs, constraints, function_fn, **kwargs):
        super(FunctionSampler, self).__init__(
            inputs, domain, outputs, constraints, **kwargs)
        self.function_fn = function_fn


class Test(FunctionSampler):

    def __init__(self, inputs, domain, constraints, test_fn, **kwargs):
        def function_fn(*args):
            return [tuple()] if test_fn(*args) else []
        super(Test, self).__init__(inputs, domain,
                                   [], constraints, function_fn, **kwargs)


class Constants(AdvancedSampler):

    def __init__(self, constraints, **kwargs):
        def generator_fn(*args):
            yield constraints
        super(Constants, self).__init__([], [], [],
                                        [], generator_fn, greedy=True, **kwargs)


import numbers

neg_inf_fn = lambda *args: -float('inf')
zero_fn = lambda *args: 0
pos_inf_fn = lambda *args: float('inf')
false_fn = lambda *args: False
true_fn = lambda *args: True


class Interval(object):

    def __init__(self, a, b):
        pass


class Singleton(object):

    def __init__(self, a, b):
        pass


class RealFunction(object):

    def __init__(self, inputs, func, eval_fn, domain=tuple(),
                 lower_fn=neg_inf_fn, upper_fn=pos_inf_fn,
                 **kwargs):
        self.inputs = inputs
        self.func = func
        self.eval_fn = eval_fn
        self.domain = domain
        self.lower_fn = lower_fn
        self.upper_fn = upper_fn

    def call(self, *values, **kwargs):
        value = self.eval_fn()
        assert isinstance(value, numbers.Real)
        return value


class NonNegFunction(RealFunction):

    def __init__(self, inputs, func, eval_fn, domain=tuple(),
                 lower_fn=zero_fn, upper_fn=pos_inf_fn, **kwargs):
        pass


class BooleanFunction(RealFunction):

    def __init__(self, bound_fn, **kwargs):
        super(BooleanFunction, self).__init__()

    def call(self, *args, **kwargs):
        value = self.eval_fn()
        assert value in (False, True)
        return value


class FiniteFunction(RealFunction):
    pass


class Relation(object):

    def __init__(self, inputs, relation, gen_fn, domain=tuple(),
                 **kwargs):
        pass
