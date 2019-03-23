import pyrsistent as p
import z3

from .utils import z3_const


class Component(p.PClass):
    name = p.field(type=str)
    domain = p.pvector_field(item_type=type)
    ret_type = p.field(mandatory=True, type=type)
    function = p.field(mandatory=True, type=object)
    spec = p.field(initial=None, mandatory=True)


class Example(p.PClass):
    inputs = p.pvector_field(object)
    output = p.field(mandatory=True, type=object)


def example(inputs, output):
    return Example(inputs=p.pvector(inputs), output=output)


class Lineno(p.PClass):
    get = p.field(mandatory=True, type=object)


def make_lineno(no, ctx):
    get = z3.Int(f'l_{no}', ctx)
    return Lineno(get=get)


class Local(p.PClass):
    get = p.field(mandatory=True, type=object)
    lineno = p.field(mandatory=True, type=Lineno)


def make_local(typ, ix, lineno, ctx):
    get = z3_const(ctx, typ, 'c', ix)
    lineno = make_lineno(lineno, ctx)

    return Local(get=get, lineno=lineno)


class Input(p.PClass):
    from_example = p.pmap_field(key_type=Example, value_type=object)
    lineno = p.field(mandatory=True, type=Lineno)


def make_input(examples, input_ix, typ, lineno, ctx):
    from_example = p.pmap((example, z3_const(ctx, typ, 'i', input_ix, n))
                          for n, example in enumerate(examples, 1))
    lineno = make_lineno(lineno, ctx)

    return Input(from_example=from_example, lineno=lineno)


class Output(p.PClass):
    from_example = p.pmap_field(key_type=Example, value_type=object)
    lineno = p.field(mandatory=True, type=Lineno)


def make_output(examples, output_ix, typ, lineno, ctx):
    from_example = p.pmap((example, z3_const(ctx, typ, 'o', output_ix, n))
                          for n, example in enumerate(examples, 1))
    lineno = make_lineno(lineno, ctx)

    return Output(from_example=from_example, lineno=lineno)


class Hole(p.PClass):
    from_example = p.pmap_field(key_type=Example, value_type=object)
    lineno = p.field(mandatory=True, type=Lineno)


def make_hole(examples, component_ix, domain_ix, typ, lineno, ctx):
    from_example = p.pmap(
        (example, z3_const(ctx, typ, 'h', component_ix, example_ix, domain_ix))
        for example_ix, example in enumerate(examples, 1))
    lineno = make_lineno(lineno, ctx)

    return Hole(from_example=from_example, lineno=lineno)


class ProgramLine(p.PClass):
    output = p.field(mandatory=True, type=Output)
    component = p.field(mandatory=True, type=Component)
    holes = p.pvector_field(item_type=Hole)


class Program(p.PClass):
    locals_ = p.pvector_field(item_type=Local)
    inputs = p.pvector_field(item_type=Input)
    lines = p.pvector_field(item_type=ProgramLine)


class UnplugableComponents(Exception):
    pass


class UnusableInput(Exception):
    pass


class SynthesisFailure(Exception):
    def __init__(self, ucores=p.pmap()):
        self.ucores = ucores


class Config(p.PRecord):
    library = p.pvector_field(item_type=Component)
    program_min_size = p.field(type=int)
    program_max_size = p.field()
    max_conflicts = p.field()
    local_string_max_len = p.field(type=int)
    fix_lines = p.field(type=bool)
