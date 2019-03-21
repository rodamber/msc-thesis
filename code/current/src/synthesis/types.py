import pyrsistent as p


class Component(p.PClass):
    name = p.field(type=str)
    domain = p.pvector_field(item_type=type)
    ret_type = p.field(mandatory=True, type=type)
    function = p.field(mandatory=True, type=object)


class Example(p.PClass):
    inputs = p.pvector_field(object)
    output = p.field(mandatory=True, type=object)


def example(inputs, output):
    return Example(inputs=p.pvector(inputs), output=output)


class Lineno(p.PClass):
    get = p.field(mandatory=True, type=object)


class Const(p.PClass):
    get = p.field(mandatory=True, type=object)
    lineno = p.field(mandatory=True, type=Lineno)


class Input(p.PClass):
    map = p.pmap_field(key_type=Example, value_type=object)
    lineno = p.field(mandatory=True, type=Lineno)


class Output(p.PClass):
    map = p.pmap_field(key_type=Example, value_type=object)
    lineno = p.field(mandatory=True, type=Lineno)


class Hole(p.PClass):
    map = p.pmap_field(key_type=Example, value_type=object)
    lineno = p.field(mandatory=True, type=Lineno)


class ProgramLine(p.PClass):
    output = p.field(mandatory=True, type=Output)
    component = p.field(mandatory=True, type=Component)
    holes = p.pvector_field(item_type=Hole)


class Program(p.PClass):
    consts = p.pvector_field(item_type=Const)
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
    timeout = p.field()


