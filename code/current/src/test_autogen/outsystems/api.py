import xml.etree.ElementTree as ET

import pyrsistent as p


class Function(p.PRecord):
    name = p.field(mandatory=True, type=str)
    ret_type = p.field(mandatory=True, type=str)
    domain = p.pvector_field(str)


def build(in_):
    '''
    Builds a very simple database of the OutSystems expressions API with names
    and type signatures.
    '''

    root = ET.parse(in_)
    functions = root.iter('Function')

    for f in functions:
        name = f.get('name')
        parameters = p.pvector(f.findall('Parameter'))

        yield name, Function(
            name=name,
            ret_type=f.get('retType'),
            domain=p.pvector(map(lambda x: x.get('type'), parameters)))
