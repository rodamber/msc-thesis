from anytree import AnyNode, RenderTree
from pyrsistent import PRecord, PVector, field, ny, pvector, v


class Tree(PRecord):
    tag = field(mandatory=True)
    children = field(
        mandatory=True,
        initial=pvector(),
        invariant=lambda cs: (
            (isinstance(cs, PVector), 'not a pvector'),
            (all(isinstance(c, Tree) for c in cs), 'expected pvector of Trees')))


def tree(tag, children=pvector()):
    return Tree(tag=tag, children=children)


def tree2anynode(tree):
    children = ()
    if tree.children:
        children = tuple(tree.children.transform([ny], tree2anynode))
    return AnyNode(tag=str(tree.tag), children=children)


def render(tree):
    return '\n'.join(
        f'{pre}{node.tag}' for pre, _, node in RenderTree(tree2anynode(tree)))


def test_tree():
    x = tree('x')
    y = tree('y')
    z = tree('z', v(x, y))
    w = tree('w', v(z, x))

    any_w = tree2anynode(w)
    assert any_w.height == 2
