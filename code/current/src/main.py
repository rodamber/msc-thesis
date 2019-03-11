from synthesis.outsystems.parser import parse
from synthesis.outsystems.type_infer import type_infer_leaves

if __name__ == '__main__':
    pass

tree = parse('substr("outsystems.com", 0, index("outsystems.com", "."))')
type_infer_leaves(tree)
