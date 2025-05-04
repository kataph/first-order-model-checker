from typing import Any
from model import Model

from lark import Tree, Transformer
from lark.visitors import Visitor, Interpreter

from functools import partialmethod, partial, wraps

from model import prover9_parser


from basic_formulas_manipulation import ToReversePrenexCNF, P9FreeVariablesExtractor, ToPrenexCNF, ToUniqueVariables, BINARY_OPS, dual_quantifier, dual_op, treeExplainer, RemoveLines, ToString

EXAMPLE_AXIOMS = [
    "(exists X all Y lec(Y) -> att(X,Y)).",
    "(exists X all Y ( - P(X,Y) | Q(X,Y))).",
    "(all X all Y lec(Y) -> att(X,Y)).",
    "(att(X,Y)).",
    "(- exists X (B(X) & - - - - att(X,Y))).",
] 

# class LogicFormulaTransformer(Transformer):
#     def __init__(self, visit_tokens = True):
#         super().__init__(visit_tokens)
def add_rule_graphic_execution_in_place(rule):
    def wrapper(*args, **kwargs):
        new_tree = rule(*args, **kwargs)
        print(f"applying {rule.__name__}, got")
        treeExplainer(new_tree)
        return new_tree
    globals()[rule.__name__] = wrapper
    globals()[rule.__name__].__name__ = rule.__name__

def equivalent_to_existential_quantifier(self, inputs, param = "universal_quantification") -> Tree:
    """all X phi --> - exists X - phi \n
    inputs = [X: variable, phi: Tree]"""
    quantified_variable, quantified_formula = inputs
    return Tree("negation", [Tree("existential_quantification", [quantified_variable, Tree("negation", [quantified_formula])])])

def reduce_to_existential_quantifier(self, inputs) -> Tree:
    """all X phi --> exists X phi \n
    inputs = [X: variable, phi: Tree]"""
    return Tree("existential_quantification", inputs)

def introduce_dom(self, children, param = "negation") -> Tree:
    """- atom(X) -> dom(X) """
    negated_formula = children[0]
    if hasattr(negated_formula, "data") and negated_formula.data in ["predicate", "equality_atom"]:
        if negated_formula.data == "predicate":
            predicate_symbol, *term_list = negated_formula.children
            if self.ranged_variable in [str(t) for t in term_list]:
                return Tree("dom", [self.ranged_variable])
        if negated_formula.data == "equality_atom":
            left, right = negated_formula.children
            if self.ranged_variable in [str(left), str(right)]:
                return Tree("dom", [self.ranged_variable])
    return Tree(param, children)



def double_negation_cancel(self, children, param = "negation") -> Tree:
        negated_formula = children[0]
        if negated_formula.data in ["negation", "negation_exc"]:
            doubly_negated_formula = negated_formula.children[0]
            return doubly_negated_formula
        return Tree(param, children)
def remove_negation_from_empty(self, children, param = "negation") -> Tree:
    negated_formula = children[0]
    if negated_formula.data in ["empty"]:
        return negated_formula
    return Tree(param, children)
def commute_negation_with_existential(self, children, param = "negation") -> Tree:
    """- exists phi --> exists - phi \n
        children = [exists phi]"""
    negated_formula = children[0]
    if negated_formula.data in ["existential_quantification"]:
        quantified_variable, quantified_formula = negated_formula.children
        return Tree("existential_quantification", [quantified_variable, Tree("negation",[quantified_formula])])
    return Tree(param, children)

def delete_empty_from_binary(self, children, param: str) -> Tree:
    """empty [binary_op] anything --> anything  \n
    inputs = [left, right] \n
    param = binary_op: str"""
    left, right = children
    if left.data == "empty":
        return right
    if right.data == "empty":
        return left
    return Tree(param, children)

def dom_cancellation(self, children, param: str) -> Tree:
    """dom(X) and phi(X) --> phi(X); otherwise keep the same \n
    inputs = [left, right]
    """
    left, right = children
    if left.data == "dom" and self.ranged_variable in self.freeVars.extract_free_variables_and_signature(right)[0]:
        return right
    if right.data == "dom" and self.ranged_variable in self.freeVars.extract_free_variables_and_signature(left)[0]:
        return left
    return Tree("conjunction", children)
def dom_absorption(self, children, param: str) -> Tree:
    """dom(X) or phi(X) --> dom(X); - dom(X) --> dom(X) otherwise keep the same \n
    inputs = [left, right] if param = disjunction
    inputs = [negated_formula] if param = negation
    """
    if param == "disjunction":
        left, right = children
        if left.data == "dom":
            return left
        if right.data == "dom":
            return right
        return Tree(param, children)
    if param == "negation":
        negated_formula = children[0]
        if negated_formula.data == "dom":
            return negated_formula
        return Tree(param, children)
    
def introduce_empty(self, children, param: str):
    """atom -> empty if ranged variable not in atom"""
    if param == "predicate":
        predicate_symbol, *term_list = children
    if param == "equality_atom":
        term_list = children
    if self.ranged_variable not in [str(t) for t in term_list]:
        return Tree("empty", [])
    return Tree(param, children)
def remove_useless_quantification(self, inputs, param: str) -> Tree:
    """[quantifier] X phi --> phi, if X not in free variables of phi; otherwise keep the same \n
    inputs = [X, phi] \n
    param = quantifier: str"""
    quantified_variable, quantified_formula = inputs
    if not str(quantified_variable) in self.freeVars.extract_free_variables_and_signature(quantified_formula)[0]:
        return quantified_formula
    else: 
        return Tree(param, [quantified_variable, quantified_formula])
    
def introduce_cond(self, inputs, param: str) -> Tree:
    """Atom -> 'cond', if ranged variable appears in Atom, else keep the same"""
    if param == "predicate":
        predicate_symbol, *term_list = inputs
    if param == "equality_atom":
        term_list = inputs
    if self.ranged_variable in [str(t) for t in term_list]:
        return Tree("cond", [])
    return Tree(param, inputs)
def remove_negation_from_cond(self, children, param = "negation") -> Tree:
    """- 'cond'Ato -> 'cond'"""
    negated_formula = children[0]
    if negated_formula.data in ["cond"]:
        return negated_formula
    return Tree(param, children)
def delete_cond_from_disjunction(self, children, param = "disjunction") -> Tree:
    """'cond' or Atom  --> Atom"""
    left, right = children
    if left.data == "cond":
        return right
    if right.data == "cond":
        return left
    return Tree(param, children)


rule_list = [equivalent_to_existential_quantifier,
reduce_to_existential_quantifier,
introduce_dom,
double_negation_cancel,
remove_negation_from_empty,
commute_negation_with_existential,
delete_empty_from_binary,
dom_cancellation,
dom_absorption,
introduce_empty,
remove_useless_quantification,]

# # this will add the decorator programmatically
# for i,rule in enumerate(rule_list):
#     add_rule_graphic_execution_in_place(rule)


delete_empty_from_disjunction=partial(delete_empty_from_binary, param = "disjunction")
dom_absorption_from_disjunction=partial(dom_absorption, param = "disjunction")
dom_absorption_from_negation=partial(dom_absorption, param = "negation")

# TODO: use this way instead?
def to_method(func):
    @wraps(func) 
    def wrapper(self, *args, **kwargs): 
        return func(*args, **kwargs)
    return wrapper


def rule_serialization(self, inputs, rules: list[callable], param) -> Tree:
    """compose rules in series from the first to the last. 
    Returns the output of the first rule that affects the node."""
    old_tree = Tree(param, children=inputs)
    for rule in rules:
        new_tree: Tree = rule(self, inputs, param)
        if new_tree != old_tree:
            return new_tree
    assert old_tree == new_tree
    return old_tree


class ExistentialFormulaTransformer(Transformer):
    """Transformer to manipulate an existential formula. If the formula is not in the shape (exists X phi) an error will be raised.
        For example, (- A(x,y) and exists B(z)) -> error"""
    def __init__(self, visit_tokens = True):
        super().__init__(visit_tokens)
        self.freeVars = P9FreeVariablesExtractor()
        self.toPCNF = ToPrenexCNF()
        self.commutes = {"existential_quantification":"disjunction", "universal_quantification":"conjunction"}
        self.CNFminiscoper = ToReversePrenexCNF()
        self.stringer = ToString()
        self.remover = RemoveLines()

    def check_if_formula_is_existential(self,tree):
        if not (len(tree.children) == 2 and tree.data == "existential_quantification"):
            tree = self.remover.transform(tree)
            if not (len(tree.children) == 2 and tree.data == "existential_quantification"):
                raise TypeError(f"Formula not in shape 'exists x phi' (not even trying to remove start/lines/line syntax nodes)! Actual shape is {self.stringer.visit(tree)}")
            else:
                print(f"Formula was in shape 'exists x phi' plus some additional start/lines/line syntax nodes that I removed! Current shape is now {self.stringer.visit(tree)}")

    def check_if_quantification_is_useless(self, ranged_variable, ranged_formula):
        free_variables_in_ranged_formula = self.freeVars.extract_free_variables_and_signature(ranged_formula)[0]
        if not self.ranged_variable in free_variables_in_ranged_formula:
            raise TypeError(f"Formula is in shape 'exists {self.ranged_variable} phi'! However, {ranged_variable} is not a free variable in phi! Free variables of phi are {free_variables_in_ranged_formula}")
    
    def adjust_transform_repeatedly(self, tree):
        self.check_if_formula_is_existential(tree)
        
        ranged_variable, ranged_formula = tree.children
        self.ranged_variable = str(ranged_variable)
        
        self.check_if_quantification_is_useless(ranged_variable, ranged_formula)
        
        CNFminiscoped_ranged_formula = self.CNFminiscoper.adjust_transform_repeatedly(ranged_formula)
        if CNFminiscoped_ranged_formula != ranged_formula:
            print(f"Attention: the fomula had shape 'exists x phi(x)'. Precisely phi = '{self.stringer.visit(ranged_formula)}'. However, in such a formula phi(x) is not CNFminiscoped. I have CNFminiscoped it. Phi is now: {self.stringer.visit(CNFminiscoped_ranged_formula)}")

        oldtree = CNFminiscoped_ranged_formula
        #print("Attached polarity to nodes of AST tree of ranged formula in CNF miniscoped form")
        #treeExplainer(oldtree)
        newtree = self.transform(oldtree)
        while newtree != oldtree:
            oldtree = newtree
            newtree = self.transform(oldtree)
        return newtree
    
class GetRange(ExistentialFormulaTransformer):
    """Get range of a formula. If the formula is not in the shape (exists X phi) an error will be raised.
        For example, (- A(x,y) and exists B(z)) -> error, (exists x all y lec(y) -> att(x,y)) -> range: exists y att(x,y)"""
    def __init__(self):
        super().__init__()
    
    universal_quantification = reduce_to_existential_quantifier
    existential_quantification = partialmethod(remove_useless_quantification, param = "existential_quantification")
    def disjunction(self, children):
        """empty or Atom --> Atom; dom(X) or Phi --> dom(X)"""
        return rule_serialization(self, inputs = children, rules = [delete_empty_from_binary, dom_absorption], param = "disjunction")
    # It can also be done with one-liner: but the alternative is clearer
    # disjunction = partialmethod(rule_serialization, rules = [delete_empty_from_binary, dom_absorption], param = "disjunction")
    disjunction_exc = disjunction
    
    def conjunction(self, children):
        """dom(X) and phi(X) --> phi(X); empty and phi --> phi; otherwise keep the same"""
        # dom_cancelled_tree = dom_cancellation(self, children)
        # if hasattr(dom_cancelled_tree, "data") and dom_cancelled_tree.data == "conjunction":
        #     return partialmethod(delete_empty_from_binary, param = "conjunction")(self, dom_cancellation.children)
        # else:
        #     return dom_cancelled_tree
        return rule_serialization(self, inputs = children, rules = [dom_cancellation, partialmethod(delete_empty_from_binary, param = "conjunction")], param = "conjunction")
    conjunction_exc = conjunction
    
    def negation_exc(self, children):
        """- - phi --> phi; - empty --> empty; - exists y G --> exists y - G (yes, it is right this way)"""
        return rule_serialization(self, inputs = children, rules = [double_negation_cancel, remove_negation_from_empty, commute_negation_with_existential, introduce_dom, partialmethod(dom_absorption, param = "negation")], param = "negation")
    negation = negation_exc

    predicate = partialmethod(introduce_empty, param = "predicate")
    equality_atom = partialmethod(introduce_empty, param = "equality_atom")

class GetCoRange(ExistentialFormulaTransformer):
    """Get co-range of a formula. If the formula is not in the shape (exists X phi) an error will be raised.
        For example, (- A(x,y) and exists B(z)) -> error, (exists x all y lec(y) -> att(x,y)) -> co-range: all y - lec(y)"""
    def __init__(self):
        super().__init__()
    
    def adjust_transform_repeatedly(self, tree):
        finalized_tree: Tree = super().adjust_transform_repeatedly(tree)
        if len(list(finalized_tree.find_data('cond'))) > 0:
            return Tree("false", [])
        else:
            return finalized_tree
    
    existential_quantification = partialmethod(remove_useless_quantification, param = "existential_quantification")
    existential_quantification = partialmethod(remove_useless_quantification, param = "existential_quantification")
    disjunction = partialmethod(delete_cond_from_disjunction, param = "disjunction")
    disjunction_exc = disjunction
    
    def negation_exc(self, children):
        """- - phi --> phi; - cond --> cond"""
        return rule_serialization(self, inputs = children, rules = [double_negation_cancel, remove_negation_from_cond], param =  "negation")
    negation = negation_exc

    predicate = partialmethod(introduce_cond, param = "predicate")
    equality_atom = partialmethod(introduce_cond, param = "equality_atom")

def get_range_corange_form(ast: Tree) -> Tree:
    range = GetRange().adjust_transform_repeatedly(ast)
    corange = GetCoRange().adjust_transform_repeatedly(ast)
    ranged_variable, ranged_formula = ast.children
    if corange == Tree("false", []):
        return Tree("existential_quantification", [ranged_variable, Tree("conjunction", [range, ranged_formula])])
    else:
        return Tree("disjunction", [corange, Tree("existential_quantification", [ranged_variable, Tree("conjunction", [range, ranged_formula])])])

def get_existential_bound_form(ast: Tree) -> Tree:
    range = GetRange().adjust_transform_repeatedly(ast)
    corange = GetCoRange().adjust_transform_repeatedly(ast)
    ranged_variable, ranged_formula = ast.children
    if corange == Tree("false", []):
        return Tree("existential_quantification_bounded", [ranged_variable, Tree("bound", [range]), ranged_formula])
    else:
        return Tree("disjunction", [corange, Tree("existential_quantification_bounded", [ranged_variable, Tree("bound", [range]), ranged_formula])])

def get_universal_bound_form(ast: Tree) -> Tree:

    def check_if_formula_is_universal(tree: Tree):
        if not (len(tree.children) == 2 and tree.data == "universal_quantification"):
            tree = RemoveLines().transform(tree)
            if not (len(tree.children) == 2 and tree.data == "universal_quantification"):
                raise TypeError(f"Formula not in shape 'all x phi' (not even trying to remove start/lines/line syntax nodes)! Actual shape is {ToString().visit(tree)}")
            else:
                print(f"Formula was in shape 'all x phi' plus some additional start/lines/line syntax nodes that I removed! Current shape is now {ToString().visit(tree)}")

    check_if_formula_is_universal(ast)
    ranged_variable, ranged_formula = ast.children
        
    existential_ast = Tree("existential_quantification", [ranged_variable, Tree("negation", [ranged_formula])])
    existential_range = GetRange().adjust_transform_repeatedly(existential_ast)
    existential_corange = GetCoRange().adjust_transform_repeatedly(existential_ast)
    range = ToReversePrenexCNF().adjust_transform_repeatedly(Tree("negation", [existential_range]))
    corange = ToReversePrenexCNF().adjust_transform_repeatedly(Tree("negation", [existential_corange]))
    if corange == Tree("true", []):
        return Tree("universal_quantification_bounded", [ranged_variable, Tree("bound", [range]), ranged_formula])
    else:
        return Tree("conjunction", [corange, Tree("universal_quantification_bounded", [ranged_variable, Tree("bound", [range]), ranged_formula])])


asts = [RemoveLines().transform(prover9_parser.parse(example_axiom)) for example_axiom in EXAMPLE_AXIOMS]
miniscopeAsts = [ToReversePrenexCNF().adjust_transform_repeatedly(ast) for ast in asts]

treeExplainer(asts[0])
# range0 = GetRange().adjust_transform_repeatedly(asts[0])
# corange0 = GetCoRange().adjust_transform_repeatedly(asts[0])
# treeExplainer(range0)
# treeExplainer(corange0)
# canonical = get_range_corange_form(asts[0])
# treeExplainer(canonical)
treeExplainer(get_existential_bound_form(asts[0]))


treeExplainer(asts[1])
# range1 = GetRange().adjust_transform_repeatedly(asts[1])
# corange1 = GetCoRange().adjust_transform_repeatedly(asts[1])
# treeExplainer(range1)
# treeExplainer(corange1)
# canonical = get_range_corange_form(asts[1])
# treeExplainer(canonical)
treeExplainer(get_existential_bound_form(asts[1]))



