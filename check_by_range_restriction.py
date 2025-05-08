from typing import Any, Literal
from model import Model, P9ModelReader

from lark import Token, Tree, Transformer
from lark.visitors import Visitor, Interpreter, visit_children_decor

from functools import partialmethod, partial, wraps
from itertools import product 

from model import prover9_parser
from join_algorithms import Relation, hash_join


from basic_formulas_manipulation import ToReversePrenexCNF, P9FreeVariablesExtractor, ToPrenexCNF, ToUniqueVariables, BINARY_OPS, dual_quantifier, dual_op, treeExplainer, treeExplainerRED, treeExplainerGREEN, RemoveLines, ToString, get_existential_closure

NEUTRAL_ELEMENT_OF_OPERATION = {
    "conjunction": "true",
    "disjunction": "false"
}

OPERATION_THAT_COMMUTES_WITH_QUANTIFICATION = {
    "existential": "disjunction",
    "universal": "conjunction",
}

NEGATION_DUAL_OF = {
    "existential": "universal",
    "universal": "existential",
    "disjunction": "conjunction",
    "conjunction": "disjunction",
    "true": "false",
    "false": "true",
}

EXAMPLE_AXIOMS = [
    "(exists X all Y lec(Y) -> att(X,Y)).",
    "(exists X all Y ( - P(X,Y) | Q(X,Y))).",
    "(U(V) | (exists X all Y ( - P(X,Y) | Q(X,Y)))).",
    "(all X all Y lec(Y) -> att(X,Y)).",
    "(att(X,Y)).",
    "(- exists X (B(X) & - - - - att(X,Y))).",
] 
EXAMPLE_ASTS = [RemoveLines().transform(prover9_parser.parse(example_axiom)) for example_axiom in EXAMPLE_AXIOMS]


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

def reduce_to_existential_quantifier(self, inputs, param = "existential_quantification") -> Tree:
    """all X phi --> exists X phi \n
    inputs = [X: variable, phi: Tree]"""
    return Tree(param, inputs)

def introduce_dom(self, children, param = "negation") -> Tree:
    """- atom(X) -> dom(X) """
    negated_formula = children[0]
    if hasattr(negated_formula, "data") and negated_formula.data in ["predicate", "equality_atom"]:
        if negated_formula.data == "predicate":
            predicate_symbol, *term_list = negated_formula.children
            if self.ranged_variable in [str(t) for t in term_list]:
                return Tree("dom", [Token("VARIABLE", self.ranged_variable)])
        if negated_formula.data == "equality_atom":
            left, right = negated_formula.children
            if self.ranged_variable in [str(left), str(right)]:
                return Tree("dom", [Token("VARIABLE", self.ranged_variable)])
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
    #param = "disjunction" if len(children) == 2 else param = "negation"
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
    quantified_variable, *bound, quantified_formula = inputs
    if not str(quantified_variable) in self.freeVars.extract_free_variables_and_signature(quantified_formula)[0]:
        return quantified_formula
    else: 
        return Tree(param, inputs)
    
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
    """Interpreter to manipulate an existential formula. If the formula is not in the shape (exists X phi) an error will be raised.
        For example, (- A(x,y) and exists B(z)) -> error"""
    def __init__(self, visit_tokens = True):
        super().__init__(visit_tokens)
        self.freeVars = P9FreeVariablesExtractor()
        self.toPCNF = ToPrenexCNF()
        self.CNFminiscoper = ToReversePrenexCNF()
        self.stringer = ToString()
        self.remover = RemoveLines()


    def check_if_quantification_is_useless(self, ranged_variable, ranged_formula):
        free_variables_in_ranged_formula = self.freeVars.extract_free_variables_and_signature(ranged_formula)[0]
        if not self.ranged_variable in free_variables_in_ranged_formula:
            raise TypeError(f"Formula is in shape 'exists {self.ranged_variable} phi'! However, {ranged_variable} is not a free variable in phi! Free variables of phi are {free_variables_in_ranged_formula}")
    
    def adjust_transform_repeatedly(self, tree):
        check_if_formula_is_existential(tree)
        
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
        For example, (- A(x,y) and exists B(z)) -> error, (exists x all y lec(y) -> att(x,y)) -> range: exists y att(x,y). 
        If the `static` input attribute is true the formula returned is the existential closure of the range (except for the ranged variable), otherwise free variable may be present that are inherited by higher-level quantifications"""
    def __init__(self, static: bool = True):
        super().__init__()
        self.static = static 
    
    def adjust_transform_repeatedly(self, tree):
        finalized_tree: Tree = super().adjust_transform_repeatedly(tree)
        if self.static:
            return get_existential_closure(finalized_tree, exceptions={self.ranged_variable})
        else: 
            return finalized_tree

    universal_quantification = reduce_to_existential_quantifier
    existential_quantification = partialmethod(remove_useless_quantification, param = "existential_quantification")
    universal_quantification_bounded = partialmethod(reduce_to_existential_quantifier, param = "universal_quantification_bounded")
    existential_quantification_bounded = partialmethod(remove_useless_quantification, param = "existential_quantification_bounded")
    
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
        return rule_serialization(self, inputs = children, rules = [dom_cancellation, delete_empty_from_binary], param = "conjunction")
    conjunction_exc = conjunction
    
    def negation_exc(self, children):
        """- - phi --> phi; - empty --> empty; - exists y G --> exists y - G (yes, it is right this way)"""
        return rule_serialization(self, inputs = children, rules = [double_negation_cancel, remove_negation_from_empty, commute_negation_with_existential, introduce_dom, dom_absorption], param = "negation")
    negation = negation_exc

    predicate = partialmethod(introduce_empty, param = "predicate")
    equality_atom = partialmethod(introduce_empty, param = "equality_atom")

class GetCoRange(ExistentialFormulaTransformer):
    """Get co-range of a formula. If the formula is not in the shape (exists X phi) an error will be raised.
        For example, (- A(x,y) and exists B(z)) -> error, (exists x all y lec(y) -> att(x,y)) -> co-range: all y - lec(y)
        If the `static` input attribute is true the formula returned is the existential closure of the co-range (except for the ranged variable), otherwise free variable may be present that are inherited by higher-level quantifications"""
    def __init__(self, static: bool = False):
        super().__init__()
        self.static = static 
    
    def adjust_transform_repeatedly(self, tree):
        finalized_tree: Tree = super().adjust_transform_repeatedly(tree)
        if len(list(finalized_tree.find_data('cond'))) > 0:
            return Tree("false", [])
        else:
            if not self.static:
                return finalized_tree
            else: 
                return get_existential_closure(finalized_tree, exceptions={self.ranged_variable})
    
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


def check_if_formula_is_quantification(tree: Tree, quantification_type: Literal["existential", "universal"]) -> None: 
    format_map = {"existential": "exists", "universal": "all"}
    if not ((len(tree.children) == 2 and tree.data == f"{quantification_type}_quantification") or (len(tree.children) == 3 and tree.data == f"{quantification_type}_quantification_bounded")):
        tree = RemoveLines().transform(tree)
        if not ((len(tree.children) == 2 and tree.data == f"{quantification_type}_quantification") or (len(tree.children) == 3 and tree.data == f"{quantification_type}_quantification_bounded")):
            raise TypeError(f"Formula not in shape '{format_map[quantification_type]} x phi' or '{format_map[quantification_type]} (x in B) phi' (not even trying to remove start/lines/line syntax nodes)! Actual shape is {ToString().visit(tree)}")
        else:
            print(f"Formula was in shape '{format_map[quantification_type]} x phi' plus some additional start/lines/line syntax nodes that I removed! Current shape is now {ToString().visit(tree)}")
check_if_formula_is_existential = partial(check_if_formula_is_quantification, quantification_type = "existential")
check_if_formula_is_universal = partial(check_if_formula_is_quantification, quantification_type = "universal")

def get_range_corange(ast: Tree, quantification_type: Literal["existential", "universal"]) -> tuple[Tree, Tree]:
    if quantification_type == "existential":
        range = GetRange().adjust_transform_repeatedly(ast)
        corange = GetCoRange().adjust_transform_repeatedly(ast)
        return range, corange
    elif quantification_type == "universal":
        # Range(all, X, phi) = Range(exists, X, not phi)
        # CoRange(all, X, phi) = not CoRange(exists, X, not phi) # TODO: check if this is correct
        ranged_variable, ranged_formula = ast.children
        existential_ast = Tree("existential_quantification", [ranged_variable, Tree("negation", [ranged_formula])])
        existential_range = GetRange().adjust_transform_repeatedly(existential_ast)
        existential_corange = GetCoRange().adjust_transform_repeatedly(existential_ast)
        range = ToReversePrenexCNF().adjust_transform_repeatedly(existential_range)
        corange = ToReversePrenexCNF().adjust_transform_repeatedly(Tree("negation", [existential_corange]))
        return range, corange


def get_range_corange_form(ast: Tree) -> Tree:
    range = GetRange().adjust_transform_repeatedly(ast)
    corange = GetCoRange().adjust_transform_repeatedly(ast)
    ranged_variable, ranged_formula = ast.children
    if corange == Tree("false", []):
        return Tree("existential_quantification", [ranged_variable, Tree("conjunction", [range, ranged_formula])])
    else:
        return Tree("disjunction", [corange, Tree("existential_quantification", [ranged_variable, Tree("conjunction", [range, ranged_formula])])])

def get_existential_bound_form(ast: Tree) -> Tree:
    check_if_formula_is_existential(ast)
    ranged_variable,*bounding_formula, ranged_formula = ast.children
    if bounding_formula != []: # formula is already in bounded form
        return ast
    range, corange = get_range_corange(ast, quantification_type="existential")
    if corange == Tree("false", []):
        return Tree("existential_quantification_bounded", [ranged_variable, range, ranged_formula])
    else:
        return Tree("disjunction", [corange, Tree("existential_quantification_bounded", [ranged_variable, range, ranged_formula])])

def get_universal_bound_form(ast: Tree) -> Tree:
    check_if_formula_is_universal(ast)
    ranged_variable, *bounding_formula, ranged_formula = ast.children
    if bounding_formula != []: # formula is already in bounded form
        return ast
    
    range, corange = get_range_corange(ast, quantification_type="universal")
    if corange == Tree("true", []):
        return Tree("universal_quantification_bounded", [ranged_variable, range, ranged_formula])
    else:
        return Tree("conjunction", [corange, Tree("universal_quantification_bounded", [ranged_variable, range, ranged_formula])])

class toBoundedMinifiedCNF(Interpreter):
    """Transformer <--TODO to manipulate an existential formula. If the formula is not in the shape (exists X phi) an error will be raised.
        For example, (- A(x,y) and exists B(z)) -> error"""
    def __init__(self):
        super().__init__()
        self.freeVars = P9FreeVariablesExtractor()
        self.toPCNF = ToPrenexCNF()
        self.CNFminiscoper = ToReversePrenexCNF()
        self.stringer = ToString()
        self.remover = RemoveLines()
        self.variablesAdjuster = ToUniqueVariables()

    def __default__(self, tree):
        #return self.visit_children(tree) <- this is the default behavior for Interpreters
        if isinstance(tree, Tree):
            return Tree(tree.data, self.visit_children(tree))
        else:
            return tree # <- to modify if tokens need to be visited
    
    def adjust_transform_repeatedly(self, tree):
        # the formula is CNF minified and corrected for variables.
        CNFminiscoped_ranged_formula = self.CNFminiscoper.adjust_transform_repeatedly(tree)
        if CNFminiscoped_ranged_formula != tree:
            print(f"Attention: the formula was not CNFminiscoped. I have CNFminiscoped it.")

        oldtree = self.variablesAdjuster.adjust_variables(CNFminiscoped_ranged_formula)
        # treeExplainerGREEN(oldtree)
        newtree = self.variablesAdjuster.adjust_variables(self.visit(oldtree))
        # treeExplainerRED(newtree)
        # oldtree = (CNFminiscoped_ranged_formula)
        # newtree = (self.visit(oldtree))
        
        # X = (self.visit(newtree))
        # treeExplainerGREEN(X)
        # X = (self.visit(X))
        # treeExplainerGREEN(X)
        # X = (self.visit(X))
        # treeExplainerRED(X)
        
        while newtree != oldtree:
            oldtree = newtree
            newtree = self.variablesAdjuster.adjust_variables(self.visit(oldtree))
            # newtree = (self.visit(oldtree))
        return newtree

    def quantification(self, tree, quantification_type: Literal["existential", "universal"]):
        range, corange =  get_range_corange(tree, quantification_type)
        ranged_variable, ranged_formula = tree.children
        visited_ranged_formula = self.visit(ranged_formula)
        if corange == Tree(NEUTRAL_ELEMENT_OF_OPERATION[OPERATION_THAT_COMMUTES_WITH_QUANTIFICATION[quantification_type]], []):
            return Tree(f"{quantification_type}_quantification_bounded", [ranged_variable, range, visited_ranged_formula])
        else:
            visited_corange = self.visit(corange)
            return Tree(OPERATION_THAT_COMMUTES_WITH_QUANTIFICATION[quantification_type], [visited_corange, Tree(f"{quantification_type}_quantification_bounded", [ranged_variable, range, visited_ranged_formula])])
    existential_quantification = partialmethod(quantification, quantification_type = "existential")
    universal_quantification = partialmethod(quantification, quantification_type = "universal")
    
    def existential_quantification_bounded(self, tree):
        var, bound, formula = tree.children
        return Tree(tree.data, [var, bound, self.visit(formula)])
    universal_quantification_bounded = existential_quantification_bounded





class evaluateQuantifierBound(Transformer):
    """Given a quantifier bound for a certain variable and formula, it calculates the set of all constants that satisfy the (existential closure of the) formula. E.g. with the model A(a,b).B(a,c).V(a,b,z), the bound {X | exists Y A(X,Y) & exists Z B(X,Z)} is evaluated to {a}.
    Assumes that the bounding formula is existentially closed except for the bounded variable."""
    def __init__(self, ranged_variable, model: Model, visit_tokens = True):
        super().__init__(visit_tokens)
        self.ranged_variable = ranged_variable
        self.model = model

    def true(self, items):
        return Relation((), True) 
    def false(self, items):
        return Relation((), False) 
    
    def dom(self, items):
        ranged_variable = items[0]
        return Relation((ranged_variable,), set((constant,) for constant in self.model.signature.constants))
    
    def equality_atom(self, items):
        """The equality is considered like a predicate"""
        left_member, right_member = items
        tuple_set: set | bool
        tuple_set = set()
        tuple_header = tuple()
        if not isinstance(left_member, Token) or not isinstance(right_member, Token):
            raise AssertionError(f"Either the left member or the right member of the equality atom {items} is not a Token. This should never happen")
        if left_member.type == right_member.type == "VARIABLE":
            tuple_header = (left_member.value, right_member.value)
            for constant in self.model.signature.constants:
                tuple_set.add((constant,constant))
        if left_member.type == "CONSTANT" and right_member.type == "VARIABLE":
            tuple_header = (right_member.value,)
            tuple_set.add((left_member.value,))
        if left_member.type == "VARIABLE" and right_member.type == "CONSTANT":
            tuple_header = (left_member.value,)
            tuple_set.add((right_member.value,))
        if left_member.type == right_member.type == "CONSTANT":
            tuple_set = left_member.value == right_member.value
        if tuple_set == set(): tuple_set = False # Empty tuple set defaults to False
        return Relation(tuple_header,tuple_set)
    
    def predicate(self, items):
        predicate_symbol, *term_list = items
        predicate_symbol = predicate_symbol.value
        tuple_set: set | bool
        tuple_set = set()
        tuple_header = tuple()
        if not all(isinstance(token, Token) for token in term_list): 
            raise AssertionError(f"Found non-token in predicate {predicate_symbol} (one of {term_list}). This should not happen")
        if not "VARIABLE" in (token.type for token in term_list): 
            # only constants
            tuple_set = tuple(token.value for token in term_list) in self.model.ordered_truth_table[predicate_symbol]
        if not "CONSTANT" in (token.type for token in term_list): 
            # only variables
            tuple_header = tuple(token.value for token in term_list)
            for tuple_of_constants in self.model.ordered_truth_table[predicate_symbol]:
                assert len(term_list) == len(tuple_of_constants), f"The predicate {predicate_symbol} has the wrong number of values!"
                tuple_set.add(tuple_of_constants)
        else:
            # there is at least one constant
            indices_of_constants = [i for i,token in enumerate(zip(term_list, )) if token.type=="CONSTANT"]
            tuple_header = tuple(token.value for token in term_list if token.type=="CONSTANT")
            for tuple_of_constants in self.model.ordered_truth_table[predicate_symbol]:
                assert len(term_list) == len(tuple_of_constants), f"The predicate {predicate_symbol} has the wrong number of values!"
                for i in indices_of_constants:
                    if tuple_of_constants[i] != term_list[i].value:
                        continue
                # now the tuple_of_constant matches, in the right positions, all constants present in the term_list. I can then save the constants that match the variables
                tuple_set.add(tuple(constant for token, constant in zip(term_list, tuple_of_constants) if token.type == "VARIABLE"))
        if tuple_set == set(): tuple_set = False # Empty tuple set defaults to False
        return Relation(tuple_header, tuple_set)

    def negation(self, items):
        """This is >>>VERY<<< dangerous if the inner formula has many free variables"""
        if not isinstance(items[0], Relation): 
            raise TypeError("A negation node in a bounding formula received a non-Relation during evaluation. This probably means that the bounding formula is not in existential CNF, while it should be!")
        tuples_from_inner_formula = items[0].tuple_set
        header_from_inner_formula = items[0].tuple_header
        if tuples_from_inner_formula == set(): tuples_from_inner_formula = False
        if isinstance(tuples_from_inner_formula, bool):
            return not tuples_from_inner_formula
        arity = len(header_from_inner_formula)
        tuple_of_all_constants = tuple(self.model.signature.constants)
        tuple_set = set(product(tuple_of_all_constants, repeat = arity)).difference(tuples_from_inner_formula) 
        return Relation(header_from_inner_formula, tuple_set)
    negation_exc = negation

    def conjunction(self, items):
        left_evaluation, right_evaluation = items
        if not (isinstance(left_evaluation, Relation) and isinstance(right_evaluation, Relation)): 
            raise TypeError("A conjunction node in a bounding formula received a non-Relation during evaluation. This probably means that the bounding formula is not in existential CNF, or that it contains subformulas that do not depend on the ranged variable. This should not happen!")
        if left_evaluation.tuple_set == set(): left_evaluation.tuple_set = False
        if right_evaluation.tuple_set == set(): right_evaluation.tuple_set = False

        if False in [left_evaluation.tuple_set, right_evaluation.tuple_set]:
            return Relation(tuple(), False)
        if True == left_evaluation.tuple_set: return right_evaluation
        if True == right_evaluation.tuple_set: return left_evaluation

        left_variables = left_evaluation.tuple_header
        right_variables = right_evaluation.tuple_header

        # if there are no common variables, the join becomes a cartesian product
        if set(left_variables).intersection(right_variables) == set():
            tuple_set = set()
            tuple_header = left_variables+right_variables
            for left_tuple in left_evaluation.tuple_set:
                for right_tuple in right_evaluation.tuple_set:
                    tuple_set.add(left_tuple + right_tuple)
            joined_relation = Relation(tuple_header, tuple_set)
        # if there are common variables, a hash join on the common variables is executed
        elif set(left_variables).intersection(right_variables) != set():
            keys = set(left_variables).intersection(right_variables)
            joined_relation = hash_join(left_evaluation, right_evaluation, keys = tuple(keys))
        return joined_relation
    conjunction_exc = conjunction

    def disjunction(self, items):
        left_evaluation, right_evaluation = items
        if not (isinstance(left_evaluation, Relation) and isinstance(right_evaluation, Relation)): 
            raise TypeError("A conjunction node in a bounding formula received a non-Relation during evaluation. This probably means that the bounding formula is not in minified existential CNF, while it should be!")

        if True in [left_evaluation.tuple_set, right_evaluation.tuple_set]:
            return Relation(tuple(), True)
        if False == left_evaluation.tuple_set: return right_evaluation
        if False == right_evaluation.tuple_set: return left_evaluation

        if not left_evaluation.tuple_header == right_evaluation.tuple_header == (self.ranged_variable,): 
            raise TypeError("A conjunction node in a bounding formula received non-unary/nullary relations or relations having a free variable that is not the ranged variable. This probably means that the bounding formula is not in minified existential CNF, while it should be!")

        # the relations are just e.g. ('X',), {("c1",),("c2",),...} and ('X',), {("c21",),("c22",),...}. So ww just need to take a simple union
        return Relation((self.ranged_variable,), left_evaluation.tuple_set.union(right_evaluation.tuple_set))
    disjunction_exc = disjunction

    def universal_quantification(self, items):
        raise TypeError("Universal quantification should not be encountered in bounding formulas!")
    
    def existential_quantification(self, items):
        quantified_variable, relation_from_inner_formula = items
        if not isinstance(quantified_variable, Token) or not isinstance(relation_from_inner_formula, Relation):
            raise TypeError(f"Something wrong with returned variable or tuples: {quantified_variable} or {relation_from_inner_formula}")
        if quantified_variable == self.ranged_variable:
            raise TypeError(f"Quantified variable {quantified_variable} is the same as the ranged variable! This should not happen.")
        if relation_from_inner_formula.tuple_set == False: return Relation((), False)
        if relation_from_inner_formula.tuple_set == True: return Relation((), True)
        
        if not quantified_variable in relation_from_inner_formula.tuple_header:
            raise TypeError(f"Quantified variable {quantified_variable} does not appear among the variables of the relation from the quantified formula, which are {relation_from_inner_formula.tuple_header}")
        projection_header = tuple(var for var in relation_from_inner_formula.tuple_header if var != quantified_variable)
        projection_indices = tuple(i for i,var in enumerate(relation_from_inner_formula.tuple_header) if var != quantified_variable)
        projection = Relation(projection_header, set())
        for t in relation_from_inner_formula.tuple_set:
            projection.tuple_set.add(tuple(t[i] for i in projection_indices))
        return projection

    def empty(self, items):
        raise TypeError("Encountered 'empty' in a bounding formula. This should never happen!")
    def cond(self, items):
        raise TypeError("Encountered 'cond' in a bounding formula. This should never happen!")
    
    def shouldnt_appear(self, items): 
        raise TypeError("This node should not appear in bounding formulas!")
    entailment = shouldnt_appear
    reverse_entailment = shouldnt_appear
    equivalence_entailment = shouldnt_appear
    entailment_exc = shouldnt_appear
    reverse_entailment_exc = shouldnt_appear
    equivalence_entailment_exc = shouldnt_appear

    car = lambda self, items: items[0]
    start = car
    lines = car
    line = car
    sentence = car
    label = lambda self, items: None


def test_bond_evaluation():
    p9model = P9ModelReader()
    # model = p9model.read_model(prover9_parser.parse("A(a).B(b).E(a,b)."))
    # formula = RemoveLines().transform(prover9_parser.parse("exists Y A(X) & E(X,Y)."))
    model = p9model.read_model(prover9_parser.parse("A(a).B(b).E(a,b).E(b,c).R(c,e).U(e,b)."))
    # formula = RemoveLines().transform(prover9_parser.parse("exists Z exists Y (E(X,Z) & R(Z,Y) & U(Y))."))
    formula = RemoveLines().transform(prover9_parser.parse("((exists Z exists Y (E(X,Z) & R(Z,Y))) | (exists Y2 U(Y2,X)))."))
    evBound = evaluateQuantifierBound("X", model)
    treeExplainer(model)
    treeExplainer(formula)
    x = evBound.transform(formula)
    print(x)

def test_range():
    assert GetRange().adjust_transform_repeatedly(EXAMPLE_ASTS[0]) == Tree("existential_quantification", [Token('VARIABLE', 'Y'), Tree("predicate", [Token("PREDICATE_SYMBOL","att"), Token("VARIABLE","X"), Token("VARIABLE","Y")])]), GetRange().adjust_transform_repeatedly(EXAMPLE_ASTS[0])
    assert GetRange().adjust_transform_repeatedly(GetRange().adjust_transform_repeatedly(EXAMPLE_ASTS[0])) == Tree("existential_quantification", [Token('VARIABLE', 'X'), Tree("predicate", [Token("PREDICATE_SYMBOL","att"), Token("VARIABLE","X"), Token("VARIABLE","Y")])]), GetRange().adjust_transform_repeatedly(EXAMPLE_ASTS[0])
    assert toBoundedMinifiedCNF().adjust_transform_repeatedly(EXAMPLE_ASTS[0]) == Tree('disjunction', [Tree('universal_quantification_bounded', [Token('VARIABLE', 'Y'), Tree('predicate', [Token('PREDICATE_SYMBOL', 'lec'), Token('VARIABLE', 'Y')]), Tree('negation', [Tree('predicate', [Token('PREDICATE_SYMBOL', 'lec'), Token('VARIABLE', 'Y')])])]), Tree('existential_quantification_bounded', [Token('VARIABLE', 'X'), Tree('existential_quantification', [Token('VARIABLE', 'Y1'), Tree('predicate', [Token('PREDICATE_SYMBOL', 'att'), Token('VARIABLE', 'X'), Token('VARIABLE', 'Y1')])]), Tree('universal_quantification_bounded', [Token('VARIABLE', 'Y2'), Tree('predicate', [Token('PREDICATE_SYMBOL', 'lec'), Token('VARIABLE', 'Y2')]), Tree('disjunction', [Tree('negation', [Tree(Token('RULE', 'predicate'), [Token('PREDICATE_SYMBOL', 'lec'), Token('VARIABLE', 'Y2')])]), Tree(Token('RULE', 'predicate'), [Token('PREDICATE_SYMBOL', 'att'), Token('VARIABLE', 'X'), Token('VARIABLE', 'Y2')])])])])])
    
    assert toBoundedMinifiedCNF().adjust_transform_repeatedly(EXAMPLE_ASTS[1]) == Tree('existential_quantification_bounded', [Token('VARIABLE', 'X2'), Tree('dom', [Token('VARIABLE', 'X2')]), Tree('universal_quantification_bounded', [Token('VARIABLE', 'Y'), Tree('existential_quantification', ['X', Tree('predicate', [Token('PREDICATE_SYMBOL', 'P'), Token('VARIABLE', 'X'), Token('VARIABLE', 'Y')])]), Tree('disjunction', [Tree('negation', [Tree(Token('RULE', 'predicate'), [Token('PREDICATE_SYMBOL', 'P'), Token('VARIABLE', 'X2'), Token('VARIABLE', 'Y')])]), Tree(Token('RULE', 'predicate'), [Token('PREDICATE_SYMBOL', 'Q'), Token('VARIABLE', 'X2'), Token('VARIABLE', 'Y')])])])])
    
    assert toBoundedMinifiedCNF().adjust_transform_repeatedly(EXAMPLE_ASTS[2]) == Tree('disjunction', [Tree(Token('RULE', 'predicate'), [Token('PREDICATE_SYMBOL', 'U'), Token('VARIABLE', 'V')]), Tree('existential_quantification_bounded', [Token('VARIABLE', 'X2'), Tree('dom', [Token('VARIABLE', 'X2')]), Tree('universal_quantification_bounded', [Token('VARIABLE', 'Y'), Tree('existential_quantification', ['X', Tree('predicate', [Token('PREDICATE_SYMBOL', 'P'), Token('VARIABLE', 'X'), Token('VARIABLE', 'Y')])]), Tree('disjunction', [Tree('negation', [Tree(Token('RULE', 'predicate'), [Token('PREDICATE_SYMBOL', 'P'), Token('VARIABLE', 'X2'), Token('VARIABLE', 'Y')])]), Tree(Token('RULE', 'predicate'), [Token('PREDICATE_SYMBOL', 'Q'), Token('VARIABLE', 'X2'), Token('VARIABLE', 'Y')])])])])])
    
    treeExplainerGREEN(EXAMPLE_ASTS[3])
    treeExplainerRED(toBoundedMinifiedCNF().adjust_transform_repeatedly(EXAMPLE_ASTS[3]))

test_range()
exit()

def test_range_corange_transform():
    asts = [RemoveLines().transform(prover9_parser.parse(example_axiom)) for example_axiom in EXAMPLE_AXIOMS]
    miniscopeAsts = [ToReversePrenexCNF().adjust_transform_repeatedly(ast) for ast in asts]
    treeExplainer(asts[0])
    # range0 = GetRange().adjust_transform_repeatedly(asts[0])
    # corange0 = GetCoRange().adjust_transform_repeatedly(asts[0])
    # treeExplainer(range0)
    # treeExplainer(corange0)
    # canonical = get_range_corange_form(asts[0])
    # treeExplainer(canonical)
    # treeExplainer(get_existential_bound_form(asts[0]))
    treeExplainer(toBoundedMinifiedCNF().adjust_transform_repeatedly(asts[0]))

    treeExplainer(asts[1])
    # range1 = GetRange().adjust_transform_repeatedly(asts[1])
    # corange1 = GetCoRange().adjust_transform_repeatedly(asts[1])
    # treeExplainer(range1)
    # treeExplainer(corange1)
    # canonical = get_range_corange_form(asts[1])
    # treeExplainer(canonical)
    # treeExplainer(get_existential_bound_form(asts[1]))
    treeExplainer(toBoundedMinifiedCNF().adjust_transform_repeatedly(asts[1]))
    
test_range_corange_transform()


