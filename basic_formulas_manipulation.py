import re

from functools import partialmethod
from typing import Literal, Callable

from lark import Tree, Token, Transformer
from lark.visitors import Interpreter, Discard

from model import prover9_parser, Signature

from PrettyPrint import PrettyPrintTree
from PrettyPrint.Utils.Orientation import Orientation
from colorama import Back



def print_tree(tree: Tree, filename: str):
    open(filename, "w", encoding = "utf-8").write(treeExplainerReturning(tree))

def base_test(tests:list[tuple[str,str]], func:Callable[[str], str], name:str):
    for i, (inp, out) in enumerate(tests):
        calc = func(inp)
        assert calc == out, f"error at test {i}: from {inp} expected {out} got {calc}"
        print(f"Test {i} is good!")
    print(f"All good for {name}")
def test_with_parsing(tests:list[tuple[str,str]], func:Callable[[Tree], Tree], name:str, postprocess: Callable[[Tree], Tree] = lambda x:x):
    for i, (inp, out) in enumerate(tests):
        calc = func(prover9_parser.parse(inp))
        assert calc == (parsed_out:=postprocess(prover9_parser.parse(out))), f"error at test {i}: from {inp} expected \n{treeExplainerReturning(parsed_out)}\n got \n{treeExplainerReturning(calc)}"
        print(f"Test {i} is good!")
    print(f"All good for {name}")
def tree_test(tests:list, func:Callable[[str],Tree], name:str):
    for i, (inp, out) in enumerate(tests):
        calc = func(inp)
        assert calc == prover9_parser.parse(out), f"error at test {i}: from {inp} (black/white) expected {out} (GREEN) got {calc} (RED) (String>>>{ToString().visit(calc)}<<<). {treeExplainer(prover9_parser.parse(inp))}, {treeExplainerGREEN(prover9_parser.parse(out))}, {treeExplainerRED(calc)}"
        print(f"Test {i} is good!")
    print(f"All good for {name}")


BINARY_OPS = [
    "conjunction",
    "disjunction",
    "conjunction_exc",
    "disjunction_exc",
    "entailment",
    "reverse_entailment",
    "equivalence_entailment",
    "entailment_exc",
    "reverse_entailment_exc",
    "equivalence_entailment_exc",
]

def dual_quantifier(string):
    q_set = {"existential_quantification", "universal_quantification"}
    if not string in q_set:
        raise TypeError(f"Dual quantifier got {string}")
    return q_set.difference({string}).pop()

def dual_op(string):
    op_map = {
        "existential_quantification": "universal_quantification",
        "existential_quantification_exc": "universal_quantification",
        "universal_quantification": "existential_quantification",
        "universal_quantification_exc": "existential_quantification",
        "conjunction": "disjunction",
        "conjunction_exc": "disjunction",
        "disjunction": "conjunction",
        "disjunction_exc": "conjunction",
        "false": "true",
        "true": "false",
    }
    if not string in op_map.keys():
        raise TypeError(
            f"Operation should not be called to get dual. Operation was {string}"
        )
    return op_map[string]


def getChildren(x):
    return x.children if hasattr(x, "children") else None

def getData(x):
    return x.data if hasattr(x, "data") else str(x)

def getExplanation(x):
    if hasattr(x, "explanation"):
        return f"{x.data} is {str(x.explanation).replace("'","").replace(": ",":")}"
    if hasattr(x, "additional_data"):
        return f"{x.data} --- {x.additional_data}"
    if hasattr(x, "data"):
        return x.data
    return str(x)

treeExplainer = PrettyPrintTree(getChildren, getExplanation, color="", orientation=Orientation.Vertical)
treeExplainerRED = PrettyPrintTree(getChildren, getExplanation, color=Back.RED, orientation=Orientation.Vertical)
treeExplainerGREEN = PrettyPrintTree(getChildren, getExplanation, color=Back.GREEN, orientation=Orientation.Vertical)
treeExplainerYELLOW = PrettyPrintTree(getChildren, getExplanation, color="", orientation=Orientation.Vertical)
treeExplainerReturning = PrettyPrintTree(
    getChildren, getExplanation, return_instead_of_print=True, color=""
)
treeExplainerReturningNoExpl = PrettyPrintTree(
    getChildren, getData, return_instead_of_print=True, color=""
)
treeExplainerReturningRED = PrettyPrintTree(
    getChildren, getExplanation, return_instead_of_print=True, color=Back.RED
)
treeExplainerReturningGREEN = PrettyPrintTree(
    getChildren, getExplanation, return_instead_of_print=True, color=Back.GREEN
)



class ToString(Interpreter):
    """Transform a tree into a formatted string"""

    def __call__(self, tree):
        return self.visit(tree)

    def print_binary_op(self, tree, op: str):
        left, right = tree.children
        yes_left_par = left.data not in ["predicate", "equality_atom", "negation", "negation_exc", "true", "false"]
        yes_right_par = right.data not in ["predicate", "equality_atom", "negation", "negation_exc", "true", "false"]
        return (
            "(" * yes_left_par
            + self.visit(left)
            + ")" * yes_left_par
            + f" {op} "
            + "(" * yes_right_par
            + self.visit(right)
            + ")" * yes_right_par
        )

    entailment = partialmethod(print_binary_op, op="->")
    reverse_entailment = partialmethod(print_binary_op, op="<-")
    equivalence_entailment = partialmethod(print_binary_op, op="<->")
    disjunction = partialmethod(print_binary_op, op="|")
    conjunction = partialmethod(print_binary_op, op="&")
    entailment_exc = entailment
    equivalence_entailment_exc = reverse_entailment
    equivalence_entailment_exc = equivalence_entailment
    disjunction_exc = disjunction
    conjunction_exc = conjunction

    def negation(self, tree):
        negated_formula = tree.children[0]
        yes_neg_par = negated_formula.data not in ["predicate", "equality_atom", "true", "false"]
        return "-"+"("*yes_neg_par+f"{self.visit(negated_formula)}"+")"*yes_neg_par

    negation_exc = negation

    def print_quantification_op(self, tree, op: str):
        variable, quantified_formula = tree.children
        return f"{op} {variable} ({self.visit(quantified_formula)})"

    universal_quantification = partialmethod(print_quantification_op, op="all")
    existential_quantification = partialmethod(print_quantification_op, op="exists")

    def print_bounded_quantification_op(self, tree, op: str):
        variable, bounding_formula, quantified_formula = tree.children
        return f"{op} ({variable} ∈ {{{variable} | {self.visit(bounding_formula)}}}) ({self.visit(quantified_formula)})"

    universal_quantification_bounded = partialmethod(
        print_bounded_quantification_op, op="all"
    )
    existential_quantification_bounded = partialmethod(
        print_bounded_quantification_op, op="exists"
    )

    def equality_atom(self, tree):
        left, right = tree.children
        return f"{str(left)} = {str(right)}"

    def predicate(self, tree):
        predicate_symbol, *term_list = tree.children
        return f"{predicate_symbol}({",".join([term.value if hasattr(term, "value") else str(term) for term in term_list])})"

    def VARIABLE(self, tree):
        return str(tree)

    def true(self, tree):
        return "True"

    def false(self, tree):
        return "False"

    def empty(self, tree):
        return "empty"
    def cond(self, tree):
        return "cond"
    def dom(self, tree):
        return f"dom({tree.children[0]})"

    def start(self, tree):
        return self.visit(tree.children[0])
    
    def lines(self, tree):
        line_s: list = tree.children
        visited_line_s: list[str] = [self.visit(line) for line in line_s]
        return "\n".join(visited_line_s)

    def line(self, tree):
        formula = tree.children[0]
        return f"({self.visit(formula)})."
    
class P9FreeVariablesExtractor(Transformer):
    """Extract all free variables and predicates from a formula. E.g. all X A(X,Y,c2) | - exists Z P(X,Z,c) .  ---> {X}; {A:3, P:3, c:0, c2:0}
    Can be used repeatedly on different formulas.
    Calling transform returns just the variables, calling extract_free_variables_and_signature returns the variables and the signature"""

    def __init__(self, visit_tokens=True):
        super().__init__(visit_tokens)
        self.axioms_signature = Signature()
        
    def extract_free_variables_and_signature(
        self, tree: Tree
    ) -> tuple[set[str], Signature]:
        out_vars = self.transform(tree)
        out_signature = self.axioms_signature
        self.axioms_signature = Signature()
        return out_vars, out_signature

    def equality_atom(self, items):
        left_member, right_member = items
        variables_set: set[str] = set()
        self.axioms_signature.add_predicate("=", 2)
        if not isinstance(left_member, Token) or not isinstance(right_member, Token):
            raise AssertionError(
                f"Either the left member or the right member of the equality atom {items} is not a Token. This should never happen"
            )
        if left_member.type == "VARIABLE":
            variables_set.add(str(left_member))
        elif left_member.type == "CONSTANT":
            self.axioms_signature.add_constant(left_member)
        if right_member.type == "VARIABLE":
            variables_set.add(str(right_member))
        elif right_member.type == "CONSTANT":
            self.axioms_signature.add_constant(right_member)
        return variables_set

    def predicate(self, items):
        predicate_symbol, *term_list = items
        predicate_symbol = str(predicate_symbol)
        variable_set: set[str] = set()
        for token in term_list:
            if not isinstance(token, Token):
                raise AssertionError(
                    f"Found non-token {token} in predicate {predicate_symbol}. This should not happen"
                )
            else:
                if token.type == "CONSTANT":
                    self.axioms_signature.add_constant(token)
                if token.type == "VARIABLE":
                    variable_set.add(str(token))
        self.axioms_signature.add_predicate(predicate_symbol, arity := len(term_list))
        return variable_set

    def quantification(self, items, thereIsBound=False):
        if thereIsBound:
            quantified_variable, bound, variables_from_inner_formula = items
            quantified_variables = [quantified_variable]
        else:
            *quantified_variables, variables_from_inner_formula = items
        if not all(isinstance(quantified_variable, (Token, str)) for quantified_variable in quantified_variables) or not isinstance(
            variables_from_inner_formula, set
        ):
            raise TypeError(
                f"Something wrong with returned variables: either the list of quantified variables(={quantified_variables}) or the variables from the inner formula (={variables_from_inner_formula})"
            )
        difference = variables_from_inner_formula.difference({str(quantified_variable) for quantified_variable in quantified_variables})
        return difference

    existential_quantification = quantification
    universal_quantification = quantification
    existential_quantification_bounded = partialmethod(
        quantification, thereIsBound=True
    )
    universal_quantification_bounded = partialmethod(quantification, thereIsBound=True)

    def empty(self, items):
        return set()
    def cond(self, items):
        return set()

    def dom(self, items):
        ranged_variable = items[0]
        return {str(ranged_variable)}

    def merge_variables(self, items):
        return set().union(*(var_set for var_set in items))

    conjunction = merge_variables
    disjunction = merge_variables
    conjunction_exc = merge_variables
    disjunction_exc = merge_variables
    entailment = merge_variables
    reverse_entailment = merge_variables
    equivalence_entailment = merge_variables
    entailment_exc = merge_variables
    reverse_entailment_exc = merge_variables
    equivalence_entailment_exc = merge_variables
    negation = merge_variables
    negation_exc = merge_variables

    true = empty
    false = empty

    do_nothing = lambda self, items: items
    car = lambda self, items: items[0]
    start = car
    lines = car
    line = car
    sentence = car

    label = lambda self, items: None

class AssociativeFlattener(Transformer):
    """flattens associative/commutative operations in a tree. E.g. (A & (B & C)) will become (A & B & C). all X all Y phi(X,Y) will become all {X Y} phi(X,Y). Also double negation will be removed"""

    def __init__(self, visit_tokens=False):
        super().__init__(visit_tokens)

    def __call__(self,tree):
        return self.transform_repeatedly(tree)

    def transform_repeatedly(self, tree):
        oldtree = tree
        newtree = self.transform(oldtree)
        while newtree != oldtree:
            oldtree = newtree
            newtree = self.transform(newtree)
        return newtree

    def flatten_and_or(self, items, op: str):
        new_items = []
        for item in items:
            if item.data in [op, op + "_exc"]:
                new_items.extend(item.children)
            else:
                new_items.append(item)
        return Tree(op, new_items)

    conjunction = conjunction_exc = partialmethod(flatten_and_or, op="conjunction")
    disjunction = disjunction_exc = partialmethod(flatten_and_or, op="disjunction")

    def negation(self, items):
        negated_formula = items[0]
        if negated_formula.data in ["negation", "negation_exc"]:
            doubly_negated = negated_formula.children[0]
            return doubly_negated
        return Tree("negation", items)

    negation_exc = negation

    def quantification(self, items, op: str):
        *variables, inner_formula = items
        if inner_formula.data == op:
            *additional_variables, doubly_quantified_formula = inner_formula.children
            return Tree(
                op, variables + additional_variables + [doubly_quantified_formula]
            )
        return Tree(op, items)

    universal_quantification = partialmethod(
        quantification, op="universal_quantification"
    )
    existential_quantification = partialmethod(
        quantification, op="existential_quantification"
    )

class ReverseAssociativeFlattener(Transformer):
    """Inverts the operations of the associative flattener"""

    def __init__(self, visit_tokens=False):
        super().__init__(visit_tokens)

    def transform_repeatedly(self, tree):
        oldtree = tree
        newtree = self.transform(oldtree)
        while newtree != oldtree:
            oldtree = newtree
            newtree = self.transform(newtree)
        return newtree

    def de_flatten_and_or(self, items, op: str):
        if len(items) > 2:
            # return Tree(op, [items[0], Tree(op, items[1:])]) # this would put the deeper tree on the right, but default parsing puts it on the left
            return Tree(op, [Tree(op, items[:-1]), items[-1]])
        return Tree(op, items)
    conjunction = conjunction_exc = partialmethod(de_flatten_and_or, op="conjunction")
    disjunction = disjunction_exc = partialmethod(de_flatten_and_or, op="disjunction")

    def quantification(self, items, op: str):
        *variables, inner_formula = items
        if len(variables) > 1:
            return Tree(op, [variables[0], Tree(op, variables[1:] + [inner_formula])])
            
        return Tree(op, items)

    universal_quantification = partialmethod(
        quantification, op="universal_quantification"
    )
    existential_quantification = partialmethod(
        quantification, op="existential_quantification"
    )


def pushdown_negation_interpreter(interpreter, tree):
    negated_formula = tree.children[0]
    if negated_formula.data in ["disjunction", "conjunction"]:
        left, right = negated_formula.children
        return Tree(
            dual_op(negated_formula.data),
            [
                Tree("negation", [interpreter.visit(left)]),
                Tree("negation", [interpreter.visit(right)]),
            ],
        )
    if negated_formula.data in ["negation", "negation_exc"]:
        sub_negated_formula = negated_formula.children[0]
        return interpreter.visit(sub_negated_formula)
    if negated_formula.data in ["true", "false"]:
        return Tree(dual_op(negated_formula.data), [])
    return Tree("negation", interpreter.visit_children(tree))

def pushdown_negation_transformer(transformer, children):
    negated_formula = children[0]
    if negated_formula.data in ["disjunction", "conjunction"]:
        left, right = negated_formula.children
        return Tree(
            dual_op(negated_formula.data),
            [
                Tree("negation", [left]),
                Tree("negation", [right]),
            ],
        )
    if negated_formula.data in ["negation", "negation_exc"]:
        sub_negated_formula = negated_formula.children[0]
        return sub_negated_formula
    if negated_formula.data in ["true", "false"]:
        return Tree(dual_op(negated_formula.data), [])
    return Tree("negation", children)

def pushdown_negation_transformer_general(transformer, children):
    negated_formula = children[0]
    if negated_formula.data in [
        "existential_quantification",
        "universal_quantification",
        "existential_quantification_exc",
        "universal_quantification_exc",
    ]:
        *quantified_variables, quantified_formula = negated_formula.children
        return Tree(
            dual_quantifier(negated_formula.data),
            quantified_variables + [Tree("negation", [quantified_formula])],
        )
        
    if negated_formula.data in [
        "disjunction",
        "disjunction_exc",
        "conjunction",
        "conjunction_exc",
    ]:
        return Tree(
            dual_op(negated_formula.data),
            [Tree("negation", [child]) for child in negated_formula.children],
        )
        
    if negated_formula.data in [
        "negation",
        "negation_exc",
    ]:
        return negated_formula.children[0]
    
    if negated_formula.data in [
        "entailment",
        "entailment_exc",
    ]:
        pre, post = negated_formula.children
        return Tree("conjunction", [pre, Tree("negation", post)])
    
    if negated_formula.data in [
        "reverse_entailment",
        "reverse_entailment_exc",
    ]:
        post, pre = negated_formula.children
        return Tree("conjunction", [pre, Tree("negation", post)])
    
    if negated_formula.data in [
        "equivalence_entailment",
        "equivalence_entailment_exc",
    ]:
        pre, post = negated_formula.children
        return Tree("disjunction",[Tree("conjunction", [pre, Tree("negation", post)]), Tree("conjunction", [post, Tree("negation", pre)])])
    
    if negated_formula.data in ["true", "false"]:
        return Tree(dual_op(negated_formula.data), [])
        
    return Tree("negation", children)

def pushdown_negation_interpreter_general(interpreter, tree):
    children = tree.children
    negated_formula = children[0]
    if negated_formula.data in [
        "existential_quantification",
        "universal_quantification",
        "existential_quantification_exc",
        "universal_quantification_exc",
    ]:
        *quantified_variables, quantified_formula = negated_formula.children
        return Tree(
            dual_quantifier(negated_formula.data),
            quantified_variables + [Tree("negation", [interpreter.visit(quantified_formula)])],
        )
        
    if negated_formula.data in [
        "disjunction",
        "disjunction_exc",
        "conjunction",
        "conjunction_exc",
    ]:
        return Tree(
            dual_op(negated_formula.data),
            [Tree("negation", [interpreter.visit(child)]) for child in negated_formula.children],
        )
        
    if negated_formula.data in [
        "negation",
        "negation_exc",
    ]:
        return interpreter.visit(negated_formula.children[0])
    
    if negated_formula.data in [
        "entailment",
        "entailment_exc",
    ]:
        pre, post = negated_formula.children
        return Tree("conjunction", [interpreter.visit(pre), interpreter.visit(Tree("negation", [post]))])
    
    if negated_formula.data in [
        "reverse_entailment",
        "reverse_entailment_exc",
    ]:
        post, pre = negated_formula.children
        return Tree("conjunction", [interpreter.visit(pre), interpreter.visit(Tree("negation", [post]))])
    
    if negated_formula.data in [
        "equivalence_entailment",
        "equivalence_entailment_exc",
    ]:
        pre, post = negated_formula.children
        left_ent = Tree("entailment", [pre,post])
        right_ent = Tree("entailment", [post,pre])
        return Tree("disjunction",[interpreter.visit(Tree("negation",[left_ent])),interpreter.visit(Tree("negation",[right_ent]))])
    
    if negated_formula.data in ["true", "false"]:
        return Tree(dual_op(negated_formula.data), [])
        
    return Tree("negation", interpreter.visit_children(tree))



class ReplaceVariable(Interpreter):
    """Replaces a variable with another. In the case of conflicting quantification the inner formula wins. E.g. calling replace X->X1 on (all X A(X)) will not change the formula, but calling it on (all X A(X)) & B(X) will result in (all X A(X)) & B(X1)"""

    def __init__(self, replaced: str, replacing: str, resolve_conflicts: bool = True):#, replacements_list: list[tuple[str,str]] = None):
        super().__init__()
        self.replaced = replaced
        self.replacing = replacing
        self.resolve_conflicts = resolve_conflicts
        #self.replacements_list = replacements_list

    def __call__(self, tree):
        return self.visit(tree)

    def __default__(self, tree):
        # These shenaningans are needed to force the behavior of an Interpretr into something more similar to a Transformer
        # if using a transformer this is not necessary, however, branching logic is needed to skip inner conflicting formulas. Therefore an Interpreter must be used. But interpreters, by default, do not visit non-Tree nodes
        if isinstance(tree, Tree):
            return Tree(tree.data, self.visit_children(tree))
        elif isinstance(tree, Token) and tree.type == "VARIABLE":
            return self.VARIABLE(tree)
        else:
            return tree
        
    def visit_children(self, tree):
        # if using a transformer this is not necessary, however, branching logic is needed to skip inner conflicting formulas. Therefore an Interpreter must be used. But interpreters, by default, do not visit non-Tree nodes
        return [self._visit_tree(child) if isinstance(child, Tree) else self.VARIABLE(child) if isinstance(child, Token) and child.type == "VARIABLE" else child for child in tree.children]
    def transform(self, tree):
        return self.visit(tree)
    
    def VARIABLE(self, token):
        assert isinstance(token, Token)
        if token.value == self.replaced:
            return Token("VARIABLE", self.replacing) # value.replace(self.replaced, self.replacing) <- this is wrong because it replaces substrings within variable names
        return token 
    
    def quantification(self, tree):
        quantified_variable, *bounding_formula_list, inner_formula = tree.children
        if self.resolve_conflicts:
            if str(quantified_variable) == self.replaced: 
                # conflicting quantification: the inner formula wins
                return tree
            else:
                # no conflict: the replacement proceeds on
                return Tree(tree.data, self.visit_children(tree)) if isinstance(tree, Tree) else self.visit(tree)
        else:
            return Tree(tree.data, self.visit_children(tree)) if isinstance(tree, Tree) else self.visit(tree)

    universal_quantification = existential_quantification_bounded = existential_quantification = existential_quantification_bounded = quantification

class ToUniqueVariables(Transformer):
    """Each quantified variable will have a unique name. Also redundant quantifications will be removed. Not to be used with flattened formulas!"""

    def __init__(self, visit_tokens=True):
        super().__init__(visit_tokens)
        self.quantified_variables = set()

    def __call__(self, tree):
        return self.adjust_variables(tree)

    def adjust_variables(self, tree):
        self.quantified_variables = set()
        out_tree = self.transform(tree)
        self.quantified_variables = set()
        return out_tree

    def quantification(self, items, quantification_type):
        quantified_variable, *bounding_formula_list, inner_formula = items
        # remove useless quantification
        if str(quantified_variable) not in P9FreeVariablesExtractor().transform(inner_formula):
            return inner_formula
        if str(quantified_variable) in self.quantified_variables:
            # checks if quantified_variable is of shape X or Xn, then it starts from X1 or Xn+1 and increases the counter until a new variable is produces
            match = re.match(r"([a-zA-Z]+)(.*?)(\d+)", str(quantified_variable))
            if not match: 
                # case of e.g. X 
                root = str(quantified_variable)
                new_number = 1
            else:
                # case of e.g. X1, X_43, etc.  
                root, _, number = match.groups()
                new_number = int(number) + 1
            # finds all variables appearing in the quantified formula and, if it is present, in the bound 
            variables_appearing_in_formula = set(inner_formula.scan_values(pred=lambda x:isinstance(x,Token) and x.type=="VARIABLE"))
            if bounding_formula_list != []:
                variables_appearing_in_formula = variables_appearing_in_formula.union(set(bounding_formula_list[0].scan_values(pred=lambda x:isinstance(x,Token) and x.type=="VARIABLE"))) 
            # forces the new variable name to be not present neither in the formula (either as a quantified or a free variable) nor in the alreadi visited quantified variables. 
            while root+str(new_number) in self.quantified_variables.union(variables_appearing_in_formula):
                new_number += 1
            new_name = root+str(new_number) #str(quantified_variable) + str(len(self.quantified_variables))
            self.quantified_variables.add(new_name)
            rp = ReplaceVariable(str(quantified_variable), new_name)
            replacing_inner_formula = rp.transform(inner_formula)
            if bounding_formula_list != []:
                bounding_formula_list = [rp.transform(bounding_formula_list[0])]
            return Tree(
                quantification_type,
                [Token(type_="VARIABLE", value=new_name)]
                + bounding_formula_list
                + [replacing_inner_formula],
            )
        self.quantified_variables.add(str(quantified_variable))
        return Tree(quantification_type, items)

    universal_quantification = partialmethod(
        quantification, quantification_type="universal_quantification"
    )
    existential_quantification = partialmethod(
        quantification, quantification_type="existential_quantification"
    )
    universal_quantification_bounded = partialmethod(
        quantification, quantification_type="universal_quantification_bounded"
    )
    existential_quantification_bounded = partialmethod(
        quantification, quantification_type="existential_quantification_bounded"
    )

class VariableNormalizer(Interpreter):
    """Each variable in the formula will be unique and will be renamed in a deterministic way. Not to be used with flattened formulas!"""

    def __init__(self):
        super().__init__()
        self.uniquifier = ToUniqueVariables()

    def __call__(self, tree):
        return self.adjust_variables(tree)

    def adjust_variables(self, tree):
        tree = self.uniquifier(tree)
        self.variables_list_sorted = sorted(set(tree.scan_values(pred=lambda x:isinstance(x,Token) and x.type=="VARIABLE")))
        for i, variable in enumerate(self.variables_list_sorted):
            rp = ReplaceVariable(str(variable), f"_X{i}", False)
            tree = rp(tree)
        return tree


class ToPrenex(Transformer):
    """Transform a formula in prenex normal form"""

    def __init__(self, visit_tokens=True):
        super().__init__(visit_tokens)

    def adjust_transform_repeatedly(self, tree):
        unique = ToUniqueVariables()
        adjusted_tree = unique.adjust_variables(tree)
        oldtree = adjusted_tree
        newtree = unique.adjust_variables(self.transform(adjusted_tree))
        while newtree != oldtree:
            oldtree = newtree
            newtree = unique.adjust_variables(self.transform(oldtree))
        return newtree

    def entailment(self, children):
        left, right = children
        if right.data in [
            "existential_quantification",
            "universal_quantification",
        ] and not left.data in [
            "existential_quantification",
            "universal_quantification",
        ]:
            quantified_variable, quantified_formula = right.children
            return Tree(
                right.data,
                [quantified_variable, Tree("entailment", [left, quantified_formula])],
            )
        if left.data in [
            "existential_quantification",
            "universal_quantification",
        ] and not right.data in [
            "existential_quantification",
            "universal_quantification",
        ]:
            quantified_variable, quantified_formula = left.children
            return Tree(
                dual_quantifier(left.data),
                [quantified_variable, Tree("entailment", [quantified_formula, right])],
            )
        if left.data in [
            "existential_quantification",
            "universal_quantification",
        ] and right.data in ["existential_quantification", "universal_quantification"]:
            left_quantified_variable, left_quantified_formula = left.children
            right_quantified_variable, right_quantified_formula = right.children
            return Tree(
                dual_quantifier(left.data),
                [
                    left_quantified_variable,
                    Tree(
                        right.data,
                        [
                            right_quantified_variable,
                            Tree(
                                "entailment",
                                [left_quantified_formula, right_quantified_formula],
                            ),
                        ],
                    ),
                ],
            )
        return Tree("entailment", children)

    entailment_exc = entailment

    def reverse_entailment(self, children):
        left, right = children
        return self.entailment([right, left])

    equivalence_entailment_exc = reverse_entailment

    def symmetric_op(self, children, operator: str):
        left, right = children
        if right.data in [
            "existential_quantification",
            "universal_quantification",
        ] and not left.data in [
            "existential_quantification",
            "universal_quantification",
        ]:
            quantified_variable, quantified_formula = right.children
            return Tree(
                right.data,
                [quantified_variable, Tree(operator, [left, quantified_formula])],
            )
        if left.data in [
            "existential_quantification",
            "universal_quantification",
        ] and not right.data in [
            "existential_quantification",
            "universal_quantification",
        ]:
            quantified_variable, quantified_formula = left.children
            return Tree(
                left.data,
                [quantified_variable, Tree(operator, [quantified_formula, right])],
            )
        if (
            left.data == "universal_quantification"
            and right.data == left.data
            and operator == "conjunction"
        ):
            # (all X phi(X)) & (all Y psi(Y)) ---> all X (phi(X) & psi(X))
            left_quantified_variable, left_quantified_formula = left.children
            right_quantified_variable, right_quantified_formula = right.children
            replace = ReplaceVariable(
                replaced=right_quantified_variable, replacing=left_quantified_variable
            )
            replaced_right_quantified_formula = replace.transform(
                right_quantified_formula
            )
            return Tree(
                left.data,
                [
                    left_quantified_variable,
                    Tree(
                        "conjunction",
                        [left_quantified_formula, replaced_right_quantified_formula],
                    ),
                ],
            )
        if (
            left.data == "existential_quantification"
            and right.data == left.data
            and operator == "disjunction"
        ):
            # (exists X phi(X)) | (exists Y psi(Y)) ---> exists X (phi(X) | psi(X))
            left_quantified_variable, left_quantified_formula = left.children
            right_quantified_variable, right_quantified_formula = right.children
            replace = ReplaceVariable(
                replaced=right_quantified_variable, replacing=left_quantified_variable
            )
            replaced_right_quantified_formula = replace.transform(
                right_quantified_formula
            )
            return Tree(
                left.data,
                [
                    left_quantified_variable,
                    Tree(
                        "disjunction",
                        [left_quantified_formula, replaced_right_quantified_formula],
                    ),
                ],
            )
        if left.data in [
            "existential_quantification",
            "universal_quantification",
        ] and right.data in ["existential_quantification", "universal_quantification"]:
            left_quantified_variable, left_quantified_formula = left.children
            right_quantified_variable, right_quantified_formula = right.children
            return Tree(
                left.data,
                [
                    left_quantified_variable,
                    Tree(
                        right.data,
                        [
                            right_quantified_variable,
                            Tree(
                                operator,
                                [left_quantified_formula, right_quantified_formula],
                            ),
                        ],
                    ),
                ],
            )
        return Tree(operator, children)

    # disjunction = partial(binary_op, operator = "disjunction")
    def disjunction(self, children):
        return self.symmetric_op(children, "disjunction")

    disjunction_exc = disjunction

    # conjunction = partial(binary_op, operator = "conjunction")
    def conjunction(self, children):
        return self.symmetric_op(children, "conjunction")

    conjunction_exc = conjunction

    def equivalence_entailment(self, children):
        left, right = children
        return Tree(
            "conjunction",
            [Tree("entailment", [left, right]), Tree("entailment", [right, left])],
        )

    equivalence_entailment_exc = equivalence_entailment

    def negation_exc(self, children):
        negated_formula = children[0]
        if negated_formula.data in [
            "existential_quantification",
            "universal_quantification",
        ]:
            quantified_variable, quantified_formula = negated_formula.children
            return Tree(
                dual_quantifier(negated_formula.data),
                [quantified_variable, Tree("negation", [quantified_formula])],
            )
        return Tree("negation", children)

    negation = negation_exc

class ToNNF(Transformer):
    """Transform a formula in negation normal form"""

    def __init__(self, visit_tokens=True):
        super().__init__(visit_tokens)
        self.unique = ToUniqueVariables()
        self.reducer = ReduceLogicalSignature()

    def adjust_transform_repeatedly(self, tree):
        adjusted_tree = self.unique.adjust_variables(self.reducer.visit_repeatedly(tree))
        oldtree = adjusted_tree
        newtree = self.unique.adjust_variables(self.transform(adjusted_tree))
        while newtree != oldtree:
            oldtree = newtree
            newtree = self.unique.adjust_variables(self.transform(oldtree))
        return newtree

    negation = negation_exc = pushdown_negation_transformer_general


class InterpreterUntilFixedPoint(Interpreter):
    """Defines a visit_repeatedly method with the possibility of pre- and post-transformations"""
    def __init__(self, pretransform_function = lambda x:x, posttransform_function = lambda x:x):
        super().__init__()
        self.pretransform_function = pretransform_function
        self.posttransform_function = posttransform_function

    def __call__(self, tree):
        return self.visit_repeatedly(tree)

    def visit_repeatedly(self, tree):
        oldtree = self.pretransform_function(tree)
        newtree = self.visit(oldtree)
        while newtree != oldtree:
            oldtree = newtree
            newtree = self.visit(oldtree)
        returned_tree = self.posttransform_function(newtree)
        return returned_tree
    
class ReduceLogicalSignature(InterpreterUntilFixedPoint):
    """Reduces the logical signature to just conjunction, disjunction, negation, and existential and univeral quantifiers"""
    def entailment(self, tree):
        left, right = tree.children
        return Tree(
            "disjunction", [Tree("negation", [self.visit(left)]), self.visit(right)]
        )
    entailment_exc = entailment

    def reverse_entailment(self, tree):
        left, right = tree.children
        return self.entailment([right, left])
    equivalence_entailment_exc = reverse_entailment
    
    def equivalence_entailment(self, tree):
        left, right = tree.children
        return Tree(
            "conjunction",
            [
                Tree("entailment", [self.visit(left), self.visit(right)]),
                Tree("entailment", [self.visit(right), self.visit(left)]),
            ],
        )
    equivalence_entailment_exc = equivalence_entailment

    def terminate(self, tree):
        return tree

    def conjunction(self, tree):
        absorbing_element = {"disjunction": "true", "conjunction": "false"}
        neutral_element = {"disjunction": "false", "conjunction": "true"}
        if any(child.data == absorbing_element[tree.data] for child in tree.children):
            return Tree(absorbing_element[tree.data], [])
        if any(child.data == neutral_element[tree.data] for child in tree.children) and any(child.data != neutral_element[tree.data] for child in tree.children):
            return Tree(tree.data, [self.visit(child) for child in tree.children if child.data != neutral_element[tree.data]])
        if any(x==y and i!=j for i,x in enumerate(tree.children) for j,y in enumerate(tree.children)): # gonna touch the list only if necessary
            return Tree(tree.data, [self.visit(child) for child in list(set(tree.children))])
        if len(tree.children) == 1:
            return self.visit(tree.children[0])
        return Tree(tree.data, self.visit_children(tree))
    disjunction = conjunction

    predicate = terminate
    equality_atom = terminate
    dom = terminate
    cond = terminate
    empty = terminate
    VARIABLE = terminate
    false = terminate
    true = terminate
    
    def __default__(self, tree):
        return Tree(tree.data, self.visit_children(tree))
    
def pushdown_binary_op(self, tree, param: Literal["conjunction", "disjunction"]):
    # First thing first: duplicates and base cases are removed
    absorbing_element = {"disjunction": "true", "conjunction": "false"}
    neutral_element = {"disjunction": "false", "conjunction": "true"}
    if any(child.data == absorbing_element[param] for child in tree.children):
        return Tree(absorbing_element[param], [])
    if any(child.data == neutral_element[param] for child in tree.children) and any(child.data != neutral_element[param] for child in tree.children):
        return Tree(param, [self.visit(child) for child in tree.children if child.data != neutral_element[param]])
    if any(x==y and i!=j for i,x in enumerate(tree.children) for j,y in enumerate(tree.children)): # gonna touch the list only if necessary
        return Tree(param, [self.visit(child) for child in list(set(tree.children))])
    if len(tree.children) == 1:
        return self.visit(tree.children[0])

    # This works for ennary operations
    if any(child.data == dual_op(param) for child in tree.children): # if any child is of the dual type
        op_child = next(child for child in tree.children if child.data == dual_op(param)) # take the first child (=: op_child) of that type
        return Tree( # and commute the two binary operations
                dual_op(param), # in such a way that now the top operation is the one that was a child
                [ # and it has as children only the old top operation, repeated as many times as there are subchildren in op_child, 
                  # the subchildrend of such old top operations are the local subchild of the op_child and for the rest the other children of the old top operation
                    Tree(param, [self.visit(child) if child != op_child else self.visit(sub_child) for child in tree.children]) for sub_child in op_child.children
                ]
        )
    return Tree(param, self.visit_children(tree))

class ToNegativeNormalForm(ReduceLogicalSignature):
    """Transform a propositional formula in negative normal form. (Non propositional operators are included)"""
    negation = negation_exc = pushdown_negation_interpreter_general

class ToDisjunctiveNormalForm(ToNegativeNormalForm):
    """Transform a propositional formula in disjunctive normal form. A pretrasformation to NNF is forced at the start, this prevents some issues with size explosion. (Non propositional operators are included but only for negation pushdown)"""
    def __init__(self):
        self.toNNF = ToNegativeNormalForm()
        super().__init__(pretransform_function=self.toNNF)

    conjunction_exc = conjunction = partialmethod(pushdown_binary_op, param = "conjunction")

class ToConjunctiveNormalForm(ToNegativeNormalForm):
    """Transform a propositional formula in conjunctive normal form. A pretrasformation to NNF is forced at the start, this prevents some issues with size explosion.. (Non propositional operators are included but only for negation pushdown)"""
    def __init__(self):
        self.toNNF = ToNegativeNormalForm()
        super().__init__(pretransform_function=self.toNNF)
    
    disjunction_exc = disjunction = partialmethod(pushdown_binary_op, param = "disjunction")

class ToPrenexCNF:
    """Transform a formula in prenex conjunctive normal form."""

    def __init__(self):
        self.toPrenex = ToPrenex()
        self.toCNF = ToConjunctiveNormalForm()

    def __call__(self, tree):
        return self.transform_repeatedly(tree)

    def transform_repeatedly(self, tree):
        oldtree = tree
        newtree_pre = self.toPrenex.adjust_transform_repeatedly(oldtree)
        newtree = self.toCNF.visit_repeatedly(newtree_pre)
        while newtree != oldtree:
            oldtree = newtree
            newtree_pre = self.toPrenex.adjust_transform_repeatedly(oldtree)
            newtree = self.toCNF.visit_repeatedly(newtree_pre)
        return newtree

class ToPrenexDNF:
    """Transform a formula in prenex disjunctive normal form."""

    def __init__(self):
        self.toPrenex = ToPrenex()
        self.toDNF = ToDisjunctiveNormalForm()

    def __call__(self, tree):
        return self.transform_repeatedly(tree)

    def transform_repeatedly(self, tree):
        oldtree = tree
        newtree_pre = self.toPrenex.adjust_transform_repeatedly(oldtree)
        newtree = self.toDNF.visit_repeatedly(newtree_pre)
        while newtree != oldtree:
            oldtree = newtree
            newtree_pre = self.toPrenex.adjust_transform_repeatedly(oldtree)
            newtree = self.toDNF.visit_repeatedly(newtree_pre)
        return newtree

class ToPrenexNNF:
    """Transform a formula in prenex negation normal form."""

    def __init__(self):
        self.toPrenex = ToPrenex()
        self.toNNF = ToNNF()

    def __call__(self, tree):
        return self.transform_repeatedly(tree)

    def transform_repeatedly(self, tree):
        oldtree = tree
        newtree_pre = self.toPrenex.adjust_transform_repeatedly(oldtree)
        newtree = self.toNNF.adjust_transform_repeatedly(newtree_pre)
        while newtree != oldtree:
            oldtree = newtree
            newtree_pre = self.toPrenex.adjust_transform_repeatedly(oldtree)
            newtree = self.toNNF.adjust_transform_repeatedly(newtree_pre)
        return newtree


class ToReversePrenex(Transformer):
    """Transforms a formula in reverse prenex (push quantifiers in the innermost position possible -- if it is immediate to do so)"""


    def __init__(self, visit_tokens=True):
        super().__init__(visit_tokens)
        self.freeVars = P9FreeVariablesExtractor()
        self.stringer = ToString()
        self.unique = ToUniqueVariables()
        self.commutes = {
            "existential_quantification": "disjunction",
            "universal_quantification": "conjunction",
        }

    def adjust_transform_repeatedly(self, tree):
        oldtree = self.unique.adjust_variables(tree)
        newtree = self.unique.adjust_variables(self.transform(oldtree))
        while newtree != oldtree:
            oldtree = newtree
            newtree = self.unique.adjust_variables(self.transform(oldtree))
        return newtree

    def quantification(self, children, quantification_type: str):
        quantified_variable, quantified_formula = children
        if quantified_formula.data in ["negation", "negation_exc"]:
            negated_formula = quantified_formula.children[0]
            return Tree(
                "negation",
                [
                    Tree(
                        dual_quantifier(quantification_type),
                        [quantified_variable, negated_formula],
                    )
                ],
            )
        if quantified_formula.data in BINARY_OPS:
            left, right = quantified_formula.children
            if not quantified_variable in self.freeVars.transform(
                left
            ) and not quantified_variable in self.freeVars.transform(right):
                raise TypeError(
                    f"In quantified formula {quantified_formula} the quantified variable {quantified_variable} does not occurr! This should never happen."
                )
            if not quantified_variable in self.freeVars.transform(left):
                return Tree(
                    quantified_formula.data,
                    [left, Tree(quantification_type, [quantified_variable, right])],
                )
            if not quantified_variable in self.freeVars.transform(right):
                return Tree(
                    quantified_formula.data,
                    [Tree(quantification_type, [quantified_variable, left]), right],
                )
        if quantified_formula.data == self.commutes[quantification_type]:
            left, right = quantified_formula.children
            return Tree(
                quantified_formula.data,
                [
                    Tree(quantification_type, [quantified_variable, left]),
                    Tree(quantification_type, [quantified_variable, right]),
                ],
            )
        return Tree(quantification_type, [quantified_variable, quantified_formula])

    existential_quantification = partialmethod(
        quantification, quantification_type="existential_quantification"
    )
    universal_quantification = partialmethod(
        quantification, quantification_type="universal_quantification"
    )

    negation_exc = pushdown_negation_transformer
    negation = negation_exc
    
class ToReversePrenexCNF(ToReversePrenex):
    """Transform a formula in prenex CNF and transforms it in reverse prenex CNF normal form (push quantifiers in the innermost position possible -- if it is immediate to do so)
    If the formula is not prenex CNF it will be made so before starting"""

    def __init__(self, visit_tokens=True):
        super().__init__(visit_tokens)
        self.toPCNF = ToPrenexCNF()

    def adjust_transform_repeatedly(self, tree):
        # ensures the tree is PCNF
        PCNFtree = self.toPCNF.transform_repeatedly(tree) 
        # if PCNFtree != tree:
            # print(f"As an input of ToReversePrenexCNF I got a formula not in PCNF. Precisely {self.stringer.visit(tree)}. I have transformed it in PCNF: the formula is now {self.stringer.visit(PCNFtree)}.")

        adjusted_tree = self.unique.adjust_variables(PCNFtree)
        oldtree = adjusted_tree
        newtree = self.unique.adjust_variables(self.transform(adjusted_tree))
        while newtree != oldtree:
            # print("I am transforming an additional time")
            oldtree = newtree
            newtree = self.unique.adjust_variables(self.transform(oldtree))
        return newtree

class ToReversePrenexNNF(ToReversePrenex):
    """Transform a formula in prenex NNF and transforms it in reverse prenex NNF normal form (push quantifiers in the innermost position possible -- if it is immediate to do so)
    If the formula is not prenex NNF it will be made so before starting"""

    def __init__(self, visit_tokens=True):
        super().__init__(visit_tokens)
        self.toPNNF = ToPrenexNNF()

    def adjust_transform_repeatedly(self, tree):
        # ensures the tree is PNNF
        PNNFtree = self.toPNNF.transform_repeatedly(tree) 
        # if PNNFtree != tree:
        #     my_logger.debug(f"As an input of ToReversePrenexNNF I got a formula not in PNNF. Precisely {self.stringer.visit(tree)}. I have transformed it in PCNF: the formula is now {self.stringer.visit(PNNFtree)}.")

        adjusted_tree = self.unique.adjust_variables(PNNFtree)
        oldtree = adjusted_tree
        newtree = self.unique.adjust_variables(self.transform(adjusted_tree))
        while newtree != oldtree:
            # print("I am transforming an additional time")
            oldtree = newtree
            newtree = self.unique.adjust_variables(self.transform(oldtree))
        return newtree

def remove_double_negation(self, children):
    negated_formula = children[0]
    if negated_formula.data in ["negation", "negation_exc"]:
        doubly_negated_formula = negated_formula.children[0]
        return doubly_negated_formula
    return Tree("negation", children)

class ToMiniscoped(Transformer):
    """Transform a formula in miniscoped form (push quantifiers in the innermost position possible -- with some for of look-ahead)
    No additional transformation are made before starting"""

    def __init__(self, visit_tokens=True):
        super().__init__(visit_tokens)
        self.freeVars = P9FreeVariablesExtractor()
        self.preliminary_transform = lambda x:x
        self.commutes = {
            "existential_quantification": "disjunction",
            "universal_quantification": "conjunction",
        }
        self.unique = ToUniqueVariables()
        self.flattener = AssociativeFlattener()
        self.reverse_flattener = ReverseAssociativeFlattener()

    def adjust_transform_repeatedly(self, tree):
        # no preliminary trasformation is made in ToMiniscoped, but child classes may do so
        transformed_tree = self.preliminary_transform(tree)
        # ensures variable name uniqueness
        UniqueVarsTree = self.unique.adjust_variables(transformed_tree)
        # ensures the tree is associatively-flattened
        FlatUniqueVarsTree = self.flattener.transform_repeatedly(UniqueVarsTree)
        oldtree = FlatUniqueVarsTree
        newtree = self.flattener.transform_repeatedly(self.transform(oldtree))
        while newtree != oldtree:
            oldtree = newtree
            newtree = self.flattener.transform_repeatedly(self.transform(oldtree))
        return self.unique.adjust_variables(self.reverse_flattener.transform_repeatedly(newtree))

    def quantification(self, children, quantification_type: str):
        *quantified_variables, quantified_formula = children

        if quantified_formula.data in ["negation", "negation_exc"]:
            negated_formula = quantified_formula.children[0]
            return Tree(
                "negation",
                [
                    Tree(
                        dual_quantifier(quantification_type),
                        quantified_variables +[negated_formula],
                    )
                ],
            )
            
        if quantified_formula.data in BINARY_OPS:
            def get_candidate_variables_for_splitting(quantified_variables, quantified_formula):
                """If None is returned there are no candidates for splitting"""
                if len(quantified_variables) < 2: return None 
                variable_sets = [frozenset(self.freeVars.transform(child)) for child in quantified_formula.children]
                variable_to_containing_sets = {var: {var_set for var_set in variable_sets if var in var_set} for var in quantified_variables}

                candidates = set()
                for var1 in quantified_variables:
                    for var2 in frozenset(quantified_variables).difference(frozenset.union(*variable_to_containing_sets[var1])):
                        candidates.add(frozenset({var1,var2}))             
                if len(candidates) > 0:
                    # for now a random (not random, but meaninglessy ordered for reproducibility) couple of candidate variables is returned
                    var1, var2 = tuple(sorted(list(candidates))[0])
                    # order the variables in fix order for reproducibility
                    if str(var1) > str(var2):
                        temp = var1
                        var1 = var2
                        var2 = temp
                    return var1, var2
                else:
                    return None
            
            candidates = get_candidate_variables_for_splitting(quantified_variables, quantified_formula)
            if candidates:
                var1, var2 = candidates
                remaining_variables = [var for var in quantified_variables if var not in [var1, var2]]
                children1 = [child for child in quantified_formula.children if var1 in self.freeVars.transform(child)]
                children2 = [child for child in quantified_formula.children if var2 in self.freeVars.transform(child)]
                if len(children1) + len(children2) > len(quantified_formula.children): raise TypeError(f"The variables {var1}, {var2} do not split the set {quantified_variables}! Something went wrong during the splitting calculation")
                if 0 in [len(children1),len(children2)]: raise TypeError(f"Either of variables {var1}, {var2} does not appear in the formula {quantified_formula}! This should not happen.")
                remaining_children = [child for child in quantified_formula.children if (child not in children1) and (child not in children2)]
                if len(remaining_variables) == 0:
                    if len(remaining_children) == 0:
                        return Tree(
                            quantified_formula.data,
                            [Tree(quantification_type, [var1, (Tree(quantified_formula.data, children1) if len(children1) > 1 else children1[0])]), 
                             Tree(quantification_type, [var2, (Tree(quantified_formula.data, children2) if len(children2) > 1 else children2[0])])],
                        )
                    if len(remaining_children) > 0:
                        # raise TypeError("The variables do not exhaust the children but there are no other variables!") # <- can happen if there is a child with no variables
                        return Tree(
                            quantified_formula.data,
                            remaining_children + [Tree(quantification_type, [var1, (Tree(quantified_formula.data, children1) if len(children1) > 1 else children1[0])]), Tree(quantification_type, [var2, (Tree(quantified_formula.data, children2) if len(children2) > 1 else children2[0])])],
                        )
                         
                if len(remaining_variables) > 0:
                    if len(remaining_children) == 0:
                        return Tree(quantification_type, remaining_variables + [Tree(
                            quantified_formula.data,
                            [Tree(quantification_type, [var1, (Tree(quantified_formula.data, children1) if len(children1) > 1 else children1[0])]), Tree(quantification_type, [var2, (Tree(quantified_formula.data, children2) if len(children2) > 1 else children2[0])])],
                        )])
                    if len(remaining_children) > 0:
                        return Tree(quantification_type, remaining_variables + [Tree(
                            quantified_formula.data,
                            remaining_children + [Tree(quantification_type, [var1, (Tree(quantified_formula.data, children1) if len(children1) > 1 else children1[0])]), Tree(quantification_type, [var2, (Tree(quantified_formula.data, children2) if len(children2) > 1 else children2[0])])],
                        )])
            else:
                variable_appearing_less = sorted([(var,len([child for child in quantified_formula.children if var in self.freeVars.transform(child)])) for var in quantified_variables], key= lambda x:x[1])[0][0]

                children_less = [child for child in quantified_formula.children if variable_appearing_less in self.freeVars.transform(child)]
                remaining_variables = [var for var in quantified_variables if var != variable_appearing_less]
                remaining_children = [child for child in quantified_formula.children if child not in children_less]
                assert len(children_less) + len(remaining_children) == len(quantified_formula.children)
                if len(remaining_children) == 0:
                    pass # This case is skipped here since if the tree arrives at the end of this function it will returned alredy 
                    # return Tree(quantification_type,
                    #     quantified_variables + [quantified_formula])
                if len(remaining_children) > 0:
                    if len(remaining_variables) == 0:
                        return Tree(quantified_formula.data, remaining_children + [Tree(quantification_type, [variable_appearing_less] + (children_less if len(children_less) == 1 else [Tree(quantified_formula.data, children_less)]))])
                    if len(remaining_variables) > 0:
                        return Tree(quantification_type, 
                            remaining_variables + [Tree(quantified_formula.data, remaining_children + [Tree(quantification_type, [variable_appearing_less] + (children_less if len(children_less) == 1 else [Tree(quantified_formula.data, children_less)]))])]
                        )
                     
        if quantified_formula.data == self.commutes[quantification_type]:
            return Tree(
                quantified_formula.data,
                [Tree(quantification_type, quantified_variables + [child]) for child in quantified_formula.children],
            )
        return Tree(quantification_type, quantified_variables + [quantified_formula])

    existential_quantification = partialmethod(
        quantification, quantification_type="existential_quantification"
    )
    universal_quantification = partialmethod(
        quantification, quantification_type="universal_quantification"
    )

    negation = negation_exc = remove_double_negation

class ToMiniscopedPDNF(ToMiniscoped):
    """Transform a formula in PDNF and transforms it in miniscoped negation normal form (push quantifiers in the innermost position possible)
    If the formula is not PDNF it will be made so before starting"""

    def __init__(self, visit_tokens=True):
        super().__init__(visit_tokens)
        self.toPDNF = ToPrenexDNF()
        self.preliminary_transform = self.toPDNF.transform_repeatedly

class ToMiniscopedPCNF(ToMiniscoped):
    """Transform a formula in prenex CNF and transforms it in reverse prenex CNF normal form (push quantifiers in the innermost position possible)
    If the formula is not prenex CNF it will be made so before starting"""

    def __init__(self, visit_tokens=True):
        super().__init__(visit_tokens)
        self.toPCNF = ToPrenexCNF()
        self.preliminary_transform = self.toPCNF.transform_repeatedly

class ToMiniscopedPNNF(ToMiniscoped):
    """Transform a formula in PNNF and transforms it in miniscoped negation normal form (push quantifiers in the innermost position possible)
    If the formula is not PNNF it will be made so before starting"""

    def __init__(self, visit_tokens=True):
        super().__init__(visit_tokens)
        self.toPNNF = ToPrenexNNF()
        self.preliminary_transform = self.toPNNF.transform_repeatedly

class ToMiniscopedDNF(ToMiniscopedPCNF):
    """Transform a formula in DNF and transforms it in miniscoped negation normal form (push quantifiers in the innermost position possible) 
    If the formula is not DNF it will be made so before starting"""
    def __init__(self, visit_tokens=True):
        super().__init__(visit_tokens)
        self.toDNF = ToDisjunctiveNormalForm()
        self.preliminary_transform = self.toDNF.visit_repeatedly

class ToMiniscopedCNF(ToMiniscoped):
    """Transform a formula in CNF and transforms it in miniscoped negation normal form (push quantifiers in the innermost position possible) 
    If the formula is not CNF it will be made so before starting"""
    def __init__(self, visit_tokens=True):
        super().__init__(visit_tokens)
        self.toCNF = ToConjunctiveNormalForm()
        self.preliminary_transform = self.toCNF.visit_repeatedly

class ToMiniscopedNNF(ToMiniscopedPCNF):
    """Transform a formula in NNF and transforms it in miniscoped negation normal form (push quantifiers in the innermost position possible) 
    If the formula is not NNF it will be made so before starting"""
    def __init__(self, visit_tokens=True):
        super().__init__(visit_tokens)
        self.toNNF = ToNNF()
        self.preliminary_transform = self.toNNF.adjust_transform_repeatedly

class BinaryOpSimplificator(InterpreterUntilFixedPoint):
    """Simplifies binary operations expressions, with some sort of look-ahead. E.g. ((A&B)&C)&A will become (A&B)&C and (A|B|C)&B will become B. Also (exists A B(A))&(exists C B(C)) will become (exists A B(A))"""
    def __init__(self):
        self.flattener = AssociativeFlattener()
        self.deflattener = ReverseAssociativeFlattener()
        self.variable_normalizer = VariableNormalizer()
        super().__init__(self.flattener.transform_repeatedly, self.deflattener.transform_repeatedly)

    def simplify_binary_op(self, tree):
        """(A&B) | A --> A; (A&B) | B --> B; A | (A&B) --> A; B | (A&B) --> B; A | A --> A\n
           (A|B) & A --> A; (A|B) & B --> B; A & (A|B) --> A; B & (A|B) --> B; A & A --> A""" 
        # first step: dedupe children
        looped_children = set()
        deduped_children = list()
        for child in tree.children:
            if self.variable_normalizer(child) in looped_children:
                continue
            else:
                looped_children.add(self.variable_normalizer(child))
                deduped_children.append(child)

        # second: for each (deduped) child that is a dual operation, if one subchild is the same as one of the top-children, remove the whole child
        deduped_and_dually_reduced_children = list()
        normalized_deduped_children = [self.variable_normalizer(child) for child in deduped_children]
        for child in deduped_children:
            if not (isinstance(child, Tree) and child.data == dual_op(tree.data)):
                deduped_and_dually_reduced_children.append(child)
                continue
            # now the child is a dual operation
            # if any of the child's subchild is already present in the deduped children, ignore it; otherwise keep it
            if not any(self.variable_normalizer(subchild) in normalized_deduped_children for subchild in child.children):
                deduped_and_dually_reduced_children.append(child)
        
        return Tree(tree.data, deduped_and_dually_reduced_children) if len(deduped_and_dually_reduced_children) > 1 else deduped_and_dually_reduced_children[0]
    disjunction = disjunction_exc = simplify_binary_op
    conjunction = conjunction_exc = simplify_binary_op

    def negation(self, tree):
        """--A --> A"""
        negated_formula = tree.children[0]
        if isinstance(negated_formula, Tree) and negated_formula.data in ["negation", "negation_exc"]:
            return negated_formula.children[0]
        return tree
    negation_exc = negation

    # visit all nodes since interpreters dont do it by default 
    def __default__(self, tree):
        return Tree(tree.data, self.visit_children(tree))# if isinstance(tree,Tree) else tree

    # def terminate(self, tree):
    #     return tree

    # predicate = terminate
    # equality_atom = terminate
    # dom = terminate
    # cond = terminate
    # empty = terminate
    # VARIABLE = terminate
    # false = terminate
    # true = terminate

class RemoveLines(Transformer):
    """removes start, lines, and line nodes; and also labels. Works only if the tree starts with one start, then one lines, then one single line"""

    def __call__(self, tree):
        return self.transform(tree)

    def start(self, children):
        assert children[0].data == "lines"
        lines = children[0]
        assert len(lines.children) == 1
        assert lines.children[0].data == "line"
        line = lines.children[0]
        return (axiom := line.children[0])
class RemoveLabels(Transformer):
    """removes labels."""
    def label(self, children):
        return Discard

def get_existential_closure(tree: Tree, exceptions={}) -> Tree:
    free_vars: set[str] = (
        P9FreeVariablesExtractor().extract_free_variables_and_signature(tree)[0]
    )
    vars_to_close = free_vars.difference(exceptions)
    closed_tree = tree.copy()
    for var in sorted(list(vars_to_close)): # order for reproducibility
        closed_tree = Tree("existential_quantification", [var, closed_tree])
    return closed_tree
