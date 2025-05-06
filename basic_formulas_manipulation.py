from functools import partialmethod

from lark import Tree, Token, Transformer
from lark.visitors import Visitor, Interpreter

from model import prover9_parser, Signature, Model, P9ModelReader

from PrettyPrint import PrettyPrintTree
import ansi2html

BINARY_OPS = ["conjunction",
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

def getChildren(x):
    return (x.children if hasattr(x,"children") else None)
def getData(x):
    return (x.data if hasattr(x,"data") else str(x))
def getExplanation(x):
    if hasattr(x,"explanation"): return f"{x.data} is {str(x.explanation).replace("'","").replace(": ",":")}"
    if hasattr(x,"additional_data"): return f"{x.data} --- {x.additional_data}"
    if hasattr(x,"data"): return x.data
    return str(x)
    # return (f"{x.data} is {x.explanation}" if hasattr(x, "explanation") else (x.data if hasattr(x,"data") else str(x)))

from colorama import Back
treeExplainer = PrettyPrintTree(getChildren, getExplanation, color="")
treeExplainerRED = PrettyPrintTree(getChildren, getExplanation, color=Back.RED)
treeExplainerGREEN = PrettyPrintTree(getChildren, getExplanation, color=Back.GREEN)
treeExplainerReturning = PrettyPrintTree(getChildren, getExplanation, return_instead_of_print=True, color="")
treeExplainerReturningRED = PrettyPrintTree(getChildren, getExplanation, return_instead_of_print=True, color=Back.RED)
treeExplainerReturningGREEN = PrettyPrintTree(getChildren, getExplanation, return_instead_of_print=True, color=Back.GREEN)

ansi2htmlConverter = ansi2html.Ansi2HTMLConverter()

text0 = '(all X (cat(X) <-> (ed(X) & (exists T pre(X,T)) & all T (pre(X,T) -> tat(X,T))))).'
# text = '(all X (cat(X) <-> (ed(X) & (exists T1 (pre(X,T1))) & all T (pre(X,T) -> tat(X,T))))).'
# text = '(A(c) & B(y)).'
# text = '(P(c1,c2) & Q(x) & T(v)) .'
# text = '''(P(c1,c2) & Q(x) & T(v)) .
            # Q(c)    . '''
# text = '''(P(c1,c2) & Q(x) & T(v)) .
#             True    . 
#             (P(c, c4) & True)    . 
#             False    . '''
# text = 'all X A(X,Y) .'
text6 = 'all X A(X,Y,c2) .'
text5 = 'all X A(X,Y,c2) & P(X,Z,c) .'
text4 = 'all X A(X,Y) & exists Z P(Z) .'
text3 = 'all X all Y exists V A(X,Y,c2) & exists Z P(X,Z,c) | V(V,C,T,l).'
text2 = 'all X A(X,Y,c2) | - exists Z P(X,Z,c) .'
text2pre = 'all X all Z A(X,Y,c2) | - P(X,Z,c) .'
text1 = 'all X all Y all Z all T all T2 A(X,Y,T) & A(Y,Z,T2) & B(T,T2) -> A(X,Z,T) .'


ast0=prover9_parser.parse(text0)
ast1=prover9_parser.parse(text1)
ast2=prover9_parser.parse(text2)
ast3=prover9_parser.parse(text3)
ast4=prover9_parser.parse(text4)
ast5=prover9_parser.parse(text5)
# treeExplainer(ast)
# s()

class P9FreeVariablesExtractor(Transformer):
    """Extract all free variables and predicates from a formula. E.g. all X A(X,Y,c2) | - exists Z P(X,Z,c) .  ---> {X}; {A:3, P:3, c:0, c2:0}
        Can be used repeatedly on different formulas. """
    def __init__(self, visit_tokens = True):
        super().__init__(visit_tokens)
        self.axioms_signature = Signature()

    def extract_free_variables_and_signature(self, tree: Tree) -> tuple[set[str],Signature]:
        out_vars = self.transform(tree)
        out_signature = self.axioms_signature
        self.axioms_signature = Signature()
        return out_vars, out_signature

    def equality_atom(self, items):
        left_member, right_member = items
        variables_set: set[str] = set()
        self.axioms_signature.add_predicate("=",2)
        if not isinstance(left_member, Token) or not isinstance(right_member, Token):
            raise AssertionError(f"Either the left member or the right member of the equality atom {items} is not a Token. This should never happen")
        if left_member.type == "VARIABLE":
            variables_set.add(left_member.value)
        elif left_member.type == "CONSTANT":
            self.axioms_signature.add_constant(left_member)
        if right_member.type == "VARIABLE":
            variables_set.add(right_member.value)
        elif right_member.type == "CONSTANT":
            self.axioms_signature.add_constant(right_member)
        return variables_set
    
    def predicate(self, items):
        predicate_symbol, *term_list = items
        predicate_symbol = predicate_symbol.value
        variable_set: set[str] = set()
        for token in term_list:
            if not isinstance(token, Token):
                # Now this can happen when using polarity...
                if isinstance(token, dict) and "polarity" in token.keys():
                    pass # it's ok, do nothing
                else: # unrecognized case
                    raise AssertionError(f"Found non-token {token} in predicate {predicate_symbol} (and the non-token is not auxillary data about polarity). This should not happen")
                    # print(f"Attention: found non-token {token} in predicate {predicate_symbol}. Ensure this makes sense (if it is additional data about polarity it is intended)")
            else:
                if (token.type == "CONSTANT"): 
                    self.axioms_signature.add_constant(token)
                if (token.type == "VARIABLE"): 
                    variable_set.add(token.value)
        self.axioms_signature.add_predicate(predicate_symbol, arity:=len(term_list))
        return variable_set

    def quantification(self, items, thereIsBound = False):
        if thereIsBound:
            quantified_variable, bound, variables_from_inner_formula = items
        else:
            quantified_variable, variables_from_inner_formula = items
        if not isinstance(quantified_variable, Token) or not isinstance(variables_from_inner_formula, set):
            raise TypeError(f"Something wrong with returned variables: {quantified_variable} or {variables_from_inner_formula}")
        difference = variables_from_inner_formula.difference({quantified_variable.value})
        return difference
    existential_quantification = quantification
    universal_quantification = quantification
    existential_quantification_bounded = partialmethod(quantification, thereIsBound = True)
    universal_quantification_bounded = partialmethod(quantification, thereIsBound = True)

    def empty(self, items):
        return set()
    def dom(self, items):
        ranged_variable = items[0]
        return {str(ranged_variable)}
    
    # merge_variables = lambda self, items: set().union(*(var_set for var_set in items))
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
    def __init__(self, visit_tokens = False):
        super().__init__(visit_tokens)

    def transform_repeatedly(self, tree):
        oldtree = tree
        newtree = self.transform(oldtree)
        while newtree != oldtree:
            oldtree = newtree
            newtree = self.transform(newtree)
        return newtree
    
    def flatten_and_or(self, items, op: str):
        print(items)
        new_items = []
        for item in items:
            if item.data in [op, op+"_exc"]:
                new_items.extend(item.children)
            else:
                new_items.append(item)
        return Tree(op, new_items)
    conjunction = conjunction_exc = partialmethod(flatten_and_or, op = "conjunction")
    disjunction = disjunction_exc = partialmethod(flatten_and_or, op = "disjunction")

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
            return Tree(op, variables + additional_variables + [doubly_quantified_formula])
        return Tree(op, items)
    universal_quantification = partialmethod(quantification, op="universal_quantification")
    existential_quantification = partialmethod(quantification, op="existential_quantification")

# axiom_text = """exists Y exists Z all X all U all UU exists T exists TT ((A(X) | -U(X) | K(X,Z)) & (B(X,Y) | -V(X,Y,Z)) & (C(Z)))."""
# axiomAST = prover9_parser.parse(axiom_text)
# flattener = AssociativeFlattener()
# flatAst = flattener.transform_repeatedly(axiomAST)
# treeExplainer(axiomAST)
# treeExplainer(flatAst)
# quit()

class TypeChecker(Interpreter):
    def __init__(self):
        self.axioms_signature = Signature()
        self.isUniversalRule = "maybe"
    
    # def equality_atom(self, items):
    #     return True 
    # def predicate(self, items):
    #     return True 
    def isUniversal(self, tree: Tree):
        self.isUniversalRule = True
        self.visit(tree)
        out = self.isUniversalRule
        self.isUniversalRule = "maybe"
        return out
    
    def conjunction(self, tree):
        left, right = tree.children
        if not(left.data in ["conjunction", "predicate", "equality_atom"] and right.data in ["conjunction", "predicate", "equality_atom"]):
            print(f"auch at {tree.data}")
            self.isUniversalRule = False
        self.visit_children(tree)

    def universal_quantification(self, tree):
        variable, quantified_formula = tree.children
        if not(quantified_formula.data in ["entailment", "conjunction", "predicate", "equality_atom", "universal_quantification"]):
            print(f"auch at {tree.data}")
            self.isUniversalRule = False
        self.visit_children(tree)
    
    def must_not_appear(self, tree): 
        print(f"auch at {tree.data}")
        self.isUniversalRule = False
    
    existential_quantification = must_not_appear

    disjunction = must_not_appear
    conjunction_exc = must_not_appear
    disjunction_exc = must_not_appear
    reverse_entailment = must_not_appear
    equivalence_entailment = must_not_appear
    entailment_exc = must_not_appear
    reverse_entailment_exc = must_not_appear
    equivalence_entailment_exc = must_not_appear
    negation = must_not_appear
    negation_exc = must_not_appear

    # car = lambda self, tree: tree.children[0]
    # start = car
    # lines = car
    # line = car
    # sentence = car
    # label = lambda self, items: None
    
# tc = TypeChecker()
# treeExplainer(ast1)
# print(tc.isUniversalRule)
# print(tc.isUniversal(ast1))
# print(tc.isUniversalRule)
# print(tc.isUniversal(ast2))
# print(tc.isUniversal(ast3))
# print(tc.isUniversal(ast4))
# print(tc.isUniversal(ast5))

def dual_quantifier(string):
    q_set = {"existential_quantification", "universal_quantification"}
    if not string in q_set:
        raise TypeError(f"Dual quantifier got {string}")
    return q_set.difference({string}).pop()
def dual_op(string):
    op_map = {"existential_quantification": "universal_quantification",
              "universal_quantification": "existential_quantification",
              "conjunction": "disjunction",
              "disjunction": "conjunction",
              "false": "true",
              "true": "false",
              }
    if not string in op_map.keys():
        raise TypeError(f"Operation should not be called to get dual. Operation was {string}")
    return op_map[string]

class ReplaceVariable(Transformer):
    """Replaces a variable with another"""
    def __init__(self, replaced: str, replacing: str, visit_tokens = True):
        super().__init__(visit_tokens)
        self.replaced = replaced
        self.replacing = replacing

    def VARIABLE(self, value):
        return Token(type_="VARIABLE", value=value.replace(self.replaced, self.replacing))

# rp = ReplaceVariable("X", "X0")
# treeExplainer(rp.transform(ast1))
# s()
class ToUniqueVariables(Transformer):
    """Each quantified variable will have a unique name"""
    def __init__(self, visit_tokens = True):
        super().__init__(visit_tokens)
        self.quantified_variables = set()

    def adjust_variables(self, tree):
        self.quantified_variables = set()
        out_tree = self.transform(tree)
        self.quantified_variables = set()
        return out_tree
    def quantification(self, items, quantification_type):
        quantified_variable, inner_formula = items
        if quantified_variable.value in self.quantified_variables:
            new_name = quantified_variable.value + str(len(self.quantified_variables))
            self.quantified_variables.add(new_name)
            rp = ReplaceVariable(quantified_variable.value, new_name)
            replacing_inner_formula = rp.transform(inner_formula)
            return Tree(quantification_type, [Token(type_ = "VARIABLE", value = new_name), replacing_inner_formula])
        self.quantified_variables.add(quantified_variable.value)
        return Tree(quantification_type, [quantified_variable, inner_formula])

    def universal_quantification(self, items):
        return self.quantification(items, "universal_quantification")
    def existential_quantification(self, items):
        return self.quantification(items, "existential_quantification")

# unique = ToUniqueVariables()
# treeExplainer(ast0)
# treeExplainer(unique.adjust_variables(ast0))
# s()

class ToPrenex(Transformer):
    """Transform a formula in prenex normal form"""
    def __init__(self, visit_tokens = True):
        super().__init__(visit_tokens)

    def adjust_transform_repeatedly(self, tree):
        unique = ToUniqueVariables()
        adjusted_tree = unique.adjust_variables(tree)
        oldtree = adjusted_tree
        newtree = unique.adjust_variables(self.transform(adjusted_tree))
        while newtree != oldtree:
            # print("I am transforming an additional time")
            oldtree = newtree
            newtree = unique.adjust_variables(self.transform(oldtree))
        return newtree

    def entailment(self, children):
        left, right = children
        if right.data in ["existential_quantification", "universal_quantification"] and not left.data in ["existential_quantification", "universal_quantification"]:
            quantified_variable, quantified_formula = right.children
            return Tree(right.data, [quantified_variable, Tree("entailment", [left, quantified_formula])])
        if left.data in ["existential_quantification", "universal_quantification"] and not right.data in ["existential_quantification", "universal_quantification"]:
            quantified_variable, quantified_formula = left.children
            return Tree(dual_quantifier(left.data), [quantified_variable, Tree("entailment", [quantified_formula, right])])
        if left.data in ["existential_quantification", "universal_quantification"] and right.data in ["existential_quantification", "universal_quantification"]:
            left_quantified_variable, left_quantified_formula = left.children
            right_quantified_variable, right_quantified_formula = right.children
            return Tree(dual_quantifier(left.data), [left_quantified_variable, Tree(right.data, [right_quantified_variable, Tree("entailment", [left_quantified_formula, right_quantified_formula])])])
        return Tree("entailment", children)
    entailment_exc = entailment
    def reverse_entailment(self, children):
        left, right = children
        return self.entailment([right, left])
    equivalence_entailment_exc = reverse_entailment
        
    def symmetric_op(self, children, operator: str):
        left, right = children
        if right.data in ["existential_quantification", "universal_quantification"] and not left.data in ["existential_quantification", "universal_quantification"]:
            quantified_variable, quantified_formula = right.children
            return Tree(right.data, [quantified_variable, Tree(operator, [left, quantified_formula])])
        if left.data in ["existential_quantification", "universal_quantification"] and not right.data in ["existential_quantification", "universal_quantification"]:
            quantified_variable, quantified_formula = left.children
            return Tree(left.data, [quantified_variable, Tree(operator, [quantified_formula, right])])
        if left.data == "universal_quantification" and right.data == left.data and operator == "conjunction":
            # (all X phi(X)) & (all Y psi(Y)) ---> all X (phi(X) & psi(X))
            left_quantified_variable, left_quantified_formula = left.children
            right_quantified_variable, right_quantified_formula = right.children
            replace = ReplaceVariable(replaced=right_quantified_variable, replacing=left_quantified_variable)
            replaced_right_quantified_formula = replace.transform(right_quantified_formula)
            return Tree(left.data, [left_quantified_variable, Tree("conjunction", [left_quantified_formula, replaced_right_quantified_formula])])
        if left.data == "existential_quantification" and right.data == left.data and operator == "disjunction":
            # (exists X phi(X)) | (exists Y psi(Y)) ---> exists X (phi(X) | psi(X))
            left_quantified_variable, left_quantified_formula = left.children
            right_quantified_variable, right_quantified_formula = right.children
            replace = ReplaceVariable(replaced=right_quantified_variable, replacing=left_quantified_variable)
            replaced_right_quantified_formula = replace.transform(right_quantified_formula)
            return Tree(left.data, [left_quantified_variable, Tree("disjunction", [left_quantified_formula, replaced_right_quantified_formula])])
        if left.data in ["existential_quantification", "universal_quantification"] and right.data in ["existential_quantification", "universal_quantification"]:
            left_quantified_variable, left_quantified_formula = left.children
            right_quantified_variable, right_quantified_formula = right.children
            return Tree(left.data, [left_quantified_variable, Tree(right.data, [right_quantified_variable, Tree(operator, [left_quantified_formula, right_quantified_formula])])])
        return Tree(operator, children)
    # disjunction = partial(binary_op, operator = "disjunction")
    def disjunction(self,children):
        return self.symmetric_op(children, "disjunction")
    disjunction_exc = disjunction
    # conjunction = partial(binary_op, operator = "conjunction")
    def conjunction(self,children):
        return self.symmetric_op(children, "conjunction")
    conjunction_exc = conjunction

    def equivalence_entailment(self, children):
        left, right = children
        return Tree("conjunction", [Tree("entailment", [left, right]), Tree("entailment", [right, left])])
        # return self.conjunction([self.entailment([left, right]), self.entailment([right, left])])
    equivalence_entailment_exc = equivalence_entailment

    def negation_exc(self, children):
        negated_formula = children[0]
        if negated_formula.data in ["existential_quantification", "universal_quantification"]:
            quantified_variable, quantified_formula = negated_formula.children
            return Tree(dual_quantifier(negated_formula.data), [quantified_variable, Tree("negation", [quantified_formula])])
        return Tree("negation", children)
    negation = negation_exc

    # do_nothing = lambda self, items: items
    # car = lambda self, items: items[0]
    # start = car
    # lines = car
    # line = car
    # sentence = car

    # label = lambda self, items: None

# tp=ToPrenex()
# textp = 'all X (exists Y R(X,Y)) & (exists Z P(X,Z)).'
# textp = '((all X (exists Y R(X,Y))) & (all X(exists Z P(X,Z)))).'
# textp = '((exists X (all Y R(X,Y))) | (exists X (all Z P(X,Z)))).'
# textp = '((all X (exists Y R(X,Y))) | (all X(exists Z P(X,Z)))).'
# astp=prover9_parser.parse(textp)
# treeExplainer(astp)
# treeExplainer(tp.adjust_transform_repeatedly(astp))
# quit()

# treeExplainer(ast0)
# ast00 = tp.adjust_transform_repeatedly(ast0)
# treeExplainer(ast00)
# treeExplainer(ast1)
# ast11 = tp.adjust_transform_repeatedly(ast1)
# treeExplainer(ast11)
# treeExplainer(ast2)
# ast22 = tp.adjust_transform_repeatedly(ast2)
# treeExplainer(ast22)
# treeExplainer(ast3)
# ast33 = tp.adjust_transform_repeatedly(ast3)
# treeExplainer(ast33)
# treeExplainer(ast4)
# ast44 = tp.transform(ast4)
# treeExplainer(ast44)
# treeExplainer(ast5)
# ast55 = tp.transform(ast5)
# treeExplainer(ast55)
# s()

class ToConjunctiveNormalForm(Interpreter):
    """Transform a propositional formula in conjunctive normal form. Non propositional operators are ignored"""
    # def __init__(self, visit_tokens = True):
    #     super().__init__(visit_tokens)

    def visit_repeatedly(self, tree):
        oldtree = tree
        newtree = self.visit(oldtree)
        while newtree != oldtree:
            oldtree = newtree
            newtree = self.visit(oldtree)
        return newtree

    def entailment(self, tree):
        left, right = tree.children
        return Tree("disjunction", [Tree("negation", [self.visit(left)]), self.visit(right)])
    entailment_exc = entailment
    def reverse_entailment(self, tree):
        left, right = tree.children
        return self.entailment([right, left])
    equivalence_entailment_exc = reverse_entailment
        
    def disjunction(self, tree):
        left, right = tree.children
        if right.data == "conjunction":
            sub_left, sub_right = right.children
            return Tree("conjunction", [Tree("disjunction", [self.visit(left), self.visit(sub_left)]), Tree("disjunction", [self.visit(left), self.visit(sub_right)])])
        if left.data == "conjunction":
            sub_left, sub_right = left.children
            return Tree("conjunction", [Tree("disjunction", [self.visit(right), self.visit(sub_left)]), Tree("disjunction", [self.visit(right), self.visit(sub_right)])])
        return Tree("disjunction", self.visit_children(tree))
    disjunction_exc = disjunction

    def equivalence_entailment(self, tree):
        left, right = tree.children
        return Tree("conjunction", [Tree("entailment", [self.visit(left), self.visit(right)]), Tree("entailment", [self.visit(right), self.visit(left)])])
    equivalence_entailment_exc = equivalence_entailment

    def false(self, tree):
        return Tree("false", [])
    def true(self, tree):
        return Tree("true", [])
    
    def negation(self, tree):
        print(111111111111)
        treeExplainer(tree)
        negated_formula = tree.children[0]
        if negated_formula.data in ["disjunction", "conjunction"]:
            left, right = negated_formula.children
            return Tree(dual_op(negated_formula.data), [Tree("negation", [self.visit(left)]), Tree("negation", [self.visit(right)])])
        if negated_formula.data in ["negation", "negation_exc"]:
            sub_negated_formula = negated_formula.children[0]
            return self.visit(sub_negated_formula)
        if negated_formula.data in ["true", "false"]:
            return Tree(dual_op(negated_formula.data), [])
        return Tree("negation", self.visit_children(tree))
    negation_exc = negation

    def pass_par_rule(self, tree, par: str):
        return Tree(Token("RULE", par) , self.visit_children(tree))
    def pass_par(self, tree, par: str):
        return Tree(par , self.visit_children(tree))
    def terminate(self, tree):
        return tree
    start = partialmethod(pass_par_rule, par = "start")
    lines = partialmethod(pass_par_rule, par = "lines")
    line = partialmethod(pass_par_rule, par = "line")
    conjunction = partialmethod(pass_par, par = "conjunction")
    universal_quantification = partialmethod(pass_par, par = "universal_quantification")
    existential_quantification = partialmethod(pass_par, par = "existential_quantification")
    # def universal_quantification(self, tree):
    #     return Tree("universal_quantification", [])
    predicate = terminate
    equality_atom = terminate
    VARIABLE = terminate
    # start = proceeds #pass_car
    # lines = proceeds #pass_by
    # line = proceeds #visit_self

class ToPrenexCNF():
    """Transform a formula in prenex conjunctive normal form."""
    def __init__(self):
        self.toPrenex = ToPrenex()
        self.toCNF = ToConjunctiveNormalForm()
    def transform_repeatedly(self, tree):
        oldtree = tree
        newtree_pre = self.toPrenex.adjust_transform_repeatedly(oldtree)
        newtree = self.toCNF.visit_repeatedly(newtree_pre)
        while newtree != oldtree:
            oldtree = newtree
            newtree_pre = self.toPrenex.adjust_transform_repeatedly(oldtree)
            newtree = self.toCNF.visit_repeatedly(newtree_pre)
        return newtree
    
# toCNF = ToConjunctiveNormalForm()
# toPCNF = ToPrenexCNF()
# text = "(P(x,y) & Q(a,b) & C(z) -> R(a))."
# text = "((P(x,y) & Q(a,b)) | (C(z) & R(a)))."
# text = "((P(x,y) & Q(a,b)) | (C(z)) )."
# text = "(- (((P(x,y) & -Q(a,b)) | (C(z)))) )."
# text = "((P(x,y) & Q(a,b)) | (C(z) <-> R(a)))."
# text = "(all X p(X) & - (exists Y (q(X,Y))))."
# text = "(all X p(X) & - (exists Y (q(X,Y))))."
# text = '(all X all Y all Z all T all T2 A(X,Y,T) & A(Y,Z,T2) & B(T,T2) -> A(X,Z,T)).'
# text = '(all X all Y all Z all T (A(X,Y,T) & (exists T2 (A(Y,Z,T2) & B(T,T2))) -> A(X,Z,T))).'
# ast = prover9_parser.parse(text)
# treeExplainer(ast)
# cnfTree = toCNF.visit_repeatedly(ast)
# pcnfTree = toPCNF.transform_repeatedly(ast)
# treeExplainer(cnfTree)
# treeExplainer(pcnfTree)
# quit()



class ToReversePrenexCNF(Transformer):
    """Transform a formula in prenex CNF and transforms it in reverse prenex CNF normal form (push quantifiers in the innermost position possible)
    If the formula is not prenex CNF it will be made so before starting"""
    def __init__(self, visit_tokens = True):
        super().__init__(visit_tokens)
        self.freeVars = P9FreeVariablesExtractor()
        self.toPCNF = ToPrenexCNF()
        self.commutes = {"existential_quantification":"disjunction", "universal_quantification":"conjunction"}

    def adjust_transform_repeatedly(self, tree):
        # ensures the tree is PCNF
        PCNFtree = self.toPCNF.transform_repeatedly(tree)
        if PCNFtree != tree:
            print("I got a formula not in PCNF. I will transform it in PCNF and continue.")
            tree = PCNFtree

        unique = ToUniqueVariables()
        adjusted_tree = unique.adjust_variables(tree)
        oldtree = adjusted_tree
        newtree = unique.adjust_variables(self.transform(adjusted_tree))
        while newtree != oldtree:
            # print("I am transforming an additional time")
            oldtree = newtree
            newtree = unique.adjust_variables(self.transform(oldtree))
        return newtree

    def quantification(self, children, quantification_type: str):
        quantified_variable, quantified_formula = children
        if quantified_formula.data in ["negation", "negation_exc"]:
            negated_formula = quantified_formula.children[0]
            return Tree("negation", [Tree(dual_quantifier(quantification_type), [quantified_variable, negated_formula])])
        if quantified_formula.data in BINARY_OPS:
            left, right = quantified_formula.children
            if not quantified_variable in self.freeVars.transform(left) and not quantified_variable in self.freeVars.transform(right):
                raise TypeError(f"In quantified formula {quantified_formula} the quantified variable {quantified_variable} does not occurr! This should never happen.")
            if not quantified_variable in self.freeVars.transform(left):
                return Tree(quantified_formula.data, [left, Tree(quantification_type, [quantified_variable, right])])
            if not quantified_variable in self.freeVars.transform(right):
                return Tree(quantified_formula.data, [Tree(quantification_type, [quantified_variable, left]), right])
        if quantified_formula.data == self.commutes[quantification_type]:
            left, right = quantified_formula.children
            return Tree(quantified_formula.data, [Tree(quantification_type, [quantified_variable, left]), Tree(quantification_type, [quantified_variable, right])])
        return Tree(quantification_type, [quantified_variable, quantified_formula])
    existential_quantification = partialmethod(quantification, quantification_type = "existential_quantification")
    universal_quantification = partialmethod(quantification, quantification_type = "universal_quantification")

    def negation_exc(self, children):
        negated_formula = children[0]
        if negated_formula.data in ["negation", "negation_exc"]:
            doubly_negated_formula = negated_formula.children[0]
            return doubly_negated_formula
        return Tree("negation", children)
    negation = negation_exc

# tp=ToReversePrenexCNF()
# textp = '(all X -( A(X) | False)).'
# textp = 'all X (exists Y R(X,Y)) & (exists Z P(X,Z)).'
# textp = '((all X (exists Y R(X,Y))) & (all X(exists Z P(X,Z)))).'
# textp = '((exists X (all Y R(X,Y))) | (exists X (all Z P(X,Z)))).'
# textp = '((all X (exists Y R(X,Y))) | (all X(exists Z P(X,Z)))).'
# textp = '(all X exists Y (R(X,Y) | P(X,Z))).'
# textp = '(exists X - all Y (R(X,Y) |  P(X,Z))).'
# textp = '(all X all Y (R(X,Y) | P(Y))).'
# textp = '(all Y all X (R(X,Y) | P(Y))).'
# astp=prover9_parser.parse(textp)
# treeExplainer(astp)
# print(astp)
# # treeExplainer(ToPrenex().adjust_transform_repeatedly(astp))
# treeExplainer(tp.adjust_transform_repeatedly(astp))
# exit()


class ToString(Interpreter):
    """Transform a tree into a formatted string"""

    def print_binary_op(self, tree, op: str):
        # print(f"tree is {tree}, op is {op}")
        left, right = tree.children
        yes_left_par = left.data not in ["predicate", "equality_atom"]
        yes_right_par = right.data not in ["predicate", "equality_atom"]
        return "("*yes_left_par+self.visit(left)+")"*yes_left_par + f" {op} " + "("*yes_right_par+self.visit(right)+")"*yes_right_par
    entailment = partialmethod(print_binary_op, op = "->")
    reverse_entailment = partialmethod(print_binary_op, op = "<-")
    equivalence_entailment = partialmethod(print_binary_op, op = "<->")
    disjunction = partialmethod(print_binary_op, op = "|")
    conjunction = partialmethod(print_binary_op, op = "&")
    entailment_exc = entailment
    equivalence_entailment_exc = reverse_entailment
    equivalence_entailment_exc = equivalence_entailment
    disjunction_exc = disjunction
    conjunction_exc = conjunction

    def negation(self, tree):
        negated_formula = tree.children[0]
        return f"-({self.visit(negated_formula)})"
    negation_exc = negation

    def print_quantification_op(self, tree, op: str):
        variable, quantified_formula = tree.children
        return f"{op} {variable} ({self.visit(quantified_formula)})"
    universal_quantification = partialmethod(print_quantification_op, op = "all")
    existential_quantification = partialmethod(print_quantification_op, op = "exists")

    def print_bounded_quantification_op(self, tree, op: str):
        variable, bound, quantified_formula = tree.children
        bounding_formula = bound.children[0]
        return f"{op} ({variable} ∈ {{{variable} | {self.visit(bounding_formula)}}}) ({self.visit(quantified_formula)})"
    universal_quantification_bounded = partialmethod(print_bounded_quantification_op, op = "all")
    existential_quantification_bounded = partialmethod(print_bounded_quantification_op, op = "exists")

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

    def pass_par_rule(self, tree, par: str):
        return Tree(Token("RULE", par) , self.visit_children(tree))
    def pass_par(self, tree, par: str):
        return Tree(par , self.visit_children(tree))
    def start(self, tree):
        return self.visit(tree.children[0])
    def lines(self, tree):
        line_s: list = tree.children
        visited_line_s: list[str] = [self.visit(line) for line in line_s]
        return "\n".join(visited_line_s)
    def line(self, tree):
        formula = tree.children[0]
        return f"({self.visit(formula)})."

# text = '(all X all Y all Z all T (A(X,Y,T) & (exists T2 (A(Y,Z,T2) & B(T,T2))) -> A(X,Z,T))).'
# ast = prover9_parser.parse(text)
# treeExplainer(ast)
# tos = ToString()
# string = tos.visit(ast)
# print(string)
# quit()

class RemoveLines(Transformer):
    """removes start, lines, and line nodes. Works only if the tree starts with one start, then one lines, then one single line"""
    def start(self, children):
        assert children[0].data == "lines"
        lines = children[0]
        assert len(lines.children) == 1
        assert lines.children[0].data == "line"
        line = lines.children[0]
        return (axiom:=line.children[0])
    
def get_existential_closure(tree: Tree, exceptions = {}) -> Tree:
    free_vars: set[str] = P9FreeVariablesExtractor().extract_free_variables_and_signature()[0]
    vars_to_close = free_vars.difference(exceptions)
    closed_tree = tree.copy()
    for var in vars_to_close:
        closed_tree = Tree("existential_quantification", [var, closed_tree])
    return closed_tree



