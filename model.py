from lark import Lark, Tree, Token, Transformer
from lark.visitors import Visitor, Interpreter

prover9_parser = Lark(r"""

start: lines

lines: line+

line: (sentence | atomicsentence) label? "."

label: "#" "label(" LABEL_TEXT ")"

?sentence: "exists" VARIABLE entailterm -> existential_quantification
          | "all" VARIABLE entailterm -> universal_quantification
          | "exists" VARIABLE sentence -> existential_quantification
          | "all" VARIABLE sentence -> universal_quantification

?entailterm: addendum
        | entailterm "->" addendum -> entailment
        | entailterm "<-" addendum -> reverse_entailment
        | entailterm "<->" addendum -> equivalence_entailment
        | entailterm "->" sentence -> entailment_exc
        | entailterm "<-" sentence -> reverse_entailment_exc
        | entailterm "<->" sentence -> equivalence_entailment_exc

?addendum: factor
        | addendum "|" factor -> disjunction
        | addendum "|" sentence -> disjunction_exc

?factor: literalatom
        | factor "&" literalatom -> conjunction
        | factor "&" sentence -> conjunction_exc

?literalatom: atomicsentence
            | "-" literalatom -> negation
            | "-" sentence -> negation_exc

?atomicsentence: dom
                | equality_atom
                | predicate0
                | "(" sentence ")"
                | "(" entailterm ")"
                | predicate

?equality_atom: term "=" term
                | term "=" "(" term ")" // there is this horrendous possibility also
                | "(" term ")" "=" term 
                | "(" term ")" "=" "(" term ")"
                //| term "!=" term // not gonna bother with this symbol
                      
?term: CONSTANT // there are no functions
    | VARIABLE

atomicstatement: PREDICATE_SYMBOL "(" _constant_list ")" // TODO: remove?
dom: "dom" "(" VARIABLE ")"

predicate0 : "True" -> true
           | "False" -> false
predicate: PREDICATE_SYMBOL "(" _term_list ")"
PREDICATE_SYMBOL:  /[a-zA-Z][a-zA-Z0-9]*_?\d*/
_term_list: (term ",")* term
_constant_list: (CONSTANT ",")* CONSTANT
CONSTANT: /[a-z0-9]+_?[0-9a-zA-Z]*/ 
VARIABLE: /[A-Z]+_?\d*/  // uppercase style
LABEL_TEXT: /"?[a-zA-Z0-9_\-\>\<\\.\+]+"?/ 

%import common.ESCAPED_STRING
%import common.SIGNED_NUMBER
%import common.WS
%ignore WS

""")

text = '(all X (cat(X) <-> (ed(X) & (exists T1 (pre(X,T1))) & all T (pre(X,T) -> tat(X,T)))))'
text = '(A(c) & B(y))'
text = '(P(c1,c2) & Q(x) & T(v)) .'
text = '''(P(c1,c2) & Q(x) & T(v)) .
            Q(c)    . '''
text = '''(P(c1,c2) & Q(x) & T(v)) .
            True    . 
            (P(c, c4) & True)    . 
            False    . '''
text = 'all X A(X,Y) .'
text = 'all X A(X,Y,c2) .'
text = 'all X A(X,Y,c2) & P(X,Z,c) .'
text = 'all X A(X,Y) & exists Z P(Z) .'
text = 'all X all Y exists V A(X,Y,c2) & exists Z P(X,Z,c) | V(V,C,T,l).'
text = 'all X A(X,Y,c2) | - exists Z P(X,Z,c) .'




class Signature:
    def __init__(self):
        self.predicates = {}
        self.constants = []
    def __str__(self):
        return f"""
                constants: {self.constants}
                predicates: {self.predicates}
                """
    def add_predicate(self, predicate_symbol: str | Token, arity: int):
        if isinstance(predicate_symbol, Token):
            predicate_symbol = predicate_symbol.value 
        if predicate_symbol in self.predicates: 
            if (arity0:=self.predicates[predicate_symbol]) != arity:
                raise TypeError(f"The symbol {predicate_symbol} is used with different arities: {arity0} and {arity}")
        else: 
            self.predicates.update({predicate_symbol:arity})
    def add_constant(self, constant_symbol: str | Token):
        if isinstance(constant_symbol, Token):
            constant_symbol = constant_symbol.value
        if constant_symbol not in self.constants: 
            self.constants.append(constant_symbol)

class Model:
    """Only true facts are recorded"""
    def __init__(self):
        self.truth_table = {}
        self.ordered_truth_table = {}
        self.model_text = ""
        self.signature = Signature()
    def __str__(self):
        if self.model_text == "":
            return f"""
                    truth_table: {self.truth_table}
                    """
        else: 
            return "\nMODEL>>>\t"+self.model_text
    def add_predicate_value(self, predicate_symbol: str, arguments: tuple[str | Token]):
        """Save both e.g. ('P', ('x', 'y')): True in truth_table and ('x', 'y'): True in ordered_truth_table['P']. The 'True' value is there in the case of needing to salve also false, or multivalued, values."""
        arguments = tuple(str(argument) for argument in arguments)
        if (predicate_symbol,arguments) not in self.truth_table: 
            self.truth_table[(predicate_symbol,arguments)] = True
        if predicate_symbol not in self.ordered_truth_table: 
            self.ordered_truth_table[predicate_symbol] = {arguments: True}
        elif not arguments in self.ordered_truth_table[predicate_symbol]:
            self.ordered_truth_table[predicate_symbol].update({arguments: True})
          
class P9ModelReader(Visitor):
    """Visits tree and add constants and predicates to self.model.signature; and adds true atomics statements to model"""
    
    def __init__(self):
        super().__init__()
        self.model = Model()

    def read_model(self, tree: Tree) -> Model:
        self.visit(tree)
        out_model = self.model
        self.model = Model()
        return out_model

    def predicate(self, tree):
        predicate_symbol, *term_list = tree.children
        predicate_symbol = predicate_symbol.value
        for token in term_list:
            if not isinstance(token, Token): raise AssertionError(f"There should only be tokens in predicates terms. Instead found {token} in {tree} in predicate {predicate_symbol}, which is not a Token")
            if (token.type == "VARIABLE"): raise AssertionError(f"There should not be variables in assertions when reading the model, only constants. Instead, I found the variable {token} in the predicate {predicate_symbol}")
            assert token.type == "CONSTANT"
            self.model.signature.add_constant(token)
        self.model.signature.add_predicate(predicate_symbol, arity:=len(term_list))
        self.model.add_predicate_value(predicate_symbol, tuple(term_list))

    def equality_atom(self, tree):
        left_member, right_member = tree.children
        variables_set = set()
        if not isinstance(left_member, Token) or not isinstance(right_member, Token):
            raise AssertionError(f"Non-token object in equality atom. This should not happen. It was one of these: {left_member.children[0], right_member.children[0]} in the equality {self}")
        if left_member.type == "VARIABLE" or right_member.type == "VARIABLE":
            raise AssertionError(f"There should not be variables in assertions when reading the model, only constants. Instead, I found a variable within {left_member, right_member} in the equality {self}")
        if left_member.type != "CONSTANT" or right_member.type != "CONSTANT":
            raise AssertionError(f"There should be constants within equalities when reading the model, only constants. Instead, I found these things {left_member, right_member} in the equality {self}")
        self.model.signature.add_constant(left_member)
        self.model.signature.add_constant(right_member)
        self.model.signature.add_predicate("=", 2)
        self.model.add_predicate_value("=", (left_member, right_member))
        return variables_set
    
    true = lambda self, _: True
    false = lambda self, _: False
