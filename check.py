import sys
import re 
from tqdm import tqdm
from lark import Lark, Tree, Token, Transformer
from lark.visitors import Visitor, Interpreter

prover9_parser = Lark(r"""

start: lines

lines: line+

line: (sentence | atomicsentence) label? "."

?label: "#" "label(" LABEL_TEXT ")"
                      
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

?atomicsentence: predicate
                | equality_atom
                | predicate0
                | "(" sentence ")"
                | "(" entailterm ")"

?equality_atom: term "=" term
                | term "=" "(" term ")" // there is this horrendous possibility also
                | "(" term ")" "=" term 
                | "(" term ")" "=" "(" term ")"
                //| term "!=" term // not gonna bother with this symbol
                      
?term: CONSTANT // there are no functions
    | VARIABLE

atomicstatement: PREDICATE_SYMBOL "(" _constant_list ")"

predicate0 : "True" -> true
           | "False" -> false
predicate: PREDICATE_SYMBOL "(" _term_list ")"
PREDICATE_SYMBOL:  /[a-zA-Z][a-zA-Z0-9]*_?\d*/
_term_list: (term ",")* term
_constant_list: (CONSTANT ",")* CONSTANT
CONSTANT: /[a-z]+_?\d*/ 
VARIABLE: /[A-Z]+_?\d*/  // uppercase style
LABEL_TEXT: /[a-zA-Z0-9_-]+/

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
        self.model_text = ""
        self.signature = Signature()
    def __str__(self):
        if self.model_text == "":
            return f"""
                    truth_table: {self.truth_table}
                    """
        else: 
            return "\nMODEL>>>\t"+model_text
    def add_predicate_value(self, predicate_symbol: str, arguments: tuple[str | Token]):
        arguments = tuple(str(argument) for argument in arguments)
        if (predicate_symbol,arguments) not in self.truth_table: 
            self.truth_table[(predicate_symbol,arguments)] = True

            
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

class P9Explainer(Visitor):
    """Visits tree and reads explanations of evaluation"""
    
    def explain(self, tree: Tree):
        self.visit(tree)
        return ">>>explanation should appear nearby<<<"

    def explain_(self, tree: Tree):
        if hasattr(tree, "explanation"):
            print(f"node {tree.data} with presentation \n {tree.pretty()} --> {tree.explanation}")
    
    equality_atom = explain_
    predicate = explain_
    existential_quantification = explain_
    universal_quantification = explain_
    conjunction = explain_
    disjunction = explain_
    conjunction_exc = explain_
    disjunction_exc = explain_
    entailment = explain_
    reverse_entailment = explain_
    equivalence_entailment = explain_
    entailment_exc = explain_
    reverse_entailment_exc = explain_
    equivalence_entailment_exc = explain_
    negation = explain_
    negation_exc = explain_

    # do_nothing = lambda self, items: items
    # car = lambda self, items: items[0]
    # start = car
    # lines = car
    # line = car
    # sentence = car

    # label = lambda self, items: None

class P9FreeVariablesExtractor(Transformer):
    """Extract all free variables from a formula. E.g. all X A(X,Y,c2) | - exists Z P(X,Z,c) .  ---> {X}
        Also adds constant and predicates to self.axioms_signature"""
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
                raise AssertionError(f"Found non-token {token} in predicate {predicate_symbol}. This should not happen")
            if (token.type == "CONSTANT"): 
                self.axioms_signature.add_constant(token)
            if (token.type == "VARIABLE"): 
                variable_set.add(token.value)
        self.axioms_signature.add_predicate(predicate_symbol, arity:=len(term_list))
        return variable_set

    def quantification(self, items):
        quantified_variable, variables_from_inner_formula = items
        if not isinstance(quantified_variable, Token) or not isinstance(variables_from_inner_formula, set):
            raise TypeError(f"Something wrong with returned variables: {quantified_variable} or {variables_from_inner_formula}")
        difference = variables_from_inner_formula.difference({quantified_variable.value})
        return difference
    existential_quantification = quantification
    universal_quantification = quantification
    
    merge_variables = lambda self, items: set().union(*(var_set for var_set in items))
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

    do_nothing = lambda self, items: items
    car = lambda self, items: items[0]
    start = car
    lines = car
    line = car
    sentence = car

    label = lambda self, items: None

# out=P9FreeVariablesExtractor().transform(prover9_parser.parse("(all X0 all X1 (ach(X0) & temporallyLocatedAt(X0,X1) -> at(X1))) # label(achievemants_atomic_Ad75)."))
# print(out)
# s()

# global_counter = 0
# def merge_subs(*args, global_counter = global_counter):
#     collected = {}

#     for arg in args:
#         for key in arg.keys() & collected.keys():
#             if arg[key] != collected[key]:
#                 value = collected[key]
#                 global_counter += 1
#                 arg.update({key + "dis" + str(global_counter): value}) 
#         collected.update(arg)
#     return collected
# # print(merge_subs({"X":"a"}, {"Y":"b"}, {"X":"z"}, {"X":"u", "V":"v"}))
# print(merge_subs([{"X":"a"}]))
# s()
# print(merge_subs({"X":"a"}, [{"Y":"b"}]))
# print(merge_subs([{"X":"a"}], [{"Y":"b"}]))

# s()


class P9Evaluator(Interpreter):
    """Evaluates a sentence give a model. 
    E.g. all X A(X) is True given the model with one constant c and the statement A(c)"""
    
    def __init__(self, model: Model = Model()):#, to_explain: bool = True):
        super().__init__()
        self.model = model
        self.is_a_tqdm_running = False
        # self.to_explain = to_explain

    def evaluate(self, tree: Tree):
        return self.visit(tree)
    # this way I ensure I can visit with some input data
    def visit_with_memory(self, tree, additional_data = {}):
            # for child in tree.children:
            #     if not isinstance(child,Token):
            #         print(22222222222222222222222222222)
            #         print(child)
            #         child.additional_data = additional_data
            #         print(vars(child))
            tree.additional_data = additional_data

            return self.visit(tree)

    def pass_by(self, tree: Tree):
        return self.visit_children(tree)
    def pass_car_and_explain(self, tree: Tree):
        truth_value_list = self.visit_children(tree)[0]
        
        # P9Explainer().visit(tree)
        return truth_value_list 
    def pass_car(self, tree: Tree):
        return self.visit_children(tree)[0]
    def pass_empty_substitutions_and_set_flag(self, tree: Tree):
        assert (children_len := len(tree.children)) == 1 or (children_len == 2 and isinstance(tree.children[-1],Token)), f"A line should only have one child or two with the second being a label token. Is something wring with the grammar? Tree is {tree}"
        self.is_a_tqdm_running = False
        if children_len == 1:
            (child,) = tree.children
        else:
            child, label = tree.children
        ret = self.visit_with_memory(child, {})
        return ret
    start = pass_car_and_explain
    lines = pass_by
    line = pass_empty_substitutions_and_set_flag

    def universal_quantification(self, tree: Tree):
        quantified_variable, quantified_formula = tree.children
        substitutions = tree.additional_data.copy()
        successful_substitutionss: list[dict[str,str]] = []
        if quantified_variable.value in substitutions: raise AssertionError(f"Found same variable symbol doubly quantified! It should not happen. Variable is {quantified_variable} for {quantified_formula}")
        if not self.is_a_tqdm_running:
            iterator=tqdm(self.model.signature.constants, "Loading bar for the first quantifier...")
            self.is_a_tqdm_running = True
        else:
            iterator = self.model.signature.constants
        for constant in iterator:
            substitutions.update({quantified_variable.value: constant}) 
            truth_value = self.visit_with_memory(quantified_formula, substitutions)
            if truth_value == False: 
                tree.explanation = f"{truth_value} with {substitutions}"
                if isinstance(iterator,tqdm): iterator.clear()
                return False
            successful_substitutionss.append(substitutions.copy())
        tree.explanation = f"{truth_value} with {successful_substitutionss}"
        if isinstance(iterator,tqdm): iterator.clear()
        return True
    
    def existential_quantification(self, tree: Tree):
        quantified_variable, quantified_formula = tree.children
        substitutions = tree.additional_data.copy()
        if quantified_variable.value in substitutions: raise AssertionError(f"Found same variable symbol doubly quantified! It should not happen. Variable is {quantified_variable} for {quantified_formula} and substitution is {substitutions}")
        failed_subss: list[dict[str,str]] = []
        if not self.is_a_tqdm_running:
            iterator=tqdm(self.model.signature.constants, "Loading bar for the first quantifier...")
            self.is_a_tqdm_running = True
        else:
            iterator = self.model.signature.constants
        for constant in iterator:
            substitutions.update({quantified_variable.value: constant}) 
            truth_value = self.visit_with_memory(quantified_formula, substitutions)
            if truth_value == True: 
                tree.explanation = f"{truth_value} with {substitutions}"
                if isinstance(iterator,tqdm): iterator.clear()
                return True
            failed_subss.append(substitutions.copy())
        tree.explanation = f"{truth_value} with {failed_subss}"
        if isinstance(iterator,tqdm): iterator.clear()
        return False


    def entails(self, tree: Tree): 
        body, head = tree.children
        #print("in entails with body", body.pretty(), tree.additional_data)
        truth_value = ((not self.visit_with_memory(body, tree.additional_data)) or (self.visit_with_memory(head, tree.additional_data)))
        tree.explanation = f"{truth_value} with {tree.additional_data}"
        return truth_value#, merge_subs(head_subs, body_subs)
    def reverse_entails(self, tree: Tree): 
        head, body = tree.children
        truth_value = ((not self.visit_with_memory(body, tree.additional_data)) or (self.visit_with_memory(head, tree.additional_data)))
        tree.explanation = f"{truth_value} with {tree.additional_data}"
        return truth_value#, merge_subs(head_subs, body_subs)
    def biconditional(self, tree: Tree): 
        definendum, definient = tree.children
        truth_value = ((self.visit_with_memory(definendum, tree.additional_data) and self.visit_with_memory(definient, tree.additional_data)) or ((not self.visit_with_memory(definendum, tree.additional_data)) and (not self.visit_with_memory(definient, tree.additional_data))))
        tree.explanation = f"{truth_value} with {tree.additional_data}"
        return truth_value
    entailment = entailment_exc = entails
    reverse_entailment = reverse_entailment_exc = reverse_entails
    equivalence_entailment = equivalence_entailment_exc = biconditional
    
    def disjunction(self, tree: Tree): 
        left_addendum, right_addendum = tree.children
        truth_value = (self.visit_with_memory(left_addendum, tree.additional_data) or self.visit_with_memory(right_addendum, tree.additional_data))
        tree.explanation = f"{truth_value} with {tree.additional_data}"
        return truth_value#, merge_subs(left_subs, right_subs)
    disjunction_exc = disjunction
    
    def conjunction(self, tree: Tree): 
        left_factor, right_factor = tree.children
        truth_value = (self.visit_with_memory(left_factor, tree.additional_data) and self.visit_with_memory(right_factor, tree.additional_data))
        tree.explanation = f"{truth_value} with {tree.additional_data}"
        return truth_value
    conjunction_exc = conjunction

    def negation(self, tree: Tree): 
        (negatum,) = tree.children
        value = self.visit_with_memory(negatum, tree.additional_data)
        truth_value = not value
        tree.explanation = f"{truth_value} with {tree.additional_data}"
        return truth_value
    negation_exc = negation

    def predicate(self, tree: Tree):
        substitutions = tree.additional_data
        predicate_symbol, *term_list = tree.children
        try:
            replaced_terms = tuple(substitutions[term.value] if term.type == "VARIABLE" else term.value for term in term_list)
        except KeyError:
            raise KeyError(f"Got key error due to a variable not in substitutions dictionary. This means that the variable is not properly quantified. Either something went wrong or a non-closed formula was evaluated (which should not happen). This happened in term list {term_list} with substitution {substitutions}")
        truth_value = (predicate_symbol,replaced_terms) in self.model.truth_table
        tree.explanation = f"{truth_value} with {tree.additional_data}"
        return truth_value
    
    def equality_atom(self, tree: Tree):
        left_member, right_member = tree.children
        
        substitutions = tree.additional_data
        
        if not isinstance(left_member, Token) or not isinstance(right_member, Token):
            raise AssertionError(f"Non-token object in equality atom. This should not happen. It was one of these: {left_member.children[0], right_member.children[0]} in the equality {self}")
        if left_member.type == "VARIABLE":
            left_member = substitutions[left_member.value]
        if right_member.type == "VARIABLE":
            right_member = substitutions[right_member.value]
        truth_value = str(left_member) == str(right_member)
        tree.explanation = f"{truth_value} with {tree.additional_data}"
        return truth_value


def loop_on_file(file_path: str, action) -> None:
    lines = open(file_path, "rt").readlines()
    for line in lines:
        no_comment_line = re.sub("%.*\n", "", line)
        no_comment_line = no_comment_line.replace("\n","")
        if no_comment_line in ["", "\n"] :
            continue
        axiom = no_comment_line
        ...

def read_model_file(model_file: str) -> Model:
    """Read file as a whole and returns corresponding model"""
    model_text = open(model_file, "rt").read()
    print("reading model file as a whole...")
    no_comment_model_text = re.sub("%.*\n", "\n", model_text)
    
    p9reader = P9ModelReader()
    modelAST: Tree = prover9_parser.parse(no_comment_model_text)       
    model = p9reader.read_model(modelAST)

    if "=" in model.signature.predicates:
        raise TypeError(f"Equality was found in the model. It should not be there, and instead all constants should be assumed to be different")

    return model

# model = read_model_file("model.p9")

def check_axioms_file(axioms_file: str, model: Model, multiprocessing_required = False, processes_number = 4):
    """Read file line by line as a whole and checks axioms one-by-one against given model"""
    
    lines = open(axioms_file, "rt").readlines()
    
    if not multiprocessing_required:
        check_lines(lines, model)
    else: 
        if processes_number < 1: raise TypeError(f"Asked for multiprocessing with non-positive process number")
        subliness = [lines[i::processes_number] for i in range(processes_number)]
        for sublines in subliness:
            process = ...
            process.execute(check_lines, sublines, model)
    


def check_lines(lines: list[str], model: Model):    
    p9variables = P9FreeVariablesExtractor()
    p9evaluator = P9Evaluator(model)
    p9explainer = P9Explainer()
    
    axioms_true = 0
    axioms_false = 0
    # for line in tqdm(lines):
    for line in lines:
        no_comment_line = re.sub("%.*\n", "", line)
        no_comment_line = no_comment_line.replace("\n","")
        if no_comment_line in ["", "\n"] :
            continue
        axiom_text = no_comment_line
        axiomsAST: Tree = prover9_parser.parse(axiom_text)
        free_variables, axiom_signature = p9variables.extract_free_variables_and_signature(axiomsAST)
        if len(free_variables) > 0:
            raise TypeError(f"An axiom was found with a free, unquantified, variable. The axiom is {axiom_text}.. The free variables are {free_variables} and the parsed tree is {axiomsAST.pretty()}")
    

        print(f"evaluating >>>{axiom_text}<<< against given model...")
        evaluation = p9evaluator.evaluate(axiomsAST)
        
        print(f"...evaluation result is >>>{evaluation}<<<")
        if evaluation == [False]:
            axioms_false += 1
            print(f"Evaluation of axiom >>>{axiom_text}<<< is False! Generating explanation...")
            p9explainer.explain(axiomsAST)
            print(f"Above should have appeared an explanation of why >>>{axiom_text}<<< is False")
            break #TODO
        else:
            axioms_true += 1
    print(f"Axioms analysis ended. Found {axioms_true}/{axioms_true+axioms_false} true axioms and {axioms_false}/{axioms_true+axioms_false} false axioms.")
    if axioms_false > 0:
        print(f"Some axioms were evaluated as false. Check printed output for information on which they were and why they were evaluated as false.")

def check_model_against_axioms(model_file: str, axioms_file: str)->None:
    model = read_model_file(model_file)
    check_axioms_file(axioms_file, model)



if __name__ == "__main__":
    check_model_against_axioms("DOLCE-clay-statue-model.p9", "DOLCE-clay-statue-axioms.p9")

    