import copy

from functools import partialmethod
from typing import Literal 
from tqdm import tqdm
from lark import Lark, Tree, Token, Transformer
from lark.visitors import Visitor, Interpreter

from basic_formulas_manipulation import treeExplainer, P9FreeVariablesExtractor, ToPrenexCNF, ToString 
from check_modulo_signature_equivalence import find_equivalent, intersects_equivalence_classes
from check import P9Explainer

from model import prover9_parser, Signature, Model, P9ModelReader


class InformationAdder(Transformer):
    """Adds info about quantified variables and quantified atoms. The formula MUST be in prenex CNF"""
    def __init__(self, model: Model, visit_tokens = True):
        super().__init__(visit_tokens)
        self.model = model

    def equality_atom(self, items):
        info = {"atoms":{"=": {"weight": 0, "arity": 2, "arguments": [{"terms": items, "positive": True}]}}}
        ret = Tree("equality_atom", items)
        ret.explanation = info
        return ret
    def predicate(self, items):
        predicate_symbol, *terms = items
        print(items)
        terms = [term.value for term in terms]
        arity = len(terms)
        weight = len(self.model.ordered_truth_table[predicate_symbol])
        info = {"atoms":{predicate_symbol.value: {"weight": weight, "arity": arity, "arguments": [{"terms": terms, "positive": True}]}}}
        ret = Tree("predicate", items)
        ret.explanation = info
        return ret
    def info_binary_op(self, items, op: str):
        left, right = items
        merged = copy.deepcopy(left.explanation)
        for predicate_symbol, info in right.explanation["atoms"].items():
            if not predicate_symbol in merged["atoms"].keys():
                merged["atoms"].update({predicate_symbol: copy.deepcopy(info)})
            else:
                merged["atoms"][predicate_symbol]["arguments"] = list(set(merged["atoms"][predicate_symbol]["arguments"]).union(set(copy.deepcopy(right.explanation["atoms"][predicate_symbol]["arguments"]))))
        ret = Tree(op, items)
        ret.explanation = merged
        return ret
    conjunction = conjunction_exc = partialmethod(info_binary_op, op = "conjunction")
    disjunction = disjunction_exc = partialmethod(info_binary_op, op = "disjunction")
    entailment = entailment_exc = partialmethod(info_binary_op, op = "entailment")
    reverse_entailment = reverse_entailment_exc = partialmethod(info_binary_op, op = "reverse_entailment")
    equivalence_entailment = equivalence_entailment_exc = partialmethod(info_binary_op, op = "equivalence_entailment")

    def negation(self, items):
        info = items[0].explanation
        if len(info.keys()) > 1:
            raise TypeError(f"Negation got information: {items}. This should not happen if the formula is in PCNF!")
        negated_info = copy.deepcopy(info)
        negated_atom_symmbol, negated_atom_info = list(negated_info["atoms"].items())[0]
        if not negated_atom_info["arguments"][0]["positive"]: 
            raise TypeError(f"Negation got information: {items} where the one predicate is negated. This should not happen if the formula is in PCNF!")
        negated_atom_info["arguments"][0]["positive"] = False
        ret = Tree("negation", items)
        ret.explanation = negated_info
        return ret
    negation_exc = negation
    def quantification(self, items, op: str):
        variable, inner_formula = items
        merged = copy.deepcopy(inner_formula.explanation)
        if not "quantifications" in merged.keys():
            merged.update({"quantifications": [(op, variable.value)]})
        else:
            merged = copy.deepcopy(inner_formula.explanation)
            merged["quantifications"] = [(op, variable.value)] + copy.copy(inner_formula.explanation["quantifications"])
        
        ret = Tree(op, items)
        ret.explanation = merged
        return ret
    universal_quantification = partialmethod(quantification, op="all")
    existential_quantification = partialmethod(quantification, op="exists")

# model_text = """A(v).A(u).A(8).B(v).C(x)."""
# axiom_text = """exists Y A(Y) & B(Y).
#                 all Y A(Y) & B(Y).
#                 all X A(X) <-> B(X).
#                 exists X C(X)."""
# axiom_text = """exists X C(X)."""
# axiom_text = """exists Y all X A(X) <-> - B(X)."""
# p9model = P9ModelReader()
# modelAST: Tree = prover9_parser.parse(model_text)       
# axiomAST: Tree = prover9_parser.parse(axiom_text)
# model = p9model.read_model(modelAST)
# infoAdd = InformationAdder(model = model)
# annotatedAxiomaAst = infoAdd.transform(axiomAST)
# treeExplainer(axiomAST)
# treeExplainer(annotatedAxiomaAst)
# # print(annotatedAxiomaAst.pretty())
# quit()




class P9SparseEvaluator(Interpreter):
    """..."""
    def evaluate(self

class P9Evaluator(Interpreter):
    """Evaluates a sentence give a model. 
    E.g. all X A(X) is True given the model with one constant c and the statement A(c)"""
    
    def __init__(self, model: Model = Model(), options: list[str] = []):#, to_explain: bool = True):
        super().__init__()
        self.model = model
        self.is_a_tqdm_running = False
        self.options = options
        self.quantification_type_to_inner_truth_value = {"universal":False, "existential":True}
        # if not set(options) <= POSSIBLE_OPTIONS: raise AssertionError(f"Called with options={options}, but options can only be {POSSIBLE_OPTIONS}")
        if "equivalence" in options:
            self.p9extractor = P9FreeVariablesExtractor()
            self.equivalences = {frozenset({"="}):[set(model.signature.constants)]} # Equality is added since the way the models are written every costant is '='-equivalent
            for predicate in self.model.signature.predicates: 
                self.equivalences.update({frozenset({predicate}): find_equivalent(self.model.ordered_truth_table[predicate], self.model)})
        # self.to_explain = to_explain

    def get_equivalent_representatives(self, tree, substitutions: dict[str,str]):
        free_variables, axiom_signature = self.p9extractor.extract_free_variables_and_signature(tree)
        predicates_in_scope = axiom_signature.predicates.keys()
        predicates_fset = frozenset(predicates_in_scope)
        for pred in predicates_in_scope:
            if not frozenset({pred}) in self.equivalences:
                print(f"The predicate {pred} was found in an axiom but not in the model. I *assume* that this is intended to mean that all {pred}-assertions are false and, thus, in the equivalence strategy only a {pred}-equivalence-class exists. I am gonna add it now.")
                self.equivalences[frozenset({pred})] = [set(self.model.signature.constants)]
        # note that in both cases the (deep!) copy is necessary otherwise the original data will be modified by the subsequent operations leading to wrong behavior
        if not predicates_fset in self.equivalences:
            classes = intersects_equivalence_classes([[clazz.copy() for clazz in self.equivalences[frozenset({pred})]] for pred in predicates_in_scope], self.model)
            self.equivalences[predicates_fset] = classes
        else:
            classes = [clazz.copy() for clazz in self.equivalences[predicates_fset]] 
        # now, if there are constants in the axiom coming either by the original axiom or by some subsequent substution, they must be removed from non-singleton equivalence classes and added to singletons
        set_constants = set(axiom_signature.constants).union(set(substitutions.values()))
        for clazz in classes:
            if (intersection:=clazz.intersection(set_constants)): 
                for element in intersection:
                    clazz.remove(element)
        classes = [x for x in classes if x!=set()] # some classes could be empty now
        for constant in set_constants:
            classes.append({constant})
        representatives = [] 
        for clazz in classes:
            if len(clazz) > 0:
                representatives.append(list(clazz)[0])
        # print(f"representatives are len {len(representatives)} and they are {representatives} and the classes are \n {classes}")
        return representatives

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

    def quantification(self, tree: Tree, quantification_type: Literal["universal", "existential"]) -> bool:
        quantified_variable, quantified_formula = tree.children
        substitutions = tree.additional_data.copy()
        if quantified_variable.value in substitutions: raise AssertionError(f"Found same variable symbol doubly quantified! It should not happen. Variable is {quantified_variable} for {quantified_formula}")
        
        # this part takes care of the execution of eventual strategies
        constants_to_check = self.model.signature.constants
        if "equivalence" in self.options:
            constants_to_check = self.get_equivalent_representatives(tree, substitutions)

        # this part decides if a loading bar should be activated 
        if not self.is_a_tqdm_running:
            iterator=tqdm(constants_to_check, "Loading bar for the first quantifier...")
            self.is_a_tqdm_running = True
        else:
            iterator = constants_to_check
        
        attempted_subsss: list[dict[str,str]] = []
        for constant in iterator:
            substitutions.update({quantified_variable.value: constant}) 
            truth_value = self.visit_with_memory(quantified_formula, substitutions)
            if truth_value == self.quantification_type_to_inner_truth_value[quantification_type]: 
                tree.explanation = f"{truth_value} with {substitutions}"
                if isinstance(iterator,tqdm): iterator.clear()
                return self.quantification_type_to_inner_truth_value[quantification_type]
            attempted_subsss.append(substitutions.copy())
        tree.explanation = f"{truth_value} with {attempted_subsss}"
        if isinstance(iterator,tqdm): iterator.clear()
        return not self.quantification_type_to_inner_truth_value[quantification_type]
    
    def universal_quantification(self, tree: Tree):
        return self.quantification(tree, "universal")
    def existential_quantification(self, tree: Tree):
        return self.quantification(tree, "existential")


    def entails(self, tree: Tree): 
        body, head = tree.children
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


    