import multiprocessing.pool
# import multiprocessing
# import multiprocess as multiprocessing
import re
import time
from typing import Literal 
import concurrent
from tqdm import tqdm
from lark import Lark, Tree, Token, Transformer
from lark.visitors import Visitor, Interpreter

from basic_formulas_manipulation import ReduceLogicalSignature, RemoveLabels, RemoveLines, treeExplainerRED, treeExplainerYELLOW, treeExplainerReturning, treeExplainerReturningNoExpl, P9FreeVariablesExtractor
from check_by_range_restriction import evaluateQuantifierBound, toBoundedMinifiedNNF, toBoundedMinifiedPCNF, toBoundedPDNF
from check_modulo_signature_equivalence import find_equivalent, intersects_equivalence_classes

from join_algorithms import Relation
from model import prover9_parser, Signature, Model, P9ModelReader

POSSIBLE_OPTIONS = {"equivalence", "range"}

# text = '(all X (cat(X) <-> (ed(X) & (exists T1 (pre(X,T1))) & all T (pre(X,T) -> tat(X,T)))))'
# text = '(A(c) & B(y))'
# text = '(P(c1,c2) & Q(x) & T(v)) .'
# text = '''(P(c1,c2) & Q(x) & T(v)) .
#             Q(c)    . '''
# text = '''(P(c1,c2) & Q(x) & T(v)) .
#             True    . 
#             (P(c, c4) & True)    . 
#             False    . '''
# text = 'all X A(X,Y) .'
# text = 'all X A(X,Y,c2) .'
# text = 'all X A(X,Y,c2) & P(X,Z,c) .'
# text = 'all X A(X,Y) & exists Z P(Z) .'
# text = 'all X all Y exists V A(X,Y,c2) & exists Z P(X,Z,c) | V(V,C,T,l).'
# text = 'all X A(X,Y,c2) | - exists Z P(X,Z,c) .'

# def run_fastest(f1, f2):
#     queue = multiprocessing.Queue()

#     p1 = multiprocessing.Process(target=f1, args=(queue,))
#     p2 = multiprocessing.Process(target=f2, args=(queue,))

#     p1.start()
#     p2.start()

#     # Get the first result
#     result = queue.get()

#     # Terminate both processes just in case both are still running
#     p1.terminate()
#     p2.terminate()

#     # Join to clean up the resources
#     p1.join()
#     p2.join()

#     return result

def run_fastest(f1, f2):
    with concurrent.futures.ThreadPoolExecutor() as executor:
        futures = [executor.submit(f) for f in (f1, f2)]
        done, not_done = concurrent.futures.wait(
            futures, return_when=concurrent.futures.FIRST_COMPLETED)

        # Get the result of the first completed future
        result = next(iter(done)).result()

        print("Got result", result)
        # Cancel remaining futures if possible
        for future in not_done:
            future.cancel()

    return result


class P9Explainer(Visitor):
    """Visits tree and reads explanations of evaluation. Obsolete, use treeExplainer """
    
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

class P9Evaluator(Interpreter):
    """Evaluates a sentence give a model. 
    E.g. all X A(X) is True given the model with one constant c and the statement A(c)"""
    
    def __init__(self, model: Model = Model(), options: list[str] = []):#, to_explain: bool = True):
        super().__init__()
        self.model = model
        self.is_a_tqdm_running = False
        self.options = options
        self.quantification_type_to_inner_truth_value = {"universal":False, "existential":True}
        if not set(options) <= POSSIBLE_OPTIONS: raise AssertionError(f"Called with options={options}, but options can only be {POSSIBLE_OPTIONS}")
        if "equivalence" in options:
            self.p9extractor = P9FreeVariablesExtractor()
            self.equivalences = {frozenset({"="}):[set(model.signature.constants)]} # Equality is added since the way the models are written every costant is '='-equivalent
            for predicate in self.model.signature.predicates: 
                self.equivalences.update({frozenset({predicate}): find_equivalent(self.model.ordered_truth_table[predicate], self.model)})
        if "range" in options:
            self.boundEvaluator = evaluateQuantifierBound(ranged_variable="", model=model)
            self.tree_to_bound_map = {}

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
        self.original_tree = tree
        ret = self.visit(tree)
        self.visited_tree = tree
        if ret == None:
            raise TypeError("This should not happen!")
        return ret
    # this way I ensure I can visit with some input data
    def visit_with_memory(self, tree, additional_data = {}):
            tree.additional_data = additional_data

            return self.visit(tree)

    def pass_by(self, tree: Tree):
        return self.visit_children(tree)
    def pass_car_and_explain(self, tree: Tree):
        truth_value_list = self.visit_children(tree)[0]
        return truth_value_list 
    def pass_car(self, tree: Tree):
        return self.visit_children(tree)[0]
    def pass_empty_substitutions_and_set_flag(self, tree: Tree):
        assert (children_len := len(tree.children)) == 1 or (children_len == 2 and isinstance(tree.children[-1],Token)), f"A line should only have one child or two with the second being a label token. Is something wring with the grammar? Tree is {tree} and is also in red {treeExplainerRED(tree)}"
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
        quantified_variable, *bounding_formula_list, quantified_formula = tree.children
        if bounding_formula_list == []:
            bounded = False
        else:
            if not "range" in self.options: raise TypeError("Received a bounded quantifier but range is not an option")
            bounded = True
            bounding_formula = bounding_formula_list[0]
            if bounding_formula in self.tree_to_bound_map:
                bound = self.tree_to_bound_map[bounding_formula]
            else:
                self.boundEvaluator.ranged_variable = quantified_variable
                bound_relation: Relation = self.boundEvaluator.transform(bounding_formula)
                if len(bound_relation.tuple_header) == 0 and bound_relation.tuple_set == False:
                    bound = set()
                elif not (len(bound_relation.tuple_header) == 1 and bound_relation.tuple_header[0] == quantified_variable):
                    open("delete-evaluated-bounding.txt", "w", encoding="utf-8").write(treeExplainerReturningNoExpl(bounding_formula))
                    open("delete-visited.txt", "w", encoding="utf-8").write(treeExplainerReturningNoExpl(self.visited_tree))
                    open("delete-evaluated.txt", "w", encoding="utf-8").write(treeExplainerReturningNoExpl(self.original_tree))
                    open("delete-tree.txt", "w", encoding="utf-8").write(treeExplainerReturningNoExpl(tree))
                    raise TypeError(f"In {quantification_type}, bounded formula evaluation returned an unexpected result: {bound_relation}. I've saved the tree received by the evaluator in delete-evaluated.txt and the bound being evaluated in delete-evaluated-bound.txt. The node in question is {tree} (printed to delete-tree.txt)")
                else:
                    bound = {t[0] for t in bound_relation.tuple_set} # de-tuple the singleton tuples
                self.tree_to_bound_map.update({bounding_formula:bound})
                
        substitutions = tree.additional_data.copy()
        if quantified_variable.value in substitutions: raise AssertionError(f"Found same variable symbol doubly quantified! It should not happen. Variable is {quantified_variable} for {quantified_formula}")
        
        # this part takes care of the execution of eventual strategies
        constants_to_check = self.model.signature.constants
        if "equivalence" in self.options:
            constants_to_check = self.get_equivalent_representatives(tree, substitutions)            
        if bounded:
            constants_to_check = set(constants_to_check).intersection(bound)
            
        # case that there are no constants to check
        if len(constants_to_check) == 0:
            tree.explanation = f"{quantification_type == "universal"} because no constants to check (possibly after bound evaluation and equivalence class reductions)"
            return quantification_type == "universal"

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
    
    existential_quantification_bounded = existential_quantification
    universal_quantification_bounded = universal_quantification


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
    
    def true(self, tree: Tree):
        tree.explanation = f"True with anything"
        return True
    def false(self, tree: Tree):
        tree.explanation = f"False with anything"
        return False

def loop_on_file(file_path: str, action) -> None:
    lines = open(file_path, "rt").readlines()
    for line in lines:
        no_comment_line = re.sub("%.*", "", line)
        no_comment_line = no_comment_line.replace("\n","")
        if no_comment_line in ["", "\n"] :
            continue
        axiom = no_comment_line
        ...

def read_model_file(model_file: str) -> Model:
    """Read file as a whole and returns corresponding model"""
    model_text = open(model_file, "rt").read()
    print("reading model file as a whole...")
    no_comment_model_text = re.sub("%.*", "\n", model_text)
    
    p9reader = P9ModelReader()
    modelAST: Tree = prover9_parser.parse(no_comment_model_text)       
    model = p9reader.read_model(modelAST)

    if "=" in model.signature.predicates:
        raise TypeError(f"Equality was found in the model. It should not be there, and instead all constants should be assumed to be different")

    print(f"...read model file. The model has {len(model.signature.constants)} constants and {len(model.signature.predicates)} predicates")
    print(f"The model ordered table is >>> {model.ordered_truth_table}")
    print(f"The model truth table is >>> {model.truth_table}")
    return model

# model = read_model_file("model.p9")

def check_axioms_file(axioms_file: str, model: Model, options: list[str], timeout: int, timeout_aux: int, no_timeout: bool, multiprocessing_required = False, processes_number = 4):
    """Read file line by line as a whole and checks axioms one-by-one against given model"""
    
    lines = open(axioms_file, "rt").readlines()
    
    if not multiprocessing_required:
        check_lines(lines, model, options, timeout, timeout_aux, no_timeout)
    else: 
        if processes_number < 1: raise TypeError(f"Asked for multiprocessing with non-positive process number")
        subliness = [lines[i::processes_number] for i in range(processes_number)]
        for sublines in subliness:
            process = ...
            process.execute(check_lines, sublines, model, options)

def check_lines(lines: list[str], model: Model, options: list[str], timeout: int, timeout_aux: int, no_timeout: bool):    
    p9variables = P9FreeVariablesExtractor()
    p9evaluator = P9Evaluator(model, options)
    p9evaluator_equivalence = P9Evaluator(model, ["equivalence"])
    p9explainer = P9Explainer()
    p9remover = RemoveLabels()
    
    axioms_true = 0
    axioms_false = 0
    axioms_unexpected = 0
    
    # for line in tqdm(lines):
    for line in lines:
        no_comment_line = re.sub("%.*", "", line) # the regex "%.*\n" is wrong because it will not match the last line of a file
        no_comment_line = no_comment_line.replace("\n","")
        if no_comment_line in ["", "\n"] :
            continue
        if "set(prolog_style_variables)" in no_comment_line: #ignore setting options
            continue
        axiom_text = no_comment_line
        axiomsAST: Tree = p9remover.transform((prover9_parser.parse(axiom_text)))
        free_variables, axiom_signature = p9variables.extract_free_variables_and_signature(axiomsAST)
        if "=" in model.signature.predicates:
            raise TypeError(f"Equality was found in the model. It should not be there, and instead all constants should be assumed to be different")
        if len(free_variables) > 0:
            raise TypeError(f"An axiom was found with a free, unquantified, variable. The axiom is {axiom_text}. The free variables are {free_variables} and the parsed tree is {axiomsAST.pretty()}")
        if (not set(axiom_signature.constants) <= set(model.signature.constants)):
            raise TypeError(f"An axiom was found with a constant that does not appear in the model!, the problematic constants are {set(axiom_signature.constants).difference(set(model.signature.constants))}")
        if (not set(axiom_signature.predicates) <= set(model.signature.predicates)):
            print(f"Warning: An axiom was found with a predicate that does not appear in the model! axioms_signature.predicates = {axiom_signature.predicates} and model.signature.predicates={model.signature.predicates}. This may or may not be correct (if it is a matter of the equality it is correct).")
        for predicate, arity in axiom_signature.predicates.items():
            if predicate in model.signature.predicates and model.signature.predicates[predicate] != arity:
                raise TypeError(f"An axiom was found with the predicate {predicate} of arity {arity}, but in the model the same predicate has arity {model.signature.predicates[predicate]}!")


        print(f"evaluating >>>{axiom_text}<<< against given model...")
        
        axiomsAST_for_equivalence = axiomsAST
        
        # if "range" in options:
        #     # axiomsAST = ReduceLogicalSignature().visit_repeatedly(axiomsAST)
        #     # axiomsAST = toBoundedMinifiedPCNF(simple).adjust_transform_repeatedly(axiomsAST)
            
        #     axiomsAST = toBoundedMinifiedNNF().adjust_transform_repeatedly(axiomsAST) # <- nukes on continuant-part-of-has-weak-supplementation-at-a-time
            
        #     # axiomsAST = toBoundedPDNF().adjust_transform_repeatedly(axiomsAST)
            
            
        def f_equivalences(axiomsAST_for_equivalence, p9evaluator_equivalence):
            print("Started f_equivalences")
            try:
                evaluation = p9evaluator_equivalence.evaluate(axiomsAST_for_equivalence)
            except Exception as e:
                raise TypeError(f"Got an exception during f_equivalences: >>>{e}<<<")
            return evaluation, axiomsAST#, f"Default parallel equivalence strategy was faster than the strategy called with the options {options}"
            
        def f_options(axiomsAST, p9evaluator, toBMNNF, options):
            print("Started f_options")
            try:
                if "range" in options:
                    axiomsAST = toBMNNF.adjust_transform_repeatedly(axiomsAST) # <- nukes on continuant-part-of-has-weak-supplementation-at-a-time
                evaluation = p9evaluator.evaluate(axiomsAST)
            except Exception as e:
                raise TypeError(f"Got an exception during f_option: >>>{e}<<<")
            return evaluation, axiomsAST#, f"The strategy called with the options {options} was faster than the default equivalence strategy"
        # try: 

            # future = run_fastest(f_equivalences, f_options)
            # evaluation, message
            # print(message)
            
        timeout = 10
        timeout_aux = 60
        
        if not no_timeout:
            evaluation = "possible time out"
            try:
                with multiprocessing.pool.ThreadPool() as pool:
                    evaluation, axiomsAST_from_multithread = pool.apply_async(f_options, args=[axiomsAST, p9evaluator, toBoundedMinifiedNNF(), options]).get(timeout = timeout)
                    axiomsAST = axiomsAST_from_multithread
            except multiprocessing.TimeoutError:
                print("==="*50)
                print("Timeout! passing to next strat")
                print("==="*50)
                try:
                    with multiprocessing.pool.ThreadPool() as pool:
                        evaluation, axiomsAST_from_multithread = pool.apply_async(f_equivalences, args = [axiomsAST_for_equivalence, p9evaluator_equivalence]).get(timeout = timeout_aux)
                        axiomsAST = axiomsAST_from_multithread
                except multiprocessing.TimeoutError:
                    print("==="*50)
                    print("Timeout again! Nothing worked!")
                    open("delete-exception-equivalence.txt","w",encoding = "utf-8").write(treeExplainerReturning(axiomsAST_for_equivalence))
                    open("delete-exception-options.txt","w",encoding = "utf-8").write(treeExplainerReturning(axiomsAST))
                    print("==="*50)
                except Exception as e:
                    raise TypeError(f"got from second strat {e}")
            except Exception as e:
                raise TypeError(f"got from first strat {e}")
        else: 
            evaluation = "not executed yet"
            evaluation = p9evaluator.evaluate(axiomsAST)
        
        
        # evaluation = p9evaluator.evaluate(axiomsAST)
        # except Exception as e:
        #     open("delete-exception-equivalence.txt","w",encoding = "utf-8").write(treeExplainerReturning(axiomsAST_for_equivalence))
        #     open("delete-exception-options.txt","w",encoding = "utf-8").write(treeExplainerReturning(axiomsAST))
        #     raise Exception(f"Got exception during evaluation (input was the printed in delete-exception-options/equivalence.txt): >>>{e}<<<")
        
        print(f"...evaluation result is >>>{evaluation}<<<")
        if evaluation == [False]:
            axioms_false += 1
            print(f"Evaluation of axiom >>>{axiom_text}<<< is False! Generating explanation...")
            #p9explainer.explain(axiomsAST)
            treeExplainerRED(axiomsAST)
            with open("explanation.txt", "w", encoding="utf-8") as fo:
                fo.write(treeExplainerReturning(axiomsAST))
            print(f"Above should have appeared an explanation of why >>>{axiom_text}<<< is False. See also the local file 'explanation.txt' in case the generated explanation does not fit the screen")
            break #TODO
        elif evaluation == [True]:
            axioms_true += 1
        else:
            print(f"This axiom was evaluated to >>>{evaluation}<<<. This should not happen.")
            axioms_unexpected += 1
    print(f"Axioms analysis ended. Found {axioms_true}/{axioms_true+axioms_false+axioms_unexpected} true axioms and {axioms_false}/{axioms_true+axioms_false+axioms_unexpected} false axioms.")
    if axioms_false > 0:
        print(f"Some axioms ({axioms_false}) were evaluated as false. Check printed output for information on which they were and why they were evaluated as false. See also the local file 'explanation.txt' in case the generated explanation does not fit the screen.")
    if axioms_unexpected > 0:
        print(f"Some axioms ({axioms_unexpected}) were evaluated to an unexpected value. Check printed output for information on which they were and what they were evaluated to.")

def check_model_against_axioms(model_file: str, axioms_file: str, options: list[str], timeout: int, timeout_aux: int, no_timeout: bool)->None:
    start1 = time.time()
    model = read_model_file(model_file)
    stop1 = time.time()
    
    start2 = time.time()
    check_axioms_file(axioms_file, model, options, timeout, timeout_aux, no_timeout)
    stop2 = time.time()
    print(f"To read model {stop1-start1} seconds were required")
    print(f"To check axioms {stop2-start2} seconds were required")


class P9SignatureExtractor(Transformer):
    """Extract the signature from a formula. E.g. all X A(X,Y,c2) | - exists Z P(X,Z,c) .  ---> {A, P}"""

    def equality_atom(self, items):
        return {"="}
    
    def predicate(self, items):
        predicate_symbol, *term_list = items
        predicate_symbol = predicate_symbol.value
        arity = len(term_list)
        return {predicate_symbol}

    def existential_quantification(self, items):
        quantified_variable, signature_from_inner_formula = items
        return signature_from_inner_formula
    universal_quantification = existential_quantification
    
    merge_signatures = lambda self, items: set().union(*(var_set for var_set in items))
    
    conjunction = merge_signatures
    disjunction = merge_signatures
    conjunction_exc = merge_signatures
    disjunction_exc = merge_signatures
    entailment = merge_signatures
    reverse_entailment = merge_signatures
    equivalence_entailment = merge_signatures
    entailment_exc = merge_signatures
    reverse_entailment_exc = merge_signatures
    equivalence_entailment_exc = merge_signatures
    negation = merge_signatures
    negation_exc = merge_signatures

    do_nothing = lambda self, items: items
    car = lambda self, items: items[0]
    start = car
    lines = car
    line = car
    sentence = car

    label = lambda self, items: None

def test_signature_extraction():
    p9sig = P9SignatureExtractor()
    assert p9sig.transform(prover9_parser.parse("all X exists Y P(X,Y) & X=Y .")) == {'=', 'P'}; print("""p9sig.transform(prover9_parser.parse("all X exists Y P(X,Y) & X=Y .")) == {'=', 'P'}""")
    assert p9sig.transform(prover9_parser.parse("((all X exists Y P(X,Y) & X=Y) | (exists X exists Z all U all V (E(X,y,Z) & R(U,V)))) .")) == {'=', 'P', 'E', 'R'}; print("""p9sig.transform(prover9_parser.parse("((all X exists Y P(X,Y) & X=Y) | (exists X exists Z all U all V (E(X,y,Z) & R(U,V)))) .")) == {'=', 'P', 'E', 'R'}""")
    assert p9sig.transform(prover9_parser.parse("all X all Y P(X) & Q(Y) .")) == {'P', 'Q'}; print("""p9sig.transform(prover9_parser.parse("all X all Y P(X) & Q(Y) .")) == {'P', 'Q'}""")


def benchmark():
    axioms = """(all X all Y all Z all T all TAU cP(X,Y,T) & cP(Y,Z,TAU) & tP(T,TAU) -> cP(X,Z,T)).
        (cP(x,z,t)).
        (all X (cP(x,z,t) | False)).
        (True)."""
    axioms = axioms.split("\n")
    model_txt = """cP(x,y,t).cP(y,z,tau).tP(t,tau).cP(x,z,t).

        C(x).C(y).C(z).
        T(t).T(tau).
        cP(x,x,t).cP(x,x,tau).
        cP(y,y,t).cP(y,y,tau).
        cP(z,z,t).cP(z,z,tau).
        tP(t,t).
        tP(tau,tau).

        cP(y,z,t).

        P(p)."""
    
    def add_counter_with_options(func):
        def wrapper(*args, **kwargs):
            s = time.perf_counter()
            out = func(*args, **kwargs)
            e = time.perf_counter()
            return f"Execution time of {func.__name__} is {e-s}, if with options = {kwargs["options"]}"
        return wrapper
    for i in range(10):
        model_txt += (".".join([f"P({i*10+j})" for j in range(5)]) + ".")
        model = P9ModelReader().read_model(prover9_parser.parse(model_txt))
        print(f"Working with model with constants: {model.signature.constants}")
        #o1 = add_counter_with_options(check_lines)(axioms, model, options = []) <- this explodes soon
        o2 = add_counter_with_options(check_lines)(axioms, model, options = ["equivalence"])
        o3 = add_counter_with_options(check_lines)(axioms, model, options = ["range"])
        o4 = add_counter_with_options(check_lines)(axioms, model, options = ["equivalence","range"])
        print("\n",o2,"\n",o3,"\n",o4) #print("\n",o1,"\n",o2,"\n",o3,"\n",o4)
    for i in range(10):
        model_txt += f"cP(x{i},y{i},t{i}).cP(y{i},z{i},tau{i}).tP(t{i},tau{i}).cP(x{i},z{i},t{i})."
        model = P9ModelReader().read_model(prover9_parser.parse(model_txt))
        print(f"Working with model with constants: {model.signature.constants}")
        #o1 = add_counter_with_options(check_lines)(axioms, model, options = []) <- this explodes soon
        # o2 = add_counter_with_options(check_lines)(axioms, model, options = ["equivalence"]) <- this also explodes in this case
        o3 = add_counter_with_options(check_lines)(axioms, model, options = ["range"])
        o4 = add_counter_with_options(check_lines)(axioms, model, options = ["equivalence","range"])
        print("\n",o3,"\n",o4) #print("\n",o1,"\n",o2,"\n",o3,"\n",o4)


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(prog='FOL model checker',description='Simply supply the location of a file containing a model and of a file containing a theory')
    parser.add_argument('-m', '--model_file', type = str, help="Model file location")
    parser.add_argument('-a', '--axioms_file', type = str, help="Axiom file location")
    parser.add_argument('-o', '--options', type = str, nargs = "+", default = [], help="Options. Currently only 'equivalence' and 'range' are supported")
    parser.add_argument('-t', '--timeout', type = int, default = 10, help="Timeout of the chosen strategy, in seconds. After the timeout the auxillary strategy will be called")
    parser.add_argument('-taux', '--timeout_aux', type = int, default = 120, help="Timeout of the auxillary strategy, in seconds.")
    parser.add_argument('-nout', '--no_timeout', type = bool, default = False, help="Deactivates the timeout system.")
    args = parser.parse_args()
    check_model_against_axioms(args.model_file, args.axioms_file, args.options, args.timeout, args.timeout_aux, args.no_timeout)
    #check_model_against_axioms(r"BFO_p9\BFO-model-from-repo.p9", r"BFO_p9\continuant-mereology_toUP.p9", ["range"])