from lark import Tree, Interpreter, Transformer

class PolarityAttatcher(Interpreter):
    def __init__(self):
        super().__init__()

    def visit_with_memory(self, tree, additional_data = {}):
            tree.additional_data = additional_data
            return self.visit(tree)
    def get_current_polarity(self, tree):
        return tree.additional_data["polarity"] if hasattr(tree, "additional_data") else 1
    
    def negation(self, tree):
        current_polarity = self.get_current_polarity(tree)
        tree.additional_data={"polarity":current_polarity}
        new_polarity = current_polarity*-1
        negated_formula = tree.children[0]
        self.visit_with_memory(negated_formula, additional_data={"polarity":new_polarity})
    negation_exc = negation
    
    def equivalence_entailment(self, tree):
        raise TypeError("I found an equivalence entailment. However, this is not allowed when adding polarity to a tree")
    equivalence_entailment_exc = equivalence_entailment

    def entailment(self, tree):
        current_polarity = self.get_current_polarity(tree)
        tree.additional_data={"polarity":current_polarity}
        premise, consequent = tree.children
        self.visit_with_memory(premise, additional_data={"polarity":current_polarity*-1})
        self.visit_with_memory(consequent, additional_data={"polarity":current_polarity})
    entailment_exc = entailment
    
    def reverse_entailment(self, tree):
        current_polarity = self.get_current_polarity(tree)
        tree.additional_data={"polarity":current_polarity}
        consequent, premise,  = tree.children
        self.visit_with_memory(premise, additional_data={"polarity":current_polarity*-1})
        self.visit_with_memory(consequent, additional_data={"polarity":current_polarity})
    reverse_entailment_exc = reverse_entailment
    
    def conjunction(self, tree):
        current_polarity = self.get_current_polarity(tree)
        tree.additional_data={"polarity":current_polarity}
        left, right = tree.children
        self.visit_with_memory(left, additional_data={"polarity":current_polarity})
        self.visit_with_memory(right, additional_data={"polarity":current_polarity})
    conjunction_exc = conjunction
    disjunction = conjunction
    disjunction_exc = conjunction

    def equality_atom(self, tree):
        current_polarity = self.get_current_polarity(tree)
        tree.additional_data = {"polarity":current_polarity}
        # extra_tree = Tree("polarity", [])
        # extra_tree.additional_data = {"polarity":current_polarity}
        # tree.children.append(extra_tree) #necessary due to inability of referencing current node in trensformer
        tree.children.append({"polarity":current_polarity}) #necessary due to inability of referencing current node in trensformer
    def predicate(self, tree):
        predicate_symbol, *term_list = tree.children
        current_polarity = self.get_current_polarity(tree)
        tree.additional_data = {"polarity":current_polarity}
        # predicate_symbol.additional_data = {"polarity":current_polarity} #doesnt work
        #setattr(predicate_symbol,"additional_data",{"polarity":current_polarity}) #doesnt work
        # extra_tree = Tree("polarity", [])
        # extra_tree.additional_data = {"polarity":current_polarity}
        # tree.children.append(extra_tree) #necessary due to inability of referencing current node in trensformer
        tree.children.append({"polarity":current_polarity}) #necessary due to inability of referencing current node in trensformer

    def existential_quantification(self, tree):
        current_polarity = self.get_current_polarity(tree)
        tree.additional_data={"polarity":current_polarity}
        quantified_variable, quantified_formula = tree.children
        self.visit_with_memory(quantified_formula, additional_data={"polarity":current_polarity})
    universal_quantification = existential_quantification

class GetPolarityFromBottom(Transformer):
    def negation(self, children):
        negated_formula = children[0]
        return -1*self.transform(negated_formula)
    negation_exc = negation
    
    def equivalence_entailment(self, children):
        raise TypeError("I found an equivalence entailment. However, this is not allowed when adding polarity to a tree")
    equivalence_entailment_exc = equivalence_entailment

    def entailment(self, children):
        premise, consequent = children
        premise_polarity = self.transform(premise)
        consequent_polarity = self.transform(consequent)
        if not premise_polarity == -1*consequent_polarity:
            raise TypeError(f"Something wrong occurred in the calculation of the polarities of the children ({children}): both children have the same polarity")
        return consequent_polarity
    entailment_exc = entailment
    
    def reverse_entailment(self, children):
        consequent, premise = children
        premise_polarity = self.transform(premise)
        consequent_polarity = self.transform(consequent)
        if not premise_polarity == -1*consequent_polarity:
            raise TypeError(f"Something wrong occurred in the calculation of the polarities of the children ({children}): both children have the same polarity")
        return consequent_polarity
    reverse_entailment_exc = reverse_entailment
    
    def conjunction(self, children):
        left, right = children
        left_polarity = self.transform(left)
        right_polarity = self.transform(right)
        if not left_polarity == right_polarity:
            raise TypeError(f"Something wrong occurred in the calculation of the polarities of the children ({children}): the children have different polarity")
        return left_polarity
    conjunction_exc = conjunction
    disjunction = conjunction
    disjunction_exc = conjunction

    def equality_atom(self, children):
        additional_data = children[-1]
        return additional_data["polarity"]
    def predicate(self, children):
        additional_data = children[-1]
        return additional_data["polarity"]

    def existential_quantification(self, children):
        quantified_variable, quantified_formula = children
        return self.transform(quantified_formula)
    universal_quantification = existential_quantification

class PolarityRemover(Transformer):
    def equality_atom(self, children):
        return Tree("equality_atom", children[:-1])
    def predicate(self, children):
        return Tree("predicate", children[:-1])

