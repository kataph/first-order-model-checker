from lark import Lark
from lark.visitors import Interpreter

prop_parser = Lark(r"""
                   ?biconditional: entailment | biconditional "iff" entailment
                   ?entailment: disjunction | entailment "entails" disjunction
                   ?disjunction: conjunction | disjunction "or" conjunction
                   ?conjunction: literal | conjunction "and" literal 
                   ?literal: atom 
                           | "not" literal -> negation
                   ?atom: BASE_ATOM | parenthesized_prop
                   BASE_ATOM: /[A-Z][A-Z0-9]*/ 
                   ?parenthesized_prop: "(" biconditional ")"

                    %import common.WS
                    %ignore WS
                    """, start="biconditional")


from lark import Tree, Token

class PropEvaluator(Interpreter): 
    """Evaluator for propositional logic formulas. It takes a truth table during instantiation e.g. {"A": False, "B": True, "C": True, "D": True}
        for example
        ```
        proposition = "not not not (A and C)"
        test_table = {"A": False, "C": True}

        AST = prop_parser.parse(proposition)
        truth_value = PropEvaluator(test_table).visit(AST)
        ```
        in this case truth_value is `True`
    """
    def __init__(self, table):
        super().__init__()
        self.table = table
         
    # this way I ensure tokens are also visited
    def visit_also_tokens(self, tree_or_token):
            if isinstance(tree_or_token, Token):
                token = tree_or_token
                return getattr(self, token.type)(token)
            else: 
                tree = tree_or_token
                return self.visit(tree)

    def biconditional(self, tree: Tree): 
        definendum, definient = tree.children
        definendum_v = self.visit_also_tokens(definendum)
        definient_v = self.visit_also_tokens(definient)
        return ((definendum_v and definient_v) or ((not definendum_v) and (not definient_v)))
    def entailment(self, tree: Tree): 
        body, head = tree.children
        return ((not self.visit_also_tokens(body)) or (self.visit_also_tokens(head)))
    def disjunction(self, tree: Tree): 
        left_addendum, right_addendum = tree.children
        return (self.visit_also_tokens(left_addendum) or self.visit_also_tokens(right_addendum))
    def conjunction(self, tree: Tree): 
        left_factor, right_factor = tree.children
        return (self.visit_also_tokens(left_factor) and self.visit_also_tokens(right_factor))
    def negation(self, tree: Tree): 
        (negatum,) = tree.children
        return not self.visit_also_tokens(negatum)
    def BASE_ATOM(self, token):
        return self.table[token]


if __name__ == "__main__":
    print("running some tests...")
    
    test_table = {"A": False, "B": True, "C": True, "D": True}
    
    propositions = [
    ("A and B or C entails D", True),
    ("A and B and C", False),
    ("A", False),
    ("not A", True),
    ("not not A", False),
    ("not not not A", True),
    ("A and D and C", False),
    ("B and D and C", True),
    ("A or B or C entails A", False),
    ("A entails A", True),
    ("not not not (A and C)", True),
    ("((A iff B) entails (C or B and A)) or A", True),
    ]

    def test_proposition(proposition, ground_truth_value):
        AST = prop_parser.parse(proposition)
        print(f"AST of {proposition} is")
        if not isinstance(AST, Token):
            print(AST.pretty())
        else:
            print(AST)

        test_pe = PropEvaluator(test_table)
        if not isinstance(AST, Token):
            out = test_pe.visit(AST)
        else: 
            out = test_pe.table[AST]
        assert out == ground_truth_value, f"An error in proposition {proposition} was found: it was evaluated to {out}, but it should be {ground_truth_value}"
        print(f"the truth value found was {out} (which is correct)")
        print("\n")

    print(f"test truth value is {test_table}")
    for proposition, ground_truth_value in propositions:
        test_proposition(proposition, ground_truth_value)
