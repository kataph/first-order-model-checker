from check import P9FreeVariablesExtractor, P9Evaluator, P9ModelReader, prover9_parser
from basic_formulas_manipulation import treeExplainerRED, treeExplainerReturning, treeExplainerReturningRED
from lark import Tree

def test_alternatives(alternative):
    axioms = """all A all B all C all T all T2  ((((continuantPartOf(A,B,T)) & (continuantPartOf(B,C,T2)) & (temporalPartOf(T,T2)))) -> (continuantPartOf(A,C,T))) # label("continuant-part-of-transitive-at-a-time") ."""
    modelAST: Tree = prover9_parser.parse(open(r"C:\Users\Francesco\Desktop\Work_Units\fol_model_checker\BFO_p9\BFO-model-from-repo.p9","r").read())       
    axiomAST: Tree = prover9_parser.parse(axioms)

    p9model = P9ModelReader()

    model = p9model.read_model(modelAST)
    out = alternative(model = model, axioms = axiomAST)
    print(out)

def tests(options):
        print("Doing some tests...")

        model_texts_axioms_evals = [
            ("P(a1,a2).",
            """all X True.
            all X False.""",
            [True, False]),
            
            ("P(a1,a2).P(a2,a3).P(a4,a4).",
            "all X exists Y P(X,Y).",
            [False]),

            ("P(a1,a2).P(a2,a3).P(a3,a4).P(a4,a5).P(a5,a6).P(a6,a1).",
            "all X exists Y P(X,Y).",
            [True]),
            
            ("A(x,y).A(z,y).",
            "all X exists Y A(X,Y) & B(Y).",
            [False]),
            
            ("""A(x,y).A(z,z).A(zz,zz).B(zz).""",
            "all X exists Y A(X,Y) & B(Y).",
            [False]),

            ("""A(v).B(v).C(x).""",
            "exists Y A(Y) & B(Y).",
            [True]),
            
            ("""A(v).B(v).C(x).""",
            "all Y A(Y) & B(Y).",
            [False]),

            ("""A(v).B(v).C(x).""",
            """exists Y A(Y) & B(Y).
                all Y A(Y) & B(Y).
                all X A(X) <-> B(X).
                exists X C(X).""",
            [True, False, True, True]),

            ("""A(x,y).B(y).A(y,x).B(x).""",
            """all X exists Y A(X,Y) -> B(Y).
                all X all Y A(X,Y) -> B(Y).
                all X all Y A(X,Y).
                exists X exists Y C(X).""",
            [True, True, False, False]),

            ("""P(x,y).P(x,x).P(y,y).""",
            """all X P(X,X) # label(reflexivity) .
                all X all Y -(X = Y) -> -(P(X,Y) & P(Y,X)) # label(antisymmetry).
                all X all Y (P(X,Y) & P(Y,X)) # label(global_symmetry).
                all X all Y all Z (P(X,Y) & P(Y,Z) -> P(X,Z)) # label(transitivity). """,
            [True, True, False, True]),
            ("""P(x,y).P(x,x).P(y,y).PP(x,y).P(x,s).PP(x,s).P(y,s).PP(y,s).S(s,x,y).P(s,s).
                O(x,x).O(x,y).O(y,x).O(y,y).O(s,s).O(x,s).O(s,x).O(s,y).O(y,s).""",
            """all X P(X,X) # label(reflexivity) .
                all X all Y -(X = Y) -> -(P(X,Y) & P(Y,X)) # label(antisymmetry).
                all X all Y (P(X,Y) & P(Y,X)) # label(global_symmetry).
                all X all Y all Z (P(X,Y) & P(Y,Z) -> P(X,Z)) # label(transitivity). 
                all X all Y PP(X,Y) <-> P(X,Y) & - X=Y # label(PP_def). 
                all X all Y O(X,Y) <-> exists Z P(Z,X) & P(Z,Y) # label(O_def). 
                """,
            [True, True, False, True, True, True]),
        ]

        p9variables = P9FreeVariablesExtractor()
        p9model = P9ModelReader()

        for model_text, axiom_text, ground_eval in model_texts_axioms_evals:
            print("testing axiom/model---->", axiom_text, model_text)
            modelAST: Tree = prover9_parser.parse(model_text)       
            axiomAST: Tree = prover9_parser.parse(axiom_text)
            print("parsed axiom --->", axiomAST.pretty())

            free_vars, axioms_signature = p9variables.extract_free_variables_and_signature(axiomAST)
            
            model = p9model.read_model(modelAST)
            p9evaluator = P9Evaluator(model = model, options = options)
            # p9evaluator.model = model
            

            print("after-model-visit-model---->", model)
            print("after-model-visit-model-signature---->", model.signature)

            if "=" in model.signature.predicates:
                raise TypeError(f"Equality was found in the model. It should not be there, and instead all constants should be assumed to be different")
            if len(free_vars) > 0:
                raise TypeError(f"An axiom was found with a free, unquantified, variable. The axiom is {axiom_text}. The free variables are {free_vars} and the parsed tree is {axiomAST.pretty()}")
            if (not set(axioms_signature.constants) <= set(model.signature.constants)):
                raise TypeError(f"An axiom was found with a constant that does not appear in the model!")
            if (not set(axioms_signature.predicates) <= set(model.signature.predicates)):
                print(f"Warning: An axiom was found with a predicate that does not appear in the model! axioms_signature.predicates = {axioms_signature.predicates} and model.signature.predicates={model.signature.predicates}. This may or may not be correct.")
            for predicate, arity in axioms_signature.predicates.items():
                if predicate in model.signature.predicates and model.signature.predicates[predicate] != arity:
                    raise TypeError(f"An axiom was found with the predicate {predicate} of arity {arity}, but in the model the same predicate has arity {model.signature.predicates[predicate]}!")
                
            print("Free variables from axioms---->", free_vars)
            print("after-variables-extraction-axioms-signature---->", axioms_signature)

            evaluation = p9evaluator.evaluate(axiomAST)
            print(f"evaluation of \n>>>{axiom_text}<<<\n is >>>{evaluation}<<< given model {model} \n actual evaluation is >>>{ground_eval}<<<")
            if not evaluation == ground_eval:
                treeExplainerRED(axiomAST)
                explanation_txt = treeExplainerReturning(axiomAST)
                explanation_file = "explanation"
                with open(explanation_file+".txt", "w", encoding='utf-8') as fo: fo.write(explanation_txt)
                raise TypeError(f"Test failed, see printed explanation above... Also saved in file {explanation_file} (both .html and .txt)")
            

        print("all the following tests where passed: ")
        for x,y,z in model_texts_axioms_evals:
            print(x)
            print(y)
            print(z)
            print("==============================================================================")
        print("all the previous tests where passed.")
        
        # loop_on_file(file_path=r"C:\Users\Francesco\Desktop\Work_Units\fol_model_checker\test_p9_parsing.txt")
        # print("axioms signature after full variable extraction of file"+r"C:\Users\Francesco\Desktop\Work_Units\fol_model_checker\test_p9_parsing.txt", ....axioms_signature)
        # print(model)

if __name__ == "__main__":
    tests(options=[])
    # tests(options=["equivalence"])
    