# Remember to execute this file in e.g. the following way (from the root folder): python -m finer_grained_tests.test_basic_formula_manipulation 
from model import prover9_parser
from basic_formulas_manipulation import *

def showcase_associative_flattener():
    axiom_text = """exists Y exists Z all X all U all UU exists T exists TT ((A(X) | -U(X) | K(X,Z)) & (B(X,Y) | -V(X,Y,Z)) & (C(Z)))."""
    axiomAST = prover9_parser.parse(axiom_text)
    flattener = AssociativeFlattener()
    flatAst = flattener.transform_repeatedly(axiomAST)
    print(f"From the axiom {axiom_text}, the following AST is obtained:")
    treeExplainer(axiomAST)
    print(f"which is flattened to:")
    treeExplainer(flatAst)

def test_free_variables_extraction():
    extractor = P9FreeVariablesExtractor()
    axiom_to_free_vars = [("(all Y p(X,Y)).", {"X"}),
                          ("(all Z all W l(X,Y,Z,W)).", {"X", "Y"})]
    for axiom, free_vars in axiom_to_free_vars:
        ast = prover9_parser.parse(axiom)
        assert free_vars == (actual:=extractor.transform(ast)), f"expected {free_vars}, got {actual}"
        assert free_vars == (actual:=extractor.transform(AssociativeFlattener().transform_repeatedly(ast))), f"expected {free_vars}, got {actual}"
    print("All good with free vars extraction")

def test_reverse_associative_flattener():
    axiom_text = """exists Y exists Z all X all U all UU exists T exists TT ((A(X) | -U(X) | K(X,Z)) & (B(X,Y) | -V(X,Y,Z)) & (C(Z)))."""
    axiomAST = prover9_parser.parse(axiom_text)
    flatAst = AssociativeFlattener().transform_repeatedly(axiomAST)
    reverseflatAst = ReverseAssociativeFlattener().transform_repeatedly(axiomAST)
    print(f"From the axiom {axiom_text}, the following AST is obtained:")
    treeExplainer(axiomAST)
    print(f"which is flattened to:")
    treeExplainer(flatAst)
    print(f"which is un-flattened to:")
    treeExplainer(reverseflatAst)
    assert reverseflatAst == axiomAST
    print(f"All good!")

def showcase_replace_variable():
    rp = ReplaceVariable("X", "X1")
    print(f"replacing X with X1 in ((all X A(X)) & B(X)). results in:")
    treeExplainer(rp.visit(prover9_parser.parse("((all X A(X)) & B(X)).")))
    print(f"replacing X with X1 in ((all X A(X)) & B(X)). with no conflic resolution results in:")
    treeExplainer(ReplaceVariable("X","X1",False).visit(prover9_parser.parse("((all X A(X)) & B(X)).")))

def test_variables_adjuster():
    unique = ToUniqueVariables()
    in_outs = [("((all X A(X,Y)) & (exists X P(X)) & (exists X V(X))).", "((all X A(X,Y)) & (exists X1 P(X1)) & (exists X2 V(X2)))."),
               ("((all X A(X,Y)) & (exists X P(X)) & (exists X (V(X) & all X B(X)))).", "((all X A(X,Y)) & (exists X1 P(X1)) & (exists X3 (V(X3) & all X2 B(X2))))."),
               ("all A all B all C all T all T2  ((((properContinuantPartOf(A,B,T)) & (properContinuantPartOf(B,C,T2)) & (temporalPartOf(T,T2)))) -> (properContinuantPartOf(A,C,T))) # label(\"proper-continuant-part-of-transitive-at-a-time\").", 
                "all A all B all C all T all T2  ((((properContinuantPartOf(A,B,T)) & (properContinuantPartOf(B,C,T2)) & (temporalPartOf(T,T2)))) -> (properContinuantPartOf(A,C,T))) # label(\"proper-continuant-part-of-transitive-at-a-time\")."),
                ("all P all C1 all C2  ((((occursIn(P,C1)) & (all T  ((eXistsAt(P,T)) <-> (locatedIn(C1,C2,T)))))) -> (occursIn(P,C2))).","all P all C1 all C2  ((((occursIn(P,C1)) & (all T  ((eXistsAt(P,T)) <-> (locatedIn(C1,C2,T)))))) -> (occursIn(P,C2)))."),
                ("all C1 (all C1 Atom(C1)) & (all C2 exists T locatedIn(C1,C2,T)).", "all C3 (all C1 Atom(C1)) & (all C2 exists T locatedIn(C3,C2,T))."),
                ("((all C2 exists C1 locatedTopOf(C1,C2,T)) & (all C2 exists C1 locatedIn(C1,C2,T))).", "((all C2 exists C1 locatedTopOf(C1,C2,T)) & (all C4 exists C3 locatedIn(C3,C4,T)))."),
                ("((all C20 exists C1 locatedTopOf(C1,C20,T)) & (all C2 exists C1 locatedIn(C1,C2,T))).", "((all C20 exists C1 locatedTopOf(C1,C20,T)) & (all C2 exists C3 locatedIn(C3,C2,T)))."),
               ]
    for inp, out in in_outs:
        base = prover9_parser.parse(inp)
        calc = unique.adjust_variables(base)
        ground = prover9_parser.parse(out)
        assert calc == ground, f"From black/white and string should have got green, got read instead {base, treeExplainer(base), treeExplainerGREEN(ground), treeExplainerRED(calc)}"
    print("All good for variables adjuster")

def test_variable_normalization():
    test_true = [
        ("(all X A(X)).","(all B A(B))."),
        ("(all X exists Y A(X,Y)).","(all B exists Z A(B,Z))."),
    ]
    test_false = [
        ("(all X A(X)).","(all B C(B))."),
        ("(all X exists Y A(X,Y)).","(exists B exists Z A(B,Z))."),
    ]
    vn = VariableNormalizer()
    for left, right in test_true:
        left_ast = prover9_parser.parse(left)
        right_ast = prover9_parser.parse(right)
        assert vn(left_ast) == vn(right_ast), (treeExplainer(left_ast),treeExplainerGREEN(vn(left_ast)),treeExplainerRED(vn(right_ast)))
    for left, right in test_false:
        left_ast = prover9_parser.parse(left)
        right_ast = prover9_parser.parse(right)
        assert not vn(left_ast) == vn(right_ast)
    print("All good for variable normalization")

def showcase_reverse_prenexCNF():
    textp = "all X (((A(X) & B(X)) | C(X)) & D(X))."
    astp=prover9_parser.parse(textp)
    print("The axiom in GREEN is transformed in the axiom in RED, by the reverse prenex CNF")
    treeExplainerGREEN(astp)
    tp=ToReversePrenexCNF()
    treeExplainerRED(tp.adjust_transform_repeatedly(astp))


def test_NNF():
    tests = [
        ("(-(all A all B A(A) & B(B))).", "(exists A (exists B (-A(A) | -B(B)))).")
    ]
    base_test(tests, lambda inp: ToString().visit(ToNNF().adjust_transform_repeatedly(prover9_parser.parse(inp))), name = "NNF")

def test_reduce_logical_signature():
    tests = [
        ("(A(X) -> B(X)).", "(-A(X) | B(X))."),
        ("(A(X) <-> B(X)).", "((-A(X) | B(X)) & (-B(X) | A(X)))."),
        ("(A(X) & A(X)).", "(A(X))."),
        ("(A(X) & A(X) & A(X)).", "(A(X))."),
    ]
    base_test(tests, lambda inp: ToString()(ReduceLogicalSignature()(prover9_parser.parse(inp))), "reduce logical signature")

def test_toNNF():
    tests = [
        ("((A(X) & A(X)) | C(X)).", "(A(X) | C(X))."),
        ("((A(X) & B(X)) | C(X)).", "((A(X) & B(X)) | C(X))."),
        ("(-((A(X) & B(X)) | exists X C(X))).", "((-A(X) | -B(X)) & (all X (-C(X))))."),
        ("all X all T  ((instanceOf(X,fiatLine,T)) -> (exists S exists TP  (((temporalPartOf(TP,T)) & (occupiesSpatialRegion(X,S,TP)) & (instanceOf(S,oneDimensionalSpatialRegion,TP)))))).", "(all X (all T (-instanceOf(X,fiatLine,T) | (exists S (exists TP ((temporalPartOf(TP,T) & occupiesSpatialRegion(X,S,TP)) & instanceOf(S,oneDimensionalSpatialRegion,TP)))))))."),
    ]
    func = lambda inp: ToString()(ToNegativeNormalForm()(prover9_parser.parse(inp)))
    name = "toCNF"
    base_test(tests, func, name)

def test_toCNF():
    tests = [
        ("((A(X) & A(X)) | C(X)).", "(A(X) | C(X))."),
        ("((A(X) & B(X)) | C(X)).", "((A(X) | C(X)) & (B(X) | C(X)))."),
        ("((A(X) & B(X)) | exists X C(X)).", "((A(X) | (exists X (C(X)))) & (B(X) | (exists X (C(X)))))."),
        ("all X all T  ((instanceOf(X,fiatLine,T)) -> (exists S exists TP  (((temporalPartOf(TP,T)) & (occupiesSpatialRegion(X,S,TP)) & (instanceOf(S,oneDimensionalSpatialRegion,TP)))))).", "(all X (all T (-instanceOf(X,fiatLine,T) | (exists S (exists TP ((temporalPartOf(TP,T) & occupiesSpatialRegion(X,S,TP)) & instanceOf(S,oneDimensionalSpatialRegion,TP)))))))."),
    ]
    func = lambda inp: ToString()(ToConjunctiveNormalForm()(prover9_parser.parse(inp)))
    name = "toCNF"
    base_test(tests, func, name)

def test_toDNF():
    tests = [
        ("((A(X) | B(X)) & C(X)).", "((A(X) & C(X)) | (B(X) & C(X)))."),
        ("((A(X) | B(X)) & (C(X) | D(X))).", "(((A(X) & C(X)) | (A(X) & D(X))) | ((B(X) & C(X)) | (B(X) & D(X))))."),
        ("((A(X) | B(X)) & (C(X) | True)).", "(A(X) | B(X))."),
        ("all X all T  ((instanceOf(X,fiatLine,T)) -> (exists S exists TP  (((temporalPartOf(TP,T)) & (occupiesSpatialRegion(X,S,TP)) & (instanceOf(S,oneDimensionalSpatialRegion,TP)))))).", "(all X (all T (-instanceOf(X,fiatLine,T) | (exists S (exists TP ((temporalPartOf(TP,T) & occupiesSpatialRegion(X,S,TP)) & instanceOf(S,oneDimensionalSpatialRegion,TP)))))))."),
    ]
    func = lambda inp: ToString()(ToDisjunctiveNormalForm()(prover9_parser.parse(inp)))
    name = "toDNF"
    base_test(tests, func, name)

def test_toPDNF():
    tests = [
        ("((A(X) | B(X)) & C(X)).", "((A(X) & C(X)) | (B(X) & C(X)))."),
        ("((A(X) | B(X)) & (C(X) | D(X))).", "(((A(X) & C(X)) | (A(X) & D(X))) | ((B(X) & C(X)) | (B(X) & D(X))))."),
        ("((A(X) | B(X)) & (C(X) | True)).", "(A(X) | B(X))."),
        ("all X all T  ((instanceOf(X,fiatLine,T)) -> (exists S exists TP  (((temporalPartOf(TP,T)) & (occupiesSpatialRegion(X,S,TP)) & (instanceOf(S,oneDimensionalSpatialRegion,TP)))))).", "(all X (all T (exists S (exists TP (-instanceOf(X,fiatLine,T) | ((temporalPartOf(TP,T) & occupiesSpatialRegion(X,S,TP)) & instanceOf(S,oneDimensionalSpatialRegion,TP)))))))."),
        ("all I all START all END  ((((instanceOf(I,temporalInterval,I)) & (hasFirstInstant(I,START)) & (hasLastInstant(I,END)))) -> (-(exists GAP exists GAPSTART exists GAPEND  (((-(instanceOf(GAP,temporalInstant,GAP))) & (hasFirstInstant(GAP,GAPSTART)) & (hasLastInstant(GAP,GAPEND)) & (((precedes(GAPEND,END)) | (((temporalPartOf(END,I)) & ((GAPEND) = (END)))))) & (((precedes(START,GAPSTART)) | (((temporalPartOf(START,I)) & ((GAPSTART) = (START)))))) & (-(temporalPartOf(GAP,I)))))))).","(all I (all START (all END (all GAP (all GAPSTART (all GAPEND (((-instanceOf(I,temporalInterval,I) | -hasFirstInstant(I,START)) | -hasLastInstant(I,END)) | (((((instanceOf(GAP,temporalInstant,GAP) | -hasFirstInstant(GAP,GAPSTART)) | -hasLastInstant(GAP,GAPEND)) | ((-precedes(GAPEND,END) & -temporalPartOf(END,I)) | (-precedes(GAPEND,END) & -GAPEND = END))) | ((-precedes(START,GAPSTART) & -temporalPartOf(START,I)) | (-precedes(START,GAPSTART) & -GAPSTART = START))) | temporalPartOf(GAP,I)))))))))."),
    ]
    func = lambda inp: ToString()(ToPrenexDNF()(prover9_parser.parse(inp)))
    name = "toPDNF"
    base_test(tests, func, name)

def test_simplification():
    tests = [
        ("(all X (A(X)&A(X))).","(all X A(X))."),
        ("(all X (B(X)|B(X)|B(X))).","(all X B(X))."),
        ("(all X (B(X)|C(X)|B(X))).","(all X B(X)|C(X))."),
        ("(all X ((A(X)|B(X)|C(X))&D(X))&B(X)).","(all X D(X) & B(X))."),
        ("(all X (A(X) | B(X) | C(X)) & B(X) & (A(X) | B(X) | C(X))).","(all X B(X))."),
        ("(all X (A(X) | B(X) | C(X)) & D(X) & (A(X) | B(X) | C(X))).","(all X (A(X) | B(X) | C(X)) & D(X))."),
        ("(all X (A(X) | B(X) | C(X))).","(all X (A(X) | B(X) | C(X)))."),
        ("(all X --A(X)).","(all X A(X))."),
        ("((all A B(A))&(all C B(C))).","(all A B(A))."),
        ("((((all A B(A))&(all C B(C))))|(all Z B(Z))).","(all Z B(Z))."),
    ]
    test_with_parsing(tests=tests, func=BinaryOpSimplificator().visit_repeatedly, name="simplification")

def showcase_miniscoping():    
    tests = [
            ("(all X all Y all Z all T all TAU cP(X,Y,T) & cP(Y,Z,TAU) & tP(T,TAU) -> cP(X,Z,T)).","(all Y (all Z (all T ((all TAU ((-(cP(Y,Z,TAU))) | (-(tP(T,TAU))))) | (all X ((-(cP(X,Y,T))) | cP(X,Z,T)))))))."),
            ("(all X all Y (C(Y) & (A(X) | B(X,Y)))).","((all Y (C(Y))) & (all X (A(X) | (all Y1 (B(X,Y1))))))."),
            ("(all X all Y A(X) & B(X,Y)).","((all X (A(X))) & (all X1 (all Y (B(X1,Y)))))."),
            ("(all X all Y (A(X) | B(X,Y))).","(all X (A(X) | (all Y (B(X,Y)))))."),
            ("(all Y (C(Y) | (A(X) | B(X,Y)))).","(A(X) | (all Y (C(Y) | B(X,Y))))."),
            ("(all X -( A(X) | False)).","(-(exists X A(X)))."),#"((True) & (-(exists X (A(X)))))."),
            ("(all X all Y (C(Y) | (A(X) & B(X,Y)))).", "(((all X (A(X))) | (all Y (C(Y)))) & (all Y1 (C(Y1) | (all X1 (B(X1,Y1))))))."),
            ("(all X all Y (C(Y) & (A(X) | B(X,Y)))).","((all Y (C(Y))) & (all X (A(X) | (all Y1 (B(X,Y1))))))."),
            ("all A all B  ((((exists T  (((instanceOf(A,objectAggregate,T)) & (continuantPartOf(A,B,T)) & (continuantPartOf(B,A,T))))) & (all T  ((continuantPartOf(A,B,T)) <-> (continuantPartOf(B,A,T)))))) -> ((A) = (B))).", 
             "all A all B  ((((exists T  (((instanceOf(A,objectAggregate,T)) & (continuantPartOf(A,B,T)) & (continuantPartOf(B,A,T))))) & (all T  ((continuantPartOf(A,B,T)) <-> (continuantPartOf(B,A,T)))))) -> ((A) = (B)))."),
            ]
    
    # open("deletePCNF.txt","w", encoding = "utf-8").write(treeExplainerReturning(ToMiniscopedPCNF().adjust_transform_repeatedly(prover9_parser.parse(tests[-1][0]))))
    # open("deletePNNF.txt","w", encoding = "utf-8").write(treeExplainerReturning(ToMiniscopedPNNF().adjust_transform_repeatedly(prover9_parser.parse(tests[-1][0]))))
    # open("deletePDNF.txt","w", encoding = "utf-8").write(treeExplainerReturning(ToMiniscopedPDNF().adjust_transform_repeatedly(prover9_parser.parse(tests[-1][0]))))
    # open("deleteCNF.txt","w", encoding = "utf-8").write(treeExplainerReturning(ToMiniscopedCNF().adjust_transform_repeatedly(prover9_parser.parse(tests[-1][0]))))
    # open("deleteNNF.txt","w", encoding = "utf-8").write(treeExplainerReturning(ToMiniscopedNNF().adjust_transform_repeatedly(prover9_parser.parse(tests[-1][0]))))
    # open("deleteDNF.txt","w", encoding = "utf-8").write(treeExplainerReturning(ToMiniscopedDNF().adjust_transform_repeatedly(prover9_parser.parse(tests[-1][0]))))
    # print("written some files")
    print(f"Various miniscoping transformations for the axiom {tests[-1][0]}")
    treeExplainerReturning(ToMiniscopedPCNF().adjust_transform_repeatedly(prover9_parser.parse(tests[-1][0])))
    treeExplainerReturning(ToMiniscopedPNNF().adjust_transform_repeatedly(prover9_parser.parse(tests[-1][0])))
    treeExplainerReturning(ToMiniscopedPDNF().adjust_transform_repeatedly(prover9_parser.parse(tests[-1][0])))
    treeExplainerReturning(ToMiniscopedCNF().adjust_transform_repeatedly(prover9_parser.parse(tests[-1][0])))
    treeExplainerReturning(ToMiniscopedNNF().adjust_transform_repeatedly(prover9_parser.parse(tests[-1][0])))
    treeExplainerReturning(ToMiniscopedDNF().adjust_transform_repeatedly(prover9_parser.parse(tests[-1][0])))

def showcase_to_string():
    tos = ToString()
    tree = Tree(
            "universal_quantification",
            [
                Token("VARIABLE", "X"),
                Tree(
                    "universal_quantification_bounded",
                    [
                        Token("VARIABLE", "Y"),
                        Tree(
                            "predicate",
                            [Token("PREDICATE_SYMBOL", "lec"), Token("VARIABLE", "Y")],
                        ),
                        Tree(
                            "disjunction",
                            [
                                Tree(
                                    "negation",
                                    [
                                        Tree(
                                            Token("RULE", "predicate"),
                                            [
                                                Token("PREDICATE_SYMBOL", "lec"),
                                                Token("VARIABLE", "Y"),
                                            ],
                                        )
                                    ],
                                ),
                                Tree(
                                    Token("RULE", "predicate"),
                                    [
                                        Token("PREDICATE_SYMBOL", "att"),
                                        Token("VARIABLE", "X"),
                                        Token("VARIABLE", "Y"),
                                    ],
                                ),
                            ],
                        ),
                    ],
                ),
            ],
        )
    string = tos.visit(tree)
    print(f"from the tree {tree} the string {string} is obtained")

def showcase_remove_labels():
    text = "all A (B(A)) # label(\"proper-continuant-part-of-transitive-at-a-time\") ."
    ast = prover9_parser.parse(text)
    tast = RemoveLabels().transform(ast)
    print(f"Remove labels from the axiom whose AST is in GREEN to the axiom whose AST is in red")
    treeExplainerGREEN(ast)
    treeExplainerRED(tast)

if __name__ == "__main__":
    showcase_associative_flattener()
    showcase_replace_variable()
    showcase_miniscoping()
    showcase_to_string()
    showcase_remove_labels()
    showcase_reverse_prenexCNF()
    
    test_reverse_associative_flattener()
    test_free_variables_extraction()
    test_variables_adjuster()
    test_variable_normalization()
    test_NNF()
    test_reduce_logical_signature()
    test_toNNF()
    test_toCNF()
    test_toDNF()
    test_toPDNF()
    test_simplification()